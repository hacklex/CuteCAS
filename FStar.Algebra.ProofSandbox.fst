module FStar.Algebra.ProofSandbox

open FStar.Algebra.Classes.Equatable
open FStar.Algebra.Classes.Grouplikes
open FStar.Algebra.Classes.Ringlikes

module LB = FStar.List.Tot.Base
module TC = FStar.Tactics.Typeclasses

#set-options "--z3rlimit 1 --ifuel 1 --fuel 1"
 
let rec map_refine (#a #b: Type) (l: list a) (f:(x:a{x<<l}) -> b)
  : Tot (list b) (decreases l) = match l with
  | [] -> []
  | h::t -> (f h)::(map_refine t f)

//open FStar.List.Tot

type formula t {| r: integral_domain t |} = 
  | Atom : t -> formula t
  | Mul : (l: list (formula t)) -> formula t
  | Add : list (formula t) -> formula t
  | Neg : (x:formula t) -> formula t
 
let neg_lemma  #t {| r: integral_domain t |} (f: formula t{Neg? f}) 
  : Lemma (Neg?.x f << f) = ()
   
let rec formula_to_expr #t {| r: integral_domain t |} (f: formula t) 
  : Tot t (decreases f)  =
  match f
  with
  | Atom t -> t
  | Neg r -> neg_lemma f;
            -(formula_to_expr r)
  | Add l -> List.Tot.Base.fold_left ( + ) zero (map_refine l formula_to_expr)
  | Mul l -> List.Tot.Base.fold_left ( * ) one (map_refine l formula_to_expr)
  | _ -> zero

instance eq_of_integral_domain t (r: integral_domain t) : equatable t
  = FStar.Tactics.Typeclasses.solve
 
let equality_lemma t {| integral_domain t |} 
  : Lemma (one = (one <: t)) = 
  let eq : equatable t = TC.solve in
  eq.reflexivity one

let plus t (r: integral_domain t) (x y:t) = add_of t #TC.solve x y
 
let rec fold_left_identity #t {| r: integral_domain t |} (x y:t) (l: list t)
  : Lemma (requires x = y) 
          (ensures LB.fold_left (+) x l = LB.fold_left (+) y l) 
          (decreases LB.length l) = 
  match l with 
  | [] -> assert_norm (LB.fold_left (+) x l == x);
         assert_norm (LB.fold_left (+) y l == y)
  | (hd::tl) -> reflexivity hd;
              add_congruence x hd y hd; 
              match tl with 
              | [] -> assert_norm (LB.fold_left (+) x l == x + hd);
                     assert_norm (LB.fold_left (+) y l == y + hd)  
              | _ -> fold_left_identity (x+hd) (y+hd) tl 

let fold_zero_lemma #t {| r: integral_domain t |} (x:t) (l: list t)
  : Lemma (LB.fold_left (+) x l = LB.fold_left (+) (zero+x) l) =  
  left_add_identity x;
  symmetry x (zero+x);
  fold_left_identity x (zero+x) l 

let sum #t {| r: integral_domain t |} (l: list t) = LB.fold_left (+) zero l

let (+$) #t {| r: integral_domain t |} (x:t) (y: list t) = LB.fold_left (+) x y

let id_sum #t {| r: integral_domain t |} (x:t) (y: list t{Cons? y}) 
  : Lemma (x +$ y == (x + Cons?.hd y) +$ Cons?.tl y) = ()

#set-options "--z3rlimit 2 --ifuel 2 --fuel 2"

let wat #t {| r: integral_domain t |} (x:t) (y: list t) 
  : Lemma (x +$ y = sum (x::y)) = 
  match y with
  | [] -> left_add_identity x;
         symmetry x (zero+x)
  | (hd::tl) -> assert (x +$ y == (x+hd) +$ tl);
              assert (sum (x::y) == (zero+x) +$ y);
              assert ((zero+x) +$ y == (zero+x+hd) +$ tl);
              transitivity_for_calc_proofs t;
              calc (=) {
                zero + x + hd; = { add_associativity zero x hd }
                zero + (x+hd); = { left_add_identity (x+hd) }
                x+hd;
              };
              fold_left_identity (zero+x+hd) (x+hd) tl;
              symmetry (x +$ y) (sum (x::y))

let sum_with_zero #t {| r: integral_domain t |} (x:t) (y: list t) 
  : Lemma (x +$ (zero :: y) = x +$ y) = 
  right_add_identity x;
  fold_left_identity (x+zero) x y

#set-options "--z3rlimit 1 --ifuel 1 --fuel 1"

let rec id_sum_comm #t {| r: integral_domain t |} (x:t) (y: list t) 
  : Lemma (ensures x +$ y = x + sum y) (decreases LB.length y) = 
  match y with
  | [] -> assert (x + sum y == x + zero);  
         right_add_identity x;
         symmetry (x+zero) x
  | (hd::tl) -> let lhs = x +$ y in
              let rhs : t = x + sum y in 
              let hd = Cons?.hd y in
              let tl = Cons?.tl y in 
              assert (lhs == (x+hd) +$ tl);
              id_sum_comm (x+hd) tl;
              assert (lhs = (x+hd) + sum tl);
              id_sum_comm (zero+hd) tl;
              assert (rhs == x + ((zero+hd) +$ tl));
              assert ((zero+hd) +$ tl = (zero+hd) + sum tl);
              reflexivity x;
              add_congruence x ((zero+hd) +$ tl) x ((zero+hd) + sum tl);
              assert (rhs = x + ((zero+hd) + sum tl));
              transitivity_for_calc_proofs t;              
              calc (=) {
                rhs; = { left_add_identity hd;
                         reflexivity (sum tl);
                         add_congruence (zero+hd) (sum tl) hd (sum tl);
                         add_congruence x ((zero+hd) + sum tl) x (hd + sum tl) }
                x + (hd + sum tl);                
              };
              symmetry (x + (hd + sum tl)) rhs;
              assert (x+(hd + sum tl) = rhs);
              add_associativity x hd (sum tl)

#set-options "--z3rlimit 2 --ifuel 2 --fuel 2"

let sum_extract_left #t {| r: integral_domain t |} (l: list t{Cons? l}) 
  : Lemma (ensures sum l = (Cons?.hd l) +$ (Cons?.tl l)) =  
  wat (Cons?.hd l) (Cons?.tl l);
  symmetry ((Cons?.hd l) +$ (Cons?.tl l)) (sum l) 

let sum_is_associative #t {| r: integral_domain t |} (l: list t{Cons? l}) 
  : Lemma (ensures sum l = Cons?.hd l + sum (Cons?.tl l)) 
          (decreases LB.length l) =  // sum l == hd + sum tl
  let hd = Cons?.hd l in
  let tl = Cons?.tl l in 
  sum_extract_left l;
  id_sum_comm hd tl;
  transitivity (sum l) (hd +$ tl) (hd + sum tl)

let ($+) #t {| r: integral_domain t |} (y: list t) (x:t) = LB.fold_right (+) y x

let sr #t {| r: integral_domain t |} (y: list t) = y $+ zero

let sum_is_r_associative #t {| r: integral_domain t |} (l: list t{Cons? l}) 
  : Lemma (ensures sr l = sr (Cons?.tl l) + Cons?.hd l) =  
  let hd = Cons?.hd l in
  let tl = Cons?.tl l in 
  match l with
  | [] -> reflexivity (zero <: t)
  | (hd::tl) -> assert (sr l == hd + (sr tl));
              add_commutativity hd (sr tl)
  
let rec fold_direction_is_insignificant #t {| r: integral_domain t |} (l: list t) 
  : Lemma (ensures sr l = sum l) (decreases LB.length l) = 
  let eq : equatable t = TC.solve in
  let zero : t = zero in
  eq.reflexivity zero;
  match l with 
  | [] -> ()
  | (hd::tl) -> let hd = Cons?.hd l in
              let tl = Cons?.tl l in   
              transitivity_for_calc_proofs t;
              calc (=) {
                sr l; = { sum_is_r_associative l }
                sr tl + hd;  = { fold_direction_is_insignificant tl; 
                                 reflexivity hd; 
                                 add_congruence (sr tl) hd (sum tl) hd }
                sum tl + hd; = { add_commutativity (sum tl) hd }
                hd + sum tl; = { symmetry (sum l) (hd + sum tl); sum_is_associative l }
                sum l;
              }
