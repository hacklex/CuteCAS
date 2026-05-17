module FStar.CAS.Tactics.CanonRing
(* 
   Ring canonicalization tactic for the CuteCAS equatable typeclass tower.
   
   Provides:
   1. Bridges from equatable/add_comm_monoid/mul_comm_monoid to 
      FStar.Algebra.CommMonoid.Equiv types (equiv/cm), enabling reuse of
      the existing canon_monoid tactic for pure commutativity/associativity.
   2. A flat cr_eq record bundling ring operations + axioms.
   3. A full ring normalizer: distributes, flattens, sorts, reflects.
   4. ring_reflect: if normalized forms match, the originals are equivalent.
*)

open FStar.CAS.Equatable
open FStar.CAS.Grouplikes
open FStar.Algebra.CommMonoid.Equiv
open FStar.List.Tot.Base
open FStar.Tactics.CanonCommMonoidSimple.Equiv
open FStar.Classical

(* ================================================================== *)
(*  Part A: Bridges to CanonCommMonoidSimple.Equiv                    *)
(* ================================================================== *)

let equatable_to_equiv (#a:Type) (eq: equatable a) : equiv a =
  EQ (fun x y -> b2t (eq.op_Equals x y))
     (fun x -> eq.reflexivity x)
     (fun x y -> eq.symmetry x y)
     (fun x y z -> eq.transitivity x y z)

let add_comm_monoid_to_cm (#a:Type) (acm: add_comm_monoid a) 
  : cm a (equatable_to_equiv acm.add_monoid.add_semigroup.has_add.eq) =
  let ha = acm.add_monoid.add_semigroup.has_add in
  CM acm.add_monoid.has_zero.zero
     ha.op_Plus
     (fun x -> acm.add_monoid.left_add_identity x)
     (fun x y z -> acm.add_monoid.add_semigroup.associativity x y z)
     (fun x y -> acm.add_comm_semigroup.add_comm_magma.add_commutativity x y)
     (fun x y z w -> ha.congruence x y z w)

let mul_comm_monoid_to_cm (#a:Type) (mcm: mul_comm_monoid a)
  : cm a (equatable_to_equiv mcm.mul_monoid.mul_semigroup.has_mul.eq) =
  let hm = mcm.mul_monoid.mul_semigroup.has_mul in
  CM mcm.mul_monoid.has_one.one
     hm.op_Star
     (fun x -> mcm.mul_monoid.left_mul_identity x)
     (fun x y z -> mcm.mul_monoid.mul_semigroup.associativity x y z)
     (fun x y -> mcm.mul_comm_semigroup.mul_comm_magma.mul_commutativity x y)
     (fun x y z w -> hm.congruence x y z w)

(* ================================================================== *)
(*  Part B: Flat ring record (cr_eq)                                  *)
(* ================================================================== *)

noeq type cr_eq (a:Type) = {
  eq: equatable a;
  add: a -> a -> a;
  mul: a -> a -> a;
  neg: a -> a;
  zero: a;
  one: a;
  add_assoc: (x:a -> y:a -> z:a -> Lemma (eq.op_Equals (add (add x y) z) (add x (add y z))));
  add_comm:  (x:a -> y:a -> Lemma (eq.op_Equals (add x y) (add y x)));
  add_zero_l: (x:a -> Lemma (eq.op_Equals (add zero x) x));
  add_neg_r: (x:a -> Lemma (eq.op_Equals (add x (neg x)) zero));
  add_cong: (x:a -> y:a -> z:a -> w:a ->
    Lemma (requires eq.op_Equals x z /\ eq.op_Equals y w)
          (ensures eq.op_Equals (add x y) (add z w)));
  neg_cong: (x:a -> y:a ->
    Lemma (requires eq.op_Equals x y)
          (ensures eq.op_Equals (neg x) (neg y)));
  mul_assoc: (x:a -> y:a -> z:a -> Lemma (eq.op_Equals (mul (mul x y) z) (mul x (mul y z))));
  mul_comm:  (x:a -> y:a -> Lemma (eq.op_Equals (mul x y) (mul y x)));
  mul_one_l: (x:a -> Lemma (eq.op_Equals (mul one x) x));
  mul_cong: (x:a -> y:a -> z:a -> w:a ->
    Lemma (requires eq.op_Equals x z /\ eq.op_Equals y w)
          (ensures eq.op_Equals (mul x y) (mul z w)));
  distrib_l: (x:a -> y:a -> z:a -> Lemma (eq.op_Equals (mul x (add y z)) (add (mul x y) (mul x z))));
  zero_mul_l: (x:a -> Lemma (eq.op_Equals (mul zero x) zero));
  neg_mul_l: (x:a -> y:a -> Lemma (eq.op_Equals (mul (neg x) y) (neg (mul x y))));
  neg_add: (x:a -> y:a -> Lemma (eq.op_Equals (neg (add x y)) (add (neg y) (neg x))));
  double_neg: (x:a -> Lemma (eq.op_Equals (neg (neg x)) x));
}

(* ================================================================== *)
(*  Part C: Ring expression AST and canonical form                    *)
(* ================================================================== *)

let atom : eqtype = nat

type rexp =
  | RZero  : rexp
  | ROne   : rexp
  | RAtom  : atom -> rexp
  | RAdd   : rexp -> rexp -> rexp
  | RMul   : rexp -> rexp -> rexp
  | RNeg   : rexp -> rexp

type monom = list atom
type signed_monom : eqtype = bool & monom
type canon = list signed_monom

let vmap (a:Type) = list (atom & a) & a

let vmap_lookup (#a:Type) (i: atom) (vm: vmap a) : a =
  match assoc i (fst vm) with
  | Some x -> x
  | None -> snd vm

(* Uniform denotation: no singleton shortcuts, for clean induction *)
let rec monom_denote (#a:Type) (r: cr_eq a) (vm: vmap a) (m: monom) : a =
  match m with
  | [] -> r.one
  | i :: rest -> r.mul (vmap_lookup i vm) (monom_denote r vm rest)

let sm_denote (#a:Type) (r: cr_eq a) (vm: vmap a) (sm: signed_monom) : a =
  let (sign, m) = sm in
  let v = monom_denote r vm m in
  if sign then v else r.neg v

let rec canon_denote (#a:Type) (r: cr_eq a) (vm: vmap a) (c: canon) : a =
  match c with
  | [] -> r.zero
  | sm :: rest -> r.add (sm_denote r vm sm) (canon_denote r vm rest)

let rec rdenote (#a:Type) (r: cr_eq a) (vm: vmap a) (e: rexp) : a =
  match e with
  | RZero -> r.zero
  | ROne -> r.one
  | RAtom i -> vmap_lookup i vm
  | RAdd e1 e2 -> r.add (rdenote r vm e1) (rdenote r vm e2)
  | RMul e1 e2 -> r.mul (rdenote r vm e1) (rdenote r vm e2)
  | RNeg e1 -> r.neg (rdenote r vm e1)

(* ================================================================== *)
(*  Normalization functions                                           *)
(* ================================================================== *)

private let ( +% ) (x y: nat) : nat = Prims.op_Addition x y

let rec monom_merge (m1 m2: monom) : Tot monom (decreases (length m1 +% length m2)) =
  match m1, m2 with
  | [], _ -> m2
  | _, [] -> m1
  | i :: rest1, j :: rest2 ->
    if i <= j then i :: monom_merge rest1 m2
    else j :: monom_merge m1 rest2

let sign_mul (s1 s2: bool) : bool = (s1 = s2)

let sm_mul (sm1 sm2: signed_monom) : signed_monom =
  let (s1, m1) = sm1 in
  let (s2, m2) = sm2 in
  (sign_mul s1 s2, monom_merge m1 m2)

let negate_all (c: canon) : canon =
  map (fun (s, m) -> (not s, m)) c

let rec cross_one (sm: signed_monom) (c: canon) : canon =
  match c with
  | [] -> []
  | sm2 :: rest -> sm_mul sm sm2 :: cross_one sm rest

let rec cross (c1 c2: canon) : canon =
  match c1 with
  | [] -> []
  | sm :: rest -> cross_one sm c2 @ cross rest c2

let rec expand (e: rexp) : canon =
  match e with
  | RZero -> []
  | ROne -> [(true, [])]
  | RAtom i -> [(true, [i])]
  | RAdd e1 e2 -> expand e1 @ expand e2
  | RNeg e1 -> negate_all (expand e1)
  | RMul e1 e2 -> cross (expand e1) (expand e2)

(* Insertion sort on signed monomials (easier to prove correct than merge sort) *)
let rec monom_lt (m1 m2: monom) : bool =
  match m1, m2 with
  | [], [] -> false
  | [], _ -> true
  | _, [] -> false
  | i :: rest1, j :: rest2 ->
    if i < j then true
    else if i = j then monom_lt rest1 rest2
    else false

let sm_leq (sm1 sm2: signed_monom) : bool =
  let (s1, m1) = sm1 in
  let (s2, m2) = sm2 in
  monom_lt m1 m2 || (m1 = m2 && (not s1 || s2))

let rec insert_sm (sm: signed_monom) (c: canon) : canon =
  match c with
  | [] -> [sm]
  | sm2 :: rest ->
    if sm_leq sm sm2 then sm :: c
    else sm2 :: insert_sm sm rest

let rec isort (c: canon) : canon =
  match c with
  | [] -> []
  | sm :: rest -> insert_sm sm (isort rest)

let normalize (e: rexp) : canon =
  isort (expand e)

(* ================================================================== *)
(*  Part D: Correctness proofs                                        *)
(* ================================================================== *)

(* Transitivity chain helpers *)
private let trans (#a:Type) (r: cr_eq a) (x1 x2 x3: a)
  : Lemma (requires r.eq.op_Equals x1 x2 /\ r.eq.op_Equals x2 x3)
          (ensures r.eq.op_Equals x1 x3)
  = r.eq.transitivity x1 x2 x3

private let trans3 (#a:Type) (r: cr_eq a) (x1 x2 x3 x4: a)
  : Lemma (requires r.eq.op_Equals x1 x2 /\ r.eq.op_Equals x2 x3 /\ r.eq.op_Equals x3 x4)
          (ensures r.eq.op_Equals x1 x4)
  = r.eq.transitivity x1 x2 x3; r.eq.transitivity x1 x3 x4

private let trans4 (#a:Type) (r: cr_eq a) (x1 x2 x3 x4 x5: a)
  : Lemma (requires r.eq.op_Equals x1 x2 /\ r.eq.op_Equals x2 x3 
                 /\ r.eq.op_Equals x3 x4 /\ r.eq.op_Equals x4 x5)
          (ensures r.eq.op_Equals x1 x5)
  = trans3 r x1 x2 x3 x4; r.eq.transitivity x1 x4 x5

(* Derived ring lemmas *)
private let add_zero_r (#a:Type) (r: cr_eq a) (x: a)
  : Lemma (r.eq.op_Equals (r.add x r.zero) x)
  = r.add_comm x r.zero; r.add_zero_l x;
    trans r (r.add x r.zero) (r.add r.zero x) x

private let mul_one_r (#a:Type) (r: cr_eq a) (x: a)
  : Lemma (r.eq.op_Equals (r.mul x r.one) x)
  = r.mul_comm x r.one; r.mul_one_l x;
    trans r (r.mul x r.one) (r.mul r.one x) x

private let mul_zero_r (#a:Type) (r: cr_eq a) (x: a)
  : Lemma (r.eq.op_Equals (r.mul x r.zero) r.zero)
  = r.mul_comm x r.zero; r.zero_mul_l x;
    trans r (r.mul x r.zero) (r.mul r.zero x) r.zero

private let neg_zero (#a:Type) (r: cr_eq a)
  : Lemma (r.eq.op_Equals (r.neg r.zero) r.zero)
  = r.add_zero_l (r.neg r.zero); r.add_neg_r r.zero;
    r.eq.symmetry (r.add r.zero (r.neg r.zero)) (r.neg r.zero);
    trans r (r.neg r.zero) (r.add r.zero (r.neg r.zero)) r.zero

private let neg_mul_r (#a:Type) (r: cr_eq a) (x y: a)
  : Lemma (r.eq.op_Equals (r.mul x (r.neg y)) (r.neg (r.mul x y)))
  = r.mul_comm x (r.neg y); r.neg_mul_l y x;
    r.mul_comm y x; r.neg_cong (r.mul y x) (r.mul x y);
    trans3 r (r.mul x (r.neg y)) (r.mul (r.neg y) x) 
             (r.neg (r.mul y x)) (r.neg (r.mul x y))

private let distrib_r (#a:Type) (r: cr_eq a) (x y z: a)
  : Lemma (r.eq.op_Equals (r.mul (r.add x y) z) (r.add (r.mul x z) (r.mul y z)))
  = r.mul_comm (r.add x y) z; r.distrib_l z x y;
    r.mul_comm z x; r.mul_comm z y;
    r.add_cong (r.mul z x) (r.mul z y) (r.mul x z) (r.mul y z);
    trans3 r (r.mul (r.add x y) z) (r.mul z (r.add x y)) 
             (r.add (r.mul z x) (r.mul z y)) (r.add (r.mul x z) (r.mul y z))

(* Negating a signed monomial *)
private let negate_sm_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (s: bool) (m: monom)
  : Lemma (r.eq.op_Equals (sm_denote r vm (not s, m)) (r.neg (sm_denote r vm (s, m))))
  = if s then r.eq.reflexivity (r.neg (monom_denote r vm m))
    else (r.double_neg (monom_denote r vm m);
          r.eq.symmetry (r.neg (r.neg (monom_denote r vm m))) (monom_denote r vm m))

(* Append preserves sum *)
private let rec canon_denote_append (#a:Type) (r: cr_eq a) (vm: vmap a) (c1 c2: canon)
  : Lemma (ensures r.eq.op_Equals (canon_denote r vm (c1 @ c2))
                                   (r.add (canon_denote r vm c1) (canon_denote r vm c2)))
          (decreases c1) =
  match c1 with
  | [] -> 
    r.add_zero_l (canon_denote r vm c2);
    r.eq.symmetry (r.add r.zero (canon_denote r vm c2)) (canon_denote r vm c2)
  | sm :: rest ->
    canon_denote_append r vm rest c2;
    let s = sm_denote r vm sm in
    let cr = canon_denote r vm rest in
    let cc = canon_denote r vm c2 in
    r.eq.reflexivity s;
    r.add_cong s (canon_denote r vm (rest @ c2)) s (r.add cr cc);
    r.add_assoc s cr cc;
    r.eq.symmetry (r.add (r.add s cr) cc) (r.add s (r.add cr cc));
    trans r (r.add s (canon_denote r vm (rest @ c2)))
           (r.add s (r.add cr cc))
           (r.add (r.add s cr) cc)

(* Negation distributes over canonical sums *)
private let rec negate_all_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (c: canon)
  : Lemma (ensures r.eq.op_Equals (r.neg (canon_denote r vm c))
                                   (canon_denote r vm (negate_all c)))
          (decreases c) =
  match c with
  | [] -> neg_zero r
  | (s, m) :: rest ->
    let sd_sm = sm_denote r vm (s, m) in
    let cd_rest = canon_denote r vm rest in
    r.neg_add sd_sm cd_rest;
    negate_all_correct r vm rest;
    negate_sm_correct r vm s m;
    r.eq.symmetry (sm_denote r vm (not s, m)) (r.neg sd_sm);
    r.eq.reflexivity (canon_denote r vm (negate_all rest));
    r.add_cong (r.neg cd_rest) (r.neg sd_sm) (canon_denote r vm (negate_all rest)) (sm_denote r vm (not s, m));
    r.add_comm (canon_denote r vm (negate_all rest)) (sm_denote r vm (not s, m));
    trans3 r (r.neg (r.add sd_sm cd_rest))
             (r.add (r.neg cd_rest) (r.neg sd_sm))
             (r.add (canon_denote r vm (negate_all rest)) (sm_denote r vm (not s, m)))
             (r.add (sm_denote r vm (not s, m)) (canon_denote r vm (negate_all rest)))

(* Sorted merge preserves product *)
private let rec monom_merge_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (m1 m2: monom)
  : Lemma (ensures r.eq.op_Equals (r.mul (monom_denote r vm m1) (monom_denote r vm m2))
                                   (monom_denote r vm (monom_merge m1 m2)))
          (decreases (length m1 +% length m2)) =
  match m1, m2 with
  | [], _ -> r.mul_one_l (monom_denote r vm m2)
  | _, [] -> mul_one_r r (monom_denote r vm m1)
  | i :: rest1, j :: rest2 ->
    let vi = vmap_lookup i vm in
    let vj = vmap_lookup j vm in
    let mr1 = monom_denote r vm rest1 in
    let mr2 = monom_denote r vm rest2 in
    let mm1 = monom_denote r vm m1 in
    let mm2 = monom_denote r vm m2 in
    if i <= j then begin
      monom_merge_correct r vm rest1 m2;
      r.mul_assoc vi mr1 mm2;
      r.eq.reflexivity vi;
      r.mul_cong vi (r.mul mr1 mm2) vi (monom_denote r vm (monom_merge rest1 m2));
      trans r (r.mul mm1 mm2) (r.mul vi (r.mul mr1 mm2))
             (r.mul vi (monom_denote r vm (monom_merge rest1 m2)))
    end else begin
      monom_merge_correct r vm m1 rest2;
      r.mul_assoc mm1 vj mr2;
      r.eq.symmetry (r.mul (r.mul mm1 vj) mr2) (r.mul mm1 (r.mul vj mr2));
      r.mul_comm mm1 vj;
      r.eq.reflexivity mr2;
      r.mul_cong (r.mul mm1 vj) mr2 (r.mul vj mm1) mr2;
      r.mul_assoc vj mm1 mr2;
      r.eq.reflexivity vj;
      r.mul_cong vj (r.mul mm1 mr2) vj (monom_denote r vm (monom_merge m1 rest2));
      trans4 r (r.mul mm1 mm2)
               (r.mul (r.mul mm1 vj) mr2)
               (r.mul (r.mul vj mm1) mr2)
               (r.mul vj (r.mul mm1 mr2))
               (r.mul vj (monom_denote r vm (monom_merge m1 rest2)))
    end

(* Signed monomial multiplication *)
private let sm_mul_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (sm1 sm2: signed_monom)
  : Lemma (r.eq.op_Equals (r.mul (sm_denote r vm sm1) (sm_denote r vm sm2))
                           (sm_denote r vm (sm_mul sm1 sm2))) =
  let (s1, m1) = sm1 in
  let (s2, m2) = sm2 in
  let md1 = monom_denote r vm m1 in
  let md2 = monom_denote r vm m2 in
  let mdm = monom_denote r vm (monom_merge m1 m2) in
  monom_merge_correct r vm m1 m2;
  match s1, s2 with
  | true, true -> ()
  | true, false ->
    neg_mul_r r md1 md2;
    r.neg_cong (r.mul md1 md2) mdm;
    trans r (r.mul md1 (r.neg md2)) (r.neg (r.mul md1 md2)) (r.neg mdm)
  | false, true ->
    r.neg_mul_l md1 md2;
    r.neg_cong (r.mul md1 md2) mdm;
    trans r (r.mul (r.neg md1) md2) (r.neg (r.mul md1 md2)) (r.neg mdm)
  | false, false ->
    r.neg_mul_l md1 (r.neg md2);
    neg_mul_r r md1 md2;
    r.neg_cong (r.mul md1 (r.neg md2)) (r.neg (r.mul md1 md2));
    r.double_neg (r.mul md1 md2);
    trans4 r (r.mul (r.neg md1) (r.neg md2))
             (r.neg (r.mul md1 (r.neg md2)))
             (r.neg (r.neg (r.mul md1 md2)))
             (r.mul md1 md2)
             mdm

(* Cross product with one element *)
private let rec cross_one_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (sm: signed_monom) (c: canon)
  : Lemma (ensures r.eq.op_Equals (r.mul (sm_denote r vm sm) (canon_denote r vm c))
                                   (canon_denote r vm (cross_one sm c)))
          (decreases c) =
  match c with
  | [] -> mul_zero_r r (sm_denote r vm sm)
  | sm2 :: rest ->
    let sd = sm_denote r vm sm in
    let sd2 = sm_denote r vm sm2 in
    let cr = canon_denote r vm rest in
    r.distrib_l sd sd2 cr;
    sm_mul_correct r vm sm sm2;
    cross_one_correct r vm sm rest;
    r.add_cong (r.mul sd sd2) (r.mul sd cr) (sm_denote r vm (sm_mul sm sm2)) (canon_denote r vm (cross_one sm rest));
    trans r (r.mul sd (r.add sd2 cr))
           (r.add (r.mul sd sd2) (r.mul sd cr))
           (r.add (sm_denote r vm (sm_mul sm sm2)) (canon_denote r vm (cross_one sm rest)))

(* Full cross product *)
private let rec cross_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (c1 c2: canon)
  : Lemma (ensures r.eq.op_Equals (r.mul (canon_denote r vm c1) (canon_denote r vm c2))
                                   (canon_denote r vm (cross c1 c2)))
          (decreases c1) =
  match c1 with
  | [] -> r.zero_mul_l (canon_denote r vm c2)
  | sm :: rest ->
    let sd = sm_denote r vm sm in
    let cr = canon_denote r vm rest in
    let cc = canon_denote r vm c2 in
    distrib_r r sd cr cc;
    cross_one_correct r vm sm c2;
    cross_correct r vm rest c2;
    r.add_cong (r.mul sd cc) (r.mul cr cc) (canon_denote r vm (cross_one sm c2)) (canon_denote r vm (cross rest c2));
    canon_denote_append r vm (cross_one sm c2) (cross rest c2);
    r.eq.symmetry (canon_denote r vm (cross_one sm c2 @ cross rest c2))
                  (r.add (canon_denote r vm (cross_one sm c2)) (canon_denote r vm (cross rest c2)));
    trans3 r (r.mul (r.add sd cr) cc)
             (r.add (r.mul sd cc) (r.mul cr cc))
             (r.add (canon_denote r vm (cross_one sm c2)) (canon_denote r vm (cross rest c2)))
             (canon_denote r vm (cross_one sm c2 @ cross rest c2))

(* Expansion preserves denotation *)
let rec expand_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (e: rexp)
  : Lemma (ensures r.eq.op_Equals (rdenote r vm e) (canon_denote r vm (expand e)))
          (decreases e) =
  match e with
  | RZero -> r.eq.reflexivity r.zero
  | ROne ->
    add_zero_r r r.one;
    r.eq.symmetry (r.add r.one r.zero) r.one
  | RAtom i ->
    let vi = vmap_lookup i vm in
    mul_one_r r vi;
    r.eq.symmetry (r.mul vi r.one) vi;
    add_zero_r r (r.mul vi r.one);
    r.eq.symmetry (r.add (r.mul vi r.one) r.zero) (r.mul vi r.one);
    trans r vi (r.mul vi r.one) (r.add (r.mul vi r.one) r.zero)
  | RAdd e1 e2 ->
    expand_correct r vm e1; expand_correct r vm e2;
    r.add_cong (rdenote r vm e1) (rdenote r vm e2) (canon_denote r vm (expand e1)) (canon_denote r vm (expand e2));
    canon_denote_append r vm (expand e1) (expand e2);
    r.eq.symmetry (canon_denote r vm (expand e1 @ expand e2))
                  (r.add (canon_denote r vm (expand e1)) (canon_denote r vm (expand e2)));
    trans r (r.add (rdenote r vm e1) (rdenote r vm e2))
           (r.add (canon_denote r vm (expand e1)) (canon_denote r vm (expand e2)))
           (canon_denote r vm (expand e1 @ expand e2))
  | RNeg e1 ->
    expand_correct r vm e1;
    r.neg_cong (rdenote r vm e1) (canon_denote r vm (expand e1));
    negate_all_correct r vm (expand e1);
    trans r (r.neg (rdenote r vm e1)) (r.neg (canon_denote r vm (expand e1)))
           (canon_denote r vm (negate_all (expand e1)))
  | RMul e1 e2 ->
    expand_correct r vm e1; expand_correct r vm e2;
    r.mul_cong (rdenote r vm e1) (rdenote r vm e2) (canon_denote r vm (expand e1)) (canon_denote r vm (expand e2));
    cross_correct r vm (expand e1) (expand e2);
    trans r (r.mul (rdenote r vm e1) (rdenote r vm e2))
           (r.mul (canon_denote r vm (expand e1)) (canon_denote r vm (expand e2)))
           (canon_denote r vm (cross (expand e1) (expand e2)))

(* Insertion preserves sum *)
private let rec insert_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (sm: signed_monom) (c: canon)
  : Lemma (ensures r.eq.op_Equals (canon_denote r vm (insert_sm sm c))
                                   (r.add (sm_denote r vm sm) (canon_denote r vm c)))
          (decreases c) =
  match c with
  | [] -> r.eq.reflexivity (r.add (sm_denote r vm sm) r.zero)
  | sm2 :: rest ->
    if sm_leq sm sm2 then
      r.eq.reflexivity (r.add (sm_denote r vm sm) (canon_denote r vm (sm2 :: rest)))
    else begin
      insert_correct r vm sm rest;
      let s = sm_denote r vm sm in
      let s2 = sm_denote r vm sm2 in
      let cr = canon_denote r vm rest in
      r.eq.reflexivity s2;
      r.add_cong s2 (canon_denote r vm (insert_sm sm rest)) s2 (r.add s cr);
      r.add_assoc s2 s cr;
      r.eq.symmetry (r.add (r.add s2 s) cr) (r.add s2 (r.add s cr));
      r.add_comm s2 s;
      r.eq.reflexivity cr;
      r.add_cong (r.add s2 s) cr (r.add s s2) cr;
      r.add_assoc s s2 cr;
      trans4 r (r.add s2 (canon_denote r vm (insert_sm sm rest)))
               (r.add s2 (r.add s cr))
               (r.add (r.add s2 s) cr)
               (r.add (r.add s s2) cr)
               (r.add s (r.add s2 cr))
    end

(* Insertion sort preserves sum *)
private let rec isort_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (c: canon)
  : Lemma (ensures r.eq.op_Equals (canon_denote r vm (isort c)) (canon_denote r vm c))
          (decreases c) =
  match c with
  | [] -> r.eq.reflexivity r.zero
  | sm :: rest ->
    isort_correct r vm rest;
    insert_correct r vm sm (isort rest);
    r.eq.reflexivity (sm_denote r vm sm);
    r.add_cong (sm_denote r vm sm) (canon_denote r vm (isort rest)) (sm_denote r vm sm) (canon_denote r vm rest);
    r.eq.symmetry (r.add (sm_denote r vm sm) (canon_denote r vm rest))
                  (r.add (sm_denote r vm sm) (canon_denote r vm (isort rest)));
    trans r (canon_denote r vm (insert_sm sm (isort rest)))
           (r.add (sm_denote r vm sm) (canon_denote r vm (isort rest)))
           (r.add (sm_denote r vm sm) (canon_denote r vm rest))

(* Full normalization preserves denotation *)
let normalize_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (e: rexp)
  : Lemma (r.eq.op_Equals (rdenote r vm e) (canon_denote r vm (normalize e))) =
  expand_correct r vm e;
  isort_correct r vm (expand e);
  r.eq.symmetry (canon_denote r vm (isort (expand e))) (canon_denote r vm (expand e));
  trans r (rdenote r vm e) (canon_denote r vm (expand e)) (canon_denote r vm (isort (expand e)))

(* ================================================================== *)
(*  Part E: Reflection lemma                                          *)
(* ================================================================== *)

let ring_reflect (#a:Type) (r: cr_eq a) (vm: vmap a) (e1 e2: rexp)
  : Lemma (requires normalize e1 == normalize e2)
          (ensures r.eq.op_Equals (rdenote r vm e1) (rdenote r vm e2)) =
  normalize_correct r vm e1;
  normalize_correct r vm e2;
  r.eq.symmetry (rdenote r vm e2) (canon_denote r vm (normalize e2));
  trans r (rdenote r vm e1) (canon_denote r vm (normalize e1)) (rdenote r vm e2)

(* ================================================================== *)
(*  Part F: comm_ring_to_cr_eq constructor                             *)
(* ================================================================== *)

open FStar.CAS.Ringlikes

private let neg_cong_from_group (#t:Type) {| r: ring t |} (x y: t)
  : Lemma (requires x = y) (ensures -x = -y) =
  let ha : has_add t = FStar.Tactics.Typeclasses.solve in
  ring_neg_x_is_minus_one_times_x x;
  ring_neg_x_is_minus_one_times_x y;
  ha.eq.reflexivity (-(one #t));
  ha.eq.symmetry (-(one #t)) (-(one #t));
  let hm : has_mul t = FStar.Tactics.Typeclasses.solve in
  hm.congruence (-one) x (-one) y;
  ha.eq.symmetry (-y) ((-one)*y);
  ha.eq.transitivity (-x) ((-one)*x) ((-one)*y);
  ha.eq.transitivity (-x) ((-one)*y) (-y)

let comm_ring_to_cr_eq (#t:Type) {| cr: commutative_ring t |} : cr_eq t =
  let ha : has_add t = FStar.Tactics.Typeclasses.solve in
  let hm : has_mul t = FStar.Tactics.Typeclasses.solve in
  let e  : equatable t = ha.eq in
  let sg : add_semigroup t = FStar.Tactics.Typeclasses.solve in
  let am : add_monoid t = FStar.Tactics.Typeclasses.solve in
  let ag : add_group t = FStar.Tactics.Typeclasses.solve in
  let acm : add_comm_monoid t = FStar.Tactics.Typeclasses.solve in
  let mm : mul_monoid t = FStar.Tactics.Typeclasses.solve in
  let mcm : mul_comm_monoid t = FStar.Tactics.Typeclasses.solve in
  let sr : semiring t = FStar.Tactics.Typeclasses.solve in
  let rr : ring t = FStar.Tactics.Typeclasses.solve in
  {
    eq = e;
    add = ha.op_Plus;
    mul = hm.op_Star;
    neg = ag.has_neg.op_Minus;
    zero = am.has_zero.zero;
    one = mm.has_one.one;
    add_assoc = (fun x y z -> sg.associativity x y z);
    add_comm  = (fun x y ->
      acm.add_comm_semigroup.add_comm_magma.add_commutativity x y);
    add_zero_l = (fun x -> am.left_add_identity x);
    add_neg_r  = (fun x -> ag.negation x);
    add_cong   = (fun x y z w -> ha.congruence x y z w);
    neg_cong   = (fun x y -> neg_cong_from_group #t #rr x y);
    mul_assoc  = (fun x y z -> mm.mul_semigroup.associativity x y z);
    mul_comm   = (fun x y ->
      mcm.mul_comm_semigroup.mul_comm_magma.mul_commutativity x y);
    mul_one_l  = (fun x -> mm.left_mul_identity x);
    mul_cong   = (fun x y z w -> hm.congruence x y z w);
    distrib_l  = (fun x y z -> sr.left_distributivity x y z);
    zero_mul_l = (fun x -> sr.left_absorption x);
    neg_mul_l  = (fun x y ->
      ring_neg_xy_is_neg_x_times_y #t #rr x y;
      e.symmetry (-(x * y)) ((-x) * y));
    neg_add    = (fun x y -> neg_of_sum #t #ag x y);
    double_neg = (fun x -> double_negation_lemma #t #ag x);
  }

(* ================================================================== *)
(*  Part G: Tests                                                      *)
(* ================================================================== *)

(* Right distributivity: (a + b) * c = a*c + b*c *)
let test_distrib_r (#t:Type) {| cr: commutative_ring t |} (a b c: t)
  : Lemma ((a + b) * c = a * c + b * c) =
  let r = comm_ring_to_cr_eq #t #cr in
  let vm : vmap t = ([(0, a); (1, b); (2, c)], a) in
  let e1 = RMul (RAdd (RAtom 0) (RAtom 1)) (RAtom 2) in
  let e2 = RAdd (RMul (RAtom 0) (RAtom 2)) (RMul (RAtom 1) (RAtom 2)) in
  assert (normalize e1 == normalize e2) by (FStar.Tactics.V2.norm [delta; zeta; iota; primops]);
  ring_reflect r vm e1 e2

(* FOIL: (a + b) * (c + d) = a*c + a*d + b*c + b*d *)
let test_foil (#t:Type) {| cr: commutative_ring t |} (a b c d: t)
  : Lemma ((a + b) * (c + d) = a*c + a*d + (b*c + b*d)) =
  let r = comm_ring_to_cr_eq #t #cr in
  let vm : vmap t = ([(0, a); (1, b); (2, c); (3, d)], a) in
  let e1 = RMul (RAdd (RAtom 0) (RAtom 1)) (RAdd (RAtom 2) (RAtom 3)) in
  let e2 = RAdd (RAdd (RMul (RAtom 0) (RAtom 2)) (RMul (RAtom 0) (RAtom 3)))
               (RAdd (RMul (RAtom 1) (RAtom 2)) (RMul (RAtom 1) (RAtom 3))) in
  assert (normalize e1 == normalize e2) by (FStar.Tactics.V2.norm [delta; zeta; iota; primops]);
  ring_reflect r vm e1 e2

(* Commutativity of addition: a + b = b + a *)
let test_add_comm (#t:Type) {| cr: commutative_ring t |} (a b: t)
  : Lemma (a + b = b + a) =
  let r = comm_ring_to_cr_eq #t #cr in
  let vm : vmap t = ([(0, a); (1, b)], a) in
  let e1 = RAdd (RAtom 0) (RAtom 1) in
  let e2 = RAdd (RAtom 1) (RAtom 0) in
  assert (normalize e1 == normalize e2) by (FStar.Tactics.V2.norm [delta; zeta; iota; primops]);
  ring_reflect r vm e1 e2

(* Commutativity of multiplication: a * b = b * a *)
let test_mul_comm (#t:Type) {| cr: commutative_ring t |} (a b: t)
  : Lemma (a * b = b * a) =
  let r = comm_ring_to_cr_eq #t #cr in
  let vm : vmap t = ([(0, a); (1, b)], a) in
  let e1 = RMul (RAtom 0) (RAtom 1) in
  let e2 = RMul (RAtom 1) (RAtom 0) in
  assert (normalize e1 == normalize e2) by (FStar.Tactics.V2.norm [delta; zeta; iota; primops]);
  ring_reflect r vm e1 e2
