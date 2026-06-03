module Core.Polynomial.CoprimeProduct

(* ================================================================ *)
(*  gcd distributes over products of pairwise-coprime polynomials:  *)
(*                                                                   *)
(*     coprime m n  ==>  gcd(f, m*n) ~ gcd(f,m) * gcd(f,n)           *)
(*                                                                   *)
(*  and the list form                                                *)
(*                                                                   *)
(*     pairwise-coprime ms ==> gcd(f, prod ms) ~ prod_i gcd(f, ms_i) *)
(*                                                                   *)
(*  Used to finish Berlekamp reverse splitting:                      *)
(*     f | prod_c (h-[c])   and the (h-[c]) pairwise coprime         *)
(*     ==>  prod_c gcd(f, h-[c]) ~ f.                                *)
(*                                                                   *)
(*  "~" here is the ASSOCIATE relation (mutual divisibility) in the  *)
(*  field-coefficient polynomial ring, NOT poly_eq.                  *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module PR = Core.Polynomial.Product
module SF = Core.Polynomial.SquareFree

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Tactics.CanonRing
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Irreducible

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------- *)
(*  L1.  a|m and b|n  ==>  (a*b)|(m*n).   [pure commutative_ring]    *)
(* ---------------------------------------------------------------- *)
let divides_mul_pair (#t:Type) {| cr: commutative_ring t |} (a b m n: t)
  : Lemma (requires divides a m /\ divides b n)
          (ensures  divides (mul a b) (mul m n))
  = eliminate exists (k:t). eq m (mul a k)
    returns divides (mul a b) (mul m n)
    with hk.
    eliminate exists (j:t). eq n (mul b j)
    returns divides (mul a b) (mul m n)
    with hj.
    begin
      mul_congruence m n (mul a k) (mul b j);
      assert (eq (mul (mul a k) (mul b j)) (mul (mul a b) (mul k j))) by canon_ring ();
      transitivity (mul m n) (mul (mul a k) (mul b j)) (mul (mul a b) (mul k j));
      divides_intro (mul a b) (mul m n) (mul k j)
    end

(* ---------------------------------------------------------------- *)
(*  L2.  coprime m n, a|m, b|n  ==>  coprime a b.                    *)
(* ---------------------------------------------------------------- *)
let coprime_both_divisors (#t:Type) {| f: field t |} (a b m n: polynomial t)
  : Lemma (requires coprime #t #f m n /\ divides a m /\ divides b n /\
                    Some? (poly_deg a) /\ Some? (poly_deg b))
          (ensures  coprime #t #f a b)
  = coprime_divisor #t #f m n a;       (* coprime a n *)
    coprime_of_divisor #t #f a n b     (* coprime a b *)

(* ---------------------------------------------------------------- *)
(*  L3.  a|ff, b|ff, coprime a b  ==>  (a*b)|ff.   [via euclid]      *)
(* ---------------------------------------------------------------- *)
let pcd2 (#t:Type) {| f: field t |} (a b ff: polynomial t)
  : Lemma (requires divides a ff /\ divides b ff /\ coprime #t #f a b /\
                    Some? (poly_deg a) /\ Some? (poly_deg b))
          (ensures  divides (poly_mul a b) ff)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    coprime_symmetric #t #f a b;                   (* coprime b a *)
    eliminate exists (k: polynomial t). eq ff (mul a k)
    returns divides (poly_mul a b) ff
    with hk.
    begin
      (* b | ff, ff ~ a*k ~ k*a  →  b | k*a *)
      divides_congruence_right #(polynomial t) #cr_p b ff (mul a k);
      mul_commutativity a k;
      divides_congruence_right #(polynomial t) #cr_p b (mul a k) (mul k a);
      (* coprime b a ∧ b | (k*a)  →  b | k *)
      euclid_lemma #t #f b a k;
      eliminate exists (j: polynomial t). eq k (mul b j)
      returns divides (poly_mul a b) ff
      with hj.
      begin
        (* ff ~ a*k ~ a*(b*j) ~ (a*b)*j *)
        reflexivity a;
        mul_congruence a k a (mul b j);
        transitivity ff (mul a k) (mul a (mul b j));
        mul_associativity a b j;
        symmetry (mul (mul a b) j) (mul a (mul b j));
        transitivity ff (mul a (mul b j)) (mul (mul a b) j);
        divides_intro #(polynomial t) #cr_p (mul a b) ff j
      end
    end

(* ---------------------------------------------------------------- *)
(*  L4 (crux).  Divisor splitting along a coprime product:           *)
(*     g | m*n   ==>   g | gcd(g,m) * gcd(g,n).                       *)
(*                                                                   *)
(*  Bezout for each gcd:  s*g + t*m ~ gcd(g,m),  s'*g + t'*n ~ gcd(g,n).  *)
(*  Their product expands into 4 terms; three carry a factor g, and  *)
(*  the fourth is (t*t')*(m*n) which g divides by hypothesis.        *)
(* ---------------------------------------------------------------- *)

(* abstract: (s*g+t*m)*(s'*g+t'*n) = g*(...) + (t*t')*(m*n). *)
let abstract_split_identity (#p:Type) {| pr: commutative_ring p |}
  (s t s' t' g m n: p)
  : Lemma ((s * g + t * m) * (s' * g + t' * n)
           = g * (s * (s' * g) + s * (t' * n) + t * (s' * m)) + (t * t') * (m * n))
  = assert ((s * g + t * m) * (s' * g + t' * n)
            = g * (s * (s' * g) + s * (t' * n) + t * (s' * m)) + (t * t') * (m * n))
      by canon_ring ()

let divisor_splits (#t:Type) {| f: field t |} (g m n: polynomial t)
  : Lemma (requires divides g (poly_mul m n))
          (ensures  divides g (poly_mul (poly_gcd #t #f g m) (poly_gcd #t #f g n)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) #(cr_p.cr_r.r_add.acg_eq) ();
    H.trans_for_calc (polynomial t) #(cr_p.cr_r.r_add.acg_eq) ();
    ext_gcd_correct #t #f g m; ext_gcd_is_gcd #t #f g m;
    ext_gcd_correct #t #f g n; ext_gcd_is_gcd #t #f g n;
    let (s,  tt,  gv ) = poly_ext_gcd #t #f g m in   (* s*g + tt*m ~ gv ~ gcd(g,m) *)
    let (s', tt', gv') = poly_ext_gcd #t #f g n in   (* s'*g + tt'*n ~ gv' ~ gcd(g,n) *)
    let gm = poly_gcd #t #f g m in
    let gn = poly_gcd #t #f g n in
    (* lhs := the product of the two Bezout sums *)
    let lhs = (s * g + tt * m) * (s' * g + tt' * n) in
    let xmid = s * (s' * g) + s * (tt' * n) + tt * (s' * m) in
    let rhs  = g * xmid + (tt * tt') * (m * n) in
    abstract_split_identity #(polynomial t) #cr_p s tt s' tt' g m n;  (* lhs = rhs *)
    (* g | rhs *)
    divides_refl #(polynomial t) #cr_p g;
    divides_mul_right #(polynomial t) #cr_p g g xmid;                 (* g | g*xmid *)
    divides_mul_left  #(polynomial t) #cr_p g (tt * tt') (m * n);     (* g | (tt*tt')*(m*n) *)
    divides_add #(polynomial t) #cr_p g (g * xmid) ((tt * tt') * (m * n));  (* g | rhs *)
    (* g | lhs  (rhs = lhs) *)
    symmetry lhs rhs;
    divides_congruence_right #(polynomial t) #cr_p g rhs lhs;          (* g | lhs *)
    (* lhs ~ gv*gv' ~ gm*gn *)
    mul_congruence (s * g + tt * m) (s' * g + tt' * n) gv gv';         (* lhs = gv*gv' *)
    mul_congruence gv gv' gm gn;                                       (* gv*gv' = gm*gn *)
    transitivity lhs (gv * gv') (gm * gn);                            (* lhs = gm*gn *)
    divides_congruence_right #(polynomial t) #cr_p g lhs (gm * gn)     (* g | gm*gn *)

(* ---------------------------------------------------------------- *)
(*  L5.  Two-factor distribution, "B" direction (UNCONDITIONAL):     *)
(*     gcd(f, m*n)  |  gcd(f,m) * gcd(f,n).                           *)
(* ---------------------------------------------------------------- *)
let gcd_mn_divides_prod (#t:Type) {| f: field t |} (ff m n: polynomial t)
  : Lemma (divides (poly_gcd #t #f ff (poly_mul m n))
                   (poly_mul (poly_gcd #t #f ff m) (poly_gcd #t #f ff n)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    let g = poly_gcd #t #f ff (poly_mul m n) in
    gcd_divides_left  #t #f ff (poly_mul m n);             (* g | ff *)
    gcd_divides_right #t #f ff (poly_mul m n);             (* g | m*n *)
    divisor_splits #t #f g m n;                            (* g | gcd(g,m)*gcd(g,n) *)
    gcd_divides_left  #t #f g m;                           (* gcd(g,m) | g *)
    gcd_divides_right #t #f g m;                           (* gcd(g,m) | m *)
    divides_trans #(polynomial t) #cr_p (poly_gcd #t #f g m) g ff;   (* gcd(g,m) | ff *)
    gcd_is_maximal #t #f ff m (poly_gcd #t #f g m);        (* gcd(g,m) | gcd(ff,m) *)
    gcd_divides_left  #t #f g n;
    gcd_divides_right #t #f g n;
    divides_trans #(polynomial t) #cr_p (poly_gcd #t #f g n) g ff;
    gcd_is_maximal #t #f ff n (poly_gcd #t #f g n);
    divides_mul_pair #(polynomial t) #cr_p
      (poly_gcd #t #f g m) (poly_gcd #t #f g n)
      (poly_gcd #t #f ff m) (poly_gcd #t #f ff n);
    divides_trans #(polynomial t) #cr_p g
      (poly_mul (poly_gcd #t #f g m) (poly_gcd #t #f g n))
      (poly_mul (poly_gcd #t #f ff m) (poly_gcd #t #f ff n))

(* ---------------------------------------------------------------- *)
(*  L6.  Two-factor distribution, "A" direction (needs coprimality): *)
(*     coprime m n  ==>  gcd(f,m) * gcd(f,n)  |  gcd(f, m*n).         *)
(* ---------------------------------------------------------------- *)
let prod_divides_gcd_mn (#t:Type) {| f: field t |} (ff m n: polynomial t)
  : Lemma (requires coprime #t #f m n /\ Some? (poly_deg ff))
          (ensures  divides (poly_mul (poly_gcd #t #f ff m) (poly_gcd #t #f ff n))
                            (poly_gcd #t #f ff (poly_mul m n)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    let a = poly_gcd #t #f ff m in
    let b = poly_gcd #t #f ff n in
    gcd_divides_left  #t #f ff m;   (* a | ff *)
    gcd_divides_right #t #f ff m;   (* a | m *)
    gcd_divides_left  #t #f ff n;   (* b | ff *)
    gcd_divides_right #t #f ff n;   (* b | n *)
    SF.gcd_has_degree #t #f ff m;   (* Some? deg a *)
    SF.gcd_has_degree #t #f ff n;   (* Some? deg b *)
    coprime_both_divisors #t #f a b m n;            (* coprime a b *)
    pcd2 #t #f a b ff;                              (* a*b | ff *)
    divides_mul_pair #(polynomial t) #cr_p a b m n; (* a*b | m*n *)
    gcd_is_maximal #t #f ff (poly_mul m n) (poly_mul a b)  (* a*b | gcd(ff,m*n) *)

(* ---------------------------------------------------------------- *)
(*  L7.  List form of L5 (UNCONDITIONAL):                            *)
(*     gcd(f, prod ms)  |  prod_i gcd(f, ms_i).                      *)
(*  Pure induction on the list using gcd_mn_divides_prod.            *)
(* ---------------------------------------------------------------- *)
let rec gcd_prod_divides_prod_gcd (#t:Type) {| f: field t |}
  (ff: polynomial t) (ms: list (polynomial t))
  : Lemma (ensures divides (poly_gcd #t #f ff (PR.poly_prod ms))
                           (PR.poly_prod (L.map (fun m -> poly_gcd #t #f ff m) ms)))
          (decreases ms)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    match ms with
    | [] ->
      (* poly_prod [] == poly_one ; map _ [] == [] ; gcd(ff,1) | 1 *)
      gcd_divides_right #t #f ff (poly_one #t)
    | x :: rest ->
      let pr = PR.poly_prod rest in
      let q  = PR.poly_prod (L.map (fun m -> poly_gcd #t #f ff m) rest) in
      gcd_mn_divides_prod #t #f ff x pr;            (* gcd(ff,x*pr) | gcd(ff,x)*gcd(ff,pr) *)
      gcd_prod_divides_prod_gcd #t #f ff rest;      (* IH: gcd(ff,pr) | q *)
      divides_refl #(polynomial t) #cr_p (poly_gcd #t #f ff x);
      divides_mul_pair #(polynomial t) #cr_p
        (poly_gcd #t #f ff x) (poly_gcd #t #f ff pr)
        (poly_gcd #t #f ff x) q;                    (* gcd(ff,x)*gcd(ff,pr) | gcd(ff,x)*q *)
      divides_trans #(polynomial t) #cr_p
        (poly_gcd #t #f ff (poly_mul x pr))
        (poly_mul (poly_gcd #t #f ff x) (poly_gcd #t #f ff pr))
        (poly_mul (poly_gcd #t #f ff x) q)

(* ---------------------------------------------------------------- *)
(*  L8 (capstone, direction B).  f | prod ms  ==>  f | prod gcd.     *)
(*     f | prod ms  ==>  f | gcd(f, prod ms)  (gcd_is_maximal+refl)  *)
(*                    |  prod_i gcd(f, ms_i)   (L7).                  *)
(* ---------------------------------------------------------------- *)
let f_divides_prod_gcd (#t:Type) {| f: field t |}
  (ff: polynomial t) (ms: list (polynomial t))
  : Lemma (requires divides ff (PR.poly_prod ms))
          (ensures  divides ff (PR.poly_prod (L.map (fun m -> poly_gcd #t #f ff m) ms)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    divides_refl #(polynomial t) #cr_p ff;
    gcd_is_maximal #t #f ff (PR.poly_prod ms) ff;     (* ff | gcd(ff, prod ms) *)
    gcd_prod_divides_prod_gcd #t #f ff ms;            (* gcd(ff, prod ms) | prod gcd *)
    divides_trans #(polynomial t) #cr_p ff
      (poly_gcd #t #f ff (PR.poly_prod ms))
      (PR.poly_prod (L.map (fun m -> poly_gcd #t #f ff m) ms))

(* ---------------------------------------------------------------- *)
(*  L9.  poly_prod respects pointwise poly_eq of equal-length lists. *)
(* ---------------------------------------------------------------- *)
let rec poly_prod_congr (#t:Type) {| cr: commutative_ring t |}
  (xs ys: list (polynomial t))
  : Lemma (requires L.length xs == L.length ys /\
                    (forall (i:nat). i < L.length xs ==>
                       poly_eq (L.index xs i) (L.index ys i)))
          (ensures  poly_eq (PR.poly_prod xs) (PR.poly_prod ys))
          (decreases xs)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) #(cr_p.cr_r.r_add.acg_eq) ();
    match xs, ys with
    | [], [] -> reflexivity #(polynomial t) #(cr_p.cr_r.r_add.acg_eq) (PR.poly_prod xs)
    | x :: xs', y :: ys' ->
      assert (poly_eq x y);
      let tail_hyp (i:nat{i < L.length xs'})
        : Lemma (poly_eq (L.index xs' i) (L.index ys' i))
        = assert (L.index xs (Prims.op_Addition i 1) == L.index xs' i);
          assert (L.index ys (Prims.op_Addition i 1) == L.index ys' i)
      in
      Classical.forall_intro tail_hyp;
      poly_prod_congr #t #cr xs' ys';
      poly_mul_congruence x (PR.poly_prod xs') y (PR.poly_prod ys')

(* ---------------------------------------------------------------- *)
(*  L10.  a coprime to each ms_i  ==>  a coprime to (prod ms).       *)
(*  (public poly_prod analogue of Irreducible.coprime_flat_product.) *)
(* ---------------------------------------------------------------- *)
#push-options "--z3rlimit 50 --fuel 3 --ifuel 2"
let rec coprime_to_prod (#t:Type) {| f: field t |}
  (a: polynomial t) (ds: list (polynomial t))
  : Lemma (requires Some? (poly_deg a) /\
                    (forall (k:nat). k < L.length ds ==> coprime #t #f a (L.index ds k)))
          (ensures  coprime #t #f a (PR.poly_prod ds))
          (decreases ds)
  = match ds with
    | [] ->
        coprime_reveal #t #f a (poly_one #t);
        SF.gcd_has_degree #t #f a (poly_one #t);
        gcd_divides_right #t #f a (poly_one #t);
        divides_degree_le (poly_gcd #t #f a (poly_one #t)) (poly_one #t)
    | d :: rest ->
        let tail_hyp (k:nat{k < L.length rest})
          : Lemma (coprime #t #f a (L.index rest k))
          = assert (L.index (d :: rest) (Prims.op_Addition k 1) == L.index rest k)
        in
        Classical.forall_intro tail_hyp;
        coprime_to_prod a rest;
        coprime_mul_right a d (PR.poly_prod rest)
#pop-options
