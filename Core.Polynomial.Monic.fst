module Core.Polynomial.Monic

(* ================================================================ *)
(*  Monic polynomials over a GENERAL commutative ring.               *)
(*                                                                   *)
(*  The coefficient ring is only assumed `commutative_ring` (it may  *)
(*  have zero divisors, e.g. zmod (p^k)).  Monicity — the leading    *)
(*  coefficient being the unit `one` — is what rescues the degree    *)
(*  and cancellation arguments that would otherwise require an        *)
(*  integral domain:                                                 *)
(*    - the top convolution coefficient of  a * b  is  lc a * lc b,  *)
(*      and for monic a this is  one * lc b = lc b <> zero, so the   *)
(*      product does not shrink at the top;                          *)
(*    - hence deg(a*b) = deg a + deg b and lc(a*b) = lc b (M1);      *)
(*    - and a*b = a*c forces b = c by a degree contradiction (M2).   *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Coeff
open Core.FinSum
open Core.Polynomial.Unique

(* ---------------------------------------------------------------- *)
(*  The monic predicate.  A plain, non-opaque conjunction.           *)
(* ---------------------------------------------------------------- *)

let monic (#t:Type) {| cr: commutative_ring t |} (a: polynomial t) : prop =
  deg a >= 0 /\ (poly_lc a = one)

(* deg / leading-coefficient of poly_one over a nontrivial CR. *)
let one_deg_lc (#t:Type) {| cr: commutative_ring t |}
  (nz: squash (not (one #t = (zero <: t))))
  : Lemma (deg (poly_one #t) == 0 /\ poly_lc (poly_one #t) = one)
  = H.elim_equatable_laws t ();
    poly_lc_reveal (poly_one #t)

(* poly_one is monic (nontrivial CR). *)
let monic_one (#t:Type) {| cr: commutative_ring t |}
  (nz: squash (not (one #t = (zero <: t))))
  : Lemma (monic (poly_one #t))
  = one_deg_lc #t nz

(* For a monic pair of equal degree, at any index at or above that degree
   the difference of coefficients vanishes (both leading `one`s cancel). *)
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let sub_high_coeff_zero (#t:Type) {| cr: commutative_ring t |}
  (g1 g2: polynomial t) (i:nat)
  : Lemma (requires monic g1 /\ monic g2 /\ deg g1 == deg g2 /\ i >= deg g1)
          (ensures  coeff (g2 -- g1) i = (zero <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let d = deg g1 in
    poly_sub_coeff g2 g1 i;                         (* coeff (g2--g1) i = coeff g2 i + (- coeff g1 i) *)
    (if i = d then begin
       last_eq_index g1 d; poly_lc_reveal g1;       (* coeff g1 d = one *)
       last_eq_index g2 d; poly_lc_reveal g2;       (* coeff g2 d = one *)
       symmetry (coeff g1 i) one;                   (* one = coeff g1 i *)
       transitivity (coeff g2 i) one (coeff g1 i)   (* coeff g2 i = coeff g1 i *)
     end else begin
       coeff_above_degree g1 i;                     (* coeff g1 i = zero (i > deg g1) *)
       coeff_above_degree g2 i;                     (* coeff g2 i = zero (i > deg g2 = deg g1) *)
       symmetry (coeff g1 i) zero;                  (* zero = coeff g1 i *)
       transitivity (coeff g2 i) zero (coeff g1 i)  (* coeff g2 i = coeff g1 i *)
     end);
    assert (coeff g2 i = coeff g1 i);
    H.sub_self_zero (coeff g2 i) (coeff g1 i);       (* (coeff g2 i -- coeff g1 i) = zero *)
    transitivity (coeff (g2 -- g1) i)
                 ((coeff g2 i) + (- (coeff g1 i)))
                 (zero <: t)

(* Hence the difference of an equal-degree monic pair drops strictly in degree. *)
let deg_sub_lt_of_monic_pair (#t:Type) {| cr: commutative_ring t |}
  (g1 g2: polynomial t)
  : Lemma (requires monic g1 /\ monic g2 /\ deg g1 == deg g2)
          (ensures  deg (g2 -- g1) < deg g1)
  = H.elim_equatable_laws t ();
    let q = g2 -- g1 in
    let d = deg g1 in
    if deg q >= d then begin
      leading_coeff_nonzero q;                       (* deg q >= d >= 0 ⇒ coeff q (deg q) ≠ zero *)
      let i : nat = deg q in
      sub_high_coeff_zero g1 g2 i                    (* coeff q i = zero — contradiction *)
    end else ()
#pop-options

(* ================================================================ *)
(*  Convolution: top coefficient of a product (CR-general).          *)
(*                                                                   *)
(*  coeff (a*b) (deg a + deg b) = lc a * lc b.                       *)
(*                                                                   *)
(*  This is the coefficient computation extracted from the           *)
(*  integral-domain lemma Core.Polynomial.Roots.poly_lc_mul, with    *)
(*  the id-locked `deg_mul` step removed: we do NOT claim the        *)
(*  product's degree here, only the value of the (deg a + deg b)     *)
(*  coefficient, which needs no domain hypothesis.                   *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
private
let coeff_mul_top (#t:Type) {| cr: commutative_ring t |} (a b: polynomial t)
  : Lemma (requires deg a >= 0 /\ deg b >= 0)
          (ensures  coeff (a * b) (deg a ++ deg b) = poly_lc a * poly_lc b)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let da = deg a in
    let db = deg b in
    let k : nat = da ++ db in
    let m = a * b in
    let g (i:nat) : t = coeff a i * coeff b ((k - i)) in
    coeff_poly_mul_named a b k g H.obvious;         (* coeff m k = sum_range g 0 (length a) *)
    assert (L.length a == (da ++ 1));
    sum_range_split g 0 da (da ++ 1);               (* sum 0 (da+1) = sum 0 da + sum da (da+1) *)
    sum_range_singleton g da;                       (* sum da (da+1) = g da *)
    let hz (i:nat{0 <= i /\ i < da}) : Lemma (g i = zero) =
      coeff_above_degree b ((k - i));               (* k-i = da+db-i > db, so coeff b (k-i) = 0 *)
      mul_congruence (coeff a i) (coeff b ((k - i))) (coeff a i) zero;
      H.x_mul_zero (coeff a i)
    in
    sum_range_all_zero g 0 da hz;                    (* sum 0 da = zero *)
    add_congruence (sum_range g 0 da) (sum_range g da (da ++ 1))
                   zero (sum_range g da (da ++ 1));
    H.zero_plus_x (sum_range g da (da ++ 1));        (* coeff m k = g da *)
    last_eq_index a da; poly_lc_reveal a;
    last_eq_index b db; poly_lc_reveal b;
    assert (coeff a da == poly_lc a);
    assert (coeff b ((k - da)) == poly_lc b);        (* k - da = db *)
    assert (g da == poly_lc a * poly_lc b)
#pop-options

(* ================================================================ *)
(*  Convolution: coefficients strictly above deg a + deg b vanish.   *)
(*  (CR-general.)  Every convolution term has a factor read past a    *)
(*  polynomial's degree, hence zero.                                 *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
private
let coeff_mul_above (#t:Type) {| cr: commutative_ring t |} (a b: polynomial t) (k: nat)
  : Lemma (requires deg a >= 0 /\ deg b >= 0 /\ k > deg a ++ deg b)
          (ensures  coeff (a * b) k = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let da = deg a in
    let db = deg b in
    let g (i:nat) : t = coeff a i * coeff b ((k - i)) in
    coeff_poly_mul_named a b k g H.obvious;          (* coeff (a*b) k = sum_range g 0 (length a) *)
    let hz (i:nat{0 <= i /\ i < L.length a}) : Lemma (g i = zero) =
      (* i <= da, so k - i >= k - da > db, hence coeff b (k-i) = 0 *)
      coeff_above_degree b ((k - i));
      mul_congruence (coeff a i) (coeff b ((k - i))) (coeff a i) zero;
      H.x_mul_zero (coeff a i)
    in
    sum_range_all_zero g 0 (L.length a) hz
#pop-options

(* ================================================================ *)
(*  M1 — monic degree/leading-coefficient of a product.              *)
(*                                                                   *)
(*  For monic a and any b with deg b >= 0:                           *)
(*     deg (a*b) = deg a + deg b   and   lc (a*b) = lc b.            *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let monic_deg_mul (#t:Type) {| cr: commutative_ring t |} (a b: polynomial t)
  : Lemma (requires monic a /\ deg b >= 0)
          (ensures  deg (a * b) == deg a ++ deg b /\
                    (poly_lc (a * b) = poly_lc b))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let da = deg a in
    let db = deg b in
    let k : nat = da ++ db in
    let m = a * b in
    (* coeff m k = lc a * lc b = one * lc b = lc b *)
    coeff_mul_top a b;                               (* coeff m k = poly_lc a * poly_lc b *)
    mul_congruence (poly_lc a) (poly_lc b) one (poly_lc b);   (* lc a = one *)
    H.one_mul_x (poly_lc b);                         (* one * lc b = lc b *)
    (* coeff m k = poly_lc b, and lc b <> zero (leading_coeff_nonzero) *)
    leading_coeff_nonzero b;                         (* not (coeff b db = zero) *)
    last_eq_index b db; poly_lc_reveal b;            (* coeff b db == poly_lc b *)
    assert (coeff b db == poly_lc b);
    assert (not (poly_lc b = zero));
    assert (coeff m k = poly_lc b);
    assert (not (coeff m k = zero));
    (* Lower bound: coeff m k <> 0 forces deg m >= k. *)
    Classical.move_requires (coeff_above_degree m) k;
    assert (deg m >= k);
    (* Upper bound: any coefficient above k vanishes, so deg m <= k. *)
    let _ : squash (deg m <= k) =
      if deg m > k then (
        leading_coeff_nonzero m;                     (* coeff m (deg m) <> zero *)
        coeff_mul_above a b (deg m)                  (* but deg m > k => coeff m (deg m) = zero *)
      ) else ()
    in
    assert (deg m == k);
    (* lc m = coeff m (deg m) = coeff m k = lc b *)
    last_eq_index m k; poly_lc_reveal m;
    assert (poly_lc m == coeff m k)
#pop-options

(* ================================================================ *)
(*  M2 — monic multiplicative cancellation.                          *)
(*                                                                   *)
(*     monic a  /\  a*b = a*c   ==>   b = c.                         *)
(*                                                                   *)
(*  Let d = b - c.  Then a*d = a*b - a*c = 0 (distributivity +       *)
(*  a*b = a*c).  If deg d >= 0, M1 gives deg(a*d) = deg a + deg d    *)
(*  >= 0, contradicting deg(a*d) = deg 0 = -1.  Hence d = 0, i.e.    *)
(*  b = c by additive cancellation.                                  *)
(* ================================================================ *)

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
let monic_mul_cancel (#t:Type) {| cr: commutative_ring t |} (a b c: polynomial t)
  : Lemma (requires monic a /\ (a * b) = (a * c))
          (ensures  b = c)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    poly_mul_sub_distrib a b c;                      (* a*(b--c) = (a*b) -- (a*c) *)
    H.sub_self_zero (a * b) (a * c);                 (* (a*b) -- (a*c) = poly_zero *)
    let _ : squash (deg (b -- c) < 0) =
      if deg (b -- c) >= 0 then (
        monic_deg_mul a (b -- c);                    (* deg(a*(b--c)) = deg a + deg(b--c) >= 0 *)
        degree_well_defined (a * (b -- c)) (poly_zero #t)  (* = deg poly_zero = -1: contradiction *)
      ) else ()
    in
    degree_none_poly_eq_zero (b -- c);               (* b -- c = poly_zero *)
    sub_zero_implies_eq b c                           (* b = c *)
#pop-options
