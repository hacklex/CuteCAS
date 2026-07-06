module Core.Risch.RationalSound

(* ================================================================ *)
(*  §F — rational-integrator soundness, the POLYNOMIAL part.         *)
(*                                                                   *)
(*  First the foundational compatibility (deferred in               *)
(*  Core.Fractions.Derivative):  on embedded polynomials the         *)
(*  rational derivative IS the polynomial derivative —               *)
(*     rational_deriv (p/1)  =  (poly_deriv p)/1.                     *)
(*                                                                   *)
(*  Then the polynomial-part soundness of the rational integrator:   *)
(*     rational_deriv (∫quot / 1)  =  quot / 1                        *)
(*  (the integrator's `poly_part = antideriv quot`, now proven        *)
(*  `D(∫p)=p` via Core.Risch.PolyAntideriv.antideriv_correct).        *)
(*                                                                   *)
(*  NO admit / assume / sorry in the final version.                  *)
(* ================================================================ *)

module H  = Core.Algebra.Helpers
module PA = Core.Risch.PolyAntideriv

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Derivative
open Core.Fractions
open Core.Fractions.Derivative
open Core.Risch.Hermite

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------- *)
(*  Generic-ring helper: the cross-multiplication obligation that    *)
(*  fraction_eq_reveal produces for rational_deriv (p/1) = p'/1.      *)
(*  With a = p', b = p (raw poly), one/zero the ring unit/zero:       *)
(*     ((a * one) -- (b * zero)) * one  =  (one * one) * a.           *)
(*  Both sides reduce to `a`.                                         *)
(* ---------------------------------------------------------------- *)
let cross_one (#t:Type) {| cr: commutative_ring t |} (a b: t)
  : Lemma ((((a * one) -- (b * zero)) * one) = ((one * one) * a))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    (* RHS:  (one * one) * a  =  one * a  =  a *)
    H.x_mul_one (one #t);                 (* one * one = one *)
    mul_congruence (one * one) a (one #t) a;   (* (one*one)*a = one*a *)
    H.one_mul_x a;                        (* one * a = a *)
    (* inner sub:  (a * one) -- (b * zero) = a *)
    H.x_mul_one a;                        (* a * one = a *)
    H.x_mul_zero b;                       (* b * zero = zero *)
    H.neg_of_zero (b * zero);             (* neg (b*zero) = zero *)
    (* (a*one) -- (b*zero) = (a*one) + neg(b*zero) = a + zero = a *)
    add_congruence (a * one) ((- (b * zero))) a (zero #t);
                                          (* (a*one)+neg(b*zero) = a + zero *)
    H.x_plus_zero a;                      (* a + zero = a *)
    (* LHS:  inner * one = a * one = a *)
    mul_congruence ((a * one) -- (b * zero)) (one #t) a (one #t)
                                          (* inner*one = a*one *)

(* COMPATIBILITY:  rational_deriv (p/1) = (poly_deriv p)/1. *)
let poly_to_rational_deriv (#t:Type) {| f: field t |} (p: polynomial t)
  : Lemma (rational_deriv (poly_to_rational p)
           = poly_to_rational (poly_deriv p))
  = let p' : polynomial t = poly_deriv p in
    let lhs : rational_function f = rational_deriv (poly_to_rational p) in
    let rhs : rational_function f = poly_to_rational p' in
    (* poly_deriv of poly_one is poly_zero (poly_one has length <= 1). *)
    poly_deriv_const (poly_one #t);
    (* reveal num/den of the rational derivative of p/1. *)
    rational_deriv_reveal (poly_to_rational p);
    (* the cross-product obligation collapses by the generic ring identity. *)
    cross_one p' p;
    (* bridge the published fraction `=` to the cross product. *)
    fraction_eq_reveal lhs rhs

(* ---------------------------------------------------------------- *)
(*  Generic-ring helper: the cross-multiplication obligation for the  *)
(*  poly_to_rational congruence  (a = b  ==>  a/1 = b/1):             *)
(*     a = b  ==>  a * one  =  one * b.                               *)
(* ---------------------------------------------------------------- *)
let cross_cong (#t:Type) {| cr: commutative_ring t |} (a b: t)
  : Lemma (requires a = b)
          (ensures (a * one) = (one * b))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    H.x_mul_one a;                        (* a * one = a *)
    H.one_mul_x b                          (* one * b = b *)

(* poly_to_rational respects polynomial equality. *)
let poly_to_rational_cong (#t:Type) {| f: field t |} (a b: polynomial t)
  : Lemma (requires a = b)
          (ensures poly_to_rational a = poly_to_rational b)
  = cross_cong a b;
    fraction_eq_reveal
      (poly_to_rational a) (poly_to_rational b)

(* POLYNOMIAL-PART SOUNDNESS:  rational_deriv (∫quot / 1) = quot / 1. *)
let poly_part_correct (#t:Type) {| f: field t |} (quot: polynomial t)
  : Lemma (requires char_zero f)
          (ensures rational_deriv (poly_to_rational (PA.antideriv quot))
                   = poly_to_rational quot)
  = let g : polynomial t = PA.antideriv quot in
    let dg : polynomial t = poly_deriv g in
    (* rational_deriv (g/1) = (poly_deriv g)/1 *)
    poly_to_rational_deriv g;
    (* poly_deriv g = poly_deriv (antideriv quot)  poly_eq  quot *)
    PA.antideriv_correct quot;
    (* hence (poly_deriv g)/1 = quot/1 *)
    poly_to_rational_cong dg quot;
    (* transitivity of the published fraction `=` *)
    H.elim_equatable_laws (rational_function f) ();
    H.trans_for_calc (rational_function f) ();
    transitivity
      (rational_deriv (poly_to_rational g))
      (poly_to_rational dg)
      (poly_to_rational quot)
