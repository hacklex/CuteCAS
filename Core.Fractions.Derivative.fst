module Core.Fractions.Derivative

(*
   Quotient-rule derivative for rational functions (fraction of polynomials).

   Given a polynomial p/q over a field t, the derivative is:
     D(p/q) = (p'·q - p·q') / q²

   This module provides:
     - `rational_deriv`: the concrete quotient-rule function
     - `rational_deriv_reveal`: reveals the numerator/denominator formula
     - `den_squared_nonzero`: q ≠ 0 → q² ≠ 0 (integral domain property)

   The soundness theorem for the Risch algorithm states:
     "The returned g satisfies D(g) = f"
   where D is this rational_deriv.
*)

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Derivative
open Core.Fractions

(* ================================================================ *)
(*  Helper: q*q is nonzero when q is nonzero (integral domain)      *)
(* ================================================================ *)

let den_squared_nonzero (#t:Type) {| f: field t |}
  (q: polynomial t)
  (h: squash (is_nonzero q))
  : Lemma (is_nonzero (q * q))
  = let id_p : integral_domain (polynomial t) =
      polynomial_id #t #(id_of_f t) in
    id_p.id_d.domain_law q q

(* ================================================================ *)
(*  The rational derivative function                                *)
(* ================================================================ *)

(* Type abbreviation for fraction of polynomials over a field t *)
let rational_function (#t:Type) (f: field t)
  = fraction (polynomial_id #t #(id_of_f t))

let rational_deriv (#t:Type) {| f: field t |}
  (x: rational_function f)
  : rational_function f
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let id_p = polynomial_id #t #(id_of_f t) in
    let p : polynomial t = Fraction?.num x in
    let q : polynomial t = Fraction?.den x in
    let p' = poly_deriv #t #cr p in
    let q' = poly_deriv #t #cr q in
    let num : polynomial t = ((p' * q) -- (p * q')) in
    let den : polynomial t = q * q in
    den_squared_nonzero q ();
    Fraction #(polynomial t) #id_p num den

(* ================================================================ *)
(*  Reveal lemma: D(p/q) = (p'q - pq') / q²                        *)
(* ================================================================ *)

let rational_deriv_reveal (#t:Type) {| f: field t |}
  (x: rational_function f)
  : Lemma (Fraction?.num (rational_deriv x)
             == ((poly_deriv #t #(cr_of_id t #(id_of_f t)) (Fraction?.num x)
                   * Fraction?.den x)
                 -- (Fraction?.num x
                       * poly_deriv #t #(cr_of_id t #(id_of_f t)) (Fraction?.den x))) /\
           Fraction?.den (rational_deriv x)
             == (Fraction?.den x * Fraction?.den x))
  = ()

(* ================================================================ *)
(*  Embedding: polynomial → rational function (as p/1)              *)
(* ================================================================ *)

let poly_to_rational (#t:Type) {| f: field t |}
  (p: polynomial t)
  : rational_function f
  = let id_p = polynomial_id #t #(id_of_f t) in
    polynomial_one_ne_zero #t #(id_of_f t);
    Fraction #(polynomial t) #id_p p poly_one

(* ================================================================ *)
(*  Compatibility: D(p/1) ~ poly_deriv(p) / 1                      *)
(*                                                                  *)
(*  For the Risch soundness theorem, the key property is that       *)
(*  rational_deriv agrees with poly_deriv on embedded polynomials.  *)
(*  Full proof deferred — requires showing poly_deriv(1) = 0 and    *)
(*  poly_mul_one identities at the fraction-equality level.         *)
(* ================================================================ *)
