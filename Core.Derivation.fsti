module Core.Derivation
(*
   Derivation structure for differential algebra.

   A derivation on a commutative ring R is a map D : R → R satisfying:
     1. D(a + b) = D(a) + D(b)           (additivity)
     2. D(a · b) = D(a)·b + a·D(b)       (Leibniz / product rule)
     3. D respects equality               (congruence)

   Derived properties (proven here):
     - D(0) = 0
     - D(-a) = -D(a)
     - D(1) = 0
     - D(a - b) = D(a) - D(b)

   This module provides:
     - `derivation_on` record type parameterized by a commutative_ring
     - Derived lemmas from the axioms
     - `poly_derivation`: standard d/dx on polynomial t (wraps poly_deriv)
*)

module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation

(* ================================================================ *)
(*  The derivation record                                           *)
(* ================================================================ *)

noeq type derivation_on (#t:Type) (cr: commutative_ring t) = {
  deriv: t -> t;
  deriv_congruence:
    (a: t) -> (b: t) ->
    Lemma (requires a = b) (ensures deriv a = deriv b);
  deriv_add:
    (a: t) -> (b: t) ->
    Lemma (ensures deriv (a + b) = deriv a + deriv b);
  deriv_leibniz:
    (a: t) -> (b: t) ->
    Lemma (ensures deriv (a * b) = deriv a * b + a * deriv b);
}

(* ================================================================ *)
(*  Derived properties                                              *)
(* ================================================================ *)

val deriv_zero (#t:Type) {| cr: commutative_ring t |}
  (d: derivation_on cr)
  : Lemma (d.deriv (zero <: t) = (zero <: t))

val deriv_neg (#t:Type) {| cr: commutative_ring t |}
  (d: derivation_on cr) (a: t)
  : Lemma (d.deriv (neg a) = neg (d.deriv a))

val deriv_one (#t:Type) {| cr: commutative_ring t |}
  (d: derivation_on cr)
  : Lemma (d.deriv (one <: t) = (zero <: t))

val deriv_sub (#t:Type) {| cr: commutative_ring t |}
  (d: derivation_on cr) (a b: t)
  : Lemma (d.deriv (a + neg b) = d.deriv a + neg (d.deriv b))

(* ================================================================ *)
(*  Polynomial derivation instance                                  *)
(* ================================================================ *)

open Core.Polynomial

val poly_derivation (#t:Type) {| cr: commutative_ring t |}
  : derivation_on (polynomial_commutative_ring_instance #t #cr).pcr
