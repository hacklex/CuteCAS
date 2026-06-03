module Core.Derivation

module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Derivative

(* ================================================================ *)
(*  Derived property: D(0) = 0                                      *)
(*                                                                  *)
(*  Proof: D(0) = D(0+0) = D(0) + D(0). So D(0) = 0 by cancel.    *)
(* ================================================================ *)

let deriv_zero (#t:Type) {| cr: commutative_ring t |}
  (d: derivation_on cr)
  : Lemma (d.deriv (zero <: t) = (zero <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    add_zero #t (zero <: t);
    d.deriv_congruence (zero <: t) ((zero <: t) + (zero <: t));
    d.deriv_add (zero <: t) (zero <: t);
    (* Now: d.deriv zero = d.deriv zero + d.deriv zero *)
    (* Cancel: x = x + x implies x = 0 *)
    let dz = d.deriv (zero <: t) in
    add_congruence dz (neg dz) (dz + dz) (neg dz);
    add_negation dz;
    add_associativity dz dz (neg dz);
    add_congruence dz (dz + neg dz) dz (zero <: t);
    H.x_plus_zero dz

(* ================================================================ *)
(*  Derived property: D(-a) = -D(a)                                 *)
(*                                                                  *)
(*  Proof: 0 = D(0) = D(a + (-a)) = D(a) + D(-a).                  *)
(*  So D(-a) = -D(a).                                               *)
(* ================================================================ *)

let deriv_neg (#t:Type) {| cr: commutative_ring t |}
  (d: derivation_on cr) (a: t)
  : Lemma (d.deriv (neg a) = neg (d.deriv a))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    deriv_zero d;
    add_negation a;
    d.deriv_congruence (a + neg a) (zero <: t);
    d.deriv_add a (neg a);
    (* d.deriv a + d.deriv (neg a) = 0 *)
    (* So d.deriv (neg a) = neg (d.deriv a) *)
    let da = d.deriv a in
    let dna = d.deriv (neg a) in
    (* da + dna = 0, want dna = neg da *)
    add_congruence (neg da) (da + dna) (neg da) (zero <: t);
    H.x_plus_zero (neg da);
    add_associativity (neg da) da dna;
    add_commutativity (neg da) da;
    add_negation da;
    add_congruence (neg da + da) dna (zero <: t) dna;
    H.zero_plus_x dna

(* ================================================================ *)
(*  Derived property: D(1) = 0                                      *)
(*                                                                  *)
(*  Proof: D(1) = D(1·1) = D(1)·1 + 1·D(1) = D(1) + D(1).         *)
(*  Same cancellation as D(0) = 0.                                  *)
(* ================================================================ *)

let deriv_one (#t:Type) {| cr: commutative_ring t |}
  (d: derivation_on cr)
  : Lemma (d.deriv (one <: t) = (zero <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    mul_one #t (one <: t);
    d.deriv_congruence ((one <: t) * (one <: t)) (one <: t);
    d.deriv_leibniz (one <: t) (one <: t);
    (* D(1) = D(1)*1 + 1*D(1) *)
    let d1 = d.deriv (one <: t) in
    mul_one #t d1;
    (* D(1)*1 = D(1) and 1*D(1) = D(1) *)
    add_congruence (d1 * (one <: t)) ((one <: t) * d1) d1 d1;
    (* D(1) = d1 + d1 *)
    (* Same cancellation: x = x+x implies x = 0 *)
    add_congruence d1 (neg d1) (d1 + d1) (neg d1);
    add_negation d1;
    add_associativity d1 d1 (neg d1);
    add_congruence d1 (d1 + neg d1) d1 (zero <: t);
    H.x_plus_zero d1

(* ================================================================ *)
(*  Derived property: D(a - b) = D(a) - D(b)                       *)
(* ================================================================ *)

let deriv_sub (#t:Type) {| cr: commutative_ring t |}
  (d: derivation_on cr) (a b: t)
  : Lemma (d.deriv (a + neg b) = d.deriv a + neg (d.deriv b))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    d.deriv_add a (neg b);
    deriv_neg d b;
    let da = d.deriv a in
    let dnb = d.deriv (neg b) in
    add_congruence da dnb da (neg (d.deriv b))

(* ================================================================ *)
(*  Polynomial derivation                                           *)
(*                                                                  *)
(*  Wraps `poly_deriv` from Core.Polynomial.Derivative as a         *)
(*  `derivation_on` record.                                         *)
(* ================================================================ *)

let poly_derivation (#t:Type) {| cr: commutative_ring t |}
  : derivation_on (polynomial_commutative_ring_instance #t #cr).pcr
  = {
    deriv = poly_deriv #t #cr;
    deriv_congruence = poly_deriv_congruence #t #cr;
    deriv_add = poly_deriv_add #t #cr;
    deriv_leibniz = poly_deriv_mul #t #cr;
  }
