module Core.Algebra.Derivation

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
    add_zero (zero <: t);
    d.deriv_congruence (zero <: t) (zero + zero);
    d.deriv_add (zero <: t) (zero <: t);
    (* Now: d.deriv zero = d.deriv zero + d.deriv zero *)
    (* Cancel: x = x + x implies x = 0 *)
    let dz = d.deriv (zero <: t) in
    add_congruence dz (- dz) (dz + dz) (- dz);
    add_negation dz;
    add_associativity dz dz (- dz);
    add_congruence dz (dz + (- dz)) dz zero;
    H.x_plus_zero dz

(* ================================================================ *)
(*  Derived property: D(-a) = -D(a)                                 *)
(*                                                                  *)
(*  Proof: 0 = D(0) = D(a + (-a)) = D(a) + D(-a).                  *)
(*  So D(-a) = -D(a).                                               *)
(* ================================================================ *)

let deriv_neg (#t:Type) {| cr: commutative_ring t |}
  (d: derivation_on cr) (a: t)
  : Lemma (d.deriv (- a) = (- (d.deriv a)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    deriv_zero d;
    add_negation a;
    d.deriv_congruence (a + (- a)) (zero <: t);
    d.deriv_add a (- a);
    (* d.deriv a + d.deriv (neg a) = 0 *)
    (* So d.deriv (neg a) = neg (d.deriv a) *)
    let da = d.deriv a in
    let dna = d.deriv (- a) in
    (* da + dna = 0, want dna = neg da *)
    add_congruence (- da) (da + dna) (- da) (zero <: t);
    H.x_plus_zero (- da);
    add_associativity (- da) da dna;
    add_commutativity (- da) da;
    add_negation da;
    add_congruence ((- da) + da) dna (zero <: t) dna;
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
    mul_one (one <: t);
    d.deriv_congruence ((one <: t) * (one <: t)) (one <: t);
    d.deriv_leibniz (one <: t) (one <: t);
    (* D(1) = D(1)*1 + 1*D(1) *)
    let d1 = d.deriv (one <: t) in
    mul_one d1;
    (* D(1)*1 = D(1) and 1*D(1) = D(1) *)
    add_congruence (d1 * (one <: t)) ((one <: t) * d1) d1 d1;
    (* D(1) = d1 + d1 *)
    (* Same cancellation: x = x+x implies x = 0 *)
    add_congruence d1 (- d1) (d1 + d1) (- d1);
    add_negation d1;
    add_associativity d1 d1 (- d1);
    add_congruence d1 (d1 + (- d1)) d1 (zero <: t);
    H.x_plus_zero d1

(* ================================================================ *)
(*  Derived property: D(a - b) = D(a) - D(b)                       *)
(* ================================================================ *)

let deriv_sub (#t:Type) {| cr: commutative_ring t |}
  (d: derivation_on cr) (a b: t)
  : Lemma (d.deriv (a + (- b)) = d.deriv a + (- (d.deriv b)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    d.deriv_add a (- b);
    deriv_neg d b;
    let da = d.deriv a in
    let dnb = d.deriv (- b) in
    add_congruence da dnb da (- (d.deriv b))

(* ================================================================ *)
(*  Polynomial derivation                                           *)
(*                                                                  *)
(*  Wraps `poly_deriv` from Core.Polynomial.Derivative as a         *)
(*  `derivation_on` record.                                         *)
(* ================================================================ *)

let poly_derivation (#t:Type) {| cr: commutative_ring t |}
  : derivation_on (polynomial_cr #t #cr)
  = {
    deriv = poly_deriv;
    deriv_congruence = poly_deriv_congruence;
    deriv_add = poly_deriv_add;
    deriv_leibniz = poly_deriv_mul;
  }
