module FStar.CAS.RingUnits

(* ------------------------------------------------------------------------ *)
(*  Units of a ring.                                                        *)
(*                                                                          *)
(*  A "unit" of a ring `t` is an element with a two-sided multiplicative    *)
(*  inverse.  We package it as a record carrying the element, its inverse,  *)
(*  and witnesses for both one-sided laws.  The collection of units of a    *)
(*  ring forms a group under multiplication; this module provides the      *)
(*  `mul_group (ring_unit t)` instance.                                     *)
(*                                                                          *)
(*  Examples:                                                               *)
(*    - In any ring, the trivial unit (one, one).                           *)
(*    - In a field, every nonzero element gives a unit.                     *)
(*    - In ℤ, the units are { 1, -1 }.                                      *)
(*                                                                          *)
(*  This complements the `mul_group` typeclass already in `Grouplikes`,     *)
(*  which captures groups where the *whole* carrier is a multiplicative    *)
(*  group (e.g. permutations).                                              *)
(* ------------------------------------------------------------------------ *)

module TC = FStar.Tactics.Typeclasses

open FStar.CAS.Equatable
open FStar.CAS.Grouplikes
open FStar.CAS.Ringlikes

noeq type ring_unit (t: Type) {| r: ring t |} = {
  value     : t;
  unit_inv  : t;
  left_law  : squash (unit_inv * value = one);
  right_law : squash (value * unit_inv = one);
}

(* Equality on ring_unit: by value-field equality. Uniqueness of inverse
   (proven below) makes this a well-behaved equivalence. *)

let ru_eq (#t: Type) {| r: ring t |} (a b: ring_unit t) : bool =
  a.value = b.value

let ru_eq_reflexivity (#t: Type) {| r: ring t |} (a: ring_unit t)
  : Lemma (ru_eq a a == true)
  = reflexivity a.value

let ru_eq_symmetry (#t: Type) {| r: ring t |} (a b: ring_unit t)
  : Lemma (ru_eq a b == true <==> ru_eq b a == true)
  = symmetry a.value b.value

let ru_eq_transitivity (#t: Type) {| r: ring t |} (a b c: ring_unit t)
  : Lemma (requires ru_eq a b == true /\ ru_eq b c == true)
          (ensures ru_eq a c == true)
  = transitivity a.value b.value c.value

instance ring_unit_equatable (t: Type) {| r: ring t |} : equatable (ring_unit t) = {
  op_Equals = ru_eq;
  reflexivity = ru_eq_reflexivity;
  symmetry = ru_eq_symmetry;
  transitivity = ru_eq_transitivity;
}

(* ------------------------------------------------------------------------ *)
(*  Multiplication of units                                                 *)
(* ------------------------------------------------------------------------ *)

let ru_mul_left_law (#t: Type) {| r: ring t |} (a b: ring_unit t)
  : Lemma ((b.unit_inv * a.unit_inv) * (a.value * b.value) = one)
  = let _ = a.left_law in
    let _ = b.left_law in
    elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    calc (=) {
      (b.unit_inv * a.unit_inv) * (a.value * b.value);
      = { mul_associativity b.unit_inv a.unit_inv (a.value * b.value) }
      b.unit_inv * (a.unit_inv * (a.value * b.value));
      = { mul_associativity a.unit_inv a.value b.value;
          mul_congruence b.unit_inv (a.unit_inv * (a.value * b.value))
                         b.unit_inv ((a.unit_inv * a.value) * b.value) }
      b.unit_inv * ((a.unit_inv * a.value) * b.value);
      = { reflexivity b.value;
          mul_congruence (a.unit_inv * a.value) b.value one b.value;
          mul_congruence b.unit_inv ((a.unit_inv * a.value) * b.value)
                         b.unit_inv (one * b.value);
          left_mul_identity b.value;
          mul_congruence b.unit_inv (one * b.value) b.unit_inv b.value }
      b.unit_inv * b.value;
      = { }
      one;
    }

let ru_mul_right_law (#t: Type) {| r: ring t |} (a b: ring_unit t)
  : Lemma ((a.value * b.value) * (b.unit_inv * a.unit_inv) = one)
  = let _ = a.right_law in
    let _ = b.right_law in
    elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    calc (=) {
      (a.value * b.value) * (b.unit_inv * a.unit_inv);
      = { mul_associativity a.value b.value (b.unit_inv * a.unit_inv) }
      a.value * (b.value * (b.unit_inv * a.unit_inv));
      = { mul_associativity b.value b.unit_inv a.unit_inv;
          mul_congruence a.value (b.value * (b.unit_inv * a.unit_inv))
                         a.value ((b.value * b.unit_inv) * a.unit_inv) }
      a.value * ((b.value * b.unit_inv) * a.unit_inv);
      = { reflexivity a.unit_inv;
          mul_congruence (b.value * b.unit_inv) a.unit_inv one a.unit_inv;
          mul_congruence a.value ((b.value * b.unit_inv) * a.unit_inv)
                         a.value (one * a.unit_inv);
          left_mul_identity a.unit_inv;
          mul_congruence a.value (one * a.unit_inv) a.value a.unit_inv }
      a.value * a.unit_inv;
      = { }
      one;
    }

let ru_mul (#t: Type) {| r: ring t |} (a b: ring_unit t) : ring_unit t =
  ru_mul_left_law a b;
  ru_mul_right_law a b;
  {
    value = a.value * b.value;
    unit_inv = b.unit_inv * a.unit_inv;
    left_law = ();
    right_law = ();
  }

let ru_mul_congruence (#t: Type) {| r: ring t |} (a1 b1 a2 b2: ring_unit t)
  : Lemma (requires ru_eq a1 a2 == true /\ ru_eq b1 b2 == true)
          (ensures ru_eq (ru_mul a1 b1) (ru_mul a2 b2) == true)
  = mul_congruence a1.value b1.value a2.value b2.value

instance ring_unit_has_mul (t: Type) {| r: ring t |} : has_mul (ring_unit t) = {
  eq = ring_unit_equatable t;
  ( * ) = ru_mul;
  congruence = ru_mul_congruence;
}

let ru_mul_associativity (#t: Type) {| r: ring t |} (a b c: ring_unit t)
  : Lemma (ru_eq (ru_mul (ru_mul a b) c) (ru_mul a (ru_mul b c)) == true)
  = mul_associativity a.value b.value c.value

instance ring_unit_mul_semigroup (t: Type) {| r: ring t |} : mul_semigroup (ring_unit t) = {
  has_mul = ring_unit_has_mul t;
  associativity = ru_mul_associativity;
}

(* The multiplicative identity unit. *)
let ru_one (#t: Type) {| r: ring t |} : ring_unit t =
  left_mul_identity (one #t);
  {
    value = one;
    unit_inv = one;
    left_law = ();
    right_law = ();
  }

instance ring_unit_has_one (t: Type) {| r: ring t |} : has_one (ring_unit t) = {
  eq = ring_unit_equatable t;
  one = ru_one;
}

let ru_left_mul_identity (#t: Type) {| r: ring t |} (a: ring_unit t)
  : Lemma (ru_eq (ru_mul ru_one a) a == true)
  = left_mul_identity a.value

let ru_right_mul_identity (#t: Type) {| r: ring t |} (a: ring_unit t)
  : Lemma (ru_eq (ru_mul a ru_one) a == true)
  = right_mul_identity a.value

instance ring_unit_mul_monoid (t: Type) {| r: ring t |} : mul_monoid (ring_unit t) = {
  mul_semigroup = ring_unit_mul_semigroup t;
  has_one = ring_unit_has_one t;
  left_mul_identity = ru_left_mul_identity;
  right_mul_identity = ru_right_mul_identity;
}

(* Inverse of a unit: swap value and unit_inv. *)
let ru_inv (#t: Type) {| r: ring t |} (u: ring_unit t) : ring_unit t = {
  value = u.unit_inv;
  unit_inv = u.value;
  left_law = u.right_law;
  right_law = u.left_law;
}

instance ring_unit_has_inv (t: Type) {| r: ring t |} : has_inv (ring_unit t) = {
  has_one = ring_unit_has_one t;
  inv = ru_inv;
}

let ru_inversion (#t: Type) {| r: ring t |} (u: ring_unit t)
  : Lemma (ru_eq (ru_mul u (ru_inv u)) ru_one == true /\
           ru_eq (ru_mul (ru_inv u) u) ru_one == true)
  = let _ = u.left_law in
    let _ = u.right_law in
    ()

instance ring_unit_mul_group (t: Type) {| r: ring t |} : mul_group (ring_unit t) = {
  mul_monoid = ring_unit_mul_monoid t;
  has_inv = ring_unit_has_inv t;
  inversion = ru_inversion;
}
