module Core.Algebra.Test

(*
  Phase 1 acceptance gate G1.

  Goal: a generic lemma in a {| commutative_ring t |} context that uses
  both `+` (resolved via add_comm_group) and `*` (resolved via ring)
  and one law from `mul_is_commutative`. Must verify without explicit
  `#`-instance annotations.
*)

open Core.Algebra
open Core.Algebra.Notation
module TC = FStar.Tactics.Typeclasses

(* G1.1: distributivity is reachable from commutative_ring without `#`. *)
let g1_left_distrib (#t:Type) {| commutative_ring t |} (x y z: t)
  : Lemma ((x * (y + z)) = (x * y + x * z))
  = left_distributivity x y z

(* G1.2: right distributivity. *)
let g1_right_distrib (#t:Type) {| commutative_ring t |} (x y z: t)
  : Lemma (((x + y) * z) = (x * z + y * z))
  = right_distributivity z x y

(* G1.3: mul_commutativity is reachable through the bundle (`cr_mic`). *)
let g1_mul_comm (#t:Type) {| cr: commutative_ring t |} (x y: t)
  : Lemma ((x * y) = (y * x))
  = cr.cr_mic.mul_commutativity x y

(* G1.4: the headline — (a + b) * c = a*c + b*c. *)
let g1_main (#t:Type) {| commutative_ring t |} (a b c: t)
  : Lemma (((a + b) * c) = (a * c + b * c))
  = right_distributivity c a b

(* G1.5: same from a field context, exercising the
   field → integral_domain → commutative_ring chain. *)
let g1_from_field (#t:Type) {| field t |} (a b c: t)
  : Lemma (((a + b) * c) = (a * c + b * c))
  = right_distributivity c a b
