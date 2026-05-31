module Core.Matrix.Determinant.Mul

module TC = FStar.Tactics.Typeclasses
module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.FinSum
open Core.Permutation
open Core.Permutation.Enum
open Core.Permutation.Sum
open Core.Matrix
open Core.Matrix.Ring
open Core.Matrix.MultiDistrib
open Core.Matrix.Determinant
open Core.Tactics.CanonRing

(* ================================================================ *)
(*  Cauchy-Binet: det(AB) = det(A) * det(B)                         *)
(* ================================================================ *)

val det_mul
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n)
  : Lemma (det (matrix_mul a b) = det a * det b)