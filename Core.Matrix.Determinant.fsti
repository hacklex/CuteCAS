module Core.Matrix.Determinant

module L = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Algebra.Helpers
open Core.Tactics.CanonRing
open Core.FinSum
open Core.Permutation
open Core.Permutation.Enum
open Core.Permutation.Sum
open Core.Matrix
open Core.Vector

(* Bridge: ring → add_comm_group *)
unfold let acg_of_ring_local (t: Type) (r: ring t) : add_comm_group t = r.r_add

(* Ring-level helpers *)
val ring_neg_xy_is_x_times_neg_y (#t: Type) {| cr: commutative_ring t |} (x y: t)
  : Lemma (-(x * y) = x * (-y))
val ring_neg_xy_is_neg_x_times_y (#t: Type) {| cr: commutative_ring t |} (x y: t)
  : Lemma (-(x * y) = (-x) * y)

(* Core definitions — exposed concretely so downstream can unfold *)
let perm_product (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (p: permutation n) : t
  = prod_range (fun i -> if i < n then m i (p.fwd i) else one) 0 n
val perm_product_unfold (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (p: permutation n)
  : Lemma (perm_product m p ==
           prod_range (fun k -> if k < n then m k (p.fwd k) else one) 0 n)

(* Named per-index entry of the Leibniz product (so downstream code can
   reference one function symbol instead of perm_product's inline lambda
   — needed to transport a ring hom through perm_product). *)
let perm_entry (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (p: permutation n) (k: nat) : t
  = if k < n then m k (p.fwd k) else one

val perm_product_via (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (p: permutation n)
  : Lemma (perm_product m p == prod_range (perm_entry m p) 0 n)
let leibniz_term (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (p: permutation n) : t
  = if parity p then perm_product m p else (-(perm_product m p))
let det (#t: Type) {| cr: commutative_ring t |} (#n: pos) (m: square_matrix t n) : t
  = sum_over_perms n (leibniz_term m)
val det_unfold (#t: Type) {| cr: commutative_ring t |} (#n: pos) (m: square_matrix t n)
  : Lemma (det m == sum_over_perms n (leibniz_term m))

(* Properties — ordered to match .fst definition order *)
val det_identity (#t: Type) {| cr: commutative_ring t |} (n: pos)
  : Lemma (det (id_matrix #t #_ #n) = one)
val det_zero_row (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (k: fin n)
  : Lemma (requires forall (j: fin n). m k j = zero)
          (ensures  det m = zero)
val leibniz_term_respects_perm_eq (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n)
  : Lemma (respects_perm_eq #t (leibniz_term m))
val det_transpose (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n)
  : Lemma (det (transpose m) = det m)
val det_pointwise_eq (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m1 m2: square_matrix t n)
  : Lemma (requires forall (a b: fin n). m1 a b = m2 a b)
          (ensures  det m1 = det m2)
val det_two_equal_rows_cr (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires ~(i == j) /\
                    (forall (k: fin n). m i k = m j k))
          (ensures  det m = zero)
let col_add (#t: Type) {| ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n) (c: t) : square_matrix t n
  = fun (a: fin n) (b: fin n) -> if Prims.op_Equality b i then m a b + m a j * c else m a b
val det_col_add (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n) (c: t)
  : Lemma (requires ~(i == j))
          (ensures det (col_add m i j c) = det m)
val det_zero_column (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (j: fin n)
  : Lemma (requires forall (k: fin n). m k j = zero)
          (ensures det m = zero)
val det_permute_rows (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (sigma: permutation n)
  : Lemma (det (permute_rows m sigma) =
           (if parity sigma then det m else -(det m)))

(* Laplace expansion infrastructure — concrete for downstream unfolding *)
let minus_one_pow (#t: Type) {| cr: commutative_ring t |} (k: nat) : t
  = if Prims.op_Modulus k 2 = 0 then one else (- (one))
let skip (#n: pos) (i: fin n) (a: fin ((n - 1))) : fin n
  = if (a <: nat) < (i <: nat) then (a <: nat) else (a ++ 1)
val skip_avoids (#n: pos) (i: fin n) (a: fin ((n - 1)))
  : Lemma (~((skip i a <: nat) == (i <: nat)))
let minor (#t: Type) (#n: pos{ n > 1 }) (m: square_matrix t n) (i j: fin n)
  : square_matrix t ((n - 1))
  = fun (a: fin ((n - 1))) (b: fin ((n - 1)))
      -> m (skip i a) (skip j b)
let cofactor_term (#t: Type) {| cr: commutative_ring t |} (#n: pos{ n > 1 })
  (m: square_matrix t n) (i j: fin n) : t
  = minus_one_pow #t #cr (((i <: nat) ++ (j <: nat)))
    * m i j
    * det #t #cr #((n - 1)) (minor m i j)
val det_laplace_row (#t: Type) {| cr: commutative_ring t |}
  (#n: pos{ n > 1 }) (m: square_matrix t n) (i: fin n)
  : Lemma (det m = fin_sum (cofactor_term #t #cr m i))

(* ================================================================== *)
(*  Cauchy-Binet (merged from Core.Matrix.Determinant.Mul):           *)
(*    det(AB) = det(A) * det(B)                                        *)
(* ================================================================== *)
val det_mul
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n)
  : Lemma (det (matrix_mul a b) = det a * det b)

(* ================================================================== *)
(*  Triangular determinants (merged from Core.Matrix.Triangular).     *)
(*  Value-defs are exposed concretely so downstream proofs can unfold  *)
(*  them (diagonal_product_from is recursively peeled at call sites).   *)
(* ================================================================== *)
let rec diagonal_product_from (#t:Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (k: nat{k <= n}) : Tot t (decreases (n - k))
  = if k >= n then one #t
    else m (k <: fin n) (k <: fin n) * diagonal_product_from m ((k ++ 1))

let diagonal_product (#t:Type) {| cr: commutative_ring t |} (#n: pos) (m: square_matrix t n) : t
  = diagonal_product_from m 0

let is_lower_triangular (#t:Type) {| cr: commutative_ring t |} (#n: pos) (m: square_matrix t n) : prop
  = forall (i j: fin n). (j <: nat) > (i <: nat) ==> m i j = zero

let is_upper_triangular (#t:Type) {| cr: commutative_ring t |} (#n: pos) (m: square_matrix t n) : prop
  = forall (i j: fin n). (i <: nat) > (j <: nat) ==> m i j = zero

val determinant_size_one (#t:Type) {| cr: commutative_ring t |} (m: square_matrix t 1)
  : Lemma (det m = m (0 <: fin 1) (0 <: fin 1))

val det_lower_triangular (#t:Type) {| cr: commutative_ring t |}
  (#n: pos) (m: square_matrix t n)
  : Lemma (requires is_lower_triangular m)
          (ensures  det m = diagonal_product m)

val diagonal_product_pointwise (#t:Type) {| cr: commutative_ring t |}
  (#n: pos) (m1 m2: square_matrix t n)
  : Lemma (requires forall (i: fin n). m1 i i = m2 i i)
          (ensures  diagonal_product m1 = diagonal_product m2)

val det_upper_triangular (#t:Type) {| cr: commutative_ring t |}
  (#n: pos) (m: square_matrix t n)
  : Lemma (requires is_upper_triangular m)
          (ensures  det m = diagonal_product m)

(* ================================================================== *)
(*  Kernel ⇔ singular determinant (merged from KernelDet / NullVec).  *)
(* ================================================================== *)
val det_zero_implies_null_vec (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n)
  : Lemma (requires det m = zero)
          (ensures  exists (v: fin n -> t) (k: fin n).
                      is_nonzero (v k) /\
                      (forall (i: fin n). vector_dot (row m i) v = zero))

(* The null-vector hypothesis: dot product of row i with v is zero.
   Exposed concretely so consumers can state Lemma (null_vec_hyp ...). *)
let null_vec_hyp (#t:Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (v: fin n -> t) (i: fin n) : prop
  = vector_dot (row m i) v = zero

val null_vec_implies_det_zero (#t:Type) {| f: field t |} (#n: nat{n > 0})
  (m: square_matrix t n) (v: fin n -> t) (k: fin n)
  : Lemma (requires is_nonzero (v k) /\
                    (forall (i: fin n). null_vec_hyp m v i))
          (ensures det m = zero)
