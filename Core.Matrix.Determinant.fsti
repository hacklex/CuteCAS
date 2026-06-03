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
let skip (#n: pos) (i: fin n) (a: fin (Prims.op_Subtraction n 1)) : fin n
  = if (a <: nat) < (i <: nat) then (a <: nat) else Prims.op_Addition a 1
val skip_avoids (#n: pos) (i: fin n) (a: fin (Prims.op_Subtraction n 1))
  : Lemma (~((skip i a <: nat) == (i <: nat)))
let minor (#t: Type) (#n: pos{ n > 1 }) (m: square_matrix t n) (i j: fin n)
  : square_matrix t (Prims.op_Subtraction n 1)
  = fun (a: fin (Prims.op_Subtraction n 1)) (b: fin (Prims.op_Subtraction n 1))
      -> m (skip i a) (skip j b)
let cofactor_term (#t: Type) {| cr: commutative_ring t |} (#n: pos{ n > 1 })
  (m: square_matrix t n) (i j: fin n) : t
  = minus_one_pow #t #cr (Prims.op_Addition (i <: nat) (j <: nat))
    * m i j
    * det #t #cr #(Prims.op_Subtraction n 1) (minor m i j)
val det_laplace_row (#t: Type) {| cr: commutative_ring t |}
  (#n: pos{ n > 1 }) (m: square_matrix t n) (i: fin n)
  : Lemma (det m = fin_sum (cofactor_term #t #cr m i))
