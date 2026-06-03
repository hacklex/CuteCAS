module Core.Matrix.Triangular

(*
   Determinant of a triangular matrix equals the product of its diagonal.

       is_lower_triangular m  ==>  det m = diagonal_product m

   Proof: Laplace expansion along row 0.  In a lower-triangular matrix row 0
   has a single nonzero entry (the corner m[0][0]), so the cofactor sum
   collapses to one term; the minor at (0,0) is again lower-triangular, and
   induction on the size finishes it.  This is the reusable unlock for the
   resultant base case  Res(x - a, B) = B(a)  (whose Sylvester matrix becomes
   triangular after column operations).
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Helpers
open Core.Algebra.Combinators
open Core.FinSum
open Core.Permutation
open Core.Permutation.Sum
open Core.Matrix
open Core.Matrix.Determinant

(* ================================================================ *)
(*  Diagonal product and triangularity.                              *)
(* ================================================================ *)

(* m[k][k] * m[k+1][k+1] * ... * m[n-1][n-1]  (named recursion avoids prod_range
   lambda-unification friction when relating a matrix to its minor). *)
let rec diagonal_product_from (#t:Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (k: nat{k <= n}) : Tot t (decreases (n - k))
  = if k >= n then one #t
    else m (k <: fin n) (k <: fin n) * diagonal_product_from m (Prims.op_Addition k 1)

(* m[0][0] * m[1][1] * ... * m[n-1][n-1] *)
let diagonal_product (#t:Type) {| cr: commutative_ring t |} (#n: pos) (m: square_matrix t n) : t
  = diagonal_product_from m 0

(* every entry strictly above the diagonal vanishes *)
let is_lower_triangular (#t:Type) {| cr: commutative_ring t |} (#n: pos) (m: square_matrix t n) : prop
  = forall (i j: fin n). (j <: nat) > (i <: nat) ==> m i j = (zero <: t)

(* ================================================================ *)
(*  Base case: determinant of a 1x1 matrix is its single entry.      *)
(* ================================================================ *)

let determinant_size_one (#t:Type) {| cr: commutative_ring t |} (m: square_matrix t 1)
  : Lemma (det m = m (0 <: fin 1) (0 <: fin 1))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let f = leibniz_term m in
    let p0 : permutation 1 = identity 1 in
    leibniz_term_respects_perm_eq m;
    let h_zero (q: permutation 1)
      : Lemma (requires ~(perm_eq p0 q)) (ensures f q = (zero <: t))
      = perm_eq_intro p0 q (fun i -> identity_fwd 1 i)   (* size 1: every perm agrees with identity, contra *)
    in
    sum_over_perms_single 1 f p0 h_zero;            (* sum_over_perms 1 f = f p0 *)
    det_unfold m;                                    (* det m == sum_over_perms 1 f *)
    parity_identity 1;                               (* parity p0 == true, so f p0 = perm_product m p0 *)
    perm_product_unfold m p0;                        (* perm_product m p0 == prod_range (...) 0 1 *)
    let body : nat -> t = fun k -> if k < 1 then m (k <: fin 1) (p0.fwd (k <: fin 1)) else one in
    prod_range_unfold_left body 0 1;                 (* = body 0 * prod_range body 1 1 *)
    prod_range_empty body 1 1;                       (* prod_range body 1 1 == one *)
    H.x_mul_one (body 0);                            (* body 0 * one = body 0 *)
    mul_congruence (body 0) (prod_range body 1 1) (body 0) (one <: t);
    (* body 0 == m 0 (p0.fwd 0) == m 0 0 ; chain det m = ... = m 0 0 *)
    transitivity (det m) (prod_range body 0 1) (m (0 <: fin 1) (0 <: fin 1))

(* ================================================================ *)
(*  The (0,0) minor of a lower-triangular matrix is lower-triangular. *)
(* ================================================================ *)

let minor_zero_zero_lower_triangular (#t:Type) {| cr: commutative_ring t |}
  (#n: pos{n > 1}) (m: square_matrix t n)
  : Lemma (requires is_lower_triangular m)
          (ensures  is_lower_triangular (minor m (0 <: fin n) (0 <: fin n)))
  = ()                                              (* minor[a][b] = m (skip 0 a)(skip 0 b) = m (a+1)(b+1); b>a => b+1>a+1 *)

(* ================================================================ *)
(*  Cofactor expansion along row 0 collapses to the corner term.     *)
(* ================================================================ *)

(* Off-diagonal cofactors of row 0 vanish (the entry m[0][k] is zero for k>0). *)
let cofactor_row_zero_off_diagonal (#t:Type) {| cr: commutative_ring t |}
  (#n: pos{n > 1}) (m: square_matrix t n) (k: fin n)
  : Lemma (requires is_lower_triangular m /\ (k <: nat) > 0)
          (ensures  cofactor_term m (0 <: fin n) k = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let i0 : fin n = 0 <: fin n in
    let mp = minus_one_pow #t #cr (Prims.op_Addition (i0 <: nat) (k <: nat)) in
    let dm = det #t #cr #(n - 1) (minor m i0 k) in
    assert (m i0 k = (zero <: t));                   (* lower-triangular, k > 0 *)
    mul_congruence mp (m i0 k) mp (zero <: t);
    H.x_mul_zero mp;
    mul_congruence (mp * m i0 k) dm (zero <: t) dm;
    H.zero_mul_x dm;
    transitivity ((mp * m i0 k) * dm) ((zero <: t) * dm) (zero <: t)

let cofactor_row_zero_collapses (#t:Type) {| cr: commutative_ring t |}
  (#n: pos{n > 1}) (m: square_matrix t n)
  : Lemma (requires is_lower_triangular m)
          (ensures  fin_sum (cofactor_term m (0 <: fin n))
                  = cofactor_term m (0 <: fin n) (0 <: fin n))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let agree (k: fin n)
      : Lemma (cofactor_term m (0 <: fin n) k
             = pointwise_mul (fin_kronecker_delta (0 <: fin n)) (cofactor_term m (0 <: fin n)) k)
      = if (k <: nat) = 0 then
          H.one_mul_x (cofactor_term m (0 <: fin n) k)   (* delta = one: term = one * cof = cof *)
        else begin
          cofactor_row_zero_off_diagonal m k;            (* cofactor = zero (k > 0) *)
          H.zero_mul_x (cofactor_term m (0 <: fin n) k)  (* delta = zero: term = zero * cof = zero *)
        end
    in
    fin_sum_congruence (cofactor_term m (0 <: fin n))
                       (pointwise_mul (fin_kronecker_delta (0 <: fin n)) (cofactor_term m (0 <: fin n)))
                       agree;
    fin_sum_kronecker (0 <: fin n) (cofactor_term m (0 <: fin n));
    transitivity (fin_sum (cofactor_term m (0 <: fin n)))
                 (fin_sum (pointwise_mul (fin_kronecker_delta (0 <: fin n)) (cofactor_term m (0 <: fin n))))
                 (cofactor_term m (0 <: fin n) (0 <: fin n))

(* ================================================================ *)
(*  Diagonal of the (0,0) minor:  the tail of m's diagonal.          *)
(*    diagonal_product_from (minor m 0 0) j  =  diagonal_product_from m (j+1) *)
(* ================================================================ *)

let rec diagonal_from_minor (#t:Type) {| cr: commutative_ring t |}
  (#n: pos{n > 1}) (m: square_matrix t n) (j: nat{j <= n - 1})
  : Lemma (ensures diagonal_product_from (minor m (0 <: fin n) (0 <: fin n)) j
                 = diagonal_product_from m (Prims.op_Addition j 1))
          (decreases (n - 1 - j))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let mm = minor m (0 <: fin n) (0 <: fin n) in
    if j >= n - 1 then ()                              (* both products are empty = one *)
    else begin
      diagonal_from_minor m (Prims.op_Addition j 1);   (* IH: tail of minor = tail of m *)
      (* mm[j][j] = m (skip 0 j)(skip 0 j) = m[j+1][j+1] *)
      mul_congruence (mm (j <: fin (n - 1)) (j <: fin (n - 1)))
                     (diagonal_product_from mm (Prims.op_Addition j 1))
                     (m (Prims.op_Addition j 1 <: fin n) (Prims.op_Addition j 1 <: fin n))
                     (diagonal_product_from m (Prims.op_Addition j 2))
    end

(* ================================================================ *)
(*  diagonal_product m = m[0][0] * diagonal_product (minor m 0 0).    *)
(* ================================================================ *)

let diagonal_product_peel (#t:Type) {| cr: commutative_ring t |}
  (#n: pos{n > 1}) (m: square_matrix t n)
  : Lemma (diagonal_product m
         = m (0 <: fin n) (0 <: fin n)
           * diagonal_product (minor m (0 <: fin n) (0 <: fin n)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    (* diagonal_product m = diagonal_product_from m 0 = m[0][0] * diagonal_product_from m 1 (n>1) *)
    diagonal_from_minor m 0;                           (* diag_from (minor) 0 = diag_from m 1 *)
    mul_congruence (m (0 <: fin n) (0 <: fin n)) (diagonal_product_from m 1)
                   (m (0 <: fin n) (0 <: fin n))
                   (diagonal_product_from (minor m (0 <: fin n) (0 <: fin n)) 0)

(* ================================================================ *)
(*  Main theorem.                                                    *)
(* ================================================================ *)

let rec det_lower_triangular (#t:Type) {| cr: commutative_ring t |}
  (#n: pos) (m: square_matrix t n)
  : Lemma (requires is_lower_triangular m)
          (ensures  det m = diagonal_product m)
          (decreases n)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if n = 1 then begin
      determinant_size_one m;                        (* det m = m 0 0 *)
      H.x_mul_one (m (0 <: fin n) (0 <: fin n))      (* diagonal_product m = m00 * one = m00 *)
    end else begin
      det_laplace_row m (0 <: fin n);                (* det m = fin_sum (cofactor_term m 0) *)
      cofactor_row_zero_collapses m;                 (* fin_sum = cofactor_term m 0 0 *)
      minor_zero_zero_lower_triangular m;            (* minor m 0 0 is lower-triangular *)
      det_lower_triangular (minor m (0 <: fin n) (0 <: fin n));   (* IH *)
      diagonal_product_peel m;                        (* diagonal_product m = m00 * diagonal_product(minor) *)
      (* cofactor_term m 0 0 = minus_one_pow 0 * m00 * det(minor) = m00 * det(minor) = m00 * diagonal_product(minor) *)
      let mm = minor m (0 <: fin n) (0 <: fin n) in
      (* cofactor_term m 0 0 == (minus_one_pow 0 * m00) * det mm == (one * m00) * det mm *)
      H.one_mul_x (m (0 <: fin n) (0 <: fin n));      (* one * m00 = m00 *)
      mul_congruence ((one <: t) * m (0 <: fin n) (0 <: fin n)) (det #t #cr #(n-1) mm)
                     (m (0 <: fin n) (0 <: fin n)) (det #t #cr #(n-1) mm);   (* (one*m00)*det = m00*det *)
      mul_congruence (m (0 <: fin n) (0 <: fin n)) (det #t #cr #(n-1) mm)
                     (m (0 <: fin n) (0 <: fin n)) (diagonal_product mm);   (* m00*det = m00*diag(minor) *)
      transitivity (det m) (fin_sum (cofactor_term m (0 <: fin n)))
                   (cofactor_term m (0 <: fin n) (0 <: fin n));
      transitivity (det m) (cofactor_term m (0 <: fin n) (0 <: fin n))
                   (m (0 <: fin n) (0 <: fin n) * det #t #cr #(n-1) mm);
      transitivity (det m) (m (0 <: fin n) (0 <: fin n) * det #t #cr #(n-1) mm)
                   (m (0 <: fin n) (0 <: fin n) * diagonal_product mm);
      transitivity (det m) (m (0 <: fin n) (0 <: fin n) * diagonal_product mm)
                   (diagonal_product m)
    end

(* ================================================================ *)
(*  diagonal_product depends only on the diagonal; upper-triangular  *)
(*  determinant (companion of the lower-triangular theorem).         *)
(* ================================================================ *)

let rec diagonal_product_from_pointwise (#t:Type) {| cr: commutative_ring t |}
  (#n: pos) (m1 m2: square_matrix t n)
  (heq: squash (forall (i: fin n). m1 i i = m2 i i)) (k: nat{k <= n})
  : Lemma (ensures diagonal_product_from m1 k = diagonal_product_from m2 k)
          (decreases (n - k))
  = elim_equatable_laws t ();
    if k >= n then reflexivity (one <: t)
    else begin
      diagonal_product_from_pointwise m1 m2 heq (Prims.op_Addition k 1);
      mul_congruence (m1 (k <: fin n) (k <: fin n)) (diagonal_product_from m1 (Prims.op_Addition k 1))
                     (m2 (k <: fin n) (k <: fin n)) (diagonal_product_from m2 (Prims.op_Addition k 1))
    end

let diagonal_product_pointwise (#t:Type) {| cr: commutative_ring t |}
  (#n: pos) (m1 m2: square_matrix t n)
  : Lemma (requires forall (i: fin n). m1 i i = m2 i i)
          (ensures  diagonal_product m1 = diagonal_product m2)
  = diagonal_product_from_pointwise m1 m2 () 0

let is_upper_triangular (#t:Type) {| cr: commutative_ring t |} (#n: pos) (m: square_matrix t n) : prop
  = forall (i j: fin n). (i <: nat) > (j <: nat) ==> m i j = (zero <: t)

let det_upper_triangular (#t:Type) {| cr: commutative_ring t |}
  (#n: pos) (m: square_matrix t n)
  : Lemma (requires is_upper_triangular m)
          (ensures  det m = diagonal_product m)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    det_transpose m;                                  (* det (transpose m) = det m *)
    assert (is_lower_triangular (transpose m));       (* (transpose m) i j = m j i *)
    det_lower_triangular (transpose m);               (* det (transpose m) = diagonal_product (transpose m) *)
    diagonal_product_pointwise (transpose m) m;       (* same diagonal *)
    transitivity (det m) (diagonal_product (transpose m)) (diagonal_product m)
