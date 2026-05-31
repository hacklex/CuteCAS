module Core.Matrix.Adjugate

(*
   The adjugate (classical adjoint) of a square matrix.

   adj(M)(i,j) = (-1)^(i+j) * det(minor M j i)

   Note the transpose: adj(M)(i,j) uses minor at row j, column i.

   Headline theorem:
     adj(M) * M = det(M) * identity_matrix    (over a commutative ring)

   This gives (over a field with det M ≠ 0) the inverse:
     M^{-1} = (1/det M) * adj(M)

   And the kernel characterization:
     det M = 0 ⟺ M is not invertible ⟺ M has a nontrivial kernel
*)

module TC = FStar.Tactics.Typeclasses
module H = Core.Algebra.Helpers
module L = FStar.List.Tot

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.FinSum
open Core.Permutation
open Core.Permutation.Enum
open Core.Permutation.Sum
open Core.Matrix
open Core.Matrix.Ring
open Core.Matrix.Determinant
open Core.Tactics.CanonRing

(* ================================================================== *)
(*  The signed cofactor (without the entry): C(M, i, j)               *)
(*  = (-1)^(i+j) * det(minor M i j)                                   *)
(* ================================================================== *)

let signed_cofactor (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n) : t
  = minus_one_pow #t #cr (Prims.op_Addition (i <: nat) (j <: nat))
    * det #t #cr #(Prims.op_Subtraction n 1) (minor m i j)

(* cofactor_term m i j = m(i,j) * signed_cofactor m i j
   (modulo associativity/commutativity) *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let cofactor_term_eq_entry_times_signed_cofactor
  (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (cofactor_term m i j = m i j * signed_cofactor m i j)
  = H.elim_equatable_laws t ();
    (* cofactor_term = mop * m(i,j) * det_min
       m(i,j) * signed_cofactor = m(i,j) * (mop * det_min)
       Need: (a*b)*c = b*(a*c) *)
    let mop = minus_one_pow #t #cr (Prims.op_Addition (i <: nat) (j <: nat)) in
    let det_min = det #t #cr #(Prims.op_Subtraction n 1) (minor m i j) in
    let e = m i j in
    (* cofactor_term = (mop * e) * det_min *)
    mul_associativity #t #cr.cr_r mop e det_min;
    (* mop * e * det_min = mop * (e * det_min) *)
    mul_commutativity #t #cr.cr_r mop (e * det_min);
    (* = (e * det_min) * mop ... no, let me just do mop*e = e*mop *)
    mul_commutativity #t #cr.cr_r mop e;
    (* mop * e = e * mop *)
    mul_congruence (mop * e) det_min (e * mop) det_min;
    mul_associativity #t #cr.cr_r e mop det_min;
    (* (e * mop) * det_min = e * (mop * det_min) = e * signed_cofactor *)
    transitivity (cofactor_term m i j) ((mop * e) * det_min) ((e * mop) * det_min);
    transitivity ((e * mop) * det_min) (e * (mop * det_min)) (e * signed_cofactor m i j);
    transitivity (cofactor_term m i j) ((e * mop) * det_min) (e * signed_cofactor m i j)
#pop-options

(* ================================================================== *)
(*  The adjugate matrix                                               *)
(* ================================================================== *)

let adjugate (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) : square_matrix t n
  = fun (i: fin n) (j: fin n) -> signed_cofactor m j i

(* ================================================================== *)
(*  Key identity: (adj M * M)(i,j) = det(M) * delta(i,j)             *)
(*                                                                     *)
(*  Split into two cases:                                              *)
(*    Diagonal (i=j): Laplace expansion along row i → det M.          *)
(*    Off-diagonal (i≠j): Laplace of a matrix with duplicate row → 0. *)
(* ================================================================== *)

(* The identity matrix. *)
let identity_matrix (#t: Type) {| cr: commutative_ring t |} (n: pos)
  : square_matrix t n
  = fun (i: fin n) (j: fin n) ->
      if (i <: nat) = (j <: nat) then (one <: t) else (zero <: t)

(* Scalar multiple of identity. *)
let scalar_identity (#t: Type) {| cr: commutative_ring t |} (#n: pos) (c: t)
  : square_matrix t n
  = fun (i: fin n) (j: fin n) ->
      if (i <: nat) = (j <: nat) then c else (zero <: t)

(* ------------------------------------------------------------------ *)
(*  Diagonal case: (adj M * M)(i,i) = det M                           *)
(*                                                                     *)
(*  (adj M * M)(i,i) = Σ_k adj(M)(i,k) * M(k,i)                     *)
(*                    = Σ_k signed_cofactor(M, k, i) * M(k,i)         *)
(*                    = Σ_k cofactor_term(M, k, i) ... by the         *)
(*                      rearrangement of cofactor_term.                *)
(*                                                                     *)
(*  Wait: cofactor_term m k i = (-1)^(k+i) * m(k,i) * det(minor m k i) *)
(*      = m(k,i) * signed_cofactor m k i                               *)
(*      = m(k,i) * adj(M)(i,k)                                        *)
(*      = M(k,i) * adj(M)(i,k)                                        *)
(*                                                                     *)
(*  So Σ_k adj(M)(i,k) * M(k,i) = Σ_k cofactor_term m k i = det M   *)
(*  by det_laplace_row applied with expansion row = ... wait, no.     *)
(*                                                                     *)
(*  Actually det_laplace_row expands along row i:                      *)
(*    det M = Σ_j cofactor_term m i j                                  *)
(*  But we need expansion along COLUMN i:                              *)
(*    det M = Σ_k cofactor_term m k i                                  *)
(*  This is Laplace expansion along column i.                          *)
(*                                                                     *)
(*  We can get this from det_laplace_row applied to M^T:               *)
(*    det(M^T) = Σ_j cofactor_term(M^T, i, j)                         *)
(*  and det(M^T) = det(M), minor(M^T, i, j) = transpose(minor(M,j,i)) *)
(* ------------------------------------------------------------------ *)

(* Laplace expansion along a column, derived from row expansion of transpose. *)

(* First: minor of transpose = transpose of minor (with swapped indices). *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let minor_transpose (#t: Type) (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n) (a b: fin (Prims.op_Subtraction n 1))
  : Lemma (minor (transpose m) i j a b == minor m j i b a)
  = ()
#pop-options

let minor_transpose_eq (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (matrix_eq #t #(cr.cr_r.r_add.acg_eq) #(Prims.op_Subtraction n 1)
             (minor (transpose m) i j)
             (transpose #t #(Prims.op_Subtraction n 1) (minor m j i)))
  = let lhs = minor (transpose m) i j in
    let rhs = transpose #t #(Prims.op_Subtraction n 1) (minor m j i) in
    let aux (a b: fin (Prims.op_Subtraction n 1))
      : Lemma (lhs a b = rhs a b)
      = minor_transpose m i j a b;
        reflexivity (minor m j i b a)
    in
    Classical.forall_intro_2 aux

(* det of minor of transpose = det of minor (via det_transpose + det_pointwise_eq). *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let det_minor_transpose (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (det #t #cr #(Prims.op_Subtraction n 1) (minor (transpose m) i j)
            = det #t #cr #(Prims.op_Subtraction n 1) (minor m j i))
  = H.elim_equatable_laws t ();
    let nm1 = Prims.op_Subtraction n 1 in
    minor_transpose_eq m i j;
    det_pointwise_eq #t #cr #nm1
      (minor (transpose m) i j)
      (transpose #t #nm1 (minor m j i));
    det_transpose #t #cr #nm1 (minor m j i);
    transitivity
      (det #t #cr #nm1 (minor (transpose m) i j))
      (det #t #cr #nm1 (transpose #t #nm1 (minor m j i)))
      (det #t #cr #nm1 (minor m j i))
#pop-options

(* signed_cofactor of transpose relates to signed_cofactor of original. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let signed_cofactor_transpose (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (signed_cofactor (transpose m) i j = signed_cofactor m j i)
  = H.elim_equatable_laws t ();
    det_minor_transpose m i j;
    (* (-1)^(i+j) * det(minor(M^T, i, j)) = (-1)^(j+i) * det(minor(M, j, i))
       and i+j = j+i *)
    assert (Prims.op_Addition (i <: nat) (j <: nat) =
            Prims.op_Addition (j <: nat) (i <: nat));
    reflexivity (minus_one_pow #t #cr (Prims.op_Addition (i <: nat) (j <: nat)));
    mul_congruence
      (minus_one_pow #t #cr (Prims.op_Addition (i <: nat) (j <: nat)))
      (det #t #cr #(Prims.op_Subtraction n 1) (minor (transpose m) i j))
      (minus_one_pow #t #cr (Prims.op_Addition (j <: nat) (i <: nat)))
      (det #t #cr #(Prims.op_Subtraction n 1) (minor m j i))
#pop-options

(* Laplace expansion along column j:
   det M = Σ_i cofactor_term_col m i j
   where cofactor_term_col m i j = m(i,j) * signed_cofactor m i j. *)

(* Actually we define a simpler "column cofactor summand": *)
let col_cofactor_summand (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (j: fin n) (i: fin n) : t
  = m i j * signed_cofactor m i j

#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let det_laplace_col
  (#t: Type) {| cr: commutative_ring t |}
  (#n: pos{n > 1}) (m: square_matrix t n) (j: fin n)
  : Lemma (det #t #cr #n m = fin_sum (col_cofactor_summand m j))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    det_transpose #t #cr #n m;
    symmetry (det (transpose m)) (det m);
    det_laplace_row #t #cr #n (transpose m) j;
    (* now: det m = det(M^T) and det(M^T) = fin_sum(cofactor_term M^T j) *)
    transitivity (det m) (det (transpose m))
                 (fin_sum (cofactor_term #t #cr (transpose m) j));
    (* now: det m = fin_sum(cofactor_term M^T j) *)
    let pw (i: fin n) : Lemma (cofactor_term #t #cr (transpose m) j i
                              = col_cofactor_summand m j i)
      = cofactor_term_eq_entry_times_signed_cofactor (transpose m) j i;
        signed_cofactor_transpose m j i;
        reflexivity (m i j);
        mul_congruence (transpose m j i) (signed_cofactor (transpose m) j i)
                       (m i j) (signed_cofactor m i j);
        transitivity (cofactor_term (transpose m) j i)
                     (transpose m j i * signed_cofactor (transpose m) j i)
                     (m i j * signed_cofactor m i j)
    in
    Classical.forall_intro pw;
    fin_sum_congruence (cofactor_term #t #cr (transpose m) j)
                       (col_cofactor_summand m j) (fun _ -> ());
    transitivity (det m) (fin_sum (cofactor_term #t #cr (transpose m) j))
                 (fin_sum (col_cofactor_summand m j))
#pop-options


(* ------------------------------------------------------------------ *)
(*  "Fake" Laplace: expand along column j using row entries from       *)
(*  a DIFFERENT column i ≠ j. This gives zero (because it's the       *)
(*  determinant of a matrix with two equal columns).                   *)
(* ------------------------------------------------------------------ *)

(* Matrix with column j replaced by column i. *)
let col_duplicate (#t: Type) (#n: pos)
  (m: square_matrix t n) (i j: fin n) : square_matrix t n
  = fun (r: fin n) (c: fin n) ->
      if (c <: nat) = (j <: nat) then m r i else m r c

(* The minor at (k, j) of col_duplicate is the same as minor at (k, j) of m,
   since we only changed column j and minor deletes column j. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let minor_col_duplicate_at_j (#t: Type) (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n) (k: fin n)
  (a b: fin (Prims.op_Subtraction n 1))
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  minor (col_duplicate m i j) k j a b == minor m k j a b)
  = (* In minor we delete column j, so column index c = skip j b ≠ j.
       Hence col_duplicate m i j (skip k a) (skip j b) = m (skip k a) (skip j b). *)
    skip_avoids j b
#pop-options

let minor_col_duplicate_eq (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n) (k: fin n)
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  matrix_eq #t #(cr.cr_r.r_add.acg_eq)
                      #(Prims.op_Subtraction n 1)
                      (minor (col_duplicate m i j) k j)
                      (minor m k j))
  = let aux (a b: fin (Prims.op_Subtraction n 1))
      : Lemma (minor (col_duplicate m i j) k j a b = minor m k j a b)
      = minor_col_duplicate_at_j m i j k a b;
        reflexivity (minor m k j a b)
    in
    Classical.forall_intro_2 aux

(* The "fake Laplace" sum: Σ_k m(k,i) * signed_cofactor(m, k, j). *)
let fake_laplace_summand (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n) (k: fin n) : t
  = m k i * signed_cofactor m k j

(* This equals det of col_duplicate m i j = 0 (two equal columns). *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let fake_laplace_is_det_col_duplicate
  (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  fin_sum (fake_laplace_summand m i j)
                  = det (col_duplicate m i j))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    det_laplace_col (col_duplicate m i j) j;
    (* det(col_dup) = fin_sum(col_cofactor_summand (col_dup) j) *)
    let pw (k: fin n)
      : Lemma (col_cofactor_summand (col_duplicate m i j) j k
             = fake_laplace_summand m i j k)
      = minor_col_duplicate_eq #t #cr m i j k;
        det_pointwise_eq #t #cr #(Prims.op_Subtraction n 1)
          (minor (col_duplicate m i j) k j) (minor m k j);
        reflexivity (minus_one_pow #t #cr (Prims.op_Addition (k <: nat) (j <: nat)));
        mul_congruence
          (minus_one_pow #t #cr (Prims.op_Addition (k <: nat) (j <: nat)))
          (det #t #cr #(Prims.op_Subtraction n 1) (minor (col_duplicate m i j) k j))
          (minus_one_pow #t #cr (Prims.op_Addition (k <: nat) (j <: nat)))
          (det #t #cr #(Prims.op_Subtraction n 1) (minor m k j));
        reflexivity (m k i);
        mul_congruence (col_duplicate m i j k j)
                       (signed_cofactor (col_duplicate m i j) k j)
                       (m k i) (signed_cofactor m k j)
    in
    Classical.forall_intro pw;
    fin_sum_congruence (col_cofactor_summand (col_duplicate m i j) j)
                       (fake_laplace_summand m i j) (fun _ -> ());
    transitivity (det (col_duplicate m i j))
                 (fin_sum (col_cofactor_summand (col_duplicate m i j) j))
                 (fin_sum (fake_laplace_summand m i j));
    symmetry (det (col_duplicate m i j)) (fin_sum (fake_laplace_summand m i j))
#pop-options

(* col_duplicate has two equal columns → det = 0. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let det_col_duplicate_zero (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  det (col_duplicate m i j) = (zero <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let m' = col_duplicate m i j in
    let tm = transpose m' in
    let cols_eq (r: fin n) : Lemma (m' r i = m' r j)
      = reflexivity (m r i)
    in
    Classical.forall_intro cols_eq;
    let rows_eq (c: fin n) : Lemma (tm i c = tm j c)
      = cols_eq c
    in
    Classical.forall_intro rows_eq;
    det_two_equal_rows_cr #t #cr #n tm i j;
    (* det tm = zero *)
    det_transpose #t #cr #n m';
    (* det tm = det m' *)
    symmetry (det tm) (det m');
    (* det m' = det tm *)
    transitivity (det m') (det tm) (zero <: t)
#pop-options

(* Combine: fake Laplace sum = 0 when i ≠ j. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let fake_laplace_zero (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  fin_sum (fake_laplace_summand m i j) = (zero <: t))
  = H.trans_for_calc t ();
    fake_laplace_is_det_col_duplicate m i j;
    det_col_duplicate_zero m i j;
    transitivity (fin_sum (fake_laplace_summand m i j))
                 (det (col_duplicate m i j)) (zero <: t)
#pop-options

(* ================================================================== *)
(*  Main theorem: adj(M) * M = det(M) * I                             *)
(* ================================================================== *)

(* Entry (i,j) of adj(M) * M. *)
(* (adj M * M)(i,j) = Σ_k adj(M)(i,k) * M(k,j)
                     = Σ_k signed_cofactor(M, k, i) * M(k,j) *)

(* When i = j: this is col_cofactor_summand m i = Σ_k M(k,i) * signed_cofactor(M,k,i) = det M *)
(* When i ≠ j: this is fake_laplace_summand m j i = Σ_k M(k,j) * signed_cofactor(M,k,i) = 0 *)

(* adj_mul_summand m i j k = adjugate m i k * m k j
                           = signed_cofactor m k i * m k j
                           = m k j * signed_cofactor m k i (by commutativity) *)

(* Diagonal entry: *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let adj_mul_diagonal (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i: fin n)
  : Lemma (matrix_mul (adjugate m) m i i = det m)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    matrix_mul_to_fin_sum #t #cr.cr_r (adjugate m) m i i;
    H.leibniz_to_eq (matrix_mul (adjugate m) m i i)
                    (fin_sum #t #(acg_of_r t #cr.cr_r) #n
                      (pointwise_mul (row (adjugate m) i) (col m i)));
    let pw (k: fin n)
      : Lemma (pointwise_mul (row (adjugate m) i) (col m i) k
             = col_cofactor_summand m i k)
      = mul_commutativity #t #cr.cr_r (signed_cofactor m k i) (m k i)
    in
    Classical.forall_intro pw;
    fin_sum_congruence #t #(acg_of_r t #cr.cr_r) #n
      (pointwise_mul (row (adjugate m) i) (col m i))
      (col_cofactor_summand m i) (fun _ -> ());
    transitivity (matrix_mul (adjugate m) m i i)
                 (fin_sum #t #(acg_of_r t #cr.cr_r) #n
                   (pointwise_mul (row (adjugate m) i) (col m i)))
                 (fin_sum (col_cofactor_summand m i));
    det_laplace_col m i;
    symmetry (det m) (fin_sum (col_cofactor_summand m i));
    transitivity (matrix_mul (adjugate m) m i i)
                 (fin_sum (col_cofactor_summand m i)) (det m)
#pop-options

(* Off-diagonal entry: *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let adj_mul_off_diagonal (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  matrix_mul (adjugate m) m i j = (zero <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    matrix_mul_to_fin_sum #t #cr.cr_r (adjugate m) m i j;
    H.leibniz_to_eq (matrix_mul (adjugate m) m i j)
                    (fin_sum #t #(acg_of_r t #cr.cr_r) #n
                      (pointwise_mul (row (adjugate m) i) (col m j)));
    let pw (k: fin n)
      : Lemma (pointwise_mul (row (adjugate m) i) (col m j) k
             = fake_laplace_summand m j i k)
      = mul_commutativity #t #cr.cr_r (signed_cofactor m k i) (m k j)
    in
    Classical.forall_intro pw;
    fin_sum_congruence #t #(acg_of_r t #cr.cr_r) #n
      (pointwise_mul (row (adjugate m) i) (col m j))
      (fake_laplace_summand m j i) (fun _ -> ());
    transitivity (matrix_mul (adjugate m) m i j)
                 (fin_sum #t #(acg_of_r t #cr.cr_r) #n
                   (pointwise_mul (row (adjugate m) i) (col m j)))
                 (fin_sum (fake_laplace_summand m j i));
    fake_laplace_zero m j i;
    transitivity (matrix_mul (adjugate m) m i j)
                 (fin_sum (fake_laplace_summand m j i)) (zero <: t)
#pop-options

(* ================================================================== *)
(*  Headline: adj(M) * M = det(M) * I  (pointwise equality)          *)
(* ================================================================== *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let adjugate_mul_eq_det_identity (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n)
  : Lemma (matrix_eq (matrix_mul (adjugate m) m) (scalar_identity (det m)))
  = H.elim_equatable_laws t ();
    let lhs = matrix_mul (adjugate m) m in
    let rhs = scalar_identity #t #cr #n (det m) in
    let pointwise (i j: fin n) : Lemma (lhs i j = rhs i j)
      = if (i <: nat) = (j <: nat) then begin
          adj_mul_diagonal m i;
          reflexivity (det m)
        end else begin
          adj_mul_off_diagonal m i j;
          reflexivity (zero <: t)
        end
    in
    Classical.forall_intro_2 pointwise
#pop-options
