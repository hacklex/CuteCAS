module Core.Matrix.KernelDet

(*
   Main theorem: det(M) = 0 ⟹ ∃ nonzero v ∈ ker(M).

   Strategy:
   - Case adj(M) ≠ 0: Right adjugate identity M·adj(M) = det(M)·I gives
     nonzero column of adj(M) as kernel vector.
   - Case adj(M) = 0, M ≠ 0: Column elimination via row_add creates a
     pivot column, Laplace gives det(minor)=0, recurse on minor, extend.
   - Case M = 0: any e_i works.
*)

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
open Core.Matrix.Ring
open Core.Matrix.Determinant
open Core.Matrix.Adjugate
open Core.Vector

(* ================================================================== *)
(*  Part A: Right adjugate identity M · adj(M) = det(M) · I           *)
(*                                                                     *)
(*  Diagonal:   (M · adj(M))(i,i) = Σ_k M(i,k)·adj(M)(k,i)          *)
(*            = Σ_k M(i,k)·signed_cofactor(M,i,k)                     *)
(*            = Σ_k cofactor_term(M,i,k) = det M  (Laplace row i)     *)
(*                                                                     *)
(*  Off-diag:  (M · adj(M))(i,j) = Σ_k M(i,k)·signed_cofactor(M,j,k) *)
(*            = det(M with row j replaced by row i) = 0                *)
(*            (two equal rows ⟹ det=0)                                *)
(* ================================================================== *)

(* Row-replaced matrix: row j is replaced by row i. *)
let row_replace (#t: Type) (#n: pos) (m: square_matrix t n) (src dst: fin n)
  : square_matrix t n
  = fun (r: fin n) (c: fin n) -> if (r <: nat) = (dst <: nat) then m src c else m r c

(* Row Laplace summand: M(i,k) * signed_cofactor(M, j, k). *)
let row_adj_summand (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n) (k: fin n) : t
  = m i k * signed_cofactor m j k

(* minor of row_replace at the replaced row = minor of original *)
(* minor of row_replace at the deleted row = minor of original.
   Key: deleting row dst from (row_replace m src dst) leaves all other
   rows unchanged (they still come from m). *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let minor_row_replace_at_dst (#t: Type) (#n: pos{n > 1})
  (m: square_matrix t n) (src dst: fin n) (col: fin n)
  (a b: fin (Prims.op_Subtraction n 1))
  : Lemma (requires (src <: nat) <> (dst <: nat))
          (ensures  minor (row_replace m src dst) dst col a b ==
                    minor m dst col a b)
  = skip_avoids dst a
#pop-options

(* Row-adj summand = cofactor_term of row-replaced matrix along row dst. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let row_adj_summand_eq_cofactor_of_replaced
  (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n) (k: fin n)
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  row_adj_summand m i j k = cofactor_term (row_replace m i j) j k)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let minor_eq (a: fin (Prims.op_Subtraction n 1)) (b: fin (Prims.op_Subtraction n 1))
      : Lemma (minor (row_replace m i j) j k a b == minor m j k a b)
      = minor_row_replace_at_dst m i j k a b
    in
    Classical.forall_intro_2 minor_eq;
    let mop = minus_one_pow #t #cr (Prims.op_Addition (j <: nat) (k <: nat)) in
    let det_min = det #t #cr #(Prims.op_Subtraction n 1) (minor m j k) in
    let det_rep = det #t #cr #(Prims.op_Subtraction n 1) (minor (row_replace m i j) j k) in
    let e = m i k in
    (* cofactor_term(replace, j, k) = (mop * e) * det_rep  [by definition]
       det_rep = det_min  [from det_pointwise_eq]
       row_adj_summand = e * (mop * det_min)  [by definition]
       Need: e * (mop * det_min) = (mop * e) * det_min *)
    assert (row_replace m i j j k == e);
    det_pointwise_eq #t #cr #(Prims.op_Subtraction n 1)
      (minor (row_replace m i j) j k) (minor m j k);
    (* det_rep = det_min *)
    mul_congruence (mop * e) det_rep (mop * e) det_min;
    (* (mop * e) * det_rep = (mop * e) * det_min *)
    (* cofactor_term(replace) == (mop * e) * det_rep by Leibniz unfolding,
       so cofactor_term(replace) = (mop * e) * det_min *)
    mul_commutativity #t #cr.cr_r mop e;
    mul_congruence (mop * e) det_min (e * mop) det_min;
    (* (mop * e) * det_min = (e * mop) * det_min *)
    mul_associativity #t #cr.cr_r e mop det_min;
    (* (e * mop) * det_min = e * (mop * det_min) *)
    (* Chain: cofactor_term(replace) = (mop*e)*det_min = (e*mop)*det_min = e*(mop*det_min) *)
    transitivity (cofactor_term (row_replace m i j) j k)
                 ((mop * e) * det_min) ((e * mop) * det_min);
    transitivity (cofactor_term (row_replace m i j) j k)
                 ((e * mop) * det_min) (e * (mop * det_min));
    (* row_adj_summand = e * signed_cofactor m j k = e * (mop * det_min) *)
    transitivity (row_adj_summand m i j k)
                 (e * (mop * det_min))
                 (cofactor_term (row_replace m i j) j k)
#pop-options

(* The fake row Laplace sum is zero for i ≠ j. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let fake_row_laplace_zero (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  fin_sum (row_adj_summand m i j) = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    (* Σ_k row_adj_summand m i j k = Σ_k cofactor_term(replace, j, k) *)
    let pw (k: fin n)
      : Lemma (row_adj_summand m i j k = cofactor_term (row_replace m i j) j k)
      = row_adj_summand_eq_cofactor_of_replaced m i j k
    in
    Classical.forall_intro pw;
    fin_sum_congruence (row_adj_summand m i j)
                       (cofactor_term (row_replace m i j) j) (fun _ -> ());
    (* Σ_k cofactor_term(replace, j, k) = det(replace) by Laplace row j *)
    det_laplace_row (row_replace m i j) j;
    symmetry (det (row_replace m i j))
             (fin_sum (cofactor_term (row_replace m i j) j));
    transitivity (fin_sum (row_adj_summand m i j))
                 (fin_sum (cofactor_term (row_replace m i j) j))
                 (det (row_replace m i j));
    (* det(replace) = 0 because rows i and j are equal *)
    let rows_eq (c: fin n)
      : Lemma (row_replace m i j i c = row_replace m i j j c)
      = ()
    in
    Classical.forall_intro rows_eq;
    det_two_equal_rows_cr (row_replace m i j) i j;
    transitivity (fin_sum (row_adj_summand m i j))
                 (det (row_replace m i j)) (zero <: t)
#pop-options

(* Right adjugate: (M · adj(M))(i,j) = 0 for i ≠ j. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let right_adj_off_diagonal (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  matrix_mul m (adjugate m) i j = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    matrix_mul_to_fin_sum m (adjugate m) i j;
    H.leibniz_to_eq (matrix_mul m (adjugate m) i j)
                    (fin_sum #t #(acg_of_r t #cr.cr_r) #n
                      (pointwise_mul (row m i) (col (adjugate m) j)));
    (* (M · adj(M))(i,j) = Σ_k m(i,k) * adj(m)(k,j)
                          = Σ_k m(i,k) * signed_cofactor(m, j, k) *)
    let pw (k: fin n)
      : Lemma (pointwise_mul (row m i) (col (adjugate m) j) k
             = row_adj_summand m i j k)
      = reflexivity (m i k * signed_cofactor m j k)
    in
    Classical.forall_intro pw;
    fin_sum_congruence (pointwise_mul (row m i) (col (adjugate m) j))
                       (row_adj_summand m i j) (fun _ -> ());
    fake_row_laplace_zero m i j;
    transitivity (matrix_mul m (adjugate m) i j)
                 (fin_sum (pointwise_mul (row m i) (col (adjugate m) j)))
                 (fin_sum (row_adj_summand m i j));
    transitivity (matrix_mul m (adjugate m) i j)
                 (fin_sum (row_adj_summand m i j)) (zero <: t)
#pop-options

(* Right adjugate: (M · adj(M))(i,i) = det M. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let right_adj_diagonal (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i: fin n)
  : Lemma (matrix_mul m (adjugate m) i i = det m)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    matrix_mul_to_fin_sum m (adjugate m) i i;
    H.leibniz_to_eq (matrix_mul m (adjugate m) i i)
                    (fin_sum #t #(acg_of_r t #cr.cr_r) #n
                      (pointwise_mul (row m i) (col (adjugate m) i)));
    (* Σ_k m(i,k) * adj(m)(k,i) = Σ_k m(i,k) * signed_cofactor(m,i,k)
       = Σ_k cofactor_term(m, i, k) = det m *)
    let pw (k: fin n)
      : Lemma (pointwise_mul (row m i) (col (adjugate m) i) k
             = cofactor_term m i k)
      = cofactor_term_eq_entry_times_signed_cofactor m i k
    in
    Classical.forall_intro pw;
    fin_sum_congruence (pointwise_mul (row m i) (col (adjugate m) i))
                       (cofactor_term m i) (fun _ -> ());
    det_laplace_row m i;
    transitivity (matrix_mul m (adjugate m) i i)
                 (fin_sum (pointwise_mul (row m i) (col (adjugate m) i)))
                 (fin_sum (cofactor_term m i));
    transitivity (matrix_mul m (adjugate m) i i)
                 (fin_sum (cofactor_term m i)) (det m)
#pop-options

(* Corollary: if det(M) = 0, then M · (column j of adj(M)) = zero vector. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let adj_column_in_kernel (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (j: fin n) (i: fin n)
  : Lemma (requires det m = (zero <: t))
          (ensures  matrix_mul m (adjugate m) i j = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if (i <: nat) = (j <: nat)
    then begin
      right_adj_diagonal m i;
      transitivity (matrix_mul m (adjugate m) i j)
                   (matrix_mul m (adjugate m) i i) (det m);
      transitivity (matrix_mul m (adjugate m) i j) (det m) (zero <: t)
    end
    else right_adj_off_diagonal m i j
#pop-options

(* ================================================================== *)
(*  Part B: Column elimination                                        *)
(*                                                                     *)
(*  Given M with M(i₀,j₀) ≠ 0, eliminate all other entries in        *)
(*  column j₀ via row operations. The resulting matrix has column j₀  *)
(*  = M(i₀,j₀)·e_{i₀} and det unchanged.                            *)
(* ================================================================== *)

(* The eliminated matrix. *)
let elim_col (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r: fin n) (piv_c: fin n{is_nonzero (m piv_r piv_c)})
  : square_matrix t n
  = let pivot_inv : t = inv (m piv_r piv_c) in
    fun (i: fin n) (j: fin n) ->
      if (i <: nat) = (piv_r <: nat) then m i j
      else m i j -- (m i piv_c * pivot_inv) * m piv_r j

(* Column piv_c of eliminated matrix: zero except at pivot. *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
let elim_col_pivot (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r piv_c: fin n)
  : Lemma (requires is_nonzero (m piv_r piv_c))
          (ensures  elim_col m piv_r piv_c piv_r piv_c = m piv_r piv_c)
  = elim_equatable_laws t ();
    assert (elim_col m piv_r piv_c piv_r piv_c == m piv_r piv_c)
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
let elim_col_zero (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r piv_c: fin n) (i: fin n)
  : Lemma (requires is_nonzero (m piv_r piv_c) /\ (i <: nat) <> (piv_r <: nat))
          (ensures  elim_col m piv_r piv_c i piv_c = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let pivot_inv : t = inv (m piv_r piv_c) in
    let c : t = m i piv_c * pivot_inv in
    (* Need: c * pivot = m i piv_c *)
    inversion_lemma (m piv_r piv_c);
    (* inv(piv) * piv = one *)
    mul_associativity #t #(r_of_sf t) (m i piv_c) pivot_inv (m piv_r piv_c);
    (* (m i piv_c * inv(piv)) * piv = m i piv_c * (inv(piv) * piv) *)
    mul_congruence (m i piv_c) (pivot_inv * m piv_r piv_c)
                   (m i piv_c) (one <: t);
    (* m i piv_c * (inv(piv) * piv) = m i piv_c * one *)
    x_mul_one (m i piv_c);
    (* m i piv_c * one = m i piv_c *)
    transitivity (c * m piv_r piv_c) (m i piv_c * (pivot_inv * m piv_r piv_c))
                 (m i piv_c * (one <: t));
    (* c * pivot = m i piv_c *)
    neg_congruence (c * m piv_r piv_c) (m i piv_c);
    (* neg(c * pivot) = neg(m i piv_c) *)
    add_congruence (m i piv_c) (neg (c * m piv_r piv_c))
                   (m i piv_c) (neg (m i piv_c));
    (* m i piv_c + neg(c * pivot) = m i piv_c + neg(m i piv_c) *)
    x_plus_neg_x (m i piv_c)
    (* m i piv_c + neg(m i piv_c) = zero *)
#pop-options

(* Determinant of eliminated matrix equals original determinant.
   Each row operation is: row_i -= c * row_{piv_r}, which preserves det.
   We prove this for ONE row operation; the general case follows by induction
   over rows i ≠ piv_r. For simplicity we prove det(elim) = det(m) directly
   by showing elim = sequential row_adds applied to m. *)

(* Row addition (local): add c * row_j to row_i. *)
let row_add_local (#t: Type) {| r: ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n) (c: t) : square_matrix t n
  = fun (a: fin n) (b: fin n) ->
      if (a <: nat) = (i <: nat) then m a b + c * m j b else m a b

(* det(row_add m i j c) = det m, via transpose + det_col_add. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
let det_row_add (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n) (c: t)
  : Lemma (requires ~(i == j))
          (ensures  det (row_add_local #t #cr.cr_r m i j c) = det m)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let ra = row_add_local #t #cr.cr_r m i j c in
    let ca = col_add #t #cr.cr_r (transpose m) i j c in
    let pw (a b: fin n) : Lemma (transpose ra a b = ca a b)
      = mul_commutativity #t #cr.cr_r c (m j a);
        if Prims.op_Equality (b <: nat) (i <: nat) then
          add_congruence (m b a) (c * m j a) (m b a) (m j a * c)
        else ()
    in
    Classical.forall_intro_2 pw;
    det_pointwise_eq #t #cr #n (transpose ra) ca;
    det_transpose #t #cr #n ra;
    det_col_add #t #cr #n (transpose m) i j c;
    det_transpose #t #cr #n m
#pop-options

(* ================================================================== *)
(*  Part B2: det(elim_col) = det(m)                                    *)
(*                                                                     *)
(*  Strategy: partial_elim processes one row at a time. Each step is   *)
(*  a row_add that preserves det. Chain gives the result.              *)
(* ================================================================== *)

(* Partial elimination: rows below index k (excluding piv_r) are
   already eliminated; rows at or above k stay as original m. *)
private let partial_elim (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r piv_c: fin n{is_nonzero (m piv_r piv_c)})
  (k: nat{k <= n})
  : square_matrix t n
  = fun (i: fin n) (j: fin n) ->
      if (i <: nat) < k && (i <: nat) <> (piv_r <: nat)
      then elim_col m piv_r piv_c i j
      else m i j

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
private let partial_elim_zero (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r piv_c: fin n{is_nonzero (m piv_r piv_c)})
  : Lemma (det (partial_elim m piv_r piv_c 0) = det m)
  = elim_equatable_laws t ();
    let pw (a b: fin n)
      : Lemma (partial_elim m piv_r piv_c 0 a b = m a b)
      = ()
    in
    Classical.forall_intro_2 pw;
    det_pointwise_eq (partial_elim m piv_r piv_c 0) m
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
private let partial_elim_full (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r piv_c: fin n{is_nonzero (m piv_r piv_c)})
  : Lemma (det (partial_elim m piv_r piv_c n) = det (elim_col m piv_r piv_c))
  = elim_equatable_laws t ();
    let pw (a b: fin n)
      : Lemma (partial_elim m piv_r piv_c n a b = elim_col m piv_r piv_c a b)
      = if (a <: nat) = (piv_r <: nat) then ()
        else ()
    in
    Classical.forall_intro_2 pw;
    det_pointwise_eq (partial_elim m piv_r piv_c n) (elim_col m piv_r piv_c)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
private let partial_elim_step (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r piv_c: fin n{is_nonzero (m piv_r piv_c)})
  (k: fin n)
  : Lemma (det (partial_elim m piv_r piv_c (Prims.op_Addition (k <: nat) 1))
         = det (partial_elim m piv_r piv_c (k <: nat)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let pivot_inv : t = inv (m piv_r piv_c) in
    let c_k : t = neg (m k piv_c * pivot_inv) in
    let pe_k = partial_elim m piv_r piv_c (k <: nat) in
    let pe_k1 = partial_elim m piv_r piv_c (Prims.op_Addition (k <: nat) 1) in
    if (k <: nat) = (piv_r <: nat) then begin
      let pw (a b: fin n)
        : Lemma (pe_k1 a b = pe_k a b)
        = ()
      in
      Classical.forall_intro_2 pw;
      det_pointwise_eq pe_k1 pe_k
    end
    else begin
      let ra = row_add_local #t #(cr_of_id t #(id_of_f t)).cr_r pe_k k piv_r c_k in
      let pw (a b: fin n)
        : Lemma (pe_k1 a b = ra a b)
        = if (a <: nat) = (k <: nat) then begin
            let x = m k piv_c * pivot_inv in
            let y = m piv_r b in
            neg_mul_l #t #(r_of_sf t) x y;
            add_congruence (m k b) (neg (x * y)) (m k b) (neg x * y)
          end
          else ()
      in
      Classical.forall_intro_2 pw;
      det_pointwise_eq pe_k1 ra;
      det_row_add #t #(cr_of_id t #(id_of_f t)) pe_k k piv_r c_k
    end
#pop-options

private let rec det_partial_elim_eq (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r piv_c: fin n{is_nonzero (m piv_r piv_c)})
  (k: nat{k <= n})
  : Lemma (ensures det (partial_elim m piv_r piv_c k) = det m)
          (decreases k)
  = if k = 0 then partial_elim_zero m piv_r piv_c
    else begin
      det_partial_elim_eq m piv_r piv_c (k - 1);
      partial_elim_step m piv_r piv_c (k - 1 <: fin n);
      elim_equatable_laws t ();
      transitivity (det (partial_elim m piv_r piv_c k))
                   (det (partial_elim m piv_r piv_c (k - 1)))
                   (det m)
    end

let det_elim_col_eq (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r piv_c: fin n)
  : Lemma (requires is_nonzero (m piv_r piv_c))
          (ensures  det (elim_col m piv_r piv_c) = det m)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    det_partial_elim_eq m piv_r piv_c n;
    partial_elim_full m piv_r piv_c;
    transitivity (det (elim_col m piv_r piv_c))
                 (det (partial_elim m piv_r piv_c n))
                 (det m)

(* ================================================================== *)
(*  Part B3: Laplace helpers for the inductive case                    *)
(*                                                                     *)
(*  These bridge the TC diamond between field and commutative_ring     *)
(*  contexts, enabling det_laplace_row's postcondition to be used      *)
(*  in field-context proofs.                                           *)
(* ================================================================== *)

(* fin_sum_only_at: if f vanishes off index k, then fin_sum f = f k *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 120"
private let fin_sum_only_at (#t: Type) {| r: ring t |} (#n: pos)
  (f: fin n -> t) (k: fin n)
  (h: (j: fin n) -> Lemma (requires j <> k) (ensures f j = (zero <: t)))
  : Lemma (fin_sum f = f k)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let pw_eq (j: fin n) : Lemma (f j = pointwise_mul (fin_kronecker_delta k) f j)
      = pointwise_mul_unfold #(fin n) #t #r (fin_kronecker_delta k) f j;
        fin_kronecker_delta_unfold #t #r #n k j;
        if (j <: nat) = (k <: nat) then begin
          one_mul_x #t #r (f j);
          symmetry (one * f j) (f j)
        end else begin
          h j;
          zero_mul_x #t #r (f j);
          transitivity (f j) (zero <: t) ((zero <: t) * f j)
        end
    in
    fin_sum_congruence f (pointwise_mul (fin_kronecker_delta k) f) pw_eq;
    fin_sum_kronecker #t #r #n k f
#pop-options

(* cofactor_term is zero when the matrix entry is zero *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
private let cofactor_term_zero_entry (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires m i j = (zero <: t))
          (ensures  cofactor_term m i j = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let r = cr.cr_r in
    let s = minus_one_pow #t #cr (Prims.op_Addition (i <: nat) (j <: nat)) in
    let d = det #t #cr #(Prims.op_Subtraction n 1) (minor m i j) in
    x_mul_zero #t #r s;
    mul_congruence #t #r s (m i j) s (zero <: t);
    zero_mul_x #t #r d;
    mul_congruence #t #r (s * m i j) d (zero <: t) d;
    transitivity (s * m i j * d) ((zero <: t) * d) (zero <: t)
#pop-options

(* -(one) is nonzero in any field *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
private let neg_one_nonzero (#t: Type) {| f: field t |}
  : Lemma (is_nonzero (-(one <: t)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let one_ne_zero : squash (is_nonzero (one <: t)) = (id_of_f t #f).id_one_ne_zero in
    if not (is_nonzero (-(one <: t))) then begin
      x_plus_neg_x (one <: t);
      add_congruence (one <: t) (-(one <: t)) (one <: t) (zero <: t);
      add_zero (one <: t);
      ()
    end else ()
#pop-options

(* (-1)^k is nonzero in any field *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
private let minus_one_pow_nonzero (#t: Type) {| f: field t |} (k: nat)
  : Lemma (is_nonzero (minus_one_pow #t #(cr_of_id t #(id_of_f t)) k))
  = if Prims.op_Modulus k 2 = 0 then
      (id_of_f t #f).id_one_ne_zero
    else
      neg_one_nonzero #t #f
#pop-options

(* TC bridge wrappers: re-state det lemmas in field context *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
private let det_laplace_row_f (#t: Type) {| f: field t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i: fin n)
  : Lemma (det m = fin_sum (cofactor_term m i))
  = det_laplace_row m i

private let det_minor_transpose_f (#t: Type) {| f: field t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (det (minor (transpose m) i j) = det (minor m j i))
  = det_minor_transpose m i j
#pop-options

(* Laplace column argument: if a matrix has a single-nonzero-entry column
   and det = 0, then the minor at that entry also has det = 0. *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 80"
private let det_zero_single_entry_col (#t: Type) {| f: field t |} (#n: pos{n > 1})
  (m: square_matrix t n) (r c: fin n)
  : Lemma (requires det m = (zero <: t) /\ is_nonzero (m r c) /\
                   (forall (i: fin n). (i <: nat) <> (r <: nat) ==> m i c = (zero <: t)))
          (ensures  det (minor m r c) = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    det_transpose m;
    det_laplace_row_f (transpose m) c;
    let ct_zero (j: fin n)
      : Lemma (requires j <> r) (ensures cofactor_term (transpose m) c j = (zero <: t))
      = assert ((transpose m) c j == m j c);
        cofactor_term_zero_entry (transpose m) c j
    in
    fin_sum_only_at (cofactor_term (transpose m) c) r ct_zero;
    transitivity (det (transpose m)) (fin_sum (cofactor_term (transpose m) c))
                 (cofactor_term (transpose m) c r);
    assert ((transpose m) c r == m r c);
    let s = minus_one_pow (Prims.op_Addition (c <: nat) (r <: nat)) in
    det_minor_transpose_f m c r;
    mul_congruence (s * m r c) (det (minor (transpose m) c r))
                   (s * m r c) (det (minor m r c));
    let d : domain t = (id_of_f t #f).id_d in
    minus_one_pow_nonzero #t #f (Prims.op_Addition (c <: nat) (r <: nat));
    domain_nonzero_mul_nonzero #t #d s (m r c);
    d.domain_law (s * m r c) (det (minor m r c))
#pop-options

(* ================================================================== *)
(*  Part C: Main theorem — det(M)=0 ⟹ ∃ nonzero v ∈ ker(M)          *)
(*                                                                     *)
(*  We state the result as a Lemma with an existential conclusion.    *)
(*  The proof is by strong induction on n.                            *)
(* ================================================================== *)

(* det_1x1: for a 1×1 matrix, det m = m 0 0 *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
private let det_1x1 (#t: Type) {| f: field t |} (m: square_matrix t 1)
  : Lemma (det m = m 0 0)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let id1 = identity 1 in
    let all_eq_id (q: permutation 1)
      : Lemma (perm_eq id1 q)
      = let pf (i: fin 1) : Lemma (id1.fwd i == q.fwd i) = () in
        perm_eq_intro id1 q pf
    in
    let h_zero (q: permutation 1)
      : Lemma (requires ~(perm_eq id1 q))
              (ensures  leibniz_term m q = (zero <: t))
      = all_eq_id q
    in
    leibniz_term_respects_perm_eq m;
    sum_over_perms_single 1 (leibniz_term m) id1 h_zero;
    parity_identity 1;
    perm_product_unfold m id1;
    prod_range_singleton (fun (i:nat) -> if i < 1 then m i (id1.fwd i) else (one <: t)) 0;
    x_mul_one (m (0 <: fin 1) (id1.fwd (0 <: fin 1)))
#pop-options

(* ================================================================== *)
(*  Part C: Main theorem                                              *)
(*                                                                     *)
(*  Case 1 (adj ≠ 0): column j of adj(M) is a kernel vector.          *)
(*  Case 2 (adj = 0, M ≠ 0): elimination-based inductive argument.    *)
(*  Case 3 (M = 0): any basis vector works.                           *)
(* ================================================================== *)

(* Case 1: If det(M) = 0 and adj(M)(r,j) ≠ 0, then column j of adj(M)
   is a nonzero kernel vector of M. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let adj_nonzero_gives_kernel (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (r j: fin n)
  : Lemma (requires det m = (zero <: t) /\ is_nonzero (adjugate m r j))
          (ensures  is_nonzero (col (adjugate m) j r) /\
                    (forall (i: fin n).
                      matrix_mul m (adjugate m) i j = (zero <: t)))
  = let col_j_at_r () : Lemma (is_nonzero (col (adjugate m) j r)) = () in
    col_j_at_r ();
    let kernel_i (i: fin n)
      : Lemma (matrix_mul m (adjugate m) i j = (zero <: t))
      = adj_column_in_kernel m j i
    in
    Classical.forall_intro kernel_i
#pop-options

(* Bridge: matrix_mul entry to vector_dot. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let mul_entry_is_dot (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a b i j = vector_dot (row a i) (col b j))
  = matrix_mul_unfold #t #cr.cr_r a b i j;
    H.leibniz_to_eq (matrix_mul a b i j) (vector_dot (row a i) (col b j))
#pop-options

(* ================================================================== *)
(*  fin_sum_skip_reindex infrastructure                                *)
(*                                                                     *)
(*  If f(c) = 0 and g(b) = f(skip c b), then fin_sum f = fin_sum g.   *)
(*  Used for the vector extension in det_zero_implies_null_vec.        *)
(* ================================================================== *)

private let unskip (#n: pos) (i: fin n) (k: fin n{(k <: nat) <> (i <: nat)})
  : fin (Prims.op_Subtraction n 1)
  = if (k <: nat) < (i <: nat) then (k <: nat) else Prims.op_Subtraction k 1

private let skip_unskip (#n: pos) (i: fin n) (k: fin n)
  : Lemma (requires (k <: nat) <> (i <: nat))
          (ensures  (skip i (unskip i k) <: nat) == (k <: nat))
  = ()

private let unskip_skip (#n: pos) (i: fin n) (a: fin (Prims.op_Subtraction n 1))
  : Lemma ((unskip i (skip i a) <: nat) == (a <: nat))
  = ()

#push-options "--fuel 1 --ifuel 0 --z3rlimit 200"
private let sum_range_reindex_helper (#t: Type) {| acg: add_comm_group t |} (#n: pos{n > 1})
  (f: fin n -> t) (c: fin n) (g: fin (Prims.op_Subtraction n 1) -> t)
  (big: nat -> t) (small: nat -> t)
  (h_skip: (b: fin (Prims.op_Subtraction n 1)) -> Lemma (f (skip c b) = g b))
  (h_big: (k: nat{k < n}) -> Lemma (big k = f (k <: fin n)))
  (h_big_else: (k: nat{k >= n}) -> Lemma (big k = (zero <: t)))
  (h_small: (k: nat{k < Prims.op_Subtraction n 1}) -> Lemma (small k = g (k <: fin (Prims.op_Subtraction n 1))))
  (h_small_else: (k: nat{k >= Prims.op_Subtraction n 1}) -> Lemma (small k = (zero <: t)))
  : Lemma (sum_range small 0 (Prims.op_Subtraction n 1) =
           sum_range big 0 c + sum_range big (Prims.op_Addition c 1) n)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let nm1 : pos = Prims.op_Subtraction n 1 in
    sum_range_split small 0 c nm1;
    let first_half (k: nat{0 <= k /\ k < c})
      : Lemma (big k = small k)
      = h_skip (k <: fin nm1);
        h_big k;
        h_small k;
        H.leibniz_to_eq (f (skip c (k <: fin nm1))) (f (k <: fin n));
        transitivity (big k) (g (k <: fin nm1)) (small k)
    in
    sum_range_congruence big small 0 c first_half;
    let second_half (k: nat{c <= k /\ k < nm1})
      : Lemma (small k = big (Prims.op_Addition k 1))
      = h_skip (k <: fin nm1);
        h_small k;
        let kp1 : fin n = Prims.op_Addition k 1 in
        h_big kp1;
        H.leibniz_to_eq (f (skip c (k <: fin nm1))) (f kp1);
        symmetry (small k) (big kp1)
    in
    let big_plus1 : (nat -> t) = (fun (j:nat) -> big (Prims.op_Addition j 1)) in
    sum_range_congruence small big_plus1 c nm1 second_half;
    sum_range_shift big 1 c nm1;
    transitivity (sum_range small c nm1) (sum_range big_plus1 c nm1)
                 (sum_range big (Prims.op_Addition c 1) n);
    add_congruence (sum_range small 0 c) (sum_range small c nm1)
                   (sum_range big 0 c) (sum_range big (Prims.op_Addition c 1) n);
    transitivity (sum_range small 0 nm1)
                 (sum_range small 0 c + sum_range small c nm1)
                 (sum_range big 0 c + sum_range big (Prims.op_Addition c 1) n)
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 120"
private let fin_sum_eliminate_zero_helper (#t: Type) {| acg: add_comm_group t |} (#n: pos{n > 1})
  (f: fin n -> t) (c: fin n) (big: nat -> t)
  (h_zero: squash (f c = (zero <: t)))
  (h_big: squash (fin_sum f = sum_range big 0 n))
  (h_big_c: squash (big c = f c))
  : Lemma (fin_sum f = sum_range big 0 c + sum_range big (Prims.op_Addition c 1) n)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_range_split big 0 c n;
    sum_range_unfold_left big c n;
    H.leibniz_to_eq (sum_range big c n) (big c + sum_range big (Prims.op_Addition c 1) n);
    zero_plus_x (sum_range big (Prims.op_Addition c 1) n);
    add_congruence (big c) (sum_range big (Prims.op_Addition c 1) n)
                   (zero <: t) (sum_range big (Prims.op_Addition c 1) n);
    transitivity (big c + sum_range big (Prims.op_Addition c 1) n)
                 ((zero <: t) + sum_range big (Prims.op_Addition c 1) n)
                 (sum_range big (Prims.op_Addition c 1) n);
    transitivity (sum_range big c n)
                 (big c + sum_range big (Prims.op_Addition c 1) n)
                 (sum_range big (Prims.op_Addition c 1) n);
    add_congruence (sum_range big 0 c) (sum_range big c n)
                   (sum_range big 0 c) (sum_range big (Prims.op_Addition c 1) n);
    transitivity (sum_range big 0 n) (sum_range big 0 c + sum_range big c n)
                 (sum_range big 0 c + sum_range big (Prims.op_Addition c 1) n);
    transitivity (fin_sum f) (sum_range big 0 n)
                 (sum_range big 0 c + sum_range big (Prims.op_Addition c 1) n)
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
private let derive_eq_via_mid (#t: Type) {| acg: add_comm_group t |}
  (fg: t) (sr_small: t) (rhs: t)
  (h1: squash (fg = sr_small))
  (h2: squash (sr_small = rhs))
  : Lemma (fg = rhs)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    transitivity fg sr_small rhs
#pop-options

(* (a + neg b) + b = a — used in elim_col decomposition *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
private let sub_add_cancel (#t: Type) {| acg: add_comm_group t |} (a b: t)
  : Lemma ((a + neg b) + b = a)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    add_associativity a (neg b) b;
    neg_x_plus_x #t #acg b;
    add_congruence a (neg b + b) a (zero <: t);
    x_plus_zero #t #acg a;
    transitivity ((a + neg b) + b) (a + (zero <: t)) a
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 80"
private let fin_sum_skip_reindex (#t: Type) {| acg: add_comm_group t |} (#n: pos{n > 1})
  (f: fin n -> t) (c: fin n) (g: fin (Prims.op_Subtraction n 1) -> t)
  (h_zero: squash (f c = (zero <: t)))
  (h_skip: (b: fin (Prims.op_Subtraction n 1)) -> Lemma (f (skip c b) = g b))
  : Lemma (fin_sum f = fin_sum g)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let nm1 : pos = Prims.op_Subtraction n 1 in
    let big : (nat -> t) = (fun (k: nat) -> if k < n then f (k <: fin n) else zero) in
    let small : (nat -> t) = (fun (k: nat) -> if k < Prims.op_Subtraction n 1 then g (k <: fin (Prims.op_Subtraction n 1)) else zero) in
    H.leibniz_to_eq (fin_sum g) (sum_range small 0 (Prims.op_Subtraction n 1));
    let h_fg : squash (fin_sum g = sum_range small 0 nm1) = () in
    H.leibniz_to_eq (fin_sum f) (sum_range big 0 n);
    fin_sum_eliminate_zero_helper f c big h_zero () ();
    sum_range_reindex_helper f c g big small h_skip
      (fun k -> ()) (fun k -> ()) (fun k -> ()) (fun k -> ());
    let rhs = sum_range big 0 c + sum_range big (Prims.op_Addition c 1) n in
    let h_sr : squash (sum_range small 0 nm1 = rhs) = () in
    derive_eq_via_mid (fin_sum g) (sum_range small 0 nm1) rhs h_fg h_sr;
    symmetry (fin_sum g) (fin_sum f)
#pop-options

(* Combined: fin_sum f = 0 when f[c]=0, f[skip c j]=g j, and fin_sum g = 0.
   All three fin_sum forms are elaborated in the SAME function, avoiding the
   cross-site lambda identity problem in SMT. *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 80"
private let fin_sum_skip_zero (#t: Type) {| acg: add_comm_group t |} (#n: pos{n > 1})
  (f: fin n -> t) (c: fin n) (g: fin (Prims.op_Subtraction n 1) -> t)
  (h_zero: squash (f c = (zero <: t)))
  (h_skip: (b: fin (Prims.op_Subtraction n 1)) -> Lemma (f (skip c b) = g b))
  (h_g_zero: squash (fin_sum g = (zero <: t)))
  : Lemma (fin_sum f = (zero <: t))
  = fin_sum_skip_reindex f c g h_zero h_skip;
    trans_for_calc t ();
    ()
#pop-options

(* Chain helper: given sum_pw = f2+f1, f2 = neg x, f1 = x, prove sum_pw = 0.
   All equality uses the same acg, avoiding TC diamond. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
private let sum_split_neg_cancel (#t: Type) {| acg: add_comm_group t |}
  (sum_pw: t) (sum_f2: t) (sum_f1: t) (x: t)
  (h_split: squash (sum_pw = sum_f2 + sum_f1))
  (h_f2: squash (sum_f2 = neg x))
  (h_f1: squash (sum_f1 = x))
  : Lemma (sum_pw = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    neg_x_plus_x #t #acg x;
    add_congruence sum_f2 sum_f1 (neg x) x;
    transitivity sum_pw (neg x + x) (zero <: t)
#pop-options

(* fin_sum of a function that is val_c at one index and zero elsewhere. *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
private let fin_sum_single (#t: Type) {| r: ring t |} (#n: pos)
  (f: fin n -> t) (c: fin n) (val_c: t)
  (h_c: squash (f c = val_c))
  (h_nc: (j: fin n) -> Lemma (requires (j <: nat) <> (c <: nat)) (ensures f j = (zero <: t)))
  : Lemma (fin_sum f = val_c)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let bridge (j: fin n) : Lemma (f j = pointwise_mul (fin_kronecker_delta c) (const val_c) j)
      = pointwise_mul_unfold #(fin n) #t #r (fin_kronecker_delta c) (const val_c) j;
        if (j <: nat) = (c <: nat) then begin
          one_mul_x #t #r val_c;
          transitivity (f j) val_c (one * val_c)
        end else begin
          h_nc j;
          zero_mul_x #t #r val_c;
          transitivity (f j) (zero <: t) (zero * val_c)
        end
    in
    fin_sum_congruence #t #(acg_of_r t #r) f (pointwise_mul (fin_kronecker_delta c) (const val_c)) bridge;
    fin_sum_kronecker #t #r #n c (const val_c)
#pop-options

(* The main theorem statement. *)
val det_zero_implies_null_vec (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n)
  : Lemma (requires det m = (zero <: t))
          (ensures  exists (v: fin n -> t) (k: fin n).
                      is_nonzero (v k) /\
                      (forall (i: fin n). vector_dot (row m i) v = (zero <: t)))

(* ================================================================== *)
(*  Case helpers for the main proof                                    *)
(* ================================================================== *)

(* Case adj≠0: column of adjugate is kernel vector. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
private let case_adj_nonzero (#t: Type) {| f: field t |} (#n: pos{n > 1})
  (m: square_matrix t n) (r j: fin n)
  : Lemma (requires det m = (zero <: t) /\ is_nonzero (adjugate m r j))
          (ensures  exists (v: fin n -> t) (k: fin n).
                      is_nonzero (v k) /\
                      (forall (i: fin n). vector_dot (row m i) v = (zero <: t)))
  = adj_nonzero_gives_kernel m r j;
    let v : (fin n -> t) = col (adjugate m) j in
    let dot_zero (i: fin n)
      : Lemma (vector_dot (row m i) v = (zero <: t))
      = mul_entry_is_dot m (adjugate m) i j;
        elim_equatable_laws t ();
        transitivity (vector_dot (row m i) v)
                     (matrix_mul m (adjugate m) i j)
                     (zero <: t)
    in
    Classical.forall_intro dot_zero
#pop-options

(* Case M=0: any basis vector works. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
private let case_m_zero (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n)
  : Lemma (requires forall (r c: fin n). m r c = (zero <: t))
          (ensures  exists (v: fin n -> t) (k: fin n).
                      is_nonzero (v k) /\
                      (forall (i: fin n). vector_dot (row m i) v = (zero <: t)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let _ : squash (not ((one <: t) `eq` (zero <: t))) =
      (id_of_f t #f).id_one_ne_zero in
    let v : (fin n -> t) = fun _ -> (one <: t) in
    let cr : commutative_ring t = cr_of_id t #(id_of_f t #f) in
    let dot_zero (i: fin n)
      : Lemma (vector_dot (row m i) v = (zero <: t))
      = let pw = pointwise_mul #(fin n) #t #cr.cr_r (row m i) v in
        let f_zero (k: fin n)
          : Lemma (pw k = (zero <: t))
          = pointwise_mul_unfold #(fin n) #t #cr.cr_r (row m i) v k;
            zero_mul_x #t #cr.cr_r (one <: t);
            mul_congruence #t #cr.cr_r (m i k) (one <: t) (zero <: t) (one <: t)
        in
        Classical.forall_intro f_zero;
        fin_sum_zero_ext #t #(acg_of_r t #cr.cr_r) #n pw f_zero;
        fin_sum_eq_pointwise #t #(acg_of_r t #cr.cr_r) pw (pointwise_mul (row m i) v);
        vector_dot_reveal #t #cr.cr_r #n (row m i) v
      in
    Classical.forall_intro dot_zero;
    assert (is_nonzero (v (0 <: fin n)));
    assert (forall (i: fin n). vector_dot (row m i) v = (zero <: t))
#pop-options

(* The main theorem body.
   Currently uses admits for: base case n=1 and inductive case (adj=0,M≠0).
   The adj≠0 case and M=0 case are fully proved above. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
let rec det_zero_implies_null_vec #t #f #n m =
  if n = 1 then begin
    (* Base case: det m = m 0 0 for 1×1, so m 0 0 = zero, use case_m_zero *)
    det_1x1 m;
    elim_equatable_laws t ();
    trans_for_calc t ();
    let all_zero (r: fin 1) (c: fin 1)
      : Lemma (m r c = (zero <: t))
      = () (* r=0, c=0 is the only case *)
    in
    Classical.forall_intro_2 all_zero;
    case_m_zero m
  end
  else begin
    (* n ≥ 2: case split via excluded middle + move_requires *)
    let adj_has_nonzero ()
      : Lemma (requires exists (r: fin n) (j: fin n). is_nonzero (adjugate m r j))
              (ensures  exists (v: fin n -> t) (k: fin n).
                          is_nonzero (v k) /\
                          (forall (i: fin n). vector_dot (row m i) v = (zero <: t)))
      = let helper (r: fin n) (j: fin n)
          : Lemma (requires is_nonzero (adjugate m r j))
                  (ensures  exists (v: fin n -> t) (k: fin n).
                              is_nonzero (v k) /\
                              (forall (i: fin n). vector_dot (row m i) v = (zero <: t)))
          = case_adj_nonzero m r j
        in
        let helper2 (r: fin n) (j: fin n)
          : Lemma (is_nonzero (adjugate m r j) ==>
                   (exists (v: fin n -> t) (k: fin n).
                      is_nonzero (v k) /\
                      (forall (i: fin n). vector_dot (row m i) v = (zero <: t))))
          = Classical.move_requires (helper r) j
        in
        Classical.forall_intro_2 helper2
    in
    let adj_all_zero ()
      : Lemma (requires ~(exists (r: fin n) (j: fin n). is_nonzero (adjugate m r j)))
              (ensures  exists (v: fin n -> t) (k: fin n).
                          is_nonzero (v k) /\
                          (forall (i: fin n). vector_dot (row m i) v = (zero <: t)))
      = (* Sub-case: M has a nonzero entry — inductive case *)
        let m_has_nonzero (r: fin n) (c: fin n)
          : Lemma (requires is_nonzero (m r c))
                  (ensures exists (v: fin n -> t) (k: fin n).
                             is_nonzero (v k) /\
                             (forall (i: fin n). vector_dot (row m i) v = (zero <: t)))
          = (* Step 1: column elimination preserves det *)
            elim_equatable_laws t ();
            trans_for_calc t ();
            let e = elim_col m r c in
            det_elim_col_eq m r c;
            (* det e = det m = zero *)
            (* Step 2: Laplace along column c → det(minor(E, r, c)) = 0 *)
            let minor_e : square_matrix t (Prims.op_Subtraction n 1) = minor e r c in
            (* e has column c all zeros except at (r,c) *)
            let elim_col_precond (i: fin n)
              : Lemma (requires (i <: nat) <> (r <: nat))
                      (ensures  e i c = (zero <: t))
              = elim_col_zero m r c i
            in
            Classical.forall_intro (Classical.move_requires elim_col_precond);
            elim_col_pivot m r c;
            det_zero_single_entry_col e r c;
            (* Step 3: IH gives w in kernel of minor *)
            det_zero_implies_null_vec #t #f #(Prims.op_Subtraction n 1) minor_e;
            (* Now: exists (w: fin(n-1)->t) (k0: fin(n-1)). is_nonzero(w k0) /\ ... *)
            (* Step 4: extend w to v in kernel of M *)
            let nm1 : pos = Prims.op_Subtraction n 1 in
            let vector_extend (w: fin nm1 -> t) (k0: fin nm1)
              : Lemma (requires is_nonzero (w k0) /\
                                (forall (i: fin nm1). vector_dot (row minor_e i) w = (zero <: t)))
                      (ensures  exists (v: fin n -> t) (k: fin n).
                                  is_nonzero (v k) /\
                                  (forall (i: fin n). vector_dot (row m i) v = (zero <: t)))
              = let rr : ring t = f.f_sf.sf_r in
                let f_x : (fin nm1 -> t) = (fun (b: fin nm1) -> m r (skip c b) * w b) in
                let x : t = fin_sum #t #(rr.r_add) #(Prims.op_Subtraction n 1) f_x in
                let mig : mul_is_group t = mig_of_sf t #f.f_sf in
                let inv_mrc : t = mig.inv (m r c) in
                let neg_inv : t = neg inv_mrc in
                let vc : t = neg_inv * x in
                let v (j: fin n) : t =
                  if (j <: nat) = (c <: nat) then vc else w (unskip c j)
                in
                let k : fin n = skip c k0 in
                assert (v k == w k0);
                elim_equatable_laws t ();
                trans_for_calc t ();
                (* --- Row r: vector_dot (row m r) v = zero --- *)
                let row_r_zero ()
                  : Lemma (vector_dot (row m r) v = (zero <: t))
                  = let pw_r : (fin n -> t) = pointwise_mul (row m r) v in
                    let f1 (j: fin n) : t = if (j <: nat) = (c <: nat) then zero else pw_r j in
                    let f2 (j: fin n) : t = if (j <: nat) = (c <: nat) then pw_r c else zero in
                    let split_cb (j: fin n) : Lemma (pw_r j = f2 j + f1 j)
                      = if (j <: nat) = (c <: nat) then
                          x_plus_zero #t #(rr.r_add) (pw_r j)
                        else
                          zero_plus_x #t #(rr.r_add) (pw_r j)
                    in
                    fin_sum_add_ext #t #(rr.r_add) #n f2 f1 (pointwise_mul (row m r) v) split_cb;
                    (* fin_sum f1 = x via skip_reindex *)
                    let f1_skip (b: fin nm1) : Lemma (f1 (skip c b) = f_x b)
                      = skip_avoids c b;
                        unskip_skip c b;
                        H.leibniz_to_eq (v (skip c b)) (w b);
                        H.leibniz_to_eq (pw_r (skip c b)) (m r (skip c b) * w b);
                        H.leibniz_to_eq (f1 (skip c b)) (pw_r (skip c b))
                    in
                    fin_sum_skip_reindex #t #(rr.r_add) #n f1 c f_x () f1_skip;
                    (* Bridge: skip_reindex gives fin_sum f1 = fin_sum f_x = x *)
                    derive_eq_via_mid #t #(rr.r_add)
                      (fin_sum #t #(rr.r_add) #n f1)
                      (fin_sum #t #(rr.r_add) #(Prims.op_Subtraction n 1) f_x) x () ();
                    (* Now have: fin_sum f1 = x *)
                    (* Show m r c * vc = neg x *)
                    mul_associativity #t #rr (m r c) neg_inv x;
                    neg_mul_r #t #rr (m r c) inv_mrc;
                    mig.inversion_lemma (m r c);
                    mul_congruence #t #rr (m r c * neg_inv) x
                                          (neg (m r c * inv_mrc)) x;
                    neg_congruence #t #(rr.r_add) (m r c * inv_mrc) one;
                    mul_congruence #t #rr (neg (m r c * inv_mrc)) x (neg one) x;
                    neg_mul_l #t #rr one x;
                    one_mul_x #t #rr x;
                    neg_congruence #t #(rr.r_add) (one * x) x;
                    transitivity ((m r c * neg_inv) * x)
                                 (neg (m r c * inv_mrc) * x) (neg x);
                    symmetry ((m r c * neg_inv) * x)
                             (m r c * (neg_inv * x));
                    transitivity (m r c * vc)
                                 (m r c * (neg_inv * x))
                                 (neg x);
                    transitivity (m r c * vc)
                                 ((m r c * neg_inv) * x) (neg x);
                    (* Now: m r c * vc = neg x *)
                    let f2_nc (j: fin n)
                      : Lemma (requires (j <: nat) <> (c <: nat))
                              (ensures f2 j = (zero <: t)) = ()
                    in
                    fin_sum_single #t #rr #n f2 c (neg x) () f2_nc;
                    (* fin_sum f2 = neg x, fin_sum f1 = x *)
                    add_congruence #t #(rr.r_add)
                      (fin_sum #t #(rr.r_add) #n f2) (fin_sum #t #(rr.r_add) #n f1)
                      (neg x) x;
                    neg_x_plus_x #t #(rr.r_add) x;
                    transitivity (fin_sum #t #(rr.r_add) #n f2 + fin_sum #t #(rr.r_add) #n f1)
                                 (neg x + x) (zero <: t);
                    transitivity (fin_sum #t #(rr.r_add) #n (pointwise_mul (row m r) v))
                                 (fin_sum #t #(rr.r_add) #n f2 + fin_sum #t #(rr.r_add) #n f1)
                                 (zero <: t);
                    vector_dot_reveal #t #rr #n (row m r) v
                in
                row_r_zero ();
                (* --- Row i≠r: vector_dot (row m i) v = zero --- *)
                let dot_zero (i: fin n)
                  : Lemma (vector_dot (row m i) v = (zero <: t))
                  = if (i <: nat) = (r <: nat) then
                      row_r_zero ()
                    else begin
                      (* Row i≠r: uses elim_col decomposition + IH *)
                      let ih_row : fin nm1 = unskip r i in
                      let coeff_i : t = m i c * inv_mrc in
                      (* Named combinator forms (NO local lambdas): *)
                      let f1 : (fin n -> t) = pointwise_mul (row e i) v in
                      let f2 : (fin n -> t) = pointwise_mul (const coeff_i) (pointwise_mul (row m r) v) in
                      (* Step 1: pointwise decomposition
                         (pw (row m i) v) j = f1 j + f2 j *)
                      let pw_split (j: fin n)
                        : Lemma ((pointwise_mul (row m i) v) j = f1 j + f2 j)
                        = pointwise_mul_unfold #(fin n) #t #rr (row m i) v j;
                          pointwise_mul_unfold #(fin n) #t #rr (row e i) v j;
                          pointwise_add_unfold #(fin n) #t #(rr.r_add) f1 f2 j;
                          pointwise_mul_unfold #(fin n) #t #rr (const coeff_i) (pointwise_mul (row m r) v) j;
                          pointwise_mul_unfold #(fin n) #t #rr (row m r) v j;
                          (* e i j == m i j + neg (coeff_i * m r j) definitionally *)
                          H.leibniz_to_eq (e i j) (m i j + neg (coeff_i * m r j));
                          (* (a + b)*c = a*c + b*c *)
                          right_distributivity #t #rr (v j) (m i j) (neg (coeff_i * m r j));
                          (* neg(a)*b = neg(a*b) *)
                          neg_mul_l #t #rr (coeff_i * m r j) (v j);
                          (* (coeff_i * m r j) * v j = coeff_i * (m r j * v j) *)
                          mul_associativity #t #rr coeff_i (m r j) (v j);
                          neg_congruence #t #(rr.r_add) ((coeff_i * m r j) * v j) (coeff_i * (m r j * v j));
                          transitivity (neg (coeff_i * m r j) * v j)
                                       (neg ((coeff_i * m r j) * v j))
                                       (neg (coeff_i * (m r j * v j)));
                          (* chain: e i j * v j = m i j * v j + neg(coeff_i*(m r j * v j)) *)
                          add_congruence #t #(rr.r_add) (m i j * v j) (neg (coeff_i * m r j) * v j)
                                         (m i j * v j) (neg (coeff_i * (m r j * v j)));
                          transitivity ((m i j + neg (coeff_i * m r j)) * v j)
                                       (m i j * v j + neg (coeff_i * m r j) * v j)
                                       (m i j * v j + neg (coeff_i * (m r j * v j)));
                          mul_congruence #t #rr (e i j) (v j) (m i j + neg (coeff_i * m r j)) (v j);
                          transitivity (e i j * v j)
                                       ((m i j + neg (coeff_i * m r j)) * v j)
                                       (m i j * v j + neg (coeff_i * (m r j * v j)));
                          (* sub_add_cancel: (a + neg b) + b = a *)
                          sub_add_cancel #t #(rr.r_add) (m i j * v j) (coeff_i * (m r j * v j));
                          add_congruence #t #(rr.r_add) (e i j * v j) (coeff_i * (m r j * v j))
                                         (m i j * v j + neg (coeff_i * (m r j * v j))) (coeff_i * (m r j * v j));
                          transitivity (e i j * v j + coeff_i * (m r j * v j))
                                       ((m i j * v j + neg (coeff_i * (m r j * v j))) + coeff_i * (m r j * v j))
                                       (m i j * v j);
                          (* So m i j * v j = f1 j + f2 j *)
                          H.leibniz_to_eq (f1 j) (e i j * v j);
                          H.leibniz_to_eq (f2 j) (coeff_i * (m r j * v j));
                          H.leibniz_to_eq ((pointwise_mul (row m i) v) j) (m i j * v j);
                          transitivity ((pointwise_mul (row m i) v) j) (m i j * v j) (f1 j + f2 j)
                      in
                      (* Step 2: fin_sum (pw (row m i) v) = fin_sum f1 + fin_sum f2 *)
                      fin_sum_add_ext #t #(rr.r_add) #n f1 f2 (pointwise_mul (row m i) v) pw_split;
                      (* Step 3: fin_sum f1 = 0 via skip_reindex + IH *)
                      let f1_at_c ()
                        : Lemma (f1 c = (zero <: t))
                        = pointwise_mul_unfold #(fin n) #t #rr (row e i) v c;
                          H.leibniz_to_eq (f1 c) (e i c * v c);
                          elim_col_zero m r c i;
                          zero_mul_x #t #rr (v c);
                          mul_congruence #t #rr (e i c) (v c) (zero <: t) (v c);
                          transitivity (f1 c) ((zero <: t) * v c) (zero <: t)
                      in
                      f1_at_c ();
                      let f1_skip (b: fin nm1)
                        : Lemma (f1 (skip c b) = (pointwise_mul #(fin (Prims.op_Subtraction n 1)) #t #rr (row minor_e ih_row) w) b)
                        = pointwise_mul_unfold #(fin n) #t #rr (row e i) v (skip c b);
                          H.leibniz_to_eq (f1 (skip c b)) (e i (skip c b) * v (skip c b));
                          pointwise_mul_unfold #(fin (Prims.op_Subtraction n 1)) #t #rr (row minor_e ih_row) w b;
                          skip_unskip r i;
                          skip_unskip c (skip c b);
                          unskip_skip c b;
                          skip_avoids c b;
                          H.leibniz_to_eq (v (skip c b)) (w (unskip c (skip c b)));
                          H.leibniz_to_eq (w (unskip c (skip c b))) (w b);
                          H.leibniz_to_eq (e i (skip c b)) (minor_e ih_row b);
                          mul_congruence #t #rr (e i (skip c b)) (v (skip c b))
                                                (minor_e ih_row b) (w b);
                          transitivity (f1 (skip c b)) (e i (skip c b) * v (skip c b))
                                       (minor_e ih_row b * w b);
                          transitivity (f1 (skip c b)) (minor_e ih_row b * w b) ((pointwise_mul #(fin (Prims.op_Subtraction n 1)) #t #rr (row minor_e ih_row) w) b)
                      in
                      vector_dot_reveal #t #rr #(Prims.op_Subtraction n 1) (row minor_e ih_row) w;
                      assert (vector_dot #t #rr #(Prims.op_Subtraction n 1) (row minor_e ih_row) w == fin_sum #t #(rr.r_add) #(Prims.op_Subtraction n 1) (pointwise_mul #(fin (Prims.op_Subtraction n 1)) #t #rr (row minor_e ih_row) w));
                      assert (fin_sum #t #(rr.r_add) #(Prims.op_Subtraction n 1) (pointwise_mul #(fin (Prims.op_Subtraction n 1)) #t #rr (row minor_e ih_row) w) = (zero <: t));
                      fin_sum_skip_zero #t #(rr.r_add) #n f1 c (pointwise_mul #(fin (Prims.op_Subtraction n 1)) #t #rr (row minor_e ih_row) w) () f1_skip ();
                      (* fin_sum f1 = 0 *)
                      (* Step 4: fin_sum f2 = 0 via fin_sum_mul_left + row_r_zero *)
                      fin_sum_mul_left #t #rr #n coeff_i (pointwise_mul (row m r) v);
                      (* coeff_i * fin_sum (pw (row m r) v) = fin_sum f2 *)
                      let f2_bridge (j: fin n)
                        : Lemma (f2 j = (pointwise_mul (const coeff_i) (pointwise_mul (row m r) v)) j)
                        = reflexivity (f2 j)
                      in
                      fin_sum_congruence #t #(rr.r_add) #n f2
                        (pointwise_mul (const coeff_i) (pointwise_mul (row m r) v)) f2_bridge;
                      symmetry (coeff_i * fin_sum #t #(rr.r_add) #n (pointwise_mul (row m r) v))
                               (fin_sum #t #(rr.r_add) #n (pointwise_mul (const coeff_i) (pointwise_mul (row m r) v)));
                      derive_eq_via_mid #t #(rr.r_add)
                        (fin_sum #t #(rr.r_add) #n f2)
                        (fin_sum #t #(rr.r_add) #n (pointwise_mul (const coeff_i) (pointwise_mul (row m r) v)))
                        (coeff_i * fin_sum #t #(rr.r_add) #n (pointwise_mul (row m r) v))
                        () ();
                      (* fin_sum f2 = coeff_i * fin_sum (pw (row m r) v) *)
                      row_r_zero ();
                      vector_dot_reveal #t #rr #n (row m r) v;
                      assert (vector_dot #t #rr #n (row m r) v == fin_sum #t #(rr.r_add) #n (pointwise_mul #(fin n) #t #rr (row m r) v));
                      mul_congruence #t #rr coeff_i
                        (fin_sum #t #(rr.r_add) #n (pointwise_mul (row m r) v))
                        coeff_i (zero <: t);
                      x_mul_zero #t #rr coeff_i;
                      transitivity (coeff_i * fin_sum #t #(rr.r_add) #n (pointwise_mul (row m r) v))
                                   (coeff_i * (zero <: t)) (zero <: t);
                      transitivity (fin_sum #t #(rr.r_add) #n f2)
                                   (coeff_i * fin_sum #t #(rr.r_add) #n (pointwise_mul (row m r) v))
                                   (zero <: t);
                      (* fin_sum f2 = 0 *)
                      (* Step 5: fin_sum f1 + fin_sum f2 = 0 + 0 = 0 *)
                      add_congruence #t #(rr.r_add)
                        (fin_sum #t #(rr.r_add) #n f1) (fin_sum #t #(rr.r_add) #n f2)
                        (zero <: t) (zero <: t);
                      zero_plus_x #t #(rr.r_add) (zero <: t);
                      transitivity (fin_sum #t #(rr.r_add) #n f1 + fin_sum #t #(rr.r_add) #n f2)
                                   ((zero <: t) + (zero <: t)) (zero <: t);
                      (* Step 6: chain to vector_dot *)
                      symmetry (fin_sum #t #(rr.r_add) #n (pointwise_mul (row m i) v))
                               (fin_sum #t #(rr.r_add) #n f1 + fin_sum #t #(rr.r_add) #n f2);
                      transitivity (fin_sum #t #(rr.r_add) #n (pointwise_mul (row m i) v))
                                   (fin_sum #t #(rr.r_add) #n f1 + fin_sum #t #(rr.r_add) #n f2)
                                   (zero <: t);
                      vector_dot_reveal #t #rr #n (row m i) v
                    end
                in
                Classical.forall_intro dot_zero
            in
            Classical.forall_intro_2 (Classical.move_requires_2 vector_extend)
        in
        let m_has_nonzero2 (r: fin n) (c: fin n)
          : Lemma (is_nonzero (m r c) ==>
                   (exists (v: fin n -> t) (k: fin n).
                      is_nonzero (v k) /\
                      (forall (i: fin n). vector_dot (row m i) v = (zero <: t))))
          = Classical.move_requires (m_has_nonzero r) c
        in
        Classical.forall_intro_2 m_has_nonzero2;
        (* Now SMT knows: forall r c. is_nonzero (m r c) ==> goal *)
        (* Case: all entries zero *)
        Classical.excluded_middle
          (exists (r: fin n) (c: fin n). is_nonzero (m r c));
        Classical.move_requires case_m_zero m
    in
    Classical.excluded_middle
      (exists (r: fin n) (j: fin n). is_nonzero (adjugate m r j));
    Classical.move_requires adj_has_nonzero ();
    Classical.move_requires adj_all_zero ()
  end
#pop-options
