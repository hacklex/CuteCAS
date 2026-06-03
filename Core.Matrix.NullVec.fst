module Core.Matrix.NullVec

(*
   Goal: prove `null_vec_implies_det_zero`:
   If Mv = 0 (entrywise) and v(k) ≠ 0 for some k, then det(M) = 0.

   Strategy (using det_mul + det_zero_column):
   1. Define elimination matrix E:
      E[i,j] = δ(i,j) for j ≠ k
      E[i,k] = v(i) * inv(v(k))  (column k = v/v(k))
   2. Show (M·E) has column k = 0 (from Mv = 0)
   3. det(M·E) = 0  (det_zero_column)
   4. det(M·E) = det(M) · det(E)  (det_mul)
   5. det(E) = one  (prove via iterative col_add from I)
   6. det(M) · one = 0  ⟹  det(M) = 0
*)

module TC = FStar.Tactics.Typeclasses
module L  = FStar.List.Tot

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Helpers
open Core.Algebra.Combinators
open Core.Permutation
open Core.Matrix
open Core.Matrix.Determinant
open Core.Matrix.Determinant.Mul
open Core.Vector
open Core.FinSum

(* ================================================================ *)
(*  Elimination matrix                                               *)
(* ================================================================ *)

(* Elimination matrix E: column k = v/v(k), other columns = identity *)
let elim_matrix (#t:Type) {| f: skewfield t |} (#n: pos) 
                (v: fin n -> t) (k: fin n{is_nonzero (v k)}) (i j: fin n) =      
      if j=k then mul (v i) (inv (v k))
      else if i=j then one else zero

(* ================================================================ *)
(*  M · E has zero column k when Mv = 0                             *)
(* ================================================================ *)

(* The null-vector hypothesis: dot product of row i with v is zero *)
let null_vec_hyp (#t:Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (v: fin n -> t) (i: fin n) : prop
  = vector_dot (row m i) v = zero

let me_col_k_is_zero (#t:Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (v: fin n -> t) (k i: fin n)
  : Lemma (requires is_nonzero (v k) /\ vector_dot (row m i) v = zero)
          (ensures matrix_mul m (elim_matrix v k) i k = zero)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    (* Bridge: unfold vector_dot to fin_sum form for the proof body *)
    let e = elim_matrix v k in
    let mi_v = pointwise_mul (row m i) v in    
    let inv_vk = inv (v k) in
    let mil_elk = pointwise_mul (row m i) (col e k) in       
    vector_dot_reveal (row m i) v;
    vector_dot_reveal (row m i) (col e k);
    fin_sum_eq_pointwise mil_elk (pointwise_mul (row m i) (col e k));
    (* pointwise congruence: m i l * e l k = pointwise_mul (...) (const inv_vk) l *)
    fin_sum_congruence mil_elk (pointwise_mul mi_v (const inv_vk)) 
                               (fun l -> mul_associativity (m i l) (v l) inv_vk);
    (* gives: fin_sum (fun l -> m i l * e l k) = fin_sum (pointwise_mul (...) (const inv_vk)) *)
    fin_sum_mul_right mi_v inv_vk;
    (* gives: fin_sum (fun l -> m i l * v l) * inv_vk = fin_sum (pointwise_mul (...) (const inv_vk)) *)    
    (* gives: fin_sum (fun l -> m i l * e l k) = fin_sum (fun l -> m i l * v l) * inv_vk *)
    zero_mul_x inv_vk;
    fin_sum_eq_pointwise mi_v (pointwise_mul (row m i) v);
    mul_congruence (fin_sum mi_v) inv_vk zero inv_vk

(* ================================================================ *)
(*  det(E) = 1                                                       *)
(*  Proof: E is obtained from I by col_add operations, each          *)
(*  preserving det. det(I) = 1 (det_identity).                       *)
(* ================================================================ *)

(* col_add_step: matrix obtained from I by adding (v(j)/v(k)) * col_j to col_k
   for all j < step, j ≠ k *)
let rec col_add_steps (#t:Type) {| f: field t |} (#n: pos)
  (v: fin n -> t) (k: fin n) (step: nat{step <= n})
  : Pure (square_matrix t n)
         (requires is_nonzero (v k))
         (ensures fun _ -> True)
         (decreases step)
  = if step = 0 then id_matrix
    else
      let prev = col_add_steps v k (step - 1) in
      let j : nat = step - 1 in
      if j = k then prev
      else col_add prev k j (mul (v j) (inv (v k)))

(* det of col_add_steps = 1 at every step *)
let rec det_col_add_steps_eq_one (#t:Type) {| f: field t |} (#n: pos)
  (v: fin n -> t) (k: fin n) (step: nat{step <= n})
  : Lemma (requires is_nonzero (v k))
          (ensures det (col_add_steps v k step) = one)
          (decreases step)
  = trans_for_calc t ();
    if step = 0 then
      det_identity #t n
    else begin
      det_col_add_steps_eq_one v k (step - 1);
      let prev = col_add_steps v k (step - 1) in
      let j : nat = step - 1 in
      if j = k then reflexivity (det prev)
      else det_col_add prev k j (mul (v j) (inv (v k)))
    end


(* Helper: explicitly state what col_add computes at a given index *)
private let col_add_at (#t:Type) {| r: ring t |} (#n: pos)
  (m: square_matrix t n) (target src: fin n) (c: t) (a b: fin n)
  : Lemma (col_add m target src c a b ==
           (if b = target then m a b + m a src * c else m a b)) = ()


(* Propositional-equality version of col_add_steps characterization.
   We use = (equatable eq) because the j=k column entries require
   ring axioms (zero*c=zero, one*c=c) that only give propositional equality. *)

let rec col_add_steps_eq_elim (#t:Type) {| f: field t |} (#n: pos)
  (v: fin n -> t) (k: fin n) (step: nat{step <= n})
  (i j: fin n)
  : Lemma (requires is_nonzero (v k))
          (ensures col_add_steps v k step i j =
                   (if j = k then
                      (if i = k then one
                       else if i < step then mul (v i) (inv (v k))
                       else zero)
                    else (if i = j then one else zero)))
          (decreases step)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let one, zero = one #t, zero #t in
    if step = 0 then
      reflexivity (col_add_steps v k 0 i j)
    else begin
      let s : nat = step - 1 in
      col_add_steps_eq_elim v k (step - 1) i j;
      if s = k then begin
        (* col_add_steps v k step = prev (skip s=k). Postcondition at step 
           matches step-1 since the only difference is i<step vs i<step-1,
           and the gap is i=s=k which falls into the "i=k → one" branch. *)
        reflexivity (col_add_steps v k step i j)
      end
      else begin
        col_add_steps_eq_elim v k (step - 1) i j;
        col_add_steps_eq_elim v k (step - 1) i s;
        let prev = col_add_steps v k (step - 1) in
        let c : t = mul (v s) (inv (v k)) in
        col_add_at prev k s c i j;
        if j <> k then ()
        else begin
          (* j=k: col_add gives prev[i,k] + prev[i,s] * c *)
          let pik = prev i k in
          let pis = prev i s in
          if i = k then begin
            (* pik = one, pis = zero → one + zero*c = one *)
            mul_congruence pis c zero c;
            zero_mul_x c;
            add_congruence pik (pis * c) one zero;
            x_plus_zero one;
            transitivity (pik + pis * c) (one + zero) one
          end
          else if i = s then begin
            (* pik = zero, pis = one → zero + one*c = c *)
            mul_congruence pis c one c;
            one_mul_x c;
            add_congruence pik (pis * c) zero c;
            zero_plus_x c;
            transitivity (pik + pis * c) (zero + c) c
          end
          else if i < s then begin
            (* pik = v(i)*inv(vk), pis = zero → v(i)*inv(vk) + zero*c = v(i)*inv(vk) *)
            let vi_inv = mul (v i) (inv (v k)) in
            mul_congruence pis c zero c;
            zero_mul_x c;
            add_congruence pik (pis * c) vi_inv zero;
            x_plus_zero vi_inv;
            transitivity (pik + pis * c) (vi_inv + zero) vi_inv
          end
          else begin
            (* pik = zero, pis = zero → zero + zero*c = zero *)
            assert (pis = zero);
            assert (pik = zero);
            mul_congruence pis c zero c;
            zero_mul_x c;
            add_congruence pik (pis * c) zero zero;
            x_plus_zero zero;
            transitivity (pik + pis * c) (zero + zero) zero
          end
        end
      end
    end

(* Bridge: col_add_steps n and elim_matrix are propositionally equal *)
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let col_add_steps_n_eq_elim (#t:Type) {| f: field t |} (#n: nat{n > 0})
  (v: fin n -> t) (k: fin n) (i j: fin n)
  : Lemma (requires is_nonzero (v k))
          (ensures col_add_steps v k n i j = elim_matrix v k i j)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    col_add_steps_eq_elim v k n i j;
    let inv_vk = inv (v k) in
    if (j <: nat) = (k <: nat) then begin
      if (i <: nat) = (k <: nat) then begin
        (* col_add_steps gives: one
           elim_matrix gives: v(k) * inv(v(k))
           Bridge: inversion_lemma gives mul (v k) (inv (v k)) = one *)
        f.f_sf.sf_mig.inversion_lemma (v k);
        symmetry (mul (v k) inv_vk) (one <: t)
      end
      else begin
        (* Both give v(i) * inv(v(k)), since i < n always for i: fin n *)
        reflexivity (mul (v i) inv_vk)
      end
    end
    else begin
      (* Both give identity: if i=j then one else zero *)
      if (i <: nat) = (j <: nat) then reflexivity (one <: t)
      else reflexivity (zero <: t)
    end
#pop-options

(* ================================================================ *)
(*  Main theorem                                                     *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let null_vec_implies_det_zero (#t:Type) {| f: field t |} (#n: nat{n > 0})
  (m: square_matrix t n) (v: fin n -> t) (k: fin n)
  : Lemma (requires is_nonzero (v k) /\
                    (forall (i: fin n). null_vec_hyp m v i))
          (ensures det m = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let e = elim_matrix v k in
    let me = matrix_mul m e in
    (* Step 1: me has zero column k *)
    let col_k_zero (i: fin n) : Lemma (me i k = (zero <: t))
      = me_col_k_is_zero m v k i
    in
    Classical.forall_intro col_k_zero;
    det_zero_column me k;
    (* det(me) = zero *)
    (* Step 2: det(me) = det(m) * det(e) *)
    det_mul m e;
    (* det(matrix_mul m e) = det m * det e *)
    (* Step 3: det(e) = one *)
    let e_steps = col_add_steps v k n in
    det_col_add_steps_eq_one v k n;
    (* det e_steps = one *)
    let pw (i j: fin n) : Lemma (e_steps i j = e i j)
      = col_add_steps_n_eq_elim v k i j
    in
    Classical.forall_intro_2 pw;
    det_pointwise_eq e_steps e;
    (* det e_steps = det e *)
    (* det e = one *)
    (* Step 4: det(m) * one = det(m) = det(me) = zero *)
    x_mul_one (det m);
    (* det m * one = det m *)
    mul_congruence (det m) (det e) (det m) (one <: t);
    (* det m * det e = det m * one *)
    (* det m * det e = det m *)
    (* det m * det e = det(me) *)
    (* det m = det(me) *)
    transitivity (det m) (det (matrix_mul m e)) (zero <: t)
    (* det m = zero *)
#pop-options