module Core.Matrix.Resultant

(*
   Resultant of two univariate polynomials.

   Given polynomials p, q over a commutative ring with formal degree
   bounds m_deg, n_deg, the resultant is the determinant of the
   Sylvester matrix:

       res(p, q) := det (sylvester_matrix m_deg n_deg p q)

   This module establishes:
     - the definition,
     - degenerate-row vanishing lemmas (zero polynomial or
       too-small polynomial input produces a zero row in the matrix
       hence a zero resultant).

   Deeper properties (sign on swap, multiplicativity, resultant = 0
   iff a common factor exists over a field) are downstream and
   depend on polynomial GCD / Bézout machinery still under
   construction.
*)

module TC = FStar.Tactics.Typeclasses
module L = FStar.List.Tot

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Permutation
open Core.Matrix
open Core.Matrix.Sylvester
open Core.Matrix.Determinant

(* ------------------------------------------------------------------ *)
(*  Definition                                                        *)
(* ------------------------------------------------------------------ *)

let resultant
    (#t: Type) {| cr: commutative_ring t |}
    (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t)
  : t
  = det (sylvester_matrix m_deg n_deg p q)

let resultant_unfold
    (#t: Type) {| cr: commutative_ring t |}
    (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t)
  : Lemma (resultant m_deg n_deg p q
        == det (sylvester_matrix m_deg n_deg p q))
  = ()

(* ------------------------------------------------------------------ *)
(*  Row 0 of the Sylvester matrix is the p-row at shift 0.            *)
(*  When p is the zero polynomial (all coefficients zero up to        *)
(*  index m_deg), the entire row is zero.                             *)
(* ------------------------------------------------------------------ *)

#push-options "--z3rlimit 40 --ifuel 2 --fuel 2"

(* Helper: in a polynomial with `p == []` (i.e. p == [] under the
   trimmed-polynomial invariant), every list index is zero. *)
let all_zero_index_lemma
    (#t: Type) {| cr: commutative_ring t |}
    (p: polynomial t) (i: nat)
  : Lemma (requires p == [] /\ i < L.length p)
          (ensures  L.index p i = (zero <: t))
  = ()

let sylvester_first_row_all_zero_when_p_zero
    (#t: Type) {| cr: commutative_ring t |}
    (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t)
  : Lemma (requires n_deg > 0 /\
                    L.length p <= Prims.op_Addition m_deg 1 /\
                    p == [])
          (ensures  (let s = sylvester_matrix m_deg n_deg p q in
                     let k : fin (nat_add m_deg n_deg) = (0 <: nat) in
                     forall (j: fin (nat_add m_deg n_deg)). s k j = (zero <: t)))
  = let s = sylvester_matrix m_deg n_deg p q in
    let k : fin (nat_add m_deg n_deg) = (0 <: nat) in
    let row_is_zero (j: fin (nat_add m_deg n_deg))
      : Lemma (s k j = (zero <: t))
      = let k_nat : nat = k in
        let j_nat : nat = j in
        assert (k_nat < n_deg);
        let idx_int : int = m_deg + k_nat - j_nat in
        if idx_int < 0 then begin
          assert (s k j == (zero <: t));
          reflexivity (zero <: t)
        end else begin
          let idx : nat = idx_int in
          if idx < L.length p then begin
            all_zero_index_lemma p idx;
            assert (L.index p idx = (zero <: t));
            assert (coeff p idx = (zero <: t));
            assert (s k j = (zero <: t))
          end else begin
            assert (coeff p idx == (zero <: t));
            reflexivity (zero <: t);
            assert (s k j = (zero <: t))
          end
        end
    in
    Classical.forall_intro row_is_zero

#pop-options

(* ------------------------------------------------------------------ *)
(*  Resultant vanishing                                               *)
(* ------------------------------------------------------------------ *)

let resultant_zero_when_p_all_zero
    (#t: Type) {| cr: commutative_ring t |}
    (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t)
  : Lemma (requires n_deg > 0 /\
                    L.length p <= Prims.op_Addition m_deg 1 /\
                    p == [])
          (ensures  resultant m_deg n_deg p q = (zero <: t))
  = let s = sylvester_matrix m_deg n_deg p q in
    let k : fin (nat_add m_deg n_deg) = (0 <: nat) in
    sylvester_first_row_all_zero_when_p_zero m_deg n_deg p q;
    det_zero_row s k

(* ------------------------------------------------------------------ *)
(*  Skew-symmetry: res(q, p) = (-1)^(m*n) * res(p, q)                *)
(* ------------------------------------------------------------------ *)

module H = Core.Algebra.Helpers

(* The Sylvester matrix of (q,p) with swapped degree bounds equals
   a row-permutation of the Sylvester matrix of (p,q). *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let sylvester_swap_entry
    (#t: Type) {| cr: commutative_ring t |}
    (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t)
    (i j: fin (nat_add m_deg n_deg))
  : Lemma (sylvester_matrix n_deg m_deg q p i j
         = sylvester_matrix m_deg n_deg p q
             ((block_swap_perm m_deg n_deg).fwd i) j)
  = let sigma = block_swap_perm m_deg n_deg in
    let i_nat : nat = i in
    let j_nat : nat = j in
    H.elim_equatable_laws t ();
    if i_nat < m_deg then begin
      block_swap_perm_fwd_in_first_block m_deg n_deg i;
      reflexivity (sylvester_matrix n_deg m_deg q p i j)
    end else begin
      block_swap_perm_fwd_in_second_block m_deg n_deg i;
      reflexivity (sylvester_matrix n_deg m_deg q p i j)
    end
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let resultant_skew_symmetry
    (#t: Type) {| cr: commutative_ring t |}
    (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t)
  : Lemma (resultant n_deg m_deg q p =
           (if (m_deg * n_deg) % 2 = 0
            then resultant m_deg n_deg p q
            else -(resultant m_deg n_deg p q)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let s_pq = sylvester_matrix m_deg n_deg p q in
    let s_qp = sylvester_matrix n_deg m_deg q p in
    let sigma = block_swap_perm m_deg n_deg in
    let pw (i j: fin (nat_add m_deg n_deg))
      : Lemma (s_qp i j = permute_rows s_pq sigma i j)
      = sylvester_swap_entry m_deg n_deg p q i j;
        reflexivity (s_qp i j)
    in
    Classical.forall_intro_2 pw;
    det_pointwise_eq #t #cr #(nat_add m_deg n_deg) s_qp (permute_rows s_pq sigma);
    det_permute_rows #t #cr #(nat_add m_deg n_deg) s_pq sigma;
    parity_block_swap m_deg n_deg;
    transitivity (resultant n_deg m_deg q p)
                 (det (permute_rows s_pq sigma))
                 (if parity sigma then det s_pq else -(det s_pq))
#pop-options
