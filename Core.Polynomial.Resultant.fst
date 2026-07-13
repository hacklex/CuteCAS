module Core.Polynomial.Resultant

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

(* aliases for the folded-in ResultantConverse body *)
module KD  = Core.Matrix.Determinant
module DET = Core.Matrix.Determinant
module SYL = Core.Polynomial.Sylvester
module GC  = Core.Polynomial.GCD
module IR  = Core.Polynomial.Irreducible
module SF  = Core.Polynomial.SquareFree
module UN  = Core.Polynomial.Unique

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Helpers
open Core.Algebra.Divisibility
open Core.Algebra.Combinators
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.Coeff
open Core.Polynomial.GCD
open Core.Polynomial.SquareFree
open Core.Permutation
open Core.Matrix
open Core.Polynomial.Sylvester
open Core.Matrix.Determinant
open Core.Vector
open Core.FinSum
open Core.Polynomial.Eval
open Core.Polynomial.Roots
open Core.Tactics.CanonRing

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

(* Opaque wrapper for the "row 0 of the Sylvester matrix is all zero"
   property, keeping the raw quantifier out of business-lemma specs. *)
[@@"opaque_to_smt"]
let sylvester_row0_all_zero
    (#t: Type) {| cr: commutative_ring t |}
    (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t) : prop
  = (let s = sylvester_matrix m_deg n_deg p q in
     let k : fin (nat_add m_deg n_deg) = (0 <: nat) in
     forall (j: fin (nat_add m_deg n_deg)). s k j = (zero <: t))

let sylvester_row0_all_zero_elim
    (#t: Type) {| cr: commutative_ring t |}
    (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t)
  : Lemma (requires sylvester_row0_all_zero m_deg n_deg p q)
          (ensures  (let s = sylvester_matrix m_deg n_deg p q in
                     let k : fin (nat_add m_deg n_deg) = (0 <: nat) in
                     forall (j: fin (nat_add m_deg n_deg)). s k j = (zero <: t)))
  = reveal_opaque (`%sylvester_row0_all_zero) (sylvester_row0_all_zero m_deg n_deg p q)

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
                    L.length p <= (m_deg ++ 1) /\
                    p == [])
          (ensures  sylvester_row0_all_zero m_deg n_deg p q)
  = reveal_opaque (`%sylvester_row0_all_zero) (sylvester_row0_all_zero m_deg n_deg p q);
    let s = sylvester_matrix m_deg n_deg p q in
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
                    L.length p <= (m_deg ++ 1) /\
                    p == [])
          (ensures  resultant m_deg n_deg p q = (zero <: t))
  = let s = sylvester_matrix m_deg n_deg p q in
    let k : fin (nat_add m_deg n_deg) = (0 <: nat) in
    sylvester_first_row_all_zero_when_p_zero m_deg n_deg p q;
    sylvester_row0_all_zero_elim m_deg n_deg p q;
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
    det_pointwise_eq s_qp (permute_rows s_pq sigma);
    det_permute_rows s_pq sigma;
    parity_block_swap m_deg n_deg;
    transitivity (resultant n_deg m_deg q p)
                 (det (permute_rows s_pq sigma))
                 (if parity sigma then det s_pq else -(det s_pq))
#pop-options

(* ================================================================== *)
(*  L4: resultant vanishes iff common factor exists (forward dir)      *)
(* ================================================================== *)

(* Helper: b*p poly_eq a*q when p = g*a, q = g*b *)
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let bp_eq_aq (#t:Type) {| f: field t |}
  (p q g: polynomial t)
  (hgp: divides g p)
  (hgq: divides g q)
  (hdeg: squash (deg g >= 0))
  : Lemma (ensures ((poly_div q g * p) = (poly_div p g * q)))
  = let a = poly_div p g in
    let b = poly_div q g in
    poly_div_correct p g;
    poly_div_correct q g;
    symmetry (g * a) p;
    reflexivity b;
    mul_congruence b p b (g * a);
    mul_associativity b g a;
    symmetry ((b * g) * a) (b * (g * a));
    mul_commutativity_cr b g;
    reflexivity a;
    mul_congruence (b * g) a (g * b) a;
    mul_congruence (g * b) a q a;
    mul_commutativity_cr q a;
    transitivity (b * p) (b * (g * a)) ((b * g) * a);
    transitivity (b * p) ((b * g) * a) ((g * b) * a);
    transitivity (b * p) ((g * b) * a) (q * a);
    transitivity (b * p) (q * a) (a * q)
#pop-options

(* Helper: poly_div yields nonzero quotient when dividend has degree *)
#push-options "--z3rlimit 150 --fuel 1 --ifuel 1"
let poly_div_has_degree_local (#t:Type) {| f: field t |}
  (p d: polynomial t)
  : Lemma (requires deg d >= 0 /\ deg p >= 0 /\ divides d p)
          (ensures  deg (poly_div p d) >= 0)
  =
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    poly_div_correct p d;
    let q = poly_div p d in
    if deg q >= 0 then ()
    else begin
        degree_none_poly_eq_zero q;
        mul_congruence d q d (poly_zero #t);
        H.x_mul_zero #(polynomial t) d;
        degree_well_defined p (poly_zero #t)
    end
#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let poly_div_degree_local (#t:Type) {| f: field t |}
  (p d: polynomial t)
  : Lemma (requires deg d >= 0 /\ deg p >= 0 /\ divides d p)
          (ensures  deg (poly_div p d) >= 0 /\
                    deg (poly_div p d) ==
                    ((deg p) - (deg d)))
  = poly_div_has_degree_local p d;
    poly_div_correct p d;
    let q = poly_div p d in
    degree_mul d q;
    symmetry (d * q) p;
    degree_well_defined p (d * q)
#pop-options

(* Sylvester null vector: encodes b*p = a*q as a kernel element *)
let syl_null_vec (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (a b: polynomial t)
  : vector t ((m_deg ++ n_deg))
  = fun (j: fin ((m_deg ++ n_deg))) ->
      if (j <: nat) < n_deg
      then coeff b ((((n_deg - 1)) - (j <: nat)))
      else (- (coeff a ((((m_deg - 1)) - (((j <: nat) - n_deg))))))

(* Helper: when poly_eq(bp,aq), their coeff difference is zero *)
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let coeff_cancel (#t:Type) {| cr: commutative_ring t |} (bp aq: polynomial t) (kk: nat)
  : Lemma (requires (bp = aq))
          (ensures coeff bp kk + (- (coeff aq kk)) = (zero <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    poly_eq_means_equal_coeffs bp aq kk;
    add_congruence (coeff bp kk) (- (coeff aq kk)) (coeff aq kk) (- (coeff aq kk));
    H.x_plus_neg_x (coeff aq kk)
#pop-options

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let vdot_zero_via_name (#t:Type) {| cr: commutative_ring t |} (#n: nat{n > 0})
  (a b: vector t n) (f: fin n -> t)
  : Lemma (requires f == pointwise_mul a b /\ fin_sum f = (zero <: t))
          (ensures vector_dot a b = (zero <: t))
  = assert (forall (k: fin n). f k == pointwise_mul a b k);
    fin_sum_eq_pointwise f (pointwise_mul a b);
    vector_dot_reveal a b
#pop-options

(* Core lemma: syl_null_vec lies in ker(S^T) *)
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let syl_null_vec_is_null (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (p q a b: polynomial t)
  (i: fin ((m_deg ++ n_deg)))
  : Lemma
    (requires ((b * p) = (a * q)) /\
             L.length b <= n_deg /\ L.length a <= m_deg)
    (ensures  vector_dot (row (transpose (sylvester_matrix m_deg n_deg p q)) i)
                         (syl_null_vec m_deg n_deg a b)
            = (zero <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let size : pos = (m_deg ++ n_deg) in
    let st = transpose (sylvester_matrix m_deg n_deg p q) in
    let v  = syl_null_vec m_deg n_deg a b in
    let kk : nat = (((size - 1)) - (i <: nat)) in
    let f_p (j: fin size) : t = if (j <: nat) < n_deg
                                then pointwise_mul (row st i) v j else zero in
    let f_q (j: fin size) : t = if (j <: nat) >= n_deg
                                then pointwise_mul (row st i) v j else zero in
    let decomp_pf (j: fin size)
      : Lemma (pointwise_mul (row st i) v j = f_p j + f_q j) =
      if (j <: nat) < n_deg then (
        assert (f_p j == pointwise_mul (row st i) v j);
        assert (f_q j == (zero <: t));
        H.x_plus_zero (pointwise_mul (row st i) v j);
        symmetry (pointwise_mul (row st i) v j) (pointwise_mul (row st i) v j + zero)
      ) else (
        assert (f_p j == (zero <: t));
        assert (f_q j == pointwise_mul (row st i) v j);
        H.zero_plus_x (pointwise_mul (row st i) v j);
        symmetry (pointwise_mul (row st i) v j) (zero + pointwise_mul (row st i) v j)
      ) in
    let pw : (fin size -> t) = pointwise_mul (row st i) v in
    fin_sum_add_ext f_p f_q pw decomp_pf;
    coeff_cancel (b * p) (a * q) kk;

    // ========== P-half: fin_sum f_p = coeff(b*p, kk) ==========
    let g_fp (j:nat) : t = if j < n_deg then
        pointwise_mul (row st i) v (j <: fin size)
      else (zero <: t) in
    fin_sum_eq_sum_range f_p g_fp;
    sum_range_split g_fp 0 n_deg size;
    sum_range_all_zero g_fp n_deg size
      (fun (k: nat{n_deg <= k /\ k < size}) -> reflexivity (zero <: t));
    add_congruence (sum_range g_fp 0 n_deg) (sum_range g_fp n_deg size)
                   (sum_range g_fp 0 n_deg) (zero <: t);
    H.x_plus_zero (sum_range g_fp 0 n_deg);
    transitivity (sum_range g_fp 0 size)
                 (sum_range g_fp 0 n_deg + sum_range g_fp n_deg size)
                 (sum_range g_fp 0 n_deg + (zero <: t));
    transitivity (sum_range g_fp 0 size)
                 (sum_range g_fp 0 n_deg + (zero <: t))
                 (sum_range g_fp 0 n_deg);
    let g_bp (r:nat) : t = coeff b r * coeff p ((kk - r)) in
    let h_rev (j: nat{j < n_deg})
      : Lemma (g_fp j = g_bp ((((n_deg - 1)) - j)))
      = assert ((j <: nat) < n_deg);
        let j_f : fin size = (j <: fin size) in
        assert (g_fp j == pointwise_mul (row st i) v j_f);
        H.mul_commutativity_cr
          (coeff p ((((m_deg ++ j)) - (i <: nat))))
          (coeff b ((((n_deg - 1)) - j)))
    in
    sum_range_reverse_named g_fp g_bp n_deg h_rev;
    sum_range_split g_bp 0 (L.length b) n_deg;
    sum_range_all_zero g_bp (L.length b) n_deg
      (fun (r: nat{L.length b <= r /\ r < n_deg}) ->
        assert (coeff b r == (zero <: t));
        H.zero_mul_x (coeff p ((kk - r))));
    add_congruence (sum_range g_bp 0 (L.length b)) (sum_range g_bp (L.length b) n_deg)
                   (sum_range g_bp 0 (L.length b)) (zero <: t);
    H.x_plus_zero (sum_range g_bp 0 (L.length b));
    transitivity (sum_range g_bp 0 n_deg)
                 (sum_range g_bp 0 (L.length b) + sum_range g_bp (L.length b) n_deg)
                 (sum_range g_bp 0 (L.length b) + (zero <: t));
    transitivity (sum_range g_bp 0 n_deg)
                 (sum_range g_bp 0 (L.length b) + (zero <: t))
                 (sum_range g_bp 0 (L.length b));
    coeff_poly_mul_named b p kk g_bp
      (fun (r:nat) -> reflexivity (coeff b r * coeff p ((kk - r))));

    // ========== Q-half: fin_sum f_q = neg(coeff(a*q, kk)) ==========
    let g_fq (j:nat) : t = if j >= n_deg && j < size
      then pointwise_mul (row st i) v (j <: fin size)
      else (zero <: t) in
    fin_sum_eq_sum_range f_q g_fq;
    sum_range_split g_fq 0 n_deg size;
    sum_range_all_zero g_fq 0 n_deg
      (fun (k: nat{0 <= k /\ k < n_deg}) -> reflexivity (zero <: t));
    add_congruence (sum_range g_fq 0 n_deg) (sum_range g_fq n_deg size)
                   (zero <: t) (sum_range g_fq n_deg size);
    H.zero_plus_x (sum_range g_fq n_deg size);
    transitivity (sum_range g_fq 0 size)
                 (sum_range g_fq 0 n_deg + sum_range g_fq n_deg size)
                 ((zero <: t) + sum_range g_fq n_deg size);
    transitivity (sum_range g_fq 0 size)
                 ((zero <: t) + sum_range g_fq n_deg size)
                 (sum_range g_fq n_deg size);
    let f_sh : nat -> t = fun (j:nat) -> g_fq ((j ++ n_deg)) in
    sum_range_shift g_fq n_deg 0 m_deg;
    let g_aq (r:nat) : t = coeff a r * coeff q ((kk - r)) in
    let g_rev (j:nat) : t = if m_deg > 0 && j < m_deg
      then g_aq ((((m_deg - 1)) - j))
      else (zero <: t) in
    let neg_g_rev : nat -> t = pointwise_neg g_rev in
    sum_range_congruence f_sh neg_g_rev 0 m_deg
      (fun (j: nat{0 <= j /\ j < m_deg}) ->
        let jj : fin size = ((j ++ n_deg) <: fin size) in
        pointwise_neg_unfold g_rev j;
        assert (f_sh j == pointwise_mul (row st i) v jj);
        H.neg_mul_r
          (coeff q ((((j ++ n_deg)) - (i <: nat))))
          (coeff a ((((m_deg - 1)) - j)));
        H.mul_commutativity_cr
          (coeff q ((((j ++ n_deg)) - (i <: nat))))
          (coeff a ((((m_deg - 1)) - j)));
        neg_congruence
          (coeff q ((((j ++ n_deg)) - (i <: nat))) *
           coeff a ((((m_deg - 1)) - j)))
          (coeff a ((((m_deg - 1)) - j)) *
           coeff q ((((j ++ n_deg)) - (i <: nat))));
        transitivity (f_sh j)
          (- (coeff q ((((j ++ n_deg)) - (i <: nat))) *
                coeff a ((((m_deg - 1)) - j))))
          (neg_g_rev j)
      );
    sum_range_neg g_rev 0 m_deg;
    sum_range_reverse_named g_rev g_aq m_deg
      (fun (j: nat{j < m_deg}) -> reflexivity (g_rev j));
    neg_congruence (sum_range g_rev 0 m_deg) (sum_range g_aq 0 m_deg);
    sum_range_split g_aq 0 (L.length a) m_deg;
    sum_range_all_zero g_aq (L.length a) m_deg
      (fun (r: nat{L.length a <= r /\ r < m_deg}) ->
        assert (coeff a r == (zero <: t));
        H.zero_mul_x (coeff q ((kk - r))));
    add_congruence (sum_range g_aq 0 (L.length a)) (sum_range g_aq (L.length a) m_deg)
                   (sum_range g_aq 0 (L.length a)) (zero <: t);
    H.x_plus_zero (sum_range g_aq 0 (L.length a));
    transitivity (sum_range g_aq 0 m_deg)
                 (sum_range g_aq 0 (L.length a) + sum_range g_aq (L.length a) m_deg)
                 (sum_range g_aq 0 (L.length a) + (zero <: t));
    transitivity (sum_range g_aq 0 m_deg)
                 (sum_range g_aq 0 (L.length a) + (zero <: t))
                 (sum_range g_aq 0 (L.length a));
    neg_congruence (sum_range g_aq 0 m_deg) (sum_range g_aq 0 (L.length a));
    coeff_poly_mul_named a q kk g_aq
      (fun (r:nat) -> reflexivity (coeff a r * coeff q ((kk - r))));
    neg_congruence (sum_range g_aq 0 (L.length a)) (coeff (a * q) kk);

    add_congruence (fin_sum f_p) (fin_sum f_q)
                   (coeff (b * p) kk) (- (coeff (a * q) kk));
    assert (fin_sum pw = (zero <: t));
    assert (pw == pointwise_mul (row st i) v);
    vdot_zero_via_name #t #cr #size (row st i) v pw
#pop-options

(* Main theorem: forward direction of L4 *)
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let resultant_zero_of_common_divisor (#t:Type) {| f: field t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (p q g: polynomial t)
  : Lemma (requires
      deg p >= 0 /\ deg p <= m_deg /\
      deg q >= 0 /\ deg q <= n_deg /\
      divides g p /\
      divides g q /\
      deg g >= 1)
    (ensures resultant m_deg n_deg p q = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let size : pos = (m_deg ++ n_deg) in
    let a = poly_div p g in
    let b = poly_div q g in
    poly_div_has_degree_local q g;
    poly_div_degree_local q g;
    poly_div_has_degree_local p g;
    poly_div_degree_local p g;
    bp_eq_aq p q g () () ();
    let v = syl_null_vec m_deg n_deg a b in
    let sm = sylvester_matrix m_deg n_deg p q in
    let st = transpose sm in
    let null_hyp (i: fin size)
      : Lemma (null_vec_hyp st v i)
      = syl_null_vec_is_null m_deg n_deg p q a b i
    in
    Classical.forall_intro null_hyp;
    let deg_b = deg b in
    leading_coeff_nonzero b;
    let k : fin size = (((n_deg - 1)) - deg_b) in
    assert (v k == coeff b deg_b);
    assert (is_nonzero (v k));
    null_vec_implies_det_zero st v k;
    det_transpose sm;
    transitivity (det sm) (det st) (zero <: t)
#pop-options

(* ================================================================================ *)
(*  FOLDED-IN: Core.Polynomial.ResultantLinear *)
(* ================================================================================ *)

(* ================================================================ *)
(*  Unipotent upper-triangular determinant = 1  (general, reusable). *)
(* ================================================================ *)

let det_unipotent_upper_triangular (#t:Type) {| cr: commutative_ring t |}
  (#n: pos) (m: square_matrix t n)
  (diag_one: (i: fin n) -> Lemma (m i i = (one <: t)))
  : Lemma (requires is_upper_triangular m)
          (ensures  det m = (one <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    Classical.forall_intro diag_one;
    det_upper_triangular m;                               (* det m = diagonal_product m *)
    diagonal_product_pointwise m (id_matrix #t #(cr.cr_r) #n);   (* same diagonal as identity (all ones) *)
    det_upper_triangular (id_matrix #t #(cr.cr_r) #n);           (* det id = diagonal_product id *)
    det_identity #t #cr n;                                (* det id = one *)
    transitivity (det m) (det (id_matrix #t #(cr.cr_r) #n)) (one <: t)

(* ================================================================ *)
(*  The shear matrix  U[k][j] = a^{j-k} for k<=j, else 0.            *)
(* ================================================================ *)

let shear (#t:Type) {| cr: commutative_ring t |} (#n: pos) (a: t)
  : square_matrix t n
  = fun (k j: fin n) -> if (k <: nat) <= (j <: nat) then cpow a (j - k) else (zero <: t)

let shear_upper_triangular (#t:Type) {| cr: commutative_ring t |} (#n: pos) (a: t)
  : Lemma (is_upper_triangular (shear #t #cr #n a))
  = elim_equatable_laws t ()                             (* shear k j = 0 when k > j by definition *)

let shear_diagonal_one (#t:Type) {| cr: commutative_ring t |} (#n: pos) (a: t) (i: fin n)
  : Lemma (shear a i i = (one <: t))
  = elim_equatable_laws t ()                             (* shear i i = cpow a 0 = one *)

let det_shear_is_one (#t:Type) {| cr: commutative_ring t |} (#n: pos) (a: t)
  : Lemma (det (shear #t #cr #n a) = (one <: t))
  = shear_upper_triangular #t #cr #n a;
    det_unipotent_upper_triangular (shear #t #cr #n a) (shear_diagonal_one #t #cr #n a)

(* ================================================================ *)
(*  Milestone 1:  Res_{1,d}(x - a, B) = B(a).                        *)
(* ================================================================ *)

(* cpow a (m+1) = a * cpow a m  (definitional). *)
let cpow_succ (#t:Type) {| cr: commutative_ring t |} (a: t) (m: nat)
  : Lemma (cpow a ((m ++ 1)) = a * cpow a m)
  = elim_equatable_laws t ();
    reflexivity (a * cpow a m)

(* A "linear-shaped" polynomial: coeff 0 = neg a, coeff 1 = one, rest 0.
   (poly_linear #t #f a satisfies this — see linpoly_is_linear_shape below.)
   Stating the matrix lemmas over an ambient commutative_ring with this
   predicate keeps all fin_sum / matrix_mul / shear typeclass instances on
   a SINGLE inferred path, avoiding the field-vs-commutative_ring instance
   duplication that breaks fin_sum unification. *)
let linear_shape (#t:Type) {| cr: commutative_ring t |} (a: t) (p: polynomial t) : prop
  = coeff p 0 == ((- a) <: t) /\
    coeff p 1 == (one <: t) /\
    (forall (k: nat). k >= 2 ==> coeff p k == (zero <: t))

let poly_linear_is_linear_shape (#t:Type) {| f: field t |} (a: t)
  : Lemma (linear_shape a (poly_linear a))
  = let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    assert_norm (L.index (poly_linear a) 0 == ((- a) <: t));
    assert_norm (L.index (poly_linear a) 1 == (one <: t));
    assert (L.length (poly_linear a) == 2)

(* ---------------------------------------------------------------- *)
(*  Sylvester matrix entries for S = sylvester_matrix 1 d p b        *)
(*  where p has linear_shape a.  Size is nat_add 1 d = d+1.           *)
(*  Rows 0..d-1 are the (single) p-row copies (bidiagonal); row d is  *)
(*  the q-row = reversed coeffs of b.                                 *)
(* ---------------------------------------------------------------- *)

let syl_diag_one (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t) (d: nat{d >= 1})
  (i: fin (nat_add 1 d))
  : Lemma (requires (i <: nat) < d /\ linear_shape a p)
          (ensures sylvester_matrix 1 d p b i i == (one <: t))
  = sylvester_p_block_lookup 1 d p b i i

let syl_super_neg_a (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t) (d: nat{d >= 1})
  (i: fin (nat_add 1 d)) (j: fin (nat_add 1 d))
  : Lemma (requires (i <: nat) < d /\ (j <: nat) == ((i <: nat) ++ 1) /\ linear_shape a p)
          (ensures sylvester_matrix 1 d p b i j == ((- a) <: t))
  = sylvester_p_block_lookup 1 d p b i j

(* off-(bi)diagonal p-row entries vanish: for i<d and k <> i, k <> i+1. *)
let syl_p_other_zero (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t) (d: nat{d >= 1})
  (i: fin (nat_add 1 d)) (k: fin (nat_add 1 d))
  : Lemma (requires (i <: nat) < d /\
                    (k <: nat) <> (i <: nat) /\
                    (k <: nat) <> ((i <: nat) ++ 1) /\
                    linear_shape a p)
          (ensures sylvester_matrix 1 d p b i k == (zero <: t))
  = sylvester_p_block_lookup 1 d p b i k

(* last row entries: S[d][j] = coeff b (d - j). *)
let syl_last_row (#t:Type) {| cr: commutative_ring t |} (p b: polynomial t) (d: nat{d >= 1})
  (j: fin (nat_add 1 d))
  : Lemma (sylvester_matrix 1 d p b (d <: fin (nat_add 1 d)) j
         == coeff b ((d - (j <: nat))))
  = sylvester_q_block_lookup 1 d p b (d <: fin (nat_add 1 d)) j


(* ---------------------------------------------------------------- *)
(*  Entries of the shear column  col U j = (fun k -> U k j).          *)
(* ---------------------------------------------------------------- *)

let shear_entry_le (#t:Type) {| cr: commutative_ring t |} (#n: pos) (a: t)
  (k j: fin n)
  : Lemma (requires (k <: nat) <= (j <: nat))
          (ensures shear a k j == cpow a (((j <: nat) - (k <: nat))))
  = ()

let shear_entry_gt (#t:Type) {| cr: commutative_ring t |} (#n: pos) (a: t)
  (k j: fin n)
  : Lemma (requires (k <: nat) > (j <: nat))
          (ensures shear a k j == (zero <: t))
  = ()

(* ---------------------------------------------------------------- *)
(*  The two surviving terms of a bidiagonal row collapse to a        *)
(*  Kronecker delta:   U[i][j] + (neg a) * U[i+1][j] = [i = j].       *)
(* ---------------------------------------------------------------- *)

let bidiag_value (#t:Type) {| cr: commutative_ring t |} (#n: pos) (a: t)
  (i: fin n{(i <: nat) + 1 < n}) (j: fin n)
  : Lemma (shear a i j + (- a) * shear a ((((i <: nat) ++ 1)) <: fin n) j
         = id_matrix #t #(cr.cr_r) #n i j)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let i1 : fin n = (((i <: nat) ++ 1)) <: fin n in
    let ui  = shear a i j in
    let ui1 = shear a i1 j in
    if (j <: nat) = (i <: nat) then begin
      (* ui = cpow a 0 = one ; ui1 = 0 (i1 > j) ; one + (neg a)*0 = one = id i j *)
      shear_entry_le a i j;                     (* ui = cpow a 0 = one *)
      shear_entry_gt a i1 j;                    (* ui1 = zero *)
      H.x_mul_zero (- a);                               (* (neg a)*0 = 0 ... wait ui1 *)
      mul_congruence (- a) ui1 (- a) (zero <: t);
      H.x_mul_zero (- a);
      H.x_plus_zero ui;
      add_congruence ui ((- a) * ui1) ui (zero <: t);
      (* ui = cpow a 0 = one ; id i i = one *)
      assert (ui == (one <: t));
      assert (id_matrix #t #(cr.cr_r) #n i j == (one <: t));
      transitivity (ui + (- a) * ui1) ui (id_matrix i j)
    end else if (j <: nat) > (i <: nat) then begin
      (* j > i: ui = cpow a (j-i), ui1 = cpow a (j-i-1), (neg a)*ui1 = neg(cpow a (j-i)) *)
      shear_entry_le a i j;                     (* ui = cpow a (j-i) *)
      shear_entry_le a i1 j;                    (* ui1 = cpow a (j-(i+1)) = cpow a (j-i-1) *)
      let m : nat = ((j <: nat) - ((i <: nat) + 1)) in
      cpow_succ a m;                               (* cpow a (m+1) = a * cpow a m ; m+1 = j-i *)
      (* (neg a)*ui1 = (neg a)*cpow a m = neg (a * cpow a m) = neg (cpow a (m+1)) = neg ui *)
      H.neg_mul_l a (cpow a m);                           (* (neg a)*cpow a m = neg (a*cpow a m) *)
      neg_congruence (a * cpow a m) (cpow a ((m ++ 1)));
      assert (ui == cpow a ((m ++ 1)));
      add_congruence ui ((- a) * ui1) ui (- ui);
      H.x_plus_neg_x ui;                                  (* ui + neg ui = zero *)
      assert (id_matrix #t #(cr.cr_r) #n i j == (zero <: t));
      transitivity (ui + (- a) * ui1) (zero <: t) (id_matrix i j)
    end else begin
      (* j < i: ui = 0 (i>j), ui1 = 0 (i1>j) *)
      shear_entry_gt a i j;                     (* ui = zero *)
      shear_entry_gt a i1 j;                    (* ui1 = zero *)
      mul_congruence (- a) ui1 (- a) (zero <: t);
      H.x_mul_zero (- a);
      add_congruence ui ((- a) * ui1) (zero <: t) (zero <: t);
      H.x_plus_zero (zero <: t);
      assert (id_matrix #t #(cr.cr_r) #n i j == (zero <: t));
      transitivity (ui + (- a) * ui1) (zero <: t) (id_matrix i j)
    end

(* ---------------------------------------------------------------- *)
(*  Bidiagonal row of  M = S * U  is a row of the identity:           *)
(*    for i < d,   M[i][j] = id_matrix i j.                           *)
(* ---------------------------------------------------------------- *)

(* Generic: a bidiagonal row dotted with the shear column gives a row of the
   identity.  Stated over a fresh size parameter #n (NOT a let), so fin_sum's
   implicit #n infers cleanly throughout — mirroring det's collapse lemmas.   *)
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let bidiag_row_times_shear (#t:Type) {| cr: commutative_ring t |} (#n: pos)
  (a: t) (s: square_matrix t n) (i j: fin n)
  : Lemma (requires (i <: nat) + 1 < n /\
                    s i i = (one <: t) /\
                    s i ((((i <: nat) ++ 1)) <: fin n) = ((- a) <: t) /\
                    (forall (k: fin n). (k <: nat) <> (i <: nat) /\
                                        (k <: nat) <> ((i <: nat) ++ 1)
                                        ==> s i k = (zero <: t)))
          (ensures matrix_mul s (shear a) i j
                 = id_matrix #t #(cr.cr_r) #n i j)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let u = shear a in
    let i1 : fin n = (((i <: nat) ++ 1)) <: fin n in
    let c0 : t = u i j in                                       (* shear a i j *)
    let c1 : t = (- a) * u i1 j in                            (* (neg a) * shear a (i+1) j *)
    let decomp (k: fin n)
      : Lemma (pointwise_mul (row s i) (col u j) k
             = pointwise_add (pointwise_mul (fin_kronecker_delta i)  (const c0))
                             (pointwise_mul (fin_kronecker_delta i1) (const c1)) k) =
      pointwise_mul_unfold (row s i) (col u j) k;               (* pw k = s i k * u k j *)
      pointwise_add_unfold (pointwise_mul (fin_kronecker_delta i)  (const c0))
                           (pointwise_mul (fin_kronecker_delta i1) (const c1)) k;
      pointwise_mul_unfold (fin_kronecker_delta i)  (const c0) k;
      pointwise_mul_unfold (fin_kronecker_delta i1) (const c1) k;
      const_unfold c0 k;
      const_unfold c1 k;
      fin_kronecker_delta_unfold #t i  k;
      fin_kronecker_delta_unfold #t i1 k;
      let lhs = (row s i) k * (col u j) k in
      let rhs = (fin_kronecker_delta i k) * c0 + (fin_kronecker_delta i1 k) * c1 in
      if (k <: nat) = (i <: nat) then begin
        kronecker_delta_eq #t (i <: nat) (k <: nat);            (* delta i k = one *)
        kronecker_delta_neq #t (i1 <: nat) (k <: nat);          (* delta i1 k = zero *)
        (* lhs = s i k * u i j = one * u i j = c0 ; rhs = one*c0 + zero*c1 = c0 *)
        assert ((row s i) k == s i i);
        assert ((col u j) k == c0);
        assert (s i i = (one <: t));
        mul_congruence (s i i) (col u j k) (one <: t) (col u j k);   (* lhs = one * col u j k *)
        H.one_mul_x (col u j k);
        H.one_mul_x c0;
        H.zero_mul_x c1;
        add_congruence ((fin_kronecker_delta i k) * c0) ((fin_kronecker_delta i1 k) * c1) c0 (zero <: t);
        H.x_plus_zero c0;
        symmetry rhs lhs
      end else if (k <: nat) = (((i <: nat) ++ 1)) then begin
        kronecker_delta_neq #t (i <: nat) (k <: nat);           (* delta i k = zero *)
        kronecker_delta_eq #t (i1 <: nat) (k <: nat);           (* delta i1 k = one *)
        assert ((k <: nat) == (i1 <: nat));
        (* lhs = s i i1 * u k j = neg a * u i1 j = c1 *)
        assert ((row s i) k == s i i1);
        assert ((col u j) k == u i1 j);
        assert (s i i1 = ((- a) <: t));
        mul_congruence (s i i1) (col u j k) (- a) (col u j k);     (* lhs = neg a * col u j k *)
        mul_congruence (- a) (col u j k) (- a) (u i1 j);
        H.zero_mul_x c0;
        H.one_mul_x c1;
        add_congruence ((fin_kronecker_delta i k) * c0) ((fin_kronecker_delta i1 k) * c1) (zero <: t) c1;
        H.zero_plus_x c1;
        symmetry rhs lhs
      end else begin
        kronecker_delta_neq #t (i <: nat) (k <: nat);           (* delta i k = zero *)
        kronecker_delta_neq #t (i1 <: nat) (k <: nat);          (* delta i1 k = zero *)
        (* lhs = zero * u k j = zero (s i k = zero by hypothesis) *)
        assert ((row s i) k == s i k);
        assert (s i k = (zero <: t));
        mul_congruence (s i k) (col u j k) (zero <: t) (col u j k);
        H.zero_mul_x (col u j k);
        H.zero_mul_x c0;
        H.zero_mul_x c1;
        add_congruence ((fin_kronecker_delta i k) * c0) ((fin_kronecker_delta i1 k) * c1) (zero <: t) (zero <: t);
        H.x_plus_zero (zero <: t);
        symmetry rhs lhs
      end
    in
    (* fin_sum pw = fin_sum (add F0 F1) = fin_sum F0 + fin_sum F1 = c0 + c1.
       #n is a real parameter here, so all fin_sum implicits infer cleanly. *)
    fin_sum_congruence (pointwise_mul (row s i) (col u j))
                       (pointwise_add (pointwise_mul (fin_kronecker_delta i)  (const c0))
                                      (pointwise_mul (fin_kronecker_delta i1) (const c1)))
                       decomp;
    fin_sum_add (pointwise_mul (fin_kronecker_delta i)  (const c0))
                (pointwise_mul (fin_kronecker_delta i1) (const c1));
    fin_sum_kronecker i  (const c0);
    fin_sum_kronecker i1 (const c1);
    const_unfold c0 i;                                          (* const c0 i == c0 *)
    const_unfold c1 i1;                                         (* const c1 i1 == c1 *)
    (* fin_sum F0 = c0 ; fin_sum F1 = c1 *)
    H.eq_then_leibniz (fin_sum (pointwise_mul (fin_kronecker_delta i)  (const c0))) (const c0 i)  c0;
    H.eq_then_leibniz (fin_sum (pointwise_mul (fin_kronecker_delta i1) (const c1))) (const c1 i1) c1;
    add_congruence (fin_sum (pointwise_mul (fin_kronecker_delta i)  (const c0)))
                   (fin_sum (pointwise_mul (fin_kronecker_delta i1) (const c1))) c0 c1;
    (* fin_sum (add F0 F1) = fin_sum F0 + fin_sum F1 = c0 + c1 *)
    transitivity (fin_sum (pointwise_add (pointwise_mul (fin_kronecker_delta i)  (const c0))
                                         (pointwise_mul (fin_kronecker_delta i1) (const c1))))
                 (fin_sum (pointwise_mul (fin_kronecker_delta i)  (const c0))
                  + fin_sum (pointwise_mul (fin_kronecker_delta i1) (const c1)))
                 (c0 + c1);
    (* fin_sum pw = fin_sum (add F0 F1) = c0 + c1 *)
    transitivity (fin_sum (pointwise_mul (row s i) (col u j)))
                 (fin_sum (pointwise_add (pointwise_mul (fin_kronecker_delta i)  (const c0))
                                         (pointwise_mul (fin_kronecker_delta i1) (const c1))))
                 (c0 + c1);
    (* M i j == fin_sum pw, then = c0 + c1 *)
    matrix_mul_to_fin_sum s u i j;
    H.leibniz_then_eq (matrix_mul s u i j) (fin_sum (pointwise_mul (row s i) (col u j))) (c0 + c1);
    bidiag_value a i j;                               (* c0 + c1 = id i j *)
    transitivity (matrix_mul s u i j) (c0 + c1) (id_matrix i j)
#pop-options

(* Sylvester-specific wrapper: row i (< d) of S = sylvester_matrix 1 d p b
   (with p of linear_shape a) dotted with the shear is a row of the identity. *)
let mul_row_bidiag (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t) (d: nat{d >= 1})
  (i: fin (nat_add 1 d)) (j: fin (nat_add 1 d))
  : Lemma (requires (i <: nat) < d /\ linear_shape a p)
          (ensures matrix_mul (sylvester_matrix 1 d p b)
                              (shear a) i j
                 = id_matrix #t #(cr.cr_r) #(nat_add 1 d) i j)
  = H.elim_equatable_laws t ();
    let s = sylvester_matrix 1 d p b in
    let i1 : fin (nat_add 1 d) = (((i <: nat) ++ 1)) <: fin (nat_add 1 d) in
    syl_diag_one a p b d i;                              (* s i i == one *)
    H.leibniz_to_eq (s i i) (one <: t);                         (* s i i = one *)
    syl_super_neg_a a p b d i i1;                        (* s i i1 == neg a *)
    H.leibniz_to_eq (s i i1) ((- a) <: t);                      (* s i i1 = neg a *)
    let others (k: fin (nat_add 1 d))
      : Lemma ((k <: nat) <> (i <: nat) /\
               (k <: nat) <> ((i <: nat) ++ 1) ==> s i k = (zero <: t)) =
      if (k <: nat) <> (i <: nat) && (k <: nat) <> ((i <: nat) ++ 1)
      then begin
        syl_p_other_zero a p b d i k;                    (* s i k == zero *)
        H.leibniz_to_eq (s i k) (zero <: t)                     (* s i k = zero *)
      end
      else ()
    in
    Classical.forall_intro others;
    bidiag_row_times_shear a s i j

(* ---------------------------------------------------------------- *)
(*  The corner entry  M[d][d] = poly_eval b a.                       *)
(*    M[d][d] = Sum_{k<=d} coeff b (d-k) * a^{d-k}                    *)
(*           = Sum_{m<=d} coeff b m * a^m  (reindex m = d-k)          *)
(*           = poly_eval b a   (length b = d+1).                      *)
(* ---------------------------------------------------------------- *)

let last_row_entry_value (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t)
  (d: nat{d >= 1})
  (k: fin (nat_add 1 d))
  : Lemma (pointwise_mul (row (sylvester_matrix 1 d p b) (d <: fin (nat_add 1 d)))
                         (col (shear a) (d <: fin (nat_add 1 d))) k
         = eval_term b a ((d - (k <: nat))))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let n : pos = nat_add 1 d in
    let s = sylvester_matrix 1 d p b in
    let u = shear a in
    pointwise_mul_unfold (row s (d <: fin n)) (col u (d <: fin n)) k;   (* = s d k * u k d *)
    syl_last_row p b d k;                            (* s d k == coeff b (d-k) *)
    (* u k d = shear a k d = cpow a (d - k)  since k <= d *)
    shear_entry_le a k (d <: fin n);             (* u k d == cpow a (d-k) *)
    (* eval_term b a (d-k) = coeff b (d-k) * cpow a (d-k) *)
    assert (eval_term b a ((d - (k <: nat)))
            == coeff b ((d - (k <: nat))) * cpow a ((d - (k <: nat))));
    assert (row s (d <: fin n) k == s (d <: fin n) k);
    assert (col u (d <: fin n) k == u k (d <: fin n))

(* Generic diagonal-entry bridge (over a real #n parameter, so fin_sum
   implicits compose cleanly):  if the (i,i) dot-product column function w
   sums to v, then matrix_mul s u i i = v. *)
let matrix_mul_diag_value (#t:Type) {| cr: commutative_ring t |} (#n: pos)
  (s u: square_matrix t n) (i: fin n) (w: fin n -> t) (v: t)
  : Lemma (requires (forall (k: fin n). pointwise_mul (row s i) (col u i) k = w k) /\
                    fin_sum w = v)
          (ensures matrix_mul s u i i = v)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pw_eq (k: fin n) : Lemma (pointwise_mul (row s i) (col u i) k = w k) = () in
    fin_sum_congruence (pointwise_mul (row s i) (col u i)) w pw_eq;   (* fin_sum pw = fin_sum w *)
    matrix_mul_to_fin_sum s u i i;                                    (* M i i == fin_sum pw *)
    assert (matrix_mul s u i i = v)

let mul_corner_is_eval (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t)
  (d: nat{d >= 1})
  : Lemma (requires deg b == d)
          (ensures matrix_mul (sylvester_matrix 1 d p b)
                              (shear a)
                              (d <: fin (nat_add 1 d)) (d <: fin (nat_add 1 d))
                 = poly_eval b a)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let n : pos = nat_add 1 d in
    let s = sylvester_matrix 1 d p b in
    let u = shear a in
    let dd : fin n = (d <: fin n) in
    assert (L.length b == (d ++ 1));
    (* column function  w k = eval_term b a (d - k)  (= pw k by last_row_entry_value) *)
    let w : (fin n -> t) = fun (k: fin n) -> eval_term b a ((d - (k <: nat))) in
    let g : nat -> t = fun (k:nat) -> if k < n then eval_term b a ((d - k))
                                      else (zero <: t) in
    (* fin_sum w = poly_eval b a, via reindex on sum_range *)
    let w_eq_g (k: nat{k < n}) : Lemma (g k = w (k <: fin n)) = reflexivity (w (k <: fin n)) in
    Classical.forall_intro w_eq_g;
    fin_sum_eq_sum_range w g;                              (* fin_sum w = sum_range g 0 n *)
    let rev (j: nat{j < n}) : Lemma (g j = eval_term b a ((((n - 1)) - j))) =
      reflexivity (eval_term b a ((d - j)))
    in
    sum_range_reverse_named g (eval_term b a) n rev;       (* sum_range g 0 n = sum_range (eval_term b a) 0 n *)
    (* pw k = w k  for all k *)
    let pw_w (k: fin n) : Lemma (pointwise_mul (row s dd) (col u dd) k = w k) =
      last_row_entry_value a p b d k
    in
    Classical.forall_intro pw_w;
    matrix_mul_diag_value #t #cr #n s u dd w (poly_eval b a)

(* ---------------------------------------------------------------- *)
(*  M = S * U is lower-triangular and its diagonal product is B(a).  *)
(* ---------------------------------------------------------------- *)

(* M[i][j] = 0 for j > i:
   - i < d : M[i][j] = id i j (mul_row_bidiag) and id i j = 0 since i <> j;
   - i = d : j > d is impossible in fin (d+1).                          *)
let mul_is_lower_triangular (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t)
  (d: nat{d >= 1})
  : Lemma (requires linear_shape a p)
          (ensures is_lower_triangular
                     (matrix_mul (sylvester_matrix 1 d p b) (shear a)))
  = H.elim_equatable_laws t ();
    let n : pos = nat_add 1 d in
    let s = sylvester_matrix 1 d p b in
    let u = shear a in
    let m = matrix_mul s u in
    let upper (i j: fin n) : Lemma ((j <: nat) > (i <: nat) ==> m i j = (zero <: t)) =
      if (j <: nat) > (i <: nat) then begin
        (* then i < d  (since j <= d) *)
        assert ((i <: nat) < d);
        mul_row_bidiag a p b d i j;                 (* m i j = id i j *)
        assert (~(i == j));
        id_matrix_off #t #(cr.cr_r) #n i j;                (* id i j == zero *)
        H.leibniz_to_eq (id_matrix #t #(cr.cr_r) #n i j) (zero <: t);   (* id i j = zero *)
        H.trans_for_calc t ();
        transitivity (m i j) (id_matrix #t #(cr.cr_r) #n i j) (zero <: t)
      end else ()
    in
    Classical.forall_intro_2 upper

(* diagonal_product_from M k = B(a) for all k <= d:
   downward the first d diagonal entries are one, the last is B(a). *)
let rec diag_prod_from_is_eval (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t)
  (d: nat{d >= 1}) (k: nat{k <= d})
  : Lemma (requires linear_shape a p /\ deg b == d)
          (ensures diagonal_product_from
                     (matrix_mul (sylvester_matrix 1 d p b) (shear a)) k
                 = poly_eval b a)
          (decreases (d - k))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let n : pos = nat_add 1 d in
    let s = sylvester_matrix 1 d p b in
    let u = shear a in
    let m = matrix_mul s u in
    if k = d then begin
      (* diagonal_product_from m d = m[d][d] * diagonal_product_from m (d+1)
                                   = B(a) * one = B(a) *)
      mul_corner_is_eval a p b d;                    (* m[d][d] = poly_eval b a *)
      assert (diagonal_product_from m d
              == m (d <: fin n) (d <: fin n) * diagonal_product_from m ((d ++ 1)));
      assert (diagonal_product_from m ((d ++ 1)) == (one <: t));   (* k+1 >= n *)
      H.x_mul_one (m (d <: fin n) (d <: fin n));
      mul_congruence (m (d <: fin n) (d <: fin n)) (diagonal_product_from m ((d ++ 1)))
                     (m (d <: fin n) (d <: fin n)) (one <: t);
      transitivity (diagonal_product_from m d)
                   (m (d <: fin n) (d <: fin n) * diagonal_product_from m ((d ++ 1)))
                   (m (d <: fin n) (d <: fin n) * (one <: t));
      transitivity (diagonal_product_from m d)
                   (m (d <: fin n) (d <: fin n) * (one <: t))
                   (m (d <: fin n) (d <: fin n));
      transitivity (diagonal_product_from m d) (m (d <: fin n) (d <: fin n)) (poly_eval b a)
    end else begin
      (* k < d:  m[k][k] = id k k = one ; diagonal_product_from m k = one * tail = tail *)
      diag_prod_from_is_eval a p b d ((k ++ 1));   (* IH: tail = B(a) *)
      mul_row_bidiag a p b d (k <: fin n) (k <: fin n);         (* m[k][k] = id k k *)
      id_matrix_diag #t #(cr.cr_r) #n (k <: fin n);                    (* id k k == one *)
      H.leibniz_to_eq (id_matrix #t #(cr.cr_r) #n (k <: fin n) (k <: fin n)) (one <: t);
      assert (diagonal_product_from m k
              == m (k <: fin n) (k <: fin n) * diagonal_product_from m ((k ++ 1)));
      mul_congruence (m (k <: fin n) (k <: fin n)) (diagonal_product_from m ((k ++ 1)))
                     (one <: t) (diagonal_product_from m ((k ++ 1)));
      H.one_mul_x (diagonal_product_from m ((k ++ 1)));
      transitivity (diagonal_product_from m k)
                   (m (k <: fin n) (k <: fin n) * diagonal_product_from m ((k ++ 1)))
                   ((one <: t) * diagonal_product_from m ((k ++ 1)));
      transitivity (diagonal_product_from m k)
                   ((one <: t) * diagonal_product_from m ((k ++ 1)))
                   (diagonal_product_from m ((k ++ 1)));
      transitivity (diagonal_product_from m k)
                   (diagonal_product_from m ((k ++ 1)))
                   (poly_eval b a)
    end

let mul_diagonal_product_is_eval (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t)
  (d: nat{d >= 1})
  : Lemma (requires linear_shape a p /\ deg b == d)
          (ensures diagonal_product
                     (matrix_mul (sylvester_matrix 1 d p b) (shear a))
                 = poly_eval b a)
  = diag_prod_from_is_eval a p b d 0

(* ---------------------------------------------------------------- *)
(*  Degenerate case d = 0:  B a degree-0 (nonzero constant).         *)
(*  The Sylvester matrix is 1x1 with single entry coeff b 0;          *)
(*  det = coeff b 0 = poly_eval b a.                                  *)
(* ---------------------------------------------------------------- *)

let resultant_linear_const (#t:Type) {| f: field t |} (a: t) (b: polynomial t)
  : Lemma (requires deg b == 0)
          (ensures (let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
                    resultant 1 0 (poly_linear a) b = poly_eval b a))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pl = poly_linear a in
    let s = sylvester_matrix 1 0 pl b in
    assert (L.length b == 1);
    (* det s = s[0][0] = coeff b 0 *)
    determinant_size_one s;                          (* det s = s 0 0 *)
    sylvester_q_block_lookup 1 0 pl b (0 <: fin (nat_add 1 0)) (0 <: fin (nat_add 1 0));
    assert (s (0 <: fin (nat_add 1 0)) (0 <: fin (nat_add 1 0)) == coeff b 0);
    (* poly_eval b a = sum_range (eval_term b a) 0 1 = eval_term b a 0 = coeff b 0 * cpow a 0 = coeff b 0 *)
    let g = eval_term b a in
    sum_range_unfold_left g 0 1;
    sum_range_empty g 1 1;
    H.x_plus_zero (g 0);
    add_congruence (g 0) (sum_range g 1 1) (g 0) (zero <: t);
    (* g 0 = coeff b 0 * cpow a 0 = coeff b 0 * one = coeff b 0 *)
    assert (g 0 == coeff b 0 * cpow a 0);
    H.x_mul_one (coeff b 0);                                (* coeff b 0 * one = coeff b 0 *)
    (* det s = coeff b 0 ; resultant = det s *)
    resultant_unfold 1 0 pl b;
    H.leibniz_then_eq (resultant 1 0 pl b) (det s) (poly_eval b a)

(* ================================================================ *)
(*  MAIN THEOREM (Milestone 1):  Res_{1,d}(x - a, B) = B(a).         *)
(* ================================================================ *)

let resultant_linear (#t:Type) {| f: field t |} (a: t) (b: polynomial t)
  : Lemma (requires deg b >= 0)
          (ensures (let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
                    resultant 1 (deg b) (poly_linear a) b
                    = poly_eval b a))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let d : nat = deg b in
    let pl = poly_linear a in
    poly_linear_is_linear_shape a;                   (* linear_shape a pl *)
    if d = 0 then resultant_linear_const a b
    else begin
    let s = sylvester_matrix 1 d pl b in
    let u = shear a in
    let m = matrix_mul s u in
    (* det (S*U) = det S * det U = det S * one = det S *)
    det_mul s u;                     (* det m = det s * det u *)
    det_shear_is_one #t #cr #(nat_add 1 d) a;              (* det u = one *)

    mul_congruence (det s) (det u) (det s) (one <: t);
    H.x_mul_one (det s);
    transitivity (det m) (det s * det u) (det s * (one <: t));
    transitivity (det m) (det s * (one <: t)) (det s);     (* det m = det s *)
    (* det m = diagonal_product m = poly_eval b a *)
    mul_is_lower_triangular a pl b d;
    det_lower_triangular #t #cr #(nat_add 1 d) m;          (* det m = diagonal_product m *)
    mul_diagonal_product_is_eval a pl b d;          (* diagonal_product m = poly_eval b a *)
    transitivity (det m) (diagonal_product m) (poly_eval b a);
    (* det s = det m = poly_eval b a *)

    transitivity (det s) (det m) (poly_eval b a);
    (* resultant = det s *)
    resultant_unfold 1 d pl b;
    H.leibniz_then_eq (resultant 1 d pl b) (det s) (poly_eval b a)
    end

(* ================================================================ *)
(*  TASK 1: generalize to a LARGER FORMAL DEGREE.                    *)
(*                                                                   *)
(*    Res_{1,N}(x - a, B) = B(a)     for any formal degree N >= deg B *)
(*                                                                   *)
(*  The peeling factorization needs the (x-a)-multiplication block   *)
(*  Mul' = sylvester_matrix 1 N (x-a) B with N = m+n possibly > deg B.*)
(*  The shear machinery is unchanged (it is generic in the size and  *)
(*  only needs `linear_shape a p`); the ONE place the original proof *)
(*  used `deg B == d` was the corner reindex, where `poly_eval b a   *)
(*  == sum_range (eval_term b a) 0 (length b)`.  For N > deg B the    *)
(*  corner sum runs to N+1 instead, and `eval_extend` (summing past  *)
(*  the support is harmless) re-establishes `= poly_eval b a`.       *)
(* ================================================================ *)

(* Corner entry of M = S*U at formal degree N >= deg B is still B(a). *)
let mul_corner_is_eval_formal (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t)
  (bigN: nat{bigN >= 1})
  : Lemma (requires deg b >= 0 /\ deg b <= bigN)
          (ensures matrix_mul (sylvester_matrix 1 bigN p b)
                              (shear a)
                              (bigN <: fin (nat_add 1 bigN)) (bigN <: fin (nat_add 1 bigN))
                 = poly_eval b a)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let n : pos = nat_add 1 bigN in
    let s = sylvester_matrix 1 bigN p b in
    let u = shear a in
    let dd : fin n = (bigN <: fin n) in
    (* length b = deg b + 1 <= bigN + 1 = n  (poly_deg unfolds to Some (length-1)) *)
    assert (L.length b == ((deg b) ++ 1));
    assert (L.length b <= n);
    let w : (fin n -> t) = fun (k: fin n) -> eval_term b a ((bigN - (k <: nat))) in
    let g : nat -> t = fun (k:nat) -> if k < n then eval_term b a ((bigN - k))
                                      else (zero <: t) in
    let w_eq_g (k: nat{k < n}) : Lemma (g k = w (k <: fin n)) = reflexivity (w (k <: fin n)) in
    Classical.forall_intro w_eq_g;
    fin_sum_eq_sum_range w g;                              (* fin_sum w = sum_range g 0 n *)
    let rev (j: nat{j < n}) : Lemma (g j = eval_term b a ((((n - 1)) - j))) =
      reflexivity (eval_term b a ((bigN - j)))
    in
    sum_range_reverse_named g (eval_term b a) n rev;       (* sum_range g 0 n = sum_range (eval_term b a) 0 n *)
    eval_extend b a n;                                      (* sum_range (eval_term b a) 0 n = poly_eval b a  (n >= length b) *)
    let pw_w (k: fin n) : Lemma (pointwise_mul (row s dd) (col u dd) k = w k) =
      last_row_entry_value a p b bigN k
    in
    Classical.forall_intro pw_w;
    matrix_mul_diag_value #t #cr #n s u dd w (poly_eval b a)

(* diagonal_product_from M k = B(a) for all k <= bigN (formal degree). *)
let rec diag_prod_from_is_eval_formal (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t)
  (bigN: nat{bigN >= 1}) (k: nat{k <= bigN})
  : Lemma (requires linear_shape a p /\ deg b >= 0 /\ deg b <= bigN)
          (ensures diagonal_product_from
                     (matrix_mul (sylvester_matrix 1 bigN p b) (shear a)) k
                 = poly_eval b a)
          (decreases (bigN - k))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let n : pos = nat_add 1 bigN in
    let s = sylvester_matrix 1 bigN p b in
    let u = shear a in
    let m = matrix_mul s u in
    if k = bigN then begin
      mul_corner_is_eval_formal a p b bigN;          (* m[N][N] = poly_eval b a *)
      assert (diagonal_product_from m bigN
              == m (bigN <: fin n) (bigN <: fin n) * diagonal_product_from m ((bigN ++ 1)));
      assert (diagonal_product_from m ((bigN ++ 1)) == (one <: t));   (* k+1 >= n *)
      H.x_mul_one (m (bigN <: fin n) (bigN <: fin n));
      mul_congruence (m (bigN <: fin n) (bigN <: fin n)) (diagonal_product_from m ((bigN ++ 1)))
                     (m (bigN <: fin n) (bigN <: fin n)) (one <: t);
      transitivity (diagonal_product_from m bigN)
                   (m (bigN <: fin n) (bigN <: fin n) * diagonal_product_from m ((bigN ++ 1)))
                   (m (bigN <: fin n) (bigN <: fin n) * (one <: t));
      transitivity (diagonal_product_from m bigN)
                   (m (bigN <: fin n) (bigN <: fin n) * (one <: t))
                   (m (bigN <: fin n) (bigN <: fin n));
      transitivity (diagonal_product_from m bigN) (m (bigN <: fin n) (bigN <: fin n)) (poly_eval b a)
    end else begin
      diag_prod_from_is_eval_formal a p b bigN ((k ++ 1));   (* IH: tail = B(a) *)
      mul_row_bidiag a p b bigN (k <: fin n) (k <: fin n);                (* m[k][k] = id k k *)
      id_matrix_diag #t #(cr.cr_r) #n (k <: fin n);                              (* id k k == one *)
      H.leibniz_to_eq (id_matrix #t #(cr.cr_r) #n (k <: fin n) (k <: fin n)) (one <: t);
      assert (diagonal_product_from m k
              == m (k <: fin n) (k <: fin n) * diagonal_product_from m ((k ++ 1)));
      mul_congruence (m (k <: fin n) (k <: fin n)) (diagonal_product_from m ((k ++ 1)))
                     (one <: t) (diagonal_product_from m ((k ++ 1)));
      H.one_mul_x (diagonal_product_from m ((k ++ 1)));
      transitivity (diagonal_product_from m k)
                   (m (k <: fin n) (k <: fin n) * diagonal_product_from m ((k ++ 1)))
                   ((one <: t) * diagonal_product_from m ((k ++ 1)));
      transitivity (diagonal_product_from m k)
                   ((one <: t) * diagonal_product_from m ((k ++ 1)))
                   (diagonal_product_from m ((k ++ 1)));
      transitivity (diagonal_product_from m k)
                   (diagonal_product_from m ((k ++ 1)))
                   (poly_eval b a)
    end

(* MAIN (Task 1):  Res_{1,N}(x - a, B) = B(a)  for any formal degree N >= deg B. *)
let resultant_linear_formal (#t:Type) {| f: field t |} (a: t) (b: polynomial t)
  (bigN: nat{bigN >= 1})
  : Lemma (requires deg b >= 0 /\ deg b <= bigN)
          (ensures (let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
                    resultant 1 bigN (poly_linear a) b
                    = poly_eval b a))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pl = poly_linear a in
    poly_linear_is_linear_shape a;                   (* linear_shape a pl *)
    let s = sylvester_matrix 1 bigN pl b in
    let u = shear a in
    let m = matrix_mul s u in
    (* det (S*U) = det S * det U = det S * one = det S *)
    det_mul s u;                  (* det m = det s * det u *)
    det_shear_is_one #t #cr #(nat_add 1 bigN) a;           (* det u = one *)
    mul_congruence (det s) (det u) (det s) (one <: t);
    H.x_mul_one (det s);
    (* det m = diagonal_product m = poly_eval b a *)
    mul_is_lower_triangular a pl b bigN;
    det_lower_triangular #t #cr #(nat_add 1 bigN) m;       (* det m = diagonal_product m *)
    diag_prod_from_is_eval_formal a pl b bigN 0;    (* diagonal_product m = poly_eval b a *)
    assert (diagonal_product m == diagonal_product_from m 0);
    resultant_unfold 1 bigN pl b;
    H.leibniz_then_eq (resultant 1 bigN pl b) (det s) (poly_eval b a)

(* ================================================================ *)
(*  Milestone 2 (partial): Res_{0,n}(const c, B) = c^n.             *)
(*                                                                  *)
(*  With m_deg = 0, the Sylvester matrix of the constant polynomial *)
(*  [c] (formal degree 0) and B (formal degree n) is the n x n      *)
(*  matrix  S[i][j] = coeff [c] (i - j) = (if i = j then c else 0). *)
(*  It is diagonal with constant diagonal c, so det S = c^n.        *)
(* ================================================================ *)

(* coeff of the constant polynomial [c] (c <> 0). *)
let coeff_const_poly (#t:Type) {| cr: commutative_ring t |} (c: t{not (c = (zero <: t))}) (k: int)
  : Lemma (coeff ([c] <: polynomial t) k == (if k = 0 then c else (zero <: t)))
  = ()

(* the constant Sylvester matrix entry. *)
let syl_const_entry (#t:Type) {| cr: commutative_ring t |} (c: t{not (c = (zero <: t))})
  (b: polynomial t) (n: nat{n >= 1}) (i j: fin (nat_add 0 n))
  : Lemma (sylvester_matrix 0 n ([c] <: polynomial t) b i j
         == (if (i <: nat) = (j <: nat) then c else (zero <: t)))
  = sylvester_p_block_lookup 0 n ([c] <: polynomial t) b i j   (* i < n = n_deg, p-block: coeff [c] (0+i-j) *)

(* the constant Sylvester matrix is lower-triangular. *)
let syl_const_lower_triangular (#t:Type) {| cr: commutative_ring t |} (c: t{not (c = (zero <: t))})
  (b: polynomial t) (n: nat{n >= 1})
  : Lemma (is_lower_triangular (sylvester_matrix 0 n ([c] <: polynomial t) b))
  = H.elim_equatable_laws t ();
    let s = sylvester_matrix 0 n ([c] <: polynomial t) b in
    let upper (i j: fin (nat_add 0 n)) : Lemma ((j <: nat) > (i <: nat) ==> s i j = (zero <: t)) =
      if (j <: nat) > (i <: nat) then begin
        syl_const_entry c b n i j;
        assert (s i j == (zero <: t))
      end else ()
    in
    Classical.forall_intro_2 upper

(* diagonal_product_from of the constant matrix = c^{n-k}. *)
let rec syl_const_diag_from (#t:Type) {| cr: commutative_ring t |} (c: t{not (c = (zero <: t))})
  (b: polynomial t) (n: nat{n >= 1}) (k: nat{k <= n})
  : Lemma (ensures diagonal_product_from (sylvester_matrix 0 n ([c] <: polynomial t) b) k
                 = cpow c ((n - k)))
          (decreases (n - k))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let s = sylvester_matrix 0 n ([c] <: polynomial t) b in
    if k >= n then begin
      (* diagonal_product_from s n = one = cpow c 0 *)
      assert (diagonal_product_from s k == (one <: t));
      assert (cpow c ((n - k)) == (one <: t));
      transitivity (diagonal_product_from s k) (one <: t) (cpow c ((n - k)))
    end else begin
      syl_const_diag_from c b n ((k ++ 1));   (* IH: tail = cpow c (n-k-1) *)
      syl_const_entry c b n (k <: fin (nat_add 0 n)) (k <: fin (nat_add 0 n));   (* s k k == c *)
      (* diagonal_product_from s k = s k k * tail = c * cpow c (n-k-1) = cpow c (n-k) *)
      assert (diagonal_product_from s k
              == s (k <: fin (nat_add 0 n)) (k <: fin (nat_add 0 n))
                 * diagonal_product_from s ((k ++ 1)));
      mul_congruence (s (k <: fin (nat_add 0 n)) (k <: fin (nat_add 0 n)))
                     (diagonal_product_from s ((k ++ 1)))
                     c (cpow c ((n - ((k ++ 1)))));
      (* c * cpow c (n-k-1) = cpow c (n-k)  (definitional: n-k = (n-k-1)+1) *)
      cpow_succ c ((n - ((k ++ 1))));
      symmetry (cpow c ((((n - ((k ++ 1)))) ++ 1)))
               (c * cpow c ((n - ((k ++ 1)))));
      transitivity (diagonal_product_from s k)
                   (s (k <: fin (nat_add 0 n)) (k <: fin (nat_add 0 n))
                    * diagonal_product_from s ((k ++ 1)))
                   (c * cpow c ((n - ((k ++ 1)))));
      transitivity (diagonal_product_from s k)
                   (c * cpow c ((n - ((k ++ 1)))))
                   (cpow c ((((n - ((k ++ 1)))) ++ 1)));
      assert (cpow c ((((n - ((k ++ 1)))) ++ 1))
              == cpow c ((n - k)));
      transitivity (diagonal_product_from s k)
                   (cpow c ((((n - ((k ++ 1)))) ++ 1)))
                   (cpow c ((n - k)))
    end

let resultant_const (#t:Type) {| f: field t |} (c: t{not (c = (zero <: t))}) (b: polynomial t) (n: nat{n >= 1})
  : Lemma (let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
           resultant 0 n ([c] <: polynomial t) b = cpow c n)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let s = sylvester_matrix 0 n ([c] <: polynomial t) b in
    syl_const_lower_triangular c b n;
    det_lower_triangular s;          (* det s = diagonal_product s *)
    syl_const_diag_from c b n 0;                    (* diagonal_product_from s 0 = cpow c n *)
    assert (diagonal_product s == diagonal_product_from s 0);
    transitivity (det s) (diagonal_product s) (cpow c n);
    resultant_unfold 0 n ([c] <: polynomial t) b;
    H.leibniz_then_eq (resultant 0 n ([c] <: polynomial t) b) (det s) (cpow c n)

(* ================================================================================ *)
(*  FOLDED-IN: Core.Polynomial.ResultantMul *)
(* ================================================================================ *)

(* ----------------------------------------------------------------- *)
(*  The combination coefficient vector.                              *)
(*    slot j < n   : coeff u (n-1-j)      (u laid out, reversed)      *)
(*    slot j >= n  : coeff v (m-1-(j-n))  (v laid out, reversed)      *)
(* ----------------------------------------------------------------- *)

let combo_vec (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (u v: polynomial t)
  : vector t ((m_deg ++ n_deg))
  = fun (j: fin ((m_deg ++ n_deg))) ->
      if (j <: nat) < n_deg
      then coeff u ((((n_deg - 1)) - (j <: nat)))
      else coeff v ((((m_deg - 1)) - (((j <: nat) - n_deg))))

(* vector_dot via a named pointwise function: mirrors
   Core.Polynomial.Resultant.vdot_zero_via_name but for an arbitrary value. *)
#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let vdot_via_name (#t:Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: vector t n) (f: fin n -> t) (value: t)
  : Lemma (requires f == pointwise_mul a b /\ fin_sum f = value)
          (ensures vector_dot a b = value)
  = assert (forall (k: fin n). f k == pointwise_mul a b k);
    fin_sum_eq_pointwise f (pointwise_mul a b);
    vector_dot_reveal a b
#pop-options

(* ----------------------------------------------------------------- *)
(*  The Sylvester action / linear-map bridge.                        *)
(*                                                                   *)
(*  row i of S^T (= column i of S) dotted with combo_vec u v gives   *)
(*  the (N-1-i)-th coefficient of  u*P + v*Q.                        *)
(*                                                                   *)
(*  Proof mirrors Core.Polynomial.Resultant.syl_null_vec_is_null, but    *)
(*  with the v-part entering with `+` (no negation), so the two      *)
(*  halves assemble to coeff(u*P) + coeff(v*Q) = coeff(u*P + v*Q).   *)
(* ----------------------------------------------------------------- *)

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"
let sylvester_action (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (p q u v: polynomial t)
  (i: fin ((m_deg ++ n_deg)))
  : Lemma
    (requires L.length u <= n_deg /\ L.length v <= m_deg)
    (ensures  vector_dot (row (transpose (sylvester_matrix m_deg n_deg p q)) i)
                         (combo_vec m_deg n_deg u v)
            = coeff ((u * p) + (v * q))
                    ((((((m_deg ++ n_deg)) - 1)) - (i <: nat))))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let size : pos = (m_deg ++ n_deg) in
    let st = transpose (sylvester_matrix m_deg n_deg p q) in
    let vv  = combo_vec m_deg n_deg u v in
    let kk : nat = (((size - 1)) - (i <: nat)) in
    let f_p (j: fin size) : t = if (j <: nat) < n_deg
                                then pointwise_mul (row st i) vv j else zero in
    let f_q (j: fin size) : t = if (j <: nat) >= n_deg
                                then pointwise_mul (row st i) vv j else zero in
    let decomp_pf (j: fin size)
      : Lemma (pointwise_mul (row st i) vv j = f_p j + f_q j) =
      if (j <: nat) < n_deg then (
        assert (f_p j == pointwise_mul (row st i) vv j);
        assert (f_q j == (zero <: t));
        H.x_plus_zero (pointwise_mul (row st i) vv j);
        symmetry (pointwise_mul (row st i) vv j) (pointwise_mul (row st i) vv j + zero)
      ) else (
        assert (f_p j == (zero <: t));
        assert (f_q j == pointwise_mul (row st i) vv j);
        H.zero_plus_x (pointwise_mul (row st i) vv j);
        symmetry (pointwise_mul (row st i) vv j) (zero + pointwise_mul (row st i) vv j)
      ) in
    let pw : (fin size -> t) = pointwise_mul (row st i) vv in
    fin_sum_add_ext f_p f_q pw decomp_pf;

    (* ========== P-half: fin_sum f_p = coeff(u*p, kk) ========== *)
    let g_fp (j:nat) : t = if j < n_deg then
        pointwise_mul (row st i) vv (j <: fin size)
      else (zero <: t) in
    fin_sum_eq_sum_range f_p g_fp;
    sum_range_split g_fp 0 n_deg size;
    sum_range_all_zero g_fp n_deg size
      (fun (k: nat{n_deg <= k /\ k < size}) -> reflexivity (zero <: t));

    add_congruence (sum_range g_fp 0 n_deg) (sum_range g_fp n_deg size)
                   (sum_range g_fp 0 n_deg) (zero <: t);
    H.x_plus_zero (sum_range g_fp 0 n_deg);

    transitivity (sum_range g_fp 0 size)
                 (sum_range g_fp 0 n_deg + sum_range g_fp n_deg size)
                 (sum_range g_fp 0 n_deg + (zero <: t));
    transitivity (sum_range g_fp 0 size)
                 (sum_range g_fp 0 n_deg + (zero <: t))
                 (sum_range g_fp 0 n_deg);
    transitivity (fin_sum f_p) (sum_range g_fp 0 size) (sum_range g_fp 0 n_deg);
    let g_up (r:nat) : t = coeff u r * coeff p ((kk - r)) in
    let h_rev (j: nat{j < n_deg})
      : Lemma (g_fp j = g_up ((((n_deg - 1)) - j)))
      = assert ((j <: nat) < n_deg);
        let j_f : fin size = (j <: fin size) in
        assert (g_fp j == pointwise_mul (row st i) vv j_f);
        H.mul_commutativity_cr
          (coeff p ((((m_deg ++ j)) - (i <: nat))))
          (coeff u ((((n_deg - 1)) - j)))
    in
    sum_range_reverse_named g_fp g_up n_deg h_rev;
    sum_range_split g_up 0 (L.length u) n_deg;
    sum_range_all_zero g_up (L.length u) n_deg
      (fun (r: nat{L.length u <= r /\ r < n_deg}) ->
        assert (coeff u r == (zero <: t));
        H.zero_mul_x (coeff p ((kk - r))));

    add_congruence (sum_range g_up 0 (L.length u)) (sum_range g_up (L.length u) n_deg)
                   (sum_range g_up 0 (L.length u)) (zero <: t);
    H.x_plus_zero (sum_range g_up 0 (L.length u));

    transitivity (sum_range g_up 0 n_deg)
                 (sum_range g_up 0 (L.length u) + sum_range g_up (L.length u) n_deg)
                 (sum_range g_up 0 (L.length u) + (zero <: t));
    transitivity (sum_range g_up 0 n_deg)
                 (sum_range g_up 0 (L.length u) + (zero <: t))
                 (sum_range g_up 0 (L.length u));
    coeff_poly_mul_named u p kk g_up
      (fun (r:nat) -> reflexivity (coeff u r * coeff p ((kk - r))));

    transitivity (fin_sum f_p) (sum_range g_fp 0 n_deg) (sum_range g_up 0 n_deg);
    transitivity (fin_sum f_p) (sum_range g_up 0 n_deg) (sum_range g_up 0 (L.length u));
    transitivity (fin_sum f_p) (sum_range g_up 0 (L.length u)) (coeff (u * p) kk);

    (* ========== Q-half: fin_sum f_q = coeff(v*q, kk) ========== *)
    let g_fq (j:nat) : t = if j >= n_deg && j < size
      then pointwise_mul (row st i) vv (j <: fin size)
      else (zero <: t) in
    fin_sum_eq_sum_range f_q g_fq;
    sum_range_split g_fq 0 n_deg size;
    sum_range_all_zero g_fq 0 n_deg
      (fun (k: nat{0 <= k /\ k < n_deg}) -> reflexivity (zero <: t));

    add_congruence (sum_range g_fq 0 n_deg) (sum_range g_fq n_deg size)
                   (zero <: t) (sum_range g_fq n_deg size);
    H.zero_plus_x (sum_range g_fq n_deg size);

    transitivity (sum_range g_fq 0 size)
                 (sum_range g_fq 0 n_deg + sum_range g_fq n_deg size)
                 ((zero <: t) + sum_range g_fq n_deg size);
    transitivity (sum_range g_fq 0 size)
                 ((zero <: t) + sum_range g_fq n_deg size)
                 (sum_range g_fq n_deg size);
    transitivity (fin_sum f_q) (sum_range g_fq 0 size) (sum_range g_fq n_deg size);
    let f_sh : nat -> t = fun (j:nat) -> g_fq ((j ++ n_deg)) in
    sum_range_shift g_fq n_deg 0 m_deg;

    transitivity (fin_sum f_q) (sum_range g_fq n_deg size) (sum_range f_sh 0 m_deg);
    let g_vq (r:nat) : t = coeff v r * coeff q ((kk - r)) in
    let g_rev (j:nat) : t = if m_deg > 0 && j < m_deg
      then g_vq ((((m_deg - 1)) - j))
      else (zero <: t) in
    sum_range_congruence f_sh g_rev 0 m_deg
      (fun (j: nat{0 <= j /\ j < m_deg}) ->
        let jj : fin size = ((j ++ n_deg) <: fin size) in
        assert (f_sh j == pointwise_mul (row st i) vv jj);
        H.mul_commutativity_cr
          (coeff q ((((j ++ n_deg)) - (i <: nat))))
          (coeff v ((((m_deg - 1)) - j)))
      );
    transitivity (fin_sum f_q) (sum_range f_sh 0 m_deg) (sum_range g_rev 0 m_deg);
    sum_range_reverse_named g_rev g_vq m_deg
      (fun (j: nat{j < m_deg}) -> reflexivity (g_rev j));
    transitivity (fin_sum f_q) (sum_range g_rev 0 m_deg) (sum_range g_vq 0 m_deg);
    sum_range_split g_vq 0 (L.length v) m_deg;
    sum_range_all_zero g_vq (L.length v) m_deg
      (fun (r: nat{L.length v <= r /\ r < m_deg}) ->
        assert (coeff v r == (zero <: t));
        H.zero_mul_x (coeff q ((kk - r))));

    add_congruence (sum_range g_vq 0 (L.length v)) (sum_range g_vq (L.length v) m_deg)
                   (sum_range g_vq 0 (L.length v)) (zero <: t);
    H.x_plus_zero (sum_range g_vq 0 (L.length v));

    transitivity (sum_range g_vq 0 m_deg)
                 (sum_range g_vq 0 (L.length v) + sum_range g_vq (L.length v) m_deg)
                 (sum_range g_vq 0 (L.length v) + (zero <: t));
    transitivity (sum_range g_vq 0 m_deg)
                 (sum_range g_vq 0 (L.length v) + (zero <: t))
                 (sum_range g_vq 0 (L.length v));
    transitivity (fin_sum f_q) (sum_range g_vq 0 m_deg) (sum_range g_vq 0 (L.length v));
    coeff_poly_mul_named v q kk g_vq
      (fun (r:nat) -> reflexivity (coeff v r * coeff q ((kk - r))));

    transitivity (fin_sum f_q) (sum_range g_vq 0 (L.length v)) (coeff (v * q) kk);

    (* ===== assemble: fin_sum pw = coeff(u*p) + coeff(v*q) = coeff(u*p + v*q) ===== *)
    add_congruence (fin_sum f_p) (fin_sum f_q)
                   (coeff (u * p) kk) (coeff (v * q) kk);
    (* fin_sum pw = fin_sum f_p + fin_sum f_q = coeff(u*p) + coeff(v*q) *)
    transitivity (fin_sum pw) (fin_sum f_p + fin_sum f_q)
                 (coeff (u * p) kk + coeff (v * q) kk);
    vdot_via_name #t #cr #size (row st i) vv pw
                  (coeff (u * p) kk + coeff (v * q) kk);
    poly_add_coeff (u * p) (v * q) kk;
    symmetry (coeff ((u * p) + (v * q)) kk)
             (coeff (u * p) kk + coeff (v * q) kk);
    transitivity (vector_dot (row st i) vv)
                 (coeff (u * p) kk + coeff (v * q) kk)
                 (coeff ((u * p) + (v * q)) kk)
#pop-options

(* ================================================================================ *)
(*  FOLDED-IN: Core.Polynomial.ResultantPeel *)
(* ================================================================================ *)

(* small ring rearrangement:  x*v + w = w + x*v  *)
let comm_helper (#t:Type) {| cr: commutative_ring t |} (x v w: t)
  : Lemma (x * v + w = w + x * v)
  = assert (x * v + w = w + x * v) by canon_ring ()

(* ================================================================ *)
(*  Coefficient of  (x - a) * A.                                     *)
(*    coeff ((x-a)*A) k = coeff A (k-1) - a * coeff A k              *)
(*  (k=0: coeff A (-1) = 0, so it is just  - a * coeff A 0).         *)
(* ================================================================ *)

let coeff_linear_mul (#t:Type) {| f: field t |} (a: t) (bigA: polynomial t) (k: nat)
  : Lemma (coeff ((poly_linear a) * bigA) k
         = coeff bigA ((k - 1)) + (- a) * coeff bigA k)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    let pl = poly_linear a in
    assert (L.length pl == 2);
    let g (i:nat) : t = coeff pl i * coeff bigA ((k - i)) in
    coeff_poly_mul_named pl bigA k g (fun (i:nat) -> reflexivity (g i));
    (* sum_range g 0 2 = g 0 + g 1 *)
    sum_range_unfold_left g 0 2;
    sum_range_unfold_left g 1 2;
    sum_range_empty g 2 2;
    H.x_plus_zero (g 1);
    add_congruence (g 1) (sum_range g 2 2) (g 1) (zero <: t);
    transitivity (sum_range g 1 2) (g 1 + sum_range g 2 2) (g 1 + (zero <: t));
    transitivity (sum_range g 1 2) (g 1 + (zero <: t)) (g 1);
    add_congruence (g 0) (sum_range g 1 2) (g 0) (g 1);
    transitivity (sum_range g 0 2) (g 0 + sum_range g 1 2) (g 0 + g 1);
    (* g 0 = coeff pl 0 * coeff A k = (neg a) * coeff A k *)
    assert (coeff pl 0 == ((- a) <: t));

    mul_congruence (coeff pl 0) (coeff bigA k) (- a) (coeff bigA k);
    assert (g 0 == coeff pl 0 * coeff bigA ((k - 0)));
    assert ((k - 0) == k);
    transitivity (g 0) (coeff pl 0 * coeff bigA k) ((- a) * coeff bigA k);
    (* g 1 = coeff pl 1 * coeff A (k-1) = one * coeff A (k-1) = coeff A (k-1) *)
    assert (coeff pl 1 == (one <: t));

    mul_congruence (coeff pl 1) (coeff bigA ((k - 1)))
                   (one <: t) (coeff bigA ((k - 1)));
    H.one_mul_x (coeff bigA ((k - 1)));
    transitivity (g 1) (coeff pl 1 * coeff bigA ((k - 1)))
                 ((one <: t) * coeff bigA ((k - 1)));
    transitivity (g 1) ((one <: t) * coeff bigA ((k - 1)))
                 (coeff bigA ((k - 1)));
    (* g 0 + g 1 = (neg a)*coeff A k + coeff A (k-1) = coeff A (k-1) + (neg a)*coeff A k *)
    add_congruence (g 0) (g 1) ((- a) * coeff bigA k) (coeff bigA ((k - 1)));
    transitivity (sum_range g 0 2) (g 0 + g 1)
                 ((- a) * coeff bigA k + coeff bigA ((k - 1)));
    comm_helper (- a) (coeff bigA k) (coeff bigA ((k - 1)));
    transitivity (sum_range g 0 2)
                 ((- a) * coeff bigA k + coeff bigA ((k - 1)))
                 (coeff bigA ((k - 1)) + (- a) * coeff bigA k);

    transitivity (coeff (pl * bigA) k) (sum_range g 0 2)
                 (coeff bigA ((k - 1)) + (- a) * coeff bigA k)

(* ================================================================ *)
(*  block_diag_corner1 S  =  [ S  0 ]                                *)
(*                           [ 0  1 ]   (size N+1; S is the NxN block) *)
(*  det (block_diag_corner1 S) = det S  (Laplace along the last row). *)
(* ================================================================ *)

let block_diag_corner1 (#t:Type) {| cr: commutative_ring t |} (#bigN: pos)
  (s: square_matrix t bigN)
  : square_matrix t ((bigN ++ 1))
  = fun (i j: fin ((bigN ++ 1))) ->
      if (i <: nat) < bigN && (j <: nat) < bigN
      then s (i <: fin bigN) (j <: fin bigN)
      else if (i <: nat) = bigN && (j <: nat) = bigN then (one <: t)
      else (zero <: t)

(* the (N,N) minor of block_diag_corner1 S is exactly S. *)
let minor_corner_is_block (#t:Type) {| cr: commutative_ring t |} (#bigN: pos)
  (s: square_matrix t bigN) (a b: fin bigN)
  : Lemma (minor (block_diag_corner1 s)
                 (bigN <: fin ((bigN ++ 1))) (bigN <: fin ((bigN ++ 1)))
                 a b
         == s a b)
  = ()   (* minor[a][b] = C (skip N a)(skip N b) = C a b = s a b  (a,b < N) *)

(* off-corner entries of the last row vanish ==> their cofactors vanish. *)
let block_corner_cofactor_off (#t:Type) {| cr: commutative_ring t |} (#bigN: pos)
  (s: square_matrix t bigN) (k: fin ((bigN ++ 1)))
  : Lemma (requires (k <: nat) < bigN)
          (ensures cofactor_term (block_diag_corner1 s)
                                 (bigN <: fin ((bigN ++ 1))) k = (zero <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let n : pos = (bigN ++ 1) in
    let c = block_diag_corner1 s in
    let nn : fin n = (bigN <: fin n) in
    let mp = minus_one_pow #t #cr (((nn <: nat) ++ (k <: nat))) in
    let dm = det (minor c nn k) in
    assert (c nn k == (zero <: t));                  (* i=N, j=k<N => zero *)

    mul_congruence mp (c nn k) mp (zero <: t);
    H.x_mul_zero mp;
    transitivity (mp * c nn k) (mp * (zero <: t)) (zero <: t);

    mul_congruence (mp * c nn k) dm (zero <: t) dm;
    H.zero_mul_x dm;
    transitivity ((mp * c nn k) * dm) ((zero <: t) * dm) (zero <: t)

(* Generic single-index collapse over a real #n parameter (anchors fin_sum's
   implicit, mirroring the determinant collapse lemmas). *)
let fin_sum_collapse_at (#t:Type) {| cr: commutative_ring t |} (#n: pos)
  (f: fin n -> t) (i0: fin n)
  (hoff: (k: fin n{(k <: nat) <> (i0 <: nat)}) -> Lemma (f k = (zero <: t)))
  : Lemma (fin_sum #t #(acg_of_r t #cr.cr_r) #n f = f i0)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let agree (k: fin n)
      : Lemma (f k = pointwise_mul (fin_kronecker_delta i0) f k)
      = if (k <: nat) = (i0 <: nat) then
          H.one_mul_x (f k)                            (* delta = one *)
        else begin
          hoff k;
          H.zero_mul_x (f k)                            (* delta = zero *)
        end
    in
    fin_sum_congruence f (pointwise_mul (fin_kronecker_delta i0) f) agree;
    fin_sum_kronecker i0 f;
    transitivity (fin_sum f)
                 (fin_sum (pointwise_mul (fin_kronecker_delta i0) f))
                 (f i0)

let block_diag_corner1_det (#t:Type) {| cr: commutative_ring t |} (#bigN: pos)
  (s: square_matrix t bigN)
  : Lemma (det (block_diag_corner1 s) = det s)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let c = block_diag_corner1 s in
    let nn : fin ((bigN ++ 1)) = (bigN <: fin ((bigN ++ 1))) in
    det_laplace_row c nn;                             (* det c = fin_sum (cofactor_term c N) *)
    (* fin_sum (cofactor_term c N) = cofactor_term c N N: collapse along last row, inlined
       so the fin_sum term is literally `cofactor_term c nn` (matching det_laplace_row). *)
    let hoff (k: fin ((bigN ++ 1)){(k <: nat) <> (nn <: nat)})
      : Lemma (cofactor_term c nn k = (zero <: t))
      = assert ((k <: nat) < bigN);
        block_corner_cofactor_off s k
    in
    fin_sum_collapse_at (cofactor_term c nn) nn hoff;
    (* cofactor_term c N N = minus_one_pow (2N) * c N N * det (minor c N N)
                           = one * one * det s = det s *)
    let mp = minus_one_pow #t #cr (((nn <: nat) ++ (nn <: nat))) in
    assert (Prims.op_Modulus (((nn <: nat) ++ (nn <: nat))) 2 = 0);
    assert (mp == (one <: t));
    assert (c nn nn == (one <: t));                   (* corner entry = one *)
    (* minor c N N = s pointwise *)
    let minor_eq (a b: fin bigN) : Lemma (minor c nn nn a b = s a b)
      = minor_corner_is_block s a b; reflexivity (s a b) in
    Classical.forall_intro_2 minor_eq;
    det_pointwise_eq (minor c nn nn) s;  (* det (minor c N N) = det s *)
    (* assemble: cofactor = (mp * c N N) * det(minor) = (one*one)*det s = det s *)

    mul_congruence mp (c nn nn) (one <: t) (one <: t);
    H.one_mul_x (one <: t);
    transitivity (mp * c nn nn) ((one <: t) * (one <: t)) (one <: t);

    mul_congruence (mp * c nn nn) (det (minor c nn nn))
                   (one <: t) (det (minor c nn nn));
    H.one_mul_x (det (minor c nn nn));
    transitivity ((mp * c nn nn) * det (minor c nn nn))
                 ((one <: t) * det (minor c nn nn))
                 (det (minor c nn nn));
    (* det (minor c N N) = det s *)
    transitivity ((mp * c nn nn) * det (minor c nn nn))
                 (det (minor c nn nn))
                 (det s);
    (* cofactor_term c N N == (mp * c N N) * det(minor) *)
    transitivity (det c)
                 (fin_sum (cofactor_term c nn))
                 (cofactor_term c nn nn);
    transitivity (det c) (cofactor_term c nn nn)
                 ((mp * c nn nn) * det (minor c nn nn));
    transitivity (det c)
                 ((mp * c nn nn) * det (minor c nn nn))
                 (det s)

(* ================================================================ *)
(*  Piece #2:  det Mul' = poly_eval b a,  where                     *)
(*    Mul' = sylvester_matrix 1 N (x-a) b   (formal degree N >= deg b). *)
(*  Immediate from resultant_linear_formal (Task 1).                 *)
(* ================================================================ *)

let det_mul_block_is_eval (#t:Type) {| f: field t |} (a: t) (b: polynomial t) (bigN: nat{bigN >= 1})
  : Lemma (requires deg b >= 0 /\ deg b <= bigN)
          (ensures (let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
                    det (sylvester_matrix 1 bigN (poly_linear a) b) = poly_eval b a))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    resultant_linear_formal a b bigN;                (* resultant 1 N (x-a) b = poly_eval b a *)
    resultant_unfold 1 bigN (poly_linear a) b (* resultant 1 N (x-a) b == det Mul' *)

(* ================================================================ *)
(*  Piece #3 (the crux): the matrix identity  C * Mul' = L * S'      *)
(*  where  L  is the unipotent bidiagonal "row-op" matrix that turns *)
(*  the q-rows of  S'  (single B-shifts) into the q-rows of  C*Mul'  *)
(*  (B-shift minus a * next-shift):                                  *)
(*                                                                   *)
(*    L[i][i]   = 1          (all i)                                  *)
(*    L[i][i+1] = -a         (n <= i < N, i.e. the inner q-block)     *)
(*    L[i][k]   = 0          otherwise.                              *)
(*                                                                   *)
(*  L is unipotent upper-triangular, so det L = 1; hence by det_mul  *)
(*    det C * det Mul' = det (C*Mul') = det (L*S') = det S'.          *)
(* ================================================================ *)

(* size synonym N+1 where N = m+n. *)
let peel_L (#t:Type) {| cr: commutative_ring t |} (a: t) (m n: nat{n >= 1})
  : square_matrix t ((((m ++ n)) ++ 1))
  = let bigNp1 = (((m ++ n)) ++ 1) in
    fun (i k: fin bigNp1) ->
      if (i <: nat) = (k <: nat) then (one <: t)
      else if (i <: nat) >= n && (i <: nat) < (m ++ n)
              && (k <: nat) = ((i <: nat) ++ 1) then ((- a) <: t)
      else (zero <: t)

let peel_L_upper_triangular (#t:Type) {| cr: commutative_ring t |} (a: t) (m n: nat{n >= 1})
  : Lemma (is_upper_triangular (peel_L a m n))
  = H.elim_equatable_laws t ()    (* L[i][k] = 0 when i > k (diag or i+1 superdiag only) *)

let peel_L_diag_one (#t:Type) {| cr: commutative_ring t |} (a: t) (m n: nat{n >= 1})
  (i: fin ((((m ++ n)) ++ 1)))
  : Lemma (peel_L a m n i i = (one <: t))
  = H.elim_equatable_laws t ()

let det_peel_L (#t:Type) {| cr: commutative_ring t |} (a: t) (m n: nat{n >= 1})
  : Lemma (det (peel_L a m n) = (one <: t))
  = peel_L_upper_triangular a m n;
    det_unipotent_upper_triangular (peel_L a m n) (peel_L_diag_one a m n)

(* ---------------------------------------------------------------- *)
(*  Generic LEFT two-term row collapse.                              *)
(*    If row i of `lmat` is  v0 at column i0  and  v1 at column i1   *)
(*    (i0 <> i1) and 0 elsewhere, then                               *)
(*       (lmat * rmat)[i][j] = v0 * rmat[i0][j] + v1 * rmat[i1][j].  *)
(*  (Mirrors bidiag_row_times_shear but as a forward value, generic  *)
(*  over a real #nn parameter so fin_sum implicits compose.)         *)
(* ---------------------------------------------------------------- *)
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let left_two_term_row (#t:Type) {| cr: commutative_ring t |} (#nn: pos)
  (lmat rmat: square_matrix t nn) (i j: fin nn) (i0 i1: fin nn) (v0 v1: t)
  : Lemma (requires (i0 <: nat) <> (i1 <: nat) /\
                    lmat i i0 = v0 /\ lmat i i1 = v1 /\
                    (forall (k: fin nn). (k <: nat) <> (i0 <: nat) /\ (k <: nat) <> (i1 <: nat)
                                         ==> lmat i k = (zero <: t)))
          (ensures matrix_mul lmat rmat i j
                 = v0 * rmat i0 j + v1 * rmat i1 j)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let c0 : t = v0 * rmat i0 j in
    let c1 : t = v1 * rmat i1 j in
    let decomp (k: fin nn)
      : Lemma (pointwise_mul (row lmat i) (col rmat j) k
             = pointwise_add (pointwise_mul (fin_kronecker_delta i0) (const c0))
                             (pointwise_mul (fin_kronecker_delta i1) (const c1)) k) =
      pointwise_mul_unfold (row lmat i) (col rmat j) k;
      pointwise_add_unfold (pointwise_mul (fin_kronecker_delta i0) (const c0))
                           (pointwise_mul (fin_kronecker_delta i1) (const c1)) k;
      pointwise_mul_unfold (fin_kronecker_delta i0) (const c0) k;
      pointwise_mul_unfold (fin_kronecker_delta i1) (const c1) k;
      const_unfold c0 k;
      const_unfold c1 k;
      fin_kronecker_delta_unfold #t i0 k;
      fin_kronecker_delta_unfold #t i1 k;
      let lhs = (row lmat i) k * (col rmat j) k in
      let rhs = (fin_kronecker_delta i0 k) * c0 + (fin_kronecker_delta i1 k) * c1 in
      if (k <: nat) = (i0 <: nat) then begin
        kronecker_delta_eq #t (i0 <: nat) (k <: nat);
        kronecker_delta_neq #t (i1 <: nat) (k <: nat);
        assert ((row lmat i) k == lmat i i0);
        assert ((col rmat j) k == rmat i0 j);

        mul_congruence (lmat i i0) (col rmat j k) v0 (col rmat j k);  (* lhs = v0 * rmat i0 j = c0 *)
        H.one_mul_x c0;
        H.zero_mul_x c1;
        add_congruence (fin_kronecker_delta i0 k * c0) (fin_kronecker_delta i1 k * c1) c0 (zero <: t);
        H.x_plus_zero c0;
        transitivity rhs (c0 + (zero <: t)) c0;
        transitivity lhs (v0 * col rmat j k) c0;   (* lhs == lmat i i0 * col = v0*rmat i0 j = c0 *)

        transitivity rhs c0 lhs;
        symmetry rhs lhs
      end else if (k <: nat) = (i1 <: nat) then begin
        kronecker_delta_neq #t (i0 <: nat) (k <: nat);
        kronecker_delta_eq #t (i1 <: nat) (k <: nat);
        assert ((row lmat i) k == lmat i i1);
        assert ((col rmat j) k == rmat i1 j);

        mul_congruence (lmat i i1) (col rmat j k) v1 (col rmat j k);
        H.zero_mul_x c0;
        H.one_mul_x c1;
        add_congruence (fin_kronecker_delta i0 k * c0) (fin_kronecker_delta i1 k * c1) (zero <: t) c1;
        H.zero_plus_x c1;
        transitivity rhs ((zero <: t) + c1) c1;
        transitivity lhs (v1 * col rmat j k) c1;

        transitivity rhs c1 lhs;
        symmetry rhs lhs
      end else begin
        kronecker_delta_neq #t (i0 <: nat) (k <: nat);
        kronecker_delta_neq #t (i1 <: nat) (k <: nat);
        assert ((row lmat i) k == lmat i k);
        assert (lmat i k = (zero <: t));
        mul_congruence (lmat i k) (col rmat j k) (zero <: t) (col rmat j k);
        H.zero_mul_x (col rmat j k);
        transitivity lhs ((zero <: t) * col rmat j k) (zero <: t);
        H.zero_mul_x c0;
        H.zero_mul_x c1;
        add_congruence (fin_kronecker_delta i0 k * c0) (fin_kronecker_delta i1 k * c1) (zero <: t) (zero <: t);
        H.x_plus_zero (zero <: t);
        transitivity rhs ((zero <: t) + (zero <: t)) (zero <: t);

        transitivity rhs (zero <: t) lhs;
        symmetry rhs lhs
      end
    in
    fin_sum_congruence (pointwise_mul (row lmat i) (col rmat j))
                       (pointwise_add (pointwise_mul (fin_kronecker_delta i0) (const c0))
                                      (pointwise_mul (fin_kronecker_delta i1) (const c1)))
                       decomp;
    fin_sum_add (pointwise_mul (fin_kronecker_delta i0) (const c0))
                (pointwise_mul (fin_kronecker_delta i1) (const c1));
    fin_sum_kronecker i0 (const c0);
    fin_sum_kronecker i1 (const c1);
    const_unfold c0 i0;
    const_unfold c1 i1;
    H.eq_then_leibniz (fin_sum (pointwise_mul (fin_kronecker_delta i0) (const c0))) (const c0 i0) c0;
    H.eq_then_leibniz (fin_sum (pointwise_mul (fin_kronecker_delta i1) (const c1))) (const c1 i1) c1;
    add_congruence (fin_sum (pointwise_mul (fin_kronecker_delta i0) (const c0)))
                   (fin_sum (pointwise_mul (fin_kronecker_delta i1) (const c1))) c0 c1;
    transitivity (fin_sum (pointwise_add (pointwise_mul (fin_kronecker_delta i0) (const c0))
                                         (pointwise_mul (fin_kronecker_delta i1) (const c1))))
                 (fin_sum (pointwise_mul (fin_kronecker_delta i0) (const c0))
                  + fin_sum (pointwise_mul (fin_kronecker_delta i1) (const c1)))
                 (c0 + c1);
    transitivity (fin_sum (pointwise_mul (row lmat i) (col rmat j)))
                 (fin_sum (pointwise_add (pointwise_mul (fin_kronecker_delta i0) (const c0))
                                         (pointwise_mul (fin_kronecker_delta i1) (const c1))))
                 (c0 + c1);
    matrix_mul_to_fin_sum lmat rmat i j;
    H.leibniz_then_eq (matrix_mul lmat rmat i j) (fin_sum (pointwise_mul (row lmat i) (col rmat j))) (c0 + c1)
#pop-options

(* Single-term (pure-diagonal-row) left collapse:  if row i of lmat is v0 at i0
   and 0 elsewhere, then (lmat*rmat)[i][j] = v0 * rmat[i0][j]. *)
let left_one_term_row (#t:Type) {| cr: commutative_ring t |} (#nn: pos{nn > 1})
  (lmat rmat: square_matrix t nn) (i j: fin nn) (i0: fin nn) (v0: t)
  : Lemma (requires lmat i i0 = v0 /\
                    (forall (k: fin nn). (k <: nat) <> (i0 <: nat) ==> lmat i k = (zero <: t)))
          (ensures matrix_mul lmat rmat i j = v0 * rmat i0 j)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    (* use the two-term collapse with v1 = zero at a witness i1 <> i0 *)
    let i1 : fin nn = if (i0 <: nat) = 0 then (1 <: fin nn) else (0 <: fin nn) in
    assert ((i0 <: nat) <> (i1 <: nat));
    assert ((i1 <: nat) <> (i0 <: nat) ==> lmat i i1 = (zero <: t));
    assert (lmat i i1 = (zero <: t));
    left_two_term_row lmat rmat i j i0 i1 v0 (zero <: t);
    (* v0 * rmat i0 j + zero * rmat i1 j = v0 * rmat i0 j *)
    H.zero_mul_x (rmat i1 j);

    add_congruence (v0 * rmat i0 j) ((zero <: t) * rmat i1 j) (v0 * rmat i0 j) (zero <: t);
    H.x_plus_zero (v0 * rmat i0 j);
    transitivity (v0 * rmat i0 j + (zero <: t) * rmat i1 j)
                 (v0 * rmat i0 j + (zero <: t)) (v0 * rmat i0 j);
    transitivity (matrix_mul lmat rmat i j)
                 (v0 * rmat i0 j + (zero <: t) * rmat i1 j) (v0 * rmat i0 j)

(* ---------------------------------------------------------------- *)
(*  Generic RIGHT three-term column collapse.                        *)
(*    If column j of rmat is  w0 at row k0, w1 at row k1, w2 at row   *)
(*    k2  (k0,k1,k2 pairwise distinct) and 0 elsewhere, then          *)
(*       (lmat*rmat)[i][j]                                            *)
(*         = lmat[i][k0]*w0 + (lmat[i][k1]*w1 + lmat[i][k2]*w2).       *)
(* ---------------------------------------------------------------- *)
#push-options "--z3rlimit 150 --fuel 1 --ifuel 1"
let right_three_term_col (#t:Type) {| cr: commutative_ring t |} (#nn: pos)
  (lmat rmat: square_matrix t nn) (i j: fin nn)
  (k0 k1 k2: fin nn) (w0 w1 w2: t)
  : Lemma (requires (k0 <: nat) <> (k1 <: nat) /\ (k0 <: nat) <> (k2 <: nat) /\ (k1 <: nat) <> (k2 <: nat) /\
                    rmat k0 j = w0 /\ rmat k1 j = w1 /\ rmat k2 j = w2 /\
                    (forall (k: fin nn). (k <: nat) <> (k0 <: nat) /\ (k <: nat) <> (k1 <: nat)
                                         /\ (k <: nat) <> (k2 <: nat) ==> rmat k j = (zero <: t)))
          (ensures matrix_mul lmat rmat i j
                 = lmat i k0 * w0 + (lmat i k1 * w1 + lmat i k2 * w2))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let d0 : t = lmat i k0 * w0 in
    let d1 : t = lmat i k1 * w1 in
    let d2 : t = lmat i k2 * w2 in
    let tgt : fin nn -> t =
      pointwise_add (pointwise_mul (fin_kronecker_delta k0) (const d0))
        (pointwise_add (pointwise_mul (fin_kronecker_delta k1) (const d1))
                       (pointwise_mul (fin_kronecker_delta k2) (const d2))) in
    let decomp (k: fin nn)
      : Lemma (pointwise_mul (row lmat i) (col rmat j) k = tgt k) =
      pointwise_mul_unfold (row lmat i) (col rmat j) k;
      pointwise_add_unfold (pointwise_mul (fin_kronecker_delta k0) (const d0))
        (pointwise_add (pointwise_mul (fin_kronecker_delta k1) (const d1))
                       (pointwise_mul (fin_kronecker_delta k2) (const d2))) k;
      pointwise_add_unfold (pointwise_mul (fin_kronecker_delta k1) (const d1))
                           (pointwise_mul (fin_kronecker_delta k2) (const d2)) k;
      pointwise_mul_unfold (fin_kronecker_delta k0) (const d0) k;
      pointwise_mul_unfold (fin_kronecker_delta k1) (const d1) k;
      pointwise_mul_unfold (fin_kronecker_delta k2) (const d2) k;
      const_unfold d0 k; const_unfold d1 k; const_unfold d2 k;
      fin_kronecker_delta_unfold #t k0 k;
      fin_kronecker_delta_unfold #t k1 k;
      fin_kronecker_delta_unfold #t k2 k;
      let lhs = (row lmat i) k * (col rmat j) k in
      let rhs = (fin_kronecker_delta k0 k) * d0
                + ((fin_kronecker_delta k1 k) * d1 + (fin_kronecker_delta k2 k) * d2) in
      if (k <: nat) = (k0 <: nat) then begin
        kronecker_delta_eq #t (k0 <: nat) (k <: nat);
        kronecker_delta_neq #t (k1 <: nat) (k <: nat);
        kronecker_delta_neq #t (k2 <: nat) (k <: nat);
        assert ((col rmat j) k == rmat k0 j);
        assert ((row lmat i) k == lmat i k0);

        mul_congruence (lmat i k0) (col rmat j k) (lmat i k0) w0;
        H.one_mul_x d0; H.zero_mul_x d1; H.zero_mul_x d2;
        add_congruence (fin_kronecker_delta k1 k * d1) (fin_kronecker_delta k2 k * d2) (zero <: t) (zero <: t);
        H.x_plus_zero (zero <: t);
        transitivity (fin_kronecker_delta k1 k * d1 + fin_kronecker_delta k2 k * d2)
                     ((zero <: t) + (zero <: t)) (zero <: t);
        add_congruence (fin_kronecker_delta k0 k * d0)
                       (fin_kronecker_delta k1 k * d1 + fin_kronecker_delta k2 k * d2)
                       d0 (zero <: t);
        H.x_plus_zero d0;
        transitivity rhs (d0 + (zero <: t)) d0;
        transitivity lhs (lmat i k0 * w0) d0;
        symmetry lhs d0; transitivity rhs d0 lhs; symmetry rhs lhs
      end else if (k <: nat) = (k1 <: nat) then begin
        kronecker_delta_neq #t (k0 <: nat) (k <: nat);
        kronecker_delta_eq #t (k1 <: nat) (k <: nat);
        kronecker_delta_neq #t (k2 <: nat) (k <: nat);
        assert ((col rmat j) k == rmat k1 j);
        assert ((row lmat i) k == lmat i k1);

        mul_congruence (lmat i k1) (col rmat j k) (lmat i k1) w1;
        H.zero_mul_x d0; H.one_mul_x d1; H.zero_mul_x d2;
        add_congruence (fin_kronecker_delta k1 k * d1) (fin_kronecker_delta k2 k * d2) d1 (zero <: t);
        H.x_plus_zero d1;
        transitivity (fin_kronecker_delta k1 k * d1 + fin_kronecker_delta k2 k * d2) (d1 + (zero <: t)) d1;
        add_congruence (fin_kronecker_delta k0 k * d0)
                       (fin_kronecker_delta k1 k * d1 + fin_kronecker_delta k2 k * d2)
                       (zero <: t) d1;
        H.zero_plus_x d1;
        transitivity rhs ((zero <: t) + d1) d1;
        transitivity lhs (lmat i k1 * w1) d1;
        symmetry lhs d1; transitivity rhs d1 lhs; symmetry rhs lhs
      end else if (k <: nat) = (k2 <: nat) then begin
        kronecker_delta_neq #t (k0 <: nat) (k <: nat);
        kronecker_delta_neq #t (k1 <: nat) (k <: nat);
        kronecker_delta_eq #t (k2 <: nat) (k <: nat);
        assert ((col rmat j) k == rmat k2 j);
        assert ((row lmat i) k == lmat i k2);

        mul_congruence (lmat i k2) (col rmat j k) (lmat i k2) w2;
        H.zero_mul_x d0; H.zero_mul_x d1; H.one_mul_x d2;
        add_congruence (fin_kronecker_delta k1 k * d1) (fin_kronecker_delta k2 k * d2) (zero <: t) d2;
        H.zero_plus_x d2;
        transitivity (fin_kronecker_delta k1 k * d1 + fin_kronecker_delta k2 k * d2) ((zero <: t) + d2) d2;
        add_congruence (fin_kronecker_delta k0 k * d0)
                       (fin_kronecker_delta k1 k * d1 + fin_kronecker_delta k2 k * d2)
                       (zero <: t) d2;
        H.zero_plus_x d2;
        transitivity rhs ((zero <: t) + d2) d2;
        transitivity lhs (lmat i k2 * w2) d2;
        symmetry lhs d2; transitivity rhs d2 lhs; symmetry rhs lhs
      end else begin
        kronecker_delta_neq #t (k0 <: nat) (k <: nat);
        kronecker_delta_neq #t (k1 <: nat) (k <: nat);
        kronecker_delta_neq #t (k2 <: nat) (k <: nat);
        assert ((col rmat j) k == rmat k j);
        assert (rmat k j = (zero <: t));

        mul_congruence (row lmat i k) (col rmat j k) (row lmat i k) (zero <: t);
        H.x_mul_zero (row lmat i k);
        transitivity lhs (row lmat i k * (zero <: t)) (zero <: t);
        H.zero_mul_x d0; H.zero_mul_x d1; H.zero_mul_x d2;
        add_congruence (fin_kronecker_delta k1 k * d1) (fin_kronecker_delta k2 k * d2) (zero <: t) (zero <: t);
        H.x_plus_zero (zero <: t);
        transitivity (fin_kronecker_delta k1 k * d1 + fin_kronecker_delta k2 k * d2)
                     ((zero <: t) + (zero <: t)) (zero <: t);
        add_congruence (fin_kronecker_delta k0 k * d0)
                       (fin_kronecker_delta k1 k * d1 + fin_kronecker_delta k2 k * d2)
                       (zero <: t) (zero <: t);
        H.x_plus_zero (zero <: t);
        transitivity rhs ((zero <: t) + (zero <: t)) (zero <: t);
        symmetry lhs (zero <: t); transitivity rhs (zero <: t) lhs; symmetry rhs lhs
      end
    in
    fin_sum_congruence (pointwise_mul (row lmat i) (col rmat j))
      (pointwise_add (pointwise_mul (fin_kronecker_delta k0) (const d0))
        (pointwise_add (pointwise_mul (fin_kronecker_delta k1) (const d1))
                       (pointwise_mul (fin_kronecker_delta k2) (const d2)))) decomp;
    fin_sum_add (pointwise_mul (fin_kronecker_delta k0) (const d0))
                (pointwise_add (pointwise_mul (fin_kronecker_delta k1) (const d1))
                               (pointwise_mul (fin_kronecker_delta k2) (const d2)));
    fin_sum_add (pointwise_mul (fin_kronecker_delta k1) (const d1))
                (pointwise_mul (fin_kronecker_delta k2) (const d2));
    fin_sum_kronecker k0 (const d0);
    fin_sum_kronecker k1 (const d1);
    fin_sum_kronecker k2 (const d2);
    const_unfold d0 k0; const_unfold d1 k1; const_unfold d2 k2;
    H.eq_then_leibniz (fin_sum (pointwise_mul (fin_kronecker_delta k0) (const d0))) (const d0 k0) d0;
    H.eq_then_leibniz (fin_sum (pointwise_mul (fin_kronecker_delta k1) (const d1))) (const d1 k1) d1;
    H.eq_then_leibniz (fin_sum (pointwise_mul (fin_kronecker_delta k2) (const d2))) (const d2 k2) d2;
    add_congruence (fin_sum (pointwise_mul (fin_kronecker_delta k1) (const d1)))
                   (fin_sum (pointwise_mul (fin_kronecker_delta k2) (const d2))) d1 d2;
    transitivity (fin_sum (pointwise_add (pointwise_mul (fin_kronecker_delta k1) (const d1))
                                         (pointwise_mul (fin_kronecker_delta k2) (const d2))))
                 (fin_sum (pointwise_mul (fin_kronecker_delta k1) (const d1))
                  + fin_sum (pointwise_mul (fin_kronecker_delta k2) (const d2)))
                 (d1 + d2);

    add_congruence (fin_sum (pointwise_mul (fin_kronecker_delta k0) (const d0)))
                   (fin_sum (pointwise_add (pointwise_mul (fin_kronecker_delta k1) (const d1))
                                           (pointwise_mul (fin_kronecker_delta k2) (const d2))))
                   d0 (d1 + d2);
    transitivity (fin_sum (pointwise_add (pointwise_mul (fin_kronecker_delta k0) (const d0))
                             (pointwise_add (pointwise_mul (fin_kronecker_delta k1) (const d1))
                                            (pointwise_mul (fin_kronecker_delta k2) (const d2)))))
                 (fin_sum (pointwise_mul (fin_kronecker_delta k0) (const d0))
                  + fin_sum (pointwise_add (pointwise_mul (fin_kronecker_delta k1) (const d1))
                                           (pointwise_mul (fin_kronecker_delta k2) (const d2))))
                 (d0 + (d1 + d2));
    transitivity (fin_sum (pointwise_mul (row lmat i) (col rmat j)))
                 (fin_sum (pointwise_add (pointwise_mul (fin_kronecker_delta k0) (const d0))
                             (pointwise_add (pointwise_mul (fin_kronecker_delta k1) (const d1))
                                            (pointwise_mul (fin_kronecker_delta k2) (const d2)))))
                 (d0 + (d1 + d2));
    matrix_mul_to_fin_sum lmat rmat i j;
    H.leibniz_then_eq (matrix_mul lmat rmat i j)
                      (fin_sum (pointwise_mul (row lmat i) (col rmat j))) (d0 + (d1 + d2))
#pop-options

(* ---------------------------------------------------------------- *)
(*  Generic RIGHT two-term column collapse (boundary columns).       *)
(*    If column j of rmat is  w0 at row k0, w1 at row k1             *)
(*    (k0 <> k1) and 0 elsewhere, then                               *)
(*       (lmat * rmat)[i][j] = lmat[i][k0]*w0 + lmat[i][k1]*w1.       *)
(* ---------------------------------------------------------------- *)
#push-options "--z3rlimit 120 --fuel 1 --ifuel 1"
let right_two_term_col (#t:Type) {| cr: commutative_ring t |} (#nn: pos)
  (lmat rmat: square_matrix t nn) (i j: fin nn)
  (k0 k1: fin nn) (w0 w1: t)
  : Lemma (requires (k0 <: nat) <> (k1 <: nat) /\
                    rmat k0 j = w0 /\ rmat k1 j = w1 /\
                    (forall (k: fin nn). (k <: nat) <> (k0 <: nat) /\ (k <: nat) <> (k1 <: nat)
                                         ==> rmat k j = (zero <: t)))
          (ensures matrix_mul lmat rmat i j
                 = lmat i k0 * w0 + lmat i k1 * w1)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let d0 : t = lmat i k0 * w0 in
    let d1 : t = lmat i k1 * w1 in
    let tgt : fin nn -> t =
      pointwise_add (pointwise_mul (fin_kronecker_delta k0) (const d0))
                    (pointwise_mul (fin_kronecker_delta k1) (const d1)) in
    let decomp (k: fin nn)
      : Lemma (pointwise_mul (row lmat i) (col rmat j) k = tgt k) =
      pointwise_mul_unfold (row lmat i) (col rmat j) k;
      pointwise_add_unfold (pointwise_mul (fin_kronecker_delta k0) (const d0))
                           (pointwise_mul (fin_kronecker_delta k1) (const d1)) k;
      pointwise_mul_unfold (fin_kronecker_delta k0) (const d0) k;
      pointwise_mul_unfold (fin_kronecker_delta k1) (const d1) k;
      const_unfold d0 k; const_unfold d1 k;
      fin_kronecker_delta_unfold #t k0 k;
      fin_kronecker_delta_unfold #t k1 k;
      let lhs = (row lmat i) k * (col rmat j) k in
      let rhs = (fin_kronecker_delta k0 k) * d0 + (fin_kronecker_delta k1 k) * d1 in
      if (k <: nat) = (k0 <: nat) then begin
        kronecker_delta_eq #t (k0 <: nat) (k <: nat);
        kronecker_delta_neq #t (k1 <: nat) (k <: nat);
        assert ((col rmat j) k == rmat k0 j);
        assert ((row lmat i) k == lmat i k0);

        mul_congruence (lmat i k0) (col rmat j k) (lmat i k0) w0;
        H.one_mul_x d0; H.zero_mul_x d1;
        add_congruence (fin_kronecker_delta k0 k * d0) (fin_kronecker_delta k1 k * d1) d0 (zero <: t);
        H.x_plus_zero d0;
        transitivity rhs (d0 + (zero <: t)) d0;
        transitivity lhs (lmat i k0 * w0) d0;
        symmetry lhs d0; transitivity rhs d0 lhs; symmetry rhs lhs
      end else if (k <: nat) = (k1 <: nat) then begin
        kronecker_delta_neq #t (k0 <: nat) (k <: nat);
        kronecker_delta_eq #t (k1 <: nat) (k <: nat);
        assert ((col rmat j) k == rmat k1 j);
        assert ((row lmat i) k == lmat i k1);

        mul_congruence (lmat i k1) (col rmat j k) (lmat i k1) w1;
        H.zero_mul_x d0; H.one_mul_x d1;
        add_congruence (fin_kronecker_delta k0 k * d0) (fin_kronecker_delta k1 k * d1) (zero <: t) d1;
        H.zero_plus_x d1;
        transitivity rhs ((zero <: t) + d1) d1;
        transitivity lhs (lmat i k1 * w1) d1;
        symmetry lhs d1; transitivity rhs d1 lhs; symmetry rhs lhs
      end else begin
        kronecker_delta_neq #t (k0 <: nat) (k <: nat);
        kronecker_delta_neq #t (k1 <: nat) (k <: nat);
        assert ((col rmat j) k == rmat k j);
        assert (rmat k j = (zero <: t));

        mul_congruence (row lmat i k) (col rmat j k) (row lmat i k) (zero <: t);
        H.x_mul_zero (row lmat i k);
        transitivity lhs (row lmat i k * (zero <: t)) (zero <: t);
        H.zero_mul_x d0; H.zero_mul_x d1;
        add_congruence (fin_kronecker_delta k0 k * d0) (fin_kronecker_delta k1 k * d1) (zero <: t) (zero <: t);
        H.x_plus_zero (zero <: t);
        transitivity rhs ((zero <: t) + (zero <: t)) (zero <: t);
        symmetry lhs (zero <: t); transitivity rhs (zero <: t) lhs; symmetry rhs lhs
      end
    in
    fin_sum_congruence (pointwise_mul (row lmat i) (col rmat j))
      (pointwise_add (pointwise_mul (fin_kronecker_delta k0) (const d0))
                     (pointwise_mul (fin_kronecker_delta k1) (const d1))) decomp;
    fin_sum_add (pointwise_mul (fin_kronecker_delta k0) (const d0))
                (pointwise_mul (fin_kronecker_delta k1) (const d1));
    fin_sum_kronecker k0 (const d0);
    fin_sum_kronecker k1 (const d1);
    const_unfold d0 k0; const_unfold d1 k1;
    H.eq_then_leibniz (fin_sum (pointwise_mul (fin_kronecker_delta k0) (const d0))) (const d0 k0) d0;
    H.eq_then_leibniz (fin_sum (pointwise_mul (fin_kronecker_delta k1) (const d1))) (const d1 k1) d1;
    add_congruence (fin_sum (pointwise_mul (fin_kronecker_delta k0) (const d0)))
                   (fin_sum (pointwise_mul (fin_kronecker_delta k1) (const d1))) d0 d1;
    transitivity (fin_sum (pointwise_add (pointwise_mul (fin_kronecker_delta k0) (const d0))
                                         (pointwise_mul (fin_kronecker_delta k1) (const d1))))
                 (fin_sum (pointwise_mul (fin_kronecker_delta k0) (const d0))
                  + fin_sum (pointwise_mul (fin_kronecker_delta k1) (const d1)))
                 (d0 + d1);
    transitivity (fin_sum (pointwise_mul (row lmat i) (col rmat j)))
                 (fin_sum (pointwise_add (pointwise_mul (fin_kronecker_delta k0) (const d0))
                                         (pointwise_mul (fin_kronecker_delta k1) (const d1))))
                 (d0 + d1);
    matrix_mul_to_fin_sum lmat rmat i j;
    H.leibniz_then_eq (matrix_mul lmat rmat i j)
                      (fin_sum (pointwise_mul (row lmat i) (col rmat j))) (d0 + d1)
#pop-options

(* ================================================================ *)
(*  The three matrices of the peeling factorization, all coerced to  *)
(*  the SINGLE size  N+1 = (((m ++ n)) ++ 1) *)
(*  so that matrix_mul instances line up.  (The underlying Sylvester  *)
(*  matrices have sizes 1+N, (m+1)+n, m+n, which are propositionally  *)
(*  equal to N or N+1 but not syntactically; index coercions via the  *)
(*  SMT-discharged `fin` refinement bridge the gap.)                  *)
(* ================================================================ *)

unfold let size_peel (m n: nat) : pos = (((m ++ n)) ++ 1)

(* mat_Mul = sylvester_matrix 1 N (x-a) B  at size N+1. *)
let mat_mul_peel (#t:Type) {| f: field t |} (a: t) (b: polynomial t) (m n: nat{n >= 1})
  : square_matrix t (size_peel m n)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let bigN : nat = (m ++ n) in
    fun (i j: fin (size_peel m n)) ->
      sylvester_matrix 1 bigN (poly_linear a) b
        ((i <: nat) <: fin (nat_add 1 bigN)) ((j <: nat) <: fin (nat_add 1 bigN))

(* mat_S' = sylvester_matrix (m+1) n ((x-a)*A) B  at size N+1. *)
let mat_sprime_peel (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  : square_matrix t (size_peel m n)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    fun (i j: fin (size_peel m n)) ->
      sylvester_matrix #t #cr ((m ++ 1)) n
        ((poly_linear a) * bigA) b
        ((i <: nat) <: fin (nat_add ((m ++ 1)) n))
        ((j <: nat) <: fin (nat_add ((m ++ 1)) n))

(* mat_C = block_diag_corner1 (sylvester_matrix m n A B)  (size N+1 already). *)
let mat_c_peel (#t:Type) {| f: field t |} (bigA b: polynomial t) (m n: nat{n >= 1})
  : square_matrix t (size_peel m n)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    block_diag_corner1 (sylvester_matrix m n bigA b)

(* mat_L = peel_L a m n  (size N+1 already). *)
let mat_l_peel (#t:Type) {| f: field t |} (a: t) (m n: nat{n >= 1})
  : square_matrix t (size_peel m n)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    peel_L a m n

(* ================================================================ *)
(*  Column structure of mat_Mul (= sylvester_matrix 1 N (x-a) B).    *)
(*  bigN := m+n;  the (x-a)-rows are 0..bigN-1, the B-row is bigN.    *)
(*    Mul'[k][j] = one         when k = j  (k < bigN)                 *)
(*    Mul'[k][j] = neg a       when k = j-1 (k < bigN, j >= 1)        *)
(*    Mul'[bigN][j] = coeff B (bigN - j)                             *)
(*    Mul'[k][j] = 0           otherwise.                            *)
(* ================================================================ *)

let mat_mul_diag_one (#t:Type) {| f: field t |} (a: t) (b: polynomial t) (m n: nat{n >= 1})
  (k j: fin (size_peel m n))
  : Lemma (requires (k <: nat) < (m ++ n) /\ (k <: nat) = (j <: nat))
          (ensures mat_mul_peel a b m n k j = (one <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let bigN : nat = (m ++ n) in
    poly_linear_is_linear_shape a;
    syl_diag_one a (poly_linear a) b bigN
      ((k <: nat) <: fin (nat_add 1 bigN)) ;
    reflexivity (one <: t)

let mat_mul_super_neg (#t:Type) {| f: field t |} (a: t) (b: polynomial t) (m n: nat{n >= 1})
  (k j: fin (size_peel m n))
  : Lemma (requires (k <: nat) < (m ++ n) /\ (j <: nat) = ((k <: nat) ++ 1))
          (ensures mat_mul_peel a b m n k j = ((- a) <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let bigN : nat = (m ++ n) in
    poly_linear_is_linear_shape a;
    syl_super_neg_a a (poly_linear a) b bigN
      ((k <: nat) <: fin (nat_add 1 bigN)) ((j <: nat) <: fin (nat_add 1 bigN));
    reflexivity ((- a) <: t)

let mat_mul_lastrow (#t:Type) {| f: field t |} (a: t) (b: polynomial t) (m n: nat{n >= 1})
  (j: fin (size_peel m n))
  : Lemma (mat_mul_peel a b m n
             (((m ++ n) <: nat) <: fin (size_peel m n)) j
         = coeff b ((((m ++ n)) - (j <: nat))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let bigN : nat = (m ++ n) in
    syl_last_row (poly_linear a) b bigN
      ((j <: nat) <: fin (nat_add 1 bigN));
    reflexivity (coeff b ((bigN - (j <: nat))))

(* off-structure p-row entries vanish *)
let mat_mul_p_other_zero (#t:Type) {| f: field t |} (a: t) (b: polynomial t) (m n: nat{n >= 1})
  (k j: fin (size_peel m n))
  : Lemma (requires (k <: nat) < (m ++ n) /\
                    (k <: nat) <> (j <: nat) /\
                    (j <: nat) <> ((k <: nat) ++ 1))
          (ensures mat_mul_peel a b m n k j = (zero <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let bigN : nat = (m ++ n) in
    poly_linear_is_linear_shape a;
    syl_p_other_zero a (poly_linear a) b bigN
      ((k <: nat) <: fin (nat_add 1 bigN)) ((j <: nat) <: fin (nat_add 1 bigN));
    reflexivity (zero <: t)

(* ================================================================ *)
(*  Entries of mat_C = block_diag_corner1 (sylvester_matrix m n A B). *)
(*    inner block (k,l < bigN):  Sm[k][l]                            *)
(*       p-row k<n :  coeff A (m + k - l)                            *)
(*       q-row k>=n:  coeff B (k - l)                                *)
(*    corner (bigN,bigN): one ;   else (last row/col off corner): 0. *)
(* ================================================================ *)

let mat_c_inner_p (#t:Type) {| f: field t |} (bigA b: polynomial t) (m n: nat{n >= 1})
  (k l: fin (size_peel m n))
  : Lemma (requires (k <: nat) < n /\ (l <: nat) < (m ++ n))
          (ensures mat_c_peel bigA b m n k l
                 = coeff bigA ((((m ++ (k <: nat))) - (l <: nat))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let bigN : nat = (m ++ n) in
    (* mat_c_peel k l = Sm[k][l] since k,l < bigN *)
    sylvester_p_block_lookup m n bigA b
      ((k <: nat) <: fin (nat_add m n)) ((l <: nat) <: fin (nat_add m n));
    reflexivity (coeff bigA ((((m ++ (k <: nat))) - (l <: nat))))

let mat_c_inner_q (#t:Type) {| f: field t |} (bigA b: polynomial t) (m n: nat{n >= 1})
  (k l: fin (size_peel m n))
  : Lemma (requires (k <: nat) >= n /\ (k <: nat) < (m ++ n) /\
                    (l <: nat) < (m ++ n))
          (ensures mat_c_peel bigA b m n k l
                 = coeff b (((k <: nat) - (l <: nat))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let bigN : nat = (m ++ n) in
    sylvester_q_block_lookup m n bigA b
      ((k <: nat) <: fin (nat_add m n)) ((l <: nat) <: fin (nat_add m n));
    reflexivity (coeff b (((k <: nat) - (l <: nat))))

let mat_c_corner (#t:Type) {| f: field t |} (bigA b: polynomial t) (m n: nat{n >= 1})
  : Lemma (mat_c_peel bigA b m n
             (((m ++ n) <: nat) <: fin (size_peel m n))
             (((m ++ n) <: nat) <: fin (size_peel m n))
         = (one <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    reflexivity (one <: t)

(* last column off corner is zero: C[k][bigN] = 0 for k < bigN *)
let mat_c_lastcol_zero (#t:Type) {| f: field t |} (bigA b: polynomial t) (m n: nat{n >= 1})
  (k: fin (size_peel m n))
  : Lemma (requires (k <: nat) < (m ++ n))
          (ensures mat_c_peel bigA b m n k
                     (((m ++ n) <: nat) <: fin (size_peel m n)) = (zero <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    reflexivity (zero <: t)

(* last row off corner is zero: C[bigN][l] = 0 for l < bigN *)
let mat_c_lastrow_zero (#t:Type) {| f: field t |} (bigA b: polynomial t) (m n: nat{n >= 1})
  (l: fin (size_peel m n))
  : Lemma (requires (l <: nat) < (m ++ n))
          (ensures mat_c_peel bigA b m n
                     (((m ++ n) <: nat) <: fin (size_peel m n)) l = (zero <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    reflexivity (zero <: t)

(* ================================================================ *)
(*  Entries of mat_L = peel_L a m n.                                 *)
(*    L[i][i]   = 1   ;   L[i][i+1] = neg a  for n <= i < bigN  ;     *)
(*    else 0.                                                        *)
(* ================================================================ *)

let mat_l_diag (#t:Type) {| f: field t |} (a: t) (m n: nat{n >= 1})
  (i: fin (size_peel m n))
  : Lemma (mat_l_peel a m n i i = (one <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    peel_L_diag_one a m n i

let mat_l_super (#t:Type) {| f: field t |} (a: t) (m n: nat{n >= 1})
  (i k: fin (size_peel m n))
  : Lemma (requires (i <: nat) >= n /\ (i <: nat) < (m ++ n) /\
                    (k <: nat) = ((i <: nat) ++ 1))
          (ensures mat_l_peel a m n i k = ((- a) <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    reflexivity ((- a) <: t)

(* L row i has only the diagonal (when i < n or i = bigN) or diagonal+super. *)
let mat_l_off_diag_zero (#t:Type) {| f: field t |} (a: t) (m n: nat{n >= 1})
  (i k: fin (size_peel m n))
  : Lemma (requires (k <: nat) <> (i <: nat) /\
                    ~((i <: nat) >= n /\ (i <: nat) < (m ++ n)
                      /\ (k <: nat) = ((i <: nat) ++ 1)))
          (ensures mat_l_peel a m n i k = (zero <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    reflexivity (zero <: t)

(* ================================================================ *)
(*  Entries of mat_S' = sylvester_matrix (m+1) n ((x-a)*A) B.        *)
(*    p-row i<n :  coeff ((x-a)*A) ((m+1) + i - j)                   *)
(*    q-row i>=n:  coeff B (i - j)                                   *)
(* ================================================================ *)

let mat_sprime_p (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires (i <: nat) < n)
          (ensures mat_sprime_peel a bigA b m n i j
                 = coeff ((poly_linear a) * bigA)
                         ((((((m ++ 1)) ++ (i <: nat))) - (j <: nat))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    sylvester_p_block_lookup #t #cr ((m ++ 1)) n
      ((poly_linear a) * bigA) b
      ((i <: nat) <: fin (nat_add ((m ++ 1)) n))
      ((j <: nat) <: fin (nat_add ((m ++ 1)) n));
    reflexivity (coeff ((poly_linear a) * bigA)
                       ((((((m ++ 1)) ++ (i <: nat))) - (j <: nat))))

let mat_sprime_q (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires (i <: nat) >= n)
          (ensures mat_sprime_peel a bigA b m n i j
                 = coeff b (((i <: nat) - (j <: nat))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    sylvester_q_block_lookup #t #cr ((m ++ 1)) n
      ((poly_linear a) * bigA) b
      ((i <: nat) <: fin (nat_add ((m ++ 1)) n))
      ((j <: nat) <: fin (nat_add ((m ++ 1)) n));
    reflexivity (coeff b (((i <: nat) - (j <: nat))))

(* Generic Mul' column off-row vanishing: rows other than {j, j-1, bigN}
   are zero in column j. *)
let mat_mul_col_off (#t:Type) {| f: field t |} (a: t) (b: polynomial t) (m n: nat{n >= 1})
  (j k: fin (size_peel m n))
  : Lemma (requires (k <: nat) <> (j <: nat) /\
                    (k <: nat) <> ((j <: nat) - 1) /\
                    (k <: nat) <> (m ++ n))
          (ensures mat_mul_peel a b m n k j = (zero <: t))
  = let bigN : nat = (m ++ n) in
    if (k <: nat) < bigN then begin
      assert ((k <: nat) <> (j <: nat));
      assert ((j <: nat) <> ((k <: nat) ++ 1));
      mat_mul_p_other_zero a b m n k j
    end else
      H.elim_equatable_laws t ()

(* ================================================================ *)
(*  Pointwise identity, LAST ROW  i = bigN.                          *)
(*  C row bigN has a single nonzero entry (the corner = one), so      *)
(*  (C*Mul')[bigN][j] = one * Mul'[bigN][j] = coeff B (bigN - j).     *)
(*  L row bigN is pure diagonal, so (L*S')[bigN][j] = S'[bigN][j]     *)
(*  = coeff B (bigN - j).                                            *)
(* ================================================================ *)
#push-options "--z3rlimit 120 --fuel 1 --ifuel 1"
let peel_pointwise_last (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  (j: fin (size_peel m n))
  : Lemma (let i : fin (size_peel m n) = ((m ++ n) <: nat) <: fin (size_peel m n) in
           matrix_mul (mat_c_peel bigA b m n) (mat_mul_peel a b m n) i j
         = matrix_mul (mat_l_peel a m n) (mat_sprime_peel a bigA b m n) i j)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let bigN : nat = (m ++ n) in
    let sz : pos = size_peel m n in
    let i : fin sz = (bigN <: nat) <: fin sz in
    let cmat = mat_c_peel bigA b m n in
    let mulm  = mat_mul_peel a b m n in
    let lmat = mat_l_peel a m n in
    let sp   = mat_sprime_peel a bigA b m n in
    (* ----- LHS: collapse on C row i (single corner entry one at column bigN). ----- *)
    let corner : fin sz = (bigN <: nat) <: fin sz in
    mat_c_corner bigA b m n;                       (* C[bigN][bigN] = one *)
    let off_c (k: fin sz{(k <: nat) <> (corner <: nat)})
      : Lemma (cmat i k = (zero <: t))
      = mat_c_lastrow_zero bigA b m n k in          (* C[bigN][k]=0 for k<bigN *)
    Classical.forall_intro (Classical.move_requires off_c);
    left_one_term_row cmat mulm i j corner (one <: t);
    (* (C*Mul')[i][j] = one * Mul'[bigN][j] *)
    mat_mul_lastrow a b m n j;                      (* Mul'[bigN][j] = coeff b (bigN - j) *)
    H.one_mul_x (mulm corner j);
    (* one * mulm corner j = mulm corner j = coeff b (bigN - j) *)
    transitivity (matrix_mul cmat mulm i j) ((one <: t) * mulm corner j) (mulm corner j);
    transitivity (matrix_mul cmat mulm i j) (mulm corner j)
                 (coeff b ((bigN - (j <: nat))));
    (* ----- RHS: collapse on L row i (pure diagonal one at i). ----- *)
    mat_l_diag a m n i;                             (* L[i][i] = one *)
    let off_l (k: fin sz{(k <: nat) <> (i <: nat)})
      : Lemma (lmat i k = (zero <: t))
      = mat_l_off_diag_zero a m n i k in            (* i=bigN not in inner block, so off-diag 0 *)
    Classical.forall_intro (Classical.move_requires off_l);
    left_one_term_row lmat sp i j i (one <: t);
    (* (L*S')[i][j] = one * S'[i][j] *)
    mat_sprime_q a bigA b m n i j;                  (* S'[bigN][j] = coeff b (bigN - j) *)
    H.one_mul_x (sp i j);
    transitivity (matrix_mul lmat sp i j) ((one <: t) * sp i j) (sp i j);
    transitivity (matrix_mul lmat sp i j) (sp i j)
                 (coeff b ((bigN - (j <: nat))));
    (* both equal coeff b (bigN - j) *)

    transitivity (matrix_mul cmat mulm i j)
                 (coeff b ((bigN - (j <: nat))))
                 (matrix_mul lmat sp i j)
#pop-options

(* ---------------------------------------------------------------- *)
(*  RHS for an inner q-row  n <= i < bigN:                           *)
(*    (L*S')[i][j] = one * S'[i][j] + neg a * S'[i+1][j]             *)
(*                 = coeff B (i-j) + neg a * coeff B (i+1-j).        *)
(*  (L row i = { i : one, i+1 : neg a }.)                           *)
(* ---------------------------------------------------------------- *)
#push-options "--z3rlimit 150 --fuel 1 --ifuel 1"
let peel_rhs_qrow (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires (i <: nat) >= n /\ (i <: nat) < (m ++ n))
          (ensures (let lmat = mat_l_peel a m n in
                    let sp   = mat_sprime_peel a bigA b m n in
                    matrix_mul lmat sp i j
                  = coeff b (((i <: nat) - (j <: nat)))
                    + (- a) * coeff b (((((i <: nat) ++ 1)) - (j <: nat)))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let bigN : nat = (m ++ n) in
    let sz : pos = size_peel m n in
    let lmat = mat_l_peel a m n in
    let sp   = mat_sprime_peel a bigA b m n in
    let i1 : fin sz = (((i <: nat) ++ 1) <: nat) <: fin sz in
    mat_l_diag a m n i;
    mat_l_super a m n i i1;
    let off_l (k: fin sz{(k <: nat) <> (i <: nat) /\ (k <: nat) <> (i1 <: nat)})
      : Lemma (lmat i k = (zero <: t))
      = mat_l_off_diag_zero a m n i k in
    Classical.forall_intro (Classical.move_requires off_l);
    left_two_term_row lmat sp i j i i1 (one <: t) ((- a) <: t);
    mat_sprime_q a bigA b m n i j;
    mat_sprime_q a bigA b m n i1 j;
    H.one_mul_x (sp i j);

    mul_congruence ((- a) <: t) (sp i1 j) ((- a) <: t)
                   (coeff b (((((i <: nat) ++ 1)) - (j <: nat))));
    add_congruence ((one <: t) * sp i j) (((- a) <: t) * sp i1 j)
                   (coeff b (((i <: nat) - (j <: nat))))
                   (((- a) <: t) * coeff b (((((i <: nat) ++ 1)) - (j <: nat))));
    transitivity (matrix_mul lmat sp i j)
                 ((one <: t) * sp i j + ((- a) <: t) * sp i1 j)
                 (coeff b (((i <: nat) - (j <: nat)))
                  + ((- a) <: t) * coeff b (((((i <: nat) ++ 1)) - (j <: nat))))
#pop-options

(* ---------------------------------------------------------------- *)
(*  LHS for an inner q-row  n <= i < bigN:                           *)
(*    (C*Mul')[i][j] = coeff B (i-j) + neg a * coeff B (i+1-j).      *)
(*  C row i is a q-row of the inner Sylvester (C[i][l]=coeff B(i-l), *)
(*  l<bigN; C[i][bigN]=0).  Collapse column j of Mul'.               *)
(* ---------------------------------------------------------------- *)
#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"
let peel_lhs_qrow (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires (i <: nat) >= n /\ (i <: nat) < (m ++ n) /\
                    deg b >= 0 /\ deg b <= n)
          (ensures (let cmat = mat_c_peel bigA b m n in
                    let mulm  = mat_mul_peel a b m n in
                    matrix_mul cmat mulm i j
                  = coeff b (((i <: nat) - (j <: nat)))
                    + (- a) * coeff b (((((i <: nat) ++ 1)) - (j <: nat)))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let bigN : nat = (m ++ n) in
    let sz : pos = size_peel m n in
    let cmat = mat_c_peel bigA b m n in
    let mulm  = mat_mul_peel a b m n in
    let nN : fin sz = (bigN <: nat) <: fin sz in
    let jn : nat = j in
    (* target expression *)
    let tgt = coeff b (((i <: nat) - jn))
              + (- a) * coeff b (((((i <: nat) ++ 1)) - jn)) in
    if jn = 0 then begin
      (* column 0: rows {0:one, bigN:coeff b bigN}. *)
      let k0 : fin sz = (0 <: nat) <: fin sz in
      mat_mul_diag_one a b m n k0 k0;               (* Mul'[0][0] = one *)
      mat_mul_lastrow a b m n k0;                   (* Mul'[bigN][0] = coeff b bigN *)
      let off (k: fin sz{(k <: nat) <> (k0 <: nat) /\ (k <: nat) <> (nN <: nat)})
        : Lemma (mulm k k0 = (zero <: t))
        = mat_mul_col_off a b m n k0 k in
      Classical.forall_intro (Classical.move_requires off);
      right_two_term_col cmat mulm i k0 k0 nN (one <: t) (coeff b bigN);
      (* (C*Mul')[i][0] = C[i][0]*one + C[i][bigN]*coeff b bigN *)
      mat_c_inner_q bigA b m n i k0;                (* C[i][0] = coeff b (i-0) = coeff b i *)
      mat_c_lastcol_zero bigA b m n i;              (* C[i][bigN] = 0 *)
      H.x_mul_one (cmat i k0);                            (* C[i][0]*one = C[i][0] = coeff b i *)
      transitivity (cmat i k0 * (one <: t)) (cmat i k0) (coeff b (i <: nat));
      H.zero_mul_x (coeff b bigN);                        (* 0 * coeff b bigN = 0 *)
      mul_congruence (cmat i nN) (coeff b bigN) (zero <: t) (coeff b bigN);
      transitivity (cmat i nN * coeff b bigN) ((zero <: t) * coeff b bigN) (zero <: t);
      add_congruence (cmat i k0 * (one <: t)) (cmat i nN * coeff b bigN)
                     (coeff b (i <: nat)) (zero <: t);
      H.x_plus_zero (coeff b (i <: nat));
      transitivity (cmat i k0 * (one <: t) + cmat i nN * coeff b bigN)
                   (coeff b (i <: nat) + (zero <: t)) (coeff b (i <: nat));
      transitivity (matrix_mul cmat mulm i k0)
                   (cmat i k0 * (one <: t) + cmat i nN * coeff b bigN)
                   (coeff b (i <: nat));
      (* now coeff b i = coeff b (i-0) + neg a * coeff b (i+1-0) since coeff b (i+1)=0 *)
      coeff_above_degree b (((i <: nat) ++ 1));   (* coeff b (i+1) = 0, i+1 > n >= deg *)
      H.x_mul_zero (- a);                               (* neg a * 0 = 0 *)

      mul_congruence ((- a) <: t) (coeff b (((i <: nat) ++ 1))) ((- a) <: t) (zero <: t);
      transitivity (((- a) <: t) * coeff b (((i <: nat) ++ 1)))
                   (((- a) <: t) * (zero <: t)) (zero <: t);

      add_congruence (coeff b (i <: nat)) (((- a) <: t) * coeff b (((i <: nat) ++ 1)))
                     (coeff b (i <: nat)) (zero <: t);
      H.x_plus_zero (coeff b (i <: nat));
      transitivity tgt (coeff b (i <: nat) + (zero <: t)) (coeff b (i <: nat));

      transitivity (matrix_mul cmat mulm i j) (coeff b (i <: nat)) tgt
    end else if jn = bigN then begin
      (* column bigN: rows {bigN-1:neg a, bigN:coeff b 0}. *)
      let km1 : fin sz = ((bigN - 1) <: nat) <: fin sz in
      mat_mul_super_neg a b m n km1 j;              (* Mul'[bigN-1][bigN] = neg a (j = (bigN-1)+1) *)
      mat_mul_lastrow a b m n j;                    (* Mul'[bigN][bigN] = coeff b 0 *)
      let off (k: fin sz{(k <: nat) <> (km1 <: nat) /\ (k <: nat) <> (nN <: nat)})
        : Lemma (mulm k j = (zero <: t))
        = mat_mul_col_off a b m n j k in
      Classical.forall_intro (Classical.move_requires off);
      right_two_term_col cmat mulm i j km1 nN ((- a) <: t)
                         (coeff b ((bigN - (jn)))) ;
      (* (C*Mul')[i][bigN] = C[i][bigN-1]*neg a + C[i][bigN]*coeff b 0 *)
      mat_c_inner_q bigA b m n i km1;               (* C[i][bigN-1] = coeff b (i-(bigN-1)) *)
      mat_c_lastcol_zero bigA b m n i;              (* C[i][bigN] = 0 *)
      (* C[i][bigN-1]*neg a = neg a * coeff b (i-(bigN-1)) = neg a * coeff b (i+1-bigN) *)

      mul_congruence (cmat i km1) ((- a) <: t)
                     (coeff b (((i <: nat) - ((bigN - 1))))) ((- a) <: t);
      H.mul_commutativity_cr (coeff b (((i <: nat) - ((bigN - 1))))) ((- a) <: t);
      transitivity (cmat i km1 * ((- a) <: t))
                   (coeff b (((i <: nat) - ((bigN - 1)))) * ((- a) <: t))
                   (((- a) <: t) * coeff b (((i <: nat) - ((bigN - 1)))));
      (* C[i][bigN]*coeff b 0 = 0 *)
      H.zero_mul_x (coeff b ((bigN - jn)));
      mul_congruence (cmat i nN) (coeff b ((bigN - jn))) (zero <: t)
                     (coeff b ((bigN - jn)));
      transitivity (cmat i nN * coeff b ((bigN - jn)))
                   ((zero <: t) * coeff b ((bigN - jn))) (zero <: t);
      add_congruence (cmat i km1 * ((- a) <: t)) (cmat i nN * coeff b ((bigN - jn)))
                     (((- a) <: t) * coeff b (((i <: nat) - ((bigN - 1)))))
                     (zero <: t);
      H.x_plus_zero (((- a) <: t) * coeff b (((i <: nat) - ((bigN - 1)))));
      transitivity (cmat i km1 * ((- a) <: t) + cmat i nN * coeff b ((bigN - jn)))
                   (((- a) <: t) * coeff b (((i <: nat) - ((bigN - 1)))) + (zero <: t))
                   (((- a) <: t) * coeff b (((i <: nat) - ((bigN - 1)))));
      transitivity (matrix_mul cmat mulm i j)
                   (cmat i km1 * ((- a) <: t) + cmat i nN * coeff b ((bigN - jn)))
                   (((- a) <: t) * coeff b (((i <: nat) - ((bigN - 1)))));
      (* tgt = coeff b (i-bigN) + neg a*coeff b (i+1-bigN);  coeff b (i-bigN)=0 (i<bigN). *)
      assert ((i <: nat) - jn < 0);                       (* i < bigN = jn *)
      assert (coeff b (((i <: nat) - jn)) == (zero <: t));   (* negative index *)
      (* i+1-bigN = i - (bigN-1) *)
      assert (((((i <: nat) ++ 1)) - jn)
              == ((i <: nat) - ((bigN - 1))));

      H.zero_plus_x (((- a) <: t) * coeff b (((((i <: nat) ++ 1)) - jn)));
      symmetry (((- a) <: t) * coeff b (((((i <: nat) ++ 1)) - jn)))
               ((zero <: t) + ((- a) <: t) * coeff b (((((i <: nat) ++ 1)) - jn)));
      transitivity (matrix_mul cmat mulm i j)
                   (((- a) <: t) * coeff b (((i <: nat) - ((bigN - 1)))))
                   tgt
    end else begin
      (* interior 0 < j < bigN: three-term collapse, rows {j:one, j-1:neg a, bigN:coeff b (bigN-j)} *)
      let k0 : fin sz = (jn <: nat) <: fin sz in
      let k1 : fin sz = ((jn - 1) <: nat) <: fin sz in
      mat_mul_diag_one a b m n k0 j;                (* Mul'[j][j] = one *)
      mat_mul_super_neg a b m n k1 j;               (* Mul'[j-1][j] = neg a *)
      mat_mul_lastrow a b m n j;                    (* Mul'[bigN][j] = coeff b (bigN-j) *)
      let off (k: fin sz{(k <: nat) <> (k0 <: nat) /\ (k <: nat) <> (k1 <: nat) /\ (k <: nat) <> (nN <: nat)})
        : Lemma (mulm k j = (zero <: t))
        = mat_mul_col_off a b m n j k in
      Classical.forall_intro (Classical.move_requires off);
      right_three_term_col cmat mulm i j k0 k1 nN (one <: t) ((- a) <: t)
                           (coeff b ((bigN - jn)));
      (* (C*Mul')[i][j] = C[i][j]*one + (C[i][j-1]*neg a + C[i][bigN]*coeff b (bigN-j)) *)
      mat_c_inner_q bigA b m n i k0;                (* C[i][j] = coeff b (i-j) *)
      mat_c_inner_q bigA b m n i k1;                (* C[i][j-1] = coeff b (i-(j-1)) = coeff b (i-j+1) *)
      mat_c_lastcol_zero bigA b m n i;              (* C[i][bigN] = 0 *)
      (* d0 = C[i][j]*one = coeff b (i-j) *)
      H.x_mul_one (cmat i k0);
      transitivity (cmat i k0 * (one <: t)) (cmat i k0) (coeff b (((i <: nat) - jn)));
      (* d1 = C[i][j-1]*neg a = neg a * coeff b (i+1-j) *)

      mul_congruence (cmat i k1) ((- a) <: t)
                     (coeff b (((i <: nat) - ((jn - 1))))) ((- a) <: t);
      H.mul_commutativity_cr (coeff b (((i <: nat) - ((jn - 1))))) ((- a) <: t);
      assert (((i <: nat) - ((jn - 1)))
              == ((((i <: nat) ++ 1)) - jn));
      transitivity (cmat i k1 * ((- a) <: t))
                   (coeff b (((i <: nat) - ((jn - 1)))) * ((- a) <: t))
                   (((- a) <: t) * coeff b (((((i <: nat) ++ 1)) - jn)));
      (* d2 = C[i][bigN]*w2 = 0 *)
      H.zero_mul_x (coeff b ((bigN - jn)));
      mul_congruence (cmat i nN) (coeff b ((bigN - jn))) (zero <: t)
                     (coeff b ((bigN - jn)));
      transitivity (cmat i nN * coeff b ((bigN - jn)))
                   ((zero <: t) * coeff b ((bigN - jn))) (zero <: t);
      (* (d1 + d2) = neg a*coeff b (i+1-j) + 0 = neg a*coeff b (i+1-j) *)
      add_congruence (cmat i k1 * ((- a) <: t)) (cmat i nN * coeff b ((bigN - jn)))
                     (((- a) <: t) * coeff b (((((i <: nat) ++ 1)) - jn)))
                     (zero <: t);
      H.x_plus_zero (((- a) <: t) * coeff b (((((i <: nat) ++ 1)) - jn)));
      transitivity (cmat i k1 * ((- a) <: t) + cmat i nN * coeff b ((bigN - jn)))
                   (((- a) <: t) * coeff b (((((i <: nat) ++ 1)) - jn)) + (zero <: t))
                   (((- a) <: t) * coeff b (((((i <: nat) ++ 1)) - jn)));
      (* d0 + (d1+d2) = coeff b (i-j) + neg a*coeff b (i+1-j) = tgt *)
      add_congruence (cmat i k0 * (one <: t))
                     (cmat i k1 * ((- a) <: t) + cmat i nN * coeff b ((bigN - jn)))
                     (coeff b (((i <: nat) - jn)))
                     (((- a) <: t) * coeff b (((((i <: nat) ++ 1)) - jn)));
      transitivity (matrix_mul cmat mulm i j)
                   (cmat i k0 * (one <: t)
                    + (cmat i k1 * ((- a) <: t) + cmat i nN * coeff b ((bigN - jn))))
                   tgt
    end
#pop-options

(* q-row pointwise identity: combine LHS and RHS. *)
let peel_pointwise_qrow (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires (i <: nat) >= n /\ (i <: nat) < (m ++ n) /\
                    deg b >= 0 /\ deg b <= n)
          (ensures matrix_mul (mat_c_peel bigA b m n) (mat_mul_peel a b m n) i j
                 = matrix_mul (mat_l_peel a m n) (mat_sprime_peel a bigA b m n) i j)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cmat = mat_c_peel bigA b m n in
    let mulm  = mat_mul_peel a b m n in
    let lmat = mat_l_peel a m n in
    let sp   = mat_sprime_peel a bigA b m n in
    let rhsv = coeff b (((i <: nat) - (j <: nat)))
               + (- a) * coeff b (((((i <: nat) ++ 1)) - (j <: nat))) in
    peel_lhs_qrow a bigA b m n i j;                 (* (C*Mul')[i][j] = rhsv *)
    peel_rhs_qrow a bigA b m n i j;                 (* (L*S')[i][j]  = rhsv *)

    transitivity (matrix_mul cmat mulm i j) rhsv (matrix_mul lmat sp i j)

(* ---------------------------------------------------------------- *)
(*  RHS for a p-row  i < n:  L row i is pure diagonal, so            *)
(*    (L*S')[i][j] = one * S'[i][j] = coeff ((x-a)A) ((m+1)+i-j).    *)
(* ---------------------------------------------------------------- *)
#push-options "--z3rlimit 150 --fuel 1 --ifuel 1"
let peel_rhs_prow (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires (i <: nat) < n)
          (ensures (let lmat = mat_l_peel a m n in
                    let sp   = mat_sprime_peel a bigA b m n in
                    matrix_mul lmat sp i j
                  = coeff ((poly_linear a) * bigA)
                          ((((((m ++ 1)) ++ (i <: nat))) - (j <: nat)))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let sz : pos = size_peel m n in
    let lmat = mat_l_peel a m n in
    let sp   = mat_sprime_peel a bigA b m n in
    mat_l_diag a m n i;                             (* L[i][i] = one *)
    let off_l (k: fin sz{(k <: nat) <> (i <: nat)})
      : Lemma (lmat i k = (zero <: t))
      = mat_l_off_diag_zero a m n i k in            (* i<n: not in inner block, off-diag 0 *)
    Classical.forall_intro (Classical.move_requires off_l);
    left_one_term_row lmat sp i j i (one <: t);
    mat_sprime_p a bigA b m n i j;
    H.one_mul_x (sp i j);
    transitivity (matrix_mul lmat sp i j) ((one <: t) * sp i j) (sp i j);
    transitivity (matrix_mul lmat sp i j) (sp i j)
                 (coeff ((poly_linear a) * bigA)
                        ((((((m ++ 1)) ++ (i <: nat))) - (j <: nat))))
#pop-options

(* ---------------------------------------------------------------- *)
(*  Bridge:  coeff ((x-a)A) ((m+1)+i-j)                              *)
(*         = coeff A (m+i-j) + neg a * coeff A (m+i-j+1).            *)
(* ---------------------------------------------------------------- *)
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let peel_prow_bridge (#t:Type) {| f: field t |} (a: t) (bigA: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires (i <: nat) < n /\ L.length bigA <= (m ++ 1))
          (ensures (let idx_lo : int = (((m ++ (i <: nat))) - (j <: nat)) in
                    coeff ((poly_linear a) * bigA)
                          ((((((m ++ 1)) ++ (i <: nat))) - (j <: nat)))
                  = coeff bigA idx_lo + (- a) * coeff bigA ((idx_lo ++ 1))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let idx_hi : int = (((((m ++ 1)) ++ (i <: nat))) - (j <: nat)) in
    let idx_lo : int = (((m ++ (i <: nat))) - (j <: nat)) in
    let pl = poly_linear a in
    if idx_hi >= 0 then begin
      let k : nat = idx_hi in
      coeff_linear_mul a bigA k;
      assert ((k - 1) == idx_lo);
      assert ((k <: int) == (idx_lo ++ 1))
    end else begin
      assert (coeff (pl * bigA) idx_hi == (zero <: t));
      assert (idx_lo < 0);
      assert (coeff bigA idx_lo == (zero <: t));
      assert ((idx_lo ++ 1) == idx_hi);
      assert (coeff bigA ((idx_lo ++ 1)) == (zero <: t));
      H.x_mul_zero (- a);

      mul_congruence ((- a) <: t) (coeff bigA ((idx_lo ++ 1))) ((- a) <: t) (zero <: t);
      transitivity (((- a) <: t) * coeff bigA ((idx_lo ++ 1)))
                   (((- a) <: t) * (zero <: t)) (zero <: t);

      add_congruence (coeff bigA idx_lo) (((- a) <: t) * coeff bigA ((idx_lo ++ 1)))
                     (zero <: t) (zero <: t);
      H.x_plus_zero (zero <: t);
      transitivity (coeff bigA idx_lo + ((- a) <: t) * coeff bigA ((idx_lo ++ 1)))
                   ((zero <: t) + (zero <: t)) (zero <: t);

      transitivity (coeff (pl * bigA) idx_hi) (zero <: t)
                   (coeff bigA idx_lo + ((- a) <: t) * coeff bigA ((idx_lo ++ 1)))
    end
#pop-options

(* ---------------------------------------------------------------- *)
(*  LHS for a p-row  i < n:                                          *)
(*    (C*Mul')[i][j] = coeff A (m+i-j) + neg a * coeff A (m+i-j+1).  *)
(* ---------------------------------------------------------------- *)
#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"
let peel_lhs_prow (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires (i <: nat) < n /\ L.length bigA <= (m ++ 1))
          (ensures (let cmat = mat_c_peel bigA b m n in
                    let mulm  = mat_mul_peel a b m n in
                    let idx_lo : int = (((m ++ (i <: nat))) - (j <: nat)) in
                    matrix_mul cmat mulm i j
                  = coeff bigA idx_lo + (- a) * coeff bigA ((idx_lo ++ 1))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let bigN : nat = (m ++ n) in
    let sz : pos = size_peel m n in
    let cmat = mat_c_peel bigA b m n in
    let mulm  = mat_mul_peel a b m n in
    let nN : fin sz = (bigN <: nat) <: fin sz in
    let jn : nat = j in
    let idx_lo : int = (((m ++ (i <: nat))) - jn) in
    let tgt = coeff bigA idx_lo + (- a) * coeff bigA ((idx_lo ++ 1)) in
    if jn = 0 then begin
      let k0 : fin sz = (0 <: nat) <: fin sz in
      mat_mul_diag_one a b m n k0 k0;
      mat_mul_lastrow a b m n k0;
      let off (k: fin sz{(k <: nat) <> (k0 <: nat) /\ (k <: nat) <> (nN <: nat)})
        : Lemma (mulm k k0 = (zero <: t))
        = mat_mul_col_off a b m n k0 k in
      Classical.forall_intro (Classical.move_requires off);
      right_two_term_col cmat mulm i k0 k0 nN (one <: t) (coeff b bigN);
      mat_c_inner_p bigA b m n i k0;
      mat_c_lastcol_zero bigA b m n i;
      H.x_mul_one (cmat i k0);
      transitivity (cmat i k0 * (one <: t)) (cmat i k0) (coeff bigA idx_lo);
      H.zero_mul_x (coeff b bigN);
      mul_congruence (cmat i nN) (coeff b bigN) (zero <: t) (coeff b bigN);
      transitivity (cmat i nN * coeff b bigN) ((zero <: t) * coeff b bigN) (zero <: t);
      add_congruence (cmat i k0 * (one <: t)) (cmat i nN * coeff b bigN)
                     (coeff bigA idx_lo) (zero <: t);
      H.x_plus_zero (coeff bigA idx_lo);
      transitivity (cmat i k0 * (one <: t) + cmat i nN * coeff b bigN)
                   (coeff bigA idx_lo + (zero <: t)) (coeff bigA idx_lo);
      transitivity (matrix_mul cmat mulm i k0)
                   (cmat i k0 * (one <: t) + cmat i nN * coeff b bigN) (coeff bigA idx_lo);
      assert ((idx_lo ++ 1) == (((m ++ (i <: nat))) ++ 1));
      assert (coeff bigA ((idx_lo ++ 1)) == (zero <: t));
      H.x_mul_zero (- a);

      mul_congruence ((- a) <: t) (coeff bigA ((idx_lo ++ 1))) ((- a) <: t) (zero <: t);
      transitivity (((- a) <: t) * coeff bigA ((idx_lo ++ 1))) (((- a) <: t) * (zero <: t)) (zero <: t);

      add_congruence (coeff bigA idx_lo) (((- a) <: t) * coeff bigA ((idx_lo ++ 1)))
                     (coeff bigA idx_lo) (zero <: t);
      H.x_plus_zero (coeff bigA idx_lo);
      transitivity tgt (coeff bigA idx_lo + (zero <: t)) (coeff bigA idx_lo);

      transitivity (matrix_mul cmat mulm i j) (coeff bigA idx_lo) tgt
    end else if jn = bigN then begin
      let km1 : fin sz = ((bigN - 1) <: nat) <: fin sz in
      mat_mul_super_neg a b m n km1 j;
      mat_mul_lastrow a b m n j;
      let off (k: fin sz{(k <: nat) <> (km1 <: nat) /\ (k <: nat) <> (nN <: nat)})
        : Lemma (mulm k j = (zero <: t))
        = mat_mul_col_off a b m n j k in
      Classical.forall_intro (Classical.move_requires off);
      right_two_term_col cmat mulm i j km1 nN ((- a) <: t)
                         (coeff b ((bigN - jn)));
      mat_c_inner_p bigA b m n i km1;
      mat_c_lastcol_zero bigA b m n i;
      assert ((((m ++ (i <: nat))) - ((bigN - 1)))
              == (idx_lo ++ 1));

      mul_congruence (cmat i km1) ((- a) <: t) (coeff bigA ((idx_lo ++ 1))) ((- a) <: t);
      H.mul_commutativity_cr (coeff bigA ((idx_lo ++ 1))) ((- a) <: t);
      transitivity (cmat i km1 * ((- a) <: t))
                   (coeff bigA ((idx_lo ++ 1)) * ((- a) <: t))
                   (((- a) <: t) * coeff bigA ((idx_lo ++ 1)));
      H.zero_mul_x (coeff b ((bigN - jn)));
      mul_congruence (cmat i nN) (coeff b ((bigN - jn))) (zero <: t)
                     (coeff b ((bigN - jn)));
      transitivity (cmat i nN * coeff b ((bigN - jn)))
                   ((zero <: t) * coeff b ((bigN - jn))) (zero <: t);
      add_congruence (cmat i km1 * ((- a) <: t)) (cmat i nN * coeff b ((bigN - jn)))
                     (((- a) <: t) * coeff bigA ((idx_lo ++ 1))) (zero <: t);
      H.x_plus_zero (((- a) <: t) * coeff bigA ((idx_lo ++ 1)));
      transitivity (cmat i km1 * ((- a) <: t) + cmat i nN * coeff b ((bigN - jn)))
                   (((- a) <: t) * coeff bigA ((idx_lo ++ 1)) + (zero <: t))
                   (((- a) <: t) * coeff bigA ((idx_lo ++ 1)));
      transitivity (matrix_mul cmat mulm i j)
                   (cmat i km1 * ((- a) <: t) + cmat i nN * coeff b ((bigN - jn)))
                   (((- a) <: t) * coeff bigA ((idx_lo ++ 1)));
      assert (idx_lo == ((i <: nat) - n));
      assert (idx_lo < 0);
      assert (coeff bigA idx_lo == (zero <: t));

      H.zero_plus_x (((- a) <: t) * coeff bigA ((idx_lo ++ 1)));
      symmetry (((- a) <: t) * coeff bigA ((idx_lo ++ 1)))
               ((zero <: t) + ((- a) <: t) * coeff bigA ((idx_lo ++ 1)));
      transitivity (matrix_mul cmat mulm i j)
                   (((- a) <: t) * coeff bigA ((idx_lo ++ 1))) tgt
    end else begin
      let k0 : fin sz = (jn <: nat) <: fin sz in
      let k1 : fin sz = ((jn - 1) <: nat) <: fin sz in
      mat_mul_diag_one a b m n k0 j;
      mat_mul_super_neg a b m n k1 j;
      mat_mul_lastrow a b m n j;
      let off (k: fin sz{(k <: nat) <> (k0 <: nat) /\ (k <: nat) <> (k1 <: nat) /\ (k <: nat) <> (nN <: nat)})
        : Lemma (mulm k j = (zero <: t))
        = mat_mul_col_off a b m n j k in
      Classical.forall_intro (Classical.move_requires off);
      right_three_term_col cmat mulm i j k0 k1 nN (one <: t) ((- a) <: t)
                           (coeff b ((bigN - jn)));
      mat_c_inner_p bigA b m n i k0;
      mat_c_inner_p bigA b m n i k1;
      mat_c_lastcol_zero bigA b m n i;
      H.x_mul_one (cmat i k0);
      transitivity (cmat i k0 * (one <: t)) (cmat i k0) (coeff bigA idx_lo);
      assert ((((m ++ (i <: nat))) - ((jn - 1)))
              == (idx_lo ++ 1));

      mul_congruence (cmat i k1) ((- a) <: t) (coeff bigA ((idx_lo ++ 1))) ((- a) <: t);
      H.mul_commutativity_cr (coeff bigA ((idx_lo ++ 1))) ((- a) <: t);
      transitivity (cmat i k1 * ((- a) <: t))
                   (coeff bigA ((idx_lo ++ 1)) * ((- a) <: t))
                   (((- a) <: t) * coeff bigA ((idx_lo ++ 1)));
      H.zero_mul_x (coeff b ((bigN - jn)));
      mul_congruence (cmat i nN) (coeff b ((bigN - jn))) (zero <: t)
                     (coeff b ((bigN - jn)));
      transitivity (cmat i nN * coeff b ((bigN - jn)))
                   ((zero <: t) * coeff b ((bigN - jn))) (zero <: t);
      add_congruence (cmat i k1 * ((- a) <: t)) (cmat i nN * coeff b ((bigN - jn)))
                     (((- a) <: t) * coeff bigA ((idx_lo ++ 1))) (zero <: t);
      H.x_plus_zero (((- a) <: t) * coeff bigA ((idx_lo ++ 1)));
      transitivity (cmat i k1 * ((- a) <: t) + cmat i nN * coeff b ((bigN - jn)))
                   (((- a) <: t) * coeff bigA ((idx_lo ++ 1)) + (zero <: t))
                   (((- a) <: t) * coeff bigA ((idx_lo ++ 1)));
      add_congruence (cmat i k0 * (one <: t))
                     (cmat i k1 * ((- a) <: t) + cmat i nN * coeff b ((bigN - jn)))
                     (coeff bigA idx_lo) (((- a) <: t) * coeff bigA ((idx_lo ++ 1)));
      transitivity (matrix_mul cmat mulm i j)
                   (cmat i k0 * (one <: t)
                    + (cmat i k1 * ((- a) <: t) + cmat i nN * coeff b ((bigN - jn))))
                   tgt
    end
#pop-options

(* p-row pointwise identity: LHS = pexpr = bridge = S'[i][j] = RHS. *)
#push-options "--z3rlimit 150 --fuel 1 --ifuel 1"
let peel_pointwise_prow (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires (i <: nat) < n /\ L.length bigA <= (m ++ 1))
          (ensures matrix_mul (mat_c_peel bigA b m n) (mat_mul_peel a b m n) i j
                 = matrix_mul (mat_l_peel a m n) (mat_sprime_peel a bigA b m n) i j)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cmat = mat_c_peel bigA b m n in
    let mulm  = mat_mul_peel a b m n in
    let lmat = mat_l_peel a m n in
    let sp   = mat_sprime_peel a bigA b m n in
    let idx_lo : int = (((m ++ (i <: nat))) - (j <: nat)) in
    let idx_hi : int = (((((m ++ 1)) ++ (i <: nat))) - (j <: nat)) in
    let pexpr = coeff bigA idx_lo + (- a) * coeff bigA ((idx_lo ++ 1)) in
    let prodc = coeff ((poly_linear a) * bigA) idx_hi in
    peel_lhs_prow a bigA b m n i j;
    peel_prow_bridge a bigA m n i j;
    peel_rhs_prow a bigA b m n i j;

    transitivity (matrix_mul cmat mulm i j) pexpr prodc;

    transitivity (matrix_mul cmat mulm i j) prodc (matrix_mul lmat sp i j)
#pop-options

(* ================================================================ *)
(*  The full pointwise identity:  C * Mul'  =  L * S'  (all i, j).    *)
(* ================================================================ *)
let peel_pointwise (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires L.length bigA <= (m ++ 1) /\
                    deg b >= 0 /\ deg b <= n)
          (ensures matrix_mul (mat_c_peel bigA b m n) (mat_mul_peel a b m n) i j
                 = matrix_mul (mat_l_peel a m n) (mat_sprime_peel a bigA b m n) i j)
  = let bigN : nat = (m ++ n) in
    if (i <: nat) < n then
      peel_pointwise_prow a bigA b m n i j
    else if (i <: nat) < bigN then
      peel_pointwise_qrow a bigA b m n i j
    else
      peel_pointwise_last a bigA b m n j

(* ================================================================ *)
(*  Determinant transport across a (propositionally equal) size.     *)
(*  Used to relate det of the size-N+1 wrappers to det of the        *)
(*  underlying Sylvester matrices at their native sizes.             *)
(* ================================================================ *)
let det_size_transport (#t:Type) {| cr: commutative_ring t |} (s1 s2: pos)
  (m1: square_matrix t s1) (m2: square_matrix t s2)
  (pf: squash (s1 == s2))
  (h: (i: fin s1) -> (j: fin s1) ->
       Lemma (m1 i j == m2 ((i <: nat) <: fin s2) ((j <: nat) <: fin s2)))
  : Lemma (det m1 = det m2)
  = H.elim_equatable_laws t ();
    (* s1 == s2, so fin s1 = fin s2 and the two matrices live at the same size. *)
    let m2' : square_matrix t s1 = m2 in
    let pw (i j: fin s1) : Lemma (m1 i j = m2' i j)
      = h i j; reflexivity (m2' i j) in
    Classical.forall_intro_2 pw;
    det_pointwise_eq m1 m2'

(* det of mat_Mul (= sylvester_matrix 1 bigN (x-a) b coerced) = poly_eval b a. *)
let det_mat_mul_peel (#t:Type) {| f: field t |} (a: t) (b: polynomial t) (m n: nat{n >= 1})
  : Lemma (requires deg b >= 0 /\ deg b <= (m ++ n))
          (ensures det (mat_mul_peel a b m n) = poly_eval b a)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let bigN : nat = (m ++ n) in
    let syl = sylvester_matrix 1 bigN (poly_linear a) b in
    let pf : squash (size_peel m n == nat_add 1 bigN) = () in
    let h (i j: fin (size_peel m n))
      : Lemma (mat_mul_peel a b m n i j
               == syl ((i <: nat) <: fin (nat_add 1 bigN)) ((j <: nat) <: fin (nat_add 1 bigN)))
      = () in
    det_size_transport (size_peel m n) (nat_add 1 bigN) (mat_mul_peel a b m n) syl pf h;
    det_mul_block_is_eval a b bigN;                 (* det syl = poly_eval b a *)
    transitivity (det (mat_mul_peel a b m n)) (det syl) (poly_eval b a)

(* det of mat_C = resultant m n A B. *)
let det_mat_c_peel (#t:Type) {| f: field t |} (bigA b: polynomial t) (m n: nat{n >= 1})
  : Lemma (det (mat_c_peel bigA b m n)
         = resultant m n bigA b)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let sm = sylvester_matrix m n bigA b in
    (* mat_c_peel = block_diag_corner1 sm  (sizes coincide definitionally). *)
    block_diag_corner1_det sm;  (* det (block) = det sm *)
    resultant_unfold m n bigA b;                   (* resultant m n A B == det sm *)

    transitivity (det (mat_c_peel bigA b m n)) (det sm) (resultant m n bigA b)

(* det of mat_L = one. *)
let det_mat_l_peel (#t:Type) {| f: field t |} (a: t) (m n: nat{n >= 1})
  : Lemma (det (mat_l_peel a m n) = (one <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    det_peel_L a m n

(* det of mat_S' = resultant (m+1) n ((x-a)A) B. *)
let det_mat_sprime_peel (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  : Lemma (det (mat_sprime_peel a bigA b m n)
         = resultant #t #(cr_of_id t #(id_of_f t)) ((m ++ 1)) n
                     ((poly_linear a) * bigA) b)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let sp_syl = sylvester_matrix #t #cr ((m ++ 1)) n
                   ((poly_linear a) * bigA) b in
    let pf : squash (size_peel m n == nat_add ((m ++ 1)) n) = () in
    let h (i j: fin (size_peel m n))
      : Lemma (mat_sprime_peel a bigA b m n i j
               == sp_syl ((i <: nat) <: fin (nat_add ((m ++ 1)) n))
                         ((j <: nat) <: fin (nat_add ((m ++ 1)) n)))
      = () in
    det_size_transport #t #cr (size_peel m n) (nat_add ((m ++ 1)) n)
      (mat_sprime_peel a bigA b m n) sp_syl pf h;
    resultant_unfold ((m ++ 1)) n ((poly_linear a) * bigA) b;
    symmetry (resultant ((m ++ 1)) n ((poly_linear a) * bigA) b)
             (det sp_syl);
    transitivity (det (mat_sprime_peel a bigA b m n)) (det sp_syl)
                 (resultant ((m ++ 1)) n ((poly_linear a) * bigA) b)

(* ================================================================ *)
(*  THE LINEAR-FACTOR PEELING LEMMA.                                 *)
(*                                                                   *)
(*    Res_{m+1, n}((x - a) * A, B) = poly_eval B a * Res_{m, n}(A, B) *)
(*                                                                   *)
(*  (formal degrees:  deg A <= m  (length A <= m+1),  deg B <= n,     *)
(*   B nonzero (deg B >= 0)).                                *)
(* ================================================================ *)
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let peel (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  : Lemma (requires L.length bigA <= (m ++ 1) /\
                    deg b >= 0 /\ deg b <= n)
          (ensures (let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
                    resultant #t #cr ((m ++ 1)) n
                              ((poly_linear a) * bigA) b
                  = poly_eval b a * resultant m n bigA b))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cmat = mat_c_peel bigA b m n in
    let mulm  = mat_mul_peel a b m n in
    let lmat = mat_l_peel a m n in
    let sp   = mat_sprime_peel a bigA b m n in
    let sz : pos = size_peel m n in
    (* det (C * Mul') = det (L * S') via the pointwise identity. *)
    let pw (i j: fin sz)
      : Lemma (matrix_mul cmat mulm i j = matrix_mul lmat sp i j)
      = peel_pointwise a bigA b m n i j in
    Classical.forall_intro_2 pw;
    det_pointwise_eq (matrix_mul cmat mulm) (matrix_mul lmat sp);
    (* det_mul on both products. *)
    det_mul cmat mulm;                          (* det(C*Mul') = det C * det Mul' *)
    det_mul lmat sp;                           (* det(L*S')   = det L * det S'   *)
    (* det values. *)
    det_mat_c_peel bigA b m n;                      (* det C  = resultant m n A B *)
    det_mat_mul_peel a b m n;                       (* det Mul' = poly_eval b a *)
    det_mat_l_peel a m n;                           (* det L  = one *)
    det_mat_sprime_peel a bigA b m n;               (* det S' = resultant (m+1) n ((x-a)A) b *)
    let rmnAB  = resultant m n bigA b in
    let rS'    = resultant ((m ++ 1)) n ((poly_linear a) * bigA) b in
    (* det C * det Mul' = resultant m n A B * poly_eval b a *)
    mul_congruence (det cmat) (det mulm) rmnAB (poly_eval b a);
    transitivity (det (matrix_mul cmat mulm)) (det cmat * det mulm) (rmnAB * poly_eval b a);
    (* det L * det S' = one * det S' = det S' = rS' *)

    mul_congruence (det lmat) (det sp) (one <: t) (det sp);   (* det L * det S' = one * det S' *)
    H.one_mul_x (det sp);
    transitivity (det lmat * det sp) ((one <: t) * det sp) (det sp);
    transitivity (det (matrix_mul lmat sp)) (det lmat * det sp) (det sp);
    transitivity (det (matrix_mul lmat sp)) (det sp) rS';
    (* chain: rS' = det(L*S') = det(C*Mul') = rmnAB * poly_eval b a *)


    transitivity rS' (det (matrix_mul lmat sp)) (det (matrix_mul cmat mulm));
    transitivity rS' (det (matrix_mul cmat mulm)) (rmnAB * poly_eval b a);
    (* commute to poly_eval b a * resultant m n A B *)
    H.mul_commutativity_cr rmnAB (poly_eval b a);
    transitivity rS' (rmnAB * poly_eval b a) (poly_eval b a * rmnAB)
#pop-options

(* ================================================================================ *)
(*  FOLDED-IN: Core.Polynomial.ResultantPoisson *)
(* ================================================================================ *)

(* ================================================================ *)
(*  The provided factorization  A = lc * prod (x - ai).             *)
(*  Linear factors folded on the OUTSIDE so the head peels first.    *)
(* ================================================================ *)

let rec scaled_prod (#t:Type) {| f: field t |} (lc: t{not (lc = (zero <: t))}) (roots: list t)
  : Tot (polynomial t) (decreases roots)
  = match roots with
    | []        -> ([lc] <: polynomial t)
    | a :: rest -> (poly_linear a) * (scaled_prod lc rest)

(* ring rearrangement:  x * (y * z) = y * (x * z)  *)
let mul_swap_mid (#t:Type) {| cr: commutative_ring t |} (x y z: t)
  : Lemma (x * (y * z) = y * (x * z))
  = assert (x * (y * z) = y * (x * z)) by canon_ring ()

(* The Poisson right-hand side:  prod_i (poly_eval b ai). *)
let rec root_eval_product (#t:Type) {| f: field t |} (b: polynomial t) (roots: list t)
  : Tot t (decreases roots)
  = match roots with
    | []        -> one #t
    | a :: rest -> poly_eval b a * root_eval_product b rest

(* ================================================================ *)
(*  Degree of the provided factorization.                           *)
(*    poly_deg (scaled_prod lc roots) = Some (length roots)   (lc<>0) *)
(*  hence  L.length (scaled_prod lc roots) = length roots + 1.       *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let rec scaled_prod_degree (#t:Type) {| f: field t |} (lc: t{not (lc = (zero <: t))}) (roots: list t)
  : Lemma (ensures deg (scaled_prod lc roots) == L.length roots)
          (decreases roots)
  = let id_t : integral_domain t = id_of_f t in
    match roots with
    | []        ->
        (* scaled_prod = [lc], lc <> 0, so poly_deg = Some 0 *)
        ()
    | a :: rest ->
        scaled_prod_degree lc rest;                 (* deg (scaled_prod rest) = length rest *)
        poly_linear_deg a;                          (* deg (x-a) = Some 1 *)
        degree_mul (poly_linear a) (scaled_prod lc rest)
        (* deg (poly_mul (x-a) (scaled_prod rest)) = 1 + length rest = length (a::rest) *)
#pop-options

let scaled_prod_length (#t:Type) {| f: field t |} (lc: t{not (lc = (zero <: t))}) (roots: list t)
  : Lemma (L.length (scaled_prod lc roots) <= ((L.length roots) ++ 1))
  = scaled_prod_degree lc roots
    (* poly_deg p = Some (L.length p - 1) on nonempty p; deg = length roots,
       so L.length p = length roots + 1. *)

(* ================================================================ *)
(*  THE POISSON PRODUCT FORMULA.                                     *)
(*                                                                   *)
(*    Res_{k, n}(scaled_prod lc roots, B)                            *)
(*      =  cpow lc n  *  prod_i (poly_eval B ai)                     *)
(*                                                                   *)
(*  where  k = length roots,  n >= deg B,  lc nonzero, B nonzero.    *)
(*  Induction on the root list:  head peels via `peel` (factor       *)
(*  poly_eval B a), base case `resultant_const` (cpow lc n).         *)
(* ================================================================ *)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 2"
let rec poisson (#t:Type) {| f: field t |} (lc: t{not (lc = (zero <: t))}) (roots: list t)
  (b: polynomial t) (n: nat{n >= 1})
  : Lemma (requires deg b >= 0 /\ deg b <= n)
          (ensures (let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
                    resultant (L.length roots) n (scaled_prod lc roots) b
                  = cpow lc n * root_eval_product b roots))
          (decreases roots)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match roots with
    | []        ->
        (* Res_{0,n}([lc], B) = cpow lc n = cpow lc n * one = cpow lc n * root_eval_product b [] *)
        resultant_const lc b n;                     (* Res_{0,n}([lc],B) = cpow lc n *)
        H.x_mul_one (cpow lc n);                          (* cpow lc n * one = cpow lc n *)

        transitivity (resultant (L.length roots) n (scaled_prod lc roots) b)
                     (cpow lc n) (cpow lc n * (one <: t))
    | a :: rest ->
        let arest = scaled_prod lc rest in
        (* peel one (x-a) factor:
             Res_{m'+1,n}((x-a)*arest, B) = poly_eval B a * Res_{m',n}(arest, B),
           with m' = length rest. *)
        scaled_prod_length lc rest;                 (* L.length arest <= length rest + 1 *)
        peel a arest b (L.length rest) n;
        (* IH: Res_{m',n}(arest, B) = cpow lc n * root_eval_product B rest *)
        poisson lc rest b n;
        let m' = L.length rest in
        let resA  = resultant #t #cr ((m' ++ 1)) n
                              ((poly_linear a) * arest) b in
        let resA' = resultant m' n arest b in
        let rep   = root_eval_product b rest in
        (* resA = poly_eval b a * resA'  (peel) *)
        (* resA' = cpow lc n * rep        (IH) *)

        mul_congruence (poly_eval b a) resA' (poly_eval b a) (cpow lc n * rep);
        transitivity resA (poly_eval b a * resA') (poly_eval b a * (cpow lc n * rep));
        (* rearrange  poly_eval b a * (cpow lc n * rep)  =  cpow lc n * (poly_eval b a * rep) *)
        mul_swap_mid (poly_eval b a) (cpow lc n) rep;
        transitivity resA (poly_eval b a * (cpow lc n * rep)) (cpow lc n * (poly_eval b a * rep))
#pop-options

(* ================================================================================ *)
(*  FOLDED-IN: Core.Polynomial.ResultantConverse *)
(* ================================================================================ *)

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* ---------------------------------------------------------------- *)
(*  List builder: build_from off len g = [g off; ...; g (off+len-1)] *)
(* ---------------------------------------------------------------- *)

let rec build_from (#t:Type) (off: nat) (len: nat) (g: nat -> t)
  : Tot (l:list t {L.length l == len}) (decreases len)
  = if len = 0 then []
    else g off :: build_from ((off ++ 1)) ((len - 1)) g

let rec build_from_index (#t:Type) (off: nat) (len: nat) (g: nat -> t) (i: nat{i < len})
  : Lemma (ensures L.index (build_from off len g) i == g ((off ++ i))) (decreases len)
  = if i = 0 then ()
    else build_from_index ((off ++ 1)) ((len - 1)) g ((i - 1))

(* coeff (poly_mul a b) j = 0 once j+1 >= len a + len b *)
let poly_mul_coeff_high (#t:Type) {| cr: commutative_ring t |}
  (a b: polynomial t) (j: nat)
  : Lemma (requires j + 1 >= ((L.length a) ++ (L.length b)))
          (ensures  coeff (a * b) j = (zero <: t))
  = H.elim_equatable_laws t ();
    let g (i:nat) : t = coeff a i * coeff b ((j - i)) in
    coeff_poly_mul_named a b j g
      (fun (i:nat) -> reflexivity (coeff a i * coeff b ((j - i))));
    sum_range_all_zero g 0 (L.length a)
      (fun (i:nat{0 <= i /\ i < L.length a}) ->
        assert ((j - i) >= L.length b);
        H.x_mul_zero (coeff a i));
    transitivity (coeff (a * b) j) (sum_range g 0 (L.length a)) (zero <: t)

(* vector_dot is congruent in its right argument (pointwise =) *)
#push-options "--z3rlimit 80"
let vector_dot_cong_right (#t:Type) {| cr: commutative_ring t |} (#n: pos)
  (a b1 b2: vector t n)
  (h: (j: fin n) -> Lemma (b1 j = b2 j))
  : Lemma (vector_dot a b1 = vector_dot a b2)
  = H.elim_equatable_laws t ();
    let per (k: fin n) : Lemma (pointwise_mul a b1 k = pointwise_mul a b2 k)
      = pointwise_mul_unfold a b1 k;
        pointwise_mul_unfold a b2 k;
        h k;

        mul_congruence (a k) (b1 k) (a k) (b2 k);
        transitivity (pointwise_mul a b1 k) (a k * b1 k) (a k * b2 k);
        transitivity (pointwise_mul a b1 k) (a k * b2 k) (pointwise_mul a b2 k)
    in
    fin_sum_congruence (pointwise_mul a b1) (pointwise_mul a b2) per;
    vector_dot_reveal a b1;
    vector_dot_reveal a b2;
    transitivity (vector_dot a b1) (fin_sum (pointwise_mul a b1)) (fin_sum (pointwise_mul a b2));

    transitivity (vector_dot a b1) (fin_sum (pointwise_mul a b2)) (vector_dot a b2)
#pop-options

(* ---------------------------------------------------------------- *)
(*  Step 3: combo_vec_surjective                                     *)
(* ---------------------------------------------------------------- *)

(* index function reading w reversed in the u-block (j < n_deg) *)
let gu_idx (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (w: fin ((m_deg ++ n_deg)) -> t) (i: nat) : t
  = if i < n_deg
    then w ((((n_deg - 1)) - i) <: fin ((m_deg ++ n_deg)))
    else (zero <: t)

(* index function reading w reversed in the v-block (j >= n_deg) *)
let gv_idx (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (w: fin ((m_deg ++ n_deg)) -> t) (i: nat) : t
  = if i < m_deg
    then w ((((((m_deg ++ n_deg)) - 1)) - i)
            <: fin ((m_deg ++ n_deg)))
    else (zero <: t)

let mk_u (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (w: fin ((m_deg ++ n_deg)) -> t) : polynomial t
  = trim (build_from 0 n_deg (gu_idx m_deg n_deg w))

let mk_v (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (w: fin ((m_deg ++ n_deg)) -> t) : polynomial t
  = trim (build_from 0 m_deg (gv_idx m_deg n_deg w))

let mk_u_length (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (w: fin ((m_deg ++ n_deg)) -> t)
  : Lemma (L.length (mk_u m_deg n_deg w) <= n_deg)
  = trim_length_le (build_from 0 n_deg (gu_idx m_deg n_deg w))

let mk_v_length (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (w: fin ((m_deg ++ n_deg)) -> t)
  : Lemma (L.length (mk_v m_deg n_deg w) <= m_deg)
  = trim_length_le (build_from 0 m_deg (gv_idx m_deg n_deg w))

let mk_u_coeff (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (w: fin ((m_deg ++ n_deg)) -> t) (i: nat{i < n_deg})
  : Lemma (coeff (mk_u m_deg n_deg w) i = gu_idx m_deg n_deg w i)
  = H.elim_equatable_laws t ();
    let lst = build_from 0 n_deg (gu_idx m_deg n_deg w) in
    coeff_trim lst i;
    build_from_index 0 n_deg (gu_idx m_deg n_deg w) i

let mk_v_coeff (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (w: fin ((m_deg ++ n_deg)) -> t) (i: nat{i < m_deg})
  : Lemma (coeff (mk_v m_deg n_deg w) i = gv_idx m_deg n_deg w i)
  = H.elim_equatable_laws t ();
    let lst = build_from 0 m_deg (gv_idx m_deg n_deg w) in
    coeff_trim lst i;
    build_from_index 0 m_deg (gv_idx m_deg n_deg w) i

(* combo_vec (mk_u) (mk_v) reproduces w at each index *)
#push-options "--z3rlimit 80"
let combo_vec_surjective (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (w: fin ((m_deg ++ n_deg)) -> t)
  (j: fin ((m_deg ++ n_deg)))
  : Lemma (combo_vec m_deg n_deg (mk_u m_deg n_deg w) (mk_v m_deg n_deg w) j = w j)
  = H.elim_equatable_laws t ();
    let size = (m_deg ++ n_deg) in
    let u = mk_u m_deg n_deg w in
    let v = mk_v m_deg n_deg w in
    if (j <: nat) < n_deg then begin
      let i : nat = (((n_deg - 1)) - (j <: nat)) in
      assert (i < n_deg);
      assert (combo_vec m_deg n_deg u v j == coeff u i);
      mk_u_coeff m_deg n_deg w i;
      assert (gu_idx m_deg n_deg w i == w (j <: fin size))
    end
    else begin
      let i : nat = (((m_deg - 1)) - (((j <: nat) - n_deg))) in
      assert (i < m_deg);
      assert (combo_vec m_deg n_deg u v j == coeff v i);
      mk_v_coeff m_deg n_deg w i;
      assert (gv_idx m_deg n_deg w i == w (j <: fin size))
    end
#pop-options

(* ---------------------------------------------------------------- *)
(*  Step 4 tail: all coeffs zero ==> poly_eq r poly_zero             *)
(* ---------------------------------------------------------------- *)

let all_coeffs_zero_poly_eq (#t:Type) {| cr: commutative_ring t |}
  (r: polynomial t)
  : Lemma (requires (forall (i:nat). coeff r i = (zero <: t)))
          (ensures  (r = (poly_zero #t)))
  = H.elim_equatable_laws t ();
    let aux (j:nat) : Lemma (coeff r j = coeff (poly_zero #t) j)
      = reflexivity (coeff r j) in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq r (poly_zero #t)

(* ---------------------------------------------------------------- *)
(*  Step 4: the combination polynomial u*pp + v*qq vanishes          *)
(* ---------------------------------------------------------------- *)

(* coeff s k = 0 for indices k in [0, size): via sylvester_action.    *)
#push-options "--z3rlimit 120 --fuel 2"
let s_coeff_zero_low (#t:Type) {| f: field t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (pp qq: polynomial t)
  (w: fin ((m_deg ++ n_deg)) -> t)
  (k: nat{k < (m_deg ++ n_deg)})
  : Lemma (requires (let cr = cr_of_id t #(id_of_f t) in
                     let st = transpose (sylvester_matrix m_deg n_deg pp qq) in
                     forall (i: fin ((m_deg ++ n_deg))). null_vec_hyp st w i))
          (ensures (let cr = cr_of_id t #(id_of_f t) in
                    coeff (((mk_u m_deg n_deg w) * pp)
                           + ((mk_v m_deg n_deg w) * qq)) k = (zero <: t)))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let size : pos = (m_deg ++ n_deg) in
    let u = mk_u m_deg n_deg w in
    let v = mk_v m_deg n_deg w in
    let st = transpose (sylvester_matrix m_deg n_deg pp qq) in
    let i : fin size = (((size - 1)) - k) in
    mk_u_length m_deg n_deg w;
    mk_v_length m_deg n_deg w;
    (* sylvester_action: vector_dot (row st i) (combo_vec u v) = coeff s (size-1-i) = coeff s k *)
    sylvester_action m_deg n_deg pp qq u v i;
    (* combo_vec u v = w pointwise, so vector_dot (row st i) (combo_vec u v) = vector_dot (row st i) w = 0 *)
    let cv = combo_vec m_deg n_deg u v in
    vector_dot_cong_right (row st i) cv w
      (fun (jj: fin size) -> combo_vec_surjective m_deg n_deg w jj);
    assert (vector_dot (row st i) w = (zero <: t));
    transitivity (vector_dot (row st i) cv) (vector_dot (row st i) w) (zero <: t);
    assert ((((size - 1)) - (i <: nat)) == k);
    symmetry (vector_dot (row st i) cv)
             (coeff ((u * pp) + (v * qq)) k);
    transitivity (coeff ((u * pp) + (v * qq)) k)
                 (vector_dot (row st i) cv)
                 (zero <: t)
#pop-options

(* coeff s k = 0 for indices k >= size: via degree/length bound.      *)
#push-options "--z3rlimit 100"
let s_coeff_zero_high (#t:Type) {| f: field t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (pp qq: polynomial t)
  (w: fin ((m_deg ++ n_deg)) -> t)
  (k: nat{k >= (m_deg ++ n_deg)})
  : Lemma (requires L.length pp <= (m_deg ++ 1) /\
                    L.length qq <= (n_deg ++ 1))
          (ensures (let cr = cr_of_id t #(id_of_f t) in
                    coeff (((mk_u m_deg n_deg w) * pp)
                           + ((mk_v m_deg n_deg w) * qq)) k = (zero <: t)))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let u = mk_u m_deg n_deg w in
    let v = mk_v m_deg n_deg w in
    mk_u_length m_deg n_deg w;   (* len u <= n_deg *)
    mk_v_length m_deg n_deg w;   (* len v <= m_deg *)
    poly_mul_coeff_high u pp k;   (* k+1 >= n_deg + (m_deg+1) >= len u + len pp *)
    poly_mul_coeff_high v qq k;   (* k+1 >= m_deg + (n_deg+1) >= len v + len qq *)
    poly_add_coeff (u * pp) (v * qq) k;
    H.x_plus_zero (zero <: t);
    add_congruence (coeff (u * pp) k) (coeff (v * qq) k)
                   (zero <: t) (zero <: t);
    transitivity (coeff ((u * pp) + (v * qq)) k)
                 (coeff (u * pp) k + coeff (v * qq) k)
                 ((zero <: t) + (zero <: t));
    transitivity (coeff ((u * pp) + (v * qq)) k)
                 ((zero <: t) + (zero <: t))
                 (zero <: t)
#pop-options

(* The combination polynomial u*pp + v*qq is poly_eq to zero.         *)
#push-options "--z3rlimit 80"
let s_is_zero (#t:Type) {| f: field t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (pp qq: polynomial t)
  (w: fin ((m_deg ++ n_deg)) -> t)
  : Lemma (requires (let cr = cr_of_id t #(id_of_f t) in
                     L.length pp <= (m_deg ++ 1) /\
                     L.length qq <= (n_deg ++ 1) /\
                     (let st = transpose (sylvester_matrix m_deg n_deg pp qq) in
                      forall (i: fin ((m_deg ++ n_deg))). null_vec_hyp st w i)))
          (ensures (let cr = cr_of_id t #(id_of_f t) in
                    (((mk_u m_deg n_deg w * pp)
                      + (mk_v m_deg n_deg w * qq)) = (poly_zero #t))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let size = (m_deg ++ n_deg) in
    let s : polynomial t = ((mk_u m_deg n_deg w) * pp) + ((mk_v m_deg n_deg w) * qq) in
    let all_zero (k: nat) : Lemma (coeff s k = (zero <: t))
      = if k < size then s_coeff_zero_low m_deg n_deg pp qq w k
        else s_coeff_zero_high m_deg n_deg pp qq w k
    in
    Classical.forall_intro all_zero;
    all_coeffs_zero_poly_eq s
#pop-options

(* ---------------------------------------------------------------- *)
(*  Step 5: not both u and v are zero (since w has a nonzero entry)   *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 80"
let not_both_zero (#t:Type) {| f: field t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (w: fin ((m_deg ++ n_deg)) -> t)
  (k: fin ((m_deg ++ n_deg)))
  : Lemma (requires is_nonzero (w k))
          (ensures  not ((mk_u m_deg n_deg w = (poly_zero #t)) /\
                         (mk_v m_deg n_deg w = (poly_zero #t))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let u = mk_u m_deg n_deg w in
    let v = mk_v m_deg n_deg w in
    let contra () : Lemma (requires (u = (poly_zero #t)) /\ (v = (poly_zero #t)))
                          (ensures  False)
      = combo_vec_surjective m_deg n_deg w k;
        (* combo_vec u v k = w k; but combo_vec entries are coeffs of u or v, both ~0 *)
        if (k <: nat) < n_deg then begin
          let i : nat = (((n_deg - 1)) - (k <: nat)) in
          assert (combo_vec m_deg n_deg u v k == coeff u i);
          poly_eq_means_equal_coeffs u (poly_zero #t) i;
          assert (coeff u i = (zero <: t));
          assert (w k = (zero <: t))
        end
        else begin
          let i : nat = (((m_deg - 1)) - (((k <: nat) - n_deg))) in
          assert (combo_vec m_deg n_deg u v k == coeff v i);
          poly_eq_means_equal_coeffs v (poly_zero #t) i;
          assert (coeff v i = (zero <: t));
          assert (w k = (zero <: t))
        end
    in
    Classical.move_requires contra ()
#pop-options

(* ---------------------------------------------------------------- *)
(*  Step 6: divisibility relation + coprime endgame                  *)
(* ---------------------------------------------------------------- *)

(* generic comm-group: a + b = 0 ==> a = neg b *)
let add_eq_zero_gives_eq_neg (#t:Type) {| acg: add_comm_group t |} (a b: t)
  : Lemma (requires (a + b) = (zero <: t))
          (ensures  a = (- b))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    x_plus_neg_x b; reflexivity a;
    add_congruence a (b + (- b)) a (zero <: t);
    x_plus_zero a;
    transitivity (a + (b + (- b))) (a + (zero <: t)) a;
    add_associativity a b (- b);
    transitivity ((a + b) + (- b)) (a + (b + (- b))) a;

    add_congruence (a + b) (- b) (zero <: t) (- b);
    zero_plus_x (- b);
    transitivity ((a + b) + (- b)) ((zero <: t) + (- b)) (- b);


    transitivity (- b) ((a + b) + (- b)) a;
    symmetry (- b) a

(* from u*pp + v*qq ~ 0, derive qq | u*pp *)
let relation_gives_div (#t:Type) {| f: field t |}
  (u v pp qq: polynomial t)
  : Lemma (requires (((u * pp) + (v * qq)) = (poly_zero #t)))
          (ensures  divides qq (u * pp))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let acg : add_comm_group (polynomial t) = polynomial_acg cr in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let a = poly_mul u pp in
    let b = poly_mul v qq in
    polynomial_acg_add_reveal cr a b;
    polynomial_acg_zero_reveal #t cr;
    polynomial_acg_eq_reveal cr (a + b) (poly_zero #t);
    assert (acg.add a b == poly_add a b);
    add_eq_zero_gives_eq_neg a b;
    polynomial_acg_neg_reveal cr b;
    assert (a = poly_neg b);
    mul_commutativity v qq;
    divides_intro qq (qq * v) v;
    divides_congruence_right qq (qq * v) (v * qq);
    divides_neg qq (v * qq);
    symmetry a (poly_neg b);
    divides_congruence_right qq (poly_neg b) a

(* given the relation and not-both-zero, coprime pp qq is impossible *)
let not_coprime_endgame (#t:Type) {| f: field t |}
  (u v pp qq: polynomial t)
  : Lemma (requires
      (((u * pp) + (v * qq)) = (poly_zero #t)) /\
      divides qq (u * pp) /\
      not ((u = (poly_zero #t)) /\ (v = (poly_zero #t))) /\
      deg pp >= 0 /\ deg qq >= 0 /\
      (deg u < 0 \/ deg u < deg qq))
    (ensures  not (coprime pp qq))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let contra () : Lemma (requires coprime pp qq) (ensures False)
      = IR.coprime_symmetric pp qq;
        euclid_lemma qq pp u;
        (if deg u >= 0 then
             IR.divides_degree_le qq u
         else begin
             UN.degree_none_poly_eq_zero u;
             reflexivity pp;
             mul_congruence u pp (poly_zero #t) pp;
             assert (((poly_zero #t) * pp) == (poly_zero #t));
             reflexivity (v * qq);
             add_congruence (u * pp) (v * qq) (poly_zero #t) (v * qq);
             add_zero (v * qq);
             symmetry ((poly_zero #t) + (v * qq)) (v * qq);
             symmetry ((u * pp) + (v * qq)) (poly_zero #t);
             transitivity (v * qq)
                ((poly_zero #t) + (v * qq))
                ((u * pp) + (v * qq));
             transitivity (v * qq)
                ((u * pp) + (v * qq)) (poly_zero #t);
             poly_domain_law v qq
         end)
    in
    Classical.move_requires contra ()

(* gcd of (pp, qq) with qq nonzero has a degree *)
let gcd_pos (#t:Type) {| f: field t |}
  (pp qq: polynomial t)
  : Lemma (requires deg qq >= 0)
          (ensures  deg (poly_gcd pp qq) >= 0)
  = H.elim_equatable_laws (polynomial t) ();
    let g = poly_gcd pp qq in
    gcd_divides_right pp qq;
    if deg g >= 0 then ()
    else begin
        UN.degree_none_poly_eq_zero g;
        symmetry g (poly_zero #t);
        divides_congruence_left g (poly_zero #t) qq;
        eliminate exists (c: polynomial t). (qq = ((poly_zero #t) * c))
        returns False
        with _hyp.
          begin
            assert (((poly_zero #t) * c) == (poly_zero #t));
            UN.degree_well_defined qq (poly_zero #t)
          end
    end

(* when pp ~ 0, gcd(pp,qq) has the same degree as qq *)
#push-options "--z3rlimit 120"
let gcd_deg_when_pp_zero (#t:Type) {| f: field t |}
  (pp qq: polynomial t)
  : Lemma (requires deg pp < 0 /\ deg qq >= 0)
          (ensures  deg (poly_gcd pp qq) == deg qq)
  = H.elim_equatable_laws (polynomial t) ();
    let g = poly_gcd pp qq in
    gcd_pos pp qq;
    gcd_divides_right pp qq;
    IR.divides_degree_le g qq;
    UN.degree_none_poly_eq_zero pp;
    divides_zero qq;
    symmetry pp (poly_zero #t);
    divides_congruence_right qq (poly_zero #t) pp;
    divides_refl qq;
    gcd_is_maximal pp qq qq;
    IR.divides_degree_le qq g
#pop-options

(* ---------------------------------------------------------------- *)
(*  Main theorem: resultant = 0 ==> deg(gcd) >= 1                     *)
(* ---------------------------------------------------------------- *)

(* core step given the null vector w with nonzero entry at k *)
#push-options "--z3rlimit 120 --fuel 2"
let resultant_converse_core (#t:Type) {| f: field t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (pp qq: polynomial t)
  (w: fin ((m_deg ++ n_deg)) -> t)
  (k: fin ((m_deg ++ n_deg)))
  : Lemma (requires (let cr = cr_of_id t #(id_of_f t) in
                     L.length pp <= (m_deg ++ 1) /\
                     L.length qq <= (n_deg ++ 1) /\
                     deg qq >= 0 /\ deg qq == n_deg /\ n_deg >= 1 /\
                     is_nonzero (w k) /\
                     (let st = transpose (sylvester_matrix m_deg n_deg pp qq) in
                      forall (i: fin ((m_deg ++ n_deg))). null_vec_hyp st w i)))
          (ensures  deg (poly_gcd pp qq) >= 1)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws (polynomial t) ();
    let u = mk_u m_deg n_deg w in
    let v = mk_v m_deg n_deg w in
    s_is_zero m_deg n_deg pp qq w;
    gcd_pos pp qq;
    (if deg pp < 0 then gcd_deg_when_pp_zero pp qq
     else begin
         relation_gives_div u v pp qq;
         not_both_zero m_deg n_deg w k;
         mk_u_length m_deg n_deg w;
         not_coprime_endgame u v pp qq;
         coprime_reveal pp qq
     end)
#pop-options

let resultant_converse (#t:Type) {| f: field t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (pp qq: polynomial t)
  : Lemma (requires resultant m_deg n_deg pp qq = (zero <: t) /\
                    L.length pp <= (m_deg ++ 1) /\
                    L.length qq <= (n_deg ++ 1) /\
                    deg qq >= 0 /\ deg qq == n_deg /\ n_deg >= 1)
          (ensures  deg (GC.poly_gcd pp qq) >= 1)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let sm = sylvester_matrix m_deg n_deg pp qq in
    let st = transpose sm in
    resultant_unfold m_deg n_deg pp qq;
    det_transpose sm;
    transitivity (det st) (det sm) (zero <: t);
    KD.det_zero_implies_null_vec st;
    eliminate exists (w: fin ((m_deg ++ n_deg)) -> t)
                     (k: fin ((m_deg ++ n_deg))).
                is_nonzero (w k) /\
                (forall (i: fin ((m_deg ++ n_deg))).
                   vector_dot (row st i) w = (zero <: t))
    returns deg (GC.poly_gcd pp qq) >= 1
    with _hyp.
      resultant_converse_core m_deg n_deg pp qq w k

(* ================================================================ *)
(*  The full matrix-level equivalence (forward + converse):          *)
(*    resultant m n pp qq = 0  <==>  deg(gcd pp qq) >= 1.            *)
(*  (pp nonzero; forward = resultant_zero_of_common_divisor,         *)
(*   backward = resultant_converse.)                                 *)
(* ================================================================ *)
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let resultant_vanishing_iff (#t:Type) {| f: field t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (pp qq: polynomial t)
  : Lemma (requires L.length pp <= (m_deg ++ 1) /\
                    L.length qq <= (n_deg ++ 1) /\
                    deg pp >= 0 /\ deg pp <= m_deg /\
                    deg qq >= 0 /\ deg qq == n_deg /\ n_deg >= 1)
          (ensures  (resultant m_deg n_deg pp qq = (zero <: t))
                    <==>
                    (deg (GC.poly_gcd pp qq) >= 1))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let g = GC.poly_gcd pp qq in
    let bwd () : Lemma (requires resultant m_deg n_deg pp qq = (zero <: t))
                       (ensures  deg g >= 1)
      = resultant_converse m_deg n_deg pp qq in
    let fwd () : Lemma (requires deg g >= 1)
                       (ensures  resultant m_deg n_deg pp qq = (zero <: t))
      = GC.gcd_divides_left  pp qq;
        GC.gcd_divides_right pp qq;
        resultant_zero_of_common_divisor m_deg n_deg pp qq g in
    FStar.Classical.move_requires bwd ();
    FStar.Classical.move_requires fwd ()
#pop-options
