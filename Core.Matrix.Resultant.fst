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
open Core.Matrix.Sylvester
open Core.Matrix.Determinant
open Core.Matrix.NullVec
open Core.Vector
open Core.FinSum

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

(* ================================================================== *)
(*  L4: resultant vanishes iff common factor exists (forward dir)      *)
(* ================================================================== *)

(* Helper: b*p poly_eq a*q when p = g*a, q = g*b *)
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let bp_eq_aq (#t:Type) {| f: field t |}
  (p q g: polynomial t)
  (hgp: divides g p)
  (hgq: divides g q)
  (hdeg: Some? (poly_deg g))
  : Lemma (ensures poly_eq (poly_mul (poly_div q g) p) (poly_mul (poly_div p g) q))
  = let a = poly_div p g in
    let b = poly_div q g in
    poly_div_correct p g;
    poly_div_correct q g;
    poly_eq_symmetry (poly_mul g a) p;
    poly_eq_reflexivity b;
    poly_mul_congruence b p b (poly_mul g a);
    poly_mul_associativity b g a;
    poly_eq_symmetry (poly_mul (poly_mul b g) a) (poly_mul b (poly_mul g a));
    mul_commutativity_cr b g;
    poly_eq_reflexivity a;
    poly_mul_congruence (poly_mul b g) a (poly_mul g b) a;
    poly_mul_congruence (poly_mul g b) a q a;
    mul_commutativity_cr q a;
    poly_eq_transitivity (poly_mul b p) (poly_mul b (poly_mul g a)) (poly_mul (poly_mul b g) a);
    poly_eq_transitivity (poly_mul b p) (poly_mul (poly_mul b g) a) (poly_mul (poly_mul g b) a);
    poly_eq_transitivity (poly_mul b p) (poly_mul (poly_mul g b) a) (poly_mul q a);
    poly_eq_transitivity (poly_mul b p) (poly_mul q a) (poly_mul a q)
#pop-options

(* Helper: poly_div yields nonzero quotient when dividend has degree *)
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let poly_div_has_degree_local (#t:Type) {| f: field t |}
  (p d: polynomial t)
  : Lemma (requires Some? (poly_deg d) /\ Some? (poly_deg p) /\ divides d p)
          (ensures  Some? (poly_deg (poly_div p d)))
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    poly_div_correct p d;
    let q = poly_div p d in
    match poly_deg q with
    | Some _ -> ()
    | None ->
        degree_none_poly_eq_zero q;
        poly_mul_congruence d q d (poly_zero #t);
        H.x_mul_zero #(polynomial t) d;
        degree_well_defined p (poly_zero #t)
#pop-options

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let poly_div_degree_local (#t:Type) {| f: field t |}
  (p d: polynomial t)
  : Lemma (requires Some? (poly_deg d) /\ Some? (poly_deg p) /\ divides d p)
          (ensures  Some? (poly_deg (poly_div p d)) /\
                    Some?.v (poly_deg (poly_div p d)) ==
                    Prims.op_Subtraction (Some?.v (poly_deg p)) (Some?.v (poly_deg d)))
  = poly_div_has_degree_local p d;
    poly_div_correct p d;
    let q = poly_div p d in
    degree_mul #t #(id_of_f t) d q;
    poly_eq_symmetry (poly_mul d q) p;
    degree_well_defined p (poly_mul d q)
#pop-options

(* Sylvester null vector: encodes b*p = a*q as a kernel element *)
let syl_null_vec (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (a b: polynomial t)
  : vector t (Prims.op_Addition m_deg n_deg)
  = fun (j: fin (Prims.op_Addition m_deg n_deg)) ->
      if (j <: nat) < n_deg
      then coeff b (Prims.op_Subtraction (Prims.op_Subtraction n_deg 1) (j <: nat))
      else neg (coeff a (Prims.op_Subtraction (Prims.op_Subtraction m_deg 1)
                          (Prims.op_Subtraction (j <: nat) n_deg)))

(* Helper: when poly_eq(bp,aq), their coeff difference is zero *)
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let coeff_cancel (#t:Type) {| cr: commutative_ring t |} (bp aq: polynomial t) (kk: nat)
  : Lemma (requires poly_eq bp aq)
          (ensures coeff bp kk + neg (coeff aq kk) = (zero <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    poly_eq_means_equal_coeffs bp aq kk;
    add_congruence (coeff bp kk) (neg (coeff aq kk)) (coeff aq kk) (neg (coeff aq kk));
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
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (p q a b: polynomial t)
  (i: fin (Prims.op_Addition m_deg n_deg))
  : Lemma
    (requires poly_eq (poly_mul b p) (poly_mul a q) /\
             L.length b <= n_deg /\ L.length a <= m_deg)
    (ensures  vector_dot (row (transpose (sylvester_matrix m_deg n_deg p q)) i)
                         (syl_null_vec m_deg n_deg a b)
            = (zero <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let size : pos = Prims.op_Addition m_deg n_deg in
    let st = transpose (sylvester_matrix m_deg n_deg p q) in
    let v  = syl_null_vec m_deg n_deg a b in
    let kk : nat = Prims.op_Subtraction (Prims.op_Subtraction size 1) (i <: nat) in
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
    coeff_cancel (poly_mul b p) (poly_mul a q) kk;

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
    let g_bp (r:nat) : t = coeff b r * coeff p (Prims.op_Subtraction kk r) in
    let h_rev (j: nat{j < n_deg})
      : Lemma (g_fp j = g_bp (Prims.op_Subtraction (Prims.op_Subtraction n_deg 1) j))
      = assert ((j <: nat) < n_deg);
        let j_f : fin size = (j <: fin size) in
        assert (g_fp j == pointwise_mul (row st i) v j_f);
        H.mul_commutativity_cr
          (coeff p (Prims.op_Subtraction (Prims.op_Addition m_deg j) (i <: nat)))
          (coeff b (Prims.op_Subtraction (Prims.op_Subtraction n_deg 1) j))
    in
    sum_range_reverse_named g_fp g_bp n_deg h_rev;
    sum_range_split g_bp 0 (L.length b) n_deg;
    sum_range_all_zero g_bp (L.length b) n_deg
      (fun (r: nat{L.length b <= r /\ r < n_deg}) ->
        assert (coeff b r == (zero <: t));
        H.zero_mul_x (coeff p (Prims.op_Subtraction kk r)));
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
      (fun (r:nat) -> reflexivity (coeff b r * coeff p (Prims.op_Subtraction kk r)));

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
    let f_sh : nat -> t = fun (j:nat) -> g_fq (Prims.op_Addition j n_deg) in
    sum_range_shift g_fq n_deg 0 m_deg;
    let g_aq (r:nat) : t = coeff a r * coeff q (Prims.op_Subtraction kk r) in
    let g_rev (j:nat) : t = if m_deg > 0 && j < m_deg
      then g_aq (Prims.op_Subtraction (Prims.op_Subtraction m_deg 1) j)
      else (zero <: t) in
    let neg_g_rev : nat -> t = fun (j:nat) -> neg (g_rev j) in
    sum_range_congruence f_sh neg_g_rev 0 m_deg
      (fun (j: nat{0 <= j /\ j < m_deg}) ->
        let jj : fin size = (Prims.op_Addition j n_deg <: fin size) in
        assert (f_sh j == pointwise_mul (row st i) v jj);
        H.neg_mul_r
          (coeff q (Prims.op_Subtraction (Prims.op_Addition j n_deg) (i <: nat)))
          (coeff a (Prims.op_Subtraction (Prims.op_Subtraction m_deg 1) j));
        H.mul_commutativity_cr
          (coeff q (Prims.op_Subtraction (Prims.op_Addition j n_deg) (i <: nat)))
          (coeff a (Prims.op_Subtraction (Prims.op_Subtraction m_deg 1) j));
        neg_congruence
          (coeff q (Prims.op_Subtraction (Prims.op_Addition j n_deg) (i <: nat)) *
           coeff a (Prims.op_Subtraction (Prims.op_Subtraction m_deg 1) j))
          (coeff a (Prims.op_Subtraction (Prims.op_Subtraction m_deg 1) j) *
           coeff q (Prims.op_Subtraction (Prims.op_Addition j n_deg) (i <: nat)));
        transitivity (f_sh j)
          (neg (coeff q (Prims.op_Subtraction (Prims.op_Addition j n_deg) (i <: nat)) *
                coeff a (Prims.op_Subtraction (Prims.op_Subtraction m_deg 1) j)))
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
        H.zero_mul_x (coeff q (Prims.op_Subtraction kk r)));
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
      (fun (r:nat) -> reflexivity (coeff a r * coeff q (Prims.op_Subtraction kk r)));
    neg_congruence (sum_range g_aq 0 (L.length a)) (coeff (poly_mul a q) kk);

    add_congruence (fin_sum f_p) (fin_sum f_q)
                   (coeff (poly_mul b p) kk) (neg (coeff (poly_mul a q) kk));
    assert (fin_sum pw = (zero <: t));
    assert (pw == pointwise_mul (row st i) v);
    vdot_zero_via_name #t #cr #size (row st i) v pw
#pop-options

(* Main theorem: forward direction of L4 *)
#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let resultant_zero_of_common_divisor (#t:Type) {| f: field t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (p q g: polynomial t)
  : Lemma (requires
      Some? (poly_deg p) /\ Some?.v (poly_deg p) <= m_deg /\
      Some? (poly_deg q) /\ Some?.v (poly_deg q) <= n_deg /\
      divides g p /\
      divides g q /\
      Some? (poly_deg g) /\ Some?.v (poly_deg g) >= 1)
    (ensures resultant m_deg n_deg p q = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let size : pos = Prims.op_Addition m_deg n_deg in
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
    let deg_b = Some?.v (poly_deg b) in
    leading_coeff_nonzero b;
    let k : fin size = Prims.op_Subtraction (Prims.op_Subtraction n_deg 1) deg_b in
    assert (v k == coeff b deg_b);
    assert (is_nonzero (v k));
    null_vec_implies_det_zero st v k;
    det_transpose sm;
    transitivity (det sm) (det st) (zero <: t)
#pop-options