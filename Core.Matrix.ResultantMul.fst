module Core.Matrix.ResultantMul

(*
   Sylvester-as-linear-map bridge (step toward resultant multiplicativity /
   the linear-factor peeling lemma for the Poisson product formula).

   The Sylvester matrix  S = sylvester_matrix m n P Q  (size N = m+n) is the
   matrix, in the monomial bases, of the linear map

       phi_{P,Q} : (u, v)  |->  u*P + v*Q,      deg u < n,  deg v < m,

   landing in  k[x]_{<m+n}.  Concretely this module proves the ACTION identity:
   feeding S^T the "combination coefficient vector"  combo_vec u v  (the
   coefficients of u and v laid out reversed, u in the first n slots, v in the
   last m slots) reproduces the coefficients of  u*P + v*Q :

       vector_dot (row (transpose S) i) (combo_vec u v)
         = coeff (poly_add (poly_mul u P) (poly_mul v Q)) (N - 1 - i).

   This is the field-agnostic, reusable bridge that the resultant
   multiplicativity proof (det_mul of the composed maps) rests on.  It is the
   `+`-version of the kernel computation already used for the resultant-
   vanishing direction in Core.Matrix.Resultant (syl_null_vec_is_null), here
   stated as a forward map identity over a commutative ring.
*)

module TC = FStar.Tactics.Typeclasses
module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Helpers
open Core.Algebra.Combinators
open Core.FinSum
open Core.Permutation
open Core.Matrix
open Core.Matrix.Sylvester
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Vector

(* ----------------------------------------------------------------- *)
(*  The combination coefficient vector.                              *)
(*    slot j < n   : coeff u (n-1-j)      (u laid out, reversed)      *)
(*    slot j >= n  : coeff v (m-1-(j-n))  (v laid out, reversed)      *)
(* ----------------------------------------------------------------- *)

let combo_vec (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (u v: polynomial t)
  : vector t (Prims.op_Addition m_deg n_deg)
  = fun (j: fin (Prims.op_Addition m_deg n_deg)) ->
      if (j <: nat) < n_deg
      then coeff u (Prims.op_Subtraction (Prims.op_Subtraction n_deg 1) (j <: nat))
      else coeff v (Prims.op_Subtraction (Prims.op_Subtraction m_deg 1)
                     (Prims.op_Subtraction (j <: nat) n_deg))

(* vector_dot via a named pointwise function: mirrors
   Core.Matrix.Resultant.vdot_zero_via_name but for an arbitrary value. *)
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
(*  Proof mirrors Core.Matrix.Resultant.syl_null_vec_is_null, but    *)
(*  with the v-part entering with `+` (no negation), so the two      *)
(*  halves assemble to coeff(u*P) + coeff(v*Q) = coeff(u*P + v*Q).   *)
(* ----------------------------------------------------------------- *)

#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"
let sylvester_action (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (p q u v: polynomial t)
  (i: fin (Prims.op_Addition m_deg n_deg))
  : Lemma
    (requires L.length u <= n_deg /\ L.length v <= m_deg)
    (ensures  vector_dot (row (transpose (sylvester_matrix m_deg n_deg p q)) i)
                         (combo_vec m_deg n_deg u v)
            = coeff (poly_add (poly_mul u p) (poly_mul v q))
                    (Prims.op_Subtraction (Prims.op_Subtraction (Prims.op_Addition m_deg n_deg) 1) (i <: nat)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let size : pos = Prims.op_Addition m_deg n_deg in
    let st = transpose (sylvester_matrix m_deg n_deg p q) in
    let vv  = combo_vec m_deg n_deg u v in
    let kk : nat = Prims.op_Subtraction (Prims.op_Subtraction size 1) (i <: nat) in
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
    reflexivity (sum_range g_fp 0 n_deg);
    add_congruence (sum_range g_fp 0 n_deg) (sum_range g_fp n_deg size)
                   (sum_range g_fp 0 n_deg) (zero <: t);
    H.x_plus_zero (sum_range g_fp 0 n_deg);
    symmetry (sum_range g_fp 0 size) (sum_range g_fp 0 n_deg + sum_range g_fp n_deg size);
    transitivity (sum_range g_fp 0 size)
                 (sum_range g_fp 0 n_deg + sum_range g_fp n_deg size)
                 (sum_range g_fp 0 n_deg + (zero <: t));
    transitivity (sum_range g_fp 0 size)
                 (sum_range g_fp 0 n_deg + (zero <: t))
                 (sum_range g_fp 0 n_deg);
    transitivity (fin_sum f_p) (sum_range g_fp 0 size) (sum_range g_fp 0 n_deg);
    let g_up (r:nat) : t = coeff u r * coeff p (Prims.op_Subtraction kk r) in
    let h_rev (j: nat{j < n_deg})
      : Lemma (g_fp j = g_up (Prims.op_Subtraction (Prims.op_Subtraction n_deg 1) j))
      = assert ((j <: nat) < n_deg);
        let j_f : fin size = (j <: fin size) in
        assert (g_fp j == pointwise_mul (row st i) vv j_f);
        H.mul_commutativity_cr
          (coeff p (Prims.op_Subtraction (Prims.op_Addition m_deg j) (i <: nat)))
          (coeff u (Prims.op_Subtraction (Prims.op_Subtraction n_deg 1) j))
    in
    sum_range_reverse_named g_fp g_up n_deg h_rev;
    sum_range_split g_up 0 (L.length u) n_deg;
    sum_range_all_zero g_up (L.length u) n_deg
      (fun (r: nat{L.length u <= r /\ r < n_deg}) ->
        assert (coeff u r == (zero <: t));
        H.zero_mul_x (coeff p (Prims.op_Subtraction kk r)));
    reflexivity (sum_range g_up 0 (L.length u));
    add_congruence (sum_range g_up 0 (L.length u)) (sum_range g_up (L.length u) n_deg)
                   (sum_range g_up 0 (L.length u)) (zero <: t);
    H.x_plus_zero (sum_range g_up 0 (L.length u));
    symmetry (sum_range g_up 0 n_deg) (sum_range g_up 0 (L.length u) + sum_range g_up (L.length u) n_deg);
    transitivity (sum_range g_up 0 n_deg)
                 (sum_range g_up 0 (L.length u) + sum_range g_up (L.length u) n_deg)
                 (sum_range g_up 0 (L.length u) + (zero <: t));
    transitivity (sum_range g_up 0 n_deg)
                 (sum_range g_up 0 (L.length u) + (zero <: t))
                 (sum_range g_up 0 (L.length u));
    coeff_poly_mul_named u p kk g_up
      (fun (r:nat) -> reflexivity (coeff u r * coeff p (Prims.op_Subtraction kk r)));
    symmetry (coeff (poly_mul u p) kk) (sum_range g_up 0 (L.length u));
    transitivity (fin_sum f_p) (sum_range g_fp 0 n_deg) (sum_range g_up 0 n_deg);
    transitivity (fin_sum f_p) (sum_range g_up 0 n_deg) (sum_range g_up 0 (L.length u));
    transitivity (fin_sum f_p) (sum_range g_up 0 (L.length u)) (coeff (poly_mul u p) kk);

    (* ========== Q-half: fin_sum f_q = coeff(v*q, kk) ========== *)
    let g_fq (j:nat) : t = if j >= n_deg && j < size
      then pointwise_mul (row st i) vv (j <: fin size)
      else (zero <: t) in
    fin_sum_eq_sum_range f_q g_fq;
    sum_range_split g_fq 0 n_deg size;
    sum_range_all_zero g_fq 0 n_deg
      (fun (k: nat{0 <= k /\ k < n_deg}) -> reflexivity (zero <: t));
    reflexivity (sum_range g_fq n_deg size);
    add_congruence (sum_range g_fq 0 n_deg) (sum_range g_fq n_deg size)
                   (zero <: t) (sum_range g_fq n_deg size);
    H.zero_plus_x (sum_range g_fq n_deg size);
    symmetry (sum_range g_fq 0 size) (sum_range g_fq 0 n_deg + sum_range g_fq n_deg size);
    transitivity (sum_range g_fq 0 size)
                 (sum_range g_fq 0 n_deg + sum_range g_fq n_deg size)
                 ((zero <: t) + sum_range g_fq n_deg size);
    transitivity (sum_range g_fq 0 size)
                 ((zero <: t) + sum_range g_fq n_deg size)
                 (sum_range g_fq n_deg size);
    transitivity (fin_sum f_q) (sum_range g_fq 0 size) (sum_range g_fq n_deg size);
    let f_sh : nat -> t = fun (j:nat) -> g_fq (Prims.op_Addition j n_deg) in
    sum_range_shift g_fq n_deg 0 m_deg;
    symmetry (sum_range f_sh 0 m_deg) (sum_range g_fq n_deg size);
    transitivity (fin_sum f_q) (sum_range g_fq n_deg size) (sum_range f_sh 0 m_deg);
    let g_vq (r:nat) : t = coeff v r * coeff q (Prims.op_Subtraction kk r) in
    let g_rev (j:nat) : t = if m_deg > 0 && j < m_deg
      then g_vq (Prims.op_Subtraction (Prims.op_Subtraction m_deg 1) j)
      else (zero <: t) in
    sum_range_congruence f_sh g_rev 0 m_deg
      (fun (j: nat{0 <= j /\ j < m_deg}) ->
        let jj : fin size = (Prims.op_Addition j n_deg <: fin size) in
        assert (f_sh j == pointwise_mul (row st i) vv jj);
        H.mul_commutativity_cr
          (coeff q (Prims.op_Subtraction (Prims.op_Addition j n_deg) (i <: nat)))
          (coeff v (Prims.op_Subtraction (Prims.op_Subtraction m_deg 1) j))
      );
    transitivity (fin_sum f_q) (sum_range f_sh 0 m_deg) (sum_range g_rev 0 m_deg);
    sum_range_reverse_named g_rev g_vq m_deg
      (fun (j: nat{j < m_deg}) -> reflexivity (g_rev j));
    transitivity (fin_sum f_q) (sum_range g_rev 0 m_deg) (sum_range g_vq 0 m_deg);
    sum_range_split g_vq 0 (L.length v) m_deg;
    sum_range_all_zero g_vq (L.length v) m_deg
      (fun (r: nat{L.length v <= r /\ r < m_deg}) ->
        assert (coeff v r == (zero <: t));
        H.zero_mul_x (coeff q (Prims.op_Subtraction kk r)));
    reflexivity (sum_range g_vq 0 (L.length v));
    add_congruence (sum_range g_vq 0 (L.length v)) (sum_range g_vq (L.length v) m_deg)
                   (sum_range g_vq 0 (L.length v)) (zero <: t);
    H.x_plus_zero (sum_range g_vq 0 (L.length v));
    symmetry (sum_range g_vq 0 m_deg) (sum_range g_vq 0 (L.length v) + sum_range g_vq (L.length v) m_deg);
    transitivity (sum_range g_vq 0 m_deg)
                 (sum_range g_vq 0 (L.length v) + sum_range g_vq (L.length v) m_deg)
                 (sum_range g_vq 0 (L.length v) + (zero <: t));
    transitivity (sum_range g_vq 0 m_deg)
                 (sum_range g_vq 0 (L.length v) + (zero <: t))
                 (sum_range g_vq 0 (L.length v));
    transitivity (fin_sum f_q) (sum_range g_vq 0 m_deg) (sum_range g_vq 0 (L.length v));
    coeff_poly_mul_named v q kk g_vq
      (fun (r:nat) -> reflexivity (coeff v r * coeff q (Prims.op_Subtraction kk r)));
    symmetry (coeff (poly_mul v q) kk) (sum_range g_vq 0 (L.length v));
    transitivity (fin_sum f_q) (sum_range g_vq 0 (L.length v)) (coeff (poly_mul v q) kk);

    (* ===== assemble: fin_sum pw = coeff(u*p) + coeff(v*q) = coeff(u*p + v*q) ===== *)
    add_congruence (fin_sum f_p) (fin_sum f_q)
                   (coeff (poly_mul u p) kk) (coeff (poly_mul v q) kk);
    (* fin_sum pw = fin_sum f_p + fin_sum f_q = coeff(u*p) + coeff(v*q) *)
    transitivity (fin_sum pw) (fin_sum f_p + fin_sum f_q)
                 (coeff (poly_mul u p) kk + coeff (poly_mul v q) kk);
    vdot_via_name #t #cr #size (row st i) vv pw
                  (coeff (poly_mul u p) kk + coeff (poly_mul v q) kk);
    poly_add_coeff (poly_mul u p) (poly_mul v q) kk;
    symmetry (coeff (poly_add (poly_mul u p) (poly_mul v q)) kk)
             (coeff (poly_mul u p) kk + coeff (poly_mul v q) kk);
    transitivity (vector_dot (row st i) vv)
                 (coeff (poly_mul u p) kk + coeff (poly_mul v q) kk)
                 (coeff (poly_add (poly_mul u p) (poly_mul v q)) kk)
#pop-options
