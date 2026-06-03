module Core.Matrix.ResultantPeel

(*
   Linear-factor PEELING lemma for the resultant (Poisson induction step):

       Res_{m+1,n}((x - a)*A, B) = poly_eval B a * Res_{m,n}(A, B)

   (formal degrees deg A <= m, deg B <= n, B nonzero, N := m+n).

   Strategy (det_mul + the matrices' determinants computed elsewhere):
   the Sylvester matrix  S' = sylvester_matrix (m+1) n ((x-a)A) B  (size N+1)
   factors as a MATRIX PRODUCT

       S' = matrix_mul Mul' C ,

   where (in the descending-degree monomial layout the Sylvester matrix uses)

     * Mul' = sylvester_matrix 1 N (x-a) B   (size N+1): the
       multiplication-by-(x-a) block with B in the last q-row;
       det Mul' = Res_{1,N}(x-a, B) = poly_eval B a  (resultant_linear_formal).

     * C = block_diag_corner1 (sylvester_matrix m n A B): the (N+1) matrix that
       is Syl_{m,n}(A,B) on the top-left NxN block, 1 at corner (N,N), 0 in the
       last row/col off the corner;  det C = det Syl_{m,n}(A,B) = Res_{m,n}(A,B)
       (block_diag_corner1_det, one Laplace expansion along the last row).

   The entrywise identity  S' = matrix_mul Mul' C  is proved by collapsing the
   inner sum  Σ_k Mul'[i][k] * C[k][j]:  the (x-a)-rows of Mul' are bidiagonal
   (only k = i, i+1 survive) and the convolution
       coeff ((x-a)*A) r = coeff A (r-1) - a * coeff A r
   reproduces the p-rows of S';  the q-row of Mul' (= B) picks out column j of C
   and reproduces the q-rows of S'.  Then

       det S' = det (Mul' C) = det Mul' * det C = poly_eval B a * Res_{m,n}(A,B).
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
open Core.Matrix
open Core.Matrix.Determinant
open Core.Matrix.Determinant.Mul
open Core.Matrix.Triangular
open Core.Matrix.Sylvester
open Core.Matrix.Resultant
open Core.Matrix.ResultantLinear
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Div
open Core.Polynomial.Eval
open Core.Polynomial.Root
open Core.Tactics.CanonRing

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
  : Lemma (coeff (poly_mul (poly_linear #t #f a) bigA) k
         = coeff bigA (Prims.op_Subtraction k 1) + (neg a) * coeff bigA k)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    let pl = poly_linear #t #f a in
    assert (L.length pl == 2);
    let g (i:nat) : t = coeff pl i * coeff bigA (Prims.op_Subtraction k i) in
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
    assert (coeff pl 0 == (neg a <: t));
    reflexivity (coeff bigA k);
    mul_congruence (coeff pl 0) (coeff bigA k) (neg a) (coeff bigA k);
    assert (g 0 == coeff pl 0 * coeff bigA (Prims.op_Subtraction k 0));
    assert (Prims.op_Subtraction k 0 == k);
    transitivity (g 0) (coeff pl 0 * coeff bigA k) ((neg a) * coeff bigA k);
    (* g 1 = coeff pl 1 * coeff A (k-1) = one * coeff A (k-1) = coeff A (k-1) *)
    assert (coeff pl 1 == (one <: t));
    reflexivity (coeff bigA (Prims.op_Subtraction k 1));
    mul_congruence (coeff pl 1) (coeff bigA (Prims.op_Subtraction k 1))
                   (one <: t) (coeff bigA (Prims.op_Subtraction k 1));
    H.one_mul_x (coeff bigA (Prims.op_Subtraction k 1));
    transitivity (g 1) (coeff pl 1 * coeff bigA (Prims.op_Subtraction k 1))
                 ((one <: t) * coeff bigA (Prims.op_Subtraction k 1));
    transitivity (g 1) ((one <: t) * coeff bigA (Prims.op_Subtraction k 1))
                 (coeff bigA (Prims.op_Subtraction k 1));
    (* g 0 + g 1 = (neg a)*coeff A k + coeff A (k-1) = coeff A (k-1) + (neg a)*coeff A k *)
    add_congruence (g 0) (g 1) ((neg a) * coeff bigA k) (coeff bigA (Prims.op_Subtraction k 1));
    transitivity (sum_range g 0 2) (g 0 + g 1)
                 ((neg a) * coeff bigA k + coeff bigA (Prims.op_Subtraction k 1));
    comm_helper (neg a) (coeff bigA k) (coeff bigA (Prims.op_Subtraction k 1));
    transitivity (sum_range g 0 2)
                 ((neg a) * coeff bigA k + coeff bigA (Prims.op_Subtraction k 1))
                 (coeff bigA (Prims.op_Subtraction k 1) + (neg a) * coeff bigA k);
    symmetry (coeff (poly_mul pl bigA) k) (sum_range g 0 2);
    transitivity (coeff (poly_mul pl bigA) k) (sum_range g 0 2)
                 (coeff bigA (Prims.op_Subtraction k 1) + (neg a) * coeff bigA k)

(* ================================================================ *)
(*  block_diag_corner1 S  =  [ S  0 ]                                *)
(*                           [ 0  1 ]   (size N+1; S is the NxN block) *)
(*  det (block_diag_corner1 S) = det S  (Laplace along the last row). *)
(* ================================================================ *)

let block_diag_corner1 (#t:Type) {| cr: commutative_ring t |} (#bigN: pos)
  (s: square_matrix t bigN)
  : square_matrix t (Prims.op_Addition bigN 1)
  = fun (i j: fin (Prims.op_Addition bigN 1)) ->
      if (i <: nat) < bigN && (j <: nat) < bigN
      then s (i <: fin bigN) (j <: fin bigN)
      else if (i <: nat) = bigN && (j <: nat) = bigN then (one <: t)
      else (zero <: t)

(* the (N,N) minor of block_diag_corner1 S is exactly S. *)
let minor_corner_is_block (#t:Type) {| cr: commutative_ring t |} (#bigN: pos)
  (s: square_matrix t bigN) (a b: fin bigN)
  : Lemma (minor (block_diag_corner1 #t #cr #bigN s)
                 (bigN <: fin (Prims.op_Addition bigN 1)) (bigN <: fin (Prims.op_Addition bigN 1))
                 a b
         == s a b)
  = ()   (* minor[a][b] = C (skip N a)(skip N b) = C a b = s a b  (a,b < N) *)

(* off-corner entries of the last row vanish ==> their cofactors vanish. *)
let block_corner_cofactor_off (#t:Type) {| cr: commutative_ring t |} (#bigN: pos)
  (s: square_matrix t bigN) (k: fin (Prims.op_Addition bigN 1))
  : Lemma (requires (k <: nat) < bigN)
          (ensures cofactor_term (block_diag_corner1 #t #cr #bigN s)
                                 (bigN <: fin (Prims.op_Addition bigN 1)) k = (zero <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let n : pos = Prims.op_Addition bigN 1 in
    let c = block_diag_corner1 #t #cr #bigN s in
    let nn : fin n = (bigN <: fin n) in
    let mp = minus_one_pow #t #cr (Prims.op_Addition (nn <: nat) (k <: nat)) in
    let dm = det #t #cr #(Prims.op_Subtraction (Prims.op_Addition bigN 1) 1) (minor c nn k) in
    assert (c nn k == (zero <: t));                  (* i=N, j=k<N => zero *)
    reflexivity mp;
    mul_congruence mp (c nn k) mp (zero <: t);
    H.x_mul_zero mp;
    transitivity (mp * c nn k) (mp * (zero <: t)) (zero <: t);
    reflexivity dm;
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
  : Lemma (det (block_diag_corner1 #t #cr #bigN s) = det s)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let c = block_diag_corner1 #t #cr #bigN s in
    let nn : fin (Prims.op_Addition bigN 1) = (bigN <: fin (Prims.op_Addition bigN 1)) in
    det_laplace_row c nn;                             (* det c = fin_sum (cofactor_term c N) *)
    (* fin_sum (cofactor_term c N) = cofactor_term c N N: collapse along last row, inlined
       so the fin_sum term is literally `cofactor_term c nn` (matching det_laplace_row). *)
    let hoff (k: fin (Prims.op_Addition bigN 1){(k <: nat) <> (nn <: nat)})
      : Lemma (cofactor_term c nn k = (zero <: t))
      = assert ((k <: nat) < bigN);
        block_corner_cofactor_off #t #cr #bigN s k
    in
    fin_sum_collapse_at #t #cr #(Prims.op_Addition bigN 1) (cofactor_term c nn) nn hoff;
    (* cofactor_term c N N = minus_one_pow (2N) * c N N * det (minor c N N)
                           = one * one * det s = det s *)
    let mp = minus_one_pow #t #cr (Prims.op_Addition (nn <: nat) (nn <: nat)) in
    assert (Prims.op_Modulus (Prims.op_Addition (nn <: nat) (nn <: nat)) 2 = 0);
    assert (mp == (one <: t));
    assert (c nn nn == (one <: t));                   (* corner entry = one *)
    (* minor c N N = s pointwise *)
    let minor_eq (a b: fin bigN) : Lemma (minor c nn nn a b = s a b)
      = minor_corner_is_block #t #cr #bigN s a b; reflexivity (s a b) in
    Classical.forall_intro_2 minor_eq;
    det_pointwise_eq #t #cr #bigN (minor c nn nn) s;  (* det (minor c N N) = det s *)
    (* assemble: cofactor = (mp * c N N) * det(minor) = (one*one)*det s = det s *)
    reflexivity (c nn nn);
    mul_congruence mp (c nn nn) (one <: t) (one <: t);
    H.one_mul_x (one <: t);
    transitivity (mp * c nn nn) ((one <: t) * (one <: t)) (one <: t);
    reflexivity (det #t #cr #(Prims.op_Subtraction (Prims.op_Addition bigN 1) 1) (minor c nn nn));
    mul_congruence (mp * c nn nn) (det #t #cr #(Prims.op_Subtraction (Prims.op_Addition bigN 1) 1) (minor c nn nn))
                   (one <: t) (det #t #cr #(Prims.op_Subtraction (Prims.op_Addition bigN 1) 1) (minor c nn nn));
    H.one_mul_x (det #t #cr #(Prims.op_Subtraction (Prims.op_Addition bigN 1) 1) (minor c nn nn));
    transitivity ((mp * c nn nn) * det #t #cr #(Prims.op_Subtraction (Prims.op_Addition bigN 1) 1) (minor c nn nn))
                 ((one <: t) * det #t #cr #(Prims.op_Subtraction (Prims.op_Addition bigN 1) 1) (minor c nn nn))
                 (det #t #cr #(Prims.op_Subtraction (Prims.op_Addition bigN 1) 1) (minor c nn nn));
    (* det (minor c N N) = det s *)
    transitivity ((mp * c nn nn) * det #t #cr #(Prims.op_Subtraction (Prims.op_Addition bigN 1) 1) (minor c nn nn))
                 (det #t #cr #(Prims.op_Subtraction (Prims.op_Addition bigN 1) 1) (minor c nn nn))
                 (det s);
    (* cofactor_term c N N == (mp * c N N) * det(minor) *)
    transitivity (det c)
                 (fin_sum #t #(acg_of_r t #cr.cr_r) #(Prims.op_Addition bigN 1) (cofactor_term c nn))
                 (cofactor_term c nn nn);
    transitivity (det c) (cofactor_term c nn nn)
                 ((mp * c nn nn) * det #t #cr #(Prims.op_Subtraction (Prims.op_Addition bigN 1) 1) (minor c nn nn));
    transitivity (det c)
                 ((mp * c nn nn) * det #t #cr #(Prims.op_Subtraction (Prims.op_Addition bigN 1) 1) (minor c nn nn))
                 (det s)

(* ================================================================ *)
(*  Piece #2:  det Mul' = poly_eval b a,  where                     *)
(*    Mul' = sylvester_matrix 1 N (x-a) b   (formal degree N >= deg b). *)
(*  Immediate from resultant_linear_formal (Task 1).                 *)
(* ================================================================ *)

let det_mul_block_is_eval (#t:Type) {| f: field t |} (a: t) (b: polynomial t) (bigN: nat{bigN >= 1})
  : Lemma (requires Some? (poly_deg b) /\ Some?.v (poly_deg b) <= bigN)
          (ensures (let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
                    det (sylvester_matrix #t #cr 1 bigN (poly_linear #t #f a) b) = poly_eval b a))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    resultant_linear_formal #t #f a b bigN;                (* resultant 1 N (x-a) b = poly_eval b a *)
    resultant_unfold #t #cr 1 bigN (poly_linear #t #f a) b (* resultant 1 N (x-a) b == det Mul' *)

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
  : square_matrix t (Prims.op_Addition (Prims.op_Addition m n) 1)
  = let bigNp1 = Prims.op_Addition (Prims.op_Addition m n) 1 in
    fun (i k: fin bigNp1) ->
      if (i <: nat) = (k <: nat) then (one <: t)
      else if (i <: nat) >= n && (i <: nat) < Prims.op_Addition m n
              && (k <: nat) = Prims.op_Addition (i <: nat) 1 then (neg a <: t)
      else (zero <: t)

let peel_L_upper_triangular (#t:Type) {| cr: commutative_ring t |} (a: t) (m n: nat{n >= 1})
  : Lemma (is_upper_triangular (peel_L #t #cr a m n))
  = H.elim_equatable_laws t ()    (* L[i][k] = 0 when i > k (diag or i+1 superdiag only) *)

let peel_L_diag_one (#t:Type) {| cr: commutative_ring t |} (a: t) (m n: nat{n >= 1})
  (i: fin (Prims.op_Addition (Prims.op_Addition m n) 1))
  : Lemma (peel_L #t #cr a m n i i = (one <: t))
  = H.elim_equatable_laws t ()

let det_peel_L (#t:Type) {| cr: commutative_ring t |} (a: t) (m n: nat{n >= 1})
  : Lemma (det (peel_L #t #cr a m n) = (one <: t))
  = peel_L_upper_triangular #t #cr a m n;
    Classical.forall_intro (peel_L_diag_one #t #cr a m n);
    det_unipotent_upper_triangular (peel_L #t #cr a m n)

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
        reflexivity (col rmat j k);
        mul_congruence (lmat i i0) (col rmat j k) v0 (col rmat j k);  (* lhs = v0 * rmat i0 j = c0 *)
        H.one_mul_x c0;
        H.zero_mul_x c1;
        add_congruence (fin_kronecker_delta i0 k * c0) (fin_kronecker_delta i1 k * c1) c0 (zero <: t);
        H.x_plus_zero c0;
        transitivity rhs (c0 + (zero <: t)) c0;
        transitivity lhs (v0 * col rmat j k) c0;   (* lhs == lmat i i0 * col = v0*rmat i0 j = c0 *)
        symmetry lhs c0;
        transitivity rhs c0 lhs;
        symmetry rhs lhs
      end else if (k <: nat) = (i1 <: nat) then begin
        kronecker_delta_neq #t (i0 <: nat) (k <: nat);
        kronecker_delta_eq #t (i1 <: nat) (k <: nat);
        assert ((row lmat i) k == lmat i i1);
        assert ((col rmat j) k == rmat i1 j);
        reflexivity (col rmat j k);
        mul_congruence (lmat i i1) (col rmat j k) v1 (col rmat j k);
        H.zero_mul_x c0;
        H.one_mul_x c1;
        add_congruence (fin_kronecker_delta i0 k * c0) (fin_kronecker_delta i1 k * c1) (zero <: t) c1;
        H.zero_plus_x c1;
        transitivity rhs ((zero <: t) + c1) c1;
        transitivity lhs (v1 * col rmat j k) c1;
        symmetry lhs c1;
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
        symmetry lhs (zero <: t);
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
    left_two_term_row #t #cr #nn lmat rmat i j i0 i1 v0 (zero <: t);
    (* v0 * rmat i0 j + zero * rmat i1 j = v0 * rmat i0 j *)
    H.zero_mul_x (rmat i1 j);
    reflexivity (v0 * rmat i0 j);
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
        reflexivity (col rmat j k);
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
        reflexivity (col rmat j k);
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
        reflexivity (col rmat j k);
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
        reflexivity (row lmat i k);
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
    reflexivity d0;
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
        reflexivity (col rmat j k);
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
        reflexivity (col rmat j k);
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
        reflexivity (row lmat i k);
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
(*  the SINGLE size  N+1 = Prims.op_Addition (Prims.op_Addition m n) 1 *)
(*  so that matrix_mul instances line up.  (The underlying Sylvester  *)
(*  matrices have sizes 1+N, (m+1)+n, m+n, which are propositionally  *)
(*  equal to N or N+1 but not syntactically; index coercions via the  *)
(*  SMT-discharged `fin` refinement bridge the gap.)                  *)
(* ================================================================ *)

unfold let size_peel (m n: nat) : pos = Prims.op_Addition (Prims.op_Addition m n) 1

(* mat_Mul = sylvester_matrix 1 N (x-a) B  at size N+1. *)
let mat_mul_peel (#t:Type) {| f: field t |} (a: t) (b: polynomial t) (m n: nat{n >= 1})
  : square_matrix t (size_peel m n)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let bigN : nat = Prims.op_Addition m n in
    fun (i j: fin (size_peel m n)) ->
      sylvester_matrix #t #cr 1 bigN (poly_linear #t #f a) b
        ((i <: nat) <: fin (nat_add 1 bigN)) ((j <: nat) <: fin (nat_add 1 bigN))

(* mat_S' = sylvester_matrix (m+1) n ((x-a)*A) B  at size N+1. *)
let mat_sprime_peel (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  : square_matrix t (size_peel m n)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    fun (i j: fin (size_peel m n)) ->
      sylvester_matrix #t #cr (Prims.op_Addition m 1) n
        (poly_mul (poly_linear #t #f a) bigA) b
        ((i <: nat) <: fin (nat_add (Prims.op_Addition m 1) n))
        ((j <: nat) <: fin (nat_add (Prims.op_Addition m 1) n))

(* mat_C = block_diag_corner1 (sylvester_matrix m n A B)  (size N+1 already). *)
let mat_c_peel (#t:Type) {| f: field t |} (bigA b: polynomial t) (m n: nat{n >= 1})
  : square_matrix t (size_peel m n)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    block_diag_corner1 #t #cr #(Prims.op_Addition m n) (sylvester_matrix #t #cr m n bigA b)

(* mat_L = peel_L a m n  (size N+1 already). *)
let mat_l_peel (#t:Type) {| f: field t |} (a: t) (m n: nat{n >= 1})
  : square_matrix t (size_peel m n)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    peel_L #t #cr a m n

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
  : Lemma (requires (k <: nat) < Prims.op_Addition m n /\ (k <: nat) = (j <: nat))
          (ensures mat_mul_peel #t #f a b m n k j = (one <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let bigN : nat = Prims.op_Addition m n in
    poly_linear_is_linear_shape #t #f a;
    syl_diag_one #t #cr a (poly_linear #t #f a) b bigN
      ((k <: nat) <: fin (nat_add 1 bigN)) ;
    reflexivity (one <: t)

let mat_mul_super_neg (#t:Type) {| f: field t |} (a: t) (b: polynomial t) (m n: nat{n >= 1})
  (k j: fin (size_peel m n))
  : Lemma (requires (k <: nat) < Prims.op_Addition m n /\ (j <: nat) = Prims.op_Addition (k <: nat) 1)
          (ensures mat_mul_peel #t #f a b m n k j = (neg a <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let bigN : nat = Prims.op_Addition m n in
    poly_linear_is_linear_shape #t #f a;
    syl_super_neg_a #t #cr a (poly_linear #t #f a) b bigN
      ((k <: nat) <: fin (nat_add 1 bigN)) ((j <: nat) <: fin (nat_add 1 bigN));
    reflexivity (neg a <: t)

let mat_mul_lastrow (#t:Type) {| f: field t |} (a: t) (b: polynomial t) (m n: nat{n >= 1})
  (j: fin (size_peel m n))
  : Lemma (mat_mul_peel #t #f a b m n
             ((Prims.op_Addition m n <: nat) <: fin (size_peel m n)) j
         = coeff b (Prims.op_Subtraction (Prims.op_Addition m n) (j <: nat)))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let bigN : nat = Prims.op_Addition m n in
    syl_last_row #t #cr (poly_linear #t #f a) b bigN
      ((j <: nat) <: fin (nat_add 1 bigN));
    reflexivity (coeff b (Prims.op_Subtraction bigN (j <: nat)))

(* off-structure p-row entries vanish *)
let mat_mul_p_other_zero (#t:Type) {| f: field t |} (a: t) (b: polynomial t) (m n: nat{n >= 1})
  (k j: fin (size_peel m n))
  : Lemma (requires (k <: nat) < Prims.op_Addition m n /\
                    (k <: nat) <> (j <: nat) /\
                    (j <: nat) <> Prims.op_Addition (k <: nat) 1)
          (ensures mat_mul_peel #t #f a b m n k j = (zero <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let bigN : nat = Prims.op_Addition m n in
    poly_linear_is_linear_shape #t #f a;
    syl_p_other_zero #t #cr a (poly_linear #t #f a) b bigN
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
  : Lemma (requires (k <: nat) < n /\ (l <: nat) < Prims.op_Addition m n)
          (ensures mat_c_peel #t #f bigA b m n k l
                 = coeff bigA (Prims.op_Subtraction (Prims.op_Addition m (k <: nat)) (l <: nat)))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let bigN : nat = Prims.op_Addition m n in
    (* mat_c_peel k l = Sm[k][l] since k,l < bigN *)
    sylvester_p_block_lookup #t #cr m n bigA b
      ((k <: nat) <: fin (nat_add m n)) ((l <: nat) <: fin (nat_add m n));
    reflexivity (coeff bigA (Prims.op_Subtraction (Prims.op_Addition m (k <: nat)) (l <: nat)))

let mat_c_inner_q (#t:Type) {| f: field t |} (bigA b: polynomial t) (m n: nat{n >= 1})
  (k l: fin (size_peel m n))
  : Lemma (requires (k <: nat) >= n /\ (k <: nat) < Prims.op_Addition m n /\
                    (l <: nat) < Prims.op_Addition m n)
          (ensures mat_c_peel #t #f bigA b m n k l
                 = coeff b (Prims.op_Subtraction (k <: nat) (l <: nat)))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let bigN : nat = Prims.op_Addition m n in
    sylvester_q_block_lookup #t #cr m n bigA b
      ((k <: nat) <: fin (nat_add m n)) ((l <: nat) <: fin (nat_add m n));
    reflexivity (coeff b (Prims.op_Subtraction (k <: nat) (l <: nat)))

let mat_c_corner (#t:Type) {| f: field t |} (bigA b: polynomial t) (m n: nat{n >= 1})
  : Lemma (mat_c_peel #t #f bigA b m n
             ((Prims.op_Addition m n <: nat) <: fin (size_peel m n))
             ((Prims.op_Addition m n <: nat) <: fin (size_peel m n))
         = (one <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    reflexivity (one <: t)

(* last column off corner is zero: C[k][bigN] = 0 for k < bigN *)
let mat_c_lastcol_zero (#t:Type) {| f: field t |} (bigA b: polynomial t) (m n: nat{n >= 1})
  (k: fin (size_peel m n))
  : Lemma (requires (k <: nat) < Prims.op_Addition m n)
          (ensures mat_c_peel #t #f bigA b m n k
                     ((Prims.op_Addition m n <: nat) <: fin (size_peel m n)) = (zero <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    reflexivity (zero <: t)

(* last row off corner is zero: C[bigN][l] = 0 for l < bigN *)
let mat_c_lastrow_zero (#t:Type) {| f: field t |} (bigA b: polynomial t) (m n: nat{n >= 1})
  (l: fin (size_peel m n))
  : Lemma (requires (l <: nat) < Prims.op_Addition m n)
          (ensures mat_c_peel #t #f bigA b m n
                     ((Prims.op_Addition m n <: nat) <: fin (size_peel m n)) l = (zero <: t))
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
  : Lemma (mat_l_peel #t #f a m n i i = (one <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    peel_L_diag_one #t #cr a m n i

let mat_l_super (#t:Type) {| f: field t |} (a: t) (m n: nat{n >= 1})
  (i k: fin (size_peel m n))
  : Lemma (requires (i <: nat) >= n /\ (i <: nat) < Prims.op_Addition m n /\
                    (k <: nat) = Prims.op_Addition (i <: nat) 1)
          (ensures mat_l_peel #t #f a m n i k = (neg a <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    reflexivity (neg a <: t)

(* L row i has only the diagonal (when i < n or i = bigN) or diagonal+super. *)
let mat_l_off_diag_zero (#t:Type) {| f: field t |} (a: t) (m n: nat{n >= 1})
  (i k: fin (size_peel m n))
  : Lemma (requires (k <: nat) <> (i <: nat) /\
                    ~((i <: nat) >= n /\ (i <: nat) < Prims.op_Addition m n
                      /\ (k <: nat) = Prims.op_Addition (i <: nat) 1))
          (ensures mat_l_peel #t #f a m n i k = (zero <: t))
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
          (ensures mat_sprime_peel #t #f a bigA b m n i j
                 = coeff (poly_mul (poly_linear #t #f a) bigA)
                         (Prims.op_Subtraction (Prims.op_Addition (Prims.op_Addition m 1) (i <: nat)) (j <: nat)))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    sylvester_p_block_lookup #t #cr (Prims.op_Addition m 1) n
      (poly_mul (poly_linear #t #f a) bigA) b
      ((i <: nat) <: fin (nat_add (Prims.op_Addition m 1) n))
      ((j <: nat) <: fin (nat_add (Prims.op_Addition m 1) n));
    reflexivity (coeff (poly_mul (poly_linear #t #f a) bigA)
                       (Prims.op_Subtraction (Prims.op_Addition (Prims.op_Addition m 1) (i <: nat)) (j <: nat)))

let mat_sprime_q (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires (i <: nat) >= n)
          (ensures mat_sprime_peel #t #f a bigA b m n i j
                 = coeff b (Prims.op_Subtraction (i <: nat) (j <: nat)))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    sylvester_q_block_lookup #t #cr (Prims.op_Addition m 1) n
      (poly_mul (poly_linear #t #f a) bigA) b
      ((i <: nat) <: fin (nat_add (Prims.op_Addition m 1) n))
      ((j <: nat) <: fin (nat_add (Prims.op_Addition m 1) n));
    reflexivity (coeff b (Prims.op_Subtraction (i <: nat) (j <: nat)))

(* Generic Mul' column off-row vanishing: rows other than {j, j-1, bigN}
   are zero in column j. *)
let mat_mul_col_off (#t:Type) {| f: field t |} (a: t) (b: polynomial t) (m n: nat{n >= 1})
  (j k: fin (size_peel m n))
  : Lemma (requires (k <: nat) <> (j <: nat) /\
                    (k <: nat) <> Prims.op_Subtraction (j <: nat) 1 /\
                    (k <: nat) <> Prims.op_Addition m n)
          (ensures mat_mul_peel #t #f a b m n k j = (zero <: t))
  = let bigN : nat = Prims.op_Addition m n in
    if (k <: nat) < bigN then begin
      assert ((k <: nat) <> (j <: nat));
      assert ((j <: nat) <> Prims.op_Addition (k <: nat) 1);
      mat_mul_p_other_zero #t #f a b m n k j
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
  : Lemma (let i : fin (size_peel m n) = (Prims.op_Addition m n <: nat) <: fin (size_peel m n) in
           matrix_mul (mat_c_peel #t #f bigA b m n) (mat_mul_peel #t #f a b m n) i j
         = matrix_mul (mat_l_peel #t #f a m n) (mat_sprime_peel #t #f a bigA b m n) i j)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let bigN : nat = Prims.op_Addition m n in
    let sz : pos = size_peel m n in
    let i : fin sz = (bigN <: nat) <: fin sz in
    let cmat = mat_c_peel #t #f bigA b m n in
    let mul  = mat_mul_peel #t #f a b m n in
    let lmat = mat_l_peel #t #f a m n in
    let sp   = mat_sprime_peel #t #f a bigA b m n in
    (* ----- LHS: collapse on C row i (single corner entry one at column bigN). ----- *)
    let corner : fin sz = (bigN <: nat) <: fin sz in
    mat_c_corner #t #f bigA b m n;                       (* C[bigN][bigN] = one *)
    let off_c (k: fin sz{(k <: nat) <> (corner <: nat)})
      : Lemma (cmat i k = (zero <: t))
      = mat_c_lastrow_zero #t #f bigA b m n k in          (* C[bigN][k]=0 for k<bigN *)
    Classical.forall_intro (Classical.move_requires off_c);
    left_one_term_row #t #cr #sz cmat mul i j corner (one <: t);
    (* (C*Mul')[i][j] = one * Mul'[bigN][j] *)
    mat_mul_lastrow #t #f a b m n j;                      (* Mul'[bigN][j] = coeff b (bigN - j) *)
    H.one_mul_x (mul corner j);
    (* one * mul corner j = mul corner j = coeff b (bigN - j) *)
    transitivity (matrix_mul cmat mul i j) ((one <: t) * mul corner j) (mul corner j);
    transitivity (matrix_mul cmat mul i j) (mul corner j)
                 (coeff b (Prims.op_Subtraction bigN (j <: nat)));
    (* ----- RHS: collapse on L row i (pure diagonal one at i). ----- *)
    mat_l_diag #t #f a m n i;                             (* L[i][i] = one *)
    let off_l (k: fin sz{(k <: nat) <> (i <: nat)})
      : Lemma (lmat i k = (zero <: t))
      = mat_l_off_diag_zero #t #f a m n i k in            (* i=bigN not in inner block, so off-diag 0 *)
    Classical.forall_intro (Classical.move_requires off_l);
    left_one_term_row #t #cr #sz lmat sp i j i (one <: t);
    (* (L*S')[i][j] = one * S'[i][j] *)
    mat_sprime_q #t #f a bigA b m n i j;                  (* S'[bigN][j] = coeff b (bigN - j) *)
    H.one_mul_x (sp i j);
    transitivity (matrix_mul lmat sp i j) ((one <: t) * sp i j) (sp i j);
    transitivity (matrix_mul lmat sp i j) (sp i j)
                 (coeff b (Prims.op_Subtraction bigN (j <: nat)));
    (* both equal coeff b (bigN - j) *)
    symmetry (matrix_mul lmat sp i j) (coeff b (Prims.op_Subtraction bigN (j <: nat)));
    transitivity (matrix_mul cmat mul i j)
                 (coeff b (Prims.op_Subtraction bigN (j <: nat)))
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
  : Lemma (requires (i <: nat) >= n /\ (i <: nat) < Prims.op_Addition m n)
          (ensures (let lmat = mat_l_peel #t #f a m n in
                    let sp   = mat_sprime_peel #t #f a bigA b m n in
                    matrix_mul lmat sp i j
                  = coeff b (Prims.op_Subtraction (i <: nat) (j <: nat))
                    + (neg a) * coeff b (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) (j <: nat))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let bigN : nat = Prims.op_Addition m n in
    let sz : pos = size_peel m n in
    let lmat = mat_l_peel #t #f a m n in
    let sp   = mat_sprime_peel #t #f a bigA b m n in
    let i1 : fin sz = (Prims.op_Addition (i <: nat) 1 <: nat) <: fin sz in
    mat_l_diag #t #f a m n i;
    mat_l_super #t #f a m n i i1;
    let off_l (k: fin sz{(k <: nat) <> (i <: nat) /\ (k <: nat) <> (i1 <: nat)})
      : Lemma (lmat i k = (zero <: t))
      = mat_l_off_diag_zero #t #f a m n i k in
    Classical.forall_intro (Classical.move_requires off_l);
    left_two_term_row #t #cr #sz lmat sp i j i i1 (one <: t) (neg a <: t);
    mat_sprime_q #t #f a bigA b m n i j;
    mat_sprime_q #t #f a bigA b m n i1 j;
    H.one_mul_x (sp i j);
    reflexivity (neg a <: t);
    mul_congruence (neg a <: t) (sp i1 j) (neg a <: t)
                   (coeff b (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) (j <: nat)));
    add_congruence ((one <: t) * sp i j) ((neg a <: t) * sp i1 j)
                   (coeff b (Prims.op_Subtraction (i <: nat) (j <: nat)))
                   ((neg a <: t) * coeff b (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) (j <: nat)));
    transitivity (matrix_mul lmat sp i j)
                 ((one <: t) * sp i j + (neg a <: t) * sp i1 j)
                 (coeff b (Prims.op_Subtraction (i <: nat) (j <: nat))
                  + (neg a <: t) * coeff b (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) (j <: nat)))
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
  : Lemma (requires (i <: nat) >= n /\ (i <: nat) < Prims.op_Addition m n /\
                    Some? (poly_deg b) /\ Some?.v (poly_deg b) <= n)
          (ensures (let cmat = mat_c_peel #t #f bigA b m n in
                    let mul  = mat_mul_peel #t #f a b m n in
                    matrix_mul cmat mul i j
                  = coeff b (Prims.op_Subtraction (i <: nat) (j <: nat))
                    + (neg a) * coeff b (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) (j <: nat))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let bigN : nat = Prims.op_Addition m n in
    let sz : pos = size_peel m n in
    let cmat = mat_c_peel #t #f bigA b m n in
    let mul  = mat_mul_peel #t #f a b m n in
    let nN : fin sz = (bigN <: nat) <: fin sz in
    let jn : nat = j in
    (* target expression *)
    let tgt = coeff b (Prims.op_Subtraction (i <: nat) jn)
              + (neg a) * coeff b (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) jn) in
    if jn = 0 then begin
      (* column 0: rows {0:one, bigN:coeff b bigN}. *)
      let k0 : fin sz = (0 <: nat) <: fin sz in
      mat_mul_diag_one #t #f a b m n k0 k0;               (* Mul'[0][0] = one *)
      mat_mul_lastrow #t #f a b m n k0;                   (* Mul'[bigN][0] = coeff b bigN *)
      let off (k: fin sz{(k <: nat) <> (k0 <: nat) /\ (k <: nat) <> (nN <: nat)})
        : Lemma (mul k k0 = (zero <: t))
        = mat_mul_col_off #t #f a b m n k0 k in
      Classical.forall_intro (Classical.move_requires off);
      right_two_term_col #t #cr #sz cmat mul i k0 k0 nN (one <: t) (coeff b bigN);
      (* (C*Mul')[i][0] = C[i][0]*one + C[i][bigN]*coeff b bigN *)
      mat_c_inner_q #t #f bigA b m n i k0;                (* C[i][0] = coeff b (i-0) = coeff b i *)
      mat_c_lastcol_zero #t #f bigA b m n i;              (* C[i][bigN] = 0 *)
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
      transitivity (matrix_mul cmat mul i k0)
                   (cmat i k0 * (one <: t) + cmat i nN * coeff b bigN)
                   (coeff b (i <: nat));
      (* now coeff b i = coeff b (i-0) + neg a * coeff b (i+1-0) since coeff b (i+1)=0 *)
      coeff_above_degree #t #cr b (Prims.op_Addition (i <: nat) 1);   (* coeff b (i+1) = 0, i+1 > n >= deg *)
      H.x_mul_zero (neg a);                               (* neg a * 0 = 0 *)
      reflexivity (neg a <: t);
      mul_congruence (neg a <: t) (coeff b (Prims.op_Addition (i <: nat) 1)) (neg a <: t) (zero <: t);
      transitivity ((neg a <: t) * coeff b (Prims.op_Addition (i <: nat) 1))
                   ((neg a <: t) * (zero <: t)) (zero <: t);
      reflexivity (coeff b (i <: nat));
      add_congruence (coeff b (i <: nat)) ((neg a <: t) * coeff b (Prims.op_Addition (i <: nat) 1))
                     (coeff b (i <: nat)) (zero <: t);
      H.x_plus_zero (coeff b (i <: nat));
      transitivity tgt (coeff b (i <: nat) + (zero <: t)) (coeff b (i <: nat));
      symmetry tgt (coeff b (i <: nat));
      transitivity (matrix_mul cmat mul i j) (coeff b (i <: nat)) tgt
    end else if jn = bigN then begin
      (* column bigN: rows {bigN-1:neg a, bigN:coeff b 0}. *)
      let km1 : fin sz = (Prims.op_Subtraction bigN 1 <: nat) <: fin sz in
      mat_mul_super_neg #t #f a b m n km1 j;              (* Mul'[bigN-1][bigN] = neg a (j = (bigN-1)+1) *)
      mat_mul_lastrow #t #f a b m n j;                    (* Mul'[bigN][bigN] = coeff b 0 *)
      let off (k: fin sz{(k <: nat) <> (km1 <: nat) /\ (k <: nat) <> (nN <: nat)})
        : Lemma (mul k j = (zero <: t))
        = mat_mul_col_off #t #f a b m n j k in
      Classical.forall_intro (Classical.move_requires off);
      right_two_term_col #t #cr #sz cmat mul i j km1 nN (neg a <: t)
                         (coeff b (Prims.op_Subtraction bigN (jn))) ;
      (* (C*Mul')[i][bigN] = C[i][bigN-1]*neg a + C[i][bigN]*coeff b 0 *)
      mat_c_inner_q #t #f bigA b m n i km1;               (* C[i][bigN-1] = coeff b (i-(bigN-1)) *)
      mat_c_lastcol_zero #t #f bigA b m n i;              (* C[i][bigN] = 0 *)
      (* C[i][bigN-1]*neg a = neg a * coeff b (i-(bigN-1)) = neg a * coeff b (i+1-bigN) *)
      reflexivity (neg a <: t);
      mul_congruence (cmat i km1) (neg a <: t)
                     (coeff b (Prims.op_Subtraction (i <: nat) (Prims.op_Subtraction bigN 1))) (neg a <: t);
      H.mul_commutativity_cr (coeff b (Prims.op_Subtraction (i <: nat) (Prims.op_Subtraction bigN 1))) (neg a <: t);
      transitivity (cmat i km1 * (neg a <: t))
                   (coeff b (Prims.op_Subtraction (i <: nat) (Prims.op_Subtraction bigN 1)) * (neg a <: t))
                   ((neg a <: t) * coeff b (Prims.op_Subtraction (i <: nat) (Prims.op_Subtraction bigN 1)));
      (* C[i][bigN]*coeff b 0 = 0 *)
      H.zero_mul_x (coeff b (Prims.op_Subtraction bigN jn));
      mul_congruence (cmat i nN) (coeff b (Prims.op_Subtraction bigN jn)) (zero <: t)
                     (coeff b (Prims.op_Subtraction bigN jn));
      transitivity (cmat i nN * coeff b (Prims.op_Subtraction bigN jn))
                   ((zero <: t) * coeff b (Prims.op_Subtraction bigN jn)) (zero <: t);
      add_congruence (cmat i km1 * (neg a <: t)) (cmat i nN * coeff b (Prims.op_Subtraction bigN jn))
                     ((neg a <: t) * coeff b (Prims.op_Subtraction (i <: nat) (Prims.op_Subtraction bigN 1)))
                     (zero <: t);
      H.x_plus_zero ((neg a <: t) * coeff b (Prims.op_Subtraction (i <: nat) (Prims.op_Subtraction bigN 1)));
      transitivity (cmat i km1 * (neg a <: t) + cmat i nN * coeff b (Prims.op_Subtraction bigN jn))
                   ((neg a <: t) * coeff b (Prims.op_Subtraction (i <: nat) (Prims.op_Subtraction bigN 1)) + (zero <: t))
                   ((neg a <: t) * coeff b (Prims.op_Subtraction (i <: nat) (Prims.op_Subtraction bigN 1)));
      transitivity (matrix_mul cmat mul i j)
                   (cmat i km1 * (neg a <: t) + cmat i nN * coeff b (Prims.op_Subtraction bigN jn))
                   ((neg a <: t) * coeff b (Prims.op_Subtraction (i <: nat) (Prims.op_Subtraction bigN 1)));
      (* tgt = coeff b (i-bigN) + neg a*coeff b (i+1-bigN);  coeff b (i-bigN)=0 (i<bigN). *)
      assert ((i <: nat) - jn < 0);                       (* i < bigN = jn *)
      assert (coeff b (Prims.op_Subtraction (i <: nat) jn) == (zero <: t));   (* negative index *)
      (* i+1-bigN = i - (bigN-1) *)
      assert (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) jn
              == Prims.op_Subtraction (i <: nat) (Prims.op_Subtraction bigN 1));
      reflexivity ((neg a <: t) * coeff b (Prims.op_Subtraction (i <: nat) (Prims.op_Subtraction bigN 1)));
      H.zero_plus_x ((neg a <: t) * coeff b (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) jn));
      symmetry ((neg a <: t) * coeff b (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) jn))
               ((zero <: t) + (neg a <: t) * coeff b (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) jn));
      transitivity (matrix_mul cmat mul i j)
                   ((neg a <: t) * coeff b (Prims.op_Subtraction (i <: nat) (Prims.op_Subtraction bigN 1)))
                   tgt
    end else begin
      (* interior 0 < j < bigN: three-term collapse, rows {j:one, j-1:neg a, bigN:coeff b (bigN-j)} *)
      let k0 : fin sz = (jn <: nat) <: fin sz in
      let k1 : fin sz = (Prims.op_Subtraction jn 1 <: nat) <: fin sz in
      mat_mul_diag_one #t #f a b m n k0 j;                (* Mul'[j][j] = one *)
      mat_mul_super_neg #t #f a b m n k1 j;               (* Mul'[j-1][j] = neg a *)
      mat_mul_lastrow #t #f a b m n j;                    (* Mul'[bigN][j] = coeff b (bigN-j) *)
      let off (k: fin sz{(k <: nat) <> (k0 <: nat) /\ (k <: nat) <> (k1 <: nat) /\ (k <: nat) <> (nN <: nat)})
        : Lemma (mul k j = (zero <: t))
        = mat_mul_col_off #t #f a b m n j k in
      Classical.forall_intro (Classical.move_requires off);
      right_three_term_col #t #cr #sz cmat mul i j k0 k1 nN (one <: t) (neg a <: t)
                           (coeff b (Prims.op_Subtraction bigN jn));
      (* (C*Mul')[i][j] = C[i][j]*one + (C[i][j-1]*neg a + C[i][bigN]*coeff b (bigN-j)) *)
      mat_c_inner_q #t #f bigA b m n i k0;                (* C[i][j] = coeff b (i-j) *)
      mat_c_inner_q #t #f bigA b m n i k1;                (* C[i][j-1] = coeff b (i-(j-1)) = coeff b (i-j+1) *)
      mat_c_lastcol_zero #t #f bigA b m n i;              (* C[i][bigN] = 0 *)
      (* d0 = C[i][j]*one = coeff b (i-j) *)
      H.x_mul_one (cmat i k0);
      transitivity (cmat i k0 * (one <: t)) (cmat i k0) (coeff b (Prims.op_Subtraction (i <: nat) jn));
      (* d1 = C[i][j-1]*neg a = neg a * coeff b (i+1-j) *)
      reflexivity (neg a <: t);
      mul_congruence (cmat i k1) (neg a <: t)
                     (coeff b (Prims.op_Subtraction (i <: nat) (Prims.op_Subtraction jn 1))) (neg a <: t);
      H.mul_commutativity_cr (coeff b (Prims.op_Subtraction (i <: nat) (Prims.op_Subtraction jn 1))) (neg a <: t);
      assert (Prims.op_Subtraction (i <: nat) (Prims.op_Subtraction jn 1)
              == Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) jn);
      transitivity (cmat i k1 * (neg a <: t))
                   (coeff b (Prims.op_Subtraction (i <: nat) (Prims.op_Subtraction jn 1)) * (neg a <: t))
                   ((neg a <: t) * coeff b (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) jn));
      (* d2 = C[i][bigN]*w2 = 0 *)
      H.zero_mul_x (coeff b (Prims.op_Subtraction bigN jn));
      mul_congruence (cmat i nN) (coeff b (Prims.op_Subtraction bigN jn)) (zero <: t)
                     (coeff b (Prims.op_Subtraction bigN jn));
      transitivity (cmat i nN * coeff b (Prims.op_Subtraction bigN jn))
                   ((zero <: t) * coeff b (Prims.op_Subtraction bigN jn)) (zero <: t);
      (* (d1 + d2) = neg a*coeff b (i+1-j) + 0 = neg a*coeff b (i+1-j) *)
      add_congruence (cmat i k1 * (neg a <: t)) (cmat i nN * coeff b (Prims.op_Subtraction bigN jn))
                     ((neg a <: t) * coeff b (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) jn))
                     (zero <: t);
      H.x_plus_zero ((neg a <: t) * coeff b (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) jn));
      transitivity (cmat i k1 * (neg a <: t) + cmat i nN * coeff b (Prims.op_Subtraction bigN jn))
                   ((neg a <: t) * coeff b (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) jn) + (zero <: t))
                   ((neg a <: t) * coeff b (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) jn));
      (* d0 + (d1+d2) = coeff b (i-j) + neg a*coeff b (i+1-j) = tgt *)
      add_congruence (cmat i k0 * (one <: t))
                     (cmat i k1 * (neg a <: t) + cmat i nN * coeff b (Prims.op_Subtraction bigN jn))
                     (coeff b (Prims.op_Subtraction (i <: nat) jn))
                     ((neg a <: t) * coeff b (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) jn));
      transitivity (matrix_mul cmat mul i j)
                   (cmat i k0 * (one <: t)
                    + (cmat i k1 * (neg a <: t) + cmat i nN * coeff b (Prims.op_Subtraction bigN jn)))
                   tgt
    end
#pop-options

(* q-row pointwise identity: combine LHS and RHS. *)
let peel_pointwise_qrow (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires (i <: nat) >= n /\ (i <: nat) < Prims.op_Addition m n /\
                    Some? (poly_deg b) /\ Some?.v (poly_deg b) <= n)
          (ensures matrix_mul (mat_c_peel #t #f bigA b m n) (mat_mul_peel #t #f a b m n) i j
                 = matrix_mul (mat_l_peel #t #f a m n) (mat_sprime_peel #t #f a bigA b m n) i j)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cmat = mat_c_peel #t #f bigA b m n in
    let mul  = mat_mul_peel #t #f a b m n in
    let lmat = mat_l_peel #t #f a m n in
    let sp   = mat_sprime_peel #t #f a bigA b m n in
    let rhsv = coeff b (Prims.op_Subtraction (i <: nat) (j <: nat))
               + (neg a) * coeff b (Prims.op_Subtraction (Prims.op_Addition (i <: nat) 1) (j <: nat)) in
    peel_lhs_qrow #t #f a bigA b m n i j;                 (* (C*Mul')[i][j] = rhsv *)
    peel_rhs_qrow #t #f a bigA b m n i j;                 (* (L*S')[i][j]  = rhsv *)
    symmetry (matrix_mul lmat sp i j) rhsv;
    transitivity (matrix_mul cmat mul i j) rhsv (matrix_mul lmat sp i j)

(* ---------------------------------------------------------------- *)
(*  RHS for a p-row  i < n:  L row i is pure diagonal, so            *)
(*    (L*S')[i][j] = one * S'[i][j] = coeff ((x-a)A) ((m+1)+i-j).    *)
(* ---------------------------------------------------------------- *)
#push-options "--z3rlimit 150 --fuel 1 --ifuel 1"
let peel_rhs_prow (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires (i <: nat) < n)
          (ensures (let lmat = mat_l_peel #t #f a m n in
                    let sp   = mat_sprime_peel #t #f a bigA b m n in
                    matrix_mul lmat sp i j
                  = coeff (poly_mul (poly_linear #t #f a) bigA)
                          (Prims.op_Subtraction (Prims.op_Addition (Prims.op_Addition m 1) (i <: nat)) (j <: nat))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let sz : pos = size_peel m n in
    let lmat = mat_l_peel #t #f a m n in
    let sp   = mat_sprime_peel #t #f a bigA b m n in
    mat_l_diag #t #f a m n i;                             (* L[i][i] = one *)
    let off_l (k: fin sz{(k <: nat) <> (i <: nat)})
      : Lemma (lmat i k = (zero <: t))
      = mat_l_off_diag_zero #t #f a m n i k in            (* i<n: not in inner block, off-diag 0 *)
    Classical.forall_intro (Classical.move_requires off_l);
    left_one_term_row #t #cr #sz lmat sp i j i (one <: t);
    mat_sprime_p #t #f a bigA b m n i j;
    H.one_mul_x (sp i j);
    transitivity (matrix_mul lmat sp i j) ((one <: t) * sp i j) (sp i j);
    transitivity (matrix_mul lmat sp i j) (sp i j)
                 (coeff (poly_mul (poly_linear #t #f a) bigA)
                        (Prims.op_Subtraction (Prims.op_Addition (Prims.op_Addition m 1) (i <: nat)) (j <: nat)))
#pop-options

(* ---------------------------------------------------------------- *)
(*  Bridge:  coeff ((x-a)A) ((m+1)+i-j)                              *)
(*         = coeff A (m+i-j) + neg a * coeff A (m+i-j+1).            *)
(* ---------------------------------------------------------------- *)
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let peel_prow_bridge (#t:Type) {| f: field t |} (a: t) (bigA: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires (i <: nat) < n /\ L.length bigA <= Prims.op_Addition m 1)
          (ensures (let idx_lo : int = Prims.op_Subtraction (Prims.op_Addition m (i <: nat)) (j <: nat) in
                    coeff (poly_mul (poly_linear #t #f a) bigA)
                          (Prims.op_Subtraction (Prims.op_Addition (Prims.op_Addition m 1) (i <: nat)) (j <: nat))
                  = coeff bigA idx_lo + (neg a) * coeff bigA (Prims.op_Addition idx_lo 1)))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let idx_hi : int = Prims.op_Subtraction (Prims.op_Addition (Prims.op_Addition m 1) (i <: nat)) (j <: nat) in
    let idx_lo : int = Prims.op_Subtraction (Prims.op_Addition m (i <: nat)) (j <: nat) in
    let pl = poly_linear #t #f a in
    if idx_hi >= 0 then begin
      let k : nat = idx_hi in
      coeff_linear_mul #t #f a bigA k;
      assert (Prims.op_Subtraction k 1 == idx_lo);
      assert ((k <: int) == Prims.op_Addition idx_lo 1)
    end else begin
      assert (coeff (poly_mul pl bigA) idx_hi == (zero <: t));
      assert (idx_lo < 0);
      assert (coeff bigA idx_lo == (zero <: t));
      assert (Prims.op_Addition idx_lo 1 == idx_hi);
      assert (coeff bigA (Prims.op_Addition idx_lo 1) == (zero <: t));
      H.x_mul_zero (neg a);
      reflexivity (neg a <: t);
      mul_congruence (neg a <: t) (coeff bigA (Prims.op_Addition idx_lo 1)) (neg a <: t) (zero <: t);
      transitivity ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1))
                   ((neg a <: t) * (zero <: t)) (zero <: t);
      reflexivity (coeff bigA idx_lo);
      add_congruence (coeff bigA idx_lo) ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1))
                     (zero <: t) (zero <: t);
      H.x_plus_zero (zero <: t);
      transitivity (coeff bigA idx_lo + (neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1))
                   ((zero <: t) + (zero <: t)) (zero <: t);
      symmetry (coeff bigA idx_lo + (neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1)) (zero <: t);
      transitivity (coeff (poly_mul pl bigA) idx_hi) (zero <: t)
                   (coeff bigA idx_lo + (neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1))
    end
#pop-options

(* ---------------------------------------------------------------- *)
(*  LHS for a p-row  i < n:                                          *)
(*    (C*Mul')[i][j] = coeff A (m+i-j) + neg a * coeff A (m+i-j+1).  *)
(* ---------------------------------------------------------------- *)
#push-options "--z3rlimit 300 --fuel 1 --ifuel 1"
let peel_lhs_prow (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires (i <: nat) < n /\ L.length bigA <= Prims.op_Addition m 1)
          (ensures (let cmat = mat_c_peel #t #f bigA b m n in
                    let mul  = mat_mul_peel #t #f a b m n in
                    let idx_lo : int = Prims.op_Subtraction (Prims.op_Addition m (i <: nat)) (j <: nat) in
                    matrix_mul cmat mul i j
                  = coeff bigA idx_lo + (neg a) * coeff bigA (Prims.op_Addition idx_lo 1)))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let bigN : nat = Prims.op_Addition m n in
    let sz : pos = size_peel m n in
    let cmat = mat_c_peel #t #f bigA b m n in
    let mul  = mat_mul_peel #t #f a b m n in
    let nN : fin sz = (bigN <: nat) <: fin sz in
    let jn : nat = j in
    let idx_lo : int = Prims.op_Subtraction (Prims.op_Addition m (i <: nat)) jn in
    let tgt = coeff bigA idx_lo + (neg a) * coeff bigA (Prims.op_Addition idx_lo 1) in
    if jn = 0 then begin
      let k0 : fin sz = (0 <: nat) <: fin sz in
      mat_mul_diag_one #t #f a b m n k0 k0;
      mat_mul_lastrow #t #f a b m n k0;
      let off (k: fin sz{(k <: nat) <> (k0 <: nat) /\ (k <: nat) <> (nN <: nat)})
        : Lemma (mul k k0 = (zero <: t))
        = mat_mul_col_off #t #f a b m n k0 k in
      Classical.forall_intro (Classical.move_requires off);
      right_two_term_col #t #cr #sz cmat mul i k0 k0 nN (one <: t) (coeff b bigN);
      mat_c_inner_p #t #f bigA b m n i k0;
      mat_c_lastcol_zero #t #f bigA b m n i;
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
      transitivity (matrix_mul cmat mul i k0)
                   (cmat i k0 * (one <: t) + cmat i nN * coeff b bigN) (coeff bigA idx_lo);
      assert (Prims.op_Addition idx_lo 1 == Prims.op_Addition (Prims.op_Addition m (i <: nat)) 1);
      assert (coeff bigA (Prims.op_Addition idx_lo 1) == (zero <: t));
      H.x_mul_zero (neg a);
      reflexivity (neg a <: t);
      mul_congruence (neg a <: t) (coeff bigA (Prims.op_Addition idx_lo 1)) (neg a <: t) (zero <: t);
      transitivity ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1)) ((neg a <: t) * (zero <: t)) (zero <: t);
      reflexivity (coeff bigA idx_lo);
      add_congruence (coeff bigA idx_lo) ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1))
                     (coeff bigA idx_lo) (zero <: t);
      H.x_plus_zero (coeff bigA idx_lo);
      transitivity tgt (coeff bigA idx_lo + (zero <: t)) (coeff bigA idx_lo);
      symmetry tgt (coeff bigA idx_lo);
      transitivity (matrix_mul cmat mul i j) (coeff bigA idx_lo) tgt
    end else if jn = bigN then begin
      let km1 : fin sz = (Prims.op_Subtraction bigN 1 <: nat) <: fin sz in
      mat_mul_super_neg #t #f a b m n km1 j;
      mat_mul_lastrow #t #f a b m n j;
      let off (k: fin sz{(k <: nat) <> (km1 <: nat) /\ (k <: nat) <> (nN <: nat)})
        : Lemma (mul k j = (zero <: t))
        = mat_mul_col_off #t #f a b m n j k in
      Classical.forall_intro (Classical.move_requires off);
      right_two_term_col #t #cr #sz cmat mul i j km1 nN (neg a <: t)
                         (coeff b (Prims.op_Subtraction bigN jn));
      mat_c_inner_p #t #f bigA b m n i km1;
      mat_c_lastcol_zero #t #f bigA b m n i;
      assert (Prims.op_Subtraction (Prims.op_Addition m (i <: nat)) (Prims.op_Subtraction bigN 1)
              == Prims.op_Addition idx_lo 1);
      reflexivity (neg a <: t);
      mul_congruence (cmat i km1) (neg a <: t) (coeff bigA (Prims.op_Addition idx_lo 1)) (neg a <: t);
      H.mul_commutativity_cr (coeff bigA (Prims.op_Addition idx_lo 1)) (neg a <: t);
      transitivity (cmat i km1 * (neg a <: t))
                   (coeff bigA (Prims.op_Addition idx_lo 1) * (neg a <: t))
                   ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1));
      H.zero_mul_x (coeff b (Prims.op_Subtraction bigN jn));
      mul_congruence (cmat i nN) (coeff b (Prims.op_Subtraction bigN jn)) (zero <: t)
                     (coeff b (Prims.op_Subtraction bigN jn));
      transitivity (cmat i nN * coeff b (Prims.op_Subtraction bigN jn))
                   ((zero <: t) * coeff b (Prims.op_Subtraction bigN jn)) (zero <: t);
      add_congruence (cmat i km1 * (neg a <: t)) (cmat i nN * coeff b (Prims.op_Subtraction bigN jn))
                     ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1)) (zero <: t);
      H.x_plus_zero ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1));
      transitivity (cmat i km1 * (neg a <: t) + cmat i nN * coeff b (Prims.op_Subtraction bigN jn))
                   ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1) + (zero <: t))
                   ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1));
      transitivity (matrix_mul cmat mul i j)
                   (cmat i km1 * (neg a <: t) + cmat i nN * coeff b (Prims.op_Subtraction bigN jn))
                   ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1));
      assert (idx_lo == Prims.op_Subtraction (i <: nat) n);
      assert (idx_lo < 0);
      assert (coeff bigA idx_lo == (zero <: t));
      reflexivity ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1));
      H.zero_plus_x ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1));
      symmetry ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1))
               ((zero <: t) + (neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1));
      transitivity (matrix_mul cmat mul i j)
                   ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1)) tgt
    end else begin
      let k0 : fin sz = (jn <: nat) <: fin sz in
      let k1 : fin sz = (Prims.op_Subtraction jn 1 <: nat) <: fin sz in
      mat_mul_diag_one #t #f a b m n k0 j;
      mat_mul_super_neg #t #f a b m n k1 j;
      mat_mul_lastrow #t #f a b m n j;
      let off (k: fin sz{(k <: nat) <> (k0 <: nat) /\ (k <: nat) <> (k1 <: nat) /\ (k <: nat) <> (nN <: nat)})
        : Lemma (mul k j = (zero <: t))
        = mat_mul_col_off #t #f a b m n j k in
      Classical.forall_intro (Classical.move_requires off);
      right_three_term_col #t #cr #sz cmat mul i j k0 k1 nN (one <: t) (neg a <: t)
                           (coeff b (Prims.op_Subtraction bigN jn));
      mat_c_inner_p #t #f bigA b m n i k0;
      mat_c_inner_p #t #f bigA b m n i k1;
      mat_c_lastcol_zero #t #f bigA b m n i;
      H.x_mul_one (cmat i k0);
      transitivity (cmat i k0 * (one <: t)) (cmat i k0) (coeff bigA idx_lo);
      assert (Prims.op_Subtraction (Prims.op_Addition m (i <: nat)) (Prims.op_Subtraction jn 1)
              == Prims.op_Addition idx_lo 1);
      reflexivity (neg a <: t);
      mul_congruence (cmat i k1) (neg a <: t) (coeff bigA (Prims.op_Addition idx_lo 1)) (neg a <: t);
      H.mul_commutativity_cr (coeff bigA (Prims.op_Addition idx_lo 1)) (neg a <: t);
      transitivity (cmat i k1 * (neg a <: t))
                   (coeff bigA (Prims.op_Addition idx_lo 1) * (neg a <: t))
                   ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1));
      H.zero_mul_x (coeff b (Prims.op_Subtraction bigN jn));
      mul_congruence (cmat i nN) (coeff b (Prims.op_Subtraction bigN jn)) (zero <: t)
                     (coeff b (Prims.op_Subtraction bigN jn));
      transitivity (cmat i nN * coeff b (Prims.op_Subtraction bigN jn))
                   ((zero <: t) * coeff b (Prims.op_Subtraction bigN jn)) (zero <: t);
      add_congruence (cmat i k1 * (neg a <: t)) (cmat i nN * coeff b (Prims.op_Subtraction bigN jn))
                     ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1)) (zero <: t);
      H.x_plus_zero ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1));
      transitivity (cmat i k1 * (neg a <: t) + cmat i nN * coeff b (Prims.op_Subtraction bigN jn))
                   ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1) + (zero <: t))
                   ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1));
      add_congruence (cmat i k0 * (one <: t))
                     (cmat i k1 * (neg a <: t) + cmat i nN * coeff b (Prims.op_Subtraction bigN jn))
                     (coeff bigA idx_lo) ((neg a <: t) * coeff bigA (Prims.op_Addition idx_lo 1));
      transitivity (matrix_mul cmat mul i j)
                   (cmat i k0 * (one <: t)
                    + (cmat i k1 * (neg a <: t) + cmat i nN * coeff b (Prims.op_Subtraction bigN jn)))
                   tgt
    end
#pop-options

(* p-row pointwise identity: LHS = pexpr = bridge = S'[i][j] = RHS. *)
#push-options "--z3rlimit 150 --fuel 1 --ifuel 1"
let peel_pointwise_prow (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires (i <: nat) < n /\ L.length bigA <= Prims.op_Addition m 1)
          (ensures matrix_mul (mat_c_peel #t #f bigA b m n) (mat_mul_peel #t #f a b m n) i j
                 = matrix_mul (mat_l_peel #t #f a m n) (mat_sprime_peel #t #f a bigA b m n) i j)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cmat = mat_c_peel #t #f bigA b m n in
    let mul  = mat_mul_peel #t #f a b m n in
    let lmat = mat_l_peel #t #f a m n in
    let sp   = mat_sprime_peel #t #f a bigA b m n in
    let idx_lo : int = Prims.op_Subtraction (Prims.op_Addition m (i <: nat)) (j <: nat) in
    let idx_hi : int = Prims.op_Subtraction (Prims.op_Addition (Prims.op_Addition m 1) (i <: nat)) (j <: nat) in
    let pexpr = coeff bigA idx_lo + (neg a) * coeff bigA (Prims.op_Addition idx_lo 1) in
    let prodc = coeff (poly_mul (poly_linear #t #f a) bigA) idx_hi in
    peel_lhs_prow #t #f a bigA b m n i j;
    peel_prow_bridge #t #f a bigA m n i j;
    peel_rhs_prow #t #f a bigA b m n i j;
    symmetry prodc pexpr;
    transitivity (matrix_mul cmat mul i j) pexpr prodc;
    symmetry (matrix_mul lmat sp i j) prodc;
    transitivity (matrix_mul cmat mul i j) prodc (matrix_mul lmat sp i j)
#pop-options

(* ================================================================ *)
(*  The full pointwise identity:  C * Mul'  =  L * S'  (all i, j).    *)
(* ================================================================ *)
let peel_pointwise (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  (i j: fin (size_peel m n))
  : Lemma (requires L.length bigA <= Prims.op_Addition m 1 /\
                    Some? (poly_deg b) /\ Some?.v (poly_deg b) <= n)
          (ensures matrix_mul (mat_c_peel #t #f bigA b m n) (mat_mul_peel #t #f a b m n) i j
                 = matrix_mul (mat_l_peel #t #f a m n) (mat_sprime_peel #t #f a bigA b m n) i j)
  = let bigN : nat = Prims.op_Addition m n in
    if (i <: nat) < n then
      peel_pointwise_prow #t #f a bigA b m n i j
    else if (i <: nat) < bigN then
      peel_pointwise_qrow #t #f a bigA b m n i j
    else
      peel_pointwise_last #t #f a bigA b m n j

(* ================================================================ *)
(*  Determinant transport across a (propositionally equal) size.     *)
(*  Used to relate det of the size-N+1 wrappers to det of the        *)
(*  underlying Sylvester matrices at their native sizes.             *)
(* ================================================================ *)
let det_size_transport (#t:Type) {| cr: commutative_ring t |} (s1 s2: pos)
  (m1: square_matrix t s1) (m2: square_matrix t s2)
  (pf: squash (s1 == s2))
  (h: (i: fin s1) -> (j: fin s1) ->
       Lemma (m1 i j == m2 (((i <: nat) <: fin s2)) (((j <: nat) <: fin s2))))
  : Lemma (det m1 = det #t #cr #s2 m2)
  = H.elim_equatable_laws t ();
    (* s1 == s2, so fin s1 = fin s2 and the two matrices live at the same size. *)
    let m2' : square_matrix t s1 = m2 in
    let pw (i j: fin s1) : Lemma (m1 i j = m2' i j)
      = h i j; reflexivity (m2' i j) in
    Classical.forall_intro_2 pw;
    det_pointwise_eq #t #cr #s1 m1 m2'

(* det of mat_Mul (= sylvester_matrix 1 bigN (x-a) b coerced) = poly_eval b a. *)
let det_mat_mul_peel (#t:Type) {| f: field t |} (a: t) (b: polynomial t) (m n: nat{n >= 1})
  : Lemma (requires Some? (poly_deg b) /\ Some?.v (poly_deg b) <= Prims.op_Addition m n)
          (ensures det (mat_mul_peel #t #f a b m n) = poly_eval b a)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let bigN : nat = Prims.op_Addition m n in
    let syl = sylvester_matrix #t #cr 1 bigN (poly_linear #t #f a) b in
    let pf : squash (size_peel m n == nat_add 1 bigN) = () in
    let h (i j: fin (size_peel m n))
      : Lemma (mat_mul_peel #t #f a b m n i j
               == syl (((i <: nat) <: fin (nat_add 1 bigN))) (((j <: nat) <: fin (nat_add 1 bigN))))
      = () in
    det_size_transport #t #cr (size_peel m n) (nat_add 1 bigN) (mat_mul_peel #t #f a b m n) syl pf h;
    det_mul_block_is_eval #t #f a b bigN;                 (* det syl = poly_eval b a *)
    transitivity (det (mat_mul_peel #t #f a b m n)) (det syl) (poly_eval b a)

(* det of mat_C = resultant m n A B. *)
let det_mat_c_peel (#t:Type) {| f: field t |} (bigA b: polynomial t) (m n: nat{n >= 1})
  : Lemma (det (mat_c_peel #t #f bigA b m n)
         = resultant #t #(cr_of_id t #(id_of_f t)) m n bigA b)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let sm = sylvester_matrix #t #cr m n bigA b in
    (* mat_c_peel = block_diag_corner1 sm  (sizes coincide definitionally). *)
    block_diag_corner1_det #t #cr #(Prims.op_Addition m n) sm;  (* det (block) = det sm *)
    resultant_unfold #t #cr m n bigA b;                   (* resultant m n A B == det sm *)
    symmetry (resultant #t #cr m n bigA b) (det sm);
    transitivity (det (mat_c_peel #t #f bigA b m n)) (det sm) (resultant #t #cr m n bigA b)

(* det of mat_L = one. *)
let det_mat_l_peel (#t:Type) {| f: field t |} (a: t) (m n: nat{n >= 1})
  : Lemma (det (mat_l_peel #t #f a m n) = (one <: t))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    det_peel_L #t #cr a m n

(* det of mat_S' = resultant (m+1) n ((x-a)A) B. *)
let det_mat_sprime_peel (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  : Lemma (det (mat_sprime_peel #t #f a bigA b m n)
         = resultant #t #(cr_of_id t #(id_of_f t)) (Prims.op_Addition m 1) n
                     (poly_mul (poly_linear #t #f a) bigA) b)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let sp_syl = sylvester_matrix #t #cr (Prims.op_Addition m 1) n
                   (poly_mul (poly_linear #t #f a) bigA) b in
    let pf : squash (size_peel m n == nat_add (Prims.op_Addition m 1) n) = () in
    let h (i j: fin (size_peel m n))
      : Lemma (mat_sprime_peel #t #f a bigA b m n i j
               == sp_syl (((i <: nat) <: fin (nat_add (Prims.op_Addition m 1) n)))
                         (((j <: nat) <: fin (nat_add (Prims.op_Addition m 1) n))))
      = () in
    det_size_transport #t #cr (size_peel m n) (nat_add (Prims.op_Addition m 1) n)
      (mat_sprime_peel #t #f a bigA b m n) sp_syl pf h;
    resultant_unfold #t #cr (Prims.op_Addition m 1) n (poly_mul (poly_linear #t #f a) bigA) b;
    symmetry (resultant #t #cr (Prims.op_Addition m 1) n (poly_mul (poly_linear #t #f a) bigA) b)
             (det sp_syl);
    transitivity (det (mat_sprime_peel #t #f a bigA b m n)) (det sp_syl)
                 (resultant #t #cr (Prims.op_Addition m 1) n (poly_mul (poly_linear #t #f a) bigA) b)

(* ================================================================ *)
(*  THE LINEAR-FACTOR PEELING LEMMA.                                 *)
(*                                                                   *)
(*    Res_{m+1, n}((x - a) * A, B) = poly_eval B a * Res_{m, n}(A, B) *)
(*                                                                   *)
(*  (formal degrees:  deg A <= m  (length A <= m+1),  deg B <= n,     *)
(*   B nonzero (Some? (poly_deg B))).                                *)
(* ================================================================ *)
#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"
let peel (#t:Type) {| f: field t |} (a: t) (bigA b: polynomial t) (m n: nat{n >= 1})
  : Lemma (requires L.length bigA <= Prims.op_Addition m 1 /\
                    Some? (poly_deg b) /\ Some?.v (poly_deg b) <= n)
          (ensures (let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
                    resultant #t #cr (Prims.op_Addition m 1) n
                              (poly_mul (poly_linear #t #f a) bigA) b
                  = poly_eval b a * resultant #t #cr m n bigA b))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cmat = mat_c_peel #t #f bigA b m n in
    let mul  = mat_mul_peel #t #f a b m n in
    let lmat = mat_l_peel #t #f a m n in
    let sp   = mat_sprime_peel #t #f a bigA b m n in
    let sz : pos = size_peel m n in
    (* det (C * Mul') = det (L * S') via the pointwise identity. *)
    let pw (i j: fin sz)
      : Lemma (matrix_mul cmat mul i j = matrix_mul lmat sp i j)
      = peel_pointwise #t #f a bigA b m n i j in
    Classical.forall_intro_2 pw;
    det_pointwise_eq #t #cr #sz (matrix_mul cmat mul) (matrix_mul lmat sp);
    (* det_mul on both products. *)
    det_mul #t #cr #sz cmat mul;                          (* det(C*Mul') = det C * det Mul' *)
    det_mul #t #cr #sz lmat sp;                           (* det(L*S')   = det L * det S'   *)
    (* det values. *)
    det_mat_c_peel #t #f bigA b m n;                      (* det C  = resultant m n A B *)
    det_mat_mul_peel #t #f a b m n;                       (* det Mul' = poly_eval b a *)
    det_mat_l_peel #t #f a m n;                           (* det L  = one *)
    det_mat_sprime_peel #t #f a bigA b m n;               (* det S' = resultant (m+1) n ((x-a)A) b *)
    let rmnAB  = resultant #t #cr m n bigA b in
    let rS'    = resultant #t #cr (Prims.op_Addition m 1) n (poly_mul (poly_linear #t #f a) bigA) b in
    (* det C * det Mul' = resultant m n A B * poly_eval b a *)
    mul_congruence (det cmat) (det mul) rmnAB (poly_eval b a);
    transitivity (det (matrix_mul cmat mul)) (det cmat * det mul) (rmnAB * poly_eval b a);
    (* det L * det S' = one * det S' = det S' = rS' *)
    reflexivity (det sp);
    mul_congruence (det lmat) (det sp) (one <: t) (det sp);   (* det L * det S' = one * det S' *)
    H.one_mul_x (det sp);
    transitivity (det lmat * det sp) ((one <: t) * det sp) (det sp);
    transitivity (det (matrix_mul lmat sp)) (det lmat * det sp) (det sp);
    transitivity (det (matrix_mul lmat sp)) (det sp) rS';
    (* chain: rS' = det(L*S') = det(C*Mul') = rmnAB * poly_eval b a *)
    symmetry (det (matrix_mul lmat sp)) rS';
    symmetry (det (matrix_mul cmat mul)) (det (matrix_mul lmat sp));   (* det(L*S') = det(C*Mul') *)
    transitivity rS' (det (matrix_mul lmat sp)) (det (matrix_mul cmat mul));
    transitivity rS' (det (matrix_mul cmat mul)) (rmnAB * poly_eval b a);
    (* commute to poly_eval b a * resultant m n A B *)
    H.mul_commutativity_cr rmnAB (poly_eval b a);
    transitivity rS' (rmnAB * poly_eval b a) (poly_eval b a * rmnAB)
#pop-options
