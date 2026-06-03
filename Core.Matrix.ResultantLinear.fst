module Core.Matrix.ResultantLinear

(*
   Resultant base case for the Poisson product formula:

       Res_{1,d}(x - a, B)  =  B(a)        (B of formal degree d)

   Strategy: the Sylvester matrix S of the monic linear (x - a) and B is
   upper-bidiagonal in its first d rows (1 on the diagonal, -a on the
   superdiagonal) with last row = B's reversed coefficients.  Right-
   multiplying by the unipotent upper-triangular shear

       U[k][j] = a^{j-k}   (k <= j),   0   (k > j)

   clears the superdiagonal: S*U is lower-triangular with diagonal
   [1, ..., 1, B(a)].  Since det U = 1 (unipotent triangular), by det_mul
       det S = det (S*U) = diagonal_product (S*U) = B(a).
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
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Root

(* ================================================================ *)
(*  Unipotent upper-triangular determinant = 1  (general, reusable). *)
(* ================================================================ *)

let det_unipotent_upper_triangular (#t:Type) {| cr: commutative_ring t |}
  (#n: pos) (m: square_matrix t n)
  : Lemma (requires is_upper_triangular m /\ (forall (i: fin n). m i i = (one <: t)))
          (ensures  det m = (one <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
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
  : Lemma (shear #t #cr #n a i i = (one <: t))
  = elim_equatable_laws t ()                             (* shear i i = cpow a 0 = one *)

let det_shear_is_one (#t:Type) {| cr: commutative_ring t |} (#n: pos) (a: t)
  : Lemma (det (shear #t #cr #n a) = (one <: t))
  = shear_upper_triangular #t #cr #n a;
    Classical.forall_intro (shear_diagonal_one #t #cr #n a);
    det_unipotent_upper_triangular (shear #t #cr #n a)

(* ================================================================ *)
(*  Milestone 1:  Res_{1,d}(x - a, B) = B(a).                        *)
(* ================================================================ *)

(* cpow a (m+1) = a * cpow a m  (definitional). *)
let cpow_succ (#t:Type) {| cr: commutative_ring t |} (a: t) (m: nat)
  : Lemma (cpow a (Prims.op_Addition m 1) = a * cpow a m)
  = elim_equatable_laws t ();
    reflexivity (a * cpow a m)

(* A "linear-shaped" polynomial: coeff 0 = neg a, coeff 1 = one, rest 0.
   (poly_linear #t #f a satisfies this — see linpoly_is_linear_shape below.)
   Stating the matrix lemmas over an ambient commutative_ring with this
   predicate keeps all fin_sum / matrix_mul / shear typeclass instances on
   a SINGLE inferred path, avoiding the field-vs-commutative_ring instance
   duplication that breaks fin_sum unification. *)
let linear_shape (#t:Type) {| cr: commutative_ring t |} (a: t) (p: polynomial t) : prop
  = coeff p 0 == (neg a <: t) /\
    coeff p 1 == (one <: t) /\
    (forall (k: nat). k >= 2 ==> coeff p k == (zero <: t))

let poly_linear_is_linear_shape (#t:Type) {| f: field t |} (a: t)
  : Lemma (linear_shape #t #(cr_of_id t #(id_of_f t)) a (poly_linear #t #f a))
  = let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    assert_norm (L.index (poly_linear #t #f a) 0 == (neg a <: t));
    assert_norm (L.index (poly_linear #t #f a) 1 == (one <: t));
    assert (L.length (poly_linear #t #f a) == 2)

(* ---------------------------------------------------------------- *)
(*  Sylvester matrix entries for S = sylvester_matrix 1 d p b        *)
(*  where p has linear_shape a.  Size is nat_add 1 d = d+1.           *)
(*  Rows 0..d-1 are the (single) p-row copies (bidiagonal); row d is  *)
(*  the q-row = reversed coeffs of b.                                 *)
(* ---------------------------------------------------------------- *)

let syl_diag_one (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t) (d: nat{d >= 1})
  (i: fin (nat_add 1 d))
  : Lemma (requires (i <: nat) < d /\ linear_shape a p)
          (ensures sylvester_matrix #t 1 d p b i i == (one <: t))
  = sylvester_p_block_lookup #t 1 d p b i i

let syl_super_neg_a (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t) (d: nat{d >= 1})
  (i: fin (nat_add 1 d)) (j: fin (nat_add 1 d))
  : Lemma (requires (i <: nat) < d /\ (j <: nat) == Prims.op_Addition (i <: nat) 1 /\ linear_shape a p)
          (ensures sylvester_matrix #t 1 d p b i j == (neg a <: t))
  = sylvester_p_block_lookup #t 1 d p b i j

(* off-(bi)diagonal p-row entries vanish: for i<d and k <> i, k <> i+1. *)
let syl_p_other_zero (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t) (d: nat{d >= 1})
  (i: fin (nat_add 1 d)) (k: fin (nat_add 1 d))
  : Lemma (requires (i <: nat) < d /\
                    (k <: nat) <> (i <: nat) /\
                    (k <: nat) <> Prims.op_Addition (i <: nat) 1 /\
                    linear_shape a p)
          (ensures sylvester_matrix #t 1 d p b i k == (zero <: t))
  = sylvester_p_block_lookup #t 1 d p b i k

(* last row entries: S[d][j] = coeff b (d - j). *)
let syl_last_row (#t:Type) {| cr: commutative_ring t |} (p b: polynomial t) (d: nat{d >= 1})
  (j: fin (nat_add 1 d))
  : Lemma (sylvester_matrix #t 1 d p b (d <: fin (nat_add 1 d)) j
         == coeff b (Prims.op_Subtraction d (j <: nat)))
  = sylvester_q_block_lookup #t 1 d p b (d <: fin (nat_add 1 d)) j


(* ---------------------------------------------------------------- *)
(*  Entries of the shear column  col U j = (fun k -> U k j).          *)
(* ---------------------------------------------------------------- *)

let shear_entry_le (#t:Type) {| cr: commutative_ring t |} (#n: pos) (a: t)
  (k j: fin n)
  : Lemma (requires (k <: nat) <= (j <: nat))
          (ensures shear #t #cr #n a k j == cpow a (Prims.op_Subtraction (j <: nat) (k <: nat)))
  = ()

let shear_entry_gt (#t:Type) {| cr: commutative_ring t |} (#n: pos) (a: t)
  (k j: fin n)
  : Lemma (requires (k <: nat) > (j <: nat))
          (ensures shear #t #cr #n a k j == (zero <: t))
  = ()

(* ---------------------------------------------------------------- *)
(*  The two surviving terms of a bidiagonal row collapse to a        *)
(*  Kronecker delta:   U[i][j] + (neg a) * U[i+1][j] = [i = j].       *)
(* ---------------------------------------------------------------- *)

let bidiag_value (#t:Type) {| cr: commutative_ring t |} (#n: pos) (a: t)
  (i: fin n{(i <: nat) + 1 < n}) (j: fin n)
  : Lemma (shear #t #cr #n a i j + (neg a) * shear #t #cr #n a ((Prims.op_Addition (i <: nat) 1) <: fin n) j
         = id_matrix #t #(cr.cr_r) #n i j)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let i1 : fin n = (Prims.op_Addition (i <: nat) 1) <: fin n in
    let ui  = shear #t #cr #n a i j in
    let ui1 = shear #t #cr #n a i1 j in
    if (j <: nat) = (i <: nat) then begin
      (* ui = cpow a 0 = one ; ui1 = 0 (i1 > j) ; one + (neg a)*0 = one = id i j *)
      shear_entry_le #t #cr #n a i j;                     (* ui = cpow a 0 = one *)
      shear_entry_gt #t #cr #n a i1 j;                    (* ui1 = zero *)
      H.x_mul_zero (neg a);                               (* (neg a)*0 = 0 ... wait ui1 *)
      mul_congruence (neg a) ui1 (neg a) (zero <: t);
      H.x_mul_zero (neg a);
      H.x_plus_zero ui;
      add_congruence ui ((neg a) * ui1) ui (zero <: t);
      (* ui = cpow a 0 = one ; id i i = one *)
      assert (ui == (one <: t));
      assert (id_matrix #t #(cr.cr_r) #n i j == (one <: t));
      transitivity (ui + (neg a) * ui1) ui (id_matrix #t #(cr.cr_r) #n i j)
    end else if (j <: nat) > (i <: nat) then begin
      (* j > i: ui = cpow a (j-i), ui1 = cpow a (j-i-1), (neg a)*ui1 = neg(cpow a (j-i)) *)
      shear_entry_le #t #cr #n a i j;                     (* ui = cpow a (j-i) *)
      shear_entry_le #t #cr #n a i1 j;                    (* ui1 = cpow a (j-(i+1)) = cpow a (j-i-1) *)
      let m : nat = Prims.op_Subtraction (j <: nat) ((i <: nat) + 1) in
      cpow_succ #t #cr a m;                               (* cpow a (m+1) = a * cpow a m ; m+1 = j-i *)
      (* (neg a)*ui1 = (neg a)*cpow a m = neg (a * cpow a m) = neg (cpow a (m+1)) = neg ui *)
      H.neg_mul_l a (cpow a m);                           (* (neg a)*cpow a m = neg (a*cpow a m) *)
      neg_congruence (a * cpow a m) (cpow a (Prims.op_Addition m 1));
      assert (ui == cpow a (Prims.op_Addition m 1));
      add_congruence ui ((neg a) * ui1) ui (neg ui);
      H.x_plus_neg_x ui;                                  (* ui + neg ui = zero *)
      assert (id_matrix #t #(cr.cr_r) #n i j == (zero <: t));
      transitivity (ui + (neg a) * ui1) (zero <: t) (id_matrix #t #(cr.cr_r) #n i j)
    end else begin
      (* j < i: ui = 0 (i>j), ui1 = 0 (i1>j) *)
      shear_entry_gt #t #cr #n a i j;                     (* ui = zero *)
      shear_entry_gt #t #cr #n a i1 j;                    (* ui1 = zero *)
      mul_congruence (neg a) ui1 (neg a) (zero <: t);
      H.x_mul_zero (neg a);
      add_congruence ui ((neg a) * ui1) (zero <: t) (zero <: t);
      H.x_plus_zero (zero <: t);
      assert (id_matrix #t #(cr.cr_r) #n i j == (zero <: t));
      transitivity (ui + (neg a) * ui1) (zero <: t) (id_matrix #t #(cr.cr_r) #n i j)
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
                    s i ((Prims.op_Addition (i <: nat) 1) <: fin n) = (neg a <: t) /\
                    (forall (k: fin n). (k <: nat) <> (i <: nat) /\
                                        (k <: nat) <> Prims.op_Addition (i <: nat) 1
                                        ==> s i k = (zero <: t)))
          (ensures matrix_mul s (shear #t #cr #n a) i j
                 = id_matrix #t #(cr.cr_r) #n i j)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let u = shear #t #cr #n a in
    let i1 : fin n = (Prims.op_Addition (i <: nat) 1) <: fin n in
    let c0 : t = u i j in                                       (* shear a i j *)
    let c1 : t = (neg a) * u i1 j in                            (* (neg a) * shear a (i+1) j *)
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
      end else if (k <: nat) = (Prims.op_Addition (i <: nat) 1) then begin
        kronecker_delta_neq #t (i <: nat) (k <: nat);           (* delta i k = zero *)
        kronecker_delta_eq #t (i1 <: nat) (k <: nat);           (* delta i1 k = one *)
        assert ((k <: nat) == (i1 <: nat));
        (* lhs = s i i1 * u k j = neg a * u i1 j = c1 *)
        assert ((row s i) k == s i i1);
        assert ((col u j) k == u i1 j);
        assert (s i i1 = (neg a <: t));
        mul_congruence (s i i1) (col u j k) (neg a) (col u j k);     (* lhs = neg a * col u j k *)
        mul_congruence (neg a) (col u j k) (neg a) (u i1 j);
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
    bidiag_value #t #cr #n a i j;                               (* c0 + c1 = id i j *)
    transitivity (matrix_mul s u i j) (c0 + c1) (id_matrix #t #(cr.cr_r) #n i j)
#pop-options

(* Sylvester-specific wrapper: row i (< d) of S = sylvester_matrix 1 d p b
   (with p of linear_shape a) dotted with the shear is a row of the identity. *)
let mul_row_bidiag (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t) (d: nat{d >= 1})
  (i: fin (nat_add 1 d)) (j: fin (nat_add 1 d))
  : Lemma (requires (i <: nat) < d /\ linear_shape a p)
          (ensures matrix_mul (sylvester_matrix #t 1 d p b)
                              (shear #t #cr #(nat_add 1 d) a) i j
                 = id_matrix #t #(cr.cr_r) #(nat_add 1 d) i j)
  = H.elim_equatable_laws t ();
    let s = sylvester_matrix #t 1 d p b in
    let i1 : fin (nat_add 1 d) = (Prims.op_Addition (i <: nat) 1) <: fin (nat_add 1 d) in
    syl_diag_one #t #cr a p b d i;                              (* s i i == one *)
    H.leibniz_to_eq (s i i) (one <: t);                         (* s i i = one *)
    syl_super_neg_a #t #cr a p b d i i1;                        (* s i i1 == neg a *)
    H.leibniz_to_eq (s i i1) (neg a <: t);                      (* s i i1 = neg a *)
    let others (k: fin (nat_add 1 d))
      : Lemma ((k <: nat) <> (i <: nat) /\
               (k <: nat) <> Prims.op_Addition (i <: nat) 1 ==> s i k = (zero <: t)) =
      if (k <: nat) <> (i <: nat) && (k <: nat) <> Prims.op_Addition (i <: nat) 1
      then begin
        syl_p_other_zero #t #cr a p b d i k;                    (* s i k == zero *)
        H.leibniz_to_eq (s i k) (zero <: t)                     (* s i k = zero *)
      end
      else ()
    in
    Classical.forall_intro others;
    bidiag_row_times_shear #t #cr #(nat_add 1 d) a s i j

(* ---------------------------------------------------------------- *)
(*  The corner entry  M[d][d] = poly_eval b a.                       *)
(*    M[d][d] = Sum_{k<=d} coeff b (d-k) * a^{d-k}                    *)
(*           = Sum_{m<=d} coeff b m * a^m  (reindex m = d-k)          *)
(*           = poly_eval b a   (length b = d+1).                      *)
(* ---------------------------------------------------------------- *)

let last_row_entry_value (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t)
  (d: nat{d >= 1})
  (k: fin (nat_add 1 d))
  : Lemma (pointwise_mul (row (sylvester_matrix #t 1 d p b) (d <: fin (nat_add 1 d)))
                         (col (shear #t #cr #(nat_add 1 d) a) (d <: fin (nat_add 1 d))) k
         = eval_term b a (Prims.op_Subtraction d (k <: nat)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let n : pos = nat_add 1 d in
    let s = sylvester_matrix #t 1 d p b in
    let u = shear #t #cr #n a in
    pointwise_mul_unfold (row s (d <: fin n)) (col u (d <: fin n)) k;   (* = s d k * u k d *)
    syl_last_row #t #cr p b d k;                            (* s d k == coeff b (d-k) *)
    (* u k d = shear a k d = cpow a (d - k)  since k <= d *)
    shear_entry_le #t #cr #n a k (d <: fin n);             (* u k d == cpow a (d-k) *)
    (* eval_term b a (d-k) = coeff b (d-k) * cpow a (d-k) *)
    assert (eval_term b a (Prims.op_Subtraction d (k <: nat))
            == coeff b (Prims.op_Subtraction d (k <: nat)) * cpow a (Prims.op_Subtraction d (k <: nat)));
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
  : Lemma (requires Some? (poly_deg b) /\ Some?.v (poly_deg b) == d)
          (ensures matrix_mul (sylvester_matrix #t 1 d p b)
                              (shear #t #cr #(nat_add 1 d) a)
                              (d <: fin (nat_add 1 d)) (d <: fin (nat_add 1 d))
                 = poly_eval b a)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let n : pos = nat_add 1 d in
    let s = sylvester_matrix #t 1 d p b in
    let u = shear #t #cr #n a in
    let dd : fin n = (d <: fin n) in
    assert (L.length b == Prims.op_Addition d 1);
    (* column function  w k = eval_term b a (d - k)  (= pw k by last_row_entry_value) *)
    let w : (fin n -> t) = fun (k: fin n) -> eval_term b a (Prims.op_Subtraction d (k <: nat)) in
    let g : nat -> t = fun (k:nat) -> if k < n then eval_term b a (Prims.op_Subtraction d k)
                                      else (zero <: t) in
    (* fin_sum w = poly_eval b a, via reindex on sum_range *)
    let w_eq_g (k: nat{k < n}) : Lemma (g k = w (k <: fin n)) = reflexivity (w (k <: fin n)) in
    Classical.forall_intro w_eq_g;
    fin_sum_eq_sum_range w g;                              (* fin_sum w = sum_range g 0 n *)
    let rev (j: nat{j < n}) : Lemma (g j = eval_term b a (Prims.op_Subtraction (Prims.op_Subtraction n 1) j)) =
      reflexivity (eval_term b a (Prims.op_Subtraction d j))
    in
    sum_range_reverse_named g (eval_term b a) n rev;       (* sum_range g 0 n = sum_range (eval_term b a) 0 n *)
    (* pw k = w k  for all k *)
    let pw_w (k: fin n) : Lemma (pointwise_mul (row s dd) (col u dd) k = w k) =
      last_row_entry_value #t #cr a p b d k
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
                     (matrix_mul (sylvester_matrix #t 1 d p b) (shear #t #cr #(nat_add 1 d) a)))
  = H.elim_equatable_laws t ();
    let n : pos = nat_add 1 d in
    let s = sylvester_matrix #t 1 d p b in
    let u = shear #t #cr #n a in
    let m = matrix_mul s u in
    let upper (i j: fin n) : Lemma ((j <: nat) > (i <: nat) ==> m i j = (zero <: t)) =
      if (j <: nat) > (i <: nat) then begin
        (* then i < d  (since j <= d) *)
        assert ((i <: nat) < d);
        mul_row_bidiag #t #cr a p b d i j;                 (* m i j = id i j *)
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
  : Lemma (requires linear_shape a p /\ Some? (poly_deg b) /\ Some?.v (poly_deg b) == d)
          (ensures diagonal_product_from
                     (matrix_mul (sylvester_matrix #t 1 d p b) (shear #t #cr #(nat_add 1 d) a)) k
                 = poly_eval b a)
          (decreases (d - k))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let n : pos = nat_add 1 d in
    let s = sylvester_matrix #t 1 d p b in
    let u = shear #t #cr #n a in
    let m = matrix_mul s u in
    if k = d then begin
      (* diagonal_product_from m d = m[d][d] * diagonal_product_from m (d+1)
                                   = B(a) * one = B(a) *)
      mul_corner_is_eval #t #cr a p b d;                    (* m[d][d] = poly_eval b a *)
      assert (diagonal_product_from m d
              == m (d <: fin n) (d <: fin n) * diagonal_product_from m (Prims.op_Addition d 1));
      assert (diagonal_product_from m (Prims.op_Addition d 1) == (one <: t));   (* k+1 >= n *)
      H.x_mul_one (m (d <: fin n) (d <: fin n));
      mul_congruence (m (d <: fin n) (d <: fin n)) (diagonal_product_from m (Prims.op_Addition d 1))
                     (m (d <: fin n) (d <: fin n)) (one <: t);
      transitivity (diagonal_product_from m d)
                   (m (d <: fin n) (d <: fin n) * diagonal_product_from m (Prims.op_Addition d 1))
                   (m (d <: fin n) (d <: fin n) * (one <: t));
      transitivity (diagonal_product_from m d)
                   (m (d <: fin n) (d <: fin n) * (one <: t))
                   (m (d <: fin n) (d <: fin n));
      transitivity (diagonal_product_from m d) (m (d <: fin n) (d <: fin n)) (poly_eval b a)
    end else begin
      (* k < d:  m[k][k] = id k k = one ; diagonal_product_from m k = one * tail = tail *)
      diag_prod_from_is_eval #t #cr a p b d (Prims.op_Addition k 1);   (* IH: tail = B(a) *)
      mul_row_bidiag #t #cr a p b d (k <: fin n) (k <: fin n);         (* m[k][k] = id k k *)
      id_matrix_diag #t #(cr.cr_r) #n (k <: fin n);                    (* id k k == one *)
      H.leibniz_to_eq (id_matrix #t #(cr.cr_r) #n (k <: fin n) (k <: fin n)) (one <: t);
      assert (diagonal_product_from m k
              == m (k <: fin n) (k <: fin n) * diagonal_product_from m (Prims.op_Addition k 1));
      mul_congruence (m (k <: fin n) (k <: fin n)) (diagonal_product_from m (Prims.op_Addition k 1))
                     (one <: t) (diagonal_product_from m (Prims.op_Addition k 1));
      H.one_mul_x (diagonal_product_from m (Prims.op_Addition k 1));
      transitivity (diagonal_product_from m k)
                   (m (k <: fin n) (k <: fin n) * diagonal_product_from m (Prims.op_Addition k 1))
                   ((one <: t) * diagonal_product_from m (Prims.op_Addition k 1));
      transitivity (diagonal_product_from m k)
                   ((one <: t) * diagonal_product_from m (Prims.op_Addition k 1))
                   (diagonal_product_from m (Prims.op_Addition k 1));
      transitivity (diagonal_product_from m k)
                   (diagonal_product_from m (Prims.op_Addition k 1))
                   (poly_eval b a)
    end

let mul_diagonal_product_is_eval (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t)
  (d: nat{d >= 1})
  : Lemma (requires linear_shape a p /\ Some? (poly_deg b) /\ Some?.v (poly_deg b) == d)
          (ensures diagonal_product
                     (matrix_mul (sylvester_matrix #t 1 d p b) (shear #t #cr #(nat_add 1 d) a))
                 = poly_eval b a)
  = diag_prod_from_is_eval #t #cr a p b d 0

(* ---------------------------------------------------------------- *)
(*  Degenerate case d = 0:  B a degree-0 (nonzero constant).         *)
(*  The Sylvester matrix is 1x1 with single entry coeff b 0;          *)
(*  det = coeff b 0 = poly_eval b a.                                  *)
(* ---------------------------------------------------------------- *)

let resultant_linear_const (#t:Type) {| f: field t |} (a: t) (b: polynomial t)
  : Lemma (requires Some? (poly_deg b) /\ Some?.v (poly_deg b) == 0)
          (ensures (let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
                    resultant #t #cr 1 0 (poly_linear #t #f a) b = poly_eval b a))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pl = poly_linear #t #f a in
    let s = sylvester_matrix #t #cr 1 0 pl b in
    assert (L.length b == 1);
    (* det s = s[0][0] = coeff b 0 *)
    determinant_size_one #t #cr s;                          (* det s = s 0 0 *)
    sylvester_q_block_lookup #t #cr 1 0 pl b (0 <: fin (nat_add 1 0)) (0 <: fin (nat_add 1 0));
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
    resultant_unfold #t #cr 1 0 pl b;
    H.leibniz_then_eq (resultant #t #cr 1 0 pl b) (det s) (poly_eval b a)

(* ================================================================ *)
(*  MAIN THEOREM (Milestone 1):  Res_{1,d}(x - a, B) = B(a).         *)
(* ================================================================ *)

let resultant_linear (#t:Type) {| f: field t |} (a: t) (b: polynomial t)
  : Lemma (requires Some? (poly_deg b))
          (ensures (let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
                    resultant #t #cr 1 (Some?.v (poly_deg b)) (poly_linear #t #f a) b
                    = poly_eval b a))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let d : nat = Some?.v (poly_deg b) in
    let pl = poly_linear #t #f a in
    poly_linear_is_linear_shape #t #f a;                   (* linear_shape a pl *)
    if d = 0 then resultant_linear_const #t #f a b
    else begin
    let s = sylvester_matrix #t #cr 1 d pl b in
    let u = shear #t #cr #(nat_add 1 d) a in
    let m = matrix_mul s u in
    (* det (S*U) = det S * det U = det S * one = det S *)
    det_mul #t #cr #(nat_add 1 d) s u;                     (* det m = det s * det u *)
    det_shear_is_one #t #cr #(nat_add 1 d) a;              (* det u = one *)
    reflexivity (det s);
    mul_congruence (det s) (det u) (det s) (one <: t);
    H.x_mul_one (det s);
    transitivity (det m) (det s * det u) (det s * (one <: t));
    transitivity (det m) (det s * (one <: t)) (det s);     (* det m = det s *)
    (* det m = diagonal_product m = poly_eval b a *)
    mul_is_lower_triangular #t #cr a pl b d;
    det_lower_triangular #t #cr #(nat_add 1 d) m;          (* det m = diagonal_product m *)
    mul_diagonal_product_is_eval #t #cr a pl b d;          (* diagonal_product m = poly_eval b a *)
    transitivity (det m) (diagonal_product m) (poly_eval b a);
    (* det s = det m = poly_eval b a *)
    symmetry (det m) (det s);
    transitivity (det s) (det m) (poly_eval b a);
    (* resultant = det s *)
    resultant_unfold #t #cr 1 d pl b;
    H.leibniz_then_eq (resultant #t #cr 1 d pl b) (det s) (poly_eval b a)
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
  : Lemma (requires Some? (poly_deg b) /\ Some?.v (poly_deg b) <= bigN)
          (ensures matrix_mul (sylvester_matrix #t 1 bigN p b)
                              (shear #t #cr #(nat_add 1 bigN) a)
                              (bigN <: fin (nat_add 1 bigN)) (bigN <: fin (nat_add 1 bigN))
                 = poly_eval b a)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let n : pos = nat_add 1 bigN in
    let s = sylvester_matrix #t 1 bigN p b in
    let u = shear #t #cr #n a in
    let dd : fin n = (bigN <: fin n) in
    (* length b = deg b + 1 <= bigN + 1 = n  (poly_deg unfolds to Some (length-1)) *)
    assert (L.length b == Prims.op_Addition (Some?.v (poly_deg b)) 1);
    assert (L.length b <= n);
    let w : (fin n -> t) = fun (k: fin n) -> eval_term b a (Prims.op_Subtraction bigN (k <: nat)) in
    let g : nat -> t = fun (k:nat) -> if k < n then eval_term b a (Prims.op_Subtraction bigN k)
                                      else (zero <: t) in
    let w_eq_g (k: nat{k < n}) : Lemma (g k = w (k <: fin n)) = reflexivity (w (k <: fin n)) in
    Classical.forall_intro w_eq_g;
    fin_sum_eq_sum_range w g;                              (* fin_sum w = sum_range g 0 n *)
    let rev (j: nat{j < n}) : Lemma (g j = eval_term b a (Prims.op_Subtraction (Prims.op_Subtraction n 1) j)) =
      reflexivity (eval_term b a (Prims.op_Subtraction bigN j))
    in
    sum_range_reverse_named g (eval_term b a) n rev;       (* sum_range g 0 n = sum_range (eval_term b a) 0 n *)
    eval_extend b a n;                                      (* sum_range (eval_term b a) 0 n = poly_eval b a  (n >= length b) *)
    let pw_w (k: fin n) : Lemma (pointwise_mul (row s dd) (col u dd) k = w k) =
      last_row_entry_value #t #cr a p b bigN k
    in
    Classical.forall_intro pw_w;
    matrix_mul_diag_value #t #cr #n s u dd w (poly_eval b a)

(* diagonal_product_from M k = B(a) for all k <= bigN (formal degree). *)
let rec diag_prod_from_is_eval_formal (#t:Type) {| cr: commutative_ring t |} (a: t) (p b: polynomial t)
  (bigN: nat{bigN >= 1}) (k: nat{k <= bigN})
  : Lemma (requires linear_shape a p /\ Some? (poly_deg b) /\ Some?.v (poly_deg b) <= bigN)
          (ensures diagonal_product_from
                     (matrix_mul (sylvester_matrix #t 1 bigN p b) (shear #t #cr #(nat_add 1 bigN) a)) k
                 = poly_eval b a)
          (decreases (bigN - k))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let n : pos = nat_add 1 bigN in
    let s = sylvester_matrix #t 1 bigN p b in
    let u = shear #t #cr #n a in
    let m = matrix_mul s u in
    if k = bigN then begin
      mul_corner_is_eval_formal #t #cr a p b bigN;          (* m[N][N] = poly_eval b a *)
      assert (diagonal_product_from m bigN
              == m (bigN <: fin n) (bigN <: fin n) * diagonal_product_from m (Prims.op_Addition bigN 1));
      assert (diagonal_product_from m (Prims.op_Addition bigN 1) == (one <: t));   (* k+1 >= n *)
      H.x_mul_one (m (bigN <: fin n) (bigN <: fin n));
      mul_congruence (m (bigN <: fin n) (bigN <: fin n)) (diagonal_product_from m (Prims.op_Addition bigN 1))
                     (m (bigN <: fin n) (bigN <: fin n)) (one <: t);
      transitivity (diagonal_product_from m bigN)
                   (m (bigN <: fin n) (bigN <: fin n) * diagonal_product_from m (Prims.op_Addition bigN 1))
                   (m (bigN <: fin n) (bigN <: fin n) * (one <: t));
      transitivity (diagonal_product_from m bigN)
                   (m (bigN <: fin n) (bigN <: fin n) * (one <: t))
                   (m (bigN <: fin n) (bigN <: fin n));
      transitivity (diagonal_product_from m bigN) (m (bigN <: fin n) (bigN <: fin n)) (poly_eval b a)
    end else begin
      diag_prod_from_is_eval_formal #t #cr a p b bigN (Prims.op_Addition k 1);   (* IH: tail = B(a) *)
      mul_row_bidiag #t #cr a p b bigN (k <: fin n) (k <: fin n);                (* m[k][k] = id k k *)
      id_matrix_diag #t #(cr.cr_r) #n (k <: fin n);                              (* id k k == one *)
      H.leibniz_to_eq (id_matrix #t #(cr.cr_r) #n (k <: fin n) (k <: fin n)) (one <: t);
      assert (diagonal_product_from m k
              == m (k <: fin n) (k <: fin n) * diagonal_product_from m (Prims.op_Addition k 1));
      mul_congruence (m (k <: fin n) (k <: fin n)) (diagonal_product_from m (Prims.op_Addition k 1))
                     (one <: t) (diagonal_product_from m (Prims.op_Addition k 1));
      H.one_mul_x (diagonal_product_from m (Prims.op_Addition k 1));
      transitivity (diagonal_product_from m k)
                   (m (k <: fin n) (k <: fin n) * diagonal_product_from m (Prims.op_Addition k 1))
                   ((one <: t) * diagonal_product_from m (Prims.op_Addition k 1));
      transitivity (diagonal_product_from m k)
                   ((one <: t) * diagonal_product_from m (Prims.op_Addition k 1))
                   (diagonal_product_from m (Prims.op_Addition k 1));
      transitivity (diagonal_product_from m k)
                   (diagonal_product_from m (Prims.op_Addition k 1))
                   (poly_eval b a)
    end

(* MAIN (Task 1):  Res_{1,N}(x - a, B) = B(a)  for any formal degree N >= deg B. *)
let resultant_linear_formal (#t:Type) {| f: field t |} (a: t) (b: polynomial t)
  (bigN: nat{bigN >= 1})
  : Lemma (requires Some? (poly_deg b) /\ Some?.v (poly_deg b) <= bigN)
          (ensures (let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
                    resultant #t #cr 1 bigN (poly_linear #t #f a) b
                    = poly_eval b a))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pl = poly_linear #t #f a in
    poly_linear_is_linear_shape #t #f a;                   (* linear_shape a pl *)
    let s = sylvester_matrix #t #cr 1 bigN pl b in
    let u = shear #t #cr #(nat_add 1 bigN) a in
    let m = matrix_mul s u in
    (* det (S*U) = det S * det U = det S * one = det S *)
    det_mul #t #cr #(nat_add 1 bigN) s u;                  (* det m = det s * det u *)
    det_shear_is_one #t #cr #(nat_add 1 bigN) a;           (* det u = one *)
    mul_congruence (det s) (det u) (det s) (one <: t);
    H.x_mul_one (det s);
    (* det m = diagonal_product m = poly_eval b a *)
    mul_is_lower_triangular #t #cr a pl b bigN;
    det_lower_triangular #t #cr #(nat_add 1 bigN) m;       (* det m = diagonal_product m *)
    diag_prod_from_is_eval_formal #t #cr a pl b bigN 0;    (* diagonal_product m = poly_eval b a *)
    assert (diagonal_product m == diagonal_product_from m 0);
    resultant_unfold #t #cr 1 bigN pl b;
    H.leibniz_then_eq (resultant #t #cr 1 bigN pl b) (det s) (poly_eval b a)

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
  : Lemma (sylvester_matrix #t 0 n ([c] <: polynomial t) b i j
         == (if (i <: nat) = (j <: nat) then c else (zero <: t)))
  = sylvester_p_block_lookup #t 0 n ([c] <: polynomial t) b i j   (* i < n = n_deg, p-block: coeff [c] (0+i-j) *)

(* the constant Sylvester matrix is lower-triangular. *)
let syl_const_lower_triangular (#t:Type) {| cr: commutative_ring t |} (c: t{not (c = (zero <: t))})
  (b: polynomial t) (n: nat{n >= 1})
  : Lemma (is_lower_triangular (sylvester_matrix #t 0 n ([c] <: polynomial t) b))
  = H.elim_equatable_laws t ();
    let s = sylvester_matrix #t 0 n ([c] <: polynomial t) b in
    let upper (i j: fin (nat_add 0 n)) : Lemma ((j <: nat) > (i <: nat) ==> s i j = (zero <: t)) =
      if (j <: nat) > (i <: nat) then begin
        syl_const_entry #t #cr c b n i j;
        assert (s i j == (zero <: t))
      end else ()
    in
    Classical.forall_intro_2 upper

(* diagonal_product_from of the constant matrix = c^{n-k}. *)
let rec syl_const_diag_from (#t:Type) {| cr: commutative_ring t |} (c: t{not (c = (zero <: t))})
  (b: polynomial t) (n: nat{n >= 1}) (k: nat{k <= n})
  : Lemma (ensures diagonal_product_from (sylvester_matrix #t 0 n ([c] <: polynomial t) b) k
                 = cpow c (Prims.op_Subtraction n k))
          (decreases (n - k))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let s = sylvester_matrix #t 0 n ([c] <: polynomial t) b in
    if k >= n then begin
      (* diagonal_product_from s n = one = cpow c 0 *)
      assert (diagonal_product_from s k == (one <: t));
      assert (cpow c (Prims.op_Subtraction n k) == (one <: t));
      transitivity (diagonal_product_from s k) (one <: t) (cpow c (Prims.op_Subtraction n k))
    end else begin
      syl_const_diag_from #t #cr c b n (Prims.op_Addition k 1);   (* IH: tail = cpow c (n-k-1) *)
      syl_const_entry #t #cr c b n (k <: fin (nat_add 0 n)) (k <: fin (nat_add 0 n));   (* s k k == c *)
      (* diagonal_product_from s k = s k k * tail = c * cpow c (n-k-1) = cpow c (n-k) *)
      assert (diagonal_product_from s k
              == s (k <: fin (nat_add 0 n)) (k <: fin (nat_add 0 n))
                 * diagonal_product_from s (Prims.op_Addition k 1));
      mul_congruence (s (k <: fin (nat_add 0 n)) (k <: fin (nat_add 0 n)))
                     (diagonal_product_from s (Prims.op_Addition k 1))
                     c (cpow c (Prims.op_Subtraction n (Prims.op_Addition k 1)));
      (* c * cpow c (n-k-1) = cpow c (n-k)  (definitional: n-k = (n-k-1)+1) *)
      cpow_succ #t #cr c (Prims.op_Subtraction n (Prims.op_Addition k 1));
      symmetry (cpow c (Prims.op_Addition (Prims.op_Subtraction n (Prims.op_Addition k 1)) 1))
               (c * cpow c (Prims.op_Subtraction n (Prims.op_Addition k 1)));
      transitivity (diagonal_product_from s k)
                   (s (k <: fin (nat_add 0 n)) (k <: fin (nat_add 0 n))
                    * diagonal_product_from s (Prims.op_Addition k 1))
                   (c * cpow c (Prims.op_Subtraction n (Prims.op_Addition k 1)));
      transitivity (diagonal_product_from s k)
                   (c * cpow c (Prims.op_Subtraction n (Prims.op_Addition k 1)))
                   (cpow c (Prims.op_Addition (Prims.op_Subtraction n (Prims.op_Addition k 1)) 1));
      assert (cpow c (Prims.op_Addition (Prims.op_Subtraction n (Prims.op_Addition k 1)) 1)
              == cpow c (Prims.op_Subtraction n k));
      transitivity (diagonal_product_from s k)
                   (cpow c (Prims.op_Addition (Prims.op_Subtraction n (Prims.op_Addition k 1)) 1))
                   (cpow c (Prims.op_Subtraction n k))
    end

let resultant_const (#t:Type) {| f: field t |} (c: t{not (c = (zero <: t))}) (b: polynomial t) (n: nat{n >= 1})
  : Lemma (let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
           resultant #t #cr 0 n ([c] <: polynomial t) b = cpow c n)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let s = sylvester_matrix #t #cr 0 n ([c] <: polynomial t) b in
    syl_const_lower_triangular #t #cr c b n;
    det_lower_triangular #t #cr #(nat_add 0 n) s;          (* det s = diagonal_product s *)
    syl_const_diag_from #t #cr c b n 0;                    (* diagonal_product_from s 0 = cpow c n *)
    assert (diagonal_product s == diagonal_product_from s 0);
    transitivity (det s) (diagonal_product s) (cpow c n);
    resultant_unfold #t #cr 0 n ([c] <: polynomial t) b;
    H.leibniz_then_eq (resultant #t #cr 0 n ([c] <: polynomial t) b) (det s) (cpow c n)
