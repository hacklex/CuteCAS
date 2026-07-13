module Core.Factor.MonicizeSqfree

(* ================================================================ *)
(*  monicize_sqfree_bridge : monic-ization preserves ℚ-square-      *)
(*  freeness.  Over ℚ, embed(monicize b) is the image of embed(b)   *)
(*  under the ℚ-algebra automorphism  σ : x ↦ c·x  (c = 1/L, L the   *)
(*  leading coeff), up to a nonzero constant scalar.  σ is a ring    *)
(*  hom that commutes with the derivative up to a scalar and is      *)
(*  invertible, hence preserves coprime(f, f') = square_free.        *)
(*                                                                   *)
(*  The scaled substitution here is  qsubst c g  with                *)
(*      coeff_i (qsubst c g) = coeff_i g · c^i.                       *)
(* ================================================================ *)

module L   = FStar.List.Tot
module E   = Core.Polynomial.Eval
module CC  = Core.Polynomial.Coeff
module H   = Core.Algebra.Helpers
module R   = Core.Polynomial.Roots
module MON = Core.Polynomial.Monic
module SF  = Core.Polynomial.SquareFree
module IRR = Core.Polynomial.Irreducible
module EQ  = Core.Polynomial.EmbedQ
module BIN = Core.Factor.BadIntNonzero
module NMZ = Core.Factor.NonMonicZass

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.Derivative
open Core.Polynomial.GCD
open Core.FinSum

(* ---------------------------------------------------------------- *)
(*  The scaled substitution  σ_c : g ↦ g(c·x),                       *)
(*    coeff_i (qsubst c g) = coeff_i g · c^i,                         *)
(*  built as a sum of monomials (mirrors monomial_decomposition).    *)
(* ---------------------------------------------------------------- *)

let qterm (#t:Type) {| cr: commutative_ring t |} (c: t) (g: polynomial t) (i: nat)
  : polynomial t
  = monomial (coeff g i * E.cpow c i) i

let qsubst (#t:Type) {| cr: commutative_ring t |} (c: t) (g: polynomial t)
  : polynomial t
  = sum_range (qterm c g) 0 (L.length g)

(* ---------------------------------------------------------------- *)
(*  The defining coefficient formula.                                *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 30 --fuel 2 --ifuel 2"
let qsubst_coeff (#t:Type) {| cr: commutative_ring t |} (c: t) (g: polynomial t) (k: nat)
  : Lemma (coeff (qsubst c g) k = coeff g k * E.cpow c k)
  = Core.Algebra.Helpers.elim_equatable_laws t ();
    Core.Algebra.Helpers.trans_for_calc t ();
    let n = L.length g in
    let f : nat -> polynomial t = qterm c g in
    CC.coeff_sum_range f 0 n k;
    (* coeff (qsubst c g) k = sum_range (fun i -> coeff (f i) k) 0 n *)
    let term (i:nat) : t = coeff (f i) k in
    let target (i:nat) : t = if i = k then coeff g i * E.cpow c i else (zero <: t) in
    let term_eq (i: nat{0 <= i /\ i < n}) : Lemma (term i = target i) =
      monomial_coeff (coeff g i * E.cpow c i) i k
    in
    sum_range_congruence term target 0 n term_eq;
    if k < n then begin
      sum_range_kronecker_in_range k (fun (i:nat) -> coeff g i * E.cpow c i) 0 n;
      let pw : nat -> t = pointwise_mul (kronecker_delta k) (fun (i:nat) -> coeff g i * E.cpow c i) in
      let pw_eq_target (i: nat{0 <= i /\ i < n}) : Lemma (pw i = target i) =
        pointwise_mul_unfold (kronecker_delta k) (fun (i:nat) -> coeff g i * E.cpow c i) i;
        if i = k then Core.Algebra.Helpers.one_mul_x (coeff g k * E.cpow c k)
        else Core.Algebra.Helpers.zero_mul_x (coeff g i * E.cpow c i)
      in
      sum_range_congruence pw target 0 n pw_eq_target
    end
    else begin
      sum_range_all_zero target 0 n (fun (i: nat{0 <= i /\ i < n}) -> ());
      (* k >= n = len g ⟹ deg g < k ⟹ coeff g k = zero ⟹ coeff g k * c^k = zero *)
      coeff_above_degree g k;
      Core.Algebra.Helpers.zero_mul_x (E.cpow c k)
    end
#pop-options

(* ---------------------------------------------------------------- *)
(*  Additivity of the scaled substitution.                           *)
(* ---------------------------------------------------------------- *)

let qsubst_add (#t:Type) {| cr: commutative_ring t |} (c: t) (f g: polynomial t)
  : Lemma (qsubst c (f + g) = (qsubst c f) + (qsubst c g))
  = Core.Algebra.Helpers.elim_equatable_laws t ();
    Core.Algebra.Helpers.trans_for_calc t ();
    let aux (k:nat) : Lemma (coeff (qsubst c (f + g)) k = coeff ((qsubst c f) + (qsubst c g)) k) =
      let ck = E.cpow c k in
      qsubst_coeff c (f + g) k;   (* LHS = coeff(f+g) k * ck *)
      qsubst_coeff c f k;         (* (qf)_k = f_k * ck *)
      qsubst_coeff c g k;         (* (qg)_k = g_k * ck *)
      poly_add_coeff f g k;                         (* coeff (f+g) k = f_k + g_k *)
      poly_add_coeff (qsubst c f) (qsubst c g) k;   (* coeff (qf+qg) k = (qf)_k + (qg)_k *)
      mul_congruence (coeff (f + g) k) ck ((coeff f k) + (coeff g k)) ck;
      right_distributivity ck (coeff f k) (coeff g k);  (* (f_k+g_k)*ck = f_k*ck + g_k*ck *)
      add_congruence (coeff f k * ck) (coeff g k * ck)
                     (coeff (qsubst c f) k) (coeff (qsubst c g) k);
      let lhs : t = coeff (qsubst c (f + g)) k in
      let s1  : t = (coeff f k + coeff g k) * ck in
      let s2  : t = coeff f k * ck + coeff g k * ck in
      let s3  : t = coeff (qsubst c f) k + coeff (qsubst c g) k in
      transitivity lhs s1 s2;
      transitivity lhs s2 s3;
      transitivity lhs s3 (coeff ((qsubst c f) + (qsubst c g)) k)
    in
    poly_eq_by_coeff (qsubst c (f + g)) ((qsubst c f) + (qsubst c g)) aux

(* ---------------------------------------------------------------- *)
(*  On constants (deg <= 0) the scaled substitution is the identity  *)
(*  (c^0 = 1 fixes the sole coefficient).                            *)
(* ---------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1"
let qsubst_const (#t:Type) {| cr: commutative_ring t |} (c: t) (p: polynomial t)
  : Lemma (requires deg p <= 0)
          (ensures qsubst c p = p)
  = Core.Algebra.Helpers.elim_equatable_laws t ();
    Core.Algebra.Helpers.trans_for_calc t ();
    let aux (k:nat) : Lemma (coeff (qsubst c p) k = coeff p k) =
      qsubst_coeff c p k;                (* coeff(qsubst c p) k = p_k * cpow c k *)
      if k = 0 then begin
        (* cpow c 0 = one, p_0 * one = p_0 *)
        Core.Algebra.Helpers.x_mul_one (coeff p 0);
        transitivity (coeff (qsubst c p) 0) (coeff p 0 * E.cpow c 0) (coeff p 0)
      end
      else begin
        coeff_above_degree p k;          (* p_k = zero *)
        mul_congruence (coeff p k) (E.cpow c k) (zero <: t) (E.cpow c k);
        Core.Algebra.Helpers.zero_mul_x (E.cpow c k);
        let lhs : t = coeff (qsubst c p) k in
        transitivity lhs (coeff p k * E.cpow c k) ((zero <: t) * E.cpow c k);
        transitivity lhs ((zero <: t) * E.cpow c k) (zero <: t);
        symmetry (coeff p k) (zero <: t);
        transitivity lhs (zero <: t) (coeff p k)
      end
    in
    poly_eq_by_coeff (qsubst c p) p aux
#pop-options

(* ---------------------------------------------------------------- *)
(*  Congruence: qsubst respects poly_eq.                             *)
(* ---------------------------------------------------------------- *)

let qsubst_congr (#t:Type) {| cr: commutative_ring t |} (c: t) (p q: polynomial t)
  : Lemma (requires p = q) (ensures qsubst c p = qsubst c q)
  = Core.Algebra.Helpers.elim_equatable_laws t ();
    Core.Algebra.Helpers.trans_for_calc t ();
    let aux (k:nat) : Lemma (coeff (qsubst c p) k = coeff (qsubst c q) k) =
      let ck = E.cpow c k in
      qsubst_coeff c p k;
      qsubst_coeff c q k;
      poly_eq_means_equal_coeffs p q k;      (* coeff p k = coeff q k *)
      mul_congruence (coeff p k) ck (coeff q k) ck;
      let lhs : t = coeff (qsubst c p) k in
      transitivity lhs (coeff p k * ck) (coeff q k * ck);
      transitivity lhs (coeff q k * ck) (coeff (qsubst c q) k)
    in
    poly_eq_by_coeff (qsubst c p) (qsubst c q) aux

(* ---------------------------------------------------------------- *)
(*  A nonzero scalar raised to a power is nonzero (field).           *)
(* ---------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1"
let rec cpow_nonzero (#t:Type) {| f: field t |} (c: t) (i: nat)
  : Lemma (requires not (c = (zero <: t)))
          (ensures not (E.cpow c i = (zero <: t)))
          (decreases i)
  = if i = 0 then ()   (* cpow c 0 = one, and one <> zero in a field *)
    else begin
      cpow_nonzero c (i - 1);
      domain_nonzero_mul_nonzero c (E.cpow c (i - 1))   (* c * cpow c (i-1) <> zero *)
    end
#pop-options

(* ---------------------------------------------------------------- *)
(*  For c <> 0 and f <> 0, the scaled substitution is nonzero: its   *)
(*  leading coefficient  lc(f) * c^(deg f)  is a product of nonzeros. *)
(* ---------------------------------------------------------------- *)

let qsubst_nonzero (#t:Type) {| f: field t |} (c: t) (g: polynomial t)
  : Lemma (requires not (c = (zero <: t)) /\ deg g >= 0)
          (ensures deg (qsubst c g) >= 0)
  = Core.Algebra.Helpers.elim_equatable_laws t ();
    Core.Algebra.Helpers.trans_for_calc t ();
    let n = deg g in
    qsubst_coeff c g n;                    (* coeff(qsubst c g) n = g_n * c^n *)
    leading_coeff_nonzero g;               (* g_n <> zero *)
    cpow_nonzero c n;                      (* c^n <> zero *)
    domain_nonzero_mul_nonzero (coeff g n) (E.cpow c n);  (* g_n * c^n <> zero *)
    (* if deg (qsubst c g) < 0 then qsubst c g = [] and coeff at n = zero: contradiction *)
    if deg (qsubst c g) < 0 then begin
      coeff_above_degree (qsubst c g) n;   (* coeff(qsubst c g) n = zero *)
      symmetry (coeff (qsubst c g) n) (zero <: t);
      transitivity (zero <: t) (coeff (qsubst c g) n) (coeff g n * E.cpow c n)
    end

(* qsubst preserves the leading position: deg (qsubst c g) >= deg g. *)
let qsubst_deg_ge (#t:Type) {| f: field t |} (c: t) (g: polynomial t)
  : Lemma (requires not (c = (zero <: t)) /\ deg g >= 0)
          (ensures deg (qsubst c g) >= deg g)
  = Core.Algebra.Helpers.elim_equatable_laws t ();
    Core.Algebra.Helpers.trans_for_calc t ();
    let n : nat = deg g in
    qsubst_coeff c g n;                    (* coeff(qsubst c g) n = g_n * c^n *)
    leading_coeff_nonzero g;
    cpow_nonzero c n;
    domain_nonzero_mul_nonzero (coeff g n) (E.cpow c n);   (* g_n * c^n <> 0 *)
    if deg (qsubst c g) < n then begin
      coeff_above_degree (qsubst c g) n;
      symmetry (coeff (qsubst c g) n) (zero <: t);
      transitivity (zero <: t) (coeff (qsubst c g) n) (coeff g n * E.cpow c n)
    end

(* ================================================================ *)
(*  MULTIPLICATIVITY of the scaled substitution.                    *)
(* ================================================================ *)

let qfn (#t:Type) {| cr: commutative_ring t |} (c: t) (f g: polynomial t) (k: nat) (i: nat)
  : t
  = (coeff f i * coeff g (k - i)) * E.cpow c k

let qfn_unfold (#t:Type) {| cr: commutative_ring t |} (c: t) (f g: polynomial t) (k: nat) (i: nat)
  : Lemma (qfn c f g k i == (coeff f i * coeff g (k - i)) * E.cpow c k)
  = ()

let lconv (#t:Type) {| cr: commutative_ring t |} (f g: polynomial t) (k: nat) (i: nat)
  : t
  = coeff f i * coeff g (k - i)

let lconv_unfold (#t:Type) {| cr: commutative_ring t |} (f g: polynomial t) (k: nat) (i: nat)
  : Lemma (lconv f g k i == coeff f i * coeff g (k - i))
  = ()

let ring_rearrange4 (#t:Type) {| cr: commutative_ring t |} (a p b q: t)
  : Lemma ((a * p) * (b * q) = (a * b) * (p * q))
  = assert ((a * p) * (b * q) = (a * b) * (p * q))
      by Core.Tactics.CanonRing.canon_ring ()

let sum_extend (#t:Type) {| m: add_comm_group t |}
  (fn: nat -> t) (lo hi: nat)
  (h: (i: nat{lo <= i /\ i < hi}) -> Lemma (fn i = zero))
  : Lemma (requires lo <= hi)
          (ensures sum_range fn 0 lo = sum_range fn 0 hi)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    sum_range_split fn 0 lo hi;
    sum_range_all_zero fn lo hi h;
    let a = sum_range fn 0 lo in
    let b = sum_range fn lo hi in
    add_congruence a b a (zero <: t);
    H.x_plus_zero a;
    transitivity (sum_range fn 0 hi) (a + b) (a + (zero <: t));
    transitivity (sum_range fn 0 hi) (a + (zero <: t)) a

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let qmul_term (#t:Type) {| cr: commutative_ring t |} (c: t) (f g: polynomial t) (k: nat) (i: nat)
  : Lemma (qfn c f g k i = coeff (qsubst c f) i * coeff (qsubst c g) (k - i))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    qfn_unfold c f g k i;
    let ck = E.cpow c k in
    let qf = qsubst c f in
    let qg = qsubst c g in
    if i > k then begin
      mul_congruence (coeff f i) (coeff g (k - i)) (coeff f i) (zero <: t);
      H.x_mul_zero (coeff f i);
      let a = coeff f i * coeff g (k - i) in
      transitivity a (coeff f i * (zero <: t)) (zero <: t);
      mul_congruence a ck (zero <: t) ck;
      H.zero_mul_x ck;
      transitivity (a * ck) ((zero <: t) * ck) (zero <: t);
      mul_congruence (coeff qf i) (coeff qg (k - i)) (coeff qf i) (zero <: t);
      H.x_mul_zero (coeff qf i);
      let b = coeff qf i * coeff qg (k - i) in
      transitivity b (coeff qf i * (zero <: t)) (zero <: t);
      transitivity (a * ck) (zero <: t) b;
      transitivity (qfn c f g k i) (a * ck) b
    end else begin
      qsubst_coeff c f i;
      qsubst_coeff c g (k - i);
      E.cpow_add c i (k - i);
      ring_rearrange4 (coeff f i) (E.cpow c i) (coeff g (k - i)) (E.cpow c (k - i));
      mul_congruence (coeff qf i) (coeff qg (k - i))
                     (coeff f i * E.cpow c i) (coeff g (k - i) * E.cpow c (k - i));
      mul_congruence (coeff f i * coeff g (k - i)) (E.cpow c i * E.cpow c (k - i))
                     (coeff f i * coeff g (k - i)) ck;
      let r0 = coeff qf i * coeff qg (k - i) in
      let r1 = (coeff f i * E.cpow c i) * (coeff g (k - i) * E.cpow c (k - i)) in
      let r2 = (coeff f i * coeff g (k - i)) * (E.cpow c i * E.cpow c (k - i)) in
      let r3 = (coeff f i * coeff g (k - i)) * ck in
      transitivity r0 r1 r2;
      transitivity r0 r2 r3;
      transitivity (qfn c f g k i) r3 r0
    end
#pop-options

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let lhs_as_sum (#t:Type) {| cr: commutative_ring t |} (c: t) (f g: polynomial t) (k: nat) (nn: nat)
  : Lemma (requires nn >= L.length f)
          (ensures coeff (qsubst c (f * g)) k = sum_range (qfn c f g k) 0 nn)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let ck = E.cpow c k in
    let lf = L.length f in
    qsubst_coeff c (f * g) k;
    let cb1 (i:nat) : Lemma (lconv f g k i = coeff f i * coeff g (k - i)) =
      lconv_unfold f g k i in
    CC.coeff_poly_mul_named f g k (lconv f g k) cb1;
    let s_lconv = sum_range (lconv f g k) 0 lf in
    mul_congruence (coeff (f * g) k) ck s_lconv ck;
    transitivity (coeff (qsubst c (f * g)) k) (coeff (f * g) k * ck) (s_lconv * ck);
    sum_range_mul_right (lconv f g k) ck 0 lf;
    let s_pw = sum_range (pointwise_mul (lconv f g k) (const ck)) 0 lf in
    transitivity (coeff (qsubst c (f * g)) k) (s_lconv * ck) s_pw;
    let bridge (i:nat{0 <= i /\ i < lf})
      : Lemma (pointwise_mul (lconv f g k) (const ck) i = qfn c f g k i) =
      pointwise_mul_unfold (lconv f g k) (const ck) i;
      const_unfold ck i;
      lconv_unfold f g k i;
      qfn_unfold c f g k i in
    sum_range_congruence (pointwise_mul (lconv f g k) (const ck)) (qfn c f g k) 0 lf bridge;
    let s_qfn_lf = sum_range (qfn c f g k) 0 lf in
    transitivity (coeff (qsubst c (f * g)) k) s_pw s_qfn_lf;
    let tail (i:nat{lf <= i /\ i < nn}) : Lemma (qfn c f g k i = zero) =
      qfn_unfold c f g k i;
      mul_congruence (coeff f i) (coeff g (k - i)) (zero <: t) (coeff g (k - i));
      H.zero_mul_x (coeff g (k - i));
      let a = coeff f i * coeff g (k - i) in
      transitivity a ((zero <: t) * coeff g (k - i)) (zero <: t);
      mul_congruence a ck (zero <: t) ck;
      H.zero_mul_x ck;
      transitivity (a * ck) ((zero <: t) * ck) (zero <: t) in
    sum_extend (qfn c f g k) lf nn tail;
    transitivity (coeff (qsubst c (f * g)) k) s_qfn_lf (sum_range (qfn c f g k) 0 nn)
#pop-options

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let rhs_as_sum (#t:Type) {| cr: commutative_ring t |} (c: t) (f g: polynomial t) (k: nat) (nn: nat)
  : Lemma (requires nn >= L.length (qsubst c f))
          (ensures coeff ((qsubst c f) * (qsubst c g)) k = sum_range (qfn c f g k) 0 nn)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let qf = qsubst c f in
    let qg = qsubst c g in
    let lqf = L.length qf in
    let cbR (i:nat) : Lemma (qfn c f g k i = coeff qf i * coeff qg (k - i)) =
      qmul_term c f g k i in
    CC.coeff_poly_mul_named qf qg k (qfn c f g k) cbR;
    let tail (i:nat{lqf <= i /\ i < nn}) : Lemma (qfn c f g k i = zero) =
      qmul_term c f g k i;
      mul_congruence (coeff qf i) (coeff qg (k - i)) (zero <: t) (coeff qg (k - i));
      H.zero_mul_x (coeff qg (k - i));
      transitivity (coeff qf i * coeff qg (k - i)) ((zero <: t) * coeff qg (k - i)) (zero <: t);
      transitivity (qfn c f g k i) (coeff qf i * coeff qg (k - i)) (zero <: t) in
    sum_extend (qfn c f g k) lqf nn tail;
    transitivity (coeff (qf * qg) k) (sum_range (qfn c f g k) 0 lqf) (sum_range (qfn c f g k) 0 nn)
#pop-options

let qsubst_mul (#t:Type) {| cr: commutative_ring t |} (c: t) (f g: polynomial t)
  : Lemma (qsubst c (f * g) = (qsubst c f) * (qsubst c g))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let aux (k:nat) : Lemma (coeff (qsubst c (f * g)) k = coeff ((qsubst c f) * (qsubst c g)) k) =
      let nn = Prims.op_Addition (L.length f) (L.length (qsubst c f)) in
      lhs_as_sum c f g k nn;
      rhs_as_sum c f g k nn;
      transitivity (coeff (qsubst c (f * g)) k)
                   (sum_range (qfn c f g k) 0 nn)
                   (coeff ((qsubst c f) * (qsubst c g)) k) in
    poly_eq_by_coeff (qsubst c (f * g)) ((qsubst c f) * (qsubst c g)) aux

(* ================================================================ *)
(*  poly_scale algebra + DERIVATIVE relation.                       *)
(* ================================================================ *)

let poly_scale_one (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (R.poly_scale one p = p)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let per (j:nat) : Lemma (coeff (R.poly_scale one p) j = coeff p j) =
      poly_mul_singleton_coeff one p j;
      H.one_mul_x (coeff p j)
    in
    poly_eq_by_coeff (R.poly_scale one p) p per

let poly_scale_scale (#t:Type) {| cr: commutative_ring t |} (a b: t) (p: polynomial t)
  : Lemma (R.poly_scale a (R.poly_scale b p) = R.poly_scale (a * b) p)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let per (j:nat)
      : Lemma (coeff (R.poly_scale a (R.poly_scale b p)) j
             = coeff (R.poly_scale (a * b) p) j) =
      poly_mul_singleton_coeff a (R.poly_scale b p) j;
      poly_mul_singleton_coeff b p j;
      mul_congruence a (coeff (R.poly_scale b p) j) a (b * coeff p j);
      poly_mul_singleton_coeff (a * b) p j;
      mul_associativity a b (coeff p j)
    in
    poly_eq_by_coeff (R.poly_scale a (R.poly_scale b p)) (R.poly_scale (a * b) p) per

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let qsubst_deriv (#t:Type) {| cr: commutative_ring t |} (c: t) (f: polynomial t)
  : Lemma (poly_deriv (qsubst c f) = R.poly_scale c (qsubst c (poly_deriv f)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let lhs = poly_deriv (qsubst c f) in
    let rhs = R.poly_scale c (qsubst c (poly_deriv f)) in
    let per (j:nat) : Lemma (coeff lhs j = coeff rhs j) =
      let n  = j ++ 1 in
      let x  = coeff f n in
      let cj = E.cpow c j in
      let dpf = poly_deriv f in
      let qf  = qsubst c f in
      let qd  = qsubst c dpf in
      poly_deriv_coeff qf j;
      qsubst_coeff c f n;
      nat_scale_congruence n (coeff qf n) (x * E.cpow c n);
      assert (E.cpow c n == c * cj);
      poly_mul_singleton_coeff c qd j;
      qsubst_coeff c dpf j;
      poly_deriv_coeff f j;
      mul_congruence (coeff dpf j) cj (nat_scale n x) cj;
      mul_congruence c (coeff qd j) c (nat_scale n x * cj);
      nat_scale_mul_left n x cj;
      mul_congruence c (nat_scale n x * cj) c (nat_scale n (x * cj));
      nat_scale_mul_right n c (x * cj);
      assert (x * (c * cj) = c * (x * cj)) by (Core.Tactics.CanonRing.canon_ring ());
      nat_scale_congruence n (x * (c * cj)) (c * (x * cj))
    in
    poly_eq_by_coeff lhs rhs per
#pop-options

(* ================================================================ *)
(*  Bezout ⟹ coprime  (generic field-polynomial lemma).            *)
(* ================================================================ *)

let divisor_of_nonzero_deg (#t:Type) {| f: field t |} (d u: polynomial t)
  : Lemma (requires divides d u /\ deg u >= 0)
          (ensures  deg d >= 0)
  = H.elim_equatable_laws (polynomial t) ();
    if deg d < 0 then begin
      assert (d == (poly_zero #t));
      eliminate exists (c: polynomial t). u = (d * c)
      returns deg d >= 0
      with _hc. begin
        H.zero_mul_x #(polynomial t) c;
        transitivity u (d * c) (poly_zero #t);
        degree_well_defined u (poly_zero #t)
      end
    end

let bezout_coprime (#t:Type) {| f: field t |} (u v a b k: polynomial t)
  : Lemma (requires (a * u + b * v) = k /\ deg k = 0 /\ deg u >= 0)
          (ensures  coprime u v)
  = let d = poly_gcd u v in
    gcd_divides_left  u v;
    gcd_divides_right u v;
    divides_mul_left d a u;
    divides_mul_left d b v;
    divides_add d (a * u) (b * v);
    divides_congruence_right d (a * u + b * v) k;
    divisor_of_nonzero_deg d u;
    IRR.divides_degree_le d k;
    coprime_reveal u v

(* ================================================================ *)
(*  ABSTRACT THEOREM: qsubst by a nonzero unit preserves square-     *)
(*  freeness over any field.                                         *)
(* ================================================================ *)

let poly_scale_poly_congr (#t:Type) {| cr: commutative_ring t |} (s: t) (a b: polynomial t)
  : Lemma (requires a = b) (ensures R.poly_scale s a = R.poly_scale s b)
  = H.elim_equatable_laws (polynomial t) ();
    reflexivity (s @ poly_zero);
    mul_congruence (s @ poly_zero) a (s @ poly_zero) b

let qsubst_deriv_solved (#t:Type) {| f: field t |} (c: t) (g: polynomial t)
  : Lemma (requires not (c = (zero <: t)))
          (ensures  qsubst c (poly_deriv g)
                    = R.poly_scale (inv c) (poly_deriv (qsubst c g)))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let qg  = qsubst c g in
    let qg' = qsubst c (poly_deriv g) in
    qsubst_deriv c g;
    poly_scale_poly_congr (inv c) (poly_deriv qg) (R.poly_scale c qg');
    poly_scale_scale (inv c) c qg';
    inversion_lemma c;
    R.poly_scale_scalar_congr (inv c * c) (one <: t) qg';
    poly_scale_one qg';
    let s1 = R.poly_scale (inv c) (poly_deriv qg) in
    let s2 = R.poly_scale (inv c) (R.poly_scale c qg') in
    let s3 = R.poly_scale (inv c * c) qg' in
    let s4 = R.poly_scale (one <: t) qg' in
    transitivity s1 s2 s3;
    transitivity s1 s3 s4;
    transitivity s1 s4 qg';
    symmetry s1 qg'

#push-options "--z3rlimit 40"
let qsubst_preserves_square_free (#t:Type) {| f: field t |} (c: t) (g: polynomial t)
  : Lemma (requires not (c = (zero <: t)) /\ deg g >= 1 /\ SF.square_free g)
          (ensures  SF.square_free (qsubst c g))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let g'  = poly_deriv g in
    let qg  = qsubst c g in
    let qg' = qsubst c g' in
    coprime_reveal g g';
    let (a, b0, gg) = poly_ext_gcd g g' in
    ext_gcd_correct g g';
    ext_gcd_is_gcd  g g';
    degree_well_defined gg (poly_gcd g g');
    let qa  = qsubst c a in
    let qb0 = qsubst c b0 in
    qsubst_add c (a * g) (b0 * g');
    qsubst_mul c a g;
    qsubst_mul c b0 g';
    add_congruence (qsubst c (a * g)) (qsubst c (b0 * g')) (qa * qg) (qb0 * qg');
    qsubst_congr c (a * g + b0 * g') gg;
    qsubst_const c gg;
    let lhs0 = qsubst c (a * g + b0 * g') in
    let mid0 = qsubst c (a * g) + qsubst c (b0 * g') in
    let sum0 = (qa * qg) + (qb0 * qg') in
    transitivity lhs0 mid0 sum0;
    symmetry lhs0 sum0;
    transitivity sum0 lhs0 gg;
    qsubst_deriv_solved c g;
    let u'  = poly_deriv qg in
    MON.poly_scale_eq_const_mul (inv c) u';
    let bb = qb0 * (poly_const (inv c)) in
    poly_mul_associativity qb0 (poly_const (inv c)) u';
    mul_congruence qb0 qg' qb0 (R.poly_scale (inv c) u');
    mul_congruence qb0 (R.poly_scale (inv c) u') qb0 (poly_const (inv c) * u');
    let t1 = qb0 * qg' in
    let t2 = qb0 * (R.poly_scale (inv c) u') in
    let t3 = qb0 * (poly_const (inv c) * u') in
    let t4 = bb * u' in
    transitivity t1 t2 t3;
    symmetry ((qb0 * poly_const (inv c)) * u') (qb0 * (poly_const (inv c) * u'));
    transitivity t1 t3 t4;
    add_congruence (qa * qg) (qb0 * qg') (qa * qg) (bb * u');
    let sum1 = (qa * qg) + (bb * u') in
    symmetry sum0 sum1;
    transitivity sum1 sum0 gg;
    qsubst_nonzero c g;
    bezout_coprime qg u' qa bb gg;
    coprime_reveal qg u'
#pop-options

let pc_inv_mul_pc (#t:Type) {| f: field t |} (a: t)
  : Lemma (requires not (a = (zero <: t)))
          (ensures (poly_const (inv a)) * (poly_const a) = (poly_one #t))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    poly_const_mul (inv a) a;
    inversion_lemma a;
    poly_const_congr (inv a * a) (one <: t);
    poly_const_one #t ();
    let e0 = poly_const (inv a) * poly_const a in
    let e1 = poly_const (inv a * a) in
    let e2 = poly_const (one <: t) in
    symmetry e1 e0;
    transitivity e0 e1 e2;
    transitivity e0 e2 (poly_one #t)

let scaled_bezout_term (#t:Type) {| f: field t |} (a: t) (w q: polynomial t)
  : Lemma (requires not (a = (zero <: t)))
          (ensures (w * (poly_const (inv a))) * ((poly_const a) * q) = w * q)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let pci = poly_const (inv a) in
    let pca = poly_const a in
    poly_mul_associativity w pci (pca * q);
    poly_mul_associativity pci pca q;
    symmetry ((pci * pca) * q) (pci * (pca * q));
    pc_inv_mul_pc a;
    reflexivity q;
    mul_congruence (pci * pca) q (poly_one #t) q;
    H.one_mul_x #(polynomial t) q;
    let e0 = (w * pci) * (pca * q) in
    let e1 = w * (pci * (pca * q)) in
    let e2 = w * ((pci * pca) * q) in
    let e3 = w * ((poly_one #t) * q) in
    reflexivity w;
    mul_congruence w (pci * (pca * q)) w ((pci * pca) * q);
    mul_congruence w ((pci * pca) * q) w ((poly_one #t) * q);
    mul_congruence w ((poly_one #t) * q) w q;
    transitivity e0 e1 e2;
    transitivity e0 e2 e3;
    transitivity e0 e3 (w * q)

let poly_scale_nonzero (#t:Type) {| f: field t |} (a: t) (p: polynomial t)
  : Lemma (requires not (a = (zero <: t)) /\ deg p >= 0)
          (ensures  deg (R.poly_scale a p) >= 0)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let n : nat = deg p in
    let sp = R.poly_scale a p in
    poly_mul_singleton_coeff a p n;
    leading_coeff_nonzero p;
    domain_nonzero_mul_nonzero a (coeff p n);
    if deg sp < 0 then begin
      coeff_above_degree sp n;
      symmetry (coeff sp n) (zero <: t);
      transitivity (zero <: t) (coeff sp n) (a * coeff p n)
    end

#push-options "--z3rlimit 40"
let scale_square_free (#t:Type) {| f: field t |} (a: t) (p: polynomial t)
  : Lemma (requires not (a = (zero <: t)) /\ deg p >= 1 /\ SF.square_free p)
          (ensures  SF.square_free (R.poly_scale a p))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let p'  = poly_deriv p in
    let sp  = R.poly_scale a p in
    let spd = poly_deriv sp in
    let pca = poly_const a in
    MON.poly_scale_eq_const_mul a p;
    poly_deriv_scalar_mul a p;
    MON.poly_scale_eq_const_mul a p';
    let sd_raw = (a @ poly_zero) * p' in
    transitivity spd sd_raw (pca * p');
    coprime_reveal p p';
    let (u, v, k) = poly_ext_gcd p p' in
    ext_gcd_correct p p';
    ext_gcd_is_gcd  p p';
    degree_well_defined k (poly_gcd p p');
    let pci = poly_const (inv a) in
    let aa  = u * pci in
    let bb  = v * pci in
    scaled_bezout_term a u p;
    mul_congruence aa sp aa (pca * p);
    transitivity (aa * sp) (aa * (pca * p)) (u * p);
    scaled_bezout_term a v p';
    mul_congruence bb spd bb (pca * p');
    transitivity (bb * spd) (bb * (pca * p')) (v * p');
    add_congruence (aa * sp) (bb * spd) (u * p) (v * p');
    let lhsb = (aa * sp) + (bb * spd) in
    let s0 = (u * p) + (v * p') in
    transitivity lhsb s0 k;
    poly_scale_nonzero a p;
    bezout_coprime sp spd aa bb k;
    coprime_reveal sp spd
#pop-options

(* square-freeness respects poly_eq. *)
let square_free_congr (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires p = q) (ensures SF.square_free p == SF.square_free q)
  = poly_deriv_congruence p q;                          (* poly_deriv p = poly_deriv q *)
    gcd_congruence p q (poly_deriv p) (poly_deriv q);   (* poly_gcd p p' = poly_gcd q q' *)
    degree_well_defined (poly_gcd p (poly_deriv p)) (poly_gcd q (poly_deriv q));
    coprime_reveal p (poly_deriv p);
    coprime_reveal q (poly_deriv q)

(* ================================================================ *)
(*  Field power/inverse cancellation:  l^k * (l^-1)^j = l^(k-j).     *)
(* ================================================================ *)

#push-options "--fuel 2 --ifuel 1"
let rec cpow_mul_inv (#t:Type) {| f: field t |} (l: t) (k j: nat)
  : Lemma (requires not (l = (zero <: t)) /\ j <= k)
          (ensures  E.cpow l k * E.cpow (inv l) j = E.cpow l (k - j))
          (decreases j)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if j = 0 then
      H.x_mul_one (E.cpow l k)          (* cpow l k * (cpow (inv l) 0 = one) = cpow l k *)
    else begin
      (* cpow l k * inv l = cpow l (k-1) *)
      inversion_lemma l;                (* l * inv l = one *)
      assert ((l * E.cpow l (k - 1)) * inv l = (l * inv l) * E.cpow l (k - 1))
        by (Core.Tactics.CanonRing.canon_ring ());
      mul_congruence (l * inv l) (E.cpow l (k - 1)) (one <: t) (E.cpow l (k - 1));
      H.one_mul_x (E.cpow l (k - 1));
      let ck   = E.cpow l k in
      let ckm1 = E.cpow l (k - 1) in
      (* ck == l * ckm1  (fuel unfold, k >= 1) *)
      transitivity (ck * inv l) ((l * ckm1) * inv l) ((l * inv l) * ckm1);
      transitivity (ck * inv l) ((l * inv l) * ckm1) ((one <: t) * ckm1);
      transitivity (ck * inv l) ((one <: t) * ckm1) ckm1;   (* ck * inv l = ckm1 *)
      (* main chain *)
      let ij  = E.cpow (inv l) j in
      let ijm1 = E.cpow (inv l) (j - 1) in
      (* ij == inv l * ijm1 (fuel unfold, j >= 1) *)
      mul_congruence ck ij ck (inv l * ijm1);
      mul_associativity ck (inv l) ijm1;                    (* (ck*inv l)*ijm1 = ck*(inv l*ijm1) *)
      symmetry ((ck * inv l) * ijm1) (ck * (inv l * ijm1));
      mul_congruence (ck * inv l) ijm1 ckm1 ijm1;           (* (ck*inv l)*ijm1 = ckm1*ijm1 *)
      cpow_mul_inv l (k - 1) (j - 1);                       (* ckm1 * ijm1 = cpow l ((k-1)-(j-1)) *)
      transitivity (ck * ij) (ck * (inv l * ijm1)) ((ck * inv l) * ijm1);
      transitivity (ck * ij) ((ck * inv l) * ijm1) (ckm1 * ijm1);
      transitivity (ck * ij) (ckm1 * ijm1) (E.cpow l (k - j))
    end
#pop-options

(* ================================================================ *)
(*  ℚ GLUE:  monic-ization preserves ℚ-square-freeness.             *)
(*                                                                   *)
(*  Over ℚ,  embed(monicize b) = L^(n-1) · (embed b)(x/L)  (L the    *)
(*  leading coeff, n = deg b), a nonzero-unit scalar times the image *)
(*  of embed b under the ℚ-automorphism x ↦ x/L.  Combined with the  *)
(*  abstract theorems above this yields the bridge.                  *)
(* ================================================================ *)

(* Local field instance so TC resolves `inv` / ring ops on ℚ. *)
instance _ffq : field EQ.qq = BIN.ff

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"

let rec cpow_congr_gen (#t:Type) {| cr: commutative_ring t |} (a b: t) (k:nat)
  : Lemma (requires a = b) (ensures E.cpow a k = E.cpow b k) (decreases k)
  = H.elim_equatable_laws t ();
    if k = 0 then ()
    else begin
      cpow_congr_gen a b (k - 1);
      mul_congruence a (E.cpow a (k - 1)) b (E.cpow b (k - 1))
    end

let rr_top (#t:Type) {| cr: commutative_ring t |} (sc lq cc: t)
  : Lemma (sc * (lq * cc) = (lq * sc) * cc)
  = assert (sc * (lq * cc) = (lq * sc) * cc) by (Core.Tactics.CanonRing.canon_ring ())

let rr_mid (#t:Type) {| cr: commutative_ring t |} (sc x y: t)
  : Lemma (sc * (x * y) = x * (sc * y))
  = assert (sc * (x * y) = x * (sc * y)) by (Core.Tactics.CanonRing.canon_ring ())

(* STEP 1 : embed_zq_const commutes with ipow / cpow. *)
let rec embed_ipow (l:int) (k:nat)
  : Lemma (ensures EQ.embed_zq_const (NMZ.ipow l k) = E.cpow (EQ.embed_zq_const l) k)
          (decreases k)
  = H.elim_equatable_laws EQ.qq ();
    H.trans_for_calc EQ.qq ();
    if k = 0 then
      BIN.embed_const_one ()
    else begin
      let el = EQ.embed_zq_const l in
      let p  = NMZ.ipow l (k - 1) in
      BIN.embed_const_mul l p;
      embed_ipow l (k - 1);
      mul_congruence el (EQ.embed_zq_const p) el (E.cpow el (k - 1));
      let e_lk = EQ.embed_zq_const (NMZ.ipow l k) in
      let bB   = el * EQ.embed_zq_const p in
      let cC   = el * E.cpow el (k - 1) in
      transitivity e_lk bB cC
    end

let lq_is_embed_lc (b: polynomial int{deg b >= 1})
  : Lemma (EQ.embed_zq_const (poly_lc b) = coeff (EQ.embed_zq b) (deg b))
  = H.elim_equatable_laws EQ.qq ();
    let n : nat = deg b in
    last_eq_index b n;
    poly_lc_reveal b;
    EQ.embed_zq_coeff b n;
    symmetry (coeff (EQ.embed_zq b) n) (EQ.embed_zq_const (coeff b n))

let top_val (#t:Type) {| f: field t |} (lq: t) (n:nat)
  : Lemma (requires not (lq = (zero <: t)) /\ n >= 1)
          (ensures (lq * E.cpow lq (n - 1)) * E.cpow (inv lq) n = (one <: t))
  = H.elim_equatable_laws t ();
    cpow_mul_inv lq n n

let mid_val (#t:Type) {| f: field t |} (lq: t) (n i:nat)
  : Lemma (requires not (lq = (zero <: t)) /\ i <= n - 1 /\ n >= 1)
          (ensures E.cpow lq (n - 1) * E.cpow (inv lq) i = E.cpow lq (n - 1 - i))
  = cpow_mul_inv lq (n - 1) i

(* STEP 2 : the scale identity, coefficient-wise. *)
#push-options "--z3rlimit 80"
let mes_coeff (b: polynomial int{deg b >= 1}) (i:nat)
  : Lemma (requires not (coeff (EQ.embed_zq b) (deg b) = (zero <: EQ.qq)))
          (ensures coeff (EQ.embed_zq (NMZ.monicize b)) i
           = coeff (R.poly_scale (E.cpow (coeff (EQ.embed_zq b) (deg b)) (deg b - 1))
                                 (qsubst (inv (coeff (EQ.embed_zq b) (deg b))) (EQ.embed_zq b))) i)
  = H.elim_equatable_laws EQ.qq ();
    H.trans_for_calc EQ.qq ();
    let n : nat = deg b in
    let eb = EQ.embed_zq b in
    let lq = coeff eb (deg b) in
    let ci = inv lq in
    let sc = E.cpow lq (deg b - 1) in
    let qs = qsubst ci eb in
    let lhs0 = coeff (EQ.embed_zq (NMZ.monicize b)) i in
    let r0   = coeff (R.poly_scale sc qs) i in
    NMZ.monicize_embed_coeff b i;
    let ez = EQ.embed_zq_const
               (if i < 0 || i > deg b then 0
                else if i = deg b then 1
                else coeff b i * NMZ.ipow (poly_lc b) (deg b - 1 - i)) in
    poly_mul_singleton_coeff sc qs i;
    qsubst_coeff ci eb i;
    mul_congruence sc (coeff qs i) sc (coeff eb i * E.cpow ci i);
    let rr = sc * (coeff eb i * E.cpow ci i) in
    transitivity r0 (sc * coeff qs i) rr;
    EQ.embed_zq_deg b;
    if i > n then begin
      EQ.embed_zq_const_zero ();
      coeff_above_degree eb i;
      mul_congruence (coeff eb i) (E.cpow ci i) (zero <: EQ.qq) (E.cpow ci i);
      H.zero_mul_x (E.cpow ci i);
      transitivity (coeff eb i * E.cpow ci i) ((zero <: EQ.qq) * E.cpow ci i) (zero <: EQ.qq);
      mul_congruence sc (coeff eb i * E.cpow ci i) sc (zero <: EQ.qq);
      H.x_mul_zero sc;
      transitivity rr (sc * (zero <: EQ.qq)) (zero <: EQ.qq);
      transitivity r0 rr (zero <: EQ.qq);
      transitivity lhs0 ez (zero <: EQ.qq);
      symmetry r0 (zero <: EQ.qq);
      transitivity lhs0 (zero <: EQ.qq) r0
    end
    else if i = n then begin
      BIN.embed_const_one ();
      let cc = E.cpow ci n in
      rr_top sc lq cc;
      top_val lq n;
      transitivity r0 rr (one <: EQ.qq);
      transitivity lhs0 ez (one <: EQ.qq);
      symmetry r0 (one <: EQ.qq);
      transitivity lhs0 (one <: EQ.qq) r0
    end
    else begin
      let e : nat = n - 1 - i in
      BIN.embed_const_mul (coeff b i) (NMZ.ipow (poly_lc b) e);
      embed_ipow (poly_lc b) e;
      lq_is_embed_lc b;
      cpow_congr_gen (EQ.embed_zq_const (poly_lc b)) lq e;
      EQ.embed_zq_coeff b i;
      symmetry (coeff eb i) (EQ.embed_zq_const (coeff b i));
      let tm = coeff eb i * E.cpow lq e in
      mul_congruence (EQ.embed_zq_const (coeff b i)) (EQ.embed_zq_const (NMZ.ipow (poly_lc b) e))
                     (EQ.embed_zq_const (coeff b i)) (E.cpow (EQ.embed_zq_const (poly_lc b)) e);
      mul_congruence (EQ.embed_zq_const (coeff b i)) (E.cpow (EQ.embed_zq_const (poly_lc b)) e)
                     (EQ.embed_zq_const (coeff b i)) (E.cpow lq e);
      mul_congruence (EQ.embed_zq_const (coeff b i)) (E.cpow lq e) (coeff eb i) (E.cpow lq e);
      transitivity ez (EQ.embed_zq_const (coeff b i) * EQ.embed_zq_const (NMZ.ipow (poly_lc b) e))
                      (EQ.embed_zq_const (coeff b i) * E.cpow (EQ.embed_zq_const (poly_lc b)) e);
      transitivity ez (EQ.embed_zq_const (coeff b i) * E.cpow (EQ.embed_zq_const (poly_lc b)) e)
                      (EQ.embed_zq_const (coeff b i) * E.cpow lq e);
      transitivity ez (EQ.embed_zq_const (coeff b i) * E.cpow lq e) tm;
      rr_mid sc (coeff eb i) (E.cpow ci i);
      mid_val lq n i;
      mul_congruence (coeff eb i) (sc * E.cpow ci i) (coeff eb i) (E.cpow lq e);
      transitivity rr (coeff eb i * (sc * E.cpow ci i)) tm;
      transitivity r0 rr tm;
      transitivity lhs0 ez tm;
      symmetry r0 tm;
      transitivity lhs0 tm r0
    end
#pop-options

let monicize_embed_scale (b: polynomial int{deg b >= 1})
  : Lemma (requires not (coeff (EQ.embed_zq b) (deg b) = (zero <: EQ.qq)))
          (ensures EQ.embed_zq (NMZ.monicize_pos b)
           = R.poly_scale (E.cpow (coeff (EQ.embed_zq b) (deg b)) (deg b - 1))
                          (qsubst (inv (coeff (EQ.embed_zq b) (deg b))) (EQ.embed_zq b)))
  = let h (j:nat)
      : Lemma (coeff (EQ.embed_zq (NMZ.monicize b)) j
               = coeff (R.poly_scale (E.cpow (coeff (EQ.embed_zq b) (deg b)) (deg b - 1))
                                     (qsubst (inv (coeff (EQ.embed_zq b) (deg b))) (EQ.embed_zq b))) j)
      = mes_coeff b j in
    poly_eq_by_coeff (EQ.embed_zq (NMZ.monicize b))
      (R.poly_scale (E.cpow (coeff (EQ.embed_zq b) (deg b)) (deg b - 1))
                    (qsubst (inv (coeff (EQ.embed_zq b) (deg b))) (EQ.embed_zq b)))
      h

let inv_nonzero (#t:Type) {| f: field t |} (x:t)
  : Lemma (requires not (x = (zero <: t))) (ensures not (inv x = (zero <: t)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    inversion_lemma x;
    if inv x = (zero <: t) then begin
      mul_congruence x (inv x) x (zero <: t);
      H.x_mul_zero x;
      transitivity (x * inv x) (x * (zero <: t)) (zero <: t);
      symmetry (x * inv x) (zero <: t);
      transitivity (one <: t) (x * inv x) (zero <: t)
    end

(* STEP 3 : THE BRIDGE. *)
let monicize_sqfree_bridge (b: polynomial int{deg b >= 1})
  : Lemma (requires SF.square_free #EQ.qq #BIN.ff (EQ.embed_zq b))
          (ensures  SF.square_free #EQ.qq #BIN.ff (EQ.embed_zq (NMZ.monicize_pos b)))
  = let eb = EQ.embed_zq b in
    let lq = coeff eb (deg b) in
    EQ.embed_zq_deg b;
    leading_coeff_nonzero eb;
    let ci = inv lq in
    inv_nonzero lq;
    let sc = E.cpow lq (deg b - 1) in
    let qs = qsubst ci eb in
    qsubst_preserves_square_free #EQ.qq #BIN.ff ci eb;
    cpow_nonzero lq (deg b - 1);
    qsubst_deg_ge #EQ.qq #BIN.ff ci eb;
    scale_square_free #EQ.qq #BIN.ff sc qs;
    monicize_embed_scale b;
    square_free_congr #EQ.qq #BIN.ff (EQ.embed_zq (NMZ.monicize_pos b)) (R.poly_scale sc qs)
#pop-options
