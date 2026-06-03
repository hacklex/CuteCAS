module Core.Polynomial.Eval

(* poly_eval (evaluation map) — Prerequisite A. Additive-group homomorphism as a ring homomorphism polynomial t -> t.
   Defined directly as the coefficient sum  Σ_{i<len} coeff p i * c^i,
   so the ring-hom laws come from the public coeff lemmas + sum_range algebra
   (avoids the trimming smart-cons `@` that fights Horner induction). *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.FinSum
open Core.FinSum.Convolution

(* c^i *)
let rec cpow (#t:Type) {| cr: commutative_ring t |} (c: t) (i: nat)
  : Tot t (decreases i)
  = if i = 0 then one #t else c * cpow c (i - 1)

(* the i-th term  coeff p i * c^i  (named, so `eval_term p c : nat -> t`
   is a named function, not a lambda) *)
let eval_term (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t) (c: t) (i: nat) : t
  = coeff p i * cpow c i

(* evaluation = sum of terms over the support *)
let poly_eval (#t:Type) {| cr: commutative_ring t |} (p: polynomial t) (c: t) : t
  = sum_range (eval_term p c) 0 (L.length p)

(* terms beyond the length vanish (coeff = 0 there) *)
let eval_term_high (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t) (c: t) (i: nat)
  : Lemma (requires i >= L.length p) (ensures eval_term p c i = (zero <: t))
  = H.elim_equatable_laws t ();
    assert (coeff p i == (zero <: t));            (* from coeff's refinement *)
    H.zero_mul_x (cpow c i)                        (* zero * cpow c i = zero *)

(* summing past the length doesn't change the value *)
let eval_extend (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t) (c: t) (n: nat)
  : Lemma (requires n >= L.length p)
          (ensures sum_range (eval_term p c) 0 n = poly_eval p c)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let f = eval_term p c in
    let lp = L.length p in
    sum_range_split f 0 lp n;                      (* sum 0 n = sum 0 lp + sum lp n *)
    sum_range_all_zero f lp n (fun (k: nat{lp <= k /\ k < n}) -> eval_term_high p c k);
    H.x_plus_zero (sum_range f 0 lp);              (* (sum 0 lp) + zero = sum 0 lp *)
    add_congruence (sum_range f 0 lp) (sum_range f lp n) (sum_range f 0 lp) (zero <: t);
    transitivity (sum_range f 0 n)
                 (sum_range f 0 lp + sum_range f lp n)
                 (sum_range f 0 lp + (zero <: t));
    transitivity (sum_range f 0 n)
                 (sum_range f 0 lp + (zero <: t))
                 (sum_range f 0 lp)

let eval_zero (#t:Type) {| cr: commutative_ring t |} (c: t)
  : Lemma (poly_eval (poly_zero #t) c = (zero <: t))
  = H.elim_equatable_laws t ();
    sum_range_empty (eval_term (poly_zero #t) c) 0 0;
    reflexivity (zero <: t)

let eval_congruence (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) (c: t)
  : Lemma (requires poly_eq p q) (ensures poly_eval p c = poly_eval q c)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    poly_eq_length p q;                            (* L.length p == L.length q *)
    let f = eval_term p c in
    let g = eval_term q c in
    let step (i: nat{0 <= i /\ i < L.length p}) : Lemma (f i = g i) =
      poly_eq_means_equal_coeffs p q i;            (* coeff p i = coeff q i *)
      mul_congruence (coeff p i) (cpow c i) (coeff q i) (cpow c i)
    in
    sum_range_congruence f g 0 (L.length p) step

(* additivity *)
let eval_add (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) (c: t)
  : Lemma (poly_eval (poly_add p q) c = poly_eval p c + poly_eval q c)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let s = poly_add p q in
    let n = L.length p + L.length q + L.length s + 1 in
    let fp = eval_term p c in
    let fq = eval_term q c in
    let fs = eval_term s c in
    eval_extend p c n;
    eval_extend q c n;
    eval_extend s c n;
    let step (i: nat{0 <= i /\ i < n}) : Lemma (fs i = pointwise_add fp fq i) =
      poly_add_coeff p q i;
      mul_congruence (coeff s i) (cpow c i) (coeff p i + coeff q i) (cpow c i);
      right_distributivity (cpow c i) (coeff p i) (coeff q i);
      transitivity (fs i)
                   ((coeff p i + coeff q i) * cpow c i)
                   (coeff p i * cpow c i + coeff q i * cpow c i)
    in
    sum_range_congruence fs (pointwise_add fp fq) 0 n step;
    sum_range_add fp fq 0 n;
    add_congruence (sum_range fp 0 n) (sum_range fq 0 n) (poly_eval p c) (poly_eval q c);
    transitivity (poly_eval s c) (sum_range (pointwise_add fp fq) 0 n)
                 (sum_range fp 0 n + sum_range fq 0 n);
    transitivity (poly_eval s c) (sum_range fp 0 n + sum_range fq 0 n)
                 (poly_eval p c + poly_eval q c)

(* negation *)
let eval_neg (#t:Type) {| cr: commutative_ring t |} (p: polynomial t) (c: t)
  : Lemma (poly_eval (poly_neg p) c = neg (poly_eval p c))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let np = poly_neg p in
    let n = L.length p + L.length np + 1 in
    let fp = eval_term p c in
    let fnp = eval_term np c in
    eval_extend p c n;
    eval_extend np c n;
    let step (i: nat{0 <= i /\ i < n}) : Lemma (fnp i = neg (fp i)) =
      poly_neg_coeff p i;
      mul_congruence (coeff np i) (cpow c i) (neg (coeff p i)) (cpow c i);
      H.neg_mul_l (coeff p i) (cpow c i);
      transitivity (fnp i) (neg (coeff p i) * cpow c i) (neg (coeff p i * cpow c i))
    in
    sum_range_congruence fnp (fun (k:nat) -> neg (fp k)) 0 n step;
    sum_range_neg fp 0 n;
    neg_congruence (sum_range fp 0 n) (poly_eval p c);
    transitivity (poly_eval np c) (neg (sum_range fp 0 n)) (neg (poly_eval p c))

(* ============================================================ *)
(*  Multiplicative law -> poly_eval is a RING homomorphism      *)
(* ============================================================ *)

(* c^(i+j) = c^i * c^j *)
let rec cpow_add (#t:Type) {| cr: commutative_ring t |} (c: t) (i j: nat)
  : Lemma (ensures cpow c (Prims.op_Addition i j) = cpow c i * cpow c j)
          (decreases j)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if j = 0 then begin
      H.x_mul_one (cpow c i);                       (* cpow c i * one = cpow c i *)
      symmetry (cpow c i * one) (cpow c i)          (* cpow c i = cpow c i * one == cpow c i * cpow c 0 *)
    end else begin
      cpow_add c i (Prims.op_Subtraction j 1);      (* IH: cpow c (i+(j-1)) = cpow c i * cpow c (j-1) *)
      (* cpow c (i+j) = c * cpow c (i+(j-1)) = c * (cpow c i * cpow c (j-1)) *)
      mul_congruence c (cpow c (Prims.op_Addition i (Prims.op_Subtraction j 1)))
                     c (cpow c i * cpow c (Prims.op_Subtraction j 1));
      (* ring: c * (cpow c i * cpow c (j-1)) = cpow c i * (c * cpow c (j-1)) = cpow c i * cpow c j *)
      assert (c * (cpow c i * cpow c (Prims.op_Subtraction j 1))
            = cpow c i * (c * cpow c (Prims.op_Subtraction j 1)))
        by Core.Tactics.CanonRing.canon_ring ();
      transitivity (cpow c (Prims.op_Addition i j))
                   (c * cpow c (Prims.op_Addition i (Prims.op_Subtraction j 1)))
                   (c * (cpow c i * cpow c (Prims.op_Subtraction j 1)));
      transitivity (cpow c (Prims.op_Addition i j))
                   (c * (cpow c i * cpow c (Prims.op_Subtraction j 1)))
                   (cpow c i * (c * cpow c (Prims.op_Subtraction j 1)))
    end

(* per-k bridge: conv_sum(eval_term p c)(eval_term q c) k = coeff(pq) k * c^k *)
let conv_to_coeff (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) (c: t) (k: nat)
  : Lemma (conv_sum (eval_term p c) (eval_term q c) k = coeff (poly_mul p q) k * cpow c k)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let fp = eval_term p c in
    let fq = eval_term q c in
    let cc : nat -> t = fun (i:nat) -> coeff p i * coeff q (Prims.op_Subtraction k i) in
    let kk1 : nat = Prims.op_Addition k 1 in
    let lp : nat = L.length p in
    let mm : nat = Prims.op_Addition kk1 lp in
    let ck : t = cpow c k in
    (* per-term on [0,kk1): conv_term fp fq k i = pointwise_mul cc (const ck) i *)
    let term_cb (i:nat{0 <= i /\ i < kk1}) : Lemma (conv_term fp fq k i = pointwise_mul cc (const ck) i) =
      cpow_add c i (Prims.op_Subtraction k i);     (* cpow c k = cpow c i * cpow c (k-i) *)
      assert ((coeff p i * cpow c i) * (coeff q (Prims.op_Subtraction k i) * cpow c (Prims.op_Subtraction k i))
            = (coeff p i * coeff q (Prims.op_Subtraction k i)) * (cpow c i * cpow c (Prims.op_Subtraction k i)))
        by Core.Tactics.CanonRing.canon_ring ();
      mul_congruence (coeff p i * coeff q (Prims.op_Subtraction k i)) (cpow c i * cpow c (Prims.op_Subtraction k i))
                     (coeff p i * coeff q (Prims.op_Subtraction k i)) ck;
      transitivity (conv_term fp fq k i)
                   ((coeff p i * coeff q (Prims.op_Subtraction k i)) * (cpow c i * cpow c (Prims.op_Subtraction k i)))
                   ((coeff p i * coeff q (Prims.op_Subtraction k i)) * ck)
    in
    sum_range_congruence (conv_term fp fq k) (pointwise_mul cc (const ck)) 0 kk1 term_cb;
    sum_range_mul_right cc ck 0 kk1;             (* (Σ_kk1 cc) * ck = Σ_kk1 (pointwise_mul cc (const ck)) *)
    (* range reconcile: Σ cc 0 kk1 = Σ cc 0 lp  (= coeff(pq) k) via common mm *)
    sum_range_split cc 0 kk1 mm;
    sum_range_all_zero cc kk1 mm (fun (i:nat{kk1 <= i /\ i < mm}) -> H.x_mul_zero (coeff p i));
    H.x_plus_zero (sum_range cc 0 kk1);
    add_congruence (sum_range cc 0 kk1) (sum_range cc kk1 mm) (sum_range cc 0 kk1) (zero <: t);
    sum_range_split cc 0 lp mm;
    sum_range_all_zero cc lp mm (fun (i:nat{lp <= i /\ i < mm}) -> H.zero_mul_x (coeff q (Prims.op_Subtraction k i)));
    H.x_plus_zero (sum_range cc 0 lp);
    add_congruence (sum_range cc 0 lp) (sum_range cc lp mm) (sum_range cc 0 lp) (zero <: t);
    (* coeff(pq) k = Σ cc 0 lp *)
    coeff_poly_mul_named p q k cc (fun (i:nat) -> reflexivity (coeff p i * coeff q (Prims.op_Subtraction k i)));
    (* assemble: conv_sum = Σcc0kk1 * ck = Σcc0lp * ck = coeff(pq)k * ck *)
    mul_congruence (sum_range cc 0 kk1) ck (sum_range cc 0 lp) ck;
    mul_congruence (sum_range cc 0 lp) ck (coeff (poly_mul p q) k) ck;
    transitivity (conv_sum fp fq k) (sum_range cc 0 lp * ck) (coeff (poly_mul p q) k * ck)

(* coeff(pq) k = 0 (hence eval_term(pq) c k = 0) for k >= len p + len q *)
let pq_high (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) (c: t) (k: nat)
  : Lemma (requires k >= L.length p + L.length q)
          (ensures eval_term (poly_mul p q) c k = (zero <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cc : nat -> t = fun (i:nat) -> coeff p i * coeff q (Prims.op_Subtraction k i) in
    coeff_poly_mul_named p q k cc
      (fun (i:nat) -> reflexivity (coeff p i * coeff q (Prims.op_Subtraction k i)));
    sum_range_all_zero cc 0 (L.length p)
      (fun (i:nat{0 <= i /\ i < L.length p}) -> H.x_mul_zero (coeff p i));
    H.zero_mul_x (cpow c k);
    mul_congruence (coeff (poly_mul p q) k) (cpow c k) (zero <: t) (cpow c k);
    transitivity (eval_term (poly_mul p q) c k) ((zero <: t) * cpow c k) (zero <: t)

(* eval_mul: poly_eval(pq) c = poly_eval p c * poly_eval q c *)
let eval_mul (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) (c: t)
  : Lemma (poly_eval (poly_mul p q) c = poly_eval p c * poly_eval q c)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let fp = eval_term p c in
    let fq = eval_term q c in
    let bnd : nat = Prims.op_Addition (L.length p) (L.length q) in
    let mm : nat = Prims.op_Addition (L.length (poly_mul p q)) bnd in
    let etpq : nat -> t = eval_term (poly_mul p q) c in
    sum_range_convolution fp fq (L.length p) (L.length q)
      (fun (i:nat{i >= L.length p}) -> eval_term_high p c i)
      (fun (j:nat{j >= L.length q}) -> eval_term_high q c j);
    sum_range_congruence (conv_sum fp fq) etpq 0 bnd
      (fun (k:nat{0 <= k /\ k < bnd}) -> conv_to_coeff p q c k);
    eval_extend (poly_mul p q) c mm;
    sum_range_split etpq 0 bnd mm;
    sum_range_all_zero etpq bnd mm (fun (k:nat{bnd <= k /\ k < mm}) -> pq_high p q c k);
    H.x_plus_zero (sum_range etpq 0 bnd);
    add_congruence (sum_range etpq 0 bnd) (sum_range etpq bnd mm) (sum_range etpq 0 bnd) (zero <: t);
    transitivity (poly_eval (poly_mul p q) c) (sum_range etpq 0 mm)
                 (sum_range etpq 0 bnd + sum_range etpq bnd mm);
    transitivity (poly_eval (poly_mul p q) c) (sum_range etpq 0 bnd + sum_range etpq bnd mm)
                 (sum_range etpq 0 bnd + (zero <: t));
    transitivity (poly_eval (poly_mul p q) c) (sum_range (conv_sum fp fq) 0 bnd)
                 (poly_eval p c * poly_eval q c)

(* eval_one: poly_eval poly_one c = one *)
let eval_one (#t:Type) {| cr: commutative_ring t |} (c: t)
  : Lemma (poly_eval (poly_one #t) c = (one <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if (one <: t) = zero then begin
      sum_range_empty (eval_term (poly_one #t) c) 0 0;
      transitivity (poly_eval (poly_one #t) c) (zero <: t) (one <: t)
    end else begin
      let f1 = eval_term (poly_one #t) c in
      sum_range_unfold_left f1 0 1;
      sum_range_empty f1 1 1;
      H.x_plus_zero (f1 0);
      add_congruence (f1 0) (sum_range f1 1 1) (f1 0) (zero <: t);
      H.x_mul_one (one <: t);                 (* one * one = one ; f1 0 == one * one *)
      transitivity (poly_eval (poly_one #t) c) (f1 0) (one <: t)
    end

