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

(* c^i *)
let rec cpow (#t:Type) {| cr: commutative_ring t |} (c: t) (i: nat)
  : Tot t (decreases i)
  = if i = 0 then one else c * cpow c (i - 1)

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
  : Lemma (requires i >= L.length p) (ensures eval_term p c i = zero)
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
    add_congruence (sum_range f 0 lp) (sum_range f lp n) (sum_range f 0 lp) zero;
    transitivity (sum_range f 0 n)
                 (sum_range f 0 lp + sum_range f lp n)
                 (sum_range f 0 lp + zero);
    transitivity (sum_range f 0 n)
                 (sum_range f 0 lp + zero)
                 (sum_range f 0 lp)

let eval_zero (#t:Type) {| cr: commutative_ring t |} (c: t)
  : Lemma (poly_eval (poly_zero) c = zero)
  = H.elim_equatable_laws t ();
    sum_range_empty (eval_term (poly_zero) c) 0 0;
    ()

let eval_congruence (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) (c: t)
  : Lemma (requires (p = q)) (ensures poly_eval p c = poly_eval q c)
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

(* poly_eval respects `=` in the POINT argument. *)
let eval_point_congruence (#t:Type) {| cr: commutative_ring t |}
  (q: polynomial t) (b c: t)
  : Lemma (requires b = c) (ensures poly_eval q b = poly_eval q c)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let rec cpow_congr (i:nat)
      : Lemma (ensures cpow b i = cpow c i) (decreases i)
      = if i = 0 then ()
        else begin
          cpow_congr (i - 1);
          mul_congruence b (cpow b (i - 1)) c (cpow c (i - 1))
        end in
    let step (i:nat{0 <= i /\ i < L.length q})
      : Lemma (eval_term q b i = eval_term q c i)
      = cpow_congr i;
        mul_congruence (coeff q i) (cpow b i) (coeff q i) (cpow c i) in
    sum_range_congruence (eval_term q b) (eval_term q c) 0 (L.length q) step

(* additivity *)
let eval_add (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) (c: t)
  : Lemma (poly_eval (p + q) c = poly_eval p c + poly_eval q c)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let s = (p + q) in
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
  : Lemma (poly_eval (- p) c = (- (poly_eval p c)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let np = (- p) in
    let n = L.length p + L.length np + 1 in
    let fp = eval_term p c in
    let fnp = eval_term np c in
    eval_extend p c n;
    eval_extend np c n;
    let step (i: nat{0 <= i /\ i < n}) : Lemma (fnp i = pointwise_neg fp i) =
      pointwise_neg_unfold fp i;
      poly_neg_coeff p i;
      mul_congruence (coeff np i) (cpow c i) (- (coeff p i)) (cpow c i);
      H.neg_mul_l (coeff p i) (cpow c i);
      transitivity (fnp i) ((- (coeff p i)) * cpow c i) (- (coeff p i * cpow c i))
    in
    sum_range_congruence fnp (pointwise_neg fp) 0 n step;
    sum_range_neg fp 0 n;
    neg_congruence (sum_range fp 0 n) (poly_eval p c);
    transitivity (poly_eval np c) (- (sum_range fp 0 n)) (- (poly_eval p c))

(* ============================================================ *)
(*  Multiplicative law -> poly_eval is a RING homomorphism      *)
(* ============================================================ *)

(* c^(i+j) = c^i * c^j *)
let rec cpow_add (#t:Type) {| cr: commutative_ring t |} (c: t) (i j: nat)
  : Lemma (ensures cpow c (i ++ j) = cpow c i * cpow c j)
          (decreases j)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if j = 0 then begin
      H.x_mul_one (cpow c i)                       (* cpow c i * one = cpow c i *)
    end else begin
      cpow_add c i (j - 1);      (* IH: cpow c (i+(j-1)) = cpow c i * cpow c (j-1) *)
      (* cpow c (i+j) = c * cpow c (i+(j-1)) = c * (cpow c i * cpow c (j-1)) *)
      mul_congruence c (cpow c (i ++ (j - 1)))
                     c (cpow c i * cpow c (j - 1));
      (* ring: c * (cpow c i * cpow c (j-1)) = cpow c i * (c * cpow c (j-1)) = cpow c i * cpow c j *)
      assert (c * (cpow c i * cpow c (j - 1))
            = cpow c i * (c * cpow c (j - 1)))
        by Core.Tactics.CanonRing.canon_ring ();
      transitivity (cpow c (i ++ j))
                   (c * cpow c (i ++ (j - 1)))
                   (c * (cpow c i * cpow c (j - 1)));
      transitivity (cpow c (i ++ j))
                   (c * (cpow c i * cpow c (j - 1)))
                   (cpow c i * (c * cpow c (j - 1)))
    end

(* per-k bridge: conv_sum(eval_term p c)(eval_term q c) k = coeff(pq) k * c^k *)
let conv_to_coeff (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) (c: t) (k: nat)
  : Lemma (conv_sum (eval_term p c) (eval_term q c) k = coeff ((p * q)) k * cpow c k)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let fp = eval_term p c in
    let fq = eval_term q c in
    let cc : nat -> t = fun (i:nat) -> coeff p i * coeff q (k - i) in
    let kk1 : nat = (k ++ 1) in
    let lp : nat = L.length p in
    let mm : nat = (kk1 ++ lp) in
    let ck : t = cpow c k in
    (* per-term on [0,kk1): conv_term fp fq k i = pointwise_mul cc (const ck) i *)
    let term_cb (i:nat{0 <= i /\ i < kk1}) : Lemma (conv_term fp fq k i = pointwise_mul cc (const ck) i) =
      conv_term_reveal fp fq k i;
      cpow_add c i (k - i);     (* cpow c k = cpow c i * cpow c (k-i) *)
      assert ((coeff p i * cpow c i) * (coeff q (k - i) * cpow c (k - i))
            = (coeff p i * coeff q (k - i)) * (cpow c i * cpow c (k - i)))
        by Core.Tactics.CanonRing.canon_ring ();
      mul_congruence (coeff p i * coeff q (k - i)) (cpow c i * cpow c (k - i))
                     (coeff p i * coeff q (k - i)) ck;
      transitivity (conv_term fp fq k i)
                   ((coeff p i * coeff q (k - i)) * (cpow c i * cpow c (k - i)))
                   ((coeff p i * coeff q (k - i)) * ck)
    in
    sum_range_congruence (conv_term fp fq k) (pointwise_mul cc (const ck)) 0 kk1 term_cb;
    sum_range_mul_right cc ck 0 kk1;             (* (Σ_kk1 cc) * ck = Σ_kk1 (pointwise_mul cc (const ck)) *)
    (* range reconcile: Σ cc 0 kk1 = Σ cc 0 lp  (= coeff(pq) k) via common mm *)
    sum_range_split cc 0 kk1 mm;
    sum_range_all_zero cc kk1 mm (fun (i:nat{kk1 <= i /\ i < mm}) -> H.x_mul_zero (coeff p i));
    H.x_plus_zero (sum_range cc 0 kk1);
    add_congruence (sum_range cc 0 kk1) (sum_range cc kk1 mm) (sum_range cc 0 kk1) zero;
    sum_range_split cc 0 lp mm;
    sum_range_all_zero cc lp mm (fun (i:nat{lp <= i /\ i < mm}) -> H.zero_mul_x (coeff q (k - i)));
    H.x_plus_zero (sum_range cc 0 lp);
    add_congruence (sum_range cc 0 lp) (sum_range cc lp mm) (sum_range cc 0 lp) zero;
    (* coeff(pq) k = Σ cc 0 lp *)
    coeff_poly_mul_named p q k cc H.obvious;
    (* assemble: conv_sum = Σcc0kk1 * ck = Σcc0lp * ck = coeff(pq)k * ck *)
    mul_congruence (sum_range cc 0 kk1) ck (sum_range cc 0 lp) ck;
    mul_congruence (sum_range cc 0 lp) ck (coeff ((p * q)) k) ck;
    conv_sum_reveal fp fq k;
    transitivity (conv_sum fp fq k) (sum_range cc 0 lp * ck) (coeff ((p * q)) k * ck)

(* coeff(pq) k = 0 (hence eval_term(pq) c k = 0) for k >= len p + len q *)
let pq_high (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) (c: t) (k: nat)
  : Lemma (requires k >= L.length p + L.length q)
          (ensures eval_term ((p * q)) c k = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cc : nat -> t = fun (i:nat) -> coeff p i * coeff q (k - i) in
    coeff_poly_mul_named p q k cc
      H.obvious;
    sum_range_all_zero cc 0 (L.length p)
      (fun (i:nat{0 <= i /\ i < L.length p}) -> H.x_mul_zero (coeff p i));
    H.zero_mul_x (cpow c k);
    mul_congruence (coeff ((p * q)) k) (cpow c k) zero (cpow c k);
    transitivity (eval_term ((p * q)) c k) (zero * cpow c k) zero

(* eval_mul: poly_eval(pq) c = poly_eval p c * poly_eval q c *)
let eval_mul (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) (c: t)
  : Lemma (poly_eval ((p * q)) c = poly_eval p c * poly_eval q c)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let fp = eval_term p c in
    let fq = eval_term q c in
    let bnd : nat = (L.length p ++ L.length q) in
    let mm : nat = (L.length (poly_mul p q) ++ bnd) in
    let etpq : nat -> t = eval_term ((p * q)) c in
    sum_range_convolution fp fq (L.length p) (L.length q)
      (fun (i:nat{i >= L.length p}) -> eval_term_high p c i)
      (fun (j:nat{j >= L.length q}) -> eval_term_high q c j);
    sum_range_congruence (conv_sum fp fq) etpq 0 bnd
      (fun (k:nat{0 <= k /\ k < bnd}) -> conv_to_coeff p q c k);
    eval_extend ((p * q)) c mm;
    sum_range_split etpq 0 bnd mm;
    sum_range_all_zero etpq bnd mm (fun (k:nat{bnd <= k /\ k < mm}) -> pq_high p q c k);
    H.x_plus_zero (sum_range etpq 0 bnd);
    add_congruence (sum_range etpq 0 bnd) (sum_range etpq bnd mm) (sum_range etpq 0 bnd) zero;
    transitivity (poly_eval ((p * q)) c) (sum_range etpq 0 mm)
                 (sum_range etpq 0 bnd + sum_range etpq bnd mm);
    transitivity (poly_eval ((p * q)) c) (sum_range etpq 0 bnd + sum_range etpq bnd mm)
                 (sum_range etpq 0 bnd + zero);
    transitivity (poly_eval ((p * q)) c) (sum_range (conv_sum fp fq) 0 bnd)
                 (poly_eval p c * poly_eval q c)

(* eval_one: poly_eval poly_one c = one *)
let eval_one (#t:Type) {| cr: commutative_ring t |} (c: t)
  : Lemma (poly_eval (poly_one) c = one)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if (one <: t) = zero then begin
      sum_range_empty (eval_term (poly_one) c) 0 0;
      transitivity (poly_eval (poly_one) c) zero one
    end else begin
      let f1 = eval_term (poly_one) c in
      sum_range_unfold_left f1 0 1;
      sum_range_empty f1 1 1;
      H.x_plus_zero (f1 0);
      add_congruence (f1 0) (sum_range f1 1 1) (f1 0) zero;
      H.x_mul_one (one <: t);                 (* one * one = one ; f1 0 == one * one *)
      transitivity (poly_eval (poly_one) c) (f1 0) one
    end

(* ===== merged from Core.Polynomial.EvalSum - eval commutes with sum/prod over a range ===== *)

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* eval (sum_range g lo hi) = sum_range (eval . g) lo hi. *)
let rec eval_sum_range (#t:Type) {| cr: commutative_ring t |}
  (g: nat -> polynomial t) (c: t) (lo hi: nat)
  : Lemma (ensures poly_eval
                     (sum_range g lo hi) c
                   = sum_range (fun (i:nat) -> poly_eval (g i) c) lo hi)
          (decreases (hi - lo))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let evg = (fun (i:nat) -> poly_eval (g i) c) in
    if lo >= hi then begin
      sum_range_empty g lo hi;
      sum_range_empty evg lo hi;
      eval_zero c
    end else begin
      let rest = sum_range g (lo ++ 1) hi in
      let sum' = sum_range evg (lo ++ 1) hi in
      sum_range_unfold_left g lo hi;  (* sum == poly_add (g lo) rest *)
      sum_range_unfold_left evg lo hi;
      eval_add (g lo) rest c;                       (* eval (poly_add (g lo) rest) = eval(g lo) + eval rest *)
      eval_sum_range g c (lo ++ 1) hi;           (* IH: eval rest = sum' *)

      add_congruence
                     (poly_eval (g lo) c) (poly_eval rest c)
                     (poly_eval (g lo) c) sum';
      transitivity (poly_eval ((g lo) + rest) c)
                   ((poly_eval (g lo) c) + (poly_eval rest c))
                   ((poly_eval (g lo) c) + sum')
    end

(* eval (prod_range g lo hi) = prod_range (eval . g) lo hi. *)
let rec eval_prod_range (#t:Type) {| cr: commutative_ring t |}
  (g: nat -> polynomial t) (c: t) (lo hi: nat)
  : Lemma (ensures poly_eval
                     (prod_range g lo hi) c
                   = prod_range (fun (i:nat) -> poly_eval (g i) c) lo hi)
          (decreases (hi - lo))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let evg = (fun (i:nat) -> poly_eval (g i) c) in
    if lo >= hi then begin
      prod_range_empty g lo hi;       (* == one == poly_one *)
      prod_range_empty evg lo hi;
      eval_one c                                      (* poly_eval poly_one c = one *)
    end else begin
      let rest = prod_range g (lo ++ 1) hi in
      let prod' = prod_range evg (lo ++ 1) hi in
      prod_range_unfold_left g lo hi;  (* prod == poly_mul (g lo) rest *)
      prod_range_unfold_left evg lo hi;
      eval_mul (g lo) rest c;                          (* eval (poly_mul (g lo) rest) = eval(g lo)*eval rest *)
      eval_prod_range g c (lo ++ 1) hi;            (* IH *)

      mul_congruence
                     (poly_eval (g lo) c) (poly_eval rest c)
                     (poly_eval (g lo) c) prod';
      transitivity (poly_eval ((g lo) * rest) c)
                   ((poly_eval (g lo) c) * (poly_eval rest c))
                   ((poly_eval (g lo) c) * prod')
    end

(* eval (sum_list xs) = sum_list (map (eval . _) xs).
   (sum_over_perms is sum_list over the permutation enumeration, so this is
    the bridge for the determinant specialization.) *)
let rec eval_sum_list (#t:Type) {| cr: commutative_ring t |}
  (xs: list (polynomial t)) (c: t)
  : Lemma (ensures poly_eval (sum_list xs) c
                   = sum_list
                       (L.map (fun (p: polynomial t) -> poly_eval p c) xs))
          (decreases xs)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match xs with
    | [] ->
      sum_list_nil #(polynomial t) #(polynomial_acg cr);
      sum_list_nil #t #(cr.cr_r.r_add);
      eval_zero c
    | p :: rest ->
      let prest = sum_list rest in
      let srest = sum_list
                    (L.map (fun (q: polynomial t) -> poly_eval q c) rest) in
      sum_list_cons p rest;   (* sum == poly_add p prest *)
      sum_list_cons (poly_eval p c)
                    (L.map (fun (q: polynomial t) -> poly_eval q c) rest);
      eval_add p prest c;                                   (* eval (poly_add p prest) = eval p + eval prest *)
      eval_sum_list rest c;                                 (* IH *)

      add_congruence
                     (poly_eval p c) (poly_eval prest c)
                     (poly_eval p c) srest;
      transitivity (poly_eval (p + prest) c)
                   ((poly_eval p c) + (poly_eval prest c))
                   ((poly_eval p c) + srest)
