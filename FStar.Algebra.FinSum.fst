module FStar.Algebra.FinSum

(*
  Finite sums and products over integer ranges and lists.

  Provides:
    sum_range  : (nat -> t) -> lo:nat -> hi:nat -> t   (over add_comm_monoid)
    prod_range : (nat -> t) -> lo:nat -> hi:nat -> t   (over mul_monoid)
    sum_list   : list t -> t                            (over add_comm_monoid)

  with basic congruence, step, and split lemmas.

  Designed for use in determinant and resultant constructions.

  Author: A. Rozanov (CuteCAS).
*)

module TC = FStar.Tactics.Typeclasses

open FStar.Algebra.Classes.Equatable
open FStar.Algebra.Classes.Grouplikes

(* Plain nat arithmetic helpers.  `open Grouplikes` above shadows the Prims
   `+` and `-` with typeclass-resolved versions; these helpers expose the
   primitive operations under fresh names. *)

unfold let nat_succ (n: nat) : nat = Prims.op_Addition n 1
unfold let nat_pred (n: nat{n > 0}) : nat = Prims.op_Subtraction n 1
unfold let nat_minus (a: nat) (b: nat) : int = Prims.op_Subtraction a b

(* ----------------------------------------------------------------- *)
(*  Sum over an integer range  [lo, hi)                              *)
(* ----------------------------------------------------------------- *)

let rec sum_range (#t:Type) {| m: add_comm_monoid t |}
                  (f: nat -> t) (lo hi: nat)
  : Tot t (decreases (if hi > lo then nat_minus hi lo else 0))
  = if lo >= hi then zero
    else f lo + sum_range f (nat_succ lo) hi

let sum_range_empty (#t:Type) {| m: add_comm_monoid t |}
                    (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo >= hi)
          (ensures sum_range f lo hi == zero)
  = ()

let sum_range_unfold_left (#t:Type) {| m: add_comm_monoid t |}
                          (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures sum_range f lo hi == f lo + sum_range f (nat_succ lo) hi)
  = ()

let sum_range_singleton (#t:Type) {| m: add_comm_monoid t |}
                        (f: nat -> t) (k: nat)
  : Lemma (sum_range f k (nat_succ k) = f k)
  = sum_range_unfold_left f k (nat_succ k);
    sum_range_empty f (nat_succ k) (nat_succ k);
    right_add_identity (f k)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec sum_range_congruence
  (#t:Type) {| m: add_comm_monoid t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (requires (forall (k:nat). lo <= k /\ k < hi ==> f k = g k))
          (ensures sum_range f lo hi = sum_range g lo hi)
          (decreases (if hi > lo then nat_minus hi lo else 0))
  = if lo >= hi then reflexivity (sum_range f lo hi)
    else begin
      sum_range_congruence f g (nat_succ lo) hi;
      reflexivity (f lo);
      add_congruence (f lo) (sum_range f (nat_succ lo) hi)
                     (g lo) (sum_range g (nat_succ lo) hi)
    end
#pop-options

(* Unfold from the right: sum_range f lo hi = sum_range f lo (hi-1) + f (hi-1). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec sum_range_unfold_right
  (#t:Type) {| m: add_comm_monoid t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures sum_range f lo hi = sum_range f lo (nat_pred hi) + f (nat_pred hi))
          (decreases nat_minus hi lo)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if nat_succ lo = hi then begin
      sum_range_unfold_left f lo hi;
      sum_range_empty f (nat_succ lo) hi;
      right_add_identity (f lo);
      sum_range_empty f lo (nat_pred hi);
      left_add_identity (f (nat_pred hi));
      symmetry (zero + f (nat_pred hi)) (f (nat_pred hi));
      add_congruence (sum_range f lo (nat_pred hi)) (f (nat_pred hi))
                     zero (f (nat_pred hi))
    end else begin
      sum_range_unfold_left f lo hi;
      sum_range_unfold_right f (nat_succ lo) hi;
      reflexivity (f lo);
      add_congruence (f lo) (sum_range f (nat_succ lo) hi)
                     (f lo) (sum_range f (nat_succ lo) (nat_pred hi) + f (nat_pred hi));
      add_associativity (f lo) (sum_range f (nat_succ lo) (nat_pred hi)) (f (nat_pred hi));
      sum_range_unfold_left f lo (nat_pred hi);
      symmetry (sum_range f lo (nat_pred hi))
               (f lo + sum_range f (nat_succ lo) (nat_pred hi));
      reflexivity (f (nat_pred hi));
      add_congruence (f lo + sum_range f (nat_succ lo) (nat_pred hi)) (f (nat_pred hi))
                     (sum_range f lo (nat_pred hi)) (f (nat_pred hi))
    end
#pop-options

(* ----------------------------------------------------------------- *)
(*  Product over an integer range  [lo, hi)                          *)
(* ----------------------------------------------------------------- *)

let rec prod_range (#t:Type) {| m: mul_monoid t |}
                   (f: nat -> t) (lo hi: nat)
  : Tot t (decreases (if hi > lo then nat_minus hi lo else 0))
  = if lo >= hi then one
    else f lo * prod_range f (nat_succ lo) hi

let prod_range_empty (#t:Type) {| m: mul_monoid t |}
                     (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo >= hi)
          (ensures prod_range f lo hi == one)
  = ()

let prod_range_unfold_left (#t:Type) {| m: mul_monoid t |}
                           (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures prod_range f lo hi == f lo * prod_range f (nat_succ lo) hi)
  = ()

let prod_range_singleton (#t:Type) {| m: mul_monoid t |}
                         (f: nat -> t) (k: nat)
  : Lemma (prod_range f k (nat_succ k) = f k)
  = prod_range_unfold_left f k (nat_succ k);
    prod_range_empty f (nat_succ k) (nat_succ k);
    right_mul_identity (f k)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec prod_range_congruence
  (#t:Type) {| m: mul_monoid t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (requires (forall (k:nat). lo <= k /\ k < hi ==> f k = g k))
          (ensures prod_range f lo hi = prod_range g lo hi)
          (decreases (if hi > lo then nat_minus hi lo else 0))
  = if lo >= hi then reflexivity (prod_range f lo hi)
    else begin
      prod_range_congruence f g (nat_succ lo) hi;
      reflexivity (f lo);
      mul_congruence (f lo) (prod_range f (nat_succ lo) hi)
                     (g lo) (prod_range g (nat_succ lo) hi)
    end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec prod_range_unfold_right
  (#t:Type) {| m: mul_monoid t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures prod_range f lo hi = prod_range f lo (nat_pred hi) * f (nat_pred hi))
          (decreases nat_minus hi lo)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if nat_succ lo = hi then begin
      prod_range_unfold_left f lo hi;
      prod_range_empty f (nat_succ lo) hi;
      right_mul_identity (f lo);
      prod_range_empty f lo (nat_pred hi);
      left_mul_identity (f (nat_pred hi));
      symmetry (one * f (nat_pred hi)) (f (nat_pred hi));
      mul_congruence (prod_range f lo (nat_pred hi)) (f (nat_pred hi))
                     one (f (nat_pred hi))
    end else begin
      prod_range_unfold_left f lo hi;
      prod_range_unfold_right f (nat_succ lo) hi;
      reflexivity (f lo);
      mul_congruence (f lo) (prod_range f (nat_succ lo) hi)
                     (f lo) (prod_range f (nat_succ lo) (nat_pred hi) * f (nat_pred hi));
      mul_associativity (f lo) (prod_range f (nat_succ lo) (nat_pred hi)) (f (nat_pred hi));
      prod_range_unfold_left f lo (nat_pred hi);
      symmetry (prod_range f lo (nat_pred hi))
               (f lo * prod_range f (nat_succ lo) (nat_pred hi));
      reflexivity (f (nat_pred hi));
      mul_congruence (f lo * prod_range f (nat_succ lo) (nat_pred hi)) (f (nat_pred hi))
                     (prod_range f lo (nat_pred hi)) (f (nat_pred hi))
    end
#pop-options

(* ----------------------------------------------------------------- *)
(*  Sum over a list                                                  *)
(* ----------------------------------------------------------------- *)

open FStar.List.Tot.Base

let rec sum_list (#t:Type) {| m: add_comm_monoid t |} (xs: list t) : Tot t
  = match xs with
    | [] -> zero
    | x :: rest -> x + sum_list rest

let sum_list_nil (#t:Type) {| m: add_comm_monoid t |}
  : Lemma (sum_list #t #m [] == zero) = ()

let sum_list_cons (#t:Type) {| m: add_comm_monoid t |} (x: t) (rest: list t)
  : Lemma (sum_list (x :: rest) == x + sum_list rest) = ()

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec sum_list_map_congruence
  (#a:Type) (#t:Type) {| m: add_comm_monoid t |}
  (f g: a -> t) (xs: list a)
  : Lemma (requires (forall (x:a). memP x xs ==> f x = g x))
          (ensures sum_list (map f xs) = sum_list (map g xs))
          (decreases xs)
  = match xs with
    | [] -> reflexivity (sum_list #t #m [])
    | x :: rest ->
      sum_list_map_congruence f g rest;
      add_congruence (f x) (sum_list (map f rest))
                     (g x) (sum_list (map g rest))
#pop-options

(* ----------------------------------------------------------------- *)
(*  Algebraic identities involving sums                              *)
(*                                                                   *)
(*  Require a ring/semiring structure to talk about scaling sums.    *)
(* ----------------------------------------------------------------- *)

open FStar.Algebra.Classes.Ringlikes

(* sum_range_const_zero: a sum of the zero function is zero. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 30"
let rec sum_range_const_zero
  (#t:Type) {| m: add_comm_monoid t |}
  (lo hi: nat)
  : Lemma (ensures sum_range #t (fun _ -> zero) lo hi = zero)
          (decreases (if hi > lo then nat_minus hi lo else 0))
  = if lo >= hi then reflexivity (zero #t)
    else begin
      sum_range_const_zero #t #m (nat_succ lo) hi;
      sum_range_unfold_left #t (fun _ -> zero) lo hi;
      reflexivity (zero #t);
      add_congruence (zero #t) (sum_range #t (fun _ -> zero) (nat_succ lo) hi)
                     (zero #t) (zero #t);
      left_add_identity (zero #t);
      reflexivity (sum_range #t (fun _ -> zero) lo hi);
      trans_lemma [ sum_range #t (fun _ -> zero) lo hi;
                    zero + sum_range #t (fun _ -> zero) (nat_succ lo) hi;
                    zero + zero #t;
                    zero #t ]
    end
#pop-options

(* Sum of left-scaled function: c * Σ f = Σ (c * f). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec sum_range_mul_left
  (#t:Type) {| r: semiring t |}
  (c: t) (f: nat -> t) (lo hi: nat)
  : Lemma (ensures c * sum_range f lo hi = sum_range (fun k -> c * f k) lo hi)
          (decreases (if hi > lo then nat_minus hi lo else 0))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if lo >= hi then begin
      sum_range_empty f lo hi;
      sum_range_empty (fun k -> c * f k) lo hi;
      reflexivity c;
      mul_congruence c (sum_range f lo hi) c zero;
      right_absorption c;
      symmetry (sum_range (fun k -> c * f k) lo hi) zero;
      transitivity (c * sum_range f lo hi) (c * zero) zero;
      transitivity (c * sum_range f lo hi) zero (sum_range (fun k -> c * f k) lo hi)
    end else begin
      sum_range_unfold_left f lo hi;
      sum_range_unfold_left (fun k -> c * f k) lo hi;
      (* Step 1: c*sum = c*(f lo + tail) — propositional from unfold_left + reflexivity *)
      let s1 = c * sum_range f lo hi in
      let s2 = c * (f lo + sum_range f (nat_succ lo) hi) in
      reflexivity s1;  (* s1 == s2 by definitional equality of sum_range *)
      (* Step 2: distributivity *)
      left_distributivity c (f lo) (sum_range f (nat_succ lo) hi);
      (* Step 3: inductive hypothesis *)
      sum_range_mul_left c f (nat_succ lo) hi;
      reflexivity (c * f lo);
      add_congruence (c * f lo) (c * sum_range f (nat_succ lo) hi)
                     (c * f lo) (sum_range (fun k -> c * f k) (nat_succ lo) hi);
      (* Step 4: reverse unfold *)
      let s5 = sum_range (fun k -> c * f k) lo hi in
      let s4 = c * f lo + sum_range (fun k -> c * f k) (nat_succ lo) hi in
      reflexivity s5;  (* s5 == s4 by definitional equality *)
      symmetry s5 s4;
      trans_lemma [ s1; s2;
                    c * f lo + c * sum_range f (nat_succ lo) hi;
                    s4; s5 ]
    end
#pop-options

(* Sum of right-scaled function: (Σ f) * c = Σ (f * c). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec sum_range_mul_right
  (#t:Type) {| r: semiring t |}
  (f: nat -> t) (c: t) (lo hi: nat)
  : Lemma (ensures sum_range f lo hi * c = sum_range (fun k -> f k * c) lo hi)
          (decreases (if hi > lo then nat_minus hi lo else 0))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if lo >= hi then begin
      sum_range_empty f lo hi;
      sum_range_empty (fun k -> f k * c) lo hi;
      reflexivity c;
      mul_congruence (sum_range f lo hi) c zero c;
      left_absorption c;
      symmetry (sum_range (fun k -> f k * c) lo hi) zero;
      transitivity (sum_range f lo hi * c) (zero * c) zero;
      transitivity (sum_range f lo hi * c) zero (sum_range (fun k -> f k * c) lo hi)
    end else begin
      sum_range_unfold_left f lo hi;
      sum_range_unfold_left (fun k -> f k * c) lo hi;
      let s1 = sum_range f lo hi * c in
      let s2 = (f lo + sum_range f (nat_succ lo) hi) * c in
      reflexivity s1;  (* s1 == s2 by definitional equality *)
      right_distributivity (f lo) (sum_range f (nat_succ lo) hi) c;
      sum_range_mul_right f c (nat_succ lo) hi;
      reflexivity (f lo * c);
      add_congruence (f lo * c) (sum_range f (nat_succ lo) hi * c)
                     (f lo * c) (sum_range (fun k -> f k * c) (nat_succ lo) hi);
      let s5 = sum_range (fun k -> f k * c) lo hi in
      let s4 = f lo * c + sum_range (fun k -> f k * c) (nat_succ lo) hi in
      reflexivity s5;  (* s5 == s4 by definitional equality *)
      symmetry s5 s4;
      trans_lemma [ s1; s2;
                    f lo * c + sum_range f (nat_succ lo) hi * c;
                    s4; s5 ]
    end
#pop-options

(* Sum is additive in the summand: Σ (f + g) = Σ f + Σ g. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec sum_range_add
  (#t:Type) {| m: add_comm_monoid t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (ensures sum_range (fun k -> f k + g k) lo hi
                  = sum_range f lo hi + sum_range g lo hi)
          (decreases (if hi > lo then nat_minus hi lo else 0))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if lo >= hi then begin
      sum_range_empty (fun k -> f k + g k) lo hi;
      sum_range_empty f lo hi;
      sum_range_empty g lo hi;
      reflexivity (zero #t);
      add_congruence (sum_range f lo hi) (sum_range g lo hi) zero zero;
      left_add_identity (zero #t);
      symmetry (zero + zero #t) zero;
      trans_lemma [ sum_range (fun k -> f k + g k) lo hi;
                    zero #t;
                    zero + zero #t;
                    sum_range f lo hi + sum_range g lo hi ]
    end else begin
      sum_range_unfold_left (fun k -> f k + g k) lo hi;
      sum_range_unfold_left f lo hi;
      sum_range_unfold_left g lo hi;
      let fl = f lo in let gl = g lo in
      let fa = sum_range f (nat_succ lo) hi in
      let ga = sum_range g (nat_succ lo) hi in
      (* IH *)
      sum_range_add f g (nat_succ lo) hi;
      reflexivity (fl + gl);
      add_congruence (fl + gl) (sum_range (fun k -> f k + g k) (nat_succ lo) hi)
                     (fl + gl) (fa + ga);
      (* Reflexivity bridges definitional equalities to the typeclass `=`. *)
      let head = sum_range (fun k -> f k + g k) lo hi in
      let target = sum_range f lo hi + sum_range g lo hi in
      reflexivity head;       (* head == (fl + gl) + sum_range (fun k -> f k + g k) (succ lo) hi *)
      reflexivity target;     (* target == (fl + fa) + (gl + ga) by definitional unfolding *)
      (* (fl + gl) + (fa + ga) = fl + (gl + (fa + ga))   assoc *)
      add_associativity fl gl (fa + ga);
      (* gl + (fa + ga) = (gl + fa) + ga                 assoc reversed *)
      add_associativity gl fa ga;
      symmetry ((gl + fa) + ga) (gl + (fa + ga));
      (* gl + fa = fa + gl                              comm *)
      add_commutativity gl fa;
      reflexivity ga;
      add_congruence (gl + fa) ga (fa + gl) ga;
      (* (fa + gl) + ga = fa + (gl + ga)                assoc *)
      add_associativity fa gl ga;
      trans_lemma [ gl + (fa + ga);
                    (gl + fa) + ga;
                    (fa + gl) + ga;
                    fa + (gl + ga) ];
      reflexivity fl;
      add_congruence fl (gl + (fa + ga)) fl (fa + (gl + ga));
      (* fl + (fa + (gl + ga)) = (fl + fa) + (gl + ga)  assoc reversed *)
      add_associativity fl fa (gl + ga);
      symmetry ((fl + fa) + (gl + ga)) (fl + (fa + (gl + ga)));
      trans_lemma [ head;
                    (fl + gl) + (fa + ga);
                    fl + (gl + (fa + ga));
                    fl + (fa + (gl + ga));
                    (fl + fa) + (gl + ga) ];
      (* Now bridge (fl + fa) + (gl + ga) = target via reflexivity. *)
      reflexivity ((fl + fa) + (gl + ga));
      transitivity head ((fl + fa) + (gl + ga)) target
    end
#pop-options

(* Double sum swap: Σ_i Σ_j f(i,j) = Σ_j Σ_i f(i,j) over rectangular ranges.

   Strategy: induct on the outer range; use sum_range_add to push the new
   row through the inner sum. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let rec sum_swap_aux
  (#t:Type) {| m: add_comm_monoid t |}
  (f: nat -> nat -> t)
  (i_lo i_hi j_lo j_hi: nat)
  : Lemma (ensures sum_range (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi
                  = sum_range (fun j -> sum_range (fun i -> f i j) i_lo i_hi) j_lo j_hi)
          (decreases (if i_hi > i_lo then nat_minus i_hi i_lo else 0))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if i_lo >= i_hi then begin
      (* LHS: empty outer sum = zero. *)
      sum_range_empty #t (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi;
      (* RHS: inner sums are all empty, so RHS = sum of zeros = zero. *)
      let inner_fn (j: nat) : t = sum_range (fun i -> f i j) i_lo i_hi in
      let pf (j: nat) : Lemma (j_lo <= j /\ j < j_hi ==> inner_fn j = zero)
        = if j_lo <= j && j < j_hi then begin
            sum_range_empty #t (fun i -> f i j) i_lo i_hi;
            reflexivity (zero #t)
          end
      in
      Classical.forall_intro pf;
      sum_range_congruence #t inner_fn (fun _ -> zero) j_lo j_hi;
      sum_range_const_zero #t #m j_lo j_hi;
      transitivity (sum_range (fun j -> sum_range (fun i -> f i j) i_lo i_hi) j_lo j_hi)
                   (sum_range #t (fun _ -> zero) j_lo j_hi)
                   zero;
      symmetry (sum_range (fun j -> sum_range (fun i -> f i j) i_lo i_hi) j_lo j_hi) zero;
      transitivity (sum_range (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi)
                   zero
                   (sum_range (fun j -> sum_range (fun i -> f i j) i_lo i_hi) j_lo j_hi)
    end else begin
      (* Outer step. Outer = f(i_lo) + outer'.  Push f(i_lo) inside. *)
      sum_range_unfold_left #t (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi;
      (* IH on outer' *)
      sum_swap_aux f (nat_succ i_lo) i_hi j_lo j_hi;
      reflexivity (sum_range (f i_lo) j_lo j_hi);
      add_congruence (sum_range (f i_lo) j_lo j_hi)
                     (sum_range (fun i -> sum_range (f i) j_lo j_hi) (nat_succ i_lo) i_hi)
                     (sum_range (f i_lo) j_lo j_hi)
                     (sum_range (fun j -> sum_range (fun i -> f i j) (nat_succ i_lo) i_hi) j_lo j_hi);
      (* sum_range (f i_lo) j_lo j_hi  +  Σ_j Σ_{i>=i_lo+1} f i j
         = Σ_j ( f i_lo j  +  Σ_{i>=i_lo+1} f i j )   by sum_range_add reversed
         = Σ_j Σ_{i>=i_lo}  f i j                     by unfolding the inner sum
      *)
      sum_range_add #t (f i_lo)
                       (fun j -> sum_range (fun i -> f i j) (nat_succ i_lo) i_hi)
                       j_lo j_hi;
      symmetry (sum_range (fun j -> f i_lo j + sum_range (fun i -> f i j) (nat_succ i_lo) i_hi) j_lo j_hi)
               (sum_range (f i_lo) j_lo j_hi
                + sum_range (fun j -> sum_range (fun i -> f i j) (nat_succ i_lo) i_hi) j_lo j_hi);
      (* Pointwise: f i_lo j + Σ_{i>=i_lo+1} f i j  =  Σ_{i>=i_lo} f i j  (unfold-left). *)
      let lhs_inner (j: nat) : t
        = f i_lo j + sum_range (fun i -> f i j) (nat_succ i_lo) i_hi in
      let rhs_inner (j: nat) : t = sum_range (fun i -> f i j) i_lo i_hi in
      let pf (j: nat) : Lemma (j_lo <= j /\ j < j_hi ==> lhs_inner j = rhs_inner j)
        = if j_lo <= j && j < j_hi then begin
            sum_range_unfold_left #t (fun i -> f i j) i_lo i_hi;
            symmetry (rhs_inner j) (lhs_inner j)
          end
      in
      Classical.forall_intro pf;
      sum_range_congruence #t lhs_inner rhs_inner j_lo j_hi;
      trans_lemma [ sum_range (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi;
                    sum_range (f i_lo) j_lo j_hi
                    + sum_range (fun i -> sum_range (f i) j_lo j_hi) (nat_succ i_lo) i_hi;
                    sum_range (f i_lo) j_lo j_hi
                    + sum_range (fun j -> sum_range (fun i -> f i j) (nat_succ i_lo) i_hi) j_lo j_hi;
                    sum_range lhs_inner j_lo j_hi;
                    sum_range rhs_inner j_lo j_hi ]
    end
#pop-options

let sum_swap
  (#t:Type) {| m: add_comm_monoid t |}
  (f: nat -> nat -> t)
  (i_lo i_hi j_lo j_hi: nat)
  : Lemma (sum_range (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi
         = sum_range (fun j -> sum_range (fun i -> f i j) i_lo i_hi) j_lo j_hi)
  = sum_swap_aux f i_lo i_hi j_lo j_hi
