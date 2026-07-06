module Core.FinSum

(*
  Finite sums and products over integer ranges and lists — public interface.

  Provides:
    sum_range  : (nat -> t) -> lo:nat -> hi:nat -> t   (over add_comm_group)
    prod_range : (nat -> t) -> lo:nat -> hi:nat -> t   (over ring)
    sum_list   : list t -> t                            (over add_comm_group)
    fin_sum    : (fin n -> t) -> t                      (over add_comm_group)

  Algebraic identities are stated in COMBINATOR form (Core.Algebra.Combinators)
  rather than with inline lambdas, so their statements survive F* unification.

  Designed for use in determinant and resultant constructions.

  Author: A. Rozanov (CuteCAS).
*)

module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Permutation
open FStar.List.Tot.Base

(* Plain nat arithmetic uses the operators directly: `n ++ 1` (= Prims
   integer addition, from Core.Algebra.Notation) and `n - 1` (Prims integer
   subtraction; binary `-` is never overloaded). The former `nat_succ` /
   `nat_pred` / `nat_minus` helpers have been retired in favour of `++` / `-`. *)

(* ----------------------------------------------------------------- *)
(*  Sum over an integer range  [lo, hi)                              *)
(* ----------------------------------------------------------------- *)

val sum_range (#t:Type) {| m: add_comm_group t |}
                  (f: nat -> t) (lo hi: nat)
  : Tot t

val sum_range_empty (#t:Type) {| m: add_comm_group t |}
                    (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo >= hi)
          (ensures sum_range f lo hi == zero)

val sum_range_unfold_left (#t:Type) {| m: add_comm_group t |}
                          (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures sum_range f lo hi == f lo + sum_range f (lo ++ 1) hi)

val sum_range_singleton (#t:Type) {| m: add_comm_group t |}
                        (f: nat -> t) (k: nat)
  : Lemma (sum_range f k (k ++ 1) = f k)

val sum_range_unfold_right
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures sum_range f lo hi = sum_range f lo (hi - 1) + f (hi - 1))

val sum_range_split
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (lo mid hi: nat)
  : Lemma (requires lo <= mid /\ mid <= hi)
          (ensures sum_range f lo hi = sum_range f lo mid + sum_range f mid hi)

val sum_range_shift
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (offset lo hi: nat)
  : Lemma (ensures sum_range (fun (j:nat) -> f (j ++ offset)) lo hi
                 = sum_range f (lo ++ offset) (hi ++ offset))

val sum_range_reverse
  (#t:Type) {| m: add_comm_group t |}
  (f: int -> t) (n: nat)
  : Lemma (ensures sum_range (fun (j:nat) -> f (n - 1 - j)) 0 n
                 = sum_range f 0 n)

val sum_range_all_zero
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (lo hi: nat)
  (h: (k: nat{lo <= k /\ k < hi}) -> Lemma (f k = zero))
  : Lemma (ensures sum_range f lo hi = zero)

(* ----------------------------------------------------------------- *)
(*  Product over an integer range  [lo, hi)                          *)
(* ----------------------------------------------------------------- *)

val prod_range (#t:Type) {| m: ring t |}
                   (f: nat -> t) (lo hi: nat)
  : Tot t

val prod_range_empty (#t:Type) {| m: ring t |}
                     (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo >= hi)
          (ensures prod_range f lo hi == one)

val prod_range_unfold_left (#t:Type) {| m: ring t |}
                           (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures prod_range f lo hi == f lo * prod_range f (lo ++ 1) hi)

val prod_range_singleton (#t:Type) {| m: ring t |}
                         (f: nat -> t) (k: nat)
  : Lemma (prod_range f k (k ++ 1) = f k)

val prod_range_unfold_right
  (#t:Type) {| m: ring t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures prod_range f lo hi = prod_range f lo (hi - 1) * f (hi - 1))

val prod_range_split
  (#t:Type) {| m: ring t |}
  (f: nat -> t) (lo mid hi: nat)
  : Lemma (requires lo <= mid /\ mid <= hi)
          (ensures prod_range f lo hi =
                   prod_range f lo mid * prod_range f mid hi)

val prod_range_two_step
  (#t:Type) {| m: ring t |}
  (f: nat -> t) (i: nat)
  : Lemma (prod_range f i ((i ++ 1) ++ 1) = f i * f (i ++ 1))

(* ----------------------------------------------------------------- *)
(*  Sum over a list                                                  *)
(* ----------------------------------------------------------------- *)

val sum_list (#t:Type) {| m: add_comm_group t |} (xs: list t) : Tot t

val sum_list_nil (#t:Type) {| m: add_comm_group t |}
  : Lemma (sum_list [] == zero #t)

val sum_list_cons (#t:Type) {| m: add_comm_group t |} (x: t) (rest: list t)
  : Lemma (sum_list (x :: rest) == x + sum_list rest)

(* ----------------------------------------------------------------- *)
(*  Sum over `fin n`  (defined via inline lambda + sum_range)        *)
(* ----------------------------------------------------------------- *)

unfold let fin_sum (#t:Type) {| m: add_comm_group t |}
            (#n: nat) (f: fin n -> t) : t
  = sum_range (fun (k: nat) -> if k < n then f k else zero) 0 n

(* Product over `fin n`, mirroring fin_sum. The internal nat-coercion
   lives here once; callers never see it. *)
unfold let fin_prod (#t:Type) {| r: ring t |}
            (#n: nat) (f: fin n -> t) : t
  = prod_range (fun (k: nat) -> if k < n then f k else one) 0 n

(* ================================================================= *)
(*  H3 hygiene (early): callback-form congruences used by the        *)
(*  algebraic-identity lemmas below.                                 *)
(* ================================================================= *)

val sum_list_map_congruence
  (#a:Type) (#t:Type) {| m: add_comm_group t |}
  (f g: a -> t) (xs: list a)
  (h: (x:a) -> Lemma (requires memP x xs) (ensures f x = g x))
  : Lemma (ensures sum_list (map f xs) = sum_list (map g xs))

val sum_range_congruence
  (#t:Type) {| m: add_comm_group t |}
  (f g: nat -> t) (lo hi: nat)
  (h: (k: nat{lo <= k /\ k < hi}) -> Lemma (f k = g k))
  : Lemma (ensures sum_range f lo hi = sum_range g lo hi)

val fin_sum_congruence
  (#t:Type) {| m: add_comm_group t |}
  (#n: nat) (f g: fin n -> t)
  (h: (k: fin n) -> Lemma (f k = g k))
  : Lemma (ensures fin_sum f = fin_sum g)

val fin_prod_congruence
  (#t:Type) {| r: ring t |}
  (#n: nat) (f g: fin n -> t)
  (h: (k: fin n) -> Lemma (f k = g k))
  : Lemma (ensures fin_prod f = fin_prod g)

(* Propositional-equality (==) variants of congruence.
   These use pointwise `==` instead of equatable `=`, bridging
   definitional equality to fin_sum/sum_range equality. *)

val sum_range_eq_pointwise
  (#t: Type) {| acg: add_comm_group t |}
  (f g: nat -> t) (from: nat) (to: nat{from < to})
  : Lemma (requires (forall (k: nat{k >= from /\ k < to}). f k == g k))
          (ensures sum_range f from to == sum_range g from to)

val fin_sum_eq_pointwise
  (#t: Type) {| acg: add_comm_group t |}
  (#n: pos) (f g: fin n -> t)
  : Lemma (requires (forall (k: fin n). f k == g k))
          (ensures fin_sum f == fin_sum g)

(* ================================================================= *)
(*  Path A refactor: pointwise-congruence bridges + combinator-shape *)
(*  algebraic identities. All declarations below this banner use the *)
(*  Core.Algebra.Combinators vocabulary (const, pointwise_*,         *)
(*  swap_args, kronecker_delta, fin_kronecker_delta).                *)
(* ================================================================= *)

(* ---------------- sum_list / map identities ---------------------- *)

val sum_list_map_neg
  (#a:Type) (#t:Type) {| g: add_comm_group t |}
  (f: a -> t) (xs: list a)
  : Lemma (sum_list (map (pointwise_neg f) xs) = neg (sum_list (map f xs)))

val sum_list_map_add
  (#a:Type) (#t:Type) {| m: add_comm_group t |}
  (f g: a -> t) (xs: list a)
  : Lemma (sum_list (map (pointwise_add f g) xs)
         = sum_list (map f xs) + sum_list (map g xs))

val sum_list_map_mul_left
  (#a:Type) (#t:Type) {| r: ring t |}
  (c: t) (f: a -> t) (xs: list a)
  : Lemma (c * sum_list (map f xs)
         = sum_list (map (pointwise_mul (const c) f) xs))

val sum_list_map_mul_right
  (#a:Type) (#t:Type) {| r: ring t |}
  (f: a -> t) (c: t) (xs: list a)
  : Lemma (sum_list (map f xs) * c
         = sum_list (map (pointwise_mul f (const c)) xs))

(* ---------------- sum_range identities --------------------------- *)

val sum_range_const_zero
  (#t:Type) {| m: add_comm_group t |}
  (lo hi: nat)
  : Lemma (sum_range #t (const zero) lo hi = zero)

val sum_range_mul_left
  (#t:Type) {| r: ring t |}
  (c: t) (f: nat -> t) (lo hi: nat)
  : Lemma (c * sum_range f lo hi
         = sum_range (pointwise_mul (const c) f) lo hi)

val sum_range_mul_right
  (#t:Type) {| r: ring t |}
  (f: nat -> t) (c: t) (lo hi: nat)
  : Lemma (sum_range f lo hi * c
         = sum_range (pointwise_mul f (const c)) lo hi)

val sum_range_add
  (#t:Type) {| m: add_comm_group t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (sum_range (pointwise_add f g) lo hi
         = sum_range f lo hi + sum_range g lo hi)

(* Partial application of sum_range to a curried first argument. *)
unfold let sum_range_on
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> nat -> t) (lo hi: nat) (i: nat) : t
  = sum_range (f i) lo hi

val sum_swap
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> nat -> t)
  (i_lo i_hi j_lo j_hi: nat)
  : Lemma (sum_range (sum_range_on f j_lo j_hi) i_lo i_hi
         = sum_range (sum_range_on (swap_args f) i_lo i_hi) j_lo j_hi)

(* ---------------- fin_sum identities ----------------------------- *)

val fin_sum_mul_left
  (#t:Type) {| r: ring t |}
  (#n: nat) (c: t) (f: fin n -> t)
  : Lemma (c * fin_sum f = fin_sum (pointwise_mul (const c) f))

val fin_sum_mul_right
  (#t:Type) {| r: ring t |}
  (#n: nat) (f: fin n -> t) (c: t)
  : Lemma (fin_sum f * c = fin_sum (pointwise_mul f (const c)))

(* Partial application of fin_sum to a curried first argument. *)
unfold let fin_sum_curry
  (#t:Type) {| m: add_comm_group t |} (#n: nat)
  (f: fin n -> fin n -> t) (i: fin n) : t
  = fin_sum (f i)

val fin_sum_swap
  (#t:Type) {| m: add_comm_group t |}
  (#n: nat) (f: fin n -> fin n -> t)
  : Lemma (fin_sum (fin_sum_curry f)
         = fin_sum (fin_sum_curry (swap_args f)))

val fin_sum_const_zero
  (#t:Type) {| m: add_comm_group t |} (#n: nat)
  : Lemma (fin_sum #t #m #n (const zero) = zero)

val fin_sum_add
  (#t:Type) {| m: add_comm_group t |} (#n: nat) (f g: fin n -> t)
  : Lemma (fin_sum (pointwise_add f g) = fin_sum f + fin_sum g)

val fin_sum_kronecker
  (#t:Type) {| r: ring t |}
  (#n: nat) (i0: fin n) (g: fin n -> t)
  : Lemma (fin_sum (pointwise_mul (fin_kronecker_delta i0) g) = g i0)


(* ================================================================= *)
(*  H3 hygiene (late): callback-form public API for lemmas whose     *)
(*  fst definitions live after the algebraic-identity section.      *)
(* ================================================================= *)

val prod_range_congruence
  (#t:Type) {| m: ring t |}
  (f g: nat -> t) (lo hi: nat)
  (h: (k: nat{lo <= k /\ k < hi}) -> Lemma (f k = g k))
  : Lemma (ensures prod_range f lo hi = prod_range g lo hi)

val prod_range_swap_adjacent
  (#t:Type) {| m: commutative_ring t |}
  (f g: nat -> t) (lo hi: nat) (i: nat)
  (h: (k: nat{lo <= k /\ k < hi /\ k <> i /\ k <> i ++ 1}) -> Lemma (g k = f k))
  : Lemma (requires lo <= i /\ i ++ 1 < hi /\
                    g i = f (i ++ 1) /\ g (i ++ 1) = f i)
          (ensures prod_range f lo hi = prod_range g lo hi)

val prod_range_perm_invariance_fn
  (#t:Type) {| m: commutative_ring t |}
  (#n: nat) (f body_p body_id: nat -> t) (p: permutation n)
  (h_p: (k: nat{0 <= k /\ k < n}) -> Lemma (body_p k = f (p.fwd k)))
  (h_id: (k: nat{0 <= k /\ k < n}) -> Lemma (body_id k = f k))
  : Lemma (ensures prod_range body_p 0 n = prod_range body_id 0 n)

val fin_sum_zero_ext
  (#t:Type) {| m: add_comm_group t |} (#n: nat) (f: fin n -> t)
  (h: (k: fin n) -> Lemma (f k = zero))
  : Lemma (ensures fin_sum f = zero)

val fin_sum_add_ext
  (#t:Type) {| m: add_comm_group t |} (#n: nat) (f g h: fin n -> t)
  (pf: (k: fin n) -> Lemma (h k = f k + g k))
  : Lemma (ensures fin_sum h = fin_sum f + fin_sum g)

val sum_range_kronecker_in_range
  (#t:Type) {| r: ring t |}
  (i0: nat) (g: nat -> t) (lo hi: nat)
  : Lemma (requires lo <= i0 /\ i0 < hi)
          (ensures sum_range (pointwise_mul (kronecker_delta i0) g) lo hi = g i0)

val sum_range_kronecker_out_of_range
  (#t:Type) {| r: ring t |}
  (i0: nat) (g: nat -> t) (lo hi: nat)
  : Lemma (requires i0 < lo \/ i0 >= hi)
          (ensures sum_range (pointwise_mul (kronecker_delta i0) g) lo hi = zero)

(* Negation distributes over sum_range. *)
val sum_range_neg
  (#t:Type) {| g: add_comm_group t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (ensures sum_range (pointwise_neg f) lo hi
                 = neg (sum_range f lo hi))

(* Bridge fin_sum to sum_range when g agrees with f on [0,n). *)
val fin_sum_eq_sum_range
  (#t:Type) {| acg: add_comm_group t |} (#n: pos)
  (f: fin n -> t) (g: nat -> t)
  : Lemma (requires (forall k. g k = f k))
          (ensures fin_sum f = sum_range g 0 n)

(* Reversal bridge for named functions:
   if f j = g (n-1-j) for all j < n, then sum_range f 0 n = sum_range g 0 n. *)
val sum_range_reverse_named
  (#t:Type) {| acg: add_comm_group t |}
  (f g: nat -> t) (n: nat)
  (h: (j: nat{j < n}) -> Lemma (f j = g (n - 1 - j)))
  : Lemma (ensures sum_range f 0 n = sum_range g 0 n)

(* ===== merged from Core.FinSum.Convolution - Cauchy product ===== *)
(* conv_term/conv_sum are transparent (referenced in consumer lemma statements);
   the padding/collapse helpers stay private in the .fst. *)
val conv_term (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (k i: nat) : t

val conv_sum (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (k: nat) : t

val conv_term_reveal (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (k i: nat)
  : Lemma (conv_term f g k i == (if i <= k then f i * g (k - i) else zero))

val conv_sum_reveal (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (k: nat)
  : Lemma (conv_sum f g k == sum_range (conv_term f g k) 0 (k ++ 1))

val sum_range_convolution (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (m n: nat)
  (hf: (i:nat{i >= m}) -> Lemma (f i = zero))
  (hg: (j:nat{j >= n}) -> Lemma (g j = zero))
  : Lemma (sum_range f 0 m * sum_range g 0 n
         = sum_range (conv_sum f g) 0 (m ++ n))
