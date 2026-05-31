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

(* ----------------------------------------------------------------- *)
(*  Plain nat arithmetic helpers.                                    *)
(* ----------------------------------------------------------------- *)

unfold let nat_succ (n: nat) : nat = Prims.op_Addition n 1
unfold let nat_pred (n: nat{n > 0}) : nat = Prims.op_Subtraction n 1
unfold let nat_minus (a: nat) (b: nat) : int = Prims.op_Subtraction a b

(* ----------------------------------------------------------------- *)
(*  Sum over an integer range  [lo, hi)                              *)
(* ----------------------------------------------------------------- *)

val sum_range (#t:Type) {| m: add_comm_group t |}
                  (f: nat -> t) (lo hi: nat)
  : Tot t (decreases (hi - lo))

val sum_range_empty (#t:Type) {| m: add_comm_group t |}
                    (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo >= hi)
          (ensures sum_range f lo hi == zero)

val sum_range_unfold_left (#t:Type) {| m: add_comm_group t |}
                          (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures sum_range f lo hi == f lo + sum_range f (nat_succ lo) hi)

val sum_range_singleton (#t:Type) {| m: add_comm_group t |}
                        (f: nat -> t) (k: nat)
  : Lemma (sum_range f k (nat_succ k) = f k)

val sum_range_unfold_right
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures sum_range f lo hi = sum_range f lo (nat_pred hi) + f (nat_pred hi))
          (decreases nat_minus hi lo)

val sum_range_split
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (lo mid hi: nat)
  : Lemma (requires lo <= mid /\ mid <= hi)
          (ensures sum_range f lo hi = sum_range f lo mid + sum_range f mid hi)
          (decreases (mid - lo))

val sum_range_shift
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (offset lo hi: nat)
  : Lemma (ensures sum_range (fun (j:nat) -> f (Prims.op_Addition j offset)) lo hi
                 = sum_range f (Prims.op_Addition lo offset) (Prims.op_Addition hi offset))
          (decreases (hi - lo))

val sum_range_reverse
  (#t:Type) {| m: add_comm_group t |}
  (f: int -> t) (n: nat)
  : Lemma (ensures sum_range (fun (j:nat) -> f (n - 1 - j)) 0 n
                 = sum_range (fun (j:nat) -> f j) 0 n)
          (decreases n)

val sum_range_all_zero
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (lo hi: nat)
  (h: (k: nat{lo <= k /\ k < hi}) -> Lemma (f k = (zero <: t)))
  : Lemma (ensures sum_range f lo hi = (zero <: t))
          (decreases (hi - lo))

(* ----------------------------------------------------------------- *)
(*  Product over an integer range  [lo, hi)                          *)
(* ----------------------------------------------------------------- *)

val prod_range (#t:Type) {| m: ring t |}
                   (f: nat -> t) (lo hi: nat)
  : Tot t (decreases (hi - lo))

val prod_range_empty (#t:Type) {| m: ring t |}
                     (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo >= hi)
          (ensures prod_range f lo hi == one)

val prod_range_unfold_left (#t:Type) {| m: ring t |}
                           (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures prod_range f lo hi == f lo * prod_range f (nat_succ lo) hi)

val prod_range_singleton (#t:Type) {| m: ring t |}
                         (f: nat -> t) (k: nat)
  : Lemma (prod_range f k (nat_succ k) = f k)

val prod_range_unfold_right
  (#t:Type) {| m: ring t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures prod_range f lo hi = prod_range f lo (nat_pred hi) * f (nat_pred hi))
          (decreases nat_minus hi lo)

val prod_range_split
  (#t:Type) {| m: ring t |}
  (f: nat -> t) (lo mid hi: nat)
  : Lemma (requires lo <= mid /\ mid <= hi)
          (ensures prod_range f lo hi =
                   prod_range f lo mid * prod_range f mid hi)
          (decreases (mid - lo))

val prod_range_two_step
  (#t:Type) {| m: ring t |}
  (f: nat -> t) (i: nat)
  : Lemma (prod_range f i (nat_succ (nat_succ i)) = f i * f (nat_succ i))

(* ----------------------------------------------------------------- *)
(*  Sum over a list                                                  *)
(* ----------------------------------------------------------------- *)

val sum_list (#t:Type) {| m: add_comm_group t |} (xs: list t) : Tot t

val sum_list_nil (#t:Type) {| m: add_comm_group t |}
  : Lemma (sum_list #t #m [] == zero)

val sum_list_cons (#t:Type) {| m: add_comm_group t |} (x: t) (rest: list t)
  : Lemma (sum_list (x :: rest) == x + sum_list rest)

(* ----------------------------------------------------------------- *)
(*  Sum over `fin n`  (defined via inline lambda + sum_range)        *)
(* ----------------------------------------------------------------- *)

unfold let fin_sum (#t:Type) {| m: add_comm_group t |}
            (#n: nat) (f: fin n -> t) : t
  = sum_range (fun (k: nat) -> if k < n then f (k <: fin n) else zero) 0 n

(* Product over `fin n`, mirroring fin_sum. The internal nat-coercion
   lives here once; callers never see it. *)
unfold let fin_prod (#t:Type) {| r: ring t |}
            (#n: nat) (f: fin n -> t) : t
  = prod_range (fun (k: nat) -> if k < n then f (k <: fin n) else one) 0 n

(* ================================================================= *)
(*  H3 hygiene (early): callback-form congruences used by the        *)
(*  algebraic-identity lemmas below.                                 *)
(* ================================================================= *)

val sum_list_map_congruence
  (#a:Type) (#t:Type) {| m: add_comm_group t |}
  (f g: a -> t) (xs: list a)
  (h: (x:a) -> Lemma (requires memP x xs) (ensures f x = g x))
  : Lemma (ensures sum_list (map f xs) = sum_list (map g xs))
          (decreases xs)

val sum_range_congruence
  (#t:Type) {| m: add_comm_group t |}
  (f g: nat -> t) (lo hi: nat)
  (h: (k: nat{lo <= k /\ k < hi}) -> Lemma (f k = g k))
  : Lemma (ensures sum_range f lo hi = sum_range g lo hi)
          (decreases (hi - lo))

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
          (decreases (to - from))

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
          (decreases (hi - lo))

val prod_range_swap_adjacent
  (#t:Type) {| m: commutative_ring t |}
  (f g: nat -> t) (lo hi: nat) (i: nat)
  (h: (k: nat{lo <= k /\ k < hi /\ k <> i /\ k <> nat_succ i}) -> Lemma (g k = f k))
  : Lemma (requires lo <= i /\ nat_succ i < hi /\
                    g i = f (nat_succ i) /\ g (nat_succ i) = f i)
          (ensures prod_range f lo hi = prod_range g lo hi)

val prod_range_perm_invariance_fn
  (#t:Type) {| m: commutative_ring t |}
  (#n: nat) (f body_p body_id: nat -> t) (p: permutation n)
  (h_p: (k: nat{0 <= k /\ k < n}) -> Lemma (body_p k = f (p.fwd (k <: fin n))))
  (h_id: (k: nat{0 <= k /\ k < n}) -> Lemma (body_id k = f k))
  : Lemma (ensures prod_range body_p 0 n = prod_range body_id 0 n)

val fin_sum_zero_ext
  (#t:Type) {| m: add_comm_group t |} (#n: nat) (f: fin n -> t)
  (h: (k: fin n) -> Lemma (f k = zero #t))
  : Lemma (ensures fin_sum f = zero #t)

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
          (ensures sum_range (pointwise_mul (kronecker_delta i0) g) lo hi = zero #t)

(* Negation distributes over sum_range. *)
val sum_range_neg
  (#t:Type) {| g: add_comm_group t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (ensures sum_range (fun (k:nat) -> neg (f k)) lo hi
                 = neg (sum_range f lo hi))
          (decreases (hi - lo))

(* Bridge fin_sum to sum_range when g agrees with f on [0,n). *)
val fin_sum_eq_sum_range
  (#t:Type) {| acg: add_comm_group t |} (#n: pos)
  (f: fin n -> t) (g: nat -> t)
  : Lemma (requires (forall (k: nat{k < n}). g k = f (k <: fin n)))
          (ensures fin_sum f = sum_range g 0 n)

(* Reversal bridge for named functions:
   if f j = g (n-1-j) for all j < n, then sum_range f 0 n = sum_range g 0 n. *)
val sum_range_reverse_named
  (#t:Type) {| acg: add_comm_group t |}
  (f g: nat -> t) (n: nat)
  (h: (j: nat{j < n}) -> Lemma (f j = g (Prims.op_Subtraction (Prims.op_Subtraction n 1) j)))
  : Lemma (ensures sum_range f 0 n = sum_range g 0 n)
          (decreases n)