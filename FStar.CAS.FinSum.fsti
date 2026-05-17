module FStar.CAS.FinSum

(*
  Finite sums and products over integer ranges and lists — public interface.

  Provides:
    sum_range  : (nat -> t) -> lo:nat -> hi:nat -> t   (over add_comm_monoid)
    prod_range : (nat -> t) -> lo:nat -> hi:nat -> t   (over mul_monoid)
    sum_list   : list t -> t                            (over add_comm_monoid)
    fin_sum    : (fin n -> t) -> t                      (over add_comm_monoid)

  with basic congruence, step, and split lemmas.

  Designed for use in determinant and resultant constructions.

  Author: A. Rozanov (CuteCAS).
*)

module TC = FStar.Tactics.Typeclasses

open FStar.CAS.Equatable
open FStar.CAS.Grouplikes

(* ----------------------------------------------------------------- *)
(*  Plain nat arithmetic helpers.                                    *)
(*                                                                   *)
(*  `open Grouplikes` above shadows the Prims `+`/`-` with typeclass-*)
(*  resolved versions; these helpers expose the primitive operations *)
(*  under fresh names.                                               *)
(* ----------------------------------------------------------------- *)

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

val sum_range_empty (#t:Type) {| m: add_comm_monoid t |}
                    (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo >= hi)
          (ensures sum_range f lo hi == zero)

val sum_range_unfold_left (#t:Type) {| m: add_comm_monoid t |}
                          (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures sum_range f lo hi == f lo + sum_range f (nat_succ lo) hi)

val sum_range_singleton (#t:Type) {| m: add_comm_monoid t |}
                        (f: nat -> t) (k: nat)
  : Lemma (sum_range f k (nat_succ k) = f k)

val sum_range_congruence
  (#t:Type) {| m: add_comm_monoid t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (requires (forall (k:nat). lo <= k /\ k < hi ==> f k = g k))
          (ensures sum_range f lo hi = sum_range g lo hi)
          (decreases (if hi > lo then nat_minus hi lo else 0))

val sum_range_unfold_right
  (#t:Type) {| m: add_comm_monoid t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures sum_range f lo hi = sum_range f lo (nat_pred hi) + f (nat_pred hi))
          (decreases nat_minus hi lo)

(* ----------------------------------------------------------------- *)
(*  Product over an integer range  [lo, hi)                          *)
(* ----------------------------------------------------------------- *)

let rec prod_range (#t:Type) {| m: mul_monoid t |}
                   (f: nat -> t) (lo hi: nat)
  : Tot t (decreases (if hi > lo then nat_minus hi lo else 0))
  = if lo >= hi then one
    else f lo * prod_range f (nat_succ lo) hi

val prod_range_empty (#t:Type) {| m: mul_monoid t |}
                     (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo >= hi)
          (ensures prod_range f lo hi == one)

val prod_range_unfold_left (#t:Type) {| m: mul_monoid t |}
                           (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures prod_range f lo hi == f lo * prod_range f (nat_succ lo) hi)

val prod_range_singleton (#t:Type) {| m: mul_monoid t |}
                         (f: nat -> t) (k: nat)
  : Lemma (prod_range f k (nat_succ k) = f k)

val prod_range_congruence
  (#t:Type) {| m: mul_monoid t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (requires (forall (k:nat). lo <= k /\ k < hi ==> f k = g k))
          (ensures prod_range f lo hi = prod_range g lo hi)
          (decreases (if hi > lo then nat_minus hi lo else 0))

val prod_range_unfold_right
  (#t:Type) {| m: mul_monoid t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures prod_range f lo hi = prod_range f lo (nat_pred hi) * f (nat_pred hi))
          (decreases nat_minus hi lo)

val prod_range_split
  (#t:Type) {| m: mul_monoid t |}
  (f: nat -> t) (lo mid hi: nat)
  : Lemma (requires lo <= mid /\ mid <= hi)
          (ensures prod_range f lo hi =
                   prod_range f lo mid * prod_range f mid hi)
          (decreases (if mid > lo then nat_minus mid lo else 0))

(* prod_range f i (i+2) = f i * f (i+1) — explicit two-element product. *)
val prod_range_two_step
  (#t:Type) {| m: mul_monoid t |}
  (f: nat -> t) (i: nat)
  : Lemma (prod_range f i (nat_succ (nat_succ i)) = f i * f (nat_succ i))

(* Swapping two adjacent indices in a commutative product is invariant. *)
val prod_range_swap_adjacent
  (#t:Type) {| m: mul_comm_monoid t |}
  (f g: nat -> t) (lo hi: nat) (i: nat)
  : Lemma (requires lo <= i /\ nat_succ i < hi /\
                    g i = f (nat_succ i) /\ g (nat_succ i) = f i /\
                    (forall (k: nat). lo <= k /\ k < hi /\ k <> i /\ k <> nat_succ i ==> g k = f k))
          (ensures prod_range f lo hi = prod_range g lo hi)

(* Reindexing a finite product by a permutation of [0, n).

   For any permutation p of `fin n` and any f : nat → t (with t a
   commutative monoid under multiplication):

       Π_{0 ≤ k < n} F(p.fwd k) = Π_{0 ≤ k < n} F(k)

   where F(k) abbreviates [if k < n then f k else one].  The guards make
   the body well-typed for k ∉ [0, n).                                       *)
open FStar.CAS.Permutation

val prod_range_perm_invariance
  (#t:Type) {| m: mul_comm_monoid t |}
  (#n: nat) (f: nat -> t) (p: permutation n)
  : Lemma (ensures
            prod_range (fun (k: nat) ->
              if k < n then f (p.fwd (k <: fin n)) else one) 0 n
          = prod_range (fun (k: nat) ->
              if k < n then f k else one) 0 n)
          (decreases inversion_count p)

val prod_range_perm_invariance_fn
  (#t:Type) {| m: mul_comm_monoid t |}
  (#n: nat) (f body_p body_id: nat -> t) (p: permutation n)
  : Lemma (requires
            (forall (k: nat). 0 <= k /\ k < n ==> body_p k = f (p.fwd (k <: fin n))) /\
            (forall (k: nat). 0 <= k /\ k < n ==> body_id k = f k))
          (ensures prod_range body_p 0 n = prod_range body_id 0 n)

(* ----------------------------------------------------------------- *)
(*  Sum over a list                                                  *)
(* ----------------------------------------------------------------- *)

open FStar.List.Tot.Base

let rec sum_list (#t:Type) {| m: add_comm_monoid t |} (xs: list t) : Tot t
  = match xs with
    | [] -> zero
    | x :: rest -> x + sum_list rest

val sum_list_nil (#t:Type) {| m: add_comm_monoid t |}
  : Lemma (sum_list #t #m [] == zero)

val sum_list_cons (#t:Type) {| m: add_comm_monoid t |} (x: t) (rest: list t)
  : Lemma (sum_list (x :: rest) == x + sum_list rest)

val sum_list_map_congruence
  (#a:Type) (#t:Type) {| m: add_comm_monoid t |}
  (f g: a -> t) (xs: list a)
  : Lemma (requires (forall (x:a). memP x xs ==> f x = g x))
          (ensures sum_list (map f xs) = sum_list (map g xs))
          (decreases xs)

val sum_list_map_neg
  (#a:Type) (#t:Type) {| g: add_comm_group t |}
  (f: a -> t) (xs: list a)
  : Lemma (ensures sum_list (map (fun x -> -(f x)) xs) = -(sum_list (map f xs)))
          (decreases xs)

val sum_list_map_add
  (#a:Type) (#t:Type) {| m: add_comm_monoid t |}
  (f g: a -> t) (xs: list a)
  : Lemma (ensures sum_list (map (fun x -> f x + g x) xs)
                 = sum_list (map f xs) + sum_list (map g xs))
          (decreases xs)

(* ----------------------------------------------------------------- *)
(*  Algebraic identities involving sums                              *)
(*                                                                   *)
(*  Require a ring/semiring structure to talk about scaling sums.    *)
(* ----------------------------------------------------------------- *)

open FStar.CAS.Ringlikes

val sum_list_map_mul_left
  (#a:Type) (#t:Type) {| r: semiring t |}
  (c: t) (f: a -> t) (xs: list a)
  : Lemma (ensures c * sum_list (map f xs) = sum_list (map (fun x -> c * f x) xs))
          (decreases xs)

val sum_range_const_zero
  (#t:Type) {| m: add_comm_monoid t |}
  (lo hi: nat)
  : Lemma (ensures sum_range #t (fun _ -> zero) lo hi = zero)
          (decreases (if hi > lo then nat_minus hi lo else 0))

val sum_range_mul_left
  (#t:Type) {| r: semiring t |}
  (c: t) (f: nat -> t) (lo hi: nat)
  : Lemma (ensures c * sum_range f lo hi = sum_range (fun k -> c * f k) lo hi)
          (decreases (if hi > lo then nat_minus hi lo else 0))

val sum_range_mul_right
  (#t:Type) {| r: semiring t |}
  (f: nat -> t) (c: t) (lo hi: nat)
  : Lemma (ensures sum_range f lo hi * c = sum_range (fun k -> f k * c) lo hi)
          (decreases (if hi > lo then nat_minus hi lo else 0))

val sum_range_add
  (#t:Type) {| m: add_comm_monoid t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (ensures sum_range (fun k -> f k + g k) lo hi
                  = sum_range f lo hi + sum_range g lo hi)
          (decreases (if hi > lo then nat_minus hi lo else 0))

val sum_swap
  (#t:Type) {| m: add_comm_monoid t |}
  (f: nat -> nat -> t)
  (i_lo i_hi j_lo j_hi: nat)
  : Lemma (sum_range (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi
         = sum_range (fun j -> sum_range (fun i -> f i j) i_lo i_hi) j_lo j_hi)

(* ----------------------------------------------------------------- *)
(*  Sum over `fin n`                                                 *)
(*                                                                   *)
(*  Convenience layer for functions already typed on the refined     *)
(*  index type.  Internally defined via `sum_range` with a guard so  *)
(*  the bridging lemmas reduce to `sum_range_congruence`.            *)
(* ----------------------------------------------------------------- *)

open FStar.CAS.Permutation  // for `fin n`

unfold let fin_sum (#t:Type) {| m: add_comm_monoid t |}
            (#n: nat) (f: fin n -> t) : t
  = sum_range (fun (k: nat) -> if k < n then f (k <: fin n) else zero) 0 n

val fin_sum_congruence
  (#t:Type) {| m: add_comm_monoid t |}
  (#n: nat) (f g: fin n -> t)
  : Lemma (requires (forall (k: fin n). f k = g k))
          (ensures fin_sum f = fin_sum g)

val fin_sum_mul_left
  (#t:Type) {| r: semiring t |}
  (#n: nat) (c: t) (f: fin n -> t)
  : Lemma (c * fin_sum f = fin_sum (fun (k: fin n) -> c * f k))

val fin_sum_mul_right
  (#t:Type) {| r: semiring t |}
  (#n: nat) (f: fin n -> t) (c: t)
  : Lemma (fin_sum f * c = fin_sum (fun (k: fin n) -> f k * c))

unfold
let fin_swap_body (#t:Type) {| m: add_comm_monoid t |}
    (#n: nat) (f: fin n -> fin n -> t) (i j: nat) : t
  = if i < n && j < n then f (i <: fin n) (j <: fin n) else zero

val fin_sum_swap
  (#t:Type) {| m: add_comm_monoid t |}
  (#n: nat) (f: fin n -> fin n -> t)
  : Lemma (fin_sum (fun (i: fin n) -> fin_sum (f i))
         = fin_sum (fun (j: fin n) -> fin_sum (fun (i: fin n) -> f i j)))

(* ----------------------------------------------------------------- *)
(*  Additional helpers needed by the matrix ring + determinant       *)
(* ----------------------------------------------------------------- *)

val fin_sum_const_zero
  (#t:Type) {| m: add_comm_monoid t |} (#n: nat)
  : Lemma (fin_sum #t #m #n (fun (_: fin n) -> zero #t) = zero #t)

val fin_sum_zero_ext
  (#t:Type) {| m: add_comm_monoid t |} (#n: nat) (f: fin n -> t)
  : Lemma (requires (forall (k: fin n). f k = zero #t))
          (ensures fin_sum f = zero #t)

val fin_sum_add
  (#t:Type) {| m: add_comm_monoid t |} (#n: nat) (f g: fin n -> t)
  : Lemma (fin_sum (fun (k: fin n) -> f k + g k)
        = fin_sum f + fin_sum g)

val fin_sum_add_ext
  (#t:Type) {| m: add_comm_monoid t |} (#n: nat) (f g h: fin n -> t)
  : Lemma (requires (forall (k: fin n). h k = f k + g k))
          (ensures fin_sum h = fin_sum f + fin_sum g)

val sum_range_kronecker
  (#t:Type) {| r: semiring t |}
  (i0: nat) (g: nat -> t) (lo hi: nat)
  : Lemma (ensures sum_range (fun (k:nat) -> (if i0 = k then one else zero #t) * g k) lo hi
                 = (if lo <= i0 && i0 < hi then g i0 else zero #t))
          (decreases (if hi > lo then nat_minus hi lo else 0))

val fin_sum_kronecker
  (#t:Type) {| r: semiring t |}
  (#n: nat) (i0: fin n) (g: fin n -> t)
  : Lemma (fin_sum (fun (k: fin n) -> (if (i0 <: nat) = (k <: nat) then one else zero #t) * g k)
        = g i0)
