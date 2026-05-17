module FStar.CAS.Permutation.Sum

(*
   Public interface for summing a function `f : permutation n -> t` over
   all permutations of `Fin n`, where `t` is an additive commutative
   monoid.  Implementation in `FStar.CAS.Permutation.Sum.fst`.
*)

open FStar.CAS.Permutation
open FStar.CAS.Permutation.Enum
open FStar.CAS.Equatable
open FStar.CAS.Grouplikes
open FStar.CAS.Ringlikes
open FStar.CAS.FinSum
module L = FStar.List.Tot

(* -------------------------------------------------------------------- *)
(*  Definition.                                                         *)
(* -------------------------------------------------------------------- *)

val sum_over_perms
  (#t: Type) {| m: add_comm_monoid t |}
  (n: nat) (f: permutation n -> t) : t

(* -------------------------------------------------------------------- *)
(*  Congruence under pointwise-equal functions.                         *)
(* -------------------------------------------------------------------- *)

val sum_over_perms_congruence
  (#t: Type) {| m: add_comm_monoid t |}
  (n: nat) (f g: permutation n -> t)
  : Lemma (requires forall (s: permutation n). f s = g s)
          (ensures sum_over_perms n f = sum_over_perms n g)

(* Negation distributes over sum_over_perms. *)
val sum_over_perms_neg
  (#t: Type) {| g: add_comm_group t |}
  (n: nat) (f: permutation n -> t)
  : Lemma (sum_over_perms n (fun s -> -(f s)) = -(sum_over_perms n f))

(* Sum-of-pointwise-sum is sum of sums. *)
val sum_over_perms_add
  (#t: Type) {| m: add_comm_monoid t |}
  (n: nat) (f g: permutation n -> t)
  : Lemma (sum_over_perms n (fun s -> f s + g s)
         = sum_over_perms n f + sum_over_perms n g)

(* Pointwise additivity with the combined function passed by name.    *)
(* Bridges the SMT lambda-skolemization gap that arises when callers   *)
(* want to apply sum_over_perms_add via a let-bound function name.     *)
val sum_over_perms_add_named
  (#t: Type) {| m: add_comm_monoid t |}
  (n: nat) (s f g: permutation n -> t)
  : Lemma (requires forall (p: permutation n). s p = f p + g p)
          (ensures  sum_over_perms n s = sum_over_perms n f + sum_over_perms n g)

(* Left-scaling distributes over sum_over_perms (semiring). *)
val sum_over_perms_mul_left
  (#t: Type) {| r: semiring t |}
  (n: nat) (c: t) (f: permutation n -> t)
  : Lemma (c * sum_over_perms n f = sum_over_perms n (fun s -> c * f s))

(* -------------------------------------------------------------------- *)
(*  Base case: n = 0.                                                   *)
(* -------------------------------------------------------------------- *)

val sum_over_perms_zero
  (#t: Type) {| m: add_comm_monoid t |}
  (f: permutation 0 -> t)
  : Lemma (sum_over_perms 0 f = f (identity 0) + zero)

(* -------------------------------------------------------------------- *)
(*  Predicate: f respects perm_eq.                                      *)
(*  Opaque to SMT — use respects_perm_eq_elim to extract the implication. *)
(* -------------------------------------------------------------------- *)

[@@ "opaque_to_smt"]
let respects_perm_eq
  (#t: Type) {| equatable t |}
  (#n: nat) (f: permutation n -> t) : prop
  = forall (p q: permutation n). perm_eq p q ==> f p = f q

val respects_perm_eq_intro
  (#t: Type) {| equatable t |}
  (#n: nat) (f: permutation n -> t)
  : Lemma (requires forall (p q: permutation n). perm_eq p q ==> f p = f q)
          (ensures respects_perm_eq f)

val respects_perm_eq_elim
  (#t: Type) {| equatable t |}
  (#n: nat) (f: permutation n -> t) (p q: permutation n)
  : Lemma (requires respects_perm_eq f /\ perm_eq p q)
          (ensures f p = f q)

(* -------------------------------------------------------------------- *)
(*  List-level infrastructure for partition/reindexing proofs.           *)
(* -------------------------------------------------------------------- *)

(* Counting perm_eq matches in a list. *)
val perm_eq_count (#n: nat) (p: permutation n) (xs: list (permutation n)) : nat

val perm_eq_count_nil (#n: nat) (p: permutation n)
  : Lemma (perm_eq_count p [] == 0)

val perm_eq_count_cons (#n: nat) (p h: permutation n) (tl: list (permutation n))
  : Lemma (perm_eq_count p (h :: tl) ==
           Prims.op_Addition (if perm_eq p h then 1 else 0) (perm_eq_count p tl))

val perm_eq_count_append (#n: nat) (p: permutation n) (xs ys: list (permutation n))
  : Lemma (perm_eq_count p (L.append xs ys) ==
           Prims.op_Addition (perm_eq_count p xs) (perm_eq_count p ys))

(* Unfolding perm_eq_count through L.map: one step. *)
val perm_eq_count_map_cons (#n #m: nat) (f: permutation m -> permutation n)
  (p: permutation n) (h: permutation m) (tl: list (permutation m))
  : Lemma (perm_eq_count p (L.map f (h :: tl)) ==
           Prims.op_Addition
             (if perm_eq p (f h) then 1 else 0)
             (perm_eq_count p (L.map f tl)))

val perm_eq_count_map_nil (#n #m: nat) (f: permutation m -> permutation n)
  (p: permutation n)
  : Lemma (perm_eq_count p (L.map f []) == 0)

(* sum_list distributes over append. *)
val sum_list_append
  (#t: Type) {| m: add_comm_monoid t |}
  (xs ys: list t)
  : Lemma (sum_list (L.append xs ys) = sum_list xs + sum_list ys)

(* Every permutation has count exactly 1 in all_permutations n. *)
val all_permutations_count_one (n: nat) (p: permutation n)
  : Lemma (perm_eq_count p (all_permutations n) == 1)

(* If f respects perm_eq, and ys has count 1 for every permutation,
   then sum_over_perms n f = sum_list (map f ys). *)
val sum_over_perms_via_count_one_list
  (#t: Type) {| m: add_comm_monoid t |}
  (#n: nat) (f: permutation n -> t) (ys: list (permutation n))
  : Lemma (requires respects_perm_eq #t f /\
                    (forall (p: permutation n). perm_eq_count p ys == 1))
          (ensures sum_over_perms n f = sum_list (L.map f ys))

(* Composing maps. *)
val map_map_eq (#a #b #c: Type) (g: a -> b) (f: b -> c) (xs: list a)
  : Lemma (L.map f (L.map g xs) == L.map (fun x -> f (g x)) xs)

(* -------------------------------------------------------------------- *)
(*  Reindexing by right-multiplication: bijection on the index set.     *)
(* -------------------------------------------------------------------- *)

val sum_over_perms_reindex
  (#t: Type) {| m: add_comm_monoid t |}
  (n: nat) (f: permutation n -> t) (q: permutation n)
  : Lemma (requires respects_perm_eq #t f)
          (ensures  sum_over_perms n f =
                    sum_over_perms n (fun s -> f (compose s q)))

(* -------------------------------------------------------------------- *)
(*  Reindexing by inverse.                                              *)
(* -------------------------------------------------------------------- *)

val sum_over_perms_reindex_inverse
  (#t: Type) {| m: add_comm_monoid t |}
  (n: nat) (f: permutation n -> t)
  : Lemma (requires respects_perm_eq #t f)
          (ensures  sum_over_perms n f =
                    sum_over_perms n (fun s -> f (inverse s)))

(* -------------------------------------------------------------------- *)
(*  Single-nonzero-summand lemma: if f vanishes off the perm_eq class    *)
(*  of [p0] and respects [perm_eq], then [sum_over_perms n f = f p0].   *)
(* -------------------------------------------------------------------- *)

val sum_over_perms_single
  (#t: Type) {| m: add_comm_monoid t |}
  (n: nat) (f: permutation n -> t) (p0: permutation n)
  : Lemma (requires respects_perm_eq #t f /\
                    (forall (q: permutation n). ~(perm_eq p0 q) ==> f q = zero))
          (ensures sum_over_perms n f = f p0)

(* -------------------------------------------------------------------- *)
(*  If every summand is zero, the whole sum is zero.                    *)
(* -------------------------------------------------------------------- *)

val sum_over_perms_all_zero
  (#t: Type) {| m: add_comm_monoid t |}
  (n: nat) (f: permutation n -> t)
  : Lemma (requires forall (p: permutation n). f p = zero)
          (ensures  sum_over_perms n f = zero)

(* -------------------------------------------------------------------- *)
(*  τ-orbit pair-cancellation: if τ is a fixed-point-free involution    *)
(*  and f σ + f (σ∘τ) = 0 for every σ, then sum_over_perms n f = 0.     *)
(*  This works over any additive commutative group; no char≠2 needed.    *)
(* -------------------------------------------------------------------- *)

val sum_over_perms_pair_cancel
  (#t: Type) {| g: add_comm_group t |}
  (n: nat) (f: permutation n -> t) (tau: permutation n)
  : Lemma (requires
              respects_perm_eq #t f /\
              ~ (perm_eq tau (identity n)) /\
              perm_eq (compose tau tau) (identity n) /\
              (forall (s: permutation n). f s + f (compose s tau) = zero))
          (ensures sum_over_perms n f = zero)
