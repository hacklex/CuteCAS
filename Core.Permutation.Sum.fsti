module Core.Permutation.Sum

(*
   Public interface for summing a function `f : permutation n -> t` over
   all permutations of `Fin n`, where `t` is an additive commutative
   monoid.  Implementation in `Core.Permutation.Sum.fst`.

   H4 hygiene: pre/postconditions of public lemmas are kept free of
   `forall`, inline `fun`, and conditional `if`/`match`.  Equality
   hypotheses are passed as callback lemmas; functional rearrangements
   are expressed via the named combinators in
   `Core.Algebra.Combinators` (`fcomp`, `flip`, `pointwise_*`).
*)

module TC = FStar.Tactics.Typeclasses
open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Permutation
open Core.Permutation.Enum
open Core.FinSum
module L = FStar.List.Tot

(* -------------------------------------------------------------------- *)
(*  Definition.                                                         *)
(* -------------------------------------------------------------------- *)

val sum_over_perms
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (f: permutation n -> t) : t

(* Reveal: sum_over_perms is the sum_list over the permutation enumeration.
   Lets downstream code transport a ring homomorphism (e.g. poly_eval at c)
   through sum_over_perms via the corresponding sum_list lemma. *)
val sum_over_perms_reveal
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (f: permutation n -> t)
  : Lemma (sum_over_perms n f == sum_list (L.map f (all_permutations n)))

(* -------------------------------------------------------------------- *)
(*  Congruence under pointwise-equal functions.                         *)
(* -------------------------------------------------------------------- *)

val sum_over_perms_congruence
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (f g: permutation n -> t)
  (h: (s: permutation n) -> Lemma (f s = g s))
  : Lemma (ensures sum_over_perms n f = sum_over_perms n g)

(* Negation distributes over sum_over_perms. *)
val sum_over_perms_neg
  (#t: Type) {| g: add_comm_group t |}
  (n: nat) (f: permutation n -> t)
  : Lemma (sum_over_perms n (pointwise_neg f) = neg (sum_over_perms n f))

(* Named-function variant of sum_over_perms_neg.
   Useful when the caller is in a commutative_ring context (where projecting
   to add_comm_group via acg_of_ring creates a TC diamond that prevents the
   lambda-based postcondition of sum_over_perms_neg from unifying). Taking
   the negated function by name and a callback avoids the lambda-encoding
   mismatch under SMT. *)
val sum_over_perms_neg_named
  (#t: Type) {| g: add_comm_group t |}
  (n: nat) (nf f: permutation n -> t)
  (h: (s: permutation n) -> Lemma (nf s = neg (f s)))
  : Lemma (ensures sum_over_perms n nf = neg (sum_over_perms n f))

(* Sum-of-pointwise-sum is sum of sums. *)
val sum_over_perms_add
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (f g: permutation n -> t)
  : Lemma (sum_over_perms n (pointwise_add f g)
         = sum_over_perms n f + sum_over_perms n g)

(* Pointwise additivity with the combined function passed by name.    *)
val sum_over_perms_add_named
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (s f g: permutation n -> t)
  (h: (p: permutation n) -> Lemma (s p = f p + g p))
  : Lemma (ensures  sum_over_perms n s = sum_over_perms n f + sum_over_perms n g)

(* Left-scaling distributes over sum_over_perms (ring). *)
val sum_over_perms_mul_left
  (#t: Type) {| r: ring t |}
  (n: nat) (c: t) (f: permutation n -> t)
  : Lemma (c * sum_over_perms n f = sum_over_perms n (pointwise_mul (const c) f))

(* Named-function variant of sum_over_perms_mul_left. *)
val sum_over_perms_mul_left_named
  (#t: Type) {| r: ring t |}
  (n: nat) (c: t) (cf f: permutation n -> t)
  (h: (s: permutation n) -> Lemma (cf s = c * f s))
  : Lemma (ensures  sum_over_perms n cf = c * sum_over_perms n f)

(* -------------------------------------------------------------------- *)
(*  Base case: n = 0.                                                   *)
(* -------------------------------------------------------------------- *)

val sum_over_perms_zero
  (#t: Type) {| m: add_comm_group t |}
  (f: permutation 0 -> t)
  : Lemma (sum_over_perms 0 f = f (identity 0) + zero)

(* -------------------------------------------------------------------- *)
(*  Predicate: f respects perm_eq.                                      *)
(*  Opaque to SMT — use respects_perm_eq_elim to extract the implication. *)
(*                                                                       *)
(*  This is a definition body (not a Lemma pre/postcondition), so the   *)
(*  internal `forall` is fine; consumers only see the predicate name.   *)
(* -------------------------------------------------------------------- *)

[@@ "opaque_to_smt"]
let respects_perm_eq
  (#t: Type) {| equatable t |}
  (#n: nat) (f: permutation n -> t) : prop
  = forall (p q: permutation n). perm_eq p q ==> f p = f q

val respects_perm_eq_intro
  (#t: Type) {| equatable t |}
  (#n: nat) (f: permutation n -> t)
  (h: (p: permutation n) -> (q: permutation n) ->
      Lemma (requires perm_eq p q) (ensures f p = f q))
  : Lemma (ensures respects_perm_eq f)

val respects_perm_eq_elim
  (#t: Type) {| equatable t |}
  (#n: nat) (f: permutation n -> t) (p q: permutation n)
  : Lemma (requires respects_perm_eq f /\ perm_eq p q)
          (ensures f p = f q)

(* -------------------------------------------------------------------- *)
(*  List-level infrastructure for partition/reindexing proofs.           *)
(* -------------------------------------------------------------------- *)

(* Indicator helper: avoids exposing `if` in public lemma signatures. *)
unfold let bool_to_nat (b: bool) : nat = if b then 1 else 0

(* Counting perm_eq matches in a list. *)
val perm_eq_count (#n: nat) (p: permutation n) (xs: list (permutation n)) : nat

val perm_eq_count_nil (#n: nat) (p: permutation n)
  : Lemma (perm_eq_count p [] == 0)

val perm_eq_count_cons (#n: nat) (p h: permutation n) (tl: list (permutation n))
  : Lemma (perm_eq_count p (h :: tl) ==
           Prims.op_Addition (bool_to_nat (perm_eq p h)) (perm_eq_count p tl))

val perm_eq_count_append (#n: nat) (p: permutation n) (xs ys: list (permutation n))
  : Lemma (perm_eq_count p (L.append xs ys) ==
           Prims.op_Addition (perm_eq_count p xs) (perm_eq_count p ys))

(* Unfolding perm_eq_count through L.map: one step. *)
val perm_eq_count_map_cons (#n #m: nat) (f: permutation m -> permutation n)
  (p: permutation n) (h: permutation m) (tl: list (permutation m))
  : Lemma (perm_eq_count p (L.map f (h :: tl)) ==
           Prims.op_Addition
             (bool_to_nat (perm_eq p (f h)))
             (perm_eq_count p (L.map f tl)))

val perm_eq_count_map_nil (#n #m: nat) (f: permutation m -> permutation n)
  (p: permutation n)
  : Lemma (perm_eq_count p (L.map f []) == 0)

(* sum_list distributes over append. *)
val sum_list_append
  (#t: Type) {| m: add_comm_group t |}
  (xs ys: list t)
  : Lemma (sum_list (L.append xs ys) = sum_list xs + sum_list ys)

(* Every permutation has count exactly 1 in all_permutations n. *)
val all_permutations_count_one (n: nat) (p: permutation n)
  : Lemma (perm_eq_count p (all_permutations n) == 1)

(* If f respects perm_eq, and ys has count 1 for every permutation,
   then sum_over_perms n f = sum_list (map f ys). *)
val sum_over_perms_via_count_one_list
  (#t: Type) {| m: add_comm_group t |}
  (#n: nat) (f: permutation n -> t) (ys: list (permutation n))
  (h_count: (p: permutation n) -> Lemma (perm_eq_count p ys == 1))
  : Lemma (requires respects_perm_eq #t f)
          (ensures sum_over_perms n f = sum_list (L.map f ys))

(* Composing maps via the named `fcomp` combinator. *)
val map_map_eq (#a #b #c: Type) (g: a -> b) (f: b -> c) (xs: list a)
  : Lemma (L.map f (L.map g xs) == L.map (fcomp f g) xs)

(* -------------------------------------------------------------------- *)
(*  Reindexing by right-multiplication: bijection on the index set.     *)
(*                                                                      *)
(*  The reindexed function `fun s -> f (compose s q)` is named as       *)
(*  `fcomp f (flip compose q)` to keep the public post lambda-free.     *)
(* -------------------------------------------------------------------- *)

val sum_over_perms_reindex
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (f: permutation n -> t) (q: permutation n)
  : Lemma (requires respects_perm_eq #t f)
          (ensures  sum_over_perms n f =
                    sum_over_perms n (fcomp f (flip compose q)))

(* -------------------------------------------------------------------- *)
(*  Reindexing by inverse.                                              *)
(* -------------------------------------------------------------------- *)

val sum_over_perms_reindex_inverse
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (f: permutation n -> t)
  : Lemma (requires respects_perm_eq #t f)
          (ensures  sum_over_perms n f =
                    sum_over_perms n (fcomp f inverse))

(* -------------------------------------------------------------------- *)
(*  Single-nonzero-summand lemma: if f vanishes off the perm_eq class    *)
(*  of [p0] and respects [perm_eq], then [sum_over_perms n f = f p0].   *)
(* -------------------------------------------------------------------- *)

val sum_over_perms_single
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (f: permutation n -> t) (p0: permutation n)
  (h_zero: (q: permutation n) ->
           Lemma (requires ~(perm_eq p0 q)) (ensures f q = zero))
  : Lemma (requires respects_perm_eq #t f)
          (ensures sum_over_perms n f = f p0)

(* -------------------------------------------------------------------- *)
(*  If every summand is zero, the whole sum is zero.                    *)
(* -------------------------------------------------------------------- *)

val sum_over_perms_all_zero
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (f: permutation n -> t)
  (h: (p: permutation n) -> Lemma (f p = zero))
  : Lemma (ensures  sum_over_perms n f = zero)

(* -------------------------------------------------------------------- *)
(*  τ-orbit pair-cancellation: if τ is a fixed-point-free involution    *)
(*  and f σ + f (σ∘τ) = 0 for every σ, then sum_over_perms n f = 0.     *)
(*  This works over any additive commutative group; no char≠2 needed.    *)
(* -------------------------------------------------------------------- *)

val sum_over_perms_pair_cancel
  (#t: Type) {| g: add_comm_group t |}
  (n: nat) (f: permutation n -> t) (tau: permutation n)
  (h_pair: (s: permutation n) -> Lemma (f s + f (compose s tau) = zero))
  : Lemma (requires
              respects_perm_eq #t f /\
              ~ (perm_eq tau (identity n)) /\
              perm_eq (compose tau tau) (identity n))
          (ensures sum_over_perms n f = zero)
