module FStar.CAS.Permutation

(*
  Permutations of [0..n) — public interface.

  A permutation of `fin n` carries its inverse and the two round-trip
  equations. Provides a `mul_group (permutation n)` typeclass instance for
  use by downstream determinant / sign-homomorphism code.

  Implementation (and a substantial pile of internal counting lemmas about
  inversion counts, adjacent-transposition swaps, etc.) lives in
  `FStar.CAS.Permutation.fst`.

  Author: A. Rozanov (CuteCAS).
*)

module TC = FStar.Tactics.Typeclasses
module E = FStar.CAS.Equatable
module G = FStar.CAS.Grouplikes

(* The natural-number-bounded index type used everywhere. *)
type fin (n: nat) = i:nat{i < n}

(* A permutation of `fin n` carries its inverse and the two round-trip proofs.
   Keeping the inverse explicit avoids any existential/decidability detours. *)
noeq type permutation (n: nat) = {
  fwd : fin n -> fin n;
  bwd : fin n -> fin n;
  fwd_bwd_id : (i: fin n) -> Lemma (fwd (bwd i) == i);
  bwd_fwd_id : (i: fin n) -> Lemma (bwd (fwd i) == i);
}

(* ------------------------------------------------------------------------ *)
(*  Basic operations                                                        *)
(* ------------------------------------------------------------------------ *)

val identity (n: nat) : permutation n

val identity_fwd (n: nat) (i: fin n)
  : Lemma ((identity n).fwd i == i /\ (identity n).bwd i == i)
          [SMTPat ((identity n).fwd i)]

val inverse (#n: nat) (p: permutation n) : permutation n

val compose (#n: nat) (p q: permutation n) : permutation n

(* Definitional unfolding of compose's .fwd: needed for downstream proofs that
   bridge composition and pointwise evaluation. *)
val compose_fwd (#n: nat) (p q: permutation n) (i: fin n)
  : Lemma ((compose p q).fwd i == p.fwd (q.fwd i))

val transposition (n: nat) (a b: fin n) : permutation n

(* Prefix-based boolean equality: agreement on every index k <= idx < n.
   Declared before perm_eq so the latter can reference it. *)
val perm_eq_bool_from (#n: nat) (p q: permutation n) (k: nat{k <= n}) : bool

(* Equality of permutations: decidable boolean equality checking every index.
   Hidden from SMT to save resources; use perm_eq_intro / _elim.
   Symmetry / transitivity / reflexivity are available via the equatable
   instance `permutation_equatable`. *)
[@@ "opaque_to_smt"]
let perm_eq (#n: nat) (p q: permutation n) : bool =
  perm_eq_bool_from p q 0

(* Internal helpers for the prefix-check. *)
val perm_eq_bool_from_sym (#n: nat) (p q: permutation n) (k: nat{k <= n})
  : Lemma (ensures perm_eq_bool_from p q k <==> perm_eq_bool_from q p k)
          (decreases (n - k))

val perm_eq_bool_from_trans (#n: nat) (p q r: permutation n) (k: nat{k <= n})
  : Lemma (requires perm_eq_bool_from p q k /\ perm_eq_bool_from q r k)
          (ensures  perm_eq_bool_from p r k)
          (decreases (n - k))

(* Pointwise agreement on fwd ⇒ prefix-equality. *)
val fwd_agree_implies_perm_eq_bool_from
  (#n: nat) (p q: permutation n) (k: nat{k <= n})
  : Lemma (requires forall (i: fin n). p.fwd i == q.fwd i)
          (ensures  perm_eq_bool_from p q k)
          (decreases (n - k))

(* The three public intro/elim lemmas — the only way to interact with
   perm_eq across the opacity barrier. *)
val perm_eq_intro (#n: nat) (p q: permutation n)
  : Lemma (requires forall (i: fin n). p.fwd i == q.fwd i)
          (ensures perm_eq p q)

val perm_eq_elim (#n: nat) (p q: permutation n) (i: fin n)
  : Lemma (requires perm_eq p q)
          (ensures p.fwd i == q.fwd i)

val perm_neq_intro (#n: nat) (p q: permutation n) (i: fin n)
  : Lemma (requires ~(p.fwd i == q.fwd i))
          (ensures ~(perm_eq p q))

(* ------------------------------------------------------------------------ *)
(*  Headline algebraic lemmas                                               *)
(* ------------------------------------------------------------------------ *)

val identity_left (#n: nat) (p: permutation n)
  : Lemma (perm_eq (compose (identity n) p) p)

val identity_right (#n: nat) (p: permutation n)
  : Lemma (perm_eq (compose p (identity n)) p)

val compose_associative (#n: nat) (p q r: permutation n)
  : Lemma (perm_eq (compose (compose p q) r) (compose p (compose q r)))

val inverse_left (#n: nat) (p: permutation n)
  : Lemma (perm_eq (compose (inverse p) p) (identity n))

val inverse_right (#n: nat) (p: permutation n)
  : Lemma (perm_eq (compose p (inverse p)) (identity n))

val inverse_involutive (#n: nat) (p: permutation n)
  : Lemma (perm_eq (inverse (inverse p)) p)

(* Definitional unfolding of inverse: its fwd is the original bwd, and vice versa.
   Exposed so downstream lemmas (e.g., reindexing by inverse) can reason about
   counts and bijection properties of `inverse` without piercing the abstraction. *)
val inverse_fwd (#n: nat) (p: permutation n) (j: fin n)
  : Lemma ((inverse p).fwd j == p.bwd j /\ (inverse p).bwd j == p.fwd j)

(* perm_eq is preserved by inverse. *)
val inverse_congruence (#n: nat) (p q: permutation n)
  : Lemma (requires perm_eq p q) (ensures perm_eq (inverse p) (inverse q))

val transposition_self_inverse (n: nat) (a b: fin n)
  : Lemma (perm_eq (compose (transposition n a b) (transposition n a b))
                   (identity n))

val transposition_trivial (n: nat) (a: fin n)
  : Lemma (perm_eq (transposition n a a) (identity n))

val transposition_fwd_left (n: nat) (a b: fin n)
  : Lemma ((transposition n a b).fwd a == b)

val transposition_fwd_right (n: nat) (a b: fin n)
  : Lemma ((transposition n a b).fwd b == a)

val transposition_fwd_other (n: nat) (a b k: fin n)
  : Lemma (requires ~(k == a) /\ ~(k == b))
          (ensures (transposition n a b).fwd k == k)

(* Injectivity of `fwd` — direct consequence of having the inverse. *)
val fwd_injective (#n: nat) (p: permutation n) (i j: fin n)
  : Lemma (requires p.fwd i == p.fwd j) (ensures i == j)

(* ------------------------------------------------------------------------ *)
(*  Inversion count and parity                                              *)
(* ------------------------------------------------------------------------ *)

val inversion_count (#n: nat) (p: permutation n) : nat

(* parity = true  <==>  even number of inversions  <==>  sign +1 *)
val parity (#n: nat) (p: permutation n) : bool

val inversion_count_identity (n: nat)
  : Lemma (inversion_count (identity n) == 0)

val parity_identity (n: nat) : Lemma (parity (identity n) == true)

(* ------------------------------------------------------------------------ *)
(*  Typeclass instances: equatable, mul_*                                   *)
(* ------------------------------------------------------------------------ *)

instance val permutation_equatable (n: nat) : E.equatable (permutation n)

(* Composition congruence over perm_eq (used by the mul_semigroup
   instance below — and by downstream proofs). *)
val compose_congruence (#n: nat) (p1 q1 p2 q2: permutation n)
  : Lemma (requires perm_eq p1 p2 /\ perm_eq q1 q2)
          (ensures  perm_eq (compose p1 q1) (compose p2 q2))

instance val permutation_has_mul (n: nat) : G.has_mul (permutation n)

instance val permutation_mul_semigroup (n: nat) : G.mul_semigroup (permutation n)

instance val permutation_has_one (n: nat) : G.has_one (permutation n)

instance val permutation_mul_monoid (n: nat) : G.mul_monoid (permutation n)

instance val permutation_has_inv (n: nat) : G.has_inv (permutation n)

instance val permutation_mul_group (n: nat) : G.mul_group (permutation n)

(* ------------------------------------------------------------------------ *)
(*  Parity headlines: transposition, perm_eq invariance, sign homomorphism   *)
(* ------------------------------------------------------------------------ *)

val parity_transposition (n: nat) (a b: fin n)
  : Lemma (ensures parity (transposition n a b) == (a = b))

(* Right multiplication by an adjacent transposition.  Kept public because
   it appears in the headline sign-homomorphism lemma. *)
val right_swap (#n: nat) (p: permutation n) (i: nat{i + 1 < n}) : permutation n

(* Explicit rewrite of [.fwd] after a right_swap. *)
val right_swap_fwd_at_k (#n: nat) (p: permutation n) (i: nat{i+1 < n}) (k: fin n)
  : Lemma (ensures
            (right_swap p i).fwd k ==
            (if k = i then p.fwd (i+1)
             else if k = i+1 then p.fwd i
             else p.fwd k))

(* Zero inversion count ⟹ extensionally the identity permutation. *)
val inv_zero_implies_identity_fwd (#n: nat) (p: permutation n) (k: fin n)
  : Lemma (requires inversion_count p == 0)
          (ensures p.fwd k == k)

val parity_perm_eq_invariant (#n: nat) (p1 p2: permutation n)
  : Lemma (requires perm_eq p1 p2)
          (ensures  parity p1 == parity p2)

(* Descent finder: returns the first position i with p.fwd i > p.fwd (i+1). *)
val find_descent (#n: nat) (q: permutation n) (i: nat{i <= n})
  : Tot (option (j: nat{j + 1 < n /\ q.fwd j > q.fwd (j+1)}))
        (decreases (n - i))

(* If find_descent returns None, inversion_count is 0. *)
val find_descent_none_implies_inv_zero (#n: nat) (q: permutation n)
  : Lemma (requires None? (find_descent q 0))
          (ensures inversion_count q == 0)

(* If find_descent returns Some i, right_swap at i decreases inv count. *)
val inv_right_swap_at_descent (#n: nat) (q: permutation n) (i: nat{i+1 < n})
  : Lemma (requires q.fwd i > q.fwd (i+1))
          (ensures inversion_count (right_swap q i) + 1 == inversion_count q)

(* Sign homomorphism: parity is a group homomorphism into the sign group. *)
val sign_homomorphism (#n: nat) (p q: permutation n)
  : Lemma (parity (compose p q) == (parity p = parity q))

(* The inverse permutation has the same parity. *)
val parity_inverse (#n: nat) (p: permutation n)
  : Lemma (parity (inverse p) == parity p)

(* Either the inversion count is zero, or some adjacent right_swap strictly
   decreases it.  Used to prove results by induction on inversion_count. *)
val perm_descent_exists_or_inv_zero (#n: nat) (p: permutation n)
  : Lemma (inversion_count p == 0 \/
           (exists (i: nat{i+1 < n}).
              inversion_count (right_swap p i) < inversion_count p))

(* ------------------------------------------------------------------------ *)
(*  Block-swap permutation: swap blocks of sizes m and n in [0..m+n).        *)
(*  Parity = (-1)^(m*n).                                                    *)
(* ------------------------------------------------------------------------ *)

val block_swap_perm (m n: nat) : permutation (m + n)

val inversion_count_block_swap (m n: nat)
  : Lemma (inversion_count (block_swap_perm m n) == m * n)

val parity_block_swap (m n: nat)
  : Lemma (parity (block_swap_perm m n) == ((m * n) % 2 = 0))

val block_swap_perm_fwd (m n: nat) (k: fin (m + n))
  : Lemma ((block_swap_perm m n).fwd k ==
           (if (k <: nat) < m then (k <: nat) + n else (k <: nat) - m))
