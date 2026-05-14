module FStar.Algebra.Permutation

(*
  Permutations of [0..n) — a bijection on `fin n` packaged with its inverse
  and the round-trip equations.

  Designed for use in determinant and resultant constructions. Provides a
  `mul_group (permutation n)` typeclass instance for use by downstream modules.

  Author: A. Rozanov (CuteCAS).
*)

module TC = FStar.Tactics.Typeclasses

(* The natural-number-bounded index type used everywhere. *)
type fin (n: nat) = i:nat{i < n}

(* A permutation of `fin n` carries its inverse and the two round-trip proofs.
   Keeping the inverse explicit avoids any existential/decidability detours.
*)
noeq type permutation (n: nat) = {
  fwd : fin n -> fin n;
  bwd : fin n -> fin n;
  fwd_bwd_id : (i: fin n) -> Lemma (fwd (bwd i) == i);
  bwd_fwd_id : (i: fin n) -> Lemma (bwd (fwd i) == i);
}

(* Basic operations *)

let identity (n: nat) : permutation n = {
  fwd = (fun i -> i);
  bwd = (fun i -> i);
  fwd_bwd_id = (fun _ -> ());
  bwd_fwd_id = (fun _ -> ());
}

let inverse (#n: nat) (p: permutation n) : permutation n = {
  fwd = p.bwd;
  bwd = p.fwd;
  fwd_bwd_id = p.bwd_fwd_id;
  bwd_fwd_id = p.fwd_bwd_id;
}

let compose (#n: nat) (p q: permutation n) : permutation n = {
  fwd = (fun i -> p.fwd (q.fwd i));
  bwd = (fun i -> q.bwd (p.bwd i));
  fwd_bwd_id = (fun i ->
    (* q.fwd (q.bwd (p.bwd i)) = p.bwd i ;  then  p.fwd (p.bwd i) = i *)
    q.fwd_bwd_id (p.bwd i);
    p.fwd_bwd_id i);
  bwd_fwd_id = (fun i ->
    p.bwd_fwd_id (q.fwd i);
    q.bwd_fwd_id i);
}

(* Transposition of two distinct indices, identity elsewhere. *)
let transposition (n: nat) (a b: fin n) : permutation n =
  let swap (i: fin n) : fin n =
    if i = a then b else if i = b then a else i
  in
  {
    fwd = swap;
    bwd = swap;
    fwd_bwd_id = (fun _ -> ());
    bwd_fwd_id = (fun _ -> ());
  }

(* Equality of permutations: agreement of `fwd` on every index. *)
let perm_eq (#n: nat) (p q: permutation n) : prop =
  forall (i: fin n). p.fwd i == q.fwd i

(* Key algebraic facts *)

let identity_left (#n: nat) (p: permutation n)
  : Lemma (perm_eq (compose (identity n) p) p) = ()

let identity_right (#n: nat) (p: permutation n)
  : Lemma (perm_eq (compose p (identity n)) p) = ()

let compose_associative (#n: nat) (p q r: permutation n)
  : Lemma (perm_eq (compose (compose p q) r) (compose p (compose q r))) = ()

let inverse_left (#n: nat) (p: permutation n)
  : Lemma (perm_eq (compose (inverse p) p) (identity n)) =
  let lhs = compose (inverse p) p in
  let goal (i: fin n) : Lemma (lhs.fwd i == i) = p.bwd_fwd_id i in
  Classical.forall_intro goal

let inverse_right (#n: nat) (p: permutation n)
  : Lemma (perm_eq (compose p (inverse p)) (identity n)) =
  let lhs = compose p (inverse p) in
  let goal (i: fin n) : Lemma (lhs.fwd i == i) = p.fwd_bwd_id i in
  Classical.forall_intro goal

let inverse_involutive (#n: nat) (p: permutation n)
  : Lemma (perm_eq (inverse (inverse p)) p) = ()

(* Transposition self-inverse + identity outside its support. *)

let transposition_self_inverse (n: nat) (a b: fin n)
  : Lemma (perm_eq (compose (transposition n a b) (transposition n a b))
                   (identity n)) = ()

let transposition_trivial (n: nat) (a: fin n)
  : Lemma (perm_eq (transposition n a a) (identity n)) = ()

(* Injectivity of `fwd` — a direct consequence of having the inverse. *)
let fwd_injective (#n: nat) (p: permutation n) (i j: fin n)
  : Lemma (requires p.fwd i == p.fwd j) (ensures i == j) =
  p.bwd_fwd_id i;
  p.bwd_fwd_id j

(* ------------------------------------------------------------------------ *)
(*  Sign / parity of a permutation                                          *)
(*                                                                          *)
(*  We use the inversion-count definition:                                  *)
(*    inv(p) = |{(i,j) : 0 <= i < j < n /\ p.fwd i > p.fwd j}|.             *)
(*  sign(p) = inv(p) mod 2 = 0  encodes  "+1" (even permutation),           *)
(*                         = 1  encodes  "-1" (odd permutation).            *)
(*  We expose `parity` as bool (true = even = "+1").                        *)
(* ------------------------------------------------------------------------ *)

(* For a fixed left index `i`, count `j > i` with `p.fwd i > p.fwd j`. *)
let rec count_at_left
  (#n: nat) (p: permutation n) (i: fin n) (j: nat{j <= n})
  : Tot nat (decreases (n - j))
  = if j >= n then 0
    else
      let here = if j > i && p.fwd i > p.fwd j then 1 else 0 in
      here + count_at_left p i (j + 1)

(* Sum the per-left-index counts across all i. *)
let rec inversion_count_aux
  (#n: nat) (p: permutation n) (i: nat{i <= n})
  : Tot nat (decreases (n - i))
  = if i >= n then 0
    else count_at_left p i 0 + inversion_count_aux p (i + 1)

let inversion_count (#n: nat) (p: permutation n) : nat =
  inversion_count_aux p 0

(* parity = true  <==>  even number of inversions  <==>  sign +1 *)
let parity (#n: nat) (p: permutation n) : bool =
  inversion_count p % 2 = 0

(* The identity has no inversions. *)

let rec count_at_left_identity (n: nat) (i: fin n) (j: nat{j <= n})
  : Lemma (ensures count_at_left (identity n) i j == 0)
          (decreases (n - j))
  = if j >= n then ()
    else count_at_left_identity n i (j + 1)

let rec inversion_count_identity_aux (n: nat) (i: nat{i <= n})
  : Lemma (ensures inversion_count_aux (identity n) i == 0)
          (decreases (n - i))
  = if i >= n then ()
    else (
      count_at_left_identity n i 0;
      inversion_count_identity_aux n (i + 1)
    )

let inversion_count_identity (n: nat)
  : Lemma (inversion_count (identity n) == 0)
  = inversion_count_identity_aux n 0

let parity_identity (n: nat) : Lemma (parity (identity n) == true) =
  inversion_count_identity n

(* ------------------------------------------------------------------------ *)
(*  Typeclass instances: G.mul_group (permutation n)                          *)
(* ------------------------------------------------------------------------ *)

module E = FStar.Algebra.Classes.Equatable
module G = FStar.Algebra.Classes.Grouplikes

(* Boolean extensional equality: agree on every index k < n. *)
let rec perm_eq_bool_from (#n: nat) (p q: permutation n) (k: nat{k <= n})
  : Tot bool (decreases (n - k))
  = if k >= n then true
    else (p.fwd k = q.fwd k) && perm_eq_bool_from p q (k + 1)

let perm_eq_bool (#n: nat) (p q: permutation n) : bool =
  perm_eq_bool_from p q 0

(* Reflexivity of perm_eq_bool_from. *)
let rec perm_eq_bool_from_refl (#n: nat) (p: permutation n) (k: nat{k <= n})
  : Lemma (ensures perm_eq_bool_from p p k) (decreases (n - k))
  = if k >= n then ()
    else perm_eq_bool_from_refl p (k + 1)

let perm_eq_bool_refl (#n: nat) (p: permutation n)
  : Lemma (perm_eq_bool p p)
  = perm_eq_bool_from_refl p 0

(* Symmetry. *)
let rec perm_eq_bool_from_sym (#n: nat) (p q: permutation n) (k: nat{k <= n})
  : Lemma (ensures perm_eq_bool_from p q k <==> perm_eq_bool_from q p k)
          (decreases (n - k))
  = if k >= n then ()
    else perm_eq_bool_from_sym p q (k + 1)

(* Transitivity. *)
let rec perm_eq_bool_from_trans (#n: nat) (p q r: permutation n) (k: nat{k <= n})
  : Lemma (requires perm_eq_bool_from p q k /\ perm_eq_bool_from q r k)
          (ensures  perm_eq_bool_from p r k)
          (decreases (n - k))
  = if k >= n then ()
    else perm_eq_bool_from_trans p q r (k + 1)

instance permutation_equatable (n: nat) : E.equatable (permutation n) = {
  op_Equals    = perm_eq_bool;
  reflexivity  = (fun p -> perm_eq_bool_refl p);
  symmetry     = (fun p q -> perm_eq_bool_from_sym p q 0);
  transitivity = (fun p q r -> perm_eq_bool_from_trans p q r 0);
}

(* From the boolean equality back to extensional agreement. *)
let rec perm_eq_bool_from_implies_fwd
  (#n: nat) (p q: permutation n) (k: nat{k <= n}) (i: fin n)
  : Lemma (requires perm_eq_bool_from p q k /\ i >= k)
          (ensures  p.fwd i == q.fwd i)
          (decreases (n - k))
  = if k >= n then ()
    else if i = k then ()
    else perm_eq_bool_from_implies_fwd p q (k + 1) i

let perm_eq_bool_implies_fwd (#n: nat) (p q: permutation n) (i: fin n)
  : Lemma (requires perm_eq_bool p q) (ensures p.fwd i == q.fwd i)
  = perm_eq_bool_from_implies_fwd p q 0 i

(* And the other direction: extensional agreement implies the boolean equality. *)
let rec fwd_agree_implies_perm_eq_bool_from
  (#n: nat) (p q: permutation n) (k: nat{k <= n})
  : Lemma (requires forall (i: fin n). p.fwd i == q.fwd i)
          (ensures  perm_eq_bool_from p q k)
          (decreases (n - k))
  = if k >= n then ()
    else fwd_agree_implies_perm_eq_bool_from p q (k + 1)

(* Composition congruence: equal in -> equal out. *)
let compose_congruence (#n: nat) (p1 q1 p2 q2: permutation n)
  : Lemma (requires perm_eq_bool p1 p2 /\ perm_eq_bool q1 q2)
          (ensures  perm_eq_bool (compose p1 q1) (compose p2 q2))
  = let aux (i: fin n) : Lemma ((compose p1 q1).fwd i == (compose p2 q2).fwd i) =
      perm_eq_bool_implies_fwd q1 q2 i;
      perm_eq_bool_implies_fwd p1 p2 (q1.fwd i)
    in
    Classical.forall_intro aux;
    fwd_agree_implies_perm_eq_bool_from (compose p1 q1) (compose p2 q2) 0

instance permutation_has_mul (n: nat) : G.has_mul (permutation n) = {
  eq = permutation_equatable n;
  ( * ) = compose;
  congruence = (fun p1 q1 p2 q2 -> compose_congruence p1 q1 p2 q2);
}

(* Associativity of composition lifted to the boolean equality. *)
let compose_assoc_bool (#n: nat) (p q r: permutation n)
  : Lemma (perm_eq_bool (compose (compose p q) r) (compose p (compose q r)))
  = fwd_agree_implies_perm_eq_bool_from
      (compose (compose p q) r) (compose p (compose q r)) 0

instance permutation_mul_semigroup (n: nat) : G.mul_semigroup (permutation n) = {
  has_mul = permutation_has_mul n;
  associativity = (fun p q r -> compose_assoc_bool p q r);
}

instance permutation_has_one (n: nat) : G.has_one (permutation n) = {
  eq = permutation_equatable n;
  one = identity n;
}

let identity_left_bool (#n: nat) (p: permutation n)
  : Lemma (perm_eq_bool (compose (identity n) p) p)
  = fwd_agree_implies_perm_eq_bool_from (compose (identity n) p) p 0

let identity_right_bool (#n: nat) (p: permutation n)
  : Lemma (perm_eq_bool (compose p (identity n)) p)
  = fwd_agree_implies_perm_eq_bool_from (compose p (identity n)) p 0

instance permutation_mul_monoid (n: nat) : G.mul_monoid (permutation n) = {
  has_one = permutation_has_one n;
  mul_semigroup = permutation_mul_semigroup n;
  left_mul_identity  = (fun p -> identity_left_bool p);
  right_mul_identity = (fun p -> identity_right_bool p);
}

instance permutation_has_inv (n: nat) : G.has_inv (permutation n) = {
  has_one = permutation_has_one n;
  inv = inverse;
}

let inverse_left_bool (#n: nat) (p: permutation n)
  : Lemma (perm_eq_bool (compose (inverse p) p) (identity n))
  = let aux (i: fin n) : Lemma ((compose (inverse p) p).fwd i == (identity n).fwd i) =
      p.bwd_fwd_id i
    in
    Classical.forall_intro aux;
    fwd_agree_implies_perm_eq_bool_from (compose (inverse p) p) (identity n) 0

let inverse_right_bool (#n: nat) (p: permutation n)
  : Lemma (perm_eq_bool (compose p (inverse p)) (identity n))
  = let aux (i: fin n) : Lemma ((compose p (inverse p)).fwd i == (identity n).fwd i) =
      p.fwd_bwd_id i
    in
    Classical.forall_intro aux;
    fwd_agree_implies_perm_eq_bool_from (compose p (inverse p)) (identity n) 0

instance permutation_mul_group (n: nat) : G.mul_group (permutation n) = {
  mul_monoid = permutation_mul_monoid n;
  has_inv = permutation_has_inv n;
  inversion = (fun p -> inverse_right_bool p; inverse_left_bool p);
}







(* ------------------------------------------------------------------------ *)
(*  Parity of a transposition                                                *)
(*                                                                          *)
(*  For a < b, transposition (a,b) has exactly 2*(b-a) - 1 inversions       *)
(*  (an odd number), so parity = false.                                     *)
(* ------------------------------------------------------------------------ *)

(* count_at_left contribution for j <= i is always 0 (the j > i check).
   So count starting at 0 equals count starting at i+1. *)
let rec count_at_left_skip_to
  (#n: nat) (p: permutation n) (i: fin n) (j: nat{j <= n /\ j <= i+1})
  : Lemma (ensures count_at_left p i j == count_at_left p i (i+1))
          (decreases (i + 1 - j))
  = if j = i+1 then ()
    else count_at_left_skip_to p i (j+1)

(* Case A: i < a  ==>  count_at_left swap i (i+1) = 0. *)
#push-options "--z3rlimit 30"
let rec count_at_left_trans_case_A
  (n: nat) (a b: fin n) (i: fin n) (j: nat{j <= n /\ j >= i+1})
  : Lemma (requires a < b /\ i < a)
          (ensures count_at_left (transposition n a b) i j == 0)
          (decreases (n - j))
  = if j >= n then ()
    else count_at_left_trans_case_A n a b i (j+1)
#pop-options

(* Case B (i = a): count contribution starting at j >= a+1 splits into
   - j in (a, b):  contributes 1
   - j = b:        contributes 1
   - j > b:        contributes 0
   Total = (b - a). We prove a tail-form: count starting at j equals:
     if j > b then 0 else (b - j) + 1 = b - j + 1   (for a+1 <= j <= b)
     simplified: (b + 1) - j   for j in [a+1, b]; 0 for j > b.
   *)
let rec count_at_left_trans_case_B
  (n: nat) (a b: fin n) (j: nat{j <= n /\ j >= a+1})
  : Lemma (requires a < b)
          (ensures count_at_left (transposition n a b) a j ==
                   (if j > b then 0 else (b + 1) - j))
          (decreases (n - j))
  = if j >= n then ()
    else count_at_left_trans_case_B n a b (j+1)

(* Case C (a < i < b): count starting at i+1 is exactly 1
   (only j = b contributes). *)
let rec count_at_left_trans_case_C
  (n: nat) (a b: fin n) (i: fin n) (j: nat{j <= n /\ j >= i+1})
  : Lemma (requires a < i /\ i < b)
          (ensures count_at_left (transposition n a b) i j ==
                   (if j > b then 0 else 1))
          (decreases (n - j))
  = if j >= n then ()
    else count_at_left_trans_case_C n a b i (j+1)

(* Case D (i = b): no inversions starting after b. *)
let rec count_at_left_trans_case_D
  (n: nat) (a b: fin n) (j: nat{j <= n /\ j >= b+1})
  : Lemma (requires a < b)
          (ensures count_at_left (transposition n a b) b j == 0)
          (decreases (n - j))
  = if j >= n then ()
    else count_at_left_trans_case_D n a b (j+1)

(* Case E (i > b): same as identity, no inversions. *)
let rec count_at_left_trans_case_E
  (n: nat) (a b: fin n) (i: fin n) (j: nat{j <= n /\ j >= i+1})
  : Lemma (requires a < b /\ i > b)
          (ensures count_at_left (transposition n a b) i j == 0)
          (decreases (n - j))
  = if j >= n then ()
    else count_at_left_trans_case_E n a b i (j+1)

(* For each i, count_at_left swap i 0 according to which case applies. *)
let count_at_left_trans_full
  (n: nat) (a b: fin n) (i: fin n)
  : Lemma (requires a < b)
          (ensures
            count_at_left (transposition n a b) i 0 ==
            (if i < a then 0
             else if i = a then b - a
             else if i < b then 1
             else 0))
  = count_at_left_skip_to (transposition n a b) i 0;
    // After skip, count_at_left ... i 0 == count_at_left ... i (i+1).
    if i < a then count_at_left_trans_case_A n a b i (i+1)
    else if i = a then count_at_left_trans_case_B n a b (a+1)
    else if i < b then count_at_left_trans_case_C n a b i (i+1)
    else if i = b then count_at_left_trans_case_D n a b (b+1)
    else count_at_left_trans_case_E n a b i (i+1)

(* Expected partial-sum function: closed-form value of inversion_count_aux. *)
let rec expected_inv_aux (n: nat) (a b: nat) (i: nat{i <= n})
  : Pure nat (requires a <= b) (ensures fun _ -> True) (decreases (n - i)) =
  if i >= n then 0
  else
    let here : nat = 
      if i < a then 0
      else if i = a then b - a
      else if i < b then 1
      else 0
    in
    here + expected_inv_aux n a b (i + 1)

(* Step 1: inversion_count_aux equals the closed-form partial sum (a < b case). *)
let rec inversion_count_aux_transposition_eq
  (n: nat) (a b: fin n) (i: nat{i <= n})
  : Lemma (requires a < b)
          (ensures inversion_count_aux (transposition n a b) i ==
                   expected_inv_aux n a b i)
          (decreases (n - i))
  = if i >= n then ()
    else (
      count_at_left_trans_full n a b i;
      inversion_count_aux_transposition_eq n a b (i+1)
    )

(* Step 2: compute expected_inv_aux n a b 0 in closed form.
   For i <= a:      sum = 2 * (b - a) - 1
   For a < i <= b:  sum = b - i
   For i > b:       sum = 0    *)
let rec expected_inv_aux_value
  (n: nat) (a b: fin n) (i: nat{i <= n})
  : Lemma (requires a < b)
          (ensures
            expected_inv_aux n a b i ==
            (if i <= a then 2 * (b - a) - 1
             else if i <= b then b - i
             else 0))
          (decreases (n - i))
  = if i >= n then ()
    else expected_inv_aux_value n a b (i+1)

let inversion_count_transposition_a_lt_b (n: nat) (a b: fin n)
  : Lemma (requires a < b)
          (ensures inversion_count (transposition n a b) == 2 * (b - a) - 1)
  = inversion_count_aux_transposition_eq n a b 0;
    expected_inv_aux_value n a b 0

let parity_transposition (n: nat) (a b: fin n)
  : Lemma (ensures parity (transposition n a b) == (a = b))
  = if a = b then (
      // transposition n a a is extensionally identity; its inversion_count is 0.
      // We don't yet have that as a closed-form lemma; prove inline using parity_identity-like
      // reasoning. count_at_left for transposition n a a at every i is 0 because
      // swap.fwd = identity, so the same proof as count_at_left_identity applies.
      let rec count_zero (i: fin n) (j: nat{j <= n})
        : Lemma (ensures count_at_left (transposition n a a) i j == 0)
                (decreases (n - j))
        = if j >= n then () else count_zero i (j+1)
      in
      let rec inv_aux_zero (k: nat{k <= n})
        : Lemma (ensures inversion_count_aux (transposition n a a) k == 0)
                (decreases (n - k))
        = if k >= n then () else (
            (if k < n then count_zero k 0);
            inv_aux_zero (k+1)
          )
      in
      inv_aux_zero 0
    )
    else if a < b then (
      inversion_count_transposition_a_lt_b n a b
      // 2*(b-a) - 1 is odd, so parity = false
    )
    else (
      // b < a; symmetry: transposition n a b extensionally equals transposition n b a.
      // Reduce to a < b case by noting count_at_left is the same in both directions.
      // Compute directly via the case lemmas with roles swapped.
      inversion_count_transposition_a_lt_b n b a;
      // Need: inversion_count (transposition n a b) == inversion_count (transposition n b a).
      // transposition n a b and transposition n b a are extensionally equal.
      let rec same_count_at_left (i: fin n) (j: nat{j <= n})
        : Lemma (ensures count_at_left (transposition n a b) i j ==
                         count_at_left (transposition n b a) i j)
                (decreases (n - j))
        = if j >= n then () else same_count_at_left i (j+1)
      in
      let rec same_inv_aux (k: nat{k <= n})
        : Lemma (ensures inversion_count_aux (transposition n a b) k ==
                         inversion_count_aux (transposition n b a) k)
                (decreases (n - k))
        = if k >= n then () else (
            (if k < n then same_count_at_left k 0);
            same_inv_aux (k+1)
          )
      in
      same_inv_aux 0
    )

(* ============================================================ *)
(* Sign homomorphism: parity (compose p q) = (parity p = parity q)         *)
(* ============================================================ *)

(* Right multiplication by an adjacent transposition. *)
let right_swap (#n: nat) (p: permutation n) (i: nat{i + 1 < n}) : permutation n =
  compose p (transposition n i (i+1))

let right_swap_fwd_at_k (#n: nat) (p: permutation n) (i: nat{i+1 < n}) (k: fin n)
  : Lemma (ensures
            (right_swap p i).fwd k ==
            (if k = i then p.fwd (i+1)
             else if k = i+1 then p.fwd i
             else p.fwd k))
  = ()

(* For k < i: count_at_left rs k j == count_at_left p k j.
   Valid for j <= i (we'll skip past i and i+1 together) or j >= i+2.  *)
let rec count_at_left_rs_below
  (#n: nat) (p: permutation n) (i: nat{i+1 < n}) (k: fin n) (j: nat{j <= n})
  : Lemma (requires k < i /\ (j <= i \/ j >= i+2))
          (ensures count_at_left (right_swap p i) k j == count_at_left p k j)
          (decreases (n - j))
  = if j >= n then ()
    else if j = i then begin
      assert (count_at_left (right_swap p i) k i ==
              (if i > k && (right_swap p i).fwd k > (right_swap p i).fwd i then 1 else 0) +
              count_at_left (right_swap p i) k (i+1));
      assert (count_at_left (right_swap p i) k (i+1) ==
              (if (i+1) > k && (right_swap p i).fwd k > (right_swap p i).fwd (i+1) then 1 else 0) +
              count_at_left (right_swap p i) k (i+2));
      assert (count_at_left p k i ==
              (if i > k && p.fwd k > p.fwd i then 1 else 0) +
              count_at_left p k (i+1));
      assert (count_at_left p k (i+1) ==
              (if (i+1) > k && p.fwd k > p.fwd (i+1) then 1 else 0) +
              count_at_left p k (i+2));
      count_at_left_rs_below p i k (i+2)
    end
    else count_at_left_rs_below p i k (j+1)

(* For k > i+1: count_at_left rs k 0 == count_at_left p k 0. *)
let rec count_at_left_rs_above
  (#n: nat) (p: permutation n) (i: nat{i+1 < n}) (k: fin n) (j: nat{j <= n})
  : Lemma (requires k > i+1)
          (ensures count_at_left (right_swap p i) k j == count_at_left p k j)
          (decreases (n - j))
  = if j >= n then ()
    else count_at_left_rs_above p i k (j+1)

(* k = i+1: count_at_left rs (i+1) (i+2) == count_at_left p i (i+2). *)
let rec count_at_left_rs_at_ip1_tail
  (#n: nat) (p: permutation n) (i: nat{i+1 < n}) (j: nat{j <= n})
  : Lemma (requires j >= i+2)
          (ensures count_at_left (right_swap p i) (i+1) j == count_at_left p i j)
          (decreases (n - j))
  = if j >= n then ()
    else count_at_left_rs_at_ip1_tail p i (j+1)

(* k = i: count_at_left rs i (i+2) == count_at_left p (i+1) (i+2). *)
let rec count_at_left_rs_at_i_tail
  (#n: nat) (p: permutation n) (i: nat{i+1 < n}) (j: nat{j <= n})
  : Lemma (requires j >= i+2)
          (ensures count_at_left (right_swap p i) i j == count_at_left p (i+1) j)
          (decreases (n - j))
  = if j >= n then ()
    else count_at_left_rs_at_i_tail p i (j+1)

(* count_at_left p k 0 == count_at_left p k (k+1)  (already have skip_to). *)
(* count_at_left p (i+1) 0 == count_at_left p (i+1) (i+2). *)
let count_at_left_p_at_ip1_zero (#n: nat) (p: permutation n) (i: nat{i+1 < n})
  : Lemma (count_at_left p (i+1) 0 == count_at_left p (i+1) (i+2))
  = count_at_left_skip_to p (i+1) 0

(* count_at_left p i 0 == [p(i) > p(i+1)] + count_at_left p i (i+2). *)
let count_at_left_p_at_i_zero (#n: nat) (p: permutation n) (i: nat{i+1 < n})
  : Lemma (count_at_left p i 0 ==
           (if p.fwd i > p.fwd (i+1) then 1 else 0) + count_at_left p i (i+2))
  = count_at_left_skip_to p i 0;
    // count_at_left p i (i+1) = here(i+1) + count_at_left p i (i+2).
    assert (count_at_left p i (i+1) ==
            (if (i+1) > i && p.fwd i > p.fwd (i+1) then 1 else 0) +
            count_at_left p i (i+2))

(* count_at_left rs i 0 == [p(i+1) > p(i)] + count_at_left p (i+1) (i+2). *)
let count_at_left_rs_at_i_zero (#n: nat) (p: permutation n) (i: nat{i+1 < n})
  : Lemma (count_at_left (right_swap p i) i 0 ==
           (if p.fwd (i+1) > p.fwd i then 1 else 0) + count_at_left p (i+1) (i+2))
  = count_at_left_skip_to (right_swap p i) i 0;
    assert (count_at_left (right_swap p i) i (i+1) ==
            (if (i+1) > i && (right_swap p i).fwd i > (right_swap p i).fwd (i+1) then 1 else 0) +
            count_at_left (right_swap p i) i (i+2));
    count_at_left_rs_at_i_tail p i (i+2)

(* count_at_left rs (i+1) 0 == count_at_left p i (i+2). *)
let count_at_left_rs_at_ip1_zero (#n: nat) (p: permutation n) (i: nat{i+1 < n})
  : Lemma (count_at_left (right_swap p i) (i+1) 0 == count_at_left p i (i+2))
  = count_at_left_skip_to (right_swap p i) (i+1) 0;
    count_at_left_rs_at_ip1_tail p i (i+2)

(* inversion_count_aux agrees on the suffix from i+2. *)
let rec inv_aux_rs_suffix
  (#n: nat) (p: permutation n) (i: nat{i+1 < n}) (k: nat{k <= n})
  : Lemma (requires k >= i+2)
          (ensures inversion_count_aux (right_swap p i) k == inversion_count_aux p k)
          (decreases (n - k))
  = if k >= n then ()
    else begin
      count_at_left_rs_above p i k 0;
      inv_aux_rs_suffix p i (k+1)
    end

(* The key per-pair flip at k = i.
   Both p.fwd i and p.fwd (i+1) are in fin n and distinct (p is a bijection), so
   exactly one of [p.fwd i > p.fwd (i+1)] and [p.fwd (i+1) > p.fwd i] is true.  *)
let fwd_distinct (#n: nat) (p: permutation n) (i: nat{i+1 < n})
  : Lemma (p.fwd i =!= p.fwd (i+1))
  = let h () : Lemma (requires p.fwd i == p.fwd (i+1)) (ensures False) =
      p.bwd_fwd_id i;
      p.bwd_fwd_id (i+1)
    in
    Classical.move_requires h ()

(* inversion_count_aux rs i + [p(i)>p(i+1)] == inversion_count_aux p i + [p(i+1)>p(i)] *)
let inv_aux_rs_at_i (#n: nat) (p: permutation n) (i: nat{i+1 < n})
  : Lemma (inversion_count_aux (right_swap p i) i +
           (if p.fwd i > p.fwd (i+1) then 1 else 0) ==
           inversion_count_aux p i +
           (if p.fwd (i+1) > p.fwd i then 1 else 0))
  = // Unfold inv_aux X i = count_at_left X i 0 + count_at_left X (i+1) 0 + inv_aux X (i+2)
    assert (inversion_count_aux (right_swap p i) i ==
            count_at_left (right_swap p i) i 0 + inversion_count_aux (right_swap p i) (i+1));
    assert (inversion_count_aux (right_swap p i) (i+1) ==
            count_at_left (right_swap p i) (i+1) 0 + inversion_count_aux (right_swap p i) (i+2));
    assert (inversion_count_aux p i ==
            count_at_left p i 0 + inversion_count_aux p (i+1));
    assert (inversion_count_aux p (i+1) ==
            count_at_left p (i+1) 0 + inversion_count_aux p (i+2));
    inv_aux_rs_suffix p i (i+2);
    count_at_left_rs_at_i_zero p i;
    count_at_left_rs_at_ip1_zero p i;
    count_at_left_p_at_i_zero p i;
    count_at_left_p_at_ip1_zero p i;
    fwd_distinct p i

(* Extend the +/- balance down to k=0.  Statement holds for k <= i (NOT k <= i+1):
   at k = i, we unfold inv_aux to include BOTH count_at_left at i and i+1, where
   the per-pair flip happens.  *)
let rec inv_aux_rs_down
  (#n: nat) (p: permutation n) (i: nat{i+1 < n}) (k: nat{k <= i})
  : Lemma (ensures
            inversion_count_aux (right_swap p i) k +
            (if p.fwd i > p.fwd (i+1) then 1 else 0) ==
            inversion_count_aux p k +
            (if p.fwd (i+1) > p.fwd i then 1 else 0))
          (decreases (i - k))
  = if k = i then inv_aux_rs_at_i p i
    else begin
      inv_aux_rs_down p i (k+1);
      count_at_left_rs_below p i k 0;
      assert (inversion_count_aux (right_swap p i) k ==
              count_at_left (right_swap p i) k 0 + inversion_count_aux (right_swap p i) (k+1));
      assert (inversion_count_aux p k ==
              count_at_left p k 0 + inversion_count_aux p (k+1))
    end

let parity_right_swap (#n: nat) (p: permutation n) (i: nat{i+1 < n})
  : Lemma (parity (right_swap p i) == not (parity p))
  = inv_aux_rs_down p i 0;
    fwd_distinct p i
    // inv(rs) + [p(i)>p(i+1)] == inv(p) + [p(i+1)>p(i)]; exactly one of the bracket
    // terms is 1, so inv(rs) and inv(p) differ by 1; parities differ.

(* Auxiliary: if count_at_left q k j = 0 for j' in [j, n), then for all
   k < j' < n in that range, q.fwd k <= q.fwd j'. *)
let rec count_at_left_zero_local
  (#n: nat) (q: permutation n) (k: fin n) (j: nat{j <= n}) (j': nat)
  : Lemma (requires count_at_left q k j == 0 /\ j <= j' /\ j' < n /\ j' > k)
          (ensures q.fwd k <= q.fwd j')
          (decreases (j' - j))
  = if j = j' then ()
    else count_at_left_zero_local q k (j+1) j'

(* Per-index summary: count_at_left q k 0 == 0 ==> q.fwd k <= q.fwd j' for k < j' < n. *)
let count_at_left_zero_imp (#n: nat) (q: permutation n) (k: fin n) (j': nat)
  : Lemma (requires count_at_left q k 0 == 0 /\ j' < n /\ j' > k)
          (ensures q.fwd k <= q.fwd j')
  = count_at_left_zero_local q k 0 j'

(* If inversion_count_aux q k = 0, then count_at_left q k' 0 = 0 for all k' >= k. *)
let rec inv_aux_zero_per_index
  (#n: nat) (q: permutation n) (k: nat{k <= n}) (k': nat)
  : Lemma (requires inversion_count_aux q k == 0 /\ k <= k' /\ k' < n)
          (ensures count_at_left q k' 0 == 0)
          (decreases (k' - k))
  = if k = k' then ()
    else inv_aux_zero_per_index q (k+1) k'

(* Hence: inv q = 0 implies q.fwd is monotone non-decreasing. *)
let inv_zero_monotone (#n: nat) (q: permutation n) (k1: fin n) (k2: fin n)
  : Lemma (requires inversion_count q == 0 /\ k1 <= k2)
          (ensures q.fwd k1 <= q.fwd k2)
  = if k1 = k2 then ()
    else begin
      inv_aux_zero_per_index q 0 k1;
      count_at_left_zero_imp q k1 k2
    end

(* Monotone permutation is identity. *)
let rec monotone_perm_is_identity_fwd
  (#n: nat) (q: permutation n) (k: fin n)
  : Lemma (requires forall (i j: nat). i < n /\ j < n /\ i <= j ==> q.fwd i <= q.fwd j)
          (ensures q.fwd k == k)
          (decreases k)
  = q.fwd_bwd_id k;
    let j = q.bwd k in
    // q.fwd j == k
    (if j < k then begin
       monotone_perm_is_identity_fwd q j
       // IH: q.fwd j == j. Combined with q.fwd j == k, j == k, contradicting j < k.
     end);
    // Hence j >= k. Monotone: q.fwd k <= q.fwd j == k.
    (if k > 0 then begin
       monotone_perm_is_identity_fwd q (k - 1);
       // IH: q.fwd (k-1) == k-1. Monotone: q.fwd (k-1) <= q.fwd k, so k-1 <= q.fwd k.
       // If q.fwd k == k-1, then q.fwd k == q.fwd (k-1), injective => k == k-1: contradiction.
       q.bwd_fwd_id k;
       q.bwd_fwd_id (k - 1)
     end)

(* inv q = 0 implies q is extensionally the identity. *)
let inv_zero_implies_identity_fwd
  (#n: nat) (q: permutation n) (k: fin n)
  : Lemma (requires inversion_count q == 0) (ensures q.fwd k == k)
  = Classical.forall_intro_2 (Classical.move_requires_2 (inv_zero_monotone q));
    monotone_perm_is_identity_fwd q k

(* Parity is invariant under extensional equality. *)
let rec count_at_left_perm_eq_invariant
  (#n: nat) (p1 p2: permutation n) (k: fin n) (j: nat{j <= n})
  : Lemma (requires forall (i: fin n). p1.fwd i == p2.fwd i)
          (ensures count_at_left p1 k j == count_at_left p2 k j)
          (decreases (n - j))
  = if j >= n then ()
    else count_at_left_perm_eq_invariant p1 p2 k (j+1)

let rec inv_aux_perm_eq_invariant
  (#n: nat) (p1 p2: permutation n) (k: nat{k <= n})
  : Lemma (requires forall (i: fin n). p1.fwd i == p2.fwd i)
          (ensures inversion_count_aux p1 k == inversion_count_aux p2 k)
          (decreases (n - k))
  = if k >= n then ()
    else begin
      count_at_left_perm_eq_invariant p1 p2 k 0;
      inv_aux_perm_eq_invariant p1 p2 (k+1)
    end

let parity_perm_eq_invariant (#n: nat) (p1 p2: permutation n)
  : Lemma (requires forall (i: fin n). p1.fwd i == p2.fwd i)
          (ensures parity p1 == parity p2)
  = inv_aux_perm_eq_invariant p1 p2 0

(* Look for the smallest adjacent descent.  *)
let rec find_descent (#n: nat) (q: permutation n) (i: nat{i <= n})
  : Tot (option (j: nat{j + 1 < n /\ q.fwd j > q.fwd (j+1)}))
        (decreases (n - i))
  = if i + 1 >= n then None
    else if q.fwd i > q.fwd (i+1) then Some i
    else find_descent q (i+1)

(* No descent search returns None ⟹ monotone non-decreasing. *)
let rec find_descent_none_monotone
  (#n: nat) (q: permutation n) (i: nat{i <= n}) (k1: nat) (k2: nat)
  : Lemma (requires None? (find_descent q i) /\ i <= k1 /\ k1 <= k2 /\ k2 < n)
          (ensures q.fwd k1 <= q.fwd k2)
          (decreases (k2 - k1))
  = if k1 = k2 then ()
    else if k1 + 1 = k2 then begin
      // need q.fwd k1 <= q.fwd (k1+1). From find_descent q i = None and i <= k1, scrolling.
      let rec at_k (j: nat{j <= n}) : Lemma (requires None? (find_descent q j) /\ j <= k1)
                                            (ensures q.fwd k1 <= q.fwd (k1+1))
                                            (decreases (k1 - j))
        = if j = k1 then ()
          else at_k (j+1)
      in at_k i
    end
    else begin
      find_descent_none_monotone q i k1 (k2-1);
      find_descent_none_monotone q i (k2-1) k2
    end

(* find_descent returns None ==> inversion_count = 0. *)
let find_descent_none_implies_inv_zero (#n: nat) (q: permutation n)
  : Lemma (requires None? (find_descent q 0))
          (ensures inversion_count q == 0)
  = let aux_mono (k1 k2: fin n) : Lemma (k1 <= k2 ==> q.fwd k1 <= q.fwd k2) =
      let h () : Lemma (requires k1 <= k2) (ensures q.fwd k1 <= q.fwd k2) =
        find_descent_none_monotone q 0 k1 k2
      in Classical.move_requires h ()
    in
    Classical.forall_intro_2 aux_mono;
    let aux_id (k: fin n) : Lemma (q.fwd k == k) = monotone_perm_is_identity_fwd q k in
    Classical.forall_intro aux_id;
    inv_aux_perm_eq_invariant q (identity n) 0;
    inversion_count_identity n

(* When q has adjacent descent at i, inv (right_swap q i) = inv q - 1. *)
let inv_right_swap_at_descent
  (#n: nat) (q: permutation n) (i: nat{i+1 < n})
  : Lemma (requires q.fwd i > q.fwd (i+1))
          (ensures inversion_count (right_swap q i) + 1 == inversion_count q)
  = inv_aux_rs_down q i 0;
    fwd_distinct q i

(* compose p (right_swap q i) is extensionally right_swap (compose p q) i *)
let compose_with_right_swap_eq
  (#n: nat) (p q: permutation n) (i: nat{i+1 < n}) (k: fin n)
  : Lemma ((compose p (right_swap q i)).fwd k == (right_swap (compose p q) i).fwd k)
  = ()

let parity_compose_right_swap
  (#n: nat) (p q: permutation n) (i: nat{i+1 < n})
  : Lemma (parity (compose p (right_swap q i)) == not (parity (compose p q)))
  = Classical.forall_intro (compose_with_right_swap_eq p q i);
    parity_perm_eq_invariant (compose p (right_swap q i)) (right_swap (compose p q) i);
    parity_right_swap (compose p q) i

(* Sign homomorphism: parity is a group homomorphism into the sign group. *)
let rec sign_homomorphism
  (#n: nat) (p q: permutation n)
  : Lemma (ensures parity (compose p q) == (parity p = parity q))
          (decreases (inversion_count q))
  = match find_descent q 0 with
    | None ->
        find_descent_none_implies_inv_zero q;
        // Now inversion_count q == 0, and q is extensionally identity.
        let aux_q (k: fin n) : Lemma (q.fwd k == k) = inv_zero_implies_identity_fwd q k in
        Classical.forall_intro aux_q;
        // compose p q is extensionally p
        let aux_cpq (k: fin n) : Lemma ((compose p q).fwd k == p.fwd k) = () in
        Classical.forall_intro aux_cpq;
        parity_perm_eq_invariant (compose p q) p
    | Some i ->
        inv_right_swap_at_descent q i;
        parity_right_swap q i;
        let q' = right_swap q i in
        sign_homomorphism p q';
        parity_compose_right_swap p q i
