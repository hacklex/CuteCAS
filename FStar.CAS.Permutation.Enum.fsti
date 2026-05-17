module FStar.CAS.Permutation.Enum

(*
   Public interface for enumeration of all permutations of `fin n`.

   The implementation in `FStar.CAS.Permutation.Enum.fst` constructs the
   list `all_permutations n` of length `n!` covering every permutation
   class exactly once (modulo `perm_eq`).
*)

open FStar.CAS.Permutation

module L = FStar.List.Tot

(* -------------------------------------------------------------------- *)
(*  The enumeration.                                                    *)
(* -------------------------------------------------------------------- *)

val all_permutations (n: nat) : Tot (list (permutation n)) (decreases n)

val all_permutations_zero (_:unit)
  : Lemma (all_permutations 0 == [identity 0])

(* -------------------------------------------------------------------- *)
(*  Membership-by-perm_eq predicate.                                    *)
(* -------------------------------------------------------------------- *)

unfold let permutation_in_list
  (#n: nat) (p: permutation n) (xs: list (permutation n)) : prop
  = exists (q: permutation n). L.memP q xs /\ perm_eq p q

(* -------------------------------------------------------------------- *)
(*  Completeness: every permutation appears in the enumeration.         *)
(* -------------------------------------------------------------------- *)

val all_permutations_complete (n: nat) (p: permutation n)
  : Lemma (ensures permutation_in_list p (all_permutations n))
          (decreases n)

(* -------------------------------------------------------------------- *)
(*  Pairwise-distinct (mod perm_eq) predicate.                          *)
(* -------------------------------------------------------------------- *)

let rec all_distinct (#n: nat) (xs: list (permutation n)) : prop
  = match xs with
    | [] -> True
    | h :: tl ->
        (forall (p: permutation n). L.memP p tl ==> ~(perm_eq h p)) /\ all_distinct tl

(* -------------------------------------------------------------------- *)
(*  No-duplicates: the enumeration has no two perm_eq-equivalent items. *)
(* -------------------------------------------------------------------- *)

val all_permutations_no_dup (n: nat)
  : Lemma (ensures all_distinct (all_permutations n))
          (decreases n)
