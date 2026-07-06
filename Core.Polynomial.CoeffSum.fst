module Core.Polynomial.CoeffSum

(* ================================================================ *)
(*  Coefficient extraction commutes with finite polynomial sums.    *)
(*                                                                   *)
(*    coeff i (sum_range f lo hi)                                    *)
(*        = sum_range (fun j -> coeff i (f j)) lo hi                 *)
(*                                                                   *)
(*  Fixing the index i, `coeff (.) i : polynomial t -> t` is an      *)
(*  add_comm_group homomorphism; this is its action on a finite sum. *)
(*  Structural half of the §D Kronecker coefficient bound.           *)
(*                                                                   *)
(*  Mirrors `eval_over_sum` in Core.Polynomial.LagrangeInterp, with  *)
(*  `coeff (.) i` in place of `poly_eval (.) c`, `poly_add_coeff` in *)
(*  place of `eval_add`, and `coeff i poly_zero = zero` in place of  *)
(*  `eval_zero`.                                                     *)
(* ================================================================ *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module FS = Core.FinSum

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial

open Core.FinSum

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------- *)
(*  The t-level summand obtained by extracting coefficient i from    *)
(*  each polynomial summand. Named to avoid anonymous lambdas in the *)
(*  lemma signature.                                                 *)
(* ---------------------------------------------------------------- *)
let coeff_at_term (#t:Type) {| cr: commutative_ring t |}
                  (i: nat) (ff: nat -> polynomial t) (j: nat)
  : t
  = coeff (ff j) i

(* Coefficient extraction respects polynomial equality.
   Mirror of `eval_congruence`: the polynomial equatable `=` is defeq to
   `poly_eq`, so the `=` produced by `sum_range_unfold_right` in `pacg cr`
   supplies the `poly_eq` hypothesis `poly_eq_means_equal_coeffs` needs. *)
let coeff_congruence (#t:Type) {| cr: commutative_ring t |}
                     (p q: polynomial t) (i: nat)
  : Lemma (requires (p = q)) (ensures coeff p i = coeff q i)
  = poly_eq_means_equal_coeffs p q i

(* ---------------------------------------------------------------- *)
(*  Coeff-over-finite-sum homomorphism.                              *)
(* ---------------------------------------------------------------- *)
let rec coeff_sum_range (#t:Type) {| cr: commutative_ring t |}
  (ff: nat -> polynomial t) (lo hi: nat) (i: nat)
  : Lemma (ensures
      coeff (sum_range ff lo hi) i
        = sum_range (coeff_at_term i ff) lo hi)
    (decreases (hi - lo))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if lo >= hi then begin
      (* both sums empty *)
      sum_range_empty ff lo hi;
      (* coeff (sum) i = coeff poly_zero i = zero  (refinement of coeff) *)
      coeff_congruence (sum_range ff lo hi)
                       (poly_zero #t) i;
      (* coeff poly_zero i == zero  holds definitionally via coeff's refinement *)
      sum_range_empty (coeff_at_term i ff) lo hi
    end else begin
      let hp = hi - 1 in
      (* unfold the polynomial sum on the right end *)
      sum_range_unfold_right ff lo hi;
      (* sum_range ff lo hi == sum_range ff lo hp + ff hp   (poly_add) *)
      coeff_congruence
        (sum_range ff lo hi)
        (sum_range ff lo hp + ff hp) i;
      (* poly_add_coeff splits the poly_add: coeff (s + ff hp) i = coeff s i + coeff (ff hp) i *)
      poly_add_coeff (sum_range ff lo hp) (ff hp) i;
      (* IH on [lo, hp) *)
      coeff_sum_range ff lo hp i;
      (* combine: coeff (sum ff lo hp) i = sum_t (coeff_at_term) lo hp *)
      add_congruence
        (coeff (sum_range ff lo hp) i)
        (coeff (ff hp) i)
        (sum_range (coeff_at_term i ff) lo hp)
        (coeff_at_term i ff hp);
      (* t-level sum unfolds the same way *)
      sum_range_unfold_right (coeff_at_term i ff) lo hi
    end
