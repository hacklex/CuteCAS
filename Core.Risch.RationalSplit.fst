module Core.Risch.RationalSplit

(* ================================================================ *)
(*  §F — rational-integrator soundness REDUCED to the proper part.   *)
(*                                                                   *)
(*  Combining the polynomial-part soundness (`poly_part_correct`:    *)
(*  D(∫quot)=quot) with the Euclidean split (`euclid_fraction_       *)
(*  identity`: p/q = quot/1 + rem/q):  IF the proper fraction `proper`*)
(*  integrates `rem/q`  (`D(proper) = rem/q` — the Hermite + LRT      *)
(*  part), THEN                                                       *)
(*     D(∫quot/1)  +  D(proper)  =  p/q.                              *)
(*                                                                   *)
(*  This isolates the ONLY remaining obligation for full rational    *)
(*  soundness to the proper-fraction part (Hermite poly identity +   *)
(*  the §A LRT log-derivative identity).                             *)
(*                                                                   *)
(*  NO admit / assume / sorry in the final version.                  *)
(* ================================================================ *)

module H  = Core.Algebra.Helpers
module PA = Core.Risch.PolyAntideriv

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Derivative
open Core.Fractions
open Core.Fractions.Derivative
open Core.Risch.Hermite
open Core.Risch.RationalSound
open Core.Risch.RationalEuclid
open Core.Risch.RTSoundness

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

let rational_split_sound (#t:Type) {| f: field t |}
  (p q quot rem: polynomial t)
  (proper: rational_function f)
  : Lemma (requires char_zero f /\ is_nonzero #_ q /\
                    p = (quot * q) + rem /\
                    rational_deriv proper = Fraction rem q)
          (ensures
            (fraction_add
               (rational_deriv (poly_to_rational (PA.antideriv quot)))
               (rational_deriv proper))
            = (Fraction p q))
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    let a   : fraction id_p =
      rational_deriv (poly_to_rational (PA.antideriv quot)) in
    let b   : fraction id_p = rational_deriv proper in
    let pq  : fraction id_p = poly_to_rational quot in
    let rq  : fraction id_p = Fraction rem q in
    let rhs : fraction id_p = fraction_add pq rq in
    (* (1)  a = poly_to_rational quot. *)
    poly_part_correct quot;
    (* (2)  b = Fraction rem q   (hypothesis). *)
    (* (3)  Fraction p q = fraction_add (poly_to_rational quot) (Fraction rem q). *)
    euclid_fraction_identity p q quot rem;
    (* LHS congruence:  fraction_add a b = fraction_add pq rq. *)
    frac_add_cong   a pq b;          (* a+b = pq+b *)
    frac_add_cong_r pq b rq           (* pq+b = pq+rq *)
