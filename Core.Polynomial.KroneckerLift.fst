module Core.Polynomial.KroneckerLift

(* ================================================================ *)
(*  §D PACKAGED LIFT-RECOVERY.                                       *)
(*                                                                   *)
(*  Composes the Kronecker whole-factor height bound                 *)
(*    poly_height g <= kbound_rhs bigF int_cs                        *)
(*  with the centered-lift exact recovery                            *)
(*    2*poly_height g < pk ==> poly_centered pk (poly_to_fp pk g) = g *)
(*  into the directly-usable form for end-to-end ℚ-factorization:    *)
(*  choosing pk > 2*(kbound_rhs ..) recovers g exactly from its       *)
(*  mod-pk Hensel reduction.                                         *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Roots
open Core.Polynomial.Eval
open Core.Polynomial.Height
open Core.Polynomial.KroneckerBound
open Core.Polynomial.KroneckerHeightBound
open Core.Modular.ResidueRing.CenteredPoly
open Core.Modular.ResidueRing.CenteredPolyExact

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

let kronecker_lift_recovers
  (g k bigF: polynomial int) (int_cs: list int) (pk: int)
  : Lemma (requires
        bigF = g * k /\
        all_distinct int_cs /\
        deg g < L.length int_cs /\
        (forall (j:nat). j < L.length int_cs ==>
            poly_eval bigF (L.index int_cs j) <> 0) /\
        pk > 1 /\ pk > 2 * (kbound_rhs bigF int_cs))
      (ensures poly_centered pk (poly_to_fp pk g) = g)
  = kronecker_height_bound g k bigF int_cs;   (* poly_height g <= kbound_rhs bigF int_cs *)
    (* 2*poly_height g <= 2*kbound_rhs < pk  (monotone *2, then transitivity) *)
    poly_centered_recovers_small pk g
