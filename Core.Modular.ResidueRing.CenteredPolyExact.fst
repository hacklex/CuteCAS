module Core.Modular.ResidueRing.CenteredPolyExact

(* ================================================================ *)
(*  §D assembly (#31) — POLYNOMIAL CENTERED-LIFT EXACT RECOVERY.     *)
(*                                                                   *)
(*  A ℤ[X] polynomial whose ∞-norm (height) is strictly below m/2    *)
(*  is recovered EXACTLY by reducing mod m (`poly_to_fp`) then        *)
(*  centered-lifting (`poly_centered`).                              *)
(*                                                                   *)
(*  This is the polynomial version of `centered_recovers_small`:     *)
(*  once the true integer factor's height is bounded by the          *)
(*  Kronecker `B` and `m = pᵏ > 2B` is chosen, that factor is         *)
(*  recovered exactly from its mod-pᵏ Hensel reduction.              *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module H = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Int
open Core.Polynomial
open Core.Modular.ResidueRing
open Core.Modular.ResidueRing.Centered
open Core.Modular.ResidueRing.CenteredExact
open Core.Modular.ResidueRing.CenteredPoly
open Core.Polynomial.Height

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* per-coefficient exact recovery. *)
private let poly_centered_recovers_small_coeff (m:int{m > 1})
  (g: polynomial int #int_cr) (i:nat)
  : Lemma (requires 2 * poly_height g < m)
          (ensures coeff #int #int_cr (poly_centered m (poly_to_fp m g)) i
                   = coeff #int #int_cr g i)
  = H.elim_equatable_laws int ();
    (* coeff (poly_centered (poly_to_fp g)) i == centered m (coeff (poly_to_fp g) i) *)
    poly_centered_coeff m (poly_to_fp m g) i;
    (* coeff (poly_to_fp g) i == to_fp m (coeff g i) *)
    poly_to_fp_coeff m g i;
    (* iabs (coeff g i) <= poly_height g, and 2*poly_height g < m,
       so 2*(coeff g i) < m /\ -m < 2*(coeff g i)   (iabs def). *)
    coeff_abs_le_height g i;
    (* centered m (to_fp m (coeff g i)) == coeff g i *)
    centered_recovers_small m (coeff g i)

(* poly_centered (poly_to_fp g) = g  in ℤ[X]  when  2*height g < m. *)
let poly_centered_recovers_small (m:int{m > 1}) (g: polynomial int #int_cr)
  : Lemma (requires 2 * poly_height g < m)
          (ensures (poly_centered m (poly_to_fp m g)) = g)
  = let lhs = poly_centered m (poly_to_fp m g) in
    let aux (i:nat)
      : Lemma (coeff #int #int_cr lhs i = coeff #int #int_cr g i)
      = poly_centered_recovers_small_coeff m g i in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs g
