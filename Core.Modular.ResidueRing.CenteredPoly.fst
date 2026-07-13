module Core.Modular.ResidueRing.CenteredPoly

(* ================================================================ *)
(*  §D — the centered lift on POLYNOMIALS:                           *)
(*    poly_centered : (ℤ/m)[X] → ℤ[X]   (coefficient-wise `centered`) *)
(*    poly_to_fp    : ℤ[X] → (ℤ/m)[X]   (coefficient-wise `to_fp`)    *)
(*  with round-trip  poly_to_fp (poly_centered g) = g  in (ℤ/m)[X].   *)
(*                                                                   *)
(*  This lifts a mod-pᵏ Hensel factor to a candidate ℤ-factor; the    *)
(*  round-trip certifies it reduces back to the Hensel factor.        *)
(*                                                                   *)
(*  NO admit / assume / sorry in the final version.                  *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Int
open Core.Modular.ResidueRing
open Core.Modular.ResidueRing.Centered
open Core.Polynomial
open Core.Polynomial.Coeff

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* coefficient-wise centered lift (ℤ/m)[X] → ℤ[X]. *)
let poly_centered (m:int{m > 1})
  (g: polynomial (zmod m))
  : polynomial int #int_cr
  = trim #int #int_cr (L.map (centered m) g)

(* coefficient-wise reduction ℤ[X] → (ℤ/m)[X]. *)
let poly_to_fp (m:int{m > 1})
  (gg: polynomial int #int_cr)
  : polynomial (zmod m)
  = trim #(zmod m) (L.map (to_fp m) gg)

(* index of a mapped list:  index (map g l) i = g (index l i).
   PUBLIC (generic list utility; reused by Core.Modular.FpZmodBridge). *)
let rec index_map_lemma (#a:Type) (#b:Type) (g: a -> b) (l: list a) (i:nat{i < L.length l})
  : Lemma (ensures (L.map_lemma g l; L.index (L.map g l) i == g (L.index l i)))
          (decreases i)
  = L.map_lemma g l;
    if i = 0 then ()
    else index_map_lemma g (L.tl l) (i - 1)

(* tiny zero helpers. *)
private let centered_zero (m:int{m > 1})
  : Lemma (centered m (zmod_zero m) == 0)
  = ()

private let to_fp_zero (m:int{m > 1})
  : Lemma (to_fp m 0 == zmod_zero m)
  = FStar.Math.Lemmas.small_mod 0 m

(* coeff characterisations. *)
let poly_centered_coeff (m:int{m > 1})
  (g: polynomial (zmod m)) (i:int)
  : Lemma (coeff #int #int_cr (poly_centered m g) i
           == centered m (coeff #(zmod m) g i))
  = let cmap = centered m in
    let mapped : list int = L.map cmap g in
    L.map_lemma cmap g;                          (* length (map cmap g) == length g *)
    H.elim_equatable_laws int ();
    if i < 0 then begin
      (* lhs = coeff (trim mapped) i = zero (i<0) = 0;
         rhs = centered m (coeff g i) = centered m (zmod_zero m) = 0. *)
      centered_zero m
    end
    else begin
      let i : nat = i in
      coeff_trim mapped i;
      if i < L.length g then begin
        (* lhs = index mapped i = centered m (index g i) = centered m (coeff g i) *)
        index_map_lemma cmap g i
      end
      else begin
        (* lhs = zero = 0; rhs = centered m (coeff g i) = centered m (zmod_zero m) = 0 *)
        centered_zero m
      end
    end

let poly_to_fp_coeff (m:int{m > 1})
  (gg: polynomial int #int_cr) (i:int)
  : Lemma (coeff #(zmod m) (poly_to_fp m gg) i
           == to_fp m (coeff #int #int_cr gg i))
  = let fmap = to_fp m in
    let mapped : list (zmod m) = L.map fmap gg in
    L.map_lemma fmap gg;                         (* length (map fmap gg) == length gg *)
    H.elim_equatable_laws (zmod m) ();
    if i < 0 then begin
      (* lhs = coeff (trim mapped) i = zmod_zero m (i<0);
         rhs = to_fp m (coeff gg i) = to_fp m 0 = zmod_zero m. *)
      to_fp_zero m
    end
    else begin
      let i : nat = i in
      coeff_trim #(zmod m) mapped i;
      if i < L.length gg then begin
        (* lhs = index mapped i = to_fp m (index gg i) = to_fp m (coeff gg i) *)
        index_map_lemma fmap gg i
      end
      else begin
        (* lhs = zmod_zero m; rhs = to_fp m (coeff gg i) = to_fp m 0 = zmod_zero m *)
        to_fp_zero m
      end
    end

(* per-coefficient round-trip. *)
private let poly_centered_roundtrip_coeff (m:int{m > 1})
  (g: polynomial (zmod m)) (i:nat)
  : Lemma (coeff #(zmod m) (poly_to_fp m (poly_centered m g)) i
           = coeff #(zmod m) g i)
  = H.elim_equatable_laws (zmod m) ();
    (* coeff (poly_to_fp (poly_centered g)) i == to_fp m (coeff (poly_centered g) i) *)
    poly_to_fp_coeff m (poly_centered m g) i;
    (* coeff (poly_centered g) i == centered m (coeff g i) *)
    poly_centered_coeff m g i;
    (* to_fp m (centered m (coeff g i)) == coeff g i *)
    centered_roundtrip m (coeff g i)

(* round-trip:  poly_to_fp (poly_centered g) = g  in (ℤ/m)[X]. *)
let poly_centered_roundtrip (m:int{m > 1})
  (g: polynomial (zmod m))
  : Lemma ((poly_to_fp m (poly_centered m g)) = g)
  = let lhs = poly_to_fp m (poly_centered m g) in
    let aux (i:nat)
      : Lemma (coeff #(zmod m) lhs i
               = coeff #(zmod m) g i)
      = poly_centered_roundtrip_coeff m g i in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs g

(* poly_centered respects poly_eq. *)
let poly_centered_congr (m:int{m > 1}) (a b: polynomial (zmod m))
  : Lemma (requires a = b)
          (ensures  (poly_centered m a) = (poly_centered m b))
  = let lhs = poly_centered m a in
    let rhs = poly_centered m b in
    let aux (i:nat) : Lemma (coeff #int lhs i = coeff #int rhs i)
      = poly_centered_coeff m a i;
        poly_centered_coeff m b i;
        poly_eq_means_equal_coeffs a b i;
        H.elim_equatable_laws int () in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs
