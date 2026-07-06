module Core.Modular.RecombinationComplete

(* ================================================================ *)
(*  §D (D2d + D3) — RECOMBINATION COMPLETENESS.                      *)
(*                                                                   *)
(*  This module closes the COMPLETENESS side of the §D theory: every *)
(*  true monic integer factor `g` of `bigF` is (the centred lift of) *)
(*  a subset-product of the mod-pᵏ Hensel factors `gs`.              *)
(*                                                                   *)
(*  TYPE SEAM (accepted design).  Berlekamp / D2b live at `fp p`     *)
(*  (a field); Hensel lives at `zmod p` / `zmod (ppow p k)`          *)
(*  (commutative rings only).  The mod-p subset-mask correspondence  *)
(*  therefore enters HERE as a HYPOTHESIS at the `zmod` level — its   *)
(*  derivation is D2b at `fp p` plus a future `fp ≅ zmod` bridge      *)
(*  (task #33's seam).                                               *)
(*                                                                   *)
(*  D2d  true_factor_is_masked_lift :  poly_to_fp pᵏ g  =  masked    *)
(*       sub-product of `gs`  (via Hensel uniqueness).               *)
(*  D3   recombination_complete :  g = poly_centered pᵏ (masked      *)
(*       sub-product)  (via kronecker_lift_recovers).               *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Modular.ResidueRing
open Core.Modular.ResidueRing.Centered
open Core.Modular.ResidueRing.Hensel.Reduce
open Core.Modular.ResidueRing.Hensel.Lift
open Core.Modular.ResidueRing.Hensel.Multi
open Core.Modular.ResidueRing.Hensel.Unique
open Core.Modular.ResidueRing.CenteredPoly
open Core.Modular.ResidueRing.IntReduce
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.Monic
open Core.Polynomial.Roots
open Core.Polynomial.Eval
open Core.Polynomial.SubsetProd
open Core.Polynomial.KroneckerBound
open Core.Polynomial.KroneckerLift
open Core.Polynomial.NodeExistence

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  0. Small structural facts about  poly_one  and  masked_prod.     *)
(* ================================================================ *)

(* `one_deg_lc` and `monic_one` (poly_one deg/lc/monic over a nontrivial CR)
   now live publicly in Core.Polynomial.Monic (in scope via open). *)

(* The generic masked_prod kit — `masked_prod_mask_nil`, `negate_mask`,
   the `all_monic` opaque predicate + elim/proof/intro/tail/head bridges,
   `masked_prod_monic`, and `masked_prod_split` — now lives publicly at its
   source Core.Polynomial.SubsetProd (in scope via open). *)

(* ================================================================ *)
(*  4. Congruences for the reduction / centring maps (support (f)).  *)
(* ================================================================ *)

(* Reduction/centring congruences (`poly_to_fp_congr`, `poly_centered_congr`)
   and `poly_to_fp_monic` now live publicly at source:
     - poly_to_fp_congr, poly_to_fp_monic : Core.Modular.ResidueRing.IntReduce
     - poly_centered_congr                : Core.Modular.ResidueRing.CenteredPoly
     - to_base_monic (poly_to_base)       : Core.Modular.ResidueRing.Hensel.Lift
     - poly_to_base_one                   : Core.Modular.ResidueRing.Hensel.Lift
   (all in scope via open). *)

(* ================================================================ *)
(*  7. poly_to_base pushes through a masked product (support (d)).    *)
(*     Given a per-index reduction correspondence gs[i] ↦ gbars[i].   *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
private let rec to_base_masked_prod (p:int{p > 1}) (k:pos)
  (gs: list (polynomial (zmod (ppow p k))))
  (gbars: list (polynomial (zmod p)))
  (mask: list bool)
  (pf: (i:nat{i < L.length gs /\ i < L.length gbars})
       -> Lemma ((poly_to_base p k (L.index gs i)) = (L.index gbars i)))
  : Lemma (requires L.length gs == L.length gbars)
          (ensures  (poly_to_base p k (masked_prod gs mask))
                    = (masked_prod gbars mask))
          (decreases gs)
  = ppow_gt_one p k;
    H.elim_equatable_laws (polynomial (zmod p)) ();
    H.trans_for_calc (polynomial (zmod p)) ();
    match gs, gbars with
    | [], [] ->
      masked_prod_nil #(zmod (ppow p k)) mask;
      masked_prod_nil #(zmod p) mask;
      poly_to_base_one p k
    | g0 :: gs', gb0 :: gbars' ->
      (match mask with
       | [] ->
         masked_prod_mask_nil gs;
         masked_prod_mask_nil gbars;
         poly_to_base_one p k
       | true :: m' ->
         pf 0;                                      (* poly_to_base g0 = gb0 *)
         let pf' (i:nat{i < L.length gs' /\ i < L.length gbars'})
           : Lemma ((poly_to_base p k (L.index gs' i)) = (L.index gbars' i))
           = pf (i ++ 1) in
         to_base_masked_prod p k gs' gbars' m' pf'; (* poly_to_base(masked gs' m') = masked gbars' m' *)
         let xg = masked_prod gs' m' in
         let xb = masked_prod gbars' m' in
         masked_prod_cons_true g0 gs' m';           (* masked gs mask == g0 * xg *)
         masked_prod_cons_true gb0 gbars' m';        (* masked gbars mask == gb0 * xb *)
         poly_to_base_mul p k g0 xg;                 (* to_base(g0*xg) = to_base g0 * to_base xg *)
         mul_congruence (poly_to_base p k g0) (poly_to_base p k xg) gb0 xb;
         poly_eq_transitivity
           (poly_to_base p k (g0 * xg))
           ((poly_to_base p k g0) * (poly_to_base p k xg))
           (gb0 * xb)
       | false :: m' ->
         let pf' (i:nat{i < L.length gs' /\ i < L.length gbars'})
           : Lemma ((poly_to_base p k (L.index gs' i)) = (L.index gbars' i))
           = pf (i ++ 1) in
         to_base_masked_prod p k gs' gbars' m' pf';
         masked_prod_cons_false g0 gs' m';
         masked_prod_cons_false gb0 gbars' m')
    | [], _ :: _ -> ()
    | _ :: _, [] -> ()
#pop-options

(* ================================================================ *)
(*  8. The mod-p reduction correspondence, as an OPAQUE predicate.    *)
(*     `to_base_corr`  ⟺  ∀ i < |gs|. poly_to_base gs[i] = gbars[i].  *)
(* ================================================================ *)

[@@"opaque_to_smt"]
let to_base_corr (p:int{p > 1}) (k:pos)
  (gs: list (polynomial (zmod (ppow p k))))
  (gbars: list (polynomial (zmod p)))
  : prop =
  forall (i:nat). (i < L.length gs /\ i < L.length gbars) ==>
    (poly_to_base p k (L.index gs i)) = (L.index gbars i)

let to_base_corr_elim (p:int{p > 1}) (k:pos)
  (gs: list (polynomial (zmod (ppow p k))))
  (gbars: list (polynomial (zmod p)){to_base_corr p k gs gbars})
  : Lemma (forall (i:nat). (i < L.length gs /\ i < L.length gbars) ==>
             (poly_to_base p k (L.index gs i)) = (L.index gbars i))
  = reveal_opaque (`%to_base_corr) (to_base_corr p k gs gbars)

let to_base_corr_proof (p:int{p > 1}) (k:pos)
  (gs: list (polynomial (zmod (ppow p k))))
  (gbars: list (polynomial (zmod p)))
  = (i:nat{i < L.length gs /\ i < L.length gbars})
    -> Lemma ((poly_to_base p k (L.index gs i)) = (L.index gbars i))

let to_base_corr_intro (p:int{p > 1}) (k:pos)
  (gs: list (polynomial (zmod (ppow p k))))
  (gbars: list (polynomial (zmod p)))
  (proof: to_base_corr_proof p k gs gbars)
  : Lemma (to_base_corr p k gs gbars)
  = reveal_opaque (`%to_base_corr) (to_base_corr p k gs gbars);
    let aux (i:nat)
      : Lemma ((i < L.length gs /\ i < L.length gbars) ==>
               (poly_to_base p k (L.index gs i)) = (L.index gbars i))
      = introduce (i < L.length gs /\ i < L.length gbars) ==>
                  (poly_to_base p k (L.index gs i)) = (L.index gbars i)
        with _hi. proof i
    in
    Classical.forall_intro aux

(* ================================================================ *)
(*  9. D2d — the pᵏ transport theorem.                              *)
(*                                                                   *)
(*  A true monic ℤ-factorization bigF = g·k0 reduces mod pᵏ to a      *)
(*  product ∏ gs.  Given (i) the per-index mod-p correspondence       *)
(*  gs[i] ↦ gbars[i], (ii) the mod-p subset-mask correspondence for g *)
(*  (the fp-side seam, as a hypothesis), (iii) all gs monic, and      *)
(*  (iv) a base-field Bézout identity for the split, the mod-pᵏ image *)
(*  of g is exactly the masked sub-product of gs.                    *)
(*                                                                   *)
(*  Route:  G := to_fp g, H := to_fp k0, C := masked gs mask,         *)
(*  D := masked gs ¬mask.  G·H = ∏gs = C·D.  to_base G = to_base C    *)
(*  (both = masked gbars mask) and both monic ⟹ to_base H = to_base D *)
(*  (monic cancel) and deg G = deg C.  Bézout transports to the       *)
(*  reductions ⟹ hensel_unique ⟹ G = C.                              *)
(* ================================================================ *)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let true_factor_is_masked_lift
  (p:int{p > 1}) (n:nat)
  (bigF g k0: polynomial int)
  (gs: list (polynomial (zmod (ppow p (n ++ 1)))))
  (gbars: list (polynomial (zmod p)))
  (mask: list bool)
  (s t: polynomial (zmod p))
  : Lemma
      (requires
        bigF = (g * k0) /\ monic g /\
        (poly_to_fp (ppow p (n ++ 1)) bigF) = (poly_prod gs) /\
        L.length mask == L.length gs /\
        L.length gbars == L.length gs /\
        to_base_corr p (n ++ 1) gs gbars /\
        (poly_to_base p (n ++ 1) (poly_to_fp (ppow p (n ++ 1)) g))
          = (masked_prod gbars mask) /\
        all_monic gs /\
        ((s * (masked_prod gbars mask))
         + (t * (masked_prod gbars (negate_mask mask))))
          = (poly_one #(zmod p)))
      (ensures (poly_to_fp (ppow p (n ++ 1)) g) = (masked_prod gs mask))
  = ppow_gt_one p (n ++ 1);
    let pk1 = ppow p (n ++ 1) in
    H.elim_equatable_laws (polynomial (zmod pk1)) ();
    H.trans_for_calc (polynomial (zmod pk1)) ();
    H.elim_equatable_laws (polynomial (zmod p)) ();
    H.trans_for_calc (polynomial (zmod p)) ();
    let bG = poly_to_fp pk1 g in
    let bH = poly_to_fp pk1 k0 in
    let cC = masked_prod gs mask in
    let dD = masked_prod gs (negate_mask mask) in
    let tbG = poly_to_base p (n ++ 1) bG in
    let tbH = poly_to_base p (n ++ 1) bH in
    let tbC = poly_to_base p (n ++ 1) cC in
    let tbD = poly_to_base p (n ++ 1) dD in
    (* ---- (1) bG · bH = poly_prod gs ---- *)
    poly_to_fp_mul pk1 g k0;                       (* to_fp (g*k0) = bG * bH *)
    poly_to_fp_congr pk1 bigF (g * k0);            (* to_fp bigF = to_fp (g*k0) *)
    poly_eq_symmetry (poly_to_fp pk1 (g * k0)) (bG * bH);
    poly_eq_transitivity (bG * bH) (poly_to_fp pk1 (g * k0)) (poly_to_fp pk1 bigF);
    poly_eq_transitivity (bG * bH) (poly_to_fp pk1 bigF) (poly_prod gs);
    (* ---- (2) poly_prod gs = cC · dD  ⟹  bG·bH = cC·dD ---- *)
    masked_prod_split gs mask;
    poly_eq_transitivity (bG * bH) (poly_prod gs) (cC * dD);
    (* ---- (3) reduce the product identity to the base field ---- *)
    poly_to_base_mul p (n ++ 1) bG bH;             (* tb(bG*bH) = tbG * tbH *)
    poly_to_base_mul p (n ++ 1) cC dD;             (* tb(cC*dD) = tbC * tbD *)
    poly_to_base_congr p (n ++ 1) (bG * bH) (cC * dD);
    poly_eq_symmetry (poly_to_base p (n ++ 1) (bG * bH)) (tbG * tbH);
    poly_eq_transitivity (tbG * tbH)
      (poly_to_base p (n ++ 1) (bG * bH)) (poly_to_base p (n ++ 1) (cC * dD));
    poly_eq_transitivity (tbG * tbH)
      (poly_to_base p (n ++ 1) (cC * dD)) (tbC * tbD);  (* tbG*tbH = tbC*tbD *)
    (* ---- (4) tbC = masked gbars mask,  tbD = masked gbars ¬mask ---- *)
    to_base_corr_elim p (n ++ 1) gs gbars;
    let pf (i:nat{i < L.length gs /\ i < L.length gbars})
      : Lemma ((poly_to_base p (n ++ 1) (L.index gs i)) = (L.index gbars i)) = () in
    to_base_masked_prod p (n ++ 1) gs gbars mask pf;               (* tbC = masked gbars mask *)
    to_base_masked_prod p (n ++ 1) gs gbars (negate_mask mask) pf; (* tbD = masked gbars ¬mask *)
    (* ---- (5) tbG = tbC  (both equal masked gbars mask) ---- *)
    poly_eq_symmetry tbC (masked_prod gbars mask);   (* masked gbars mask = tbC *)
    poly_eq_transitivity tbG (masked_prod gbars mask) tbC;   (* tbG = tbC *)
    (* ---- (6) monicity (deg equality now derived inside hensel_unique) ---- *)
    poly_to_fp_monic pk1 g;                          (* monic bG *)
    masked_prod_monic () gs mask;                    (* monic cC *)
    to_base_monic p (n ++ 1) cC;                     (* monic tbC — needed by monic_mul_cancel *)
    (* ---- (7) cofactor reductions agree:  tbH = tbD ---- *)
    mul_congruence tbG tbH tbC tbH;                  (* tbG*tbH = tbC*tbH *)
    poly_eq_symmetry (tbG * tbH) (tbC * tbH);
    poly_eq_transitivity (tbC * tbH) (tbG * tbH) (tbC * tbD);  (* tbC*tbH = tbC*tbD *)
    monic_mul_cancel tbC tbH tbD;                    (* tbH = tbD *)
    (* ---- (8) transport the Bézout identity to (tbG, tbH) ---- *)
    poly_eq_transitivity tbH tbD (masked_prod gbars (negate_mask mask));  (* tbH = masked gbars ¬mask *)
    poly_eq_symmetry tbH (masked_prod gbars (negate_mask mask));          (* masked ¬mask = tbH *)
    poly_eq_symmetry tbG (masked_prod gbars mask);                        (* masked mask = tbG *)
    mul_congruence s (masked_prod gbars mask) s tbG;                      (* s*masked = s*tbG *)
    mul_congruence t (masked_prod gbars (negate_mask mask)) t tbH;         (* t*masked¬ = t*tbH *)
    add_congruence
      ((s * (masked_prod gbars mask)))
      ((t * (masked_prod gbars (negate_mask mask))))
      ((s * tbG)) ((t * tbH));
    poly_eq_symmetry
      ((s * (masked_prod gbars mask)) + (t * (masked_prod gbars (negate_mask mask))))
      ((s * tbG) + (t * tbH));
    poly_eq_transitivity
      ((s * tbG) + (t * tbH))
      ((s * (masked_prod gbars mask)) + (t * (masked_prod gbars (negate_mask mask))))
      (poly_one #(zmod p));                          (* (s*tbG)+(t*tbH) = poly_one *)
    (* ---- (9) Hensel uniqueness closes G = C ---- *)
    hensel_unique p n bG bH cC dD s t
#pop-options

(* ================================================================ *)
(*  10. D3 — the completeness headline.                             *)
(*                                                                   *)
(*  Adds the Kronecker node conditions and a modulus large enough    *)
(*  (pᵏ > 2·kbound_rhs) to recover g exactly by centring the masked  *)
(*  sub-product of the Hensel factors.                              *)
(* ================================================================ *)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let recombination_complete
  (p:int{p > 1}) (n:nat)
  (bigF g k0: polynomial int)
  (gs: list (polynomial (zmod (ppow p (n ++ 1)))))
  (gbars: list (polynomial (zmod p)))
  (mask: list bool)
  (s t: polynomial (zmod p))
  (int_cs: list int)
  : Lemma
      (requires
        (* --- D2d hypotheses --- *)
        bigF = (g * k0) /\ monic g /\
        (poly_to_fp (ppow p (n ++ 1)) bigF) = (poly_prod gs) /\
        L.length mask == L.length gs /\
        L.length gbars == L.length gs /\
        to_base_corr p (n ++ 1) gs gbars /\
        (poly_to_base p (n ++ 1) (poly_to_fp (ppow p (n ++ 1)) g))
          = (masked_prod gbars mask) /\
        all_monic gs /\
        ((s * (masked_prod gbars mask))
         + (t * (masked_prod gbars (negate_mask mask))))
          = (poly_one #(zmod p)) /\
        (* --- Kronecker node conditions (mirror kronecker_lift_recovers) --- *)
        all_distinct int_cs /\
        deg g < L.length int_cs /\
        (forall (j:nat). j < L.length int_cs ==>
            poly_eval bigF (L.index int_cs j) <> 0) /\
        (ppow p (n ++ 1)) > 2 * (kbound_rhs bigF int_cs))
      (ensures g = (poly_centered (ppow p (n ++ 1)) (masked_prod gs mask)))
  = let pk1 = ppow p (n ++ 1) in
    ppow_gt_one p (n ++ 1);                          (* pk1 > 1 *)
    H.elim_equatable_laws (polynomial int) ();
    H.trans_for_calc (polynomial int) ();
    (* D2d:  to_fp pk1 g = masked_prod gs mask *)
    true_factor_is_masked_lift p n bigF g k0 gs gbars mask s t;
    (* Kronecker recovery:  poly_centered pk1 (to_fp pk1 g) = g *)
    kronecker_lift_recovers g k0 bigF int_cs pk1;
    (* congruence:  poly_centered pk1 (to_fp pk1 g) = poly_centered pk1 (masked_prod gs mask) *)
    poly_centered_congr pk1 (poly_to_fp pk1 g) (masked_prod gs mask);
    poly_eq_symmetry (poly_centered pk1 (poly_to_fp pk1 g)) g;   (* g = poly_centered pk1 (to_fp g) *)
    poly_eq_transitivity g
      (poly_centered pk1 (poly_to_fp pk1 g))
      (poly_centered pk1 (masked_prod gs mask))
#pop-options

(* ================================================================ *)
(*  11. D1 wiring — valid Kronecker nodes exist (remark corollary).  *)
(*     A nonzero bigF and a monic factor g admit a node list long    *)
(*     enough (length > deg g) on which bigF never vanishes.          *)
(* ================================================================ *)

let recombination_nodes_exist (bigF g: polynomial int)
  : Lemma (requires monic g /\ deg bigF >= 0)
          (ensures  exists (int_cs: list int).
             deg g < L.length int_cs /\
             all_distinct int_cs /\
             (forall (j:nat). j < L.length int_cs ==>
                poly_eval bigF (L.index int_cs j) <> 0))
  = assert (deg g >= 0);
    let dgn : nat = deg g in
    let nn : nat = dgn ++ 1 in
    nodes_exist bigF nn;
    eliminate exists (cs: list int).
       L.length cs == nn /\ all_distinct cs /\
       (forall (j:nat). j < nn ==>
          poly_eval bigF (L.index cs j) <> 0)
    returns (exists (int_cs: list int).
       deg g < L.length int_cs /\
       all_distinct int_cs /\
       (forall (j:nat). j < L.length int_cs ==>
          poly_eval bigF (L.index int_cs j) <> 0))
    with _hcs.
    introduce exists (int_cs: list int).
       deg g < L.length int_cs /\
       all_distinct int_cs /\
       (forall (j:nat). j < L.length int_cs ==>
          poly_eval bigF (L.index int_cs j) <> 0)
    with cs and ()
