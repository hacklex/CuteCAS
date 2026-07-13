module Core.Factor.ZassenhausComplete

(* ================================================================ *)
(*  MONIC Zassenhaus recombination completeness — ASSEMBLY.          *)
(*                                                                   *)
(*  Every monic factor g of a monic primitive b (good prime p,       *)
(*  monic reduce_to_fp p b) is recovered by the recombination:       *)
(*  g IS the centered masked-product of the Hensel-lifted monic      *)
(*  Berlekamp factors.                                               *)
(*                                                                   *)
(*  All discharge lemmas are proven+green elsewhere; this wires them. *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L   = FStar.List.Tot
module HR  = Core.Modular.ResidueRing.Hensel.Reduce
module HL  = Core.Modular.ResidueRing.Hensel.Lift
module CP  = Core.Modular.ResidueRing.CenteredPoly
module PS  = Core.Factor.PrimeSelect
module Z   = Core.Factor.Zassenhaus
module ZM  = Core.Factor.ZassCompleteMod
module ZA  = Core.Factor.ZassCompleteArith
module HC  = Core.Factor.HenselCompute
module ML  = Core.Modular.ResidueRing.Hensel.MonicLift
module IntR = Core.Modular.ResidueRing.IntReduce
module FZB = Core.Modular.FpZmodBridge
module RC  = Core.Modular.RecombinationComplete
module SP  = Core.Polynomial.SubsetProd
module IR  = Core.Polynomial.Irreducible
module KB  = Core.Polynomial.KroneckerBound
module BF  = Core.Factor.BerlekampFactor
module BC6 = Core.Factor.BerlekampComplete6
module BCM = Core.Modular.PrimeField.BerlekampComplete
module SF  = Core.Polynomial.SquareFree
module PR  = Core.Polynomial.Roots
module EV  = Core.Polynomial.Eval
module UNI = Core.Polynomial.Unique

open Core.Algebra
open Core.Algebra.Notation
open Core.NumberTheory
open Core.Polynomial
open Core.Polynomial.Monic
open Core.Algebra.Divisibility
open Core.Modular.ResidueRing
open Core.Modular.PrimeField

#set-options "--fuel 2 --ifuel 1 --z3rlimit 20"

(* ================================================================ *)
(*  Helper — all_irreducible (bfm p fbar).                           *)
(*                                                                   *)
(*  bfm = L.map make_monic (berlekamp_factor p fbar); each raw       *)
(*  Berlekamp factor is irreducible (B.5), and make_monic preserves  *)
(*  irreducibility (associate of irreducible).                       *)
(* ================================================================ *)

let bfm_all_irreducible (p:int{is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  : Lemma (requires SF.square_free fbar)
          (ensures  SP.all_irreducible (ZM.bfm p fbar))
  = let bf = BF.berlekamp_factor p fbar in
    let gs = ZM.bfm p fbar in
    BC6.berlekamp_factor_all_irreducible p fbar;      (* all_irreducible bf *)
    SP.all_irreducible_elim bf;                       (* forall x. memP x bf ==> irreducible x *)
    let pir (h: polynomial (fp p){L.memP h gs}) : Lemma (IR.poly_irreducible h)
      = L.memP_map_elim make_monic h bf;
        eliminate exists (x: polynomial (fp p)). L.memP x bf /\ make_monic x == h
        returns IR.poly_irreducible h
        with _. BCM.make_monic_irreducible x in
    SP.all_irreducible_intro gs pir

(* ================================================================ *)
(*  Helper — poly_fz preserves monicity across a list (map version). *)
(*                                                                   *)
(*  poly_fz sends each monic fp-factor to a monic zmod-factor        *)
(*  (FZB.poly_fz_monic); an all_monic list therefore maps to an      *)
(*  all_monic list.  Needed to satisfy the {Cons? /\ all_monic}      *)
(*  refinement on the gbars argument of the MONIC multi-Hensel lift. *)
(* ================================================================ *)

let all_monic_map_poly_fz (p:int{is_prime p}) (fps: list (polynomial (fp p)))
  : Lemma (requires SP.all_monic fps)
          (ensures  SP.all_monic (L.map (FZB.poly_fz #p) fps))
  = let gs = L.map (FZB.poly_fz #p) fps in
    SP.all_monic_elim fps;
    let pmon (h: polynomial (zmod p){L.memP h gs}) : Lemma (monic h)
      = L.memP_map_elim (FZB.poly_fz #p) h fps;
        eliminate exists (x: polynomial (fp p)). L.memP x fps /\ FZB.poly_fz #p x == h
        returns monic h
        with _. FZB.poly_fz_monic #p x in
    SP.all_monic_intro gs pmon

(* ================================================================ *)
(*  MAIN — zassenhaus_recombines_monic.  UNCONDITIONAL.               *)
(*                                                                   *)
(*  all_monic gs — the ONE premise of recombination_complete_fp not   *)
(*  delivered by the raw executable Hensel lift — is now discharged    *)
(*  INTERNALLY by the degree-controlled MONIC multi-Hensel lift        *)
(*  (Core.Modular.ResidueRing.Hensel.MonicLift): monic b ⇒ monic       *)
(*  fpoly, and monic_hensel_lift_multi_all_monic yields all_monic gs.  *)
(*  No Lemma-valued caller obligation remains.                         *)
(* ================================================================ *)

module HeL = Core.Algebra.Helpers

(* pk = pⁿ⁺¹ > 1 at every level, exposed with an SMT pattern so the zmod /
   poly_centered / poly_to_fp terms under the existential binder n in the
   returns / ensures clauses are well-formed WITHOUT an unrestricted (and
   cascade-prone) quantifier in the proof context. *)
let ppow_succ_gt_one (p:int{is_prime p}) (m:nat)
  : Lemma (HR.ppow p (m ++ 1) > 1) [SMTPat (HR.ppow p (m ++ 1))]
  = HR.ppow_gt_one p (m ++ 1)

(* Clean-context wrapper for the capstone: with the recombination hypotheses
   presented as its OWN requires, the precondition of recombination_complete_fp
   matches syntactically, so the call discharges at fuel 1 / ifuel 0 (no
   quantifier search over the caller's equational / kbound context). *)
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let finish_recomb
  (p:int{is_prime p}) (n:nat)
  (b g k0: polynomial int)
  (gs: list (polynomial (zmod (HR.ppow p (n ++ 1)))))
  (fps: list (polynomial (fp p)))
  (int_cs: list int)
  : Lemma
      (requires
        b = (g * k0) /\ monic g /\
        (CP.poly_to_fp (HR.ppow p (n ++ 1)) b) = (PR.poly_prod gs) /\
        L.length fps == L.length gs /\
        RC.to_base_corr p (n ++ 1) gs (L.map (FZB.poly_fz #p) fps) /\
        SP.all_monic gs /\ SP.all_irreducible fps /\ SP.all_monic fps /\
        divides (FZB.poly_zf (HL.poly_to_base p (n ++ 1)
                  (CP.poly_to_fp (HR.ppow p (n ++ 1)) g))) (PR.poly_prod fps) /\
        IR.pairwise_coprime fps /\
        PR.all_distinct int_cs /\ deg g < L.length int_cs /\
        (forall (j:nat). j < L.length int_cs ==>
           EV.poly_eval b (L.index int_cs j) <> 0) /\
        (HR.ppow p (n ++ 1)) > 2 * (KB.kbound_rhs b int_cs))
      (ensures  exists (mask: list bool).
        g = CP.poly_centered (HR.ppow p (n ++ 1)) (SP.masked_prod gs mask))
  = FZB.recombination_complete_fp p n b g k0 gs fps int_cs
#pop-options

(* Clean-context existential wrapper: from the recombination conclusion for the
   concrete (n, gs), introduce the top-level existential.  Isolated so the
   introduce runs without the caller's equational / hensel quantifier context. *)
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
let wrap_exists (p:int{is_prime p}) (n:nat) (b g: polynomial int)
  (gs: list (polynomial (zmod (HR.ppow p (n ++ 1)))))
  : Lemma
      (requires
        deg (PS.reduce_to_fp p b) >= 1 /\
        Cons? (L.map (FZB.poly_fz #p) (ZM.bfm p (PS.reduce_to_fp p b))) /\
        SP.all_monic (L.map (FZB.poly_fz #p) (ZM.bfm p (PS.reduce_to_fp p b))) /\
        gs == ML.monic_hensel_lift_multi_compute p n
                (CP.poly_to_fp (HR.ppow p (n ++ 1)) b)
                (L.map (FZB.poly_fz #p) (ZM.bfm p (PS.reduce_to_fp p b)))
                (Z.compute_bez p (ZM.bfm p (PS.reduce_to_fp p b))) /\
        (exists (mask: list bool).
           g = CP.poly_centered (HR.ppow p (n ++ 1)) (SP.masked_prod gs mask)))
      (ensures exists (n':nat)
                      (gs': list (polynomial (zmod (HR.ppow p (n' ++ 1)))))
                      (mask': list bool).
          g = CP.poly_centered (HR.ppow p (n' ++ 1)) (SP.masked_prod gs' mask') /\
          gs' == ML.monic_hensel_lift_multi_compute p n'
                   (CP.poly_to_fp (HR.ppow p (n' ++ 1)) b)
                   (L.map (FZB.poly_fz #p) (ZM.bfm p (PS.reduce_to_fp p b)))
                   (Z.compute_bez p (ZM.bfm p (PS.reduce_to_fp p b))))
  = eliminate exists (mask: list bool).
        g = CP.poly_centered (HR.ppow p (n ++ 1)) (SP.masked_prod gs mask)
    returns (exists (n':nat)
                    (gs': list (polynomial (zmod (HR.ppow p (n' ++ 1)))))
                    (mask': list bool).
        g = CP.poly_centered (HR.ppow p (n' ++ 1)) (SP.masked_prod gs' mask') /\
        gs' == ML.monic_hensel_lift_multi_compute p n'
                 (CP.poly_to_fp (HR.ppow p (n' ++ 1)) b)
                 (L.map (FZB.poly_fz #p) (ZM.bfm p (PS.reduce_to_fp p b)))
                 (Z.compute_bez p (ZM.bfm p (PS.reduce_to_fp p b))))
    with _.
    introduce exists (n':nat)
                     (gs': list (polynomial (zmod (HR.ppow p (n' ++ 1)))))
                     (mask': list bool).
        g = CP.poly_centered (HR.ppow p (n' ++ 1)) (SP.masked_prod gs' mask') /\
        gs' == ML.monic_hensel_lift_multi_compute p n'
                 (CP.poly_to_fp (HR.ppow p (n' ++ 1)) b)
                 (L.map (FZB.poly_fz #p) (ZM.bfm p (PS.reduce_to_fp p b)))
                 (Z.compute_bez p (ZM.bfm p (PS.reduce_to_fp p b)))
    with n gs mask
    and ()
#pop-options

#push-options "--z3rlimit 40 --fuel 4 --ifuel 1 --split_queries always"
let zassenhaus_recombines_monic (b g: polynomial int) (p:int{is_prime p})
  : Lemma
      (requires monic b /\ monic g /\ deg b >= 1 /\ divides g b /\
                PS.is_good_prime p b /\ monic (PS.reduce_to_fp p b) /\
                (* derived (via good_prime_sound + berlekamp_prod_eq +
                   berlekamp_monic + all_monic_map_poly_fz); exposed here only so
                   the bfm / monic_hensel_lift_multi_compute terms in the ensures
                   are well-typed (deg + Cons? + all_monic refinements).  A caller
                   discharges all_monic via `all_monic_map_poly_fz`. *)
                deg (PS.reduce_to_fp p b) >= 1 /\
                Cons? (L.map (FZB.poly_fz #p) (ZM.bfm p (PS.reduce_to_fp p b))) /\
                SP.all_monic (L.map (FZB.poly_fz #p) (ZM.bfm p (PS.reduce_to_fp p b))))
      (ensures exists (n:nat)
                      (gs: list (polynomial (zmod (HR.ppow p (n ++ 1)))))
                      (mask: list bool).
          g = CP.poly_centered (HR.ppow p (n ++ 1)) (SP.masked_prod gs mask) /\
          gs == ML.monic_hensel_lift_multi_compute p n
                  (CP.poly_to_fp (HR.ppow p (n ++ 1)) b)
                  (L.map (FZB.poly_fz #p) (ZM.bfm p (PS.reduce_to_fp p b)))
                  (Z.compute_bez p (ZM.bfm p (PS.reduce_to_fp p b))))
  = HeL.elim_equatable_laws (polynomial int) ();
    HeL.elim_equatable_laws (polynomial (zmod p)) ();
    HeL.elim_equatable_laws (polynomial (fp p)) ();
    let bbar = PS.reduce_to_fp p b in
    PS.good_prime_sound p b;                    (* deg bbar == deg b, square_free bbar *)
    (* --- unpack divides g b : exists k0. b = g * k0 --- *)
    eliminate exists (k0: polynomial int). poly_eq b (g * k0)
    returns (exists (n:nat)
                    (gs: list (polynomial (zmod (HR.ppow p (n ++ 1)))))
                    (mask: list bool).
          g = CP.poly_centered (HR.ppow p (n ++ 1)) (SP.masked_prod gs mask) /\
          gs == ML.monic_hensel_lift_multi_compute p n
                  (CP.poly_to_fp (HR.ppow p (n ++ 1)) b)
                  (L.map (FZB.poly_fz #p) (ZM.bfm p bbar))
                  (Z.compute_bez p (ZM.bfm p bbar)))
    with _.
    begin
      (* --- Kronecker non-vanishing node list --- *)
      ZA.node_nonvanishing_exist b g;
      eliminate exists (int_cs: list int).
          deg g < L.length int_cs /\ PR.all_distinct #int int_cs /\
          (forall (j:nat). j < L.length int_cs ==>
             EV.poly_eval b (L.index int_cs j) <> 0)
      returns (exists (n:nat)
                      (gs: list (polynomial (zmod (HR.ppow p (n ++ 1)))))
                      (mask: list bool).
          g = CP.poly_centered (HR.ppow p (n ++ 1)) (SP.masked_prod gs mask) /\
          gs == ML.monic_hensel_lift_multi_compute p n
                  (CP.poly_to_fp (HR.ppow p (n ++ 1)) b)
                  (L.map (FZB.poly_fz #p) (ZM.bfm p bbar))
                  (Z.compute_bez p (ZM.bfm p bbar)))
      with _.
      begin
        (* --- choose the modulus level --- *)
        let bnd : int = KB.kbound_rhs b int_cs in
        let target : nat = if bnd >= 0 then Prims.op_Star 2 bnd else 0 in
        let kk : pos = Z.choose_k p target 1 (Prims.op_Addition target 1) in
        let n : nat = Prims.op_Subtraction kk 1 in
        HR.ppow_gt_one p (n ++ 1);                 (* pk > 1 *)
        let pk : int = HR.ppow p (n ++ 1) in
        ZA.choose_k_spec p target;                 (* ppow p kk > target *)
        assert (n ++ 1 == kk);
        assert (pk > target);
        assert (pk > Prims.op_Star 2 bnd);         (* Kronecker: pk > 2*kbound *)

        (* --- Berlekamp factor bundle over fp p --- *)
        let fps   = ZM.bfm p bbar in
        ZM.berlekamp_prod_eq p bbar;               (* poly_prod fps = bbar *)
        UNI.degree_well_defined (PR.poly_prod fps) bbar;
        assert (Cons? fps);
        let gbars = L.map (FZB.poly_fz #p) fps in
        L.map_lemma (FZB.poly_fz #p) fps;          (* len gbars == len fps *)
        assert (Cons? gbars);
        ZM.berlekamp_monic p bbar;                 (* all_monic fps *)
        all_monic_map_poly_fz p fps;               (* all_monic gbars — refines the ML arg *)
        assert (SP.all_monic gbars);
        let bez   = Z.compute_bez p fps in
        let fpoly = CP.poly_to_fp pk b in
        let gs    = ML.monic_hensel_lift_multi_compute p n fpoly gbars bez in
        HeL.elim_equatable_laws (polynomial (zmod pk)) ();

        ZM.berlekamp_coprime p bbar;               (* pairwise_coprime fps *)
        bfm_all_irreducible p bbar;                (* all_irreducible fps *)

        (* --- Bezout chain & Hensel input --- *)
        ZM.bezout_chain_of_coprime p fps;          (* bezout_chain p gbars bez *)
        ZM.hensel_input_eq p n b;                  (* poly_to_base fpoly = poly_prod gbars *)

        (* --- Hensel-lift compute soundness --- *)
        ML.monic_hensel_lift_multi_compute_correct p n fpoly gbars bez;
        (* build to_base_corr from the per-index poly_eq facts *)
        let tbc (i:nat{i < L.length gs /\ i < L.length gbars})
          : Lemma ((HL.poly_to_base p (n ++ 1) (L.index gs i)) = (L.index gbars i))
          = HeL.elim_equatable_laws (polynomial (zmod p)) () in
        RC.to_base_corr_intro p (n ++ 1) gs gbars tbc;

        (* --- monic gs: discharged INTERNALLY by the degree-controlled MONIC
           multi-Hensel lift (monic b ⇒ monic fpoly; all_monic gbars, product
           and Bezout chain from above ⇒ all_monic gs). --- *)
        IntR.poly_to_fp_monic pk b;                (* monic fpoly *)
        ML.monic_hensel_lift_multi_all_monic p n fpoly gbars bez;

        (* --- true factor divides the fp product --- *)
        ZM.true_factor_divides_prod p n b g;

        (* --- capstone: recombination completeness on the fp side --- *)
        (* bridge Prims mul (from choose_k target) to the ring `*` that
           finish_recomb's Kronecker hypothesis is stated with. *)
        assert (2 * bnd == Prims.op_Star 2 bnd);
        finish_recomb p n b g k0 gs fps int_cs;
        wrap_exists p n b g gs
      end
    end
#pop-options
