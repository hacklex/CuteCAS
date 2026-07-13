module Core.Factor.ZassComplete

(* ================================================================ *)
(*  EXECUTABLE monic-pipeline factorizer + COMPLETENESS.             *)
(*                                                                   *)
(*  For a MONIC primitive input b (good prime p known), every monic  *)
(*  factor g of b is REACHED by the executable candidate list        *)
(*  `monic_candidates b`, and every survivor of the divides-filter    *)
(*  genuinely divides b.                                             *)
(*                                                                   *)
(*  Builds on the proven-green MONIC recombination completeness       *)
(*  (Core.Factor.ZassenhausComplete.finish_recomb) — replacing the    *)
(*  EXISTENTIAL Kronecker node list with an EXECUTABLE one.           *)
(*                                                                   *)
(*  Standalone (NOT on build-all).  NO admit / assume / sorry.        *)
(* ================================================================ *)

module L    = FStar.List.Tot
module LP   = FStar.List.Tot.Properties
module HeL  = Core.Algebra.Helpers
module HR   = Core.Modular.ResidueRing.Hensel.Reduce
module HL   = Core.Modular.ResidueRing.Hensel.Lift
module CP   = Core.Modular.ResidueRing.CenteredPoly
module PS   = Core.Factor.PrimeSelect
module Z    = Core.Factor.Zassenhaus
module ZM   = Core.Factor.ZassCompleteMod
module ZA   = Core.Factor.ZassCompleteArith
module ZC   = Core.Factor.ZassenhausComplete
module ML   = Core.Modular.ResidueRing.Hensel.MonicLift
module IntR = Core.Modular.ResidueRing.IntReduce
module FZB  = Core.Modular.FpZmodBridge
module RCmp = Core.Modular.RecombinationComplete
module RC   = Core.Factor.Recombine
module SP   = Core.Polynomial.SubsetProd
module IR   = Core.Polynomial.Irreducible
module KB   = Core.Polynomial.KroneckerBound
module PR   = Core.Polynomial.Roots
module EV   = Core.Polynomial.Eval
module UNI  = Core.Polynomial.Unique
module IRC  = Core.Polynomial.NodeExistence

open Core.Algebra
open Core.Algebra.Notation
open Core.NumberTheory
open Core.Polynomial
open Core.Polynomial.Monic
open Core.Polynomial.Roots
open Core.Polynomial.Eval
open Core.Algebra.Divisibility
open Core.Modular.ResidueRing
open Core.Modular.PrimeField

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ================================================================ *)
(*  §1 — EXECUTABLE non-vanishing node list.                        *)
(*                                                                   *)
(*  Filter a long-enough integer pool, dropping the (<= deg b) roots *)
(*  of b.  The remaining list is distinct, non-vanishing, and longer *)
(*  than deg b — valid Kronecker nodes for EVERY factor g (deg g <=  *)
(*  deg b).                                                          *)
(* ================================================================ *)

let non_root (b: polynomial int) (c: int) : bool = poly_eval b c <> 0
let is_root  (b: polynomial int) (c: int) : bool = poly_eval b c =  0

(* length of the consecutive-integer pool. *)
let rec iota_length (a:int) (cnt:nat)
  : Lemma (ensures L.length (Z.iota a cnt) == cnt) (decreases cnt)
  = if cnt = 0 then () else iota_length (a + 1) (cnt - 1)

(* filtering an integer list preserves distinctness. *)
let rec filter_all_distinct (f: int -> bool) (l: list int)
  : Lemma (requires all_distinct #int l)
          (ensures  all_distinct #int (L.filter f l))
          (decreases l)
  = match l with
    | [] -> ()
    | c :: cs ->
      filter_all_distinct f cs;
      if f c then
        introduce forall (d:int). L.memP d (L.filter f cs) ==> not (c = d)
        with introduce _ ==> _
          with _hm. L.mem_filter f cs d
      else ()

(* the pool splits into the kept (non-roots) and dropped (roots). *)
let rec pool_split_length (b: polynomial int) (l: list int)
  : Lemma (ensures L.length l ==
             L.length (L.filter (non_root b) l) ++ L.length (L.filter (is_root b) l))
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: cs -> pool_split_length b cs

(* the executable node list. *)
let nonvanishing_nodes (b: polynomial int{deg b >= 1}) : list int =
  let cnt : nat = Prims.op_Addition (Prims.op_Star 2 (deg b)) 2 in
  L.filter (non_root b) (Z.iota 0 cnt)

#push-options "--z3rlimit 40"
let nonvanishing_nodes_wf (b: polynomial int{deg b >= 1})
  : Lemma (all_distinct #int (nonvanishing_nodes b) /\
           L.length (nonvanishing_nodes b) > deg b /\
           (forall (j:nat). j < L.length (nonvanishing_nodes b) ==>
              poly_eval b (L.index (nonvanishing_nodes b) j) <> 0))
  = let cnt : nat = Prims.op_Addition (Prims.op_Star 2 (deg b)) 2 in
    let pool = Z.iota 0 cnt in
    iota_length 0 cnt;                        (* length pool == cnt *)
    ZA.iota_all_distinct 0 cnt;               (* all_distinct pool *)
    filter_all_distinct (non_root b) pool;    (* all_distinct nodes *)
    let roots = L.filter (is_root b) pool in
    filter_all_distinct (is_root b) pool;     (* all_distinct roots *)
    let pf (c:int) : Lemma (requires L.memP c roots) (ensures poly_eval b c == 0) =
      L.mem_filter (is_root b) pool c;
      assert (is_root b c);
      assert (poly_eval b c == 0)
    in
    IRC.int_root_count_bound b roots pf;      (* length roots <= deg b *)
    pool_split_length b pool;                 (* length nodes + length roots == cnt *)
    let nodes = nonvanishing_nodes b in
    let jpf (j:nat)
      : Lemma (j < L.length nodes ==> poly_eval b (L.index nodes j) <> 0)
      = if j < L.length nodes then begin
          L.lemma_index_memP nodes j;
          L.mem_filter (non_root b) pool (L.index nodes j)
        end
    in
    Classical.forall_intro jpf
#pop-options

(* ================================================================ *)
(*  §2 — EXECUTABLE monic candidate generator.                      *)
(*                                                                   *)
(*  Mirrors Core.Factor.Zassenhaus.zass_candidates, but with the     *)
(*  EXECUTABLE non-vanishing node list and the degree-controlled     *)
(*  MONIC multi-Hensel lift.                                         *)
(* ================================================================ *)

(* the chosen lift amount n (so pⁿ⁺¹ > 2·kbound over the executable nodes). *)
let mc_n (b: polynomial int{deg b >= 1}) (p:int{is_prime p}) : nat =
  Z.prime_gt1 p;
  let int_cs = nonvanishing_nodes b in
  let bnd : int = KB.kbound_rhs b int_cs in
  let target : nat = if bnd >= 0 then Prims.op_Star 2 bnd else 0 in
  Prims.op_Subtraction (Z.choose_k p target 1 (Prims.op_Addition target 1)) 1

(* the Hensel-lifted MONIC factors over zmod pⁿ⁺¹. *)
let mc_gs (b: polynomial int{deg b >= 1}) (p:int{is_prime p})
  : Pure (list (polynomial (zmod (HR.ppow p (mc_n b p ++ 1)))))
         (requires PS.is_good_prime p b /\ monic (PS.reduce_to_fp p b))
         (ensures  fun _ -> True)
  = PS.good_prime_sound p b;                     (* deg bbar == deg b, square_free bbar *)
    let bbar = PS.reduce_to_fp p b in
    let fps  = ZM.bfm p bbar in
    ZM.berlekamp_prod_eq p bbar;                 (* poly_prod fps = bbar *)
    UNI.degree_well_defined (PR.poly_prod fps) bbar;
    assert (Cons? fps);
    let gbars = L.map (FZB.poly_fz #p) fps in
    L.map_lemma (FZB.poly_fz #p) fps;            (* len gbars == len fps *)
    assert (Cons? gbars);
    ZM.berlekamp_monic p bbar;                   (* all_monic fps *)
    ZC.all_monic_map_poly_fz p fps;              (* all_monic gbars *)
    assert (SP.all_monic gbars);
    let bez   = Z.compute_bez p fps in
    let n     = mc_n b p in
    HR.ppow_gt_one p (n ++ 1);
    let pk    = HR.ppow p (n ++ 1) in
    let f     = CP.poly_to_fp pk b in
    ML.monic_hensel_lift_multi_compute p n f gbars bez

(* the executable candidate list. *)
let monic_candidates (b: polynomial int{deg b >= 1}) (p:int{is_prime p})
  : Pure (list (polynomial int))
         (requires PS.is_good_prime p b /\ monic (PS.reduce_to_fp p b))
         (ensures  fun _ -> True)
  = HR.ppow_gt_one p (mc_n b p ++ 1);
    let pk = HR.ppow p (mc_n b p ++ 1) in
    let gs = mc_gs b p in
    L.map (RC.recomb_candidate pk gs) (RC.subset_masks (L.length gs))

(* ================================================================ *)
(*  §3 — degree of a monic divisor is bounded by deg b.             *)
(* ================================================================ *)

let factor_deg_le (b g k0: polynomial int)
  : Lemma (requires monic g /\ deg b >= 1 /\ poly_eq b (g * k0))
          (ensures  deg g <= deg b)
  = HeL.elim_equatable_laws (polynomial int) ();
    UNI.degree_well_defined b (g * k0);            (* deg b == deg (g*k0) *)
    UNI.nonzero_iff_some_deg b;                     (* is_nonzero b (deg b >= 1) *)
    UNI.nonzero_iff_some_deg (g * k0);              (* is_nonzero (g*k0) <==> deg >= 0 *)
    poly_domain_law g k0;                           (* g*k0 ~ 0 <==> g ~ 0 \/ k0 ~ 0 *)
    UNI.nonzero_iff_some_deg k0;                    (* deg k0 >= 0 *)
    monic_deg_mul g k0                              (* deg (g*k0) == deg g + deg k0 *)

(* ================================================================ *)
(*  §4 — mask normalisation (recover a length-|gs| witness mask).    *)
(*                                                                   *)
(*  The recombination completeness returns g = poly_centered pk      *)
(*  (masked_prod gs mask) for an existential mask WITHOUT its length. *)
(*  `fit_mask` truncates / false-pads a mask to length |gs|; since a  *)
(*  false bit and an exhausted mask both DROP the remaining factors,  *)
(*  the masked product is unchanged — so we recover a mask the        *)
(*  enumeration `subset_masks |gs|` provably contains.               *)
(* ================================================================ *)

let rec fit_mask (n:nat) (mask: list bool) : Tot (list bool) (decreases n) =
  if n = 0 then []
  else (match mask with
        | []      -> false :: fit_mask (n - 1) []
        | b :: m' -> b     :: fit_mask (n - 1) m')

let rec fit_mask_length (n:nat) (mask: list bool)
  : Lemma (ensures L.length (fit_mask n mask) == n) (decreases n)
  = if n = 0 then ()
    else (match mask with
          | []      -> fit_mask_length (n - 1) []
          | _ :: m' -> fit_mask_length (n - 1) m')

#push-options "--fuel 2 --ifuel 1"
let rec masked_prod_fit (#t:Type) {| cr: commutative_ring t |}
  (gs: list (polynomial t)) (mask: list bool)
  : Lemma (ensures SP.masked_prod gs mask ==
                   SP.masked_prod gs (fit_mask (L.length gs) mask))
          (decreases gs)
  = match gs with
    | [] -> ()
    | _ :: gs' ->
      (match mask with
       | []      -> masked_prod_fit gs' []
       | _ :: m' -> masked_prod_fit gs' m')
#pop-options

(* ================================================================ *)
(*  §5 — COMPLETENESS: every monic factor is reached.               *)
(* ================================================================ *)

(* the executable modulus level exceeds the recombination bound.     *)
#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let mc_n_spec (b: polynomial int{deg b >= 1}) (p:int{is_prime p})
  : Lemma (HR.ppow p (mc_n b p ++ 1) >
           2 * KB.kbound_rhs b (nonvanishing_nodes b))
  = Z.prime_gt1 p;
    let int_cs = nonvanishing_nodes b in
    let bnd : int = KB.kbound_rhs b int_cs in
    let target : nat = if bnd >= 0 then Prims.op_Star 2 bnd else 0 in
    ZA.choose_k_spec p target;                (* ppow p (choose_k …) > target *)
    assert (mc_n b p ++ 1 == Z.choose_k p target 1 (Prims.op_Addition target 1));
    assert (2 * bnd == Prims.op_Star 2 bnd)
#pop-options

(* HEAVY: the Berlekamp / Hensel / recombination bundle for the       *)
(* EXECUTABLE (int_cs = nonvanishing_nodes b, n = mc_n b p) pipeline.  *)
(* The Kronecker node conditions are HYPOTHESES (kept out of the       *)
(* berlekamp query context), so this discharges like the proven-green  *)
(* zassenhaus_recombines_monic body.                                   *)
#push-options "--z3rlimit 40 --fuel 4 --ifuel 1 --split_queries always"
let reached_at (b g: polynomial int) (p:int{is_prime p})
  : Lemma
      (requires monic b /\ monic g /\ deg b >= 1 /\ divides g b /\
                PS.is_good_prime p b /\ monic (PS.reduce_to_fp p b) /\
                PR.all_distinct (nonvanishing_nodes b) /\
                deg g < L.length (nonvanishing_nodes b) /\
                (forall (j:nat). j < L.length (nonvanishing_nodes b) ==>
                   poly_eval b (L.index (nonvanishing_nodes b) j) <> 0) /\
                HR.ppow p (mc_n b p ++ 1) >
                  2 * KB.kbound_rhs b (nonvanishing_nodes b))
      (ensures exists (d: polynomial int).
          L.memP d (monic_candidates b p) /\ poly_eq d g)
  = HeL.elim_equatable_laws (polynomial int) ();
    HeL.elim_equatable_laws (polynomial (zmod p)) ();
    HeL.elim_equatable_laws (polynomial (fp p)) ();
    let bbar = PS.reduce_to_fp p b in
    PS.good_prime_sound p b;
    let int_cs = nonvanishing_nodes b in
    let n : nat = mc_n b p in
    HR.ppow_gt_one p (n ++ 1);
    let pk : int = HR.ppow p (n ++ 1) in
    eliminate exists (k0: polynomial int). poly_eq b (g * k0)
    returns (exists (d: polynomial int). L.memP d (monic_candidates b p) /\ poly_eq d g)
    with _.
    begin
      (* --- Berlekamp factor bundle over fp p --- *)
      let fps   = ZM.bfm p bbar in
      ZM.berlekamp_prod_eq p bbar;
      UNI.degree_well_defined (PR.poly_prod fps) bbar;
      assert (Cons? fps);
      let gbars = L.map (FZB.poly_fz #p) fps in
      L.map_lemma (FZB.poly_fz #p) fps;
      assert (Cons? gbars);
      ZM.berlekamp_monic p bbar;
      ZC.all_monic_map_poly_fz p fps;
      assert (SP.all_monic gbars);
      let bez   = Z.compute_bez p fps in
      let fpoly = CP.poly_to_fp pk b in
      let gs    = ML.monic_hensel_lift_multi_compute p n fpoly gbars bez in
      HeL.elim_equatable_laws (polynomial (zmod pk)) ();
      ZM.berlekamp_coprime p bbar;
      ZC.bfm_all_irreducible p bbar;
      ZM.bezout_chain_of_coprime p fps;
      ZM.hensel_input_eq p n b;
      ML.monic_hensel_lift_multi_compute_correct p n fpoly gbars bez;
      let tbc (i:nat{i < L.length gs /\ i < L.length gbars})
        : Lemma ((HL.poly_to_base p (n ++ 1) (L.index gs i)) = (L.index gbars i))
        = HeL.elim_equatable_laws (polynomial (zmod p)) () in
      RCmp.to_base_corr_intro p (n ++ 1) gs gbars tbc;
      IntR.poly_to_fp_monic pk b;
      ML.monic_hensel_lift_multi_all_monic p n fpoly gbars bez;
      ZM.true_factor_divides_prod p n b g;
      ZC.finish_recomb p n b g k0 gs fps int_cs;
      (* --- wrap: recover a length-|gs| mask + monic_candidates membership --- *)
      eliminate exists (mask: list bool).
          g = CP.poly_centered pk (SP.masked_prod gs mask)
      returns (exists (d: polynomial int). L.memP d (monic_candidates b p) /\ poly_eq d g)
      with _.
      begin
        let mask'' = fit_mask (L.length gs) mask in
        masked_prod_fit gs mask;                   (* masked_prod gs mask == masked_prod gs mask'' *)
        fit_mask_length (L.length gs) mask;        (* length mask'' == length gs *)
        RC.mask_in_subset_masks mask'';            (* memP mask'' (subset_masks (length gs)) *)
        let d = RC.recomb_candidate pk gs mask'' in
        LP.memP_map_intro (RC.recomb_candidate pk gs) mask'' (RC.subset_masks (L.length gs));
        assert (mc_gs b p == gs);
        assert (monic_candidates b p ==
                L.map (RC.recomb_candidate pk gs) (RC.subset_masks (L.length gs)));
        introduce exists (dd: polynomial int).
            L.memP dd (monic_candidates b p) /\ poly_eq dd g
        with d and ()
      end
    end
#pop-options

(* LIGHT: derive the executable node bundle, then invoke reached_at.  *)
#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let monic_factor_reached (b g: polynomial int) (p:int{is_prime p})
  : Lemma
      (requires monic b /\ monic g /\ deg b >= 1 /\ divides g b /\
                PS.is_good_prime p b /\ monic (PS.reduce_to_fp p b))
      (ensures exists (d: polynomial int).
          L.memP d (monic_candidates b p) /\ poly_eq d g)
  = nonvanishing_nodes_wf b;                 (* distinct, length > deg b, non-vanishing *)
    eliminate exists (k0: polynomial int). poly_eq b (g * k0)
    returns deg g <= deg b
    with _. factor_deg_le b g k0;            (* deg g <= deg b < length nodes *)
    mc_n_spec b p;                            (* pk > 2*kbound *)
    reached_at b g p
#pop-options

(* ================================================================ *)
(*  §6 — SOUNDNESS: every filtered survivor divides b.              *)
(* ================================================================ *)

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let monic_factor_sound (b d: polynomial int) (p:int{is_prime p})
  : Lemma
      (requires deg b >= 1 /\ PS.is_good_prime p b /\ monic (PS.reduce_to_fp p b) /\
                L.memP d (L.filter (Z.keep_int b) (monic_candidates b p)))
      (ensures  deg d >= 1 /\ divides d b)
  = L.mem_filter (Z.keep_int b) (monic_candidates b p) d;   (* keep_int b d /\ memP d cands *)
    RC.divides_test_sound b d                               (* divides d b *)
#pop-options
