module Core.Factor.Zassenhaus

(* ================================================================ *)
(*  M2 · S8+S9 — the executable Zassenhaus assembly.                 *)
(*                                                                   *)
(*  factor_Z : polynomial int -> list (p:int{is_prime p})           *)
(*                            -> list (polynomial int)               *)
(*    content/primitive (S1) → good prime (S4) → Berlekamp mod p     *)
(*    (S5) → Hensel lift to mod pᵏ (S6) → subset recombination (S7). *)
(*    Every emitted ℤ-polynomial is NON-CONSTANT and DIVIDES F.      *)
(*                                                                   *)
(*  factor_Q : polynomial qq -> list (p:int{is_prime p})            *)
(*                           -> list (polynomial qq)                 *)
(*    clear denominators (S1) → factor_Z → embed back to ℚ[z].       *)
(*                                                                   *)
(*  SOUNDNESS  (the load-bearing guarantee, proven unconditionally): *)
(*    factor_Z_sound : every output divides F over ℤ;                *)
(*    factor_Q_sound : every output divides the cleared/embedded     *)
(*                     integer poly `embed_zq n`, an associate of r  *)
(*                     (embed_zq n ~ (const d)·r), i.e. divides r     *)
(*                     up to the nonzero ℚ-unit d = denom_prod r.     *)
(*                                                                   *)
(*  The soundness is DECOUPLED from the (heuristic) pipeline: the     *)
(*  FINAL stage filters candidates by an EXECUTED ℤ-division test     *)
(*  (`divides_test`), so `divides d F` holds for every survivor       *)
(*  regardless of how the candidate was proposed.  The Berlekamp /    *)
(*  Hensel / recombination machinery only affects COMPLETENESS        *)
(*  (whether the true factors are among the proposals).               *)
(*                                                                   *)
(*  COMPLETENESS is WIRED as far as the stages permit                 *)
(*  (`recombination_reaches` below relays S7's `try_recombine_        *)
(*  complete`); the residual R2 gaps (Berlekamp reaches-r /           *)
(*  coprimality, S7 divides_test completeness, S4 unconditional       *)
(*  prime existence) are inherited from the stages and reported.      *)
(*                                                                   *)
(*  Standalone (NOT on build-all).  NO admit / assume / sorry.        *)
(* ================================================================ *)

module L  = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module H  = Core.Algebra.Helpers

module CC = Core.Factor.Content
module PS = Core.Factor.PrimeSelect
module BF = Core.Factor.BerlekampFactor
module HC = Core.Factor.HenselCompute
module RC = Core.Factor.Recombine
module KB = Core.Polynomial.KroneckerBound
module FZ = Core.Modular.FpZmodBridge
module CP = Core.Modular.ResidueRing.CenteredPoly
module HR = Core.Modular.ResidueRing.Hensel.Reduce
module HM = Core.Modular.ResidueRing.Hensel.Multi
module PF = Core.Polynomial.PartialFraction
module GC = Core.Polynomial.GCD
module EQ = Core.Polynomial.EmbedQ
module RCmp = Core.Modular.RecombinationComplete
module HL = Core.Modular.ResidueRing.Hensel.Lift
module SP = Core.Polynomial.SubsetProd
module EV = Core.Polynomial.Eval

open Core.NumberTheory
open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Int
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Monic
open Core.Polynomial.Roots
open Core.Modular.ResidueRing
open Core.Modular.PrimeField
open Core.Polynomial.EmbedQ

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ================================================================ *)
(*  §0 — tiny total helpers (nodes, k-choice, prime bound).          *)
(* ================================================================ *)

let prime_gt1 (p:int{is_prime p}) : Lemma (p > 1) = ()

(* distinct integer node pool a, a+1, …  (for the Kronecker bound).  *)
let rec iota (a:int) (cnt:nat) : Tot (list int) (decreases cnt) =
  if cnt = 0 then []
  else a :: iota (Prims.op_Addition a 1) (Prims.op_Subtraction cnt 1)

let node_list (b: polynomial int) : list int =
  let m : nat = if deg b >= 0 then Prims.op_Addition (deg b) 1 else 1 in
  iota 1 m

(* smallest k≥1 with pᵏ > target (fuel-bounded; total).             *)
let rec choose_k (p:int{p > 1}) (target:nat) (k:pos) (fuel:nat)
  : Tot pos (decreases fuel) =
  if HR.ppow p k > target then k
  else if fuel = 0 then k
  else choose_k p target (Prims.op_Addition k 1) (Prims.op_Subtraction fuel 1)

(* ================================================================ *)
(*  §1 — Bézout chain over 𝔽ₚ (guarded; total).                       *)
(*                                                                   *)
(*  For pairwise-coprime Berlekamp factors h :: tail, the head pair  *)
(*  (bezout_left h ∏tail, bezout_right h ∏tail) satisfies the        *)
(*  bezout_chain identity — but we do NOT need to PROVE that for      *)
(*  soundness, so the construction is guarded and total (a non-       *)
(*  coprime pair merely degrades completeness, never soundness).     *)
(* ================================================================ *)

let compute_bez_pair (p:int{is_prime p}) (h pt: polynomial (fp p))
  : HM.bez_pair p =
  if (deg h >= 0 && GC.coprime h pt)
  then (FZ.poly_fz #p (PF.bezout_left h pt), FZ.poly_fz #p (PF.bezout_right h pt))
  else (poly_zero #(zmod p), poly_zero #(zmod p))

let rec compute_bez (p:int{is_prime p}) (fps: list (polynomial (fp p)))
  : Tot (list (HM.bez_pair p)) (decreases fps) =
  match fps with
  | []       -> []
  | [_]      -> []
  | h :: tail -> compute_bez_pair p h (poly_prod #(fp p) tail) :: compute_bez p tail

(* ================================================================ *)
(*  §2 — the pipeline: PROPOSE ℤ-candidate factors of B.             *)
(*                                                                   *)
(*  find good prime → reduce → Berlekamp → Hensel-lift → subset      *)
(*  recombination, returning the centered subset-products.  Purely   *)
(*  heuristic: soundness is enforced later by the divides filter.    *)
(* ================================================================ *)

let zass_candidates (b: polynomial int) (primes: list (p:int{is_prime p}))
  : list (polynomial int) =
  if not (PS.good_in_list b primes) then []
  else begin
    let p = PS.find_good_prime b primes () in
    let bbar = PS.reduce_to_fp p b in
    if deg bbar < 1 then []
    else
      match BF.berlekamp_factor p bbar with
      | []  -> []
      | [_] -> []
      | hd1 :: hd2 :: rest ->
        let fps   : list (polynomial (fp p))   = hd1 :: hd2 :: rest in
        let gbars : list (polynomial (zmod p)) =
          FZ.poly_fz #p hd1 :: FZ.poly_fz #p hd2 :: L.map (FZ.poly_fz #p) rest in
        let bez   : list (HM.bez_pair p) = compute_bez p fps in
        let target : nat =
          let bnd = KB.kbound_rhs b (node_list b) in
          if bnd >= 0 then Prims.op_Star 2 bnd else 0 in
        prime_gt1 p;
        let kk : pos = choose_k p target 1 (Prims.op_Addition target 1) in
        let n  : nat = Prims.op_Subtraction kk 1 in
        HR.ppow_gt_one p (n ++ 1);
        let pk : int = HR.ppow p (n ++ 1) in
        let f  : polynomial (zmod (HR.ppow p (n ++ 1))) = CP.poly_to_fp pk b in
        let gs : list (polynomial (zmod (HR.ppow p (n ++ 1)))) =
          HC.hensel_lift_multi_compute p n f gbars bez in
        L.map (RC.recomb_candidate pk gs) (RC.subset_masks (L.length gs))
  end

(* ================================================================ *)
(*  §3 — factor_Z : the SOUND executable ℤ-factorizer.               *)
(* ================================================================ *)

(* keep a candidate iff non-constant AND (executed test) divides B.  *)
let keep_int (b d: polynomial int) : bool =
  (deg d >= 1) && RC.divides_test b d

let factor_Z (f: polynomial int) (primes: list (p:int{is_prime p}))
  : list (polynomial int) =
  let b = CC.primitive_part f in
  (* B is always a fallback candidate: an irreducible B survives.  *)
  L.filter (keep_int f) (b :: zass_candidates b primes)

(* ================================================================ *)
(*  §4 — SOUNDNESS of factor_Z: every output divides F.              *)
(* ================================================================ *)

let factor_Z_sound (f: polynomial int) (primes: list (p:int{is_prime p}))
  (d: polynomial int)
  : Lemma (requires L.memP d (factor_Z f primes))
          (ensures  deg d >= 1 /\ divides d f)
  = let b    = CC.primitive_part f in
    let cand = b :: zass_candidates b primes in
    (* d ∈ filter keep cand  ⟹  memP d cand  ∧  keep_int f d = true *)
    L.mem_filter (keep_int f) cand d;
    (* keep_int f d = true  ⟹  deg d >= 1  ∧  divides_test f d = true *)
    RC.divides_test_sound f d          (* divides d f *)

(* ================================================================ *)
(*  §5 — factor_Q : the SOUND executable ℚ-factorizer.               *)
(* ================================================================ *)

let factor_Q (r: polynomial qq) (primes: list (p:int{is_prime p}))
  : list (polynomial qq) =
  let (_, n) = CC.clear_denominators r in
  L.map EQ.embed_zq (factor_Z n primes)

(* ================================================================ *)
(*  §6 — SOUNDNESS of factor_Q.                                       *)
(*                                                                   *)
(*  Each output divides `embed_zq n`, which by clear_denominators_   *)
(*  sound is an associate of r (embed_zq n ~ (const d)·r).  Hence     *)
(*  each output divides r up to the nonzero ℚ-unit d = denom_prod r. *)
(* ================================================================ *)

(* embed preserves poly_eq (coefficient-wise; embed is ℤ→ℚ hom). *)
let embed_zq_congr (a b: polynomial int)
  : Lemma (requires poly_eq a b)
          (ensures  poly_eq (EQ.embed_zq a) (EQ.embed_zq b))
  = H.elim_equatable_laws qq ();
    let per (i:nat)
      : Lemma (coeff (EQ.embed_zq a) i = coeff (EQ.embed_zq b) i)
      = EQ.embed_zq_coeff a i;                       (* coeff (embed a) i ~ embed_const (coeff a i) *)
        EQ.embed_zq_coeff b i;                       (* coeff (embed b) i ~ embed_const (coeff b i) *)
        poly_eq_means_equal_coeffs a b i;            (* coeff a i == coeff b i (==) *)
        symmetry (coeff (EQ.embed_zq b) i) (EQ.embed_zq_const (coeff b i));
        transitivity (coeff (EQ.embed_zq a) i)
                     (EQ.embed_zq_const (coeff a i))
                     (coeff (EQ.embed_zq b) i)
    in
    poly_eq_by_coeff (EQ.embed_zq a) (EQ.embed_zq b) per

(* embed preserves divisibility:  g | n  ⟹  embed g | embed n. *)
let embed_zq_divides (g n: polynomial int)
  : Lemma (requires divides g n)
          (ensures  divides (EQ.embed_zq g) (EQ.embed_zq n))
  = H.elim_equatable_laws (polynomial qq) ();
    eliminate exists (c: polynomial int). poly_eq n (g * c)
    returns divides (EQ.embed_zq g) (EQ.embed_zq n)
    with _hc.
    begin
      embed_zq_congr n (g * c);                      (* embed n ~ embed (g*c) *)
      EQ.embed_zq_mul g c;                           (* embed (g*c) ~ embed g * embed c *)
      poly_eq_transitivity (EQ.embed_zq n)
                           (EQ.embed_zq (g * c))
                           ((EQ.embed_zq g) * (EQ.embed_zq c));
      divides_intro (EQ.embed_zq g) (EQ.embed_zq n) (EQ.embed_zq c)
    end

let factor_Q_sound (r: polynomial qq) (primes: list (p:int{is_prime p}))
  (d: polynomial qq)
  : Lemma (requires L.memP d (factor_Q r primes))
          (ensures  (let (_, n) = CC.clear_denominators r in
                     divides d (EQ.embed_zq n)))
  = let (_, n) = CC.clear_denominators r in
    let ints = factor_Z n primes in
    (* d ∈ map embed_zq ints  ⟹  ∃ g ∈ ints. embed_zq g == d *)
    LP.memP_map_elim EQ.embed_zq d ints;
    eliminate exists (g: polynomial int). L.memP g ints /\ EQ.embed_zq g == d
    returns divides d (EQ.embed_zq n)
    with _hg.
    begin
      factor_Z_sound n primes g;                     (* divides g n *)
      embed_zq_divides g n                            (* divides (embed g) (embed n) = divides d (embed n) *)
    end

(* ================================================================ *)
(*  §7 — COMPLETENESS, WIRED to the finished §D theory.               *)
(*                                                                   *)
(*  This is the assembly-level relay of S7's `try_recombine_complete` *)
(*  (which itself consumes RecombinationComplete.recombination_       *)
(*  complete): under the full recombination hypothesis bundle, a      *)
(*  true monic ℤ-factor g of bigF EQUALS the centered masked sub-     *)
(*  product for a mask the enumeration `subset_masks` provably        *)
(*  contains — i.e. the raw candidate list produced by the pipeline   *)
(*  (`L.map (recomb_candidate …) (subset_masks …)`) reaches g.        *)
(*                                                                   *)
(*  RESIDUAL R2 (inherited from the stages; NOT closed here) — the    *)
(*  hypothesis bundle is exactly what the pipeline would have to      *)
(*  DISCHARGE to conclude g ∈ factor_Z, and each conjunct is an open  *)
(*  completeness gap of an earlier stage:                            *)
(*   (i)   S5 Berlekamp "reaches r"  (kernel spanning, S3 dependency) *)
(*         and pairwise-coprimality of the gbars — needed so the      *)
(*         `to_base_corr` / Bézout / `all_monic` premises HOLD for    *)
(*         the ACTUAL Hensel lift the pipeline computes;              *)
(*   (ii)  S6 Hensel `bezout_chain` discharge — needed so            *)
(*         `poly_to_fp bigF = poly_prod gs` holds for the computed gs;*)
(*   (iii) S7 `divides_test` COMPLETENESS (monic d ∧ d|bigF ⟹         *)
(*         divides_test = true) — needed so g SURVIVES `keep_int`     *)
(*         into the output list;                                      *)
(*   (iv)  S4 unconditional good-prime EXISTENCE (is_prime            *)
(*         non-decidable) — needed so `good_in_list` fires.           *)
(*  All SOUNDNESS above is unconditional; these are completeness/     *)
(*  executability-existence gaps only.                                *)
(* ================================================================ *)

let recombination_reaches
  (p:int{p > 1}) (n:nat)
  (bigF g k0: polynomial int)
  (gs: list (polynomial (zmod (HR.ppow p (n ++ 1)))))
  (gbars: list (polynomial (zmod p)))
  (mask: list bool)
  (s t: polynomial (zmod p))
  (int_cs: list int)
  : Lemma
      (requires
        bigF = (g * k0) /\ monic g /\
        (CP.poly_to_fp (HR.ppow p (n ++ 1)) bigF) = (poly_prod gs) /\
        L.length mask == L.length gs /\
        L.length gbars == L.length gs /\
        RCmp.to_base_corr p (n ++ 1) gs gbars /\
        (HL.poly_to_base p (n ++ 1) (CP.poly_to_fp (HR.ppow p (n ++ 1)) g))
          = (SP.masked_prod gbars mask) /\
        SP.all_monic gs /\
        ((s * (SP.masked_prod gbars mask))
         + (t * (SP.masked_prod gbars (SP.negate_mask mask))))
          = (poly_one #(zmod p)) /\
        all_distinct int_cs /\
        deg g < L.length int_cs /\
        (forall (j:nat). j < L.length int_cs ==>
            EV.poly_eval bigF (L.index int_cs j) <> 0) /\
        (HR.ppow p (n ++ 1)) > Prims.op_Star 2 (KB.kbound_rhs bigF int_cs))
      (ensures
        (exists (m: list bool).
           L.memP m (RC.subset_masks (L.length gs)) /\
           g = (RC.recomb_candidate (HR.ppow p (n ++ 1)) gs m)))
  = RC.try_recombine_complete p n bigF g k0 gs gbars mask s t int_cs;
    introduce exists (m: list bool).
                L.memP m (RC.subset_masks (L.length gs)) /\
                g = (RC.recomb_candidate (HR.ppow p (n ++ 1)) gs m)
    with mask
    and ()

(* r is an associate of embed_zq n:  embed_zq n ~ (const d)·r,        *)
(* d = denom_prod r ≠ 0 a ℚ-unit — so "divides d (embed n)" is        *)
(* exactly "divides d r up to a nonzero ℚ-unit".                      *)
let factor_Q_associate (r: polynomial qq)
  : Lemma (poly_eq (EQ.embed_zq (snd (CC.clear_denominators r)))
                   (poly_scale (EQ.embed_zq_const (fst (CC.clear_denominators r))) r))
  = CC.clear_denominators_sound r
