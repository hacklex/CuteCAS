module Core.Risch.ResultantFactorExec

(* ================================================================ *)
(*  EXECUTABLE resultant-factor coverage.                            *)
(*                                                                   *)
(*  Upgrades `Core.Risch.VcRendering.resultant_factorization_covers` *)
(*  (which covers every residue via factorization-EXISTENCE          *)
(*  `poly_factorization_exists`) towards the EXECUTABLE complete      *)
(*  factorizer `Core.Factor.ZassComplete.monic_candidates`, which     *)
(*  provably REACHES every monic factor of a monic input.            *)
(*                                                                   *)
(*  Two halves, joined honestly (see NOTE on the type gap):          *)
(*                                                                   *)
(*  (A) ABSTRACT side  `resultant_factors_reached_exec`              *)
(*      For the RT resultant  R = lrt_resultant_raw p q  over a       *)
(*      generic field t (deg R >= 1), the MONIC NORMALISATION        *)
(*      Rm = make_monic R  is monic, an associate of R (same roots), *)
(*      still has every residue  beta = residue p roots (hd g)  as a *)
(*      root, and R factors into irreducibles whose roots cover all  *)
(*      residues.  This is the "monic-normalise R" step, done         *)
(*      UNCONDITIONALLY at the abstract level.                       *)
(*                                                                   *)
(*  (B) EXECUTABLE side  `monic_factors_all_reached`                 *)
(*      For a MONIC integer polynomial b (good prime p known, monic  *)
(*      reduction mod p), EVERY monic factor in any factor list of b *)
(*      is EXECUTABLY reached by `ZassComplete.monic_candidates b p` *)
(*      (a straight map of `ZassComplete.monic_factor_reached`).     *)
(*                                                                   *)
(*  NOTE — TYPE GAP (honest, unclosed).  `monic_candidates` and       *)
(*  `monic_factor_reached` are strictly `polynomial int`             *)
(*  (Zassenhaus over Q), while the RT resultant `lrt_resultant_raw`  *)
(*  and residues live over an ABSTRACT `field t`.  There is no        *)
(*  `field int`, and no Q[z]<->Z[z] (Gauss's-lemma) executable        *)
(*  bridge in the tower, so `Rm : polynomial t` CANNOT be fed to      *)
(*  `monic_candidates` for abstract t.  Hence (A) and (B) are         *)
(*  delivered separately: the executable REACHING is fully proved     *)
(*  (B, at int), the abstract residue COVERAGE + monic normalisation  *)
(*  is fully proved (A), and the single wiring step between them      *)
(*  awaits the (still-open) integer-realisation bridge.               *)
(*                                                                   *)
(*  Standalone (NOT on build-all).  NO admit / assume / sorry.        *)
(* ================================================================ *)

module L    = FStar.List.Tot
module VR   = Core.Risch.VcRendering
module RP   = Core.Risch.ResiduePartition
module RTS  = Core.Risch.RTSoundness
module LRT  = Core.Risch.LRT
module LAG  = Core.Polynomial.Lagrange
module PR   = Core.Polynomial.Roots
module IR   = Core.Polynomial.Irreducible
module PS   = Core.Factor.PrimeSelect
module ZAC  = Core.Factor.ZassComplete
module NT   = Core.NumberTheory
module H    = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Monic
open Core.Polynomial.Roots
open Core.Polynomial.Eval
open Core.Polynomial.Div

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ================================================================ *)
(*  §A.1 — a residue is still a root after monic normalisation.      *)
(*         poly_eval (make_monic R) beta = inv(lc R) * poly_eval R   *)
(*         beta = inv(lc R) * 0 = 0.                                 *)
(* ================================================================ *)
let residue_root_of_monic (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t) (g: list t) (q: polynomial t{deg q >= 1})
  : Lemma (requires all_distinct roots /\ Cons? g /\ L.memP (L.hd g) roots /\
                    q == poly_prod_linears roots /\
                    deg (LRT.lrt_resultant_raw p q) >= 1)
          (ensures  poly_eval (make_monic (LRT.lrt_resultant_raw p q))
                              (RTS.residue p roots (L.hd g)) = (zero <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let bigR = LRT.lrt_resultant_raw p q in
    let beta = RTS.residue p roots (L.hd g) in
    VR.rendered_coeff_is_resultant_root p roots g q;   (* poly_eval bigR beta = zero *)
    leading_coeff_nonzero bigR;
    last_eq_index bigR (deg bigR);
    poly_lc_reveal bigR;
    let u : t = inv (poly_lc bigR) in
    assert (make_monic bigR == poly_scale u bigR);
    LAG.eval_scale u bigR beta;                        (* eval (scale u bigR) beta = u * eval bigR beta *)
    assert (poly_eval (make_monic bigR) beta = (u * poly_eval bigR beta));
    mul_congruence u (poly_eval bigR beta) u (zero <: t);
    H.x_mul_zero u

(* ================================================================ *)
(*  §A.2 — ABSTRACT capstone.  Monic-normalise R, cover residues.    *)
(* ================================================================ *)
#push-options "--z3rlimit 40"
let resultant_factors_reached_exec (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t) (q: polynomial t{deg q >= 1})
  : Lemma (requires all_distinct roots /\ q == poly_prod_linears roots /\
                    deg (LRT.lrt_resultant_raw p q) >= 1)
          (ensures (let bigR  = LRT.lrt_resultant_raw p q in
                    let bigRm = make_monic bigR in
                    (* monic normalisation of R *)
                    monic bigRm /\
                    (exists (u:t). not (u = (zero <: t)) /\ (bigRm = (poly_const u * bigR))) /\
                    (* every residue is a root of the monic Rm *)
                    (forall (grp:list t). L.memP grp (RP.residue_partition p roots) ==>
                       poly_eval bigRm (RTS.residue p roots (L.hd grp)) = (zero <: t)) /\
                    (* R factors into irreducibles whose roots cover all residues *)
                    (exists (facs: list (polynomial t)).
                       Cons? facs /\
                       (divides (PR.poly_prod facs) bigR /\ divides bigR (PR.poly_prod facs)) /\
                       (forall (h:polynomial t). L.memP h facs ==> IR.poly_irreducible h) /\
                       (forall (grp:list t). L.memP grp (RP.residue_partition p roots) ==>
                          (exists (h:polynomial t). L.memP h facs /\
                             poly_eval h (RTS.residue p roots (L.hd grp)) = (zero <: t))))))
  = let bigR  = LRT.lrt_resultant_raw p q in
    make_monic_monic bigR;
    make_monic_associate bigR;
    let groups = RP.residue_partition p roots in
    introduce forall (grp:list t). L.memP grp groups ==>
                poly_eval (make_monic bigR) (RTS.residue p roots (L.hd grp)) = (zero <: t)
    with introduce _ ==> _
    with _hg. residue_root_of_monic p roots grp q;
    VR.resultant_factorization_covers p roots q
#pop-options

(* ================================================================ *)
(*  §B — EXECUTABLE reaching (int level).  Every monic factor in a    *)
(*        factor list of a monic integer b is reached by the          *)
(*        executable candidate list `monic_candidates b p`.           *)
(* ================================================================ *)
let monic_factors_all_reached
  (b: polynomial int) (facs: list (polynomial int)) (p:int{NT.is_prime p})
  : Lemma
      (requires monic b /\ deg b >= 1 /\
                PS.is_good_prime p b /\ monic (PS.reduce_to_fp p b) /\
                (forall (h: polynomial int). L.memP h facs ==>
                   (monic h /\ divides h b)))
      (ensures  forall (h: polynomial int). L.memP h facs ==>
                   (exists (d: polynomial int).
                      L.memP d (ZAC.monic_candidates b p) /\ poly_eq d h))
  = introduce forall (h: polynomial int). L.memP h facs ==>
                (exists (d: polynomial int).
                   L.memP d (ZAC.monic_candidates b p) /\ poly_eq d h)
    with introduce _ ==> _
    with _hmem. ZAC.monic_factor_reached b h p
