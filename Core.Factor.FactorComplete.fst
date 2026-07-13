module Core.Factor.FactorComplete

(* ================================================================ *)
(*  CAP — the named executable integer factorizer, SOUND + COMPLETE,  *)
(*  with the completeness hypothesis phrased on `b` directly.         *)
(*                                                                   *)
(*  `Core.Factor.FactorIntComplete.factor_int_complete` is proven     *)
(*  sound (`factor_int_complete_sound`) and complete                 *)
(*  (`factor_int_complete_complete`).  The latter's squarefree        *)
(*  hypothesis was on `embed_zq (monicize_pos b)`; the bridge         *)
(*  `MonicizeSqfree.monicize_sqfree_bridge` (monic-ization preserves  *)
(*  ℚ-squarefreeness) lets us restate it on `embed_zq b` directly —   *)
(*  removing the last hypothesis-phrasing daylight.                   *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                        *)
(* ================================================================ *)

module L    = FStar.List.Tot
module H    = Core.Algebra.Helpers
module DV   = Core.Algebra.Divisibility
module R    = Core.Polynomial.Roots
module EQ   = Core.Polynomial.EmbedQ
module SF   = Core.Polynomial.SquareFree
module BIN  = Core.Factor.BadIntNonzero
module PS   = Core.Factor.PrimeSelect
module E    = Core.NumberTheory
module CC   = Core.Factor.Content
module NMZ  = Core.Factor.NonMonicZass
module FIC  = Core.Factor.FactorIntComplete
module MSF  = Core.Factor.MonicizeSqfree

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Monic

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* Completeness of the named executable factorizer, with the       *)
(* squarefree hypothesis on `b` directly (via the monicize bridge). *)
let factor_int_complete_complete_b (b: polynomial int)
  : Lemma (requires CC.is_primitive b /\ deg b >= 1 /\
                    SF.square_free #EQ.qq #BIN.ff (EQ.embed_zq b))
          (ensures exists (p:int{E.is_prime p}) (facs': list (polynomial int)).
             PS.is_good_prime p (NMZ.monicize_pos b) /\
             monic (PS.reduce_to_fp p (NMZ.monicize_pos b)) /\
             Cons? facs' /\
             (DV.divides (R.poly_prod facs') b /\ DV.divides b (R.poly_prod facs')) /\
             (forall (g: polynomial int). L.memP g facs' ==> DV.divides g b) /\
             (forall (g: polynomial int). L.memP g facs' ==>
                (exists (d': polynomial int).
                   L.memP d' (FIC.factor_int_complete b p) /\ poly_eq d' g)))
  = MSF.monicize_sqfree_bridge b;             (* square_free (embed_zq (monicize_pos b)) *)
    FIC.factor_int_complete_complete b
