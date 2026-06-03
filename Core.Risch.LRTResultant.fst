module Core.Risch.LRTResultant

(* ================================================================ *)
(*  Rothstein-Trager resultant specialization (plan §5.1.b, final     *)
(*  application of det_eval):                                         *)
(*    R(c) = poly_eval (lrt_resultant_raw p q) c = res_x(p-c*q', q).  *)
(*                                                                   *)
(*  R = resultant over k[z] of (p - z*q') and q (LRT).  Specializing  *)
(*  z := c is poly_eval at c; det_eval pushes it through det, and     *)
(*  the Sylvester ENTRIES specialize coefficient-wise:                *)
(*    poly_eval (embed_const (coeff q i)) c          = coeff q i      *)
(*    poly_eval (p_minus_z_qprime_coeff p q' i) c    = coeff p i      *)
(*                                              - c * coeff q' i.     *)
(*  These entry lemmas are the content here; the full assembly        *)
(*  (eval_matrix (sylvester ...) c = sylvester (p-c*q') q via         *)
(*  det_pointwise_eq, then DetEval.resultant_eval) follows.           *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module LRT = Core.Risch.LRT
module RT  = Core.Polynomial.Root

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Eval

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* Evaluating the constant embedding gives the constant back. *)
let embed_const_eval (#t:Type) {| f: field t |} (c0 c: t)
  : Lemma (poly_eval #t #(cr_of_id t #(id_of_f t)) (LRT.embed_const #t #(cr_of_id t #(id_of_f t)) c0) c = c0)
  = let cr = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    assert (LRT.embed_const #t #cr c0
            == (if c0 = (zero <: t) then (poly_zero #t) else ([c0] <: polynomial t)))
      by (FStar.Tactics.norm [delta_only [`%LRT.embed_const]; primops]; FStar.Tactics.trefl ());
    if c0 = (zero <: t) then begin
      eval_zero #t #cr c;                   (* eval poly_zero c = zero *)
      symmetry c0 (zero <: t)
    end else
      RT.eval_singleton #t #f c0 c          (* poly_eval [c0] c = c0 *)
