module Core.Risch.IntegrateExplicit

(* ================================================================ *)
(*  TOP-LEVEL RATIONAL INTEGRATOR CAPSTONE.                           *)
(*                                                                   *)
(*  Every rational function p/q (q <> 0) over a char-zero field has  *)
(*  an ELEMENTARY antiderivative whose derivative is exactly p/q,    *)
(*  and whose LOG PART is genuinely elementarily integrable — each   *)
(*  proper squarefree piece rem_j / d_j has a Rothstein-Trager /     *)
(*  RootSum logarithmic part with derivative rem_j / d_j over a       *)
(*  splitting field (`rt_unconditionally_sound`).                    *)
(*                                                                   *)
(*  This wires two already-proven theorems:                          *)
(*                                                                   *)
(*   (1) `Integrate.rational_integrable p q` :  p/q reduces (over the *)
(*       base field) to a rational part D(R) plus a list of PROPER   *)
(*       squarefree log specs summing to p/q (`elem_integrable`).    *)
(*                                                                   *)
(*   (2) `Integrate.logspec_rt_integrable` :  each such piece is      *)
(*       RT/RootSum integrable over a splitting field                *)
(*       (`rt_unconditionally_sound`, proven in RTUnconditional).    *)
(*                                                                   *)
(*  The NEW content here is the RECURSIVE lift of the per-spec fact  *)
(*  (2) across the whole `logspecs` list, and its packaging into a   *)
(*  single top-level existential (`integrate_explicit_sound`).       *)
(*                                                                   *)
(*  The vc-EXPLICIT log rendering (each piece's log part equals the  *)
(*  explicit  Σ β·log(VC_g)  terms) lives over the SPLITTING FIELD   *)
(*  of d_j and is exposed as the companion `integrate_log_part_      *)
(*  explicit` (= `VcRendering.vc_rendering_theorem`), NOT threaded    *)
(*  into the base-field top-level statement — see the honesty note.  *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                        *)
(* ================================================================ *)

module L    = FStar.List.Tot
module RI   = Core.Risch.RationalIntegrate
module RU   = Core.Risch.RTUnconditional
module IG   = Core.Risch.Integrate
module VC   = Core.Risch.VcRendering
module RTS  = Core.Risch.RTSoundness
module RP   = Core.Risch.ResiduePartition
module RTAF = Core.Risch.RTAnswerForm
module AC   = Core.Risch.AnswerCheck

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Roots
open Core.Polynomial.Irreducible
open Core.Fractions
open Core.Fractions.Derivative

#set-options "--fuel 1 --ifuel 1 --z3rlimit 5"

(* ---------------------------------------------------------------- *)
(*  NEW: recursive lift.  If every spec in `logspecs` is a proper     *)
(*  squarefree piece (`logspec_ok`), then every spec is RT/RootSum    *)
(*  integrable over a splitting field (`rt_unconditionally_sound`).   *)
(*  Uses `Integrate.logspec_rt_integrable` per element.               *)
(* ---------------------------------------------------------------- *)
let rec logspecs_all_rt_sound (#t:Type) {| f: field t |}
  (logspecs: list (RI.log_spec f))
  : Lemma (requires L.for_all RI.logspec_ok logspecs)
          (ensures (forall (s: RI.log_spec f). L.memP s logspecs ==>
                      RU.rt_unconditionally_sound (fst s) (snd s)))
          (decreases logspecs)
  = match logspecs with
    | [] -> ()
    | x :: rest ->
        IG.logspec_rt_integrable x;
        logspecs_all_rt_sound rest

(* ---------------------------------------------------------------- *)
(*  Transparent elimination of `Integrate.elem_integrable` into its   *)
(*  raw existential body (exposes the witnesses to SMT / eliminate).  *)
(* ---------------------------------------------------------------- *)
let elem_integrable_elim (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires IG.elem_integrable p q)
          (ensures
            is_nonzero q /\
            (exists (rr: rational_function f) (logspecs: list (RI.log_spec f)).
               ((fraction_add (rational_deriv rr)
                              (RI.frac_sum_list (L.map RI.log_frac logspecs)))
                  = (Fraction #(polynomial t) #(polynomial_id #t #(id_of_f t)) p
                       (q <: (x:polynomial t{is_nonzero x})))) /\
               L.for_all RI.logspec_ok logspecs))
  = ()

(* ================================================================ *)
(*  CAPSTONE.  Every rational function p/q (q <> 0) over a char-zero  *)
(*  field is elementarily integrable, AND every proper squarefree     *)
(*  piece of its log part is RT/RootSum integrable over a splitting   *)
(*  field.                                                            *)
(* ================================================================ *)
let integrate_explicit_sound (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires char_zero f /\ is_nonzero q)
          (ensures
            (exists (rr: rational_function f) (logspecs: list (RI.log_spec f)).
               (let id_p = polynomial_id #t #(id_of_f t) in
                let qn : (x:polynomial t{is_nonzero x}) = q in
                (fraction_add (rational_deriv rr)
                              (RI.frac_sum_list (L.map RI.log_frac logspecs)))
                  = (Fraction #(polynomial t) #id_p p qn)) /\
               L.for_all RI.logspec_ok logspecs /\
               (forall (s: RI.log_spec f). L.memP s logspecs ==>
                  RU.rt_unconditionally_sound (fst s) (snd s))))
  = let id_p = polynomial_id #t #(id_of_f t) in
    let qn : (x:polynomial t{is_nonzero x}) = q in
    IG.rational_integrable p q;
    elem_integrable_elim p q;
    eliminate exists (rr: rational_function f) (logspecs: list (RI.log_spec f)).
       ((fraction_add (rational_deriv rr)
                      (RI.frac_sum_list (L.map RI.log_frac logspecs)))
          = (Fraction #(polynomial t) #id_p p qn)) /\
       L.for_all RI.logspec_ok logspecs
    returns (exists (rr: rational_function f) (logspecs: list (RI.log_spec f)).
               ((fraction_add (rational_deriv rr)
                              (RI.frac_sum_list (L.map RI.log_frac logspecs)))
                  = (Fraction #(polynomial t) #id_p p qn)) /\
               L.for_all RI.logspec_ok logspecs /\
               (forall (s: RI.log_spec f). L.memP s logspecs ==>
                  RU.rt_unconditionally_sound (fst s) (snd s)))
    with _.
    begin
      logspecs_all_rt_sound logspecs;
      introduce exists (rr': rational_function f) (logspecs': list (RI.log_spec f)).
                  ((fraction_add (rational_deriv rr')
                                 (RI.frac_sum_list (L.map RI.log_frac logspecs')))
                     = (Fraction #(polynomial t) #id_p p qn)) /\
                  L.for_all RI.logspec_ok logspecs' /\
                  (forall (s: RI.log_spec f). L.memP s logspecs' ==>
                     RU.rt_unconditionally_sound (fst s) (snd s))
      with rr logspecs and ()
    end

(* ================================================================ *)
(*  COMPANION — vc-EXPLICIT rendering of one proper squarefree        *)
(*  piece's log part.                                                 *)
(*                                                                   *)
(*  HONESTY on the field of definition.  `integrate_explicit_sound`   *)
(*  lives over the BASE char-zero field: it exhibits the rational-    *)
(*  part reduction  D(R) + Σ_j rm_j/d_j = p/q  and asserts each piece *)
(*  rm_j/d_j is RT-integrable (`rt_unconditionally_sound`), which      *)
(*  itself EXISTENTIALLY quantifies the splitting field of d_j.        *)
(*                                                                   *)
(*  The vc-EXPLICIT terms  Σ_g β·log(VC_g)  can only be written down   *)
(*  once the roots of d_j are named — i.e. OVER THE SPLITTING FIELD.   *)
(*  So the explicit rendering is stated for `rm` over a field `t` in   *)
(*  which the squarefree denominator has SPLIT as ∏(X−root):           *)
(*  `roots` are those (distinct) roots, `d = poly_prod_linears roots`, *)
(*  and the log part folds to the explicit vc terms summing to rm/d.   *)
(*  This is exactly `VcRendering.vc_rendering_theorem`; re-exported     *)
(*  here as the capstone's explicit-log companion.  It is NOT threaded *)
(*  into the base-field top-level statement above, because the vc      *)
(*  terms are not expressible over the base field.                    *)
(* ---------------------------------------------------------------- *)
let integrate_log_part_explicit (#t:Type) {| f: field t |}
  (rm: polynomial t) (roots: list t)
  : Lemma (requires Cons? roots /\ all_distinct roots /\ deg rm < L.length roots)
          (ensures (let id_p = polynomial_id #t in
                    let groups = RP.residue_partition rm roots in
                    is_nonzero (poly_prod_linears roots) /\
                    (let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
                     (RTS.frac_sum_over_groups rm roots groups)
                       = (Fraction #(polynomial t) #id_p rm q)) /\
                    (forall (g:list t). L.memP g groups ==> RTAF.group_wf rm roots g) /\
                    (forall (g:list t). L.memP g groups ==>
                       RTAF.group_wf rm roots g ==>
                       (RTS.frac_sum rm roots g)
                         = (AC.log_deriv_term
                              (RTS.residue rm roots (L.hd g), RTAF.vc_group rm roots g)))))
  = VC.vc_rendering_theorem rm roots
