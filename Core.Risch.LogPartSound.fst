module Core.Risch.LogPartSound

(* ================================================================ *)
(*  C7 — soundness of the vc-explicit FACTORED logarithmic part.     *)
(*                                                                   *)
(*  The LRT log answer for a squarefree denominator, expressed as     *)
(*  Σ_{β : R(β)=0} β·log(gcd(p−β·q', q)), can be REGROUPED by the      *)
(*  ℚ-irreducible factors of the Rothstein-Trager resultant R.  This  *)
(*  module proves that the regrouping is SOUND: for ANY partition of  *)
(*  the denominator's roots (which the factorization of R induces),   *)
(*  the total value of the regrouped answer is unchanged and equals   *)
(*      p / (∏ linears)  =  p / q.                                    *)
(*                                                                   *)
(*  Hence rendering the log part factor-by-factor (linear factors     *)
(*  collapsed to explicit β·log(v) ℚ-terms, higher factors kept as    *)
(*  RootSums) does not change the integral.                          *)
(*                                                                   *)
(*  Chain (= `rt_answer_constructed`'s value chain, but for an        *)
(*  ARBITRARY root-partition — no residue-homogeneity needed):        *)
(*    frac_sum_over_groups p roots groups                             *)
(*      = frac_sum p roots (flatten groups)     [frac_sum_flatten]    *)
(*      = frac_sum p roots roots                 [frac_sum_perm]      *)
(*      = Fraction p (∏ linears)                 [partial_fraction..] *)
(*                                                                   *)
(*  The product relation  ∏ factors = R  (completeness of the         *)
(*  resultant factorization) is the factorizer's obligation           *)
(*  (Zassenhaus/factor_Q completeness, tracked separately); it enters *)
(*  here only as the hypothesis that `flatten groups` re-lists the    *)
(*  full root set.                                                    *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                        *)
(* ================================================================ *)

module L    = FStar.List.Tot
module H    = Core.Algebra.Helpers
module RTS  = Core.Risch.RTSoundness
module RTE  = Core.Risch.RTAnswerEnd
module RT   = Core.Risch.RTAnswer
module RTAF = Core.Risch.RTAnswerForm
module AC   = Core.Risch.AnswerCheck

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Roots
open Core.Fractions
open Core.Risch.RTSoundness

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  Core rendering soundness.  Regrouping the roots into ANY ordered  *)
(*  partition preserves the log-part value = p / (∏ linears).         *)
(* ================================================================ *)
let factored_value_sound (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t) (groups: list (list t))
  : Lemma (requires Cons? roots /\ all_distinct roots /\ deg p < L.length roots /\
                    (forall (g:list t). L.memP g groups ==>
                       (forall (b:t). L.memP b g ==> L.memP b roots)) /\
                    all_distinct (L.flatten groups) /\
                    (forall (b:t). L.memP b (L.flatten groups) <==> L.memP b roots))
          (ensures (let id_p = polynomial_id #t in
                    is_nonzero (poly_prod_linears roots) /\
                    (let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
                     (RTS.frac_sum_over_groups p roots groups)
                       = (Fraction #(polynomial t) #id_p p q))))
  = let id_p = polynomial_id #t in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    prod_linears_nonzero roots;
    let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
    let fsog = RTS.frac_sum_over_groups p roots groups in
    let ffl  = frac_sum p roots (L.flatten groups) in
    let frr  = frac_sum p roots roots in
    RTS.frac_sum_flatten p roots groups;                    (* fsog = ffl *)
    RTE.frac_sum_perm p roots (L.flatten groups) roots;     (* ffl  = frr *)
    partial_fraction_decomposition p roots;                 (* Fraction p q = frr *)
    symmetry (Fraction #(polynomial t) #id_p p q) frr;      (* frr = Fraction p q *)
    transitivity fsog ffl frr;                              (* fsog = frr *)
    transitivity fsog frr (Fraction #(polynomial t) #id_p p q)

(* ================================================================ *)
(*  vc-EXPLICIT term soundness.  A residue-homogeneous group g       *)
(*  (all its roots share one residue value β = residue p roots hd g) *)
(*  — which is exactly what a LINEAR factor of R contributes, β ∈ ℚ  *)
(*  — has value equal to the EXPLICIT logarithmic term                *)
(*      β · log(vc),   vc = gcd(p − β·q', q)  =  vc_group,            *)
(*  i.e. its value IS  log_deriv_term (β, vc)  =  (β·vc') / vc.       *)
(*  So the linear factors render to explicit ℚ log terms with the     *)
(*  correct derivative.  (per_group_eq ∘ group_contribution_is_vc.)  *)
(* ================================================================ *)
let group_vc_explicit_sound (#t:Type) {| f: field t |}
  (p: polynomial t) (roots g: list t)
  : Lemma (requires Cons? g /\ all_distinct g /\ all_distinct roots /\
                    (forall (b:t). L.memP b g ==> L.memP b roots) /\
                    L.memP (L.hd g) roots /\
                    RT.residue_homog_complete p roots g)
          (ensures (RTS.frac_sum p roots g)
                     = (AC.log_deriv_term
                          (RTS.residue p roots (L.hd g), RTAF.vc_group p roots g)))
  = let id_p = polynomial_id #t in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    (* residue-homogeneity per element (needed by per_group_eq). *)
    RT.residue_homog_complete_elim p roots g;
    RTS.per_group_eq p roots g;                         (* gc = frac_sum p roots g *)
    RTAF.group_contribution_eq_log_deriv_term p roots g; (* gc = log_deriv_term (β, vc) *)
    let gc  = RTS.group_contribution p roots g in
    let fs  = RTS.frac_sum p roots g in
    let lt  = AC.log_deriv_term (RTS.residue p roots (L.hd g), RTAF.vc_group p roots g) in
    symmetry gc fs;                                     (* fs = gc *)
    transitivity fs gc lt                               (* fs = lt *)

(* Every group of a residue-homogeneous partition renders to its explicit  *)
(* vc log term.                                                            *)
let rec groups_all_vc_explicit (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t) (groups: list (list t))
  : Lemma (requires all_distinct roots /\
                    (forall (g:list t). L.memP g groups ==>
                       (Cons? g /\ all_distinct g /\
                        (forall (b:t). L.memP b g ==> L.memP b roots) /\
                        L.memP (L.hd g) roots /\
                        RT.residue_homog_complete p roots g)))
          (ensures (forall (g:list t). L.memP g groups ==>
                      (RTS.frac_sum p roots g)
                        = (AC.log_deriv_term
                             (RTS.residue p roots (L.hd g), RTAF.vc_group p roots g))))
          (decreases groups)
  = match groups with
    | []      -> ()
    | g :: gs -> group_vc_explicit_sound p roots g;
                 groups_all_vc_explicit p roots gs

(* ================================================================ *)
(*  C7 CAPSTONE — vc-explicit factored rendering is sound.           *)
(*                                                                   *)
(*  For a residue-homogeneous partition of the denominator's roots   *)
(*  (which the ℚ-linear factorization of the RT resultant R          *)
(*  induces — one class per rational residue β), the log part        *)
(*  renders as a sum of EXPLICIT ℚ terms  β·log(gcd(p−β·q', q))       *)
(*  whose total derivative is exactly p/q:                           *)
(*    (1) Σ over groups of the value  =  Fraction p (∏ linears) = p/q *)
(*    (2) each group's value  =  the explicit log term (β, vc).       *)
(* ================================================================ *)
let vc_explicit_rendering_sound (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t) (groups: list (list t))
  : Lemma (requires Cons? roots /\ all_distinct roots /\ deg p < L.length roots /\
                    all_distinct (L.flatten groups) /\
                    (forall (b:t). L.memP b (L.flatten groups) <==> L.memP b roots) /\
                    (forall (g:list t). L.memP g groups ==>
                       (Cons? g /\ all_distinct g /\
                        (forall (b:t). L.memP b g ==> L.memP b roots) /\
                        L.memP (L.hd g) roots /\
                        RT.residue_homog_complete p roots g)))
          (ensures (let id_p = polynomial_id #t in
                    is_nonzero (poly_prod_linears roots) /\
                    (let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
                     (RTS.frac_sum_over_groups p roots groups)
                       = (Fraction #(polynomial t) #id_p p q)) /\
                    (forall (g:list t). L.memP g groups ==>
                       (RTS.frac_sum p roots g)
                         = (AC.log_deriv_term
                              (RTS.residue p roots (L.hd g), RTAF.vc_group p roots g)))))
  = factored_value_sound p roots groups;
    groups_all_vc_explicit p roots groups
