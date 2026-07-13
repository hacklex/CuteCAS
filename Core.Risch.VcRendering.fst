module Core.Risch.VcRendering

(* ================================================================ *)
(*  C7 CAPSTONE — vc-explicit rendering of the logarithmic part,      *)
(*  wired to the CONSTRUCTED residue partition and to the executable  *)
(*  Rothstein-Trager resultant.                                       *)
(*                                                                   *)
(*  Two halves, composed:                                            *)
(*                                                                   *)
(*  (A)  UNCONDITIONAL sound + explicit rendering over the           *)
(*       residue_partition of `roots` (no residue-homogeneity        *)
(*       hypothesis needed — it is DISCHARGED from the partition's    *)
(*       own well-formedness via `partition_groups_wf`):             *)
(*         Σ_groups value  =  Fraction p (∏ linears)  =  p/q         *)
(*         each group's value  =  the explicit log term (β, VC_g).   *)
(*       (`vc_rendering_value_sound`, `vc_rendering_explicit_sound`,  *)
(*        combined in `vc_rendering_theorem`.)                        *)
(*                                                                   *)
(*  (B)  EXECUTABLE-ENUMERATION bridge: every rendered coefficient    *)
(*       β = residue p roots (hd g) is a ROOT of the ℚ-computable RT  *)
(*       resultant  R = lrt_resultant_raw p (∏ linears)  — indeed a   *)
(*       RESIDUE of p/q (`rendered_coeff_is_resultant_root`,          *)
(*       `rendered_coeff_is_residue`) — and hence (given deg R >= 1)  *)
(*       is a root of ONE of R's irreducible factors from            *)
(*       `poly_factorization_exists` (`resultant_factorization_covers`)*)
(*                                                                   *)
(*  HONESTY on the field of definition.  Everything is parametric in  *)
(*  a single field `t`.  When integrating a RATIONAL function, the RT *)
(*  resultant  R ∈ ℚ[z]  is genuinely ℚ-COMPUTABLE and its factors    *)
(*  are ℚ-irreducible (Part B is field-generic and specializes to     *)
(*  ℚ for R).  The residue COEFFICIENTS β, however, are the algebraic *)
(*  roots of R: they need NOT lie in ℚ — they live in the splitting   *)
(*  field of R (= the extension containing `roots`).  So here `t` is  *)
(*  that splitting field, `roots` are its elements, and Part B's      *)
(*  resultant/factorization statements hold over `t` while the        *)
(*  polynomial R itself is defined over the base (ℚ) subfield.  This  *)
(*  is exactly the Rothstein-Trager picture: the log part is          *)
(*  Σ_{R(β)=0} β·log(gcd(p−β·q', q)), a ℚ-computable resultant with    *)
(*  algebraic coefficients.                                          *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                        *)
(* ================================================================ *)

module L    = FStar.List.Tot
module H    = Core.Algebra.Helpers
module RTS  = Core.Risch.RTSoundness
module RTE  = Core.Risch.RTAnswerEnd
module RTAF = Core.Risch.RTAnswerForm
module RP   = Core.Risch.ResiduePartition
module AC   = Core.Risch.AnswerCheck
module LPS  = Core.Risch.LogPartSound
module RR   = Core.Risch.ResidueRoot
module LRT  = Core.Risch.LRT
module PR   = Core.Polynomial.Roots
module IR   = Core.Polynomial.Irreducible
module FE   = Core.Polynomial.FactorizationExists

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Roots
open Core.Polynomial.Derivative
open Core.Polynomial.GCD
open Core.Polynomial.Eval
open Core.Fractions
open Core.Risch.RTSoundness

#set-options "--fuel 2 --ifuel 1 --z3rlimit 20"

(* ================================================================ *)
(*  PART A — sound + explicit vc rendering over the constructed       *)
(*  residue partition.                                                *)
(* ================================================================ *)

(* (A.1)  VALUE soundness: the folded log-part value equals p/q,      *)
(*  UNCONDITIONALLY (residue-homogeneity discharged from the          *)
(*  partition's own well-formedness).                                 *)
let vc_rendering_value_sound (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t)
  : Lemma (requires Cons? roots /\ all_distinct roots /\ deg p < L.length roots)
          (ensures (let id_p = polynomial_id #t in
                    is_nonzero (poly_prod_linears roots) /\
                    (let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
                     (RTS.frac_sum_over_groups p roots (RP.residue_partition p roots))
                       = (Fraction #(polynomial t) #id_p p q))))
  = let groups = RP.residue_partition p roots in
    RTAF.partition_groups_wf p roots;
    RTE.residue_partition_flatten_distinct p roots;
    LPS.factored_value_sound p roots groups

(* (A.2)  EXPLICIT rendering: every partition group renders to its    *)
(*  explicit log term  β·log(VC_g),  β = residue p roots (hd g).      *)
(*  The `group_wf` guard is available for every partition group from  *)
(*  `vc_rendering_groups_wf` below, so this is unconditional in       *)
(*  content.                                                          *)
let vc_rendering_explicit_sound (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t)
  : Lemma (requires all_distinct roots)
          (ensures (forall (g:list t).
                      L.memP g (RP.residue_partition p roots) ==>
                      RTAF.group_wf p roots g ==>
                      (RTS.frac_sum p roots g)
                        = (AC.log_deriv_term
                             (RTS.residue p roots (L.hd g), RTAF.vc_group p roots g))))
  = let groups = RP.residue_partition p roots in
    RTAF.partition_groups_wf p roots;
    LPS.groups_all_vc_explicit p roots groups

(* (A.3)  Every partition group is well-formed (packages the          *)
(*  precondition consumed by A.2's rendering).                        *)
let vc_rendering_groups_wf (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t)
  : Lemma (requires all_distinct roots)
          (ensures (forall (g:list t).
                      L.memP g (RP.residue_partition p roots) ==>
                      RTAF.group_wf p roots g))
  = RTAF.partition_groups_wf p roots

(* ---------------------------------------------------------------- *)
(*  CAPSTONE (A).  The single sound + explicit rendering statement    *)
(*  over the constructed residue partition.                          *)
(* ---------------------------------------------------------------- *)
let vc_rendering_theorem (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t)
  : Lemma (requires Cons? roots /\ all_distinct roots /\ deg p < L.length roots)
          (ensures (let id_p = polynomial_id #t in
                    let groups = RP.residue_partition p roots in
                    is_nonzero (poly_prod_linears roots) /\
                    (let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
                     (RTS.frac_sum_over_groups p roots groups)
                       = (Fraction #(polynomial t) #id_p p q)) /\
                    (forall (g:list t). L.memP g groups ==> RTAF.group_wf p roots g) /\
                    (forall (g:list t). L.memP g groups ==>
                       RTAF.group_wf p roots g ==>
                       (RTS.frac_sum p roots g)
                         = (AC.log_deriv_term
                              (RTS.residue p roots (L.hd g), RTAF.vc_group p roots g)))))
  = vc_rendering_value_sound p roots;
    vc_rendering_groups_wf p roots;
    vc_rendering_explicit_sound p roots

(* ================================================================ *)
(*  PART B — the executable Rothstein-Trager resultant bridge.        *)
(* ================================================================ *)

(* (B.0)  Over a field, a vanishing product of poly-evaluations has a *)
(*  vanishing factor.                                                 *)
let rec eval_prod_zero_factor (#t:Type) {| f: field t |}
  (facs: list (polynomial t)) (c: t)
  : Lemma (requires eval_prod facs c = (zero <: t))
          (ensures (exists (h: polynomial t).
                      L.memP h facs /\ poly_eval h c = (zero <: t)))
          (decreases facs)
  = H.elim_equatable_laws t ();
    match facs with
    | [] -> assert (not ((one <: t) = (zero <: t)))
    | h :: rest ->
        let a = poly_eval h c in
        let b = eval_prod rest c in
        domain_law a b;
        eliminate (a = (zero <: t)) \/ (b = (zero <: t))
        returns (exists (h': polynomial t).
                   L.memP h' facs /\ poly_eval h' c = (zero <: t))
        with _hl.
          introduce exists (h': polynomial t).
                      L.memP h' facs /\ poly_eval h' c = (zero <: t)
          with h and ()
        and _hr. begin
          eval_prod_zero_factor rest c;
          eliminate exists (h': polynomial t).
                      L.memP h' rest /\ poly_eval h' c = (zero <: t)
          returns (exists (h'': polynomial t).
                     L.memP h'' facs /\ poly_eval h'' c = (zero <: t))
          with _.
            introduce exists (h'': polynomial t).
                        L.memP h'' facs /\ poly_eval h'' c = (zero <: t)
            with h' and ()
        end

(* (B.1)  Root transport: if rr | (∏ facs) and rr(c) = 0, then some   *)
(*  factor of facs vanishes at c.                                     *)
let root_of_prod_from_divides (#t:Type) {| f: field t |}
  (rr: polynomial t) (facs: list (polynomial t)) (c: t)
  : Lemma (requires divides rr (PR.poly_prod facs) /\ poly_eval rr c = (zero <: t))
          (ensures (exists (h: polynomial t).
                      L.memP h facs /\ poly_eval h c = (zero <: t)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let m = PR.poly_prod facs in
    assert (exists (k: polynomial t). (m = (rr * k)));
    eliminate exists (k: polynomial t). (m = (rr * k))
    returns (exists (h: polynomial t).
               L.memP h facs /\ poly_eval h c = (zero <: t))
    with _.
    begin
      eval_congruence m (rr * k) c;                 (* eval m c = eval (rr*k) c *)
      eval_mul rr k c;                              (* eval (rr*k) c = eval rr c * eval k c *)
      mul_congruence (poly_eval rr c) (poly_eval k c) (zero <: t) (poly_eval k c);
      H.zero_mul_x (poly_eval k c);                 (* zero * eval k c = zero *)
      eval_poly_prod facs c;                        (* eval m c = eval_prod facs c *)
      assert (eval_prod facs c = (zero <: t));
      eval_prod_zero_factor facs c
    end

(* (B.2)  Every rendered coefficient  β = residue p roots (hd g)  is  *)
(*  a ROOT of the RT resultant  R = lrt_resultant_raw p q,            *)
(*  q = ∏ linears.  (`q` carried refined `deg q >= 1` so `R` is       *)
(*  well-defined in the statement; the caller supplies                *)
(*  q = poly_prod_linears roots with deg = length roots >= 1.)        *)
let rendered_coeff_is_resultant_root (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t) (g: list t) (q: polynomial t{deg q >= 1})
  : Lemma (requires all_distinct roots /\ Cons? g /\ L.memP (L.hd g) roots /\
                    q == poly_prod_linears roots)
          (ensures poly_eval (LRT.lrt_resultant_raw p q)
                             (RTS.residue p roots (L.hd g)) = (zero <: t))
  = H.elim_equatable_laws t ();
    let c = RTS.residue p roots (L.hd g) in
    RTS.residue_implies_gcd_nonconstant p roots c (L.hd g);
    RR.resultant_zero_iff_gcd p q c

(* (B.2')  Semantic restatement: β IS a residue of p/q. *)
let rendered_coeff_is_residue (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t) (g: list t) (q: polynomial t{deg q >= 1})
  : Lemma (requires all_distinct roots /\ Cons? g /\ L.memP (L.hd g) roots /\
                    q == poly_prod_linears roots)
          (ensures RR.is_residue p q (RTS.residue p roots (L.hd g)))
  = let c = RTS.residue p roots (L.hd g) in
    rendered_coeff_is_resultant_root p roots g q;
    RR.residue_iff_resultant_root p q c

(* ---------------------------------------------------------------- *)
(*  CAPSTONE (B).  Factoring the RT resultant R (deg R >= 1) with     *)
(*  `poly_factorization_exists` yields irreducible factors whose      *)
(*  product is an associate of R and whose ROOTS COVER every rendered *)
(*  residue coefficient:  each partition group's β is a root of ONE   *)
(*  of the factors.  This is the executable-enumeration correspondence*)
(*  — the ℚ-irreducible factors of R enumerate the residue classes.   *)
(* ---------------------------------------------------------------- *)
#push-options "--z3rlimit 40"
let resultant_factorization_covers (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t) (q: polynomial t{deg q >= 1})
  : Lemma (requires all_distinct roots /\ q == poly_prod_linears roots /\
                    deg (LRT.lrt_resultant_raw p q) >= 1)
          (ensures (let rr = LRT.lrt_resultant_raw p q in
                    exists (facs: list (polynomial t)).
                      Cons? facs /\
                      (divides (PR.poly_prod facs) rr /\ divides rr (PR.poly_prod facs)) /\
                      (forall (h:polynomial t). L.memP h facs ==> IR.poly_irreducible h) /\
                      (forall (g:list t). L.memP g (RP.residue_partition p roots) ==>
                         (exists (h:polynomial t). L.memP h facs /\
                            poly_eval h (RTS.residue p roots (L.hd g)) = (zero <: t)))))
  = let rr = LRT.lrt_resultant_raw p q in
    let groups = RP.residue_partition p roots in
    FE.poly_factorization_exists rr;
    eliminate exists (facs: list (polynomial t)).
                Cons? facs /\
                (divides (PR.poly_prod facs) rr /\ divides rr (PR.poly_prod facs)) /\
                (forall (h:polynomial t). L.memP h facs ==> IR.poly_irreducible h)
    returns (exists (facs: list (polynomial t)).
               Cons? facs /\
               (divides (PR.poly_prod facs) rr /\ divides rr (PR.poly_prod facs)) /\
               (forall (h:polynomial t). L.memP h facs ==> IR.poly_irreducible h) /\
               (forall (g:list t). L.memP g groups ==>
                  (exists (h:polynomial t). L.memP h facs /\
                     poly_eval h (RTS.residue p roots (L.hd g)) = (zero <: t))))
    with _.
    begin
      introduce forall (g:list t). L.memP g groups ==>
                  (exists (h:polynomial t). L.memP h facs /\
                     poly_eval h (RTS.residue p roots (L.hd g)) = (zero <: t))
      with introduce L.memP g groups ==>
                     (exists (h:polynomial t). L.memP h facs /\
                        poly_eval h (RTS.residue p roots (L.hd g)) = (zero <: t))
      with _hg. begin
        rendered_coeff_is_resultant_root p roots g q;
        root_of_prod_from_divides rr facs (RTS.residue p roots (L.hd g))
      end;
      introduce exists (facs': list (polynomial t)).
                  Cons? facs' /\
                  (divides (PR.poly_prod facs') rr /\ divides rr (PR.poly_prod facs')) /\
                  (forall (h:polynomial t). L.memP h facs' ==> IR.poly_irreducible h) /\
                  (forall (g:list t). L.memP g groups ==>
                     (exists (h:polynomial t). L.memP h facs' /\
                        poly_eval h (RTS.residue p roots (L.hd g)) = (zero <: t)))
      with facs and ()
    end
#pop-options
