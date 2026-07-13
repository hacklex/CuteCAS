module Core.Risch.RTAnswerForm

(* ================================================================ *)
(*  RT residue partition  ->  AnswerCheck `log_term` representation.  *)
(*                                                                   *)
(*  Bridges the abstract Rothstein-Trager residue-partition          *)
(*  soundness (`RTAnswerEnd.rt_answer_constructed`) to the concrete   *)
(*  checker answer form (`AnswerCheck.log_term` / `log_part_deriv`).  *)
(*  Each residue class `g` of the partition becomes the log term      *)
(*    ( residue p roots (hd g) ,  VC_g )                              *)
(*  whose `log_deriv_term` is exactly `group_contribution p roots g`, *)
(*  so the folded derivative of the log part is `p / ∏(x - root_i)`.  *)
(*                                                                   *)
(*  FIELD-GENERIC: works over any field `t` (e.g. a splitting field). *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module AC = Core.Risch.AnswerCheck
module RT = Core.Risch.RTAnswer
module RS = Core.Risch.RTSoundness
module RE = Core.Risch.RTAnswerEnd
module RP = Core.Risch.ResiduePartition

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Derivative
open Core.Polynomial.Roots
open Core.Polynomial.GCD
open Core.Fractions

#set-options "--fuel 2 --ifuel 1 --z3rlimit 10"

(* ---------------------------------------------------------------- *)
(*  Intro for the opaque residue-homogeneity-completeness predicate. *)
(* ---------------------------------------------------------------- *)
let residue_homog_complete_intro (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t{all_distinct roots})
  (g: list t{Cons? g /\ L.memP (L.hd g) roots})
  : Lemma (requires
            (forall (b:t). L.memP b g ==> L.memP b roots) /\
            (forall (b:t). L.memP b g ==>
               RS.residue p roots b = RS.residue p roots (L.hd g)) /\
            (forall (b:t). (L.memP b roots /\
               RS.residue p roots b = RS.residue p roots (L.hd g)) ==> L.memP b g))
          (ensures RT.residue_homog_complete p roots g)
  = reveal_opaque (`%RT.residue_homog_complete) (RT.residue_homog_complete p roots g)

(* ---------------------------------------------------------------- *)
(*  Per-group well-formedness carried through the partition.         *)
(* ---------------------------------------------------------------- *)
let group_wf (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t{all_distinct roots}) (g: list t) : prop =
  Cons? g /\ all_distinct g /\
  (forall (b:t). L.memP b g ==> L.memP b roots) /\
  L.memP (L.hd g) roots /\
  RT.residue_homog_complete p roots g

(* ---------------------------------------------------------------- *)
(*  The Rothstein-Trager denominator of one residue class:           *)
(*    VC_g = gcd( p - r_g·(∏(x-root))'  ,  ∏(x-root) ),  r_g ≠ 0-gcd. *)
(*  Nonzero by `group_contribution_is_vc_term`.                      *)
(* ---------------------------------------------------------------- *)
let vc_group (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t) (g: list t)
  : Pure (polynomial t)
    (requires Cons? g /\ all_distinct g /\ all_distinct roots /\
              (forall (b:t). L.memP b g ==> L.memP b roots) /\
              L.memP (L.hd g) roots /\
              RT.residue_homog_complete p roots g)
    (ensures fun v -> is_nonzero v)
  = RT.group_contribution_is_vc_term p roots g;
    poly_gcd ((p -- (poly_scale (RS.residue p roots (L.hd g))
                       (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
             (poly_prod_linears roots)

(* ---------------------------------------------------------------- *)
(*  Every class produced by `residue_partition` is `group_wf`.       *)
(* ---------------------------------------------------------------- *)
let partition_groups_wf (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t{all_distinct roots})
  : Lemma (ensures
            (forall (g:list t). L.memP g (RP.residue_partition p roots) ==>
                                group_wf p roots g))
  = let groups = RP.residue_partition p roots in
    introduce forall (g:list t). L.memP g groups ==> group_wf p roots g
    with introduce L.memP g groups ==> group_wf p roots g
    with _hg. (
      (* The `residue_partition` post (in scope for `groups`) gives, for this g:
           Cons? g, all_distinct g, subset, forward-homogeneity, completeness. *)
      (* head membership: hd g ∈ g ⊆ roots. *)
      assert (L.memP (L.hd g) g);
      residue_homog_complete_intro p roots g
    )

(* ---------------------------------------------------------------- *)
(*  DELIVERABLE 1.  Map a well-formed group list to log terms.       *)
(* ---------------------------------------------------------------- *)
let rec rt_log_terms_aux (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t{all_distinct roots}) (groups: list (list t))
  : Pure (list (AC.log_term #t #f))
    (requires (forall (g:list t). L.memP g groups ==> group_wf p roots g))
    (ensures fun _ -> True)
    (decreases groups)
  = match groups with
    | [] -> []
    | g :: gs ->
        (RS.residue p roots (L.hd g), vc_group p roots g)
          :: rt_log_terms_aux p roots gs

(* Package the RT residue partition as concrete checker log terms. *)
let rt_log_terms (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t{Cons? roots /\ all_distinct roots})
  : list (AC.log_term #t #f)
  = partition_groups_wf p roots;
    rt_log_terms_aux p roots (RP.residue_partition p roots)

(* ---------------------------------------------------------------- *)
(*  DELIVERABLE 2.  The group contribution IS the log-term deriv.     *)
(* ---------------------------------------------------------------- *)
let group_contribution_eq_log_deriv_term (#t:Type) {| f: field t |}
  (p: polynomial t) (roots g: list t)
  : Lemma (requires Cons? g /\ all_distinct g /\ all_distinct roots /\
                    (forall (b:t). L.memP b g ==> L.memP b roots) /\
                    L.memP (L.hd g) roots /\
                    RT.residue_homog_complete p roots g)
          (ensures RS.group_contribution p roots g
                   = AC.log_deriv_term
                       (RS.residue p roots (L.hd g), vc_group p roots g))
  = RT.group_contribution_is_vc_term p roots g

(* ---------------------------------------------------------------- *)
(*  Fold correspondence: `log_part_deriv` of the mapped log terms     *)
(*  equals `answer_deriv` over the same group list (termwise, by      *)
(*  deliverable 2, and `frac_add_cong` congruence — same order).      *)
(* ---------------------------------------------------------------- *)
let rec log_part_deriv_eq_answer_deriv (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t{all_distinct roots}) (groups: list (list t))
  : Lemma (requires (forall (g:list t). L.memP g groups ==> group_wf p roots g))
          (ensures AC.log_part_deriv (rt_log_terms_aux p roots groups)
                   = RS.answer_deriv p roots groups)
          (decreases groups)
  = let id_p = polynomial_id #t in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    match groups with
    | [] -> ()
    | g :: gs ->
        let c  : t = RS.residue p roots (L.hd g) in
        let v  : (vv:polynomial t{is_nonzero vv}) = vc_group p roots g in
        let ld : fraction id_p = AC.log_deriv_term (c, v) in
        let gc : fraction id_p = RS.group_contribution p roots g in
        let lp : fraction id_p = AC.log_part_deriv (rt_log_terms_aux p roots gs) in
        let ad : fraction id_p = RS.answer_deriv p roots gs in
        (* (a) gc = ld  (deliverable 2). *)
        group_contribution_eq_log_deriv_term p roots g;
        symmetry gc ld;                                  (* ld = gc *)
        (* (b) IH: lp = ad. *)
        log_part_deriv_eq_answer_deriv p roots gs;
        (* fraction_add ld lp = fraction_add gc lp = fraction_add gc ad. *)
        RS.frac_add_cong #(polynomial t) #id_p ld gc lp;
        RS.frac_add_cong_r #(polynomial t) #id_p gc lp ad;
        transitivity (fraction_add #(polynomial t) #id_p ld lp)
                     (fraction_add #(polynomial t) #id_p gc lp)
                     (fraction_add #(polynomial t) #id_p gc ad)

(* ---------------------------------------------------------------- *)
(*  DELIVERABLE 3.  Soundness of the RT log part:  the derivative of  *)
(*  Σ residue·log(VC) equals the integrand fraction  p / ∏(x-root).   *)
(* ---------------------------------------------------------------- *)
let rt_log_terms_sound (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t)
  : Lemma (requires Cons? roots /\ all_distinct roots /\ deg p < L.length roots)
          (ensures
            is_nonzero (poly_prod_linears roots) /\
            (let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
             AC.log_part_deriv (rt_log_terms p roots)
               = (Fraction #(polynomial t) #(polynomial_id #t) p q)))
  = let id_p = polynomial_id #t in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    RE.rt_answer_constructed p roots;
    let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
    let groups = RP.residue_partition p roots in
    partition_groups_wf p roots;
    (* rt_log_terms p roots == rt_log_terms_aux p roots groups  (definitional). *)
    log_part_deriv_eq_answer_deriv p roots groups;
    (* chain: log_part_deriv (rt_log_terms …) = answer_deriv p roots groups = Fraction p q. *)
    transitivity (AC.log_part_deriv (rt_log_terms p roots))
                 (RS.answer_deriv p roots groups)
                 (Fraction #(polynomial t) #id_p p q)
