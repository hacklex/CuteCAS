module Core.Risch.RTUnconditional

(*
   §E capstone (E5/E6) — UNCONDITIONAL Rothstein–Trager soundness.

   For any proper rational integrand p/q over a field t (q squarefree,
   deg p < deg q), there EXISTS a splitting field l — CONSTRUCTED by
   build_splitting_field, not assumed — with a certified embedding
   (e, emb) and the full root list of q, over which the LRT answer's
   derivative equals (emb p)/∏(X−β):

       d/dx [ Σ_c c·log(∏ group_c) ]  =  (emb p) / ∏(X−β)

   with  emb q = e(lc q)·∏(X−β)  part of the certificate (splits_with),
   tying the monic denominator to q itself.  This discharges the
   splitting-field HYPOTHESIS of the tier-2 result rt_answer_constructed;
   no unproven assumptions remain (tier 3 of SPLITTING-FIELD-PLAN.md).
*)

module L  = FStar.List.Tot
module RP = Core.Risch.ResiduePartition

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Roots
open Core.Polynomial.SquareFree
open Core.Fractions
open Core.Risch.RTSoundness
open Core.Risch.RTAnswerEnd
open Core.AlgebraicConstant.SplittingField
open Core.AlgebraicConstant.SplitBuild

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* Refined root-list type, instance pinned via the packed field (the same
   unfold-abbreviation trick as SplittingField.poly_over). *)
unfold let distinct_roots (l: Type0) {| fl: field l |} : Type =
  rs: list l { all_distinct rs }

(* The certified answer over the constructed field. *)
[@@"opaque_to_smt"]
let rt_split_answer (#t:Type) {| f: field t |} (p q: polynomial t)
  (l: Type0) {| fl: field l |}
  (e: t -> l) (emb: polynomial t -> poly_over l #fl)
  (roots: distinct_roots l #fl)
  : prop
  = splits_with q l #fl e emb roots /\
    is_nonzero (poly_prod_linears roots) /\
    ((answer_deriv (emb p) roots (RP.residue_partition (emb p) roots))
       = (Fraction #(polynomial l) #(polynomial_id #l #(id_of_f l))
            (emb p) (poly_prod_linears roots)))

(* The headline proposition: such a field exists. *)
[@@"opaque_to_smt"]
let rt_unconditionally_sound (#t:Type) {| f: field t |} (p q: polynomial t)
  : prop
  = exists (l: Type0) (fl: field l)
      (e: t -> l) (emb: polynomial t -> poly_over l #fl)
      (roots: distinct_roots l #fl).
      rt_split_answer p q l #fl e emb roots

let rt_split_answer_elim (#t:Type) {| f: field t |} (p q: polynomial t)
  (l: Type0) {| fl: field l |}
  (e: t -> l) (emb: polynomial t -> poly_over l #fl)
  (roots: distinct_roots l #fl)
  : Lemma (requires rt_split_answer p q l #fl e emb roots)
          (ensures
            splits_with q l #fl e emb roots /\
            is_nonzero (poly_prod_linears roots) /\
            ((answer_deriv (emb p) roots (RP.residue_partition (emb p) roots))
               = (Fraction #(polynomial l) #(polynomial_id #l #(id_of_f l))
                    (emb p) (poly_prod_linears roots))))
  = reveal_opaque (`%rt_split_answer)
      (rt_split_answer p q l #fl e emb roots)

let rt_unconditionally_sound_elim (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires rt_unconditionally_sound p q)
          (ensures
            exists (l: Type0) (fl: field l)
              (e: t -> l) (emb: polynomial t -> poly_over l #fl)
              (roots: distinct_roots l #fl).
              rt_split_answer p q l #fl e emb roots)
  = reveal_opaque (`%rt_unconditionally_sound)
      (rt_unconditionally_sound #t #f p q)

(* ---------------------------------------------------------------- *)
(*  The instantiation core (packed field as an instance binder).     *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 80"
private let rt_unconditional_core (#t:Type) {| f: field t |} (p q: polynomial t)
  (l: Type0) {| fl: field l |}
  (e: t -> l) (emb: polynomial t -> poly_over l #fl) (roots: list l)
  : Lemma (requires
            deg q >= 1 /\ square_free q /\ deg p < deg q /\
            splits_with q l #fl e emb roots)
          (ensures rt_unconditionally_sound p q)
  = splits_with_elim q l #fl e emb roots;
    is_embedding_elim l #fl e emb;
    (* Cons? roots, all_distinct roots, length roots == deg q (P4);
       deg (emb p) == deg p < deg q == length roots (P3). *)
    rt_answer_constructed #l #fl (emb p) roots;
    let roots_d : distinct_roots l #fl = roots in
    reveal_opaque (`%rt_split_answer)
      (rt_split_answer p q l #fl e emb roots_d);
    reveal_opaque (`%rt_unconditionally_sound)
      (rt_unconditionally_sound #t #f p q);
    introduce exists (l0: Type0).
        (exists (fl0: field l0)
           (e0: t -> l0) (emb0: polynomial t -> poly_over l0 #fl0)
           (roots0: distinct_roots l0 #fl0).
           rt_split_answer p q l0 #fl0 e0 emb0 roots0)
      with l
      and introduce exists (fl0: field l)
            (e0: t -> l) (emb0: polynomial t -> poly_over l #fl0)
            (roots0: distinct_roots l #fl0).
            rt_split_answer p q l #fl0 e0 emb0 roots0
          with fl e emb roots_d and ()
#pop-options

(* ---------------------------------------------------------------- *)
(*  E6 — the headline: unconditional RT soundness.                   *)
(* ---------------------------------------------------------------- *)

let rt_unconditional (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires deg q >= 1 /\ square_free q /\ deg p < deg q)
          (ensures  rt_unconditionally_sound p q)
  = build_splitting_field q;
    splits_elim q;
    eliminate exists (l: Type0) (fl: field l)
        (e: t -> l) (emb: polynomial t -> poly_over l #fl) (roots: list l).
        splits_with q l #fl e emb roots
      returns rt_unconditionally_sound p q
      with _. rt_unconditional_core p q l #fl e emb roots
