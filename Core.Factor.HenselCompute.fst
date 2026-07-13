module Core.Factor.HenselCompute

(* ================================================================ *)
(*  M2 · S6 — EXECUTABLE (Tot) multi-factor Hensel lift.            *)
(*                                                                   *)
(*  The existing Hensel machinery proves EXISTENCE of the lifted     *)
(*  factorization (`hensel_lift_step`, `hensel_lift`,                *)
(*  `hensel_lift_multi` are Lemmas).  The witnesses are, however,    *)
(*  computations.  This module exposes the actual COMPUTED lifted    *)
(*  factors as Tot functions and proves their concrete soundness by  *)
(*  reusing the existing proofs.                                     *)
(*                                                                   *)
(*    hensel_step_compute        — one linear Hensel step (level k). *)
(*    hensel_lift_compute        — iterate a two-factor lift 1..n+1. *)
(*    hensel_lift_multi_compute  — lift a whole list of mod-p        *)
(*                                 factors to mod-pⁿ⁺¹.              *)
(*                                                                   *)
(*  Standalone (NOT on build-all).  NO admit / assume / sorry.       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Modular.ResidueRing
open Core.Modular.ResidueRing.Hensel.Reduce
open Core.Modular.ResidueRing.Hensel.Lift
open Core.Modular.ResidueRing.Hensel.Multi
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Roots

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* ================================================================ *)
(*  §1 — the single Hensel step (re-export of the Lift primitives).  *)
(* ================================================================ *)

(* Compute the lifted pair (g',h') of one linear Hensel step. *)
let hensel_step_compute = hensel_lift_step_compute

(* Concrete soundness of the computed pair. *)
let hensel_step_compute_correct = hensel_lift_step_compute_correct

(* ================================================================ *)
(*  §2 — the two-factor lift iterated over levels 1..n+1.            *)
(* ================================================================ *)

(* Coerce a mod-p polynomial to level 1 (ppow p 1 == p). *)
let to_level1 (p:int{p > 1}) (g: polynomial (zmod p))
  : polynomial (zmod (ppow p 1))
  = ppow_one p; g

(* Executable two-factor Hensel iteration: lift the mod-p pair
   (gbar,hbar) all the way to mod-pⁿ⁺¹.  Mirror of `hensel_lift`
   but RETURNING the computed pair. *)
let rec hensel_lift_compute (p:int{p > 1}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbar hbar s t: polynomial (zmod p))
  : Tot (tuple2 (polynomial (zmod (ppow p (n ++ 1))))
                (polynomial (zmod (ppow p (n ++ 1)))))
        (decreases n)
  = if n = 0 then (to_level1 p gbar, to_level1 p hbar)
    else begin
      let fn = poly_reduce p n f in
      let gh = hensel_lift_compute p (n - 1) fn gbar hbar s t in
      hensel_lift_step_compute p n f (fst gh) (snd gh) s t
    end

(* ---------------------------------------------------------------- *)
(*  Crystallized generic equatable-reasoning helpers.  Each lifts a  *)
(*  ring-agnostic equational sub-chain out of the concrete           *)
(*  polynomial (zmod _) type, resolving the poly-over-zmod instance   *)
(*  ONCE at the call site rather than per explicit step.             *)
(* ---------------------------------------------------------------- *)

(* x = y /\ y = z  ⇒  x = z. *)
private let eq_trans3 (#t:Type) {| cr: commutative_ring t |} (x y z : t)
  : Lemma (requires x = y /\ y = z) (ensures x = z)
  = H.trans2 x y z

(* a = b /\ a = c /\ c = d  ⇒  b = d. *)
private let eq_bridge4 (#t:Type) {| cr: commutative_ring t |} (a b c d : t)
  : Lemma (requires a = b /\ a = c /\ c = d) (ensures b = d)
  = symmetry a b;
    H.trans3 b a c d

(* Bézout transport: a = a' /\ b = b' /\ (s·a' + tt·b') = e  ⇒  (s·a + tt·b) = e. *)
private let bezout_transport (#t:Type) {| cr: commutative_ring t |}
  (s tt a b a' b' e : t)
  : Lemma (requires a = a' /\ b = b' /\ ((s * a') + (tt * b')) = e)
          (ensures  ((s * a) + (tt * b)) = e)
  = reflexivity s;
    reflexivity tt;
    mul_congruence s a s a';
    mul_congruence tt b tt b';
    add_congruence (s * a) (tt * b) (s * a') (tt * b');
    H.trans2 ((s * a) + (tt * b)) ((s * a') + (tt * b')) e

(* Base case n = 0 (isolated VC): ppow p 1 == p, level-1 identity. *)
private let hensel_lift_compute_correct_base (p:int{p > 1})
  (f: polynomial (zmod (ppow p (0 ++ 1))))
  (gbar hbar s t: polynomial (zmod p))
  : Lemma
      (requires (poly_to_base p (0 ++ 1) f) = (gbar * hbar))
      (ensures
        (let gh = hensel_lift_compute p 0 f gbar hbar s t in
         poly_eq f ((fst gh) * (snd gh)) /\
         poly_eq (poly_to_base p (0 ++ 1) (fst gh)) gbar /\
         poly_eq (poly_to_base p (0 ++ 1) (snd gh)) hbar))
  = ppow_one p;
    poly_to_base_level1 p f;
    poly_eq_symmetry (poly_to_base p 1 f) f;
    poly_eq_transitivity f (poly_to_base p 1 f) (gbar * hbar);
    poly_to_base_level1 p gbar;
    poly_to_base_level1 p hbar

(* Step case (isolated VC): given the recursion facts about the reduced
   pair (gn,hn), prove the ensures for the computed Hensel-step pair. *)
private let hensel_lift_compute_correct_step (p:int{p > 1}) (n:pos)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbar hbar s t: polynomial (zmod p))
  (gn hn: polynomial (zmod (ppow p n)))
  : Lemma
      (requires
        (poly_reduce p n f) = (gn * hn) /\
        (poly_to_base p n gn) = gbar /\
        (poly_to_base p n hn) = hbar /\
        ((s * gbar) + (t * hbar)) = (poly_one #(zmod p)))
      (ensures
        (let gh = hensel_lift_step_compute p n f gn hn s t in
         poly_eq f ((fst gh) * (snd gh)) /\
         poly_eq (poly_to_base p (n ++ 1) (fst gh)) gbar /\
         poly_eq (poly_to_base p (n ++ 1) (snd gh)) hbar))
  = (* step's Bezout requires (b): s·(to_base gn) + t·(to_base hn) = 1 *)
    bezout_transport
      s t
      (poly_to_base p n gn) (poly_to_base p n hn)
      gbar hbar
      (poly_one #(zmod p));
    hensel_lift_step_compute_correct p n f gn hn s t;
    let gh = hensel_lift_step_compute p n f gn hn s t in
    (* gh: reduce (fst gh) ~ gn, reduce (snd gh) ~ hn, f ~ fst·snd *)
    (* to_base (fst gh) ~ gbar *)
    poly_to_base_reduce p n (fst gh);
    poly_to_base_congr p n (poly_reduce p n (fst gh)) gn;
    eq_bridge4
      (poly_to_base p n (poly_reduce p n (fst gh)))
      (poly_to_base p (n ++ 1) (fst gh))
      (poly_to_base p n gn)
      gbar;
    (* to_base (snd gh) ~ hbar *)
    poly_to_base_reduce p n (snd gh);
    poly_to_base_congr p n (poly_reduce p n (snd gh)) hn;
    eq_bridge4
      (poly_to_base p n (poly_reduce p n (snd gh)))
      (poly_to_base p (n ++ 1) (snd gh))
      (poly_to_base p n hn)
      hbar

(* Concrete soundness of the iterated lift. *)
let rec hensel_lift_compute_correct (p:int{p > 1}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbar hbar s t: polynomial (zmod p))
  : Lemma
      (requires
        (poly_to_base p (n ++ 1) f) = (gbar * hbar) /\
        ((s * gbar) + (t * hbar)) = (poly_one #(zmod p)))
      (ensures
        (let gh = hensel_lift_compute p n f gbar hbar s t in
         poly_eq f ((fst gh) * (snd gh)) /\
         poly_eq (poly_to_base p (n ++ 1) (fst gh)) gbar /\
         poly_eq (poly_to_base p (n ++ 1) (snd gh)) hbar))
      (decreases n)
  =
    if n = 0 then
      hensel_lift_compute_correct_base p f gbar hbar s t
    else begin
      let fn = poly_reduce p n f in
      let gh_rec = hensel_lift_compute p (n - 1) fn gbar hbar s t in
      let gn = fst gh_rec in
      let hn = snd gh_rec in
      (* recursion precondition: poly_to_base p n fn ~ gbar*hbar *)
      poly_to_base_reduce p n f;
      eq_trans3
        (poly_to_base p n fn) (poly_to_base p (n ++ 1) f) (gbar * hbar);
      hensel_lift_compute_correct p (n - 1) fn gbar hbar s t;
      (* gh_rec: fn ~ gn*hn, to_base gn ~ gbar, to_base hn ~ hbar *)
      hensel_lift_compute_correct_step p n f gbar hbar s t gn hn;
      assert (hensel_lift_compute p n f gbar hbar s t
              == hensel_lift_step_compute p n f gn hn s t)
    end

(* ================================================================ *)
(*  §3 — the multi-factor lift over a LIST of mod-p factors.         *)
(* ================================================================ *)

(* Executable multi-factor Hensel lift: compute the list of lifted
   factors.  Mirror of `hensel_lift_multi` but RETURNING the list. *)
let rec hensel_lift_multi_compute (p:int{p > 1}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbars: list (polynomial (zmod p)) {Cons? gbars})
  (bez: list (bez_pair p))
  : Tot (list (polynomial (zmod (ppow p (n ++ 1)))))
        (decreases gbars)
  = match gbars with
    | [_] -> [f]
    | g_head :: tail ->
      (match bez with
       | [] -> [f]  (* dead under `bezout_chain`; keep Tot total *)
       | (s, t) :: brest ->
         let prod_tail = poly_prod #(zmod p) tail in
         let gh = hensel_lift_compute p n f g_head prod_tail s t in
         (fst gh) :: hensel_lift_multi_compute p n (snd gh) tail brest)

(* Product-assembly helper (isolated VC): from f ~ glift·hh and
   hh ~ poly_prod gs_tail, conclude f ~ poly_prod (glift::gs_tail). *)
private let multi_prod_assemble (p:int{p > 1}) (n:nat)
  (f glift hh: polynomial (zmod (ppow p (n ++ 1))))
  (gs_tail: list (polynomial (zmod (ppow p (n ++ 1)))))
  : Lemma
      (requires
        poly_eq f (glift * hh) /\
        poly_eq hh (poly_prod #(zmod (ppow p (n ++ 1))) gs_tail))
      (ensures
        poly_eq f (poly_prod #(zmod (ppow p (n ++ 1))) (glift :: gs_tail)))
  = H.elim_equatable_laws (zmod (ppow p (n ++ 1))) ();
    poly_eq_reflexivity glift;
    poly_mul_congruence glift hh glift (poly_prod #(zmod (ppow p (n ++ 1))) gs_tail);
    poly_eq_transitivity
      f (glift * hh)
      (glift * (poly_prod #(zmod (ppow p (n ++ 1))) gs_tail));
    assert (poly_prod #(zmod (ppow p (n ++ 1))) (glift :: gs_tail)
            == glift * (poly_prod #(zmod (ppow p (n ++ 1))) gs_tail))
      by (FStar.Tactics.norm [delta_only [`%poly_prod]; iota; zeta];
          FStar.Tactics.trefl ())

(* Index-assembly helper (isolated VC): pure list-indexing.  From the head
   fact and the per-index tail proof-fn, conclude the full per-index post. *)
private let multi_index_assemble (p:int{p > 1}) (n:nat)
  (g_head: polynomial (zmod p))
  (tail: list (polynomial (zmod p)))
  (glift: polynomial (zmod (ppow p (n ++ 1))))
  (gs_tail: list (polynomial (zmod (ppow p (n ++ 1))))
              { L.length gs_tail == L.length tail })
  (tl_ok: (i:nat{i < L.length tail}
            -> Lemma (poly_eq (poly_to_base p (n ++ 1) (L.index gs_tail i))
                              (L.index tail i))))
  : Lemma
      (requires
        poly_eq (poly_to_base p (n ++ 1) glift) g_head)
      (ensures
        (forall (i:nat). i < L.length (g_head :: tail) ==>
           poly_eq (poly_to_base p (n ++ 1) (L.index (glift :: gs_tail) i))
                   (L.index (g_head :: tail) i)))
  = introduce forall (i:nat).
        i < L.length (g_head :: tail) ==>
        poly_eq (poly_to_base p (n ++ 1) (L.index (glift :: gs_tail) i))
                (L.index (g_head :: tail) i)
    with
      introduce _ ==> _
      with _pf.
        if i = 0 then ()
        else tl_ok (i - 1)

(* Concrete soundness of the multi-factor lift.  Mirror of
   `hensel_lift_multi` but proving the property for the COMPUTED list. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 120"
let rec hensel_lift_multi_compute_correct (p:int{p > 1}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbars: list (polynomial (zmod p)) {Cons? gbars})
  (bez: list (bez_pair p))
  : Lemma
      (requires
        (poly_to_base p (n ++ 1) f) = (poly_prod #(zmod p) gbars) /\
        bezout_chain p gbars bez)
      (ensures
        (let gs = hensel_lift_multi_compute p n f gbars bez in
         poly_eq f (poly_prod #(zmod (ppow p (n ++ 1))) gs) /\
         L.length gs == L.length gbars /\
         (forall (i:nat). i < L.length gbars ==>
            poly_eq (poly_to_base p (n ++ 1) (L.index gs i)) (L.index gbars i))))
      (decreases gbars)
  =
    match gbars with
    | [g] ->
      H.elim_equatable_laws (zmod p) ();
      H.elim_equatable_laws (zmod (ppow p (n ++ 1))) ();
      poly_prod_singleton_lift p (n ++ 1) f;
      poly_eq_symmetry (poly_prod #(zmod (ppow p (n ++ 1))) [f]) f;
      poly_prod_singleton p g;
      poly_eq_transitivity (poly_to_base p (n ++ 1) f) (poly_prod #(zmod p) [g]) g
    | g_head :: tail ->
      match bez with
      | [] -> assert (Cons? tail); assert False
      | (s, t) :: brest ->
        let prod_tail = poly_prod #(zmod p) tail in
        (* requires: poly_to_base f ~ poly_prod (g_head::tail) = g_head*prod_tail
           and s*g_head + t*prod_tail ~ 1  (head of bezout_chain). *)
        assert (poly_prod #(zmod p) (g_head :: tail)
                == g_head * (poly_prod #(zmod p) tail))
          by (FStar.Tactics.norm [delta_only [`%poly_prod]; iota; zeta];
              FStar.Tactics.trefl ());
        hensel_lift_compute_correct p n f g_head prod_tail s t;
        let gh = hensel_lift_compute p n f g_head prod_tail s t in
        let glift = fst gh in
        let hh = snd gh in
        (* gh: f ~ glift*hh, to_base glift ~ g_head, to_base hh ~ prod_tail *)
        H.elim_equatable_laws (zmod p) ();
        H.elim_equatable_laws (zmod (ppow p (n ++ 1))) ();
        (* recurse on hh with tail *)
        hensel_lift_multi_compute_correct p n hh tail brest;
        let gs_tail = hensel_lift_multi_compute p n hh tail brest in
        (* gs = glift :: gs_tail  (definition of hensel_lift_multi_compute) *)
        multi_prod_assemble p n f glift hh gs_tail;
        let tl_ok (i:nat{i < L.length tail})
          : Lemma (poly_eq (poly_to_base p (n ++ 1) (L.index gs_tail i))
                           (L.index tail i))
          = () in
        multi_index_assemble p n g_head tail glift gs_tail tl_ok
#pop-options
