module Core.Modular.ResidueRing.Hensel.Multi

(* ================================================================ *)
(*  §C/§D — TOWER CONSISTENCY, the two-factor HENSEL ITERATION, and  *)
(*  the MULTI-FACTOR HENSEL LIFT, merged into one module.            *)
(*                                                                   *)
(*  §C (tower): reducing to the base field 𝔽_p is independent of the *)
(*  level you start from —  to_base ∘ reduce_step = to_base.         *)
(*                                                                   *)
(*  §C (iteration): lift a mod-p factorization all the way to        *)
(*  mod-pⁿ⁺¹; induction on n, applying `hensel_lift_step` per level. *)
(*                                                                   *)
(*  §D (multi): iterate the two-factor `hensel_lift` over a LIST of   *)
(*  mod-p factors to lift a whole coprime factorization from ℤ/p to  *)
(*  ℤ/pⁿ⁺¹.                                                           *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Modular.ResidueRing
open Core.Modular.ResidueRing.Hensel.Reduce
open Core.Modular.ResidueRing.Hensel.Lift
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Roots
open FStar.Math.Lemmas

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* ================================================================ *)
(*  §C — tower consistency.                                          *)
(* ================================================================ *)

(* scalar:  to_base (reduce_step a) = to_base a   (both = a mod p). *)
let to_base_reduce (p:int{p > 1}) (k:pos) (a: zmod (ppow p (k ++ 1)))
  : Lemma (to_base p k (reduce_step p k a) == to_base p (k ++ 1) a)
  = ppow_gt_one p k;
    ppow_gt_one p (k ++ 1);
    ppow_pred p k;
    (* reduce_step p k a == Zm (zv a % (ppow p k));  to_base of it == (zv a % (ppow p k)) % p.
       ppow p k == p * ppow p (k-1), so
       (zv a % (p * ppow p (k-1))) % p == zv a % p  by modulo_modulo_lemma. *)
    modulo_modulo_lemma (zv a) p (ppow p (k - 1))

(* poly:  poly_to_base (poly_reduce f) = poly_to_base f   in (zmod p)[X]. *)
let poly_to_base_reduce (p:int{p > 1}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  : Lemma ((poly_to_base p k (poly_reduce p k f))
             = (poly_to_base p (k ++ 1) f))
  = let lhs = poly_to_base p k (poly_reduce p k f) in
    let rhs = poly_to_base p (k ++ 1) f in
    let aux (i:nat)
      : Lemma (coeff #(zmod p) lhs i
               = coeff #(zmod p) rhs i)
      = (* coeff (poly_to_base (poly_reduce f)) i
           == to_base p k (coeff (poly_reduce f) i)        [poly_to_base_coeff @ k]
           == to_base p k (reduce_step (coeff f i))        [poly_reduce_coeff]
           == to_base p (k+1) (coeff f i)                  [to_base_reduce]
           == coeff (poly_to_base f) i                     [poly_to_base_coeff @ k+1] *)
        poly_to_base_coeff p k (poly_reduce p k f) i;
        poly_reduce_coeff p k f i;
        to_base_reduce p k (coeff f i);
        poly_to_base_coeff p (k ++ 1) f i;
        H.elim_equatable_laws (zmod p) () in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* ================================================================ *)
(*  §C — the two-factor HENSEL ITERATION.                           *)
(* ================================================================ *)

(* poly_to_base respects poly_eq. *)
let poly_to_base_congr (p:int{p > 1}) (k:pos)
  (a b: polynomial (zmod (ppow p k)))
  : Lemma (requires a = b)
          (ensures (poly_to_base p k a) = (poly_to_base p k b))
  = let lhs = poly_to_base p k a in
    let rhs = poly_to_base p k b in
    let aux (i:nat)
      : Lemma (coeff #(zmod p) lhs i
               = coeff #(zmod p) rhs i)
      = (* coeff (poly_to_base a) i == to_base (coeff a i)   [poly_to_base_coeff]
           coeff a i == coeff b i                            [poly_eq_means_equal_coeffs]
           to_base is a function: equal args give equal results
           coeff (poly_to_base b) i == to_base (coeff b i)   [poly_to_base_coeff] *)
        poly_to_base_coeff p k a i;
        poly_to_base_coeff p k b i;
        poly_eq_means_equal_coeffs a b i;
        H.elim_equatable_laws (zmod p) () in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* ppow p 1 reduces to p (definitionally: p * ppow p 0 = p * 1). *)
#push-options "--fuel 2"
let ppow_one (p:int{p > 1}) : Lemma (ppow p 1 == p) = ()
#pop-options

(* level-1 identity:  poly_to_base p 1 x  ≡  x   (mod p).
   At k = 1, ppow p 1 == p, so a : fp p has a < p, hence
   to_base p 1 a = a % p = a (small_mod). *)
#push-options "--fuel 2"
let poly_to_base_level1 (p:int{p > 1})
  (x: polynomial (zmod p))
  : Lemma ((poly_to_base p 1 x) = x)
  = ppow_one p;
    let lhs = poly_to_base p 1 x in
    let aux (i:nat)
      : Lemma (coeff #(zmod p) lhs i
               = coeff #(zmod p) x i)
      = (* coeff (poly_to_base p 1 x) i == to_base p 1 (coeff x i)  [poly_to_base_coeff]
           coeff x i : fp (ppow p 1) == fp p, so (coeff x i) < p,
           hence to_base p 1 (coeff x i) = (coeff x i) % p = coeff x i  [small_mod] *)
        poly_to_base_coeff p 1 x i;
        let c = coeff #(zmod p) x i in
        small_mod (zv c) p;
        H.elim_equatable_laws (zmod p) () in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs x
#pop-options

(* Existence postcondition of the Hensel iteration, as an OPAQUE proposition so
   the `exists` never lands in a consumer's SMT context.  Consumers recover the
   existential through `hensel_lift_post_elim`. *)
[@@"opaque_to_smt"]
let hensel_lift_post (p:int{p > 1}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbar hbar: polynomial (zmod p))
  : prop =
  exists (g hh: polynomial (zmod (ppow p (n ++ 1)))).
    f = (g * hh) /\
    (poly_to_base p (n ++ 1) g) = gbar /\
    (poly_to_base p (n ++ 1) hh) = hbar

let hensel_lift_post_elim (p:int{p > 1}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbar hbar: polynomial (zmod p))
  : Lemma (requires hensel_lift_post p n f gbar hbar)
          (ensures
            (exists (g hh: polynomial (zmod (ppow p (n ++ 1)))).
              f = (g * hh) /\
              (poly_to_base p (n ++ 1) g) = gbar /\
              (poly_to_base p (n ++ 1) hh) = hbar))
  = reveal_opaque (`%hensel_lift_post) (hensel_lift_post p n f gbar hbar)

(* THE Hensel iteration (existence of the lifted factorization). *)
let rec hensel_lift (p:int{p > 1}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbar hbar s t: polynomial (zmod p))
  : Lemma
      (requires
        (poly_to_base p (n ++ 1) f) = (gbar * hbar) /\
        ((s * gbar) + (t * hbar)) = (poly_one #(zmod p)))
      (ensures hensel_lift_post p n f gbar hbar)
      (decreases n)
  =
    if n = 0 then begin
      (* Base case n = 0:  f : polynomial (fp (ppow p 1)),  ppow p 1 == p.
         The level-1 identity gives  poly_to_base p 1 z poly_eq z  for any z.
         From the requires:  poly_to_base p 1 f poly_eq gbar*hbar.
         Witnesses: gbar, hbar (well-typed at fp (ppow p 1) since ppow p 1 == p). *)
      ppow_one p;
      (* f poly_eq poly_mul gbar hbar  (level-1 id + requires, trans/sym) *)
      poly_to_base_level1 p f;                       (* poly_to_base p 1 f poly_eq f *)
      poly_eq_symmetry (poly_to_base p 1 f) f;  (* f poly_eq poly_to_base p 1 f *)
      poly_eq_transitivity
        f (poly_to_base p 1 f) (gbar * hbar);
      (* poly_to_base p 1 gbar poly_eq gbar *)
      poly_to_base_level1 p gbar;
      poly_to_base_level1 p hbar;
      introduce exists (g hh: polynomial (zmod (ppow p (n ++ 1)))).
          f = (g * hh) /\
          (poly_to_base p (n ++ 1) g) = gbar /\
          (poly_to_base p (n ++ 1) hh) = hbar
      with gbar hbar
      and ();
      reveal_opaque (`%hensel_lift_post) (hensel_lift_post p n f gbar hbar)
    end
    else begin
      (* Step case n >= 1. *)
      let fn = poly_reduce p n f in                  (* : polynomial (zmod (ppow p n)) *)
      (* Recursion precondition (factorization):
         poly_to_base p n fn poly_eq poly_mul gbar hbar.
         From poly_to_base_reduce:  poly_to_base p n fn poly_eq poly_to_base p (n+1) f,
         and the requires:          poly_to_base p (n+1) f poly_eq gbar*hbar. *)
      poly_to_base_reduce p n f;
      poly_eq_transitivity
        (poly_to_base p n fn) (poly_to_base p (n ++ 1) f)
        (gbar * hbar);
      (* The Bezout requires is unchanged; recurse. *)
      hensel_lift p (n - 1) fn gbar hbar s t;
      (* Recover the bare existential from the opaque postcondition. *)
      hensel_lift_post_elim p (n - 1) fn gbar hbar;
      (* Eliminate the recursion's existential. *)
      eliminate exists (gn hn: polynomial (zmod (ppow p n))).
          fn = (gn * hn) /\
          (poly_to_base p n gn) = gbar /\
          (poly_to_base p n hn) = hbar
      returns hensel_lift_post p n f gbar hbar
      with _h.
      begin
        (* discharge hensel_lift_step's requires *)
        (* (a) poly_reduce p n f poly_eq poly_mul gn hn:  poly_reduce p n f == fn. *)
        (* (already have fn poly_eq poly_mul gn hn in _h) *)
        (* (b) Bezout:
           poly_mul s (poly_to_base p n gn) poly_eq poly_mul s gbar   (mul_congruence, refl s)
           poly_mul t (poly_to_base p n hn) poly_eq poly_mul t hbar
           add_congruence + requires Bezout + transitivity. *)
        poly_eq_reflexivity s;
        poly_eq_reflexivity t;
        poly_mul_congruence
          s (poly_to_base p n gn) s gbar;
        poly_mul_congruence
          t (poly_to_base p n hn) t hbar;
        poly_add_congruence
          (s * (poly_to_base p n gn))
          (t * (poly_to_base p n hn))
          (s * gbar)
          (t * hbar);
        poly_eq_transitivity
          ((s * (poly_to_base p n gn)) + (t * (poly_to_base p n hn)))
          ((s * gbar) + (t * hbar))
          (poly_one #(zmod p));
        hensel_lift_step p n f gn hn s t;
        (* Recover the bare existential from the opaque postcondition. *)
        hensel_lift_step_post_elim p n f gn hn;
        (* Eliminate the step's existential. *)
        eliminate exists (g' h': polynomial (zmod (ppow p (n ++ 1)))).
            (poly_reduce p n g') = gn /\
            (poly_reduce p n h') = hn /\
            f = (g' * h')
        returns hensel_lift_post p n f gbar hbar
        with _hs.
        begin
          (* poly_to_base p (n+1) g' poly_eq gbar:
             poly_to_base p (n+1) g' poly_eq poly_to_base p n (poly_reduce p n g')  [poly_to_base_reduce, sym]
             poly_to_base p n (poly_reduce p n g') poly_eq poly_to_base p n gn       [poly_to_base_congr, since poly_reduce p n g' poly_eq gn]
             poly_to_base p n gn poly_eq gbar                                        [_h] *)
          poly_to_base_reduce p n g';
          poly_eq_symmetry
            (poly_to_base p n (poly_reduce p n g')) (poly_to_base p (n ++ 1) g');
          poly_to_base_congr p n (poly_reduce p n g') gn;
          poly_eq_transitivity
            (poly_to_base p (n ++ 1) g')
            (poly_to_base p n (poly_reduce p n g'))
            (poly_to_base p n gn);
          poly_eq_transitivity
            (poly_to_base p (n ++ 1) g')
            (poly_to_base p n gn)
            gbar;
          (* same for h' *)
          poly_to_base_reduce p n h';
          poly_eq_symmetry
            (poly_to_base p n (poly_reduce p n h')) (poly_to_base p (n ++ 1) h');
          poly_to_base_congr p n (poly_reduce p n h') hn;
          poly_eq_transitivity
            (poly_to_base p (n ++ 1) h')
            (poly_to_base p n (poly_reduce p n h'))
            (poly_to_base p n hn);
          poly_eq_transitivity
            (poly_to_base p (n ++ 1) h')
            (poly_to_base p n hn)
            hbar;
          introduce exists (g hh: polynomial (zmod (ppow p (n ++ 1)))).
              f = (g * hh) /\
              (poly_to_base p (n ++ 1) g) = gbar /\
              (poly_to_base p (n ++ 1) hh) = hbar
          with g' h'
          and ();
          reveal_opaque (`%hensel_lift_post) (hensel_lift_post p n f gbar hbar)
        end
      end
    end

(* ================================================================ *)
(*  §D — MULTI-FACTOR HENSEL LIFT.                                  *)
(* ================================================================ *)

(* ---------------------------------------------------------------- *)
(*  Bézout-per-peel hypothesis, threaded as a list of (s,t) pairs.   *)
(* ---------------------------------------------------------------- *)

(* A Bézout chain for `gbars` is a list of (s,t) pairs, one per
   NON-trivial peel.  At `g_head :: tail` (tail non-empty) the head
   pair certifies  s·g_head + t·(poly_prod tail) ≈ 1  over 𝔽_p, and
   the rest is a chain for `tail`.  The singleton and empty lists need
   no pair (they are the base case). *)
(* A Bézout (s,t) pair over 𝔽_p.  Defined as a named type to avoid the
   `*` tuple constructor colliding with the ring `*` from
   Core.Algebra.Notation. *)
let bez_pair (p:int{p > 1}) : Type0 =
  tuple2 (polynomial (zmod p)) (polynomial (zmod p))

let rec bezout_chain (p:int{p > 1})
  (gbars: list (polynomial (zmod p)))
  (bez: list (bez_pair p))
  : Tot prop (decreases gbars)
  = match gbars with
    | []        -> True
    | [_]       -> True
    | g :: tail ->
      (match bez with
       | []            -> False
       | (s, t) :: brest ->
         ((s * g) + (t * (poly_prod #(zmod p) tail)))
           = (poly_one #(zmod p))
         /\ bezout_chain p tail brest)

(* ---------------------------------------------------------------- *)
(*  Index helper for the per-factor reduction post-condition.        *)
(* ---------------------------------------------------------------- *)

(* poly_prod of a singleton reduces (mod-p) congruence: poly_prod [g] ≈ g. *)
let poly_prod_singleton (p:int{p > 1})
  (g: polynomial (zmod p))
  : Lemma ((poly_prod #(zmod p) [g]) = g)
  =
    H.elim_equatable_laws (zmod p) ();
    (* poly_prod [g] = poly_mul g (poly_prod []) = poly_mul g poly_one *)
    assert (poly_prod #(zmod p) [g]
            == g * (poly_one #(zmod p)))
      by (FStar.Tactics.norm [delta_only [`%poly_prod]; iota; zeta];
          FStar.Tactics.trefl ());
    poly_mul_one g

(* poly_prod of a singleton over the LIFTED ring ≈ the element. *)
let poly_prod_singleton_lift (p:int{p > 1}) (k:pos)
  (g: polynomial (zmod (ppow p k)))
  : Lemma ((poly_prod #(zmod (ppow p k)) [g]) = g)
  =
    H.elim_equatable_laws (zmod (ppow p k)) ();
    assert (poly_prod #(zmod (ppow p k)) [g]
            == g * (poly_one #(zmod (ppow p k))))
      by (FStar.Tactics.norm [delta_only [`%poly_prod]; iota; zeta];
          FStar.Tactics.trefl ());
    poly_mul_one g

(* ---------------------------------------------------------------- *)
(*  THE multi-factor Hensel lift.                                    *)
(* ---------------------------------------------------------------- *)

(* Existence postcondition of the multi-factor Hensel lift, as an OPAQUE
   proposition so the `exists` (and its inner `forall`) never lands in a
   consumer's SMT context.  Consumers recover it through
   `hensel_lift_multi_post_elim`. *)
[@@"opaque_to_smt"]
let hensel_lift_multi_post (p:int{p > 1}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbars: list (polynomial (zmod p)) {Cons? gbars})
  : prop =
  exists (gs: list (polynomial (zmod (ppow p (n ++ 1))))).
    f = (poly_prod #(zmod (ppow p (n ++ 1))) gs) /\
    L.length gs == L.length gbars /\
    (forall (i:nat). i < L.length gbars ==>
       (poly_to_base p (n ++ 1) (L.index gs i)) = (L.index gbars i))

let hensel_lift_multi_post_elim (p:int{p > 1}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbars: list (polynomial (zmod p)) {Cons? gbars})
  : Lemma (requires hensel_lift_multi_post p n f gbars)
          (ensures
            (exists (gs: list (polynomial (zmod (ppow p (n ++ 1))))).
              f = (poly_prod #(zmod (ppow p (n ++ 1))) gs) /\
              L.length gs == L.length gbars /\
              (forall (i:nat). i < L.length gbars ==>
                 (poly_to_base p (n ++ 1) (L.index gs i)) = (L.index gbars i))))
  = reveal_opaque (`%hensel_lift_multi_post) (hensel_lift_multi_post p n f gbars)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let rec hensel_lift_multi (p:int{p > 1}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbars: list (polynomial (zmod p)) {Cons? gbars})
  (bez: list (bez_pair p))
  : Lemma
      (requires
        (poly_to_base p (n ++ 1) f) = (poly_prod #(zmod p) gbars) /\
        bezout_chain p gbars bez)
      (ensures hensel_lift_multi_post p n f gbars)
      (decreases gbars)
  =
    
    match gbars with
    | [g] ->
      (* BASE CASE — singleton.  No two-factor / Bézout needed.
         requires:  poly_to_base f ≈ poly_prod [g] ≈ g.
         witness:   gs = [f].  poly_prod [f] = f * one ≈ f, length 1 = 1,
                    poly_to_base f ≈ g = gbars[0]. *)
      H.elim_equatable_laws (zmod p) ();
      H.elim_equatable_laws (zmod (ppow p (n ++ 1))) ();
      (* (1)  f ≈ poly_prod [f]   over the lifted ring *)
      poly_prod_singleton_lift p (n ++ 1) f;
      poly_eq_symmetry
        (poly_prod #(zmod (ppow p (n ++ 1))) [f]) f;
      (* (2)  poly_to_base f ≈ g  :  poly_to_base f ≈ poly_prod [g] ≈ g *)
      poly_prod_singleton p g;
      poly_eq_transitivity
        (poly_to_base p (n ++ 1) f)
        (poly_prod #(zmod p) [g])
        g;
      introduce exists (gs: list (polynomial (zmod (ppow p (n ++ 1))))).
          f = (poly_prod #(zmod (ppow p (n ++ 1))) gs) /\
          L.length gs == L.length gbars /\
          (forall (i:nat). i < L.length gbars ==>
             (poly_to_base p (n ++ 1) (L.index gs i)) = (L.index gbars i))
      with [f]
      and ();
      reveal_opaque (`%hensel_lift_multi_post) (hensel_lift_multi_post p n f gbars)
    | g_head :: tail ->
      (* STEP CASE — tail non-empty (otherwise we'd have matched [g]). *)
      (* destructure the head Bézout pair.  `bezout_chain p gbars bez`
         forces `bez = (s,t)::brest` here (the [] arm is vacuous). *)
      match bez with
      | [] ->
        (* dead: bezout_chain (g_head::tail) [] reduces to False. *)
        assert (Cons? tail);
        assert False
      | (s, t) :: brest ->
      let prod_tail = poly_prod #(zmod p) tail in
      (* requires gives:  poly_to_base f ≈ poly_prod (g_head::tail)
                         = poly_mul g_head prod_tail.   (poly_prod unfolds.) *)
      (* Apply the TWO-FACTOR Hensel lift:  gbar = g_head, hbar = prod_tail. *)
      hensel_lift p n f g_head prod_tail s t;
      (* Recover the bare existential from the opaque postcondition. *)
      hensel_lift_post_elim p n f g_head prod_tail;
      (* eliminate the two-factor existential *)
      eliminate exists (glift hh: polynomial (zmod (ppow p (n ++ 1)))).
          f = (glift * hh) /\
          (poly_to_base p (n ++ 1) glift) = g_head /\
          (poly_to_base p (n ++ 1) hh) = prod_tail
      returns hensel_lift_multi_post p n f gbars
      with _h.
      begin
        H.elim_equatable_laws (zmod p) ();
        H.elim_equatable_laws (zmod (ppow p (n ++ 1))) ();
        (* RECURSE on hh with tail.
           Recursion requires:  poly_to_base hh ≈ poly_prod tail  (have it: third conjunct)
           and bezout_chain p tail brest  (from bezout_chain p gbars bez). *)
        hensel_lift_multi p n hh tail brest;
        (* Recover the bare existential from the opaque postcondition. *)
        hensel_lift_multi_post_elim p n hh tail;
        eliminate exists (gs_tail: list (polynomial (zmod (ppow p (n ++ 1))))).
            hh = (poly_prod #(zmod (ppow p (n ++ 1))) gs_tail) /\
            L.length gs_tail == L.length tail /\
            (forall (i:nat). i < L.length tail ==>
               (poly_to_base p (n ++ 1) (L.index gs_tail i)) = (L.index tail i))
        returns hensel_lift_multi_post p n f gbars
        with _ht.
        begin
          (* COMBINE:  gs = glift :: gs_tail.
             poly_prod (glift::gs_tail) = poly_mul glift (poly_prod gs_tail).
             f ≈ poly_mul glift hh ≈ poly_mul glift (poly_prod gs_tail). *)
          poly_eq_reflexivity glift;
          poly_mul_congruence
            glift hh
            glift (poly_prod #(zmod (ppow p (n ++ 1))) gs_tail);
          poly_eq_transitivity
            f
            (glift * hh)
            (glift * (poly_prod #(zmod (ppow p (n ++ 1))) gs_tail));
          (* poly_prod (glift::gs_tail) == poly_mul glift (poly_prod gs_tail). *)
          assert (poly_prod #(zmod (ppow p (n ++ 1))) (glift :: gs_tail)
                  == glift * (poly_prod #(zmod (ppow p (n ++ 1))) gs_tail))
            by (FStar.Tactics.norm [delta_only [`%poly_prod]; iota; zeta];
                FStar.Tactics.trefl ());
          (* conjunct 1:  f ≈ poly_prod (glift::gs_tail). *)
          assert (f = (poly_prod #(zmod (ppow p (n ++ 1))) (glift :: gs_tail)));
          (* conjunct 2:  lengths.  length (glift::gs_tail) = 1 + length gs_tail
             = 1 + length tail = length (g_head::tail) = length gbars. *)
          assert (L.length (glift :: gs_tail) == L.length gbars);
          (* conjunct 3:  per-index reduction.
             i = 0  -> poly_to_base glift ≈ g_head = gbars[0]   (two-factor)
             i > 0  -> poly_to_base gs_tail[i-1] ≈ tail[i-1] = gbars[i] (recursion) *)
          introduce forall (i:nat). i < L.length gbars ==>
                      (poly_to_base p (n ++ 1) (L.index (glift :: gs_tail) i))
                        = (L.index gbars i)
          with begin
            introduce i < L.length gbars ==>
                      (poly_to_base p (n ++ 1) (L.index (glift :: gs_tail) i))
                        = (L.index gbars i)
            with _pf. begin
              if i = 0 then
                (* L.index (glift::gs_tail) 0 = glift; L.index gbars 0 = g_head. *)
                ()
              else
                (* L.index (glift::gs_tail) i = L.index gs_tail (i-1);
                   L.index gbars i = L.index tail (i-1). *)
                ()
            end
          end;
          introduce exists (gs: list (polynomial (zmod (ppow p (n ++ 1))))).
              f = (poly_prod #(zmod (ppow p (n ++ 1))) gs) /\
              L.length gs == L.length gbars /\
              (forall (i:nat). i < L.length gbars ==>
                 (poly_to_base p (n ++ 1) (L.index gs i)) = (L.index gbars i))
          with (glift :: gs_tail)
          and ();
          reveal_opaque (`%hensel_lift_multi_post) (hensel_lift_multi_post p n f gbars)
        end
      end
#pop-options
