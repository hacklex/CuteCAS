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

(* ================================================================ *)
(*  Crystallized generic commutative-ring assembly lemmas.          *)
(*  Each lifts a ring-agnostic equational sub-chain out of the       *)
(*  concrete polynomial (zmod _) type, resolving the poly-over-zmod  *)
(*  instance ONCE at the call site rather than per explicit step.    *)
(* ================================================================ *)

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

(* Base case n = 0.  Split so the ppow p 1 == p type-conversion reasoning
   is isolated in its own VC. *)
#push-options "--fuel 2"
private let hensel_lift_base (p:int{p > 1})
  (f: polynomial (zmod (ppow p (0 ++ 1))))
  (gbar hbar: polynomial (zmod p))
  : Lemma
      (requires (poly_to_base p (0 ++ 1) f) = (gbar * hbar))
      (ensures hensel_lift_post p 0 f gbar hbar)
  = ppow_one p;
    poly_to_base_level1 p f;
    poly_eq_symmetry (poly_to_base p 1 f) f;
    poly_eq_transitivity
      f (poly_to_base p 1 f) (gbar * hbar);
    poly_to_base_level1 p gbar;
    poly_to_base_level1 p hbar;
    introduce exists (g hh: polynomial (zmod (ppow p (0 ++ 1)))).
        f = (g * hh) /\
        (poly_to_base p (0 ++ 1) g) = gbar /\
        (poly_to_base p (0 ++ 1) hh) = hbar
    with gbar hbar
    and ();
    reveal_opaque (`%hensel_lift_post) (hensel_lift_post p 0 f gbar hbar)
#pop-options

(* Step-case combine: from the two eliminated existentials, assemble the
   opaque post.  Split so its VC is small and independent. *)
private let hensel_lift_assemble (p:int{p > 1}) (n:pos)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbar hbar: polynomial (zmod p))
  (gn hn: polynomial (zmod (ppow p n)))
  (g' h': polynomial (zmod (ppow p (n ++ 1))))
  : Lemma
      (requires
        (poly_to_base p n gn) = gbar /\
        (poly_to_base p n hn) = hbar /\
        (poly_reduce p n g') = gn /\
        (poly_reduce p n h') = hn /\
        f = (g' * h'))
      (ensures hensel_lift_post p n f gbar hbar)
  = poly_to_base_reduce p n g';
    poly_to_base_congr p n (poly_reduce p n g') gn;
    eq_bridge4
      (poly_to_base p n (poly_reduce p n g'))
      (poly_to_base p (n ++ 1) g')
      (poly_to_base p n gn)
      gbar;
    poly_to_base_reduce p n h';
    poly_to_base_congr p n (poly_reduce p n h') hn;
    eq_bridge4
      (poly_to_base p n (poly_reduce p n h'))
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

(* Step-case middle: from the reduced factorization gn·hn, run the two-factor
   Hensel step and assemble.  Split so its VC is small and independent. *)
private let hensel_lift_from_reduced (p:int{p > 1}) (n:pos)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbar hbar s t: polynomial (zmod p))
  (gn hn: polynomial (zmod (ppow p n)))
  : Lemma
      (requires
        (poly_reduce p n f) = (gn * hn) /\
        (poly_to_base p n gn) = gbar /\
        (poly_to_base p n hn) = hbar /\
        ((s * gbar) + (t * hbar)) = (poly_one #(zmod p)))
      (ensures hensel_lift_post p n f gbar hbar)
  = bezout_transport
      s t
      (poly_to_base p n gn) (poly_to_base p n hn)
      gbar hbar
      (poly_one #(zmod p));
    hensel_lift_step p n f gn hn s t;
    hensel_lift_step_post_elim p n f gn hn;
    eliminate exists (g' h': polynomial (zmod (ppow p (n ++ 1)))).
        (poly_reduce p n g') = gn /\
        (poly_reduce p n h') = hn /\
        f = (g' * h')
    returns hensel_lift_post p n f gbar hbar
    with _hs.
    hensel_lift_assemble p n f gbar hbar gn hn g' h'

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
    if n = 0 then
      (* Base case n = 0 (isolated VC): ppow p 1 == p, level-1 identity. *)
      hensel_lift_base p f gbar hbar
    else begin
      (* Step case n >= 1. *)
      let fn = poly_reduce p n f in                  (* : polynomial (zmod (ppow p n)) *)
      (* Recursion precondition (factorization):  poly_to_base p n fn = gbar*hbar,
         via poly_to_base_reduce (= poly_to_base p (n+1) f) and the requires. *)
      poly_to_base_reduce p n f;
      eq_trans3
        (poly_to_base p n fn) (poly_to_base p (n ++ 1) f)
        (gbar * hbar);
      (* The Bezout requires is unchanged; recurse. *)
      hensel_lift p (n - 1) fn gbar hbar s t;
      hensel_lift_post_elim p (n - 1) fn gbar hbar;
      eliminate exists (gn hn: polynomial (zmod (ppow p n))).
          fn = (gn * hn) /\
          (poly_to_base p n gn) = gbar /\
          (poly_to_base p n hn) = hbar
      returns hensel_lift_post p n f gbar hbar
      with _h.
      (* Two-factor Hensel step + assemble (isolated VC). *)
      hensel_lift_from_reduced p n f gbar hbar s t gn hn
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

(* ring-agnostic:  b = b' /\ e = a·b  ⇒  e = a·b'. *)
private let mul_left_transport (#t:Type) {| cr: commutative_ring t |}
  (a b b' e : t)
  : Lemma (requires b = b' /\ e = (a * b)) (ensures e = (a * b'))
  = reflexivity a;
    mul_congruence a b a b';
    H.trans2 e (a * b) (a * b')

(* Base case — singleton list.  Split for a small independent VC. *)
#push-options "--fuel 2 --ifuel 2"
private let hensel_lift_multi_base (p:int{p > 1}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (g: polynomial (zmod p))
  : Lemma
      (requires (poly_to_base p (n ++ 1) f) = (poly_prod #(zmod p) [g]))
      (ensures hensel_lift_multi_post p n f [g])
  = H.elim_equatable_laws (zmod p) ();
    H.elim_equatable_laws (zmod (ppow p (n ++ 1))) ();
    poly_prod_singleton_lift p (n ++ 1) f;
    poly_eq_symmetry
      (poly_prod #(zmod (ppow p (n ++ 1))) [f]) f;
    poly_prod_singleton p g;
    eq_trans3
      (poly_to_base p (n ++ 1) f)
      (poly_prod #(zmod p) [g])
      g;
    introduce exists (gs: list (polynomial (zmod (ppow p (n ++ 1))))).
        f = (poly_prod #(zmod (ppow p (n ++ 1))) gs) /\
        L.length gs == L.length [g] /\
        (forall (i:nat). i < L.length [g] ==>
           (poly_to_base p (n ++ 1) (L.index gs i)) = (L.index [g] i))
    with [f]
    and ();
    reveal_opaque (`%hensel_lift_multi_post) (hensel_lift_multi_post p n f [g])
#pop-options

(* Step-case combine — from the head lift (glift,hh) and the tail recursion
   (gs_tail with per-index reduction via idx_pf), assemble the multi post.
   Split for a small independent VC; the per-index tail hypothesis is a
   proof-function argument (no forall in requires). *)
#push-options "--fuel 2 --ifuel 2"
private let hensel_lift_multi_assemble (p:int{p > 1}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (g_head: polynomial (zmod p))
  (tail: list (polynomial (zmod p)))
  (glift hh: polynomial (zmod (ppow p (n ++ 1))))
  (gs_tail: list (polynomial (zmod (ppow p (n ++ 1)))))
  (idx_pf: (i:nat{i < L.length tail /\ i < L.length gs_tail}) ->
     Lemma ((poly_to_base p (n ++ 1) (L.index gs_tail i)) = (L.index tail i)))
  : Lemma
      (requires
        f = (glift * hh) /\
        (poly_to_base p (n ++ 1) glift) = g_head /\
        hh = (poly_prod #(zmod (ppow p (n ++ 1))) gs_tail) /\
        L.length gs_tail == L.length tail)
      (ensures hensel_lift_multi_post p n f (g_head :: tail))
  = mul_left_transport
      glift hh
      (poly_prod #(zmod (ppow p (n ++ 1))) gs_tail)
      f;
    assert (poly_prod #(zmod (ppow p (n ++ 1))) (glift :: gs_tail)
            == glift * (poly_prod #(zmod (ppow p (n ++ 1))) gs_tail))
      by (FStar.Tactics.norm [delta_only [`%poly_prod]; iota; zeta];
          FStar.Tactics.trefl ());
    introduce forall (i:nat). i < L.length (g_head :: tail) ==>
                (poly_to_base p (n ++ 1) (L.index (glift :: gs_tail) i))
                  = (L.index (g_head :: tail) i)
    with introduce _ ==> _
    with _pf.
      (if i = 0 then () else idx_pf (i - 1));
    introduce exists (gs: list (polynomial (zmod (ppow p (n ++ 1))))).
        f = (poly_prod #(zmod (ppow p (n ++ 1))) gs) /\
        L.length gs == L.length (g_head :: tail) /\
        (forall (i:nat). i < L.length (g_head :: tail) ==>
           (poly_to_base p (n ++ 1) (L.index gs i)) = (L.index (g_head :: tail) i))
    with (glift :: gs_tail)
    and ();
    reveal_opaque (`%hensel_lift_multi_post)
      (hensel_lift_multi_post p n f (g_head :: tail))
#pop-options

(* Non-recursive step wrapper: given the tail recursion's opaque post plus the
   head-lift facts, produce the multi post.  Keeps the recursive body's VC small
   by moving the tail-elim + combine into an independent VC. *)
#push-options "--fuel 2 --ifuel 2"
private let hensel_lift_multi_step (p:int{p > 1}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (g_head: polynomial (zmod p))
  (tail: list (polynomial (zmod p)) {Cons? tail})
  (glift hh: polynomial (zmod (ppow p (n ++ 1))))
  : Lemma
      (requires
        hensel_lift_multi_post p n hh tail /\
        f = (glift * hh) /\
        (poly_to_base p (n ++ 1) glift) = g_head)
      (ensures hensel_lift_multi_post p n f (g_head :: tail))
  = hensel_lift_multi_post_elim p n hh tail;
    eliminate exists (gs_tail: list (polynomial (zmod (ppow p (n ++ 1))))).
        hh = (poly_prod #(zmod (ppow p (n ++ 1))) gs_tail) /\
        L.length gs_tail == L.length tail /\
        (forall (i:nat). i < L.length tail ==>
           (poly_to_base p (n ++ 1) (L.index gs_tail i)) = (L.index tail i))
    returns hensel_lift_multi_post p n f (g_head :: tail)
    with _ht.
    hensel_lift_multi_assemble p n f g_head tail glift hh gs_tail
      (fun (i:nat{i < L.length tail /\ i < L.length gs_tail}) -> ())
#pop-options

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
      (* BASE CASE — singleton (isolated VC). *)
      hensel_lift_multi_base p n f g
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
      (* Apply the TWO-FACTOR Hensel lift:  gbar = g_head, hbar = prod_tail. *)
      hensel_lift p n f g_head prod_tail s t;
      hensel_lift_post_elim p n f g_head prod_tail;
      eliminate exists (glift hh: polynomial (zmod (ppow p (n ++ 1)))).
          f = (glift * hh) /\
          (poly_to_base p (n ++ 1) glift) = g_head /\
          (poly_to_base p (n ++ 1) hh) = prod_tail
      returns hensel_lift_multi_post p n f gbars
      with _h.
      begin
        (* RECURSE on hh with tail; then combine (isolated VC). *)
        hensel_lift_multi p n hh tail brest;
        hensel_lift_multi_step p n f g_head tail glift hh
      end
#pop-options
