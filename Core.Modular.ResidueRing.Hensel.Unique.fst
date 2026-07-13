module Core.Modular.ResidueRing.Hensel.Unique

(* ================================================================ *)
(*  §D (D2c) — HENSEL LIFT UNIQUENESS.                              *)
(*                                                                   *)
(*  Coprime-factor lifting mod pᵏ is UNIQUE given the mod-p          *)
(*  congruence, monic normalization, and a Bézout identity at the    *)
(*  base field.  This is the uniqueness companion to the existence   *)
(*  layer `hensel_lift` (Core.Modular.ResidueRing.Hensel.Multi).     *)
(*                                                                   *)
(*  Structure:                                                       *)
(*    - support privates: poly_mulpk injectivity, quotient degree    *)
(*      bound, to_base/reduce monicity preservation, monic-pair sub  *)
(*      degree drop;                                                  *)
(*    - hensel_step_unique: the one-level uniqueness step (Bézout +   *)
(*      degree argument at the base field);                          *)
(*    - hensel_unique: induction over the tower (level n+1 = pⁿ⁺¹).   *)
(*                                                                   *)
(*  Reuses the reduction/lift/absorption kit from Hensel.Reduce /     *)
(*  Hensel.Lift / Hensel.Multi and the generic monic facts from      *)
(*  Core.Polynomial.Monic (M1 monic_deg_mul, M2 monic_mul_cancel).    *)
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
open Core.Modular.ResidueRing.Hensel.Multi
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.Monic
open Core.Tactics.CanonRing

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  A1 — mulpk injectivity.                                          *)
(* ================================================================ *)

(* scalar:  pᵏ·d ≡ 0 (mod pᵏ⁺¹)  ⇒  d ≡ 0 (mod p). *)
private let mulpk_inj_scalar (p:int{p > 1}) (k:pos) (d: zmod p)
  : Lemma (requires mulpk p k d == zmod_zero (ppow p (k ++ 1)))
          (ensures  d == zmod_zero p)
  = ppow_gt_one p k;
    let pk : pos = ppow p k in
    mulpk_lt p k d;
    (* mulpk p k d == Zm (pk * zv d),  zmod_zero (ppow p (k+1)) == Zm 0. *)
    assert (mulpk p k d == Zm (pk `Prims.op_Star` zv d));
    (* Zm-injectivity: pk * zv d == 0, and pk > 0 forces zv d == 0. *)
    assert (pk `Prims.op_Star` zv d == 0);
    assert (zv d == 0)

(* poly:  poly_mulpk w = 0  ⇒  w = 0   (in (zmod p)[X]). *)
private let poly_mulpk_inj (p:int{p > 1}) (k:pos)
  (w: polynomial (zmod p))
  : Lemma (requires (poly_mulpk p k w)
                    = (poly_zero #(zmod (ppow p (k ++ 1)))))
          (ensures  w = (poly_zero #(zmod p)))
  = let m1 = ppow p (k ++ 1) in
    let aux (i:nat)
      : Lemma (coeff w i = coeff (poly_zero #(zmod p)) i)
      = poly_mulpk_coeff p k w i;                                (* coeff (poly_mulpk w) i == mulpk (coeff w i) *)
        poly_eq_means_equal_coeffs
          (poly_mulpk p k w) (poly_zero #(zmod m1)) i;          (* coeff (poly_mulpk w) i = zmod_zero m1 *)
        (* so mulpk (coeff w i) == zmod_zero m1 *)
        mulpk_inj_scalar p k (coeff w i);                        (* coeff w i == zmod_zero p *)
        H.elim_equatable_laws (zmod p) () in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq w (poly_zero #(zmod p))

(* ================================================================ *)
(*  A6 — quotient degree bound.                                     *)
(* ================================================================ *)

private let quotient_deg_le (p:int{p > 1}) (k:pos)
  (e: polynomial (zmod (ppow p (k ++ 1))))
  : Lemma (deg (poly_quotient p k e) <= deg e)
  = let g = qdiv p k in
    L.map_lemma g e;                                             (* length (map g e) == length e *)
    trim_length_le #(zmod p) (L.map g e)                         (* length (trim (map g e)) <= length (map g e) *)

(* ================================================================ *)
(*  poly_mulpk sends the zero polynomial to zero.                   *)
(* ================================================================ *)

private let poly_mulpk_zero_poly (p:int{p > 1}) (k:pos)
  (w: polynomial (zmod p))
  : Lemma (requires w = (poly_zero #(zmod p)))
          (ensures  (poly_mulpk p k w)
                    = (poly_zero #(zmod (ppow p (k ++ 1)))))
  = let m1 = ppow p (k ++ 1) in
    let aux (i:nat)
      : Lemma (coeff (poly_mulpk p k w) i = coeff (poly_zero #(zmod m1)) i)
      = poly_mulpk_coeff p k w i;                                (* coeff (poly_mulpk w) i == mulpk (coeff w i) *)
        poly_eq_means_equal_coeffs w (poly_zero #(zmod p)) i;    (* coeff w i = zmod_zero p *)
        (* coeff w i == zmod_zero p, so mulpk (coeff w i) == mulpk 0 == 0 *)
        H.elim_equatable_laws (zmod p) ();
        mulpk_zero p k;                                          (* mulpk (zmod_zero p) == zmod_zero m1 *)
        H.elim_equatable_laws (zmod m1) () in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (poly_mulpk p k w) (poly_zero #(zmod m1))

(* ================================================================ *)
(*  reduce preserves monicity and degree.                           *)
(*  (`to_base_monic`, the analogous to_base fact, lives in           *)
(*   Core.Modular.ResidueRing.Hensel.Lift next to to_base_one.)      *)
(* ================================================================ *)

private let reduce_preserves_monic (p:int{p > 1}) (k:pos)
  (g: polynomial (zmod (ppow p (k ++ 1))))
  : Lemma (requires monic g)
          (ensures  monic (poly_reduce p k g) /\
                    deg (poly_reduce p k g) == deg g)
  = ppow_gt_one p k;
    let m1 = ppow p (k ++ 1) in
    let m  = ppow p k in
    let gr = poly_reduce p k g in
    let d  = deg g in
    H.elim_equatable_laws (zmod m1) ();
    H.elim_equatable_laws (zmod m) ();
    last_eq_index g d;
    poly_lc_reveal g;
    assert (coeff g d = (one <: zmod m1));
    poly_reduce_coeff p k g d;
    reduce_step_one p k;
    assert (coeff gr d == zmod_one m);
    assert (not ((zmod_one m) = (zmod_zero m)));   (* m = pᵏ > 1 ⇒ 1 ≠ 0 *)
    L.map_lemma (reduce_step p k) g;
    trim_length_le #(zmod m) (L.map (reduce_step p k) g);
    let _ : squash (deg gr >= d) =
      if deg gr < d then coeff_above_degree gr d else () in
    assert (deg gr == d);
    last_eq_index gr (deg gr);
    poly_lc_reveal gr

(* `sub_high_coeff_zero` and `deg_sub_lt_of_monic_pair` (equal-degree monic
   pair ⇒ difference drops in degree) now live publicly, generic over any
   commutative_ring, in Core.Polynomial.Monic (in scope via open). *)

(* `sub_to_add` (a -- b = c ⇒ a = b + c) now lives publicly, generic over any
   add_comm_group, in Core.Algebra.Helpers (H.sub_to_add). *)

(* ================================================================ *)
(*  Plumbing:  reduce a = reduce b  ⇒  reduce (b -- a) = 0.         *)
(* ================================================================ *)

(* Ring-agnostic collapse (RING-AGNOSTIC congruence chain):
   lhs = rb + rna, rna = -ra, ra = rb  ⇒  lhs = zero.  Abstract over
   {|add_comm_group t|} and invoked ONCE at the concrete poly type — resolves
   the add-group instance once instead of ~6 concrete poly-eq steps. *)
private let reduce_collapse (#t:Type) {| cr: add_comm_group t |} (lhs rb ra rna: t)
  : Lemma (requires lhs = (rb + rna) /\ rna = (- ra) /\ ra = rb)
          (ensures  lhs = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    neg_congruence ra rb;                     (* (- ra) = (- rb) *)
    add_congruence rb rna rb (- ra);          (* rb + rna = rb + (- ra) *)
    add_congruence rb (- ra) rb (- rb);       (* rb + (- ra) = rb + (- rb) *)
    H.x_plus_neg_x rb                          (* rb + (- rb) = zero *)

private let reduce_sub_zero (p:int{p > 1}) (k:pos)
  (a b: polynomial (zmod (ppow p (k ++ 1))))
  : Lemma (requires (poly_reduce p k a) = (poly_reduce p k b))
          (ensures  (poly_reduce p k (b -- a))
                    = (poly_zero #(zmod (ppow p k))))
  = let m = ppow p k in
    let ra = poly_reduce p k a in
    let rb = poly_reduce p k b in
    (* poly-specific reduce homomorphism: reduce (b -- a) = rb + reduce(-a),
       reduce(-a) = -ra.  The remaining collapse is ring-agnostic. *)
    poly_reduce_add p k b (- a);                     (* reduce (b + -a) = rb + reduce(-a) *)
    poly_reduce_neg p k a;                           (* reduce(-a) = - ra *)
    reduce_collapse #(polynomial (zmod m))
      (poly_reduce p k (b -- a)) rb ra (poly_reduce p k (- a))

(* ================================================================ *)
(*  Generic commutative-ring algebra (pure rearrangements).         *)
(* ================================================================ *)

(* FOIL isolating the cross terms and the b·d corner. *)
private let ring_foil (#t:Type) {| cr: commutative_ring t |} (a b c d: t)
  : Lemma (((a + b) * (c + d))
           = (((a * c) + ((a * d) + (b * c))) + (b * d)))
  = assert (((a + b) * (c + d))
            = (((a * c) + ((a * d) + (b * c))) + (b * d)))
      by canon_ring ()

(* Bézout rearrangement:
   u·(s·g + t·h) = g·(s·u − t·v) + t·(v·g + u·h). *)
private let bezout_identity (#a:Type) {| cr: commutative_ring a |}
  (u v g h s t: a)
  : Lemma ((u * ((s * g) + (t * h)))
           = ((g * ((s * u) -- (t * v))) + (t * ((v * g) + (u * h)))))
  = assert ((u * ((s * g) + (t * h)))
            = ((g * ((s * u) -- (t * v))) + (t * ((v * g) + (u * h)))))
      by canon_ring ()

(* Cross-term cancellation (RING-AGNOSTIC, canon_ring):  x = (x+s)+z, z=0 ⇒ s=0.
   Abstract over {|commutative_ring t|} and invoked at the concrete poly type —
   resolves the instance ONCE instead of ~20 concrete poly-eq steps. *)
private let cross_cancel (#t:Type) {| cr: commutative_ring t |} (x s z: t)
  : Lemma (requires x = ((x + s) + z) /\ z = zero)
          (ensures  s = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    add_congruence (x + s) z (x + s) zero;
    assert (((x + s) + zero) = (x + s)) by canon_ring ();
    assert ((((- x) + (x + s))) = s) by canon_ring ();
    assert (((- x) + x) = zero) by canon_ring ();
    add_congruence (- x) (x + s) (- x) x

(* g1·h1 = g2·h2, g2 = g1+pu, h2 = h1+pv, pu·pv = 0 ⇒ (g1·pv)+(pu·h1) = 0. *)
private let cross_vanish (#t:Type) {| cr: commutative_ring t |}
  (g1 h1 g2 h2 pu pv: t)
  : Lemma (requires (g1 * h1) = (g2 * h2) /\ g2 = (g1 + pu) /\ h2 = (h1 + pv)
                    /\ (pu * pv) = zero)
          (ensures  ((g1 * pv) + (pu * h1)) = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    mul_congruence g2 h2 (g1 + pu) (h1 + pv);
    assert (((g1 + pu) * (h1 + pv))
            = (((g1 * h1) + ((g1 * pv) + (pu * h1))) + (pu * pv)))
      by canon_ring ();
    cross_cancel (g1 * h1) ((g1 * pv) + (pu * h1)) (pu * pv)

(* s·gbar1 + t·hbar1 = 1 and v·gbar1 + u·hbar1 = 0 ⇒ u = gbar1·(s·u − t·v). *)
private let u_collapse (#t:Type) {| cr: commutative_ring t |}
  (u v gbar1 hbar1 s tt: t)
  : Lemma (requires ((s * gbar1) + (tt * hbar1)) = one
                    /\ ((v * gbar1) + (u * hbar1)) = zero)
          (ensures  u = (gbar1 * ((s * u) -- (tt * v))))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let w0 = (s * u) -- (tt * v) in
    let xb = (v * gbar1) + (u * hbar1) in
    bezout_identity u v gbar1 hbar1 s tt;
    mul_congruence u ((s * gbar1) + (tt * hbar1)) u one;
    assert ((u * one) = u) by canon_ring ();
    mul_congruence tt xb tt zero;
    H.x_mul_zero tt;
    add_congruence (gbar1 * w0) (tt * xb) (gbar1 * w0) zero;
    H.x_plus_zero (gbar1 * w0)

(* u = gbar1·w0 and w0 = 0 ⇒ u = 0. *)
private let mul_zero_collapse (#t:Type) {| cr: commutative_ring t |}
  (u gbar1 w0: t)
  : Lemma (requires u = (gbar1 * w0) /\ w0 = zero)
          (ensures  u = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    mul_congruence gbar1 w0 gbar1 zero;
    H.x_mul_zero gbar1

(* Equatable four-corner transport (RING-AGNOSTIC): a=b, c=d, a=c ⇒ b=d.
   Abstract over {|equatable t|}, invoked ONCE per equational chain — resolves
   the instance once instead of a per-step symmetry/transitivity ladder. *)
private let transport_bd (#t:Type) {| equatable t |} (a b c d: t)
  : Lemma (requires a = b /\ c = d /\ a = c) (ensures b = d)
  = H.elim_equatable_laws t (); H.trans_for_calc t ()

(* Equatable four-corner transport: a=b, c=d, b=d ⇒ a=c. *)
private let transport_ac (#t:Type) {| equatable t |} (a b c d: t)
  : Lemma (requires a = b /\ c = d /\ b = d) (ensures a = c)
  = H.elim_equatable_laws t (); H.trans_for_calc t ()

(* Bézout transport (RING-AGNOSTIC): g=g', h=h', (s·g')+(tt·h')=o ⇒ (s·g)+(tt·h)=o. *)
private let bezout_transport (#t:Type) {| cr: commutative_ring t |}
  (s tt g g' h h' o: t)
  : Lemma (requires g = g' /\ h = h' /\ ((s * g') + (tt * h')) = o)
          (ensures  ((s * g) + (tt * h)) = o)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    mul_congruence s g s g';
    mul_congruence tt h tt h';
    add_congruence (s * g) (tt * h) (s * g') (tt * h')

(* Absorb the two poly_mulpk cross-terms down to the base field (poly-specific). *)
private let absorb_cross (p:int{p > 1}) (k:pos)
  (g1 h1: polynomial (zmod (ppow p (k ++ 1))))
  (u v: polynomial (zmod p))
  : Lemma
      (requires
        ((g1 * (poly_mulpk p k v)) + ((poly_mulpk p k u) * h1))
        = (poly_zero #(zmod (ppow p (k ++ 1)))))
      (ensures
        ((v * (poly_to_base p (k ++ 1) g1)) + (u * (poly_to_base p (k ++ 1) h1)))
        = (poly_zero #(zmod p)))
  = ppow_gt_one p (k ++ 1);
    let m1 = ppow p (k ++ 1) in
    H.elim_equatable_laws (polynomial (zmod m1)) ();
    let gbar1 = poly_to_base p (k ++ 1) g1 in
    let hbar1 = poly_to_base p (k ++ 1) h1 in
    let pu = poly_mulpk p k u in
    let pv = poly_mulpk p k v in
    let ss : polynomial (zmod m1) = (g1 * pv) + (pu * h1) in
    poly_mulpk_absorb p k u h1;
    poly_mul_commutativity g1 pv;
    poly_mulpk_absorb p k v g1;
    poly_eq_transitivity (g1 * pv) (pv * g1) (poly_mulpk p k (v * gbar1));
    poly_add_congruence (g1 * pv) (pu * h1)
      (poly_mulpk p k (v * gbar1)) (poly_mulpk p k (u * hbar1));
    poly_mulpk_add p k (v * gbar1) (u * hbar1);
    poly_eq_symmetry
      (poly_mulpk p k ((v * gbar1) + (u * hbar1)))
      ((poly_mulpk p k (v * gbar1)) + (poly_mulpk p k (u * hbar1)));
    poly_eq_transitivity ss
      ((poly_mulpk p k (v * gbar1)) + (poly_mulpk p k (u * hbar1)))
      (poly_mulpk p k ((v * gbar1) + (u * hbar1)));
    poly_eq_symmetry ss (poly_mulpk p k ((v * gbar1) + (u * hbar1)));
    poly_eq_transitivity
      (poly_mulpk p k ((v * gbar1) + (u * hbar1))) ss (poly_zero #(zmod m1));
    poly_mulpk_inj p k ((v * gbar1) + (u * hbar1))

(* ================================================================ *)
(*  THE STEP LEMMA — one-level Hensel uniqueness.                   *)
(*                                                                   *)
(*  Given two factorizations of the same polynomial at level pᵏ⁺¹    *)
(*  that agree mod pᵏ, with g₁,g₂ monic of equal degree and a        *)
(*  Bézout identity for the mod-p reductions of g₁,h₁, the two       *)
(*  factorizations coincide.                                         *)
(* ================================================================ *)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let hensel_step_unique (p:int{p > 1}) (k:pos)
  (g1 h1 g2 h2: polynomial (zmod (ppow p (k ++ 1))))
  (s t: polynomial (zmod p))
  : Lemma
      (requires
        (g1 * h1) = (g2 * h2) /\
        (poly_reduce p k g1) = (poly_reduce p k g2) /\
        (poly_reduce p k h1) = (poly_reduce p k h2) /\
        monic g1 /\ monic g2 /\
        ((s * (poly_to_base p (k ++ 1) g1)) + (t * (poly_to_base p (k ++ 1) h1)))
        = (poly_one #(zmod p)))
      (ensures g1 = g2 /\ h1 = h2)
  = ppow_gt_one p k;
    ppow_gt_one p (k ++ 1);
    let m1 = ppow p (k ++ 1) in
    H.elim_equatable_laws (polynomial (zmod m1)) ();
    H.elim_equatable_laws (polynomial (zmod p)) ();
    reduce_preserves_monic p k g1;
    reduce_preserves_monic p k g2;
    degree_well_defined (poly_reduce p k g1) (poly_reduce p k g2);
    let gbar1 = poly_to_base p (k ++ 1) g1 in
    let hbar1 = poly_to_base p (k ++ 1) h1 in
    let dg = g2 -- g1 in
    let dh = h2 -- h1 in
    reduce_sub_zero p k g1 g2;
    reduce_sub_zero p k h1 h2;
    error_reconstruction p k dg;
    error_reconstruction p k dh;
    let u  = poly_quotient p k dg in
    let v  = poly_quotient p k dh in
    let pu = poly_mulpk p k u in
    let pv = poly_mulpk p k v in
    H.sub_to_add g2 g1 pu;
    H.sub_to_add h2 h1 pv;
    poly_mulpk_mul_zero p k u v;                    (* pu*pv = 0 *)
    cross_vanish g1 h1 g2 h2 pu pv;                 (* (g1*pv)+(pu*h1) = 0 *)
    absorb_cross p k g1 h1 u v;                     (* (v*gbar1)+(u*hbar1) = 0 *)
    let w0 = (s * u) -- (t * v) in
    u_collapse u v gbar1 hbar1 s t;                 (* u = gbar1 * w0 *)
    to_base_monic p (k ++ 1) g1;
    quotient_deg_le p k dg;
    deg_sub_lt_of_monic_pair g1 g2;
    let _ : squash (deg w0 < 0) =
      if deg w0 >= 0 then begin
        monic_deg_mul gbar1 w0;
        degree_well_defined u (gbar1 * w0)
      end else () in
    degree_none_poly_eq_zero w0;                    (* w0 = 0 *)
    mul_zero_collapse u gbar1 w0;                   (* u = 0 *)
    poly_mulpk_zero_poly p k u;                     (* pu = 0 *)
    poly_eq_transitivity dg pu (poly_zero #(zmod m1));   (* dg = 0 *)
    sub_zero_implies_eq g2 g1;
    poly_eq_symmetry g2 g1;
    poly_mul_congruence g2 h2 g1 h2;
    poly_eq_transitivity (g1 * h1) (g2 * h2) (g1 * h2);
    monic_mul_cancel g1 h1 h2                        (* h1 = h2 *)
#pop-options

(* `poly_reduce_congr` (poly_reduce respects poly_eq) now lives publicly
   in Core.Modular.ResidueRing.Hensel.Reduce (in scope via open). *)

(* ================================================================ *)
(*  THE INDUCTION — Hensel uniqueness up the tower.                 *)
(*                                                                   *)
(*  Level n+1 = pⁿ⁺¹ (matching Hensel.Multi.hensel_lift's indexing). *)
(*  Base n=0: mod-p injectivity of poly_to_base at level 1.          *)
(*  Step n≥1: reduce the quadruple to level n, invoke IH to get the  *)
(*  mod-pⁿ congruence, then close with hensel_step_unique.           *)
(* ================================================================ *)

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let rec hensel_unique (p:int{p > 1}) (n:nat)
  (g1 h1 g2 h2: polynomial (zmod (ppow p (n ++ 1))))
  (s t: polynomial (zmod p))
  : Lemma
      (requires
        (g1 * h1) = (g2 * h2) /\
        (poly_to_base p (n ++ 1) g1) = (poly_to_base p (n ++ 1) g2) /\
        (poly_to_base p (n ++ 1) h1) = (poly_to_base p (n ++ 1) h2) /\
        monic g1 /\ monic g2 /\
        ((s * (poly_to_base p (n ++ 1) g1)) + (t * (poly_to_base p (n ++ 1) h1)))
        = (poly_one #(zmod p)))
      (ensures g1 = g2 /\ h1 = h2)
      (decreases n)
  = 
  H.elim_equatable_laws (polynomial (zmod p)) ();
  H.trans_for_calc (polynomial (zmod p)) ();
  
  if n = 0 then begin
      (* Base case: level 1, ppow p 1 == p, poly_to_base p 1 is the identity. *)
      ppow_one p;
      poly_to_base_level1 p g1;                     (* poly_to_base p 1 g1 = g1 *)
      poly_to_base_level1 p g2;
      poly_to_base_level1 p h1;
      poly_to_base_level1 p h2
      (* g1 = poly_to_base p 1 g1 = poly_to_base p 1 g2 = g2 *)
    end else begin
      (* Step case n >= 1: reduce to level n = pⁿ. *)
      let g1r = poly_reduce p n g1 in
      let h1r = poly_reduce p n h1 in
      let g2r = poly_reduce p n g2 in
      let h2r = poly_reduce p n h2 in
      let bg1 = poly_to_base p (n ++ 1) g1 in
      let bh1 = poly_to_base p (n ++ 1) h1 in
      let bg2 = poly_to_base p (n ++ 1) g2 in
      let bh2 = poly_to_base p (n ++ 1) h2 in
      let bg1r = poly_to_base p n g1r in
      let bh1r = poly_to_base p n h1r in
      let bg2r = poly_to_base p n g2r in
      let bh2r = poly_to_base p n h2r in
      H.elim_equatable_laws (polynomial (zmod (ppow p n))) ();      
      H.trans_for_calc (polynomial (zmod (ppow p n))) ();
      (* (a) reduced product: g1r*h1r = g2r*h2r.  poly-specific reduce facts +
         one ring-agnostic four-corner transport. *)
      poly_reduce_mul p n g1 h1;                    (* reduce(g1*h1) = g1r*h1r *)
      poly_reduce_mul p n g2 h2;                    (* reduce(g2*h2) = g2r*h2r *)
      poly_reduce_congr p n (g1 * h1) (g2 * h2);    (* reduce(g1*h1) = reduce(g2*h2) *)
      (* (b) reduced base agreement (g and h) *)
      poly_to_base_reduce p n g1;                   (* bg1r = bg1 *)
      poly_to_base_reduce p n g2;                   (* bg2r = bg2 *)
      //transport_ac bg1r bg1 bg2r bg2;               (* bg1r = bg2r *)
      poly_to_base_reduce p n h1;                   (* bh1r = bh1 *)
      poly_to_base_reduce p n h2;                   (* bh2r = bh2 *)
      (* (c) monicity + degree at level n *)
      reduce_preserves_monic p n g1;                (* monic g1r /\ deg g1r == deg g1 *)
      reduce_preserves_monic p n g2;                (* monic g2r /\ deg g2r == deg g2 *)
      (* (d) Bezout at level n *)
      bezout_transport s t bg1r bg1 bh1r bh1 (poly_one #(zmod p));
      (* (e) IH at level n = (n-1)+1 *)
      hensel_unique p (n - 1) g1r h1r g2r h2r s t;  (* ⇒ g1r = g2r /\ h1r = h2r *)
      (* (f) close with the step lemma at level n+1 *)
      hensel_step_unique p n g1 h1 g2 h2 s t
    end
#pop-options
