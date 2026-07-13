module Core.Modular.ResidueRing.Hensel.MonicLift

(* ================================================================ *)
(*  Degree-controlled MONIC linear Hensel single step + iteration.   *)
(*                                                                   *)
(*  The existing `hensel_lift_step_compute` (Hensel.Lift) adds a RAW *)
(*  correction  pt = poly_mulpk p k (t·δ)  whose degree is unbounded, *)
(*  so the lifted g' is NOT monic.  Completeness (hensel_unique)     *)
(*  needs monic lifted factors.  Here we reduce the g-correction     *)
(*  modulo the monic factor  gbar = poly_to_base g  before lifting,  *)
(*  yielding a degree-controlled monic single step.                  *)
(*                                                                   *)
(*  We do NOT modify the existing green Hensel modules (soundness     *)
(*  depends on them); this is an additive layer that mirrors their    *)
(*  interface so it can later replace the raw step in the completeness *)
(*  pipeline.                                                         *)
(*                                                                   *)
(*  NO admit / assume / sorry in the final version.                  *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.NumberTheory
open Core.Modular.PrimeField
open Core.Modular.ResidueRing
open Core.Modular.ResidueRing.Hensel.Reduce
open Core.Modular.ResidueRing.Hensel.Lift
open Core.Modular.ResidueRing.Hensel.Multi
open Core.Modular.FpZmodBridge
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Monic
open Core.Polynomial.Roots
open Core.Polynomial.SubsetProd
open Core.Polynomial.Div
open Core.FinSum
open FStar.Math.Lemmas
open Core.Tactics.CanonRing

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* ================================================================ *)
(*  §1 — poly_lift preserves monicity and degree.                    *)
(*                                                                   *)
(*  The exact analogue of `to_base_monic` (Hensel.Lift:384), with    *)
(*  lift_step / poly_lift / poly_lift_coeff replacing the base-       *)
(*  reduction versions.  lift_step is the identity int map, so it     *)
(*  sends one ↦ one; the leading coefficient survives (no trim).      *)
(* ================================================================ *)

(* lift_step preserves one (identity int map; zmod_one = Zm 1). *)
let lift_step_one (p:int{p > 1}) (k:pos)
  : Lemma (lift_step p k (zmod_one (ppow p k)) == zmod_one (ppow p (k ++ 1)))
  = ppow_gt_one p k;
    ppow_gt_one p (k ++ 1)

let poly_lift_monic (p:int{p > 1}) (k:pos)
  (g: polynomial (zmod (ppow p k)))
  : Lemma (requires monic g)
          (ensures  monic (poly_lift p k g) /\
                    deg (poly_lift p k g) == deg g)
  = ppow_gt_one p k;
    ppow_gt_one p (k ++ 1);
    let mk = ppow p k in
    let m1 = ppow p (k ++ 1) in
    let lg = poly_lift p k g in
    let d  = deg g in                              (* d >= 0 from monic *)
    H.elim_equatable_laws (zmod mk) ();
    H.elim_equatable_laws (zmod m1) ();
    (* coeff g d == poly_lc g == one == zmod_one mk *)
    last_eq_index g d;
    poly_lc_reveal g;
    assert (coeff g d = (one <: zmod mk));         (* coeff g d == poly_lc g = one *)
    (* coeff lg d == lift_step (coeff g d) == lift_step (zmod_one mk) == zmod_one m1 *)
    poly_lift_coeff p k g d;
    lift_step_one p k;
    assert (coeff lg d == zmod_one m1);
    assert (not ((zmod_one m1) = (zmod_zero m1)));  (* m1 > 1 ⇒ 1 ≠ 0 *)
    (* upper: length lg <= length g, so deg lg <= d *)
    L.map_lemma (lift_step p k) g;
    trim_length_le #(zmod m1) (L.map (lift_step p k) g);
    (* lower: nonzero top coeff at d forces deg lg >= d *)
    let _ : squash (deg lg >= d) =
      if deg lg < d then coeff_above_degree lg d else () in
    assert (deg lg == d);
    (* monic lg: poly_lc lg == coeff lg (deg lg) == coeff lg d = one *)
    last_eq_index lg (deg lg);
    poly_lc_reveal lg

(* ================================================================ *)
(*  §2 — poly_mulpk does not raise degree, and the degree-controlled *)
(*        monic single step.                                          *)
(* ================================================================ *)

(* poly_mulpk = trim (map (mulpk) w), so length <= length w, hence
   deg (poly_mulpk w) <= deg w. *)
let poly_mulpk_deg_le (p:int{p > 1}) (k:pos)
  (w: polynomial (zmod p))
  : Lemma (deg (poly_mulpk p k w) <= deg w)
  = L.map_lemma (mulpk p k) w;                     (* length (map (mulpk) w) == length w *)
    trim_length_le #(zmod (ppow p (k ++ 1))) (L.map (mulpk p k) w)

(* THE monicity of the corrected g-side.  If the correction r has degree
   strictly below deg g, then g' = (poly_lift g) + poly_mulpk r is monic
   of the same degree as g.  (poly_lift preserves lc/degree; poly_mulpk
   does not raise degree; adding a strictly-lower-degree term keeps the
   leading `one`.) *)
let monic_step (p:int{p > 1}) (k:pos)
  (g: polynomial (zmod (ppow p k)))
  (r: polynomial (zmod p))
  : Lemma (requires monic g /\ deg r < deg g)
          (ensures  (let g' = (poly_lift p k g) + (poly_mulpk p k r) in
                     monic g' /\ deg g' == deg g))
  = let lg = poly_lift p k g in
    let pr = poly_mulpk p k r in
    poly_lift_monic p k g;                          (* monic lg /\ deg lg == deg g *)
    poly_mulpk_deg_le p k r;                        (* deg pr <= deg r < deg g == deg lg *)
    (* deg lg == deg g, deg pr < deg lg, so deg (lg+pr)=deg lg, lc(lg+pr)=lc lg=one *)
    poly_add_deg_dominant lg pr (deg lg)

(* ================================================================ *)
(*  §3 — The Bezout regrouping identity (generic commutative ring).  *)
(*                                                                   *)
(*  This is the algebraic heart of the corrected product proof.      *)
(*  Splitting  t·δ = q·ḡ + r  (deg r < deg ḡ) and moving  q·h̄  to the *)
(*  h-side, the combined g-correction collapses back to δ:            *)
(*                                                                   *)
(*     (w·ḡ) + (r·h̄) = δ        where  w = s·δ + q·h̄,               *)
(*                                                                   *)
(*  using  b = q·ḡ + r = t·δ  and the Bezout relation  s·ḡ + t·h̄ = 1. *)
(* ================================================================ *)

private let bezout_regroup (#t:Type) {| cr: commutative_ring t |}
  (ww gg rr hh ss tt dd bb qq : t)
  : Lemma (requires
             bb = ((qq * gg) + rr) /\
             bb = (tt * dd) /\
             ((ss * gg) + (tt * hh)) = one /\
             ww = ((ss * dd) + (qq * hh)))
          (ensures ((ww * gg) + (rr * hh)) = dd)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    (* A0 = (ww*gg)+(rr*hh);  substitute ww = (ss*dd)+(qq*hh)  *)
    mul_congruence ww gg ((ss * dd) + (qq * hh)) gg;
    add_congruence (ww * gg) (rr * hh)
                   (((ss * dd) + (qq * hh)) * gg) (rr * hh);
    (* A1 = (((ss*dd)+(qq*hh))*gg)+(rr*hh) = (ss*dd*gg)+(hh*((qq*gg)+rr))  [ring] *)
    assert ((((ss * dd) + (qq * hh)) * gg) + (rr * hh)
            = ((ss * (dd * gg)) + (hh * ((qq * gg) + rr)))) by canon_ring ();
    (* substitute (qq*gg)+rr = bb  *)
    mul_congruence hh ((qq * gg) + rr) hh bb;
    add_congruence (ss * (dd * gg)) (hh * ((qq * gg) + rr))
                   (ss * (dd * gg)) (hh * bb);
    (* substitute bb = tt*dd  *)
    mul_congruence hh bb hh (tt * dd);
    add_congruence (ss * (dd * gg)) (hh * bb)
                   (ss * (dd * gg)) (hh * (tt * dd));
    (* A4 = (ss*dd*gg)+(hh*(tt*dd)) = dd*((ss*gg)+(tt*hh))  [ring] *)
    assert (((ss * (dd * gg)) + (hh * (tt * dd)))
            = (dd * ((ss * gg) + (tt * hh)))) by canon_ring ();
    (* substitute (ss*gg)+(tt*hh) = one  *)
    mul_congruence dd ((ss * gg) + (tt * hh)) dd one;
    (* dd*one = dd  [ring] *)
    assert ((dd * one) = dd) by canon_ring ()

(* ================================================================ *)
(*  §4 — poly_to_base kills a poly_mulpk correction (mod p).         *)
(*                                                                   *)
(*  mulpk multiplies by pᵏ (k >= 1), which is ≡ 0 (mod p); hence the *)
(*  base reduction of a poly_mulpk correction is the zero polynomial. *)
(* ================================================================ *)

(* scalar:  to_base(pᵏ·a) = 0  (mod p). *)
let to_base_mulpk_scalar_zero (p:int{p > 1}) (k:pos) (a: zmod p)
  : Lemma (to_base p (k ++ 1) (mulpk p k a) == zmod_zero p)
  = ppow_gt_one p k;
    let pk : pos = ppow p k in
    let av = zv a in
    (* zv (mulpk p k a) == pk * av;  to_base = (pk*av) % p;  pk = p * ppow p (k-1). *)
    assert (zv (mulpk p k a) == pk `Prims.op_Star` av);
    ppow_pred p k;                                 (* pk == p * ppow p (k-1) *)
    let q = ppow p (k - 1) in
    assert (pk `Prims.op_Star` av == (q `Prims.op_Star` av) `Prims.op_Star` p);
    cancel_mul_mod (q `Prims.op_Star` av) p        (* ((q*av)*p) % p == 0 *)

(* poly:  poly_to_base (poly_mulpk x) = 0  in (zmod p)[X]. *)
let poly_to_base_mulpk_zero (p:int{p > 1}) (k:pos)
  (x: polynomial (zmod p))
  : Lemma ((poly_to_base p (k ++ 1) (poly_mulpk p k x))
           = (poly_zero #(zmod p)))
  = let lhs = poly_to_base p (k ++ 1) (poly_mulpk p k x) in
    let aux (i:nat)
      : Lemma (coeff lhs i = coeff (poly_zero #(zmod p)) i)
      = poly_to_base_coeff p (k ++ 1) (poly_mulpk p k x) i;
        poly_mulpk_coeff p k x i;
        to_base_mulpk_scalar_zero p k (coeff x i);
        H.elim_equatable_laws (zmod p) () in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs (poly_zero #(zmod p))

(* ================================================================ *)
(*  §5 — Local replicas of the (private) product-assembly helpers.   *)
(*                                                                   *)
(*  cross_absorb / lift_assemble / poly_mulpk_congr are `private` in  *)
(*  Hensel.Lift, so we re-derive verbatim copies here (identical      *)
(*  proofs) to build the corrected product.                          *)
(* ================================================================ *)

(* poly_mulpk respects poly_eq (congruence). *)
private let ml_poly_mulpk_congr (p:int{p > 1}) (k:pos)
  (a b: polynomial (zmod p))
  : Lemma (requires a = b)
          (ensures (poly_mulpk p k a) = (poly_mulpk p k b))
  = let m1 = ppow p (k ++ 1) in
    let la = poly_mulpk p k a in
    let lb = poly_mulpk p k b in
    let aux (i:nat)
      : Lemma (coeff la i = coeff lb i)
      = poly_mulpk_coeff p k a i;
        poly_mulpk_coeff p k b i;
        poly_eq_means_equal_coeffs a b i;
        H.elim_equatable_laws (zmod m1) () in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq la lb

(* The cross product  lg · (poly_mulpk u)  =  poly_mulpk (u · ḡ). *)
private let ml_cross_absorb (p:int{p > 1}) (k:pos)
  (g: polynomial (zmod (ppow p k)))
  (u: polynomial (zmod p))
  : Lemma (((poly_lift p k g) * (poly_mulpk p k u))
           = (poly_mulpk p k (u * (poly_to_base p k g))))
  = let lg  = poly_lift p k g in
    let pu  = poly_mulpk p k u in
    let blg = poly_to_base p (k ++ 1) lg in
    let bg  = poly_to_base p k g in
    poly_mul_commutativity lg pu;
    poly_mulpk_absorb p k u lg;
    poly_eq_transitivity (lg * pu) (pu * lg) (poly_mulpk p k (u * blg));
    poly_to_base_lift p k g;
    poly_eq_reflexivity u;
    poly_mul_congruence u blg u bg;
    ml_poly_mulpk_congr p k (u * blg) (u * bg);
    poly_eq_transitivity
      (lg * pu)
      (poly_mulpk p k (u * blg))
      (poly_mulpk p k (u * bg))

(* product-side collapse (ring-agnostic FOIL identity), verbatim
   copy of the private `lift_assemble` in Hensel.Lift. *)
private let ml_lift_assemble (#t:Type) {| cr: commutative_ring t |}
  (lg lh pt ps ff bb cc q pp : t)
  : Lemma (requires
             (pt * ps) = zero /\
             (lg * ps) = bb /\
             (lh * pt) = cc /\
             q = (bb + cc) /\
             q = pp /\
             (ff + (- (lg * lh))) = pp)
          (ensures  ff = ((lg + pt) * (lh + ps)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    assert (((lg + pt) * (lh + ps))
            = ((lg * lh) + ((lg * ps) + ((lh * pt) + (pt * ps))))) by canon_ring ();
    add_congruence (lh * pt) (pt * ps) cc zero;
    assert ((cc + zero) = cc) by canon_ring ();
    add_congruence (lg * ps) ((lh * pt) + (pt * ps)) bb cc;
    add_congruence (lg * lh) ((lg * ps) + ((lh * pt) + (pt * ps))) (lg * lh) pp;
    add_congruence (lg * lh) pp (lg * lh) (ff + (- (lg * lh)));
    assert (((lg * lh) + (ff + (- (lg * lh)))) = ff) by canon_ring ()

(* ================================================================ *)
(*  §6 — The corrected product identity  f ~ g'·h'.                  *)
(*                                                                   *)
(*  g' = lg + poly_mulpk r,   h' = lh + poly_mulpk (s·δ + q·h̄),      *)
(*  with the divmod split  t·δ = q·ḡ + r.  Mirrors `lift_product`    *)
(*  but routes the g-side/h-side collapse through `bezout_regroup`.  *)
(* ================================================================ *)

private let monic_product (p:int{p > 1}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  (g h: polynomial (zmod (ppow p k)))
  (s t q r: polynomial (zmod p))
  : Lemma
      (requires
        (poly_reduce p k f) = (g * h) /\
        ((s * (poly_to_base p k g)) + (t * (poly_to_base p k h)))
          = (poly_one #(zmod p)) /\
        (t * (poly_quotient p k (f + (- ((poly_lift p k g) * (poly_lift p k h))))))
          = ((q * (poly_to_base p k g)) + r))
      (ensures
        poly_eq f
          ((poly_lift p k g + poly_mulpk p k r)
           * (poly_lift p k h + poly_mulpk p k
                ((s * (poly_quotient p k
                        (f + (- ((poly_lift p k g) * (poly_lift p k h))))))
                 + (q * (poly_to_base p k h))))))
  = let m1 = ppow p (k ++ 1) in
    let lg = poly_lift p k g in
    let lh = poly_lift p k h in
    let gbar = poly_to_base p k g in
    let hbar = poly_to_base p k h in
    let e : polynomial (zmod m1) = f + (- (lg * lh)) in
    let dd = poly_quotient p k e in
    let w : polynomial (zmod p) = (s * dd) + (q * hbar) in
    let pr = poly_mulpk p k r in
    let pw = poly_mulpk p k w in
    let bb = poly_mulpk p k (w * gbar) in
    let cc = poly_mulpk p k (r * hbar) in
    let sum : polynomial (zmod p) = (w * gbar) + (r * hbar) in
    H.elim_equatable_laws (polynomial (zmod p)) ();
    H.elim_equatable_laws (polynomial (zmod m1)) ();
    (* one #(polynomial (zmod p)) reduces to poly_one — bridge the Bezout form *)
    assert ((one <: polynomial (zmod p)) == (poly_one #(zmod p)));
    (* fact1: pr·pw = 0 *)
    poly_mulpk_mul_zero p k r w;
    (* fact2: lg·pw = bb ;  fact3: lh·pr = cc *)
    ml_cross_absorb p k g w;
    ml_cross_absorb p k h r;
    (* bb + cc = poly_mulpk sum *)
    poly_mulpk_add p k (w * gbar) (r * hbar);
    poly_eq_symmetry (poly_mulpk p k sum) (bb + cc);
    (* sum = dd  (the Bezout regrouping) *)
    bezout_regroup #(polynomial (zmod p)) w gbar r hbar s t dd (t * dd) q;
    ml_poly_mulpk_congr p k sum dd;
    (* e = poly_mulpk dd *)
    hensel_error_reduces p k f g h;
    error_reconstruction p k e;
    poly_eq_symmetry e (poly_mulpk p k dd);
    (* chain:  bb+cc = poly_mulpk sum = poly_mulpk dd = e *)
    poly_eq_transitivity (bb + cc) (poly_mulpk p k sum) (poly_mulpk p k dd);
    poly_eq_transitivity (bb + cc) (poly_mulpk p k dd) e;
    (* assemble *)
    ml_lift_assemble #(polynomial (zmod m1)) lg lh pr pw f bb cc (bb + cc) e

(* ================================================================ *)
(*  §7 — Base reduction of a lifted+corrected factor is unchanged.   *)
(*                                                                   *)
(*  poly_to_base ((poly_lift g) + poly_mulpk r) = poly_to_base g,    *)
(*  because base-reducing the lift gives back ḡ and base-reducing a  *)
(*  poly_mulpk correction gives 0.                                    *)
(* ================================================================ *)

private let to_base_correction (p:int{p > 1}) (k:pos)
  (g: polynomial (zmod (ppow p k)))
  (r: polynomial (zmod p))
  : Lemma ((poly_to_base p (k ++ 1) ((poly_lift p k g) + (poly_mulpk p k r)))
           = (poly_to_base p k g))
  = let lg = poly_lift p k g in
    let pr = poly_mulpk p k r in
    let gbar = poly_to_base p k g in
    let blg = poly_to_base p (k ++ 1) lg in
    let bpr = poly_to_base p (k ++ 1) pr in
    poly_to_base_add p (k ++ 1) lg pr;       (* to_base(lg+pr) = blg + bpr *)
    poly_to_base_lift p k g;                 (* blg = gbar *)
    poly_to_base_mulpk_zero p k r;           (* bpr = 0 *)
    poly_add_congruence blg bpr gbar (poly_zero #(zmod p));
    poly_add_zero gbar;                      (* gbar + 0 = gbar *)
    poly_eq_transitivity
      (poly_to_base p (k ++ 1) (lg + pr))
      (blg + bpr)
      (gbar + (poly_zero #(zmod p)));
    poly_eq_transitivity
      (poly_to_base p (k ++ 1) (lg + pr))
      (gbar + (poly_zero #(zmod p)))
      gbar

(* ================================================================ *)
(*  §8 — THE degree-controlled MONIC Hensel single step + soundness. *)
(*                                                                   *)
(*  Given the reduction/Bezout preconditions AND a divmod split      *)
(*    t·δ = q·ḡ + r  with  deg r < deg ḡ,  the corrected pair         *)
(*    g' = (lift g) + poly_mulpk r                                    *)
(*    h' = (lift h) + poly_mulpk (s·δ + q·h̄)                          *)
(*  multiplies back to f, keeps the base reductions (ḡ, h̄), and — the *)
(*  point of the correction — g' is MONIC (deg g' = deg g).          *)
(* ================================================================ *)

let monic_lift_step_compute (p:int{p > 1}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  (g h: polynomial (zmod (ppow p k)))
  (s t: polynomial (zmod p))
  (q r: polynomial (zmod p))
  : tuple2 (polynomial (zmod (ppow p (k ++ 1))))
           (polynomial (zmod (ppow p (k ++ 1))))
  = let lg = poly_lift p k g in
    let lh = poly_lift p k h in
    let dd = poly_quotient p k (f + (- (lg * lh))) in
    let hbar = poly_to_base p k h in
    let gc = lg + poly_mulpk p k r in
    let hc = lh + poly_mulpk p k ((s * dd) + (q * hbar)) in
    (gc, hc)

let monic_lift_step_correct (p:int{p > 1}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  (g h: polynomial (zmod (ppow p k)))
  (s t: polynomial (zmod p))
  (q r: polynomial (zmod p))
  : Lemma
      (requires
        (poly_reduce p k f) = (g * h) /\
        ((s * (poly_to_base p k g)) + (t * (poly_to_base p k h)))
          = (poly_one #(zmod p)) /\
        monic g /\
        (t * (poly_quotient p k (f + (- ((poly_lift p k g) * (poly_lift p k h))))))
          = ((q * (poly_to_base p k g)) + r) /\
        deg r < deg (poly_to_base p k g))
      (ensures
        (let gh = monic_lift_step_compute p k f g h s t q r in
         poly_eq f ((fst gh) * (snd gh)) /\
         (poly_to_base p (k ++ 1) (fst gh)) = (poly_to_base p k g) /\
         (poly_to_base p (k ++ 1) (snd gh)) = (poly_to_base p k h) /\
         monic (fst gh)))
  = let lg = poly_lift p k g in
    let lh = poly_lift p k h in
    let dd = poly_quotient p k (f + (- (lg * lh))) in
    let hbar = poly_to_base p k h in
    let w = (s * dd) + (q * hbar) in
    (* product:  f ~ g'·h' *)
    monic_product p k f g h s t q r;
    (* base reductions preserved *)
    to_base_correction p k g r;
    to_base_correction p k h w;
    (* monicity:  deg r < deg ḡ = deg g  ⇒  g' monic *)
    to_base_monic p k g;                     (* deg (poly_to_base p k g) == deg g *)
    monic_step p k g r

(* ================================================================ *)
(*  §9 — Division by a MONIC divisor over 𝔽_p = zmod p (p prime).    *)
(*                                                                   *)
(*  zmod p is a field for prime p, but the field instance lives on   *)
(*  the isomorphic carrier fp p.  We transport `poly_divmod` across   *)
(*  the fp≅zmod bridge (poly_fz / poly_zf): divide in (fp p)[X] and   *)
(*  carry quotient/remainder back.  Monicity of the divisor keeps     *)
(*  deg gbar >= 0, so the degree bound  deg r < deg gbar  survives.   *)
(* ================================================================ *)

(* poly_fz does not raise degree (trim of a coeff-map). *)
let poly_fz_deg_le (#p:int{is_prime p}) (x: polynomial (fp p))
  : Lemma (deg (poly_fz x) <= deg x)
  = L.map_lemma (fz #p) x;
    trim_length_le #(zmod p) (L.map (fz #p) x)

let zmod_monic_divmod (p:int{is_prime p})
  (b gbar: polynomial (zmod p))
  : Pure (tuple2 (polynomial (zmod p)) (polynomial (zmod p)))
         (requires monic gbar)
         (ensures fun res -> b = ((gbar * (fst res)) + (snd res)) /\
                             deg (snd res) < deg gbar)
  = let bf = poly_zf b in
    let gf = poly_zf gbar in
    let qr = poly_divmod bf gf in
    let qf = fst qr in
    let rf = snd qr in
    let q  = poly_fz qf in
    let r  = poly_fz rf in
    H.elim_equatable_laws (polynomial (zmod p)) ();
    H.trans_for_calc (polynomial (zmod p)) ();
    (* divisor is monic ⇒ deg gf == deg gbar >= 0, so divmod's degree bound fires *)
    poly_zf_monic gbar;                       (* monic gf /\ deg gf == deg gbar *)
    poly_fz_deg_le rf;                         (* deg r <= deg rf < deg gf == deg gbar *)
    (* --- homomorphism chain:  b = (gbar*q) + r --- *)
    (* poly_fz bf = b *)
    poly_fz_zf b;                              (* poly_fz (poly_zf b) = b *)
    poly_eq_symmetry (poly_fz bf) b;           (* b = poly_fz bf *)
    (* poly_fz bf = poly_fz ((gf*qf)+rf)  (from divmod correctness bf = (gf*qf)+rf) *)
    poly_fz_congr bf ((gf * qf) + rf);
    (* poly_fz ((gf*qf)+rf) = poly_fz (gf*qf) + r *)
    poly_fz_add (gf * qf) rf;
    (* poly_fz (gf*qf) = (poly_fz gf) * q *)
    poly_fz_mul gf qf;
    poly_eq_reflexivity r;
    poly_add_congruence (poly_fz (gf * qf)) r ((poly_fz gf) * q) r;
    (* poly_fz gf = gbar *)
    poly_fz_zf gbar;                           (* poly_fz (poly_zf gbar) = gbar *)
    poly_eq_reflexivity q;
    poly_mul_congruence (poly_fz gf) q gbar q;
    poly_add_congruence ((poly_fz gf) * q) r (gbar * q) r;
    (q, r)

(* ================================================================ *)
(*  §10 — THE self-contained MONIC Hensel single step (prime p).     *)
(*                                                                   *)
(*  Mirrors `hensel_lift_step_compute` (f g h s t ↦ (g',h')) — no    *)
(*  externally-supplied divmod witnesses — but produces a MONIC g'.  *)
(*  The remainder r = (t·δ) mod ḡ is computed by `zmod_monic_divmod`. *)
(* ================================================================ *)

let monic_lift_step (p:int{is_prime p}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  (g: polynomial (zmod (ppow p k)) {monic g})
  (h: polynomial (zmod (ppow p k)))
  (s t: polynomial (zmod p))
  : tuple2 (polynomial (zmod (ppow p (k ++ 1))))
           (polynomial (zmod (ppow p (k ++ 1))))
  = let lg = poly_lift p k g in
    let lh = poly_lift p k h in
    let dd = poly_quotient p k (f + (- (lg * lh))) in
    let gbar = poly_to_base p k g in
    to_base_monic p k g;                       (* monic gbar — divmod precondition *)
    let qr = zmod_monic_divmod p (t * dd) gbar in
    monic_lift_step_compute p k f g h s t (fst qr) (snd qr)

let monic_lift_step_sound (p:int{is_prime p}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  (g: polynomial (zmod (ppow p k)) {monic g})
  (h: polynomial (zmod (ppow p k)))
  (s t: polynomial (zmod p))
  : Lemma
      (requires
        (poly_reduce p k f) = (g * h) /\
        ((s * (poly_to_base p k g)) + (t * (poly_to_base p k h)))
          = (poly_one #(zmod p)))
      (ensures
        (let gh = monic_lift_step p k f g h s t in
         poly_eq f ((fst gh) * (snd gh)) /\
         (poly_to_base p (k ++ 1) (fst gh)) = (poly_to_base p k g) /\
         (poly_to_base p (k ++ 1) (snd gh)) = (poly_to_base p k h) /\
         monic (fst gh)))
  = let lg = poly_lift p k g in
    let lh = poly_lift p k h in
    let dd = poly_quotient p k (f + (- (lg * lh))) in
    let gbar = poly_to_base p k g in
    to_base_monic p k g;                       (* monic gbar *)
    H.elim_equatable_laws (polynomial (zmod p)) ();
    H.trans_for_calc (polynomial (zmod p)) ();
    let qr = zmod_monic_divmod p (t * dd) gbar in
    let q = fst qr in
    let r = snd qr in
    (* divmod:  (t·δ) = (gbar·q) + r,  deg r < deg gbar.  Commute to (q·gbar). *)
    poly_mul_commutativity gbar q;             (* gbar·q = q·gbar *)
    poly_eq_reflexivity r;
    poly_add_congruence (gbar * q) r (q * gbar) r;  (* (gbar·q)+r = (q·gbar)+r *)
    poly_eq_transitivity (t * dd) ((gbar * q) + r) ((q * gbar) + r);
    monic_lift_step_correct p k f g h s t q r

(* Monicity of the lifted g' is UNCONDITIONAL: it needs only  monic g  (via
   the divmod's degree bound  deg r < deg ḡ = deg g), NOT the reduction /
   Bezout preconditions.  This lets the level-iterator maintain the monic
   invariant inside a Tot return-type refinement. *)
let monic_lift_step_preserves_monic (p:int{is_prime p}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  (g: polynomial (zmod (ppow p k)) {monic g})
  (h: polynomial (zmod (ppow p k)))
  (s t: polynomial (zmod p))
  : Lemma (ensures monic (fst (monic_lift_step p k f g h s t)))
  = let lg = poly_lift p k g in
    let lh = poly_lift p k h in
    let dd = poly_quotient p k (f + (- (lg * lh))) in
    let gbar = poly_to_base p k g in
    to_base_monic p k g;                       (* monic gbar /\ deg gbar == deg g *)
    let qr = zmod_monic_divmod p (t * dd) gbar in
    (* divmod: deg (snd qr) < deg gbar == deg g *)
    monic_step p k g (snd qr)                   (* monic (lg + poly_mulpk (snd qr)) *)

(* ================================================================ *)
(*  §11 — Two-factor MONIC lift iterated over levels 1..n+1.         *)
(*                                                                   *)
(*  Mirror of `hensel_lift_compute` (HenselCompute) but each level   *)
(*  uses the degree-controlled monic step, and the returned first    *)
(*  factor is MONIC (carried in the Tot return-type refinement).     *)
(* ================================================================ *)

(* ppow p 1 == p. *)
#push-options "--fuel 2"
let ml_ppow_one (p:int{p > 1}) : Lemma (ppow p 1 == p) = ()
#pop-options

(* Coerce a mod-p polynomial to level 1 (ppow p 1 == p). *)
let to_level1 (p:int{p > 1}) (g: polynomial (zmod p))
  : polynomial (zmod (ppow p 1))
  = ml_ppow_one p; g

(* monicity survives the level-1 coercion (same value, ppow p 1 == p). *)
let monic_to_level1 (p:int{p > 1}) (g: polynomial (zmod p) {monic g})
  : Lemma (monic (to_level1 p g))
  = ml_ppow_one p

let rec monic_hensel_lift_compute (p:int{is_prime p}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbar: polynomial (zmod p) {monic gbar})
  (hbar s t: polynomial (zmod p))
  : Tot (gh: tuple2 (polynomial (zmod (ppow p (n ++ 1))))
                    (polynomial (zmod (ppow p (n ++ 1))))
         { monic (fst gh) })
        (decreases n)
  = if n = 0 then begin
      ml_ppow_one p;
      monic_to_level1 p gbar;
      (to_level1 p gbar, to_level1 p hbar)
    end
    else begin
      let fn = poly_reduce p n f in
      let gh = monic_hensel_lift_compute p (n - 1) fn gbar hbar s t in
      let g' = fst gh in
      let h' = snd gh in
      monic_lift_step_preserves_monic p n f g' h' s t;
      monic_lift_step p n f g' h' s t
    end

(* Generic equatable glue (local replicas of HenselCompute's private helpers). *)
private let ml_eq_trans3 (#a:Type) {| cr: commutative_ring a |} (x y z : a)
  : Lemma (requires x = y /\ y = z) (ensures x = z)
  = H.trans2 x y z

private let ml_bezout_transport (#a:Type) {| cr: commutative_ring a |}
  (s tt u v u' v' e : a)
  : Lemma (requires u = u' /\ v = v' /\ ((s * u') + (tt * v')) = e)
          (ensures  ((s * u) + (tt * v)) = e)
  = reflexivity s;
    reflexivity tt;
    mul_congruence s u s u';
    mul_congruence tt v tt v';
    add_congruence (s * u) (tt * v) (s * u') (tt * v');
    H.trans2 ((s * u) + (tt * v)) ((s * u') + (tt * v')) e

(* Concrete soundness of the iterated monic two-factor lift. *)
let rec monic_hensel_lift_compute_correct (p:int{is_prime p}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbar: polynomial (zmod p) {monic gbar})
  (hbar s t: polynomial (zmod p))
  : Lemma
      (requires
        (poly_to_base p (n ++ 1) f) = (gbar * hbar) /\
        ((s * gbar) + (t * hbar)) = (poly_one #(zmod p)))
      (ensures
        (let gh = monic_hensel_lift_compute p n f gbar hbar s t in
         poly_eq f ((fst gh) * (snd gh)) /\
         (poly_to_base p (n ++ 1) (fst gh)) = gbar /\
         (poly_to_base p (n ++ 1) (snd gh)) = hbar /\
         monic (fst gh)))
      (decreases n)
  = if n = 0 then begin
      ml_ppow_one p;
      poly_to_base_level1 p f;
      poly_eq_symmetry (poly_to_base p 1 f) f;
      poly_eq_transitivity f (poly_to_base p 1 f) (gbar * hbar);
      poly_to_base_level1 p gbar;
      poly_to_base_level1 p hbar;
      monic_to_level1 p gbar
    end
    else begin
      let fn = poly_reduce p n f in
      let gh_rec = monic_hensel_lift_compute p (n - 1) fn gbar hbar s t in
      let gn = fst gh_rec in
      let hn = snd gh_rec in
      (* recursion precondition: poly_to_base p n fn = gbar*hbar *)
      poly_to_base_reduce p n f;
      ml_eq_trans3 (poly_to_base p n fn) (poly_to_base p (n ++ 1) f) (gbar * hbar);
      monic_hensel_lift_compute_correct p (n - 1) fn gbar hbar s t;
      (* recursion gives: poly_eq fn (gn*hn), to_base(n) gn = gbar, to_base(n) hn = hbar *)
      (* step's Bezout: s*(to_base gn)+t*(to_base hn) = 1 *)
      ml_bezout_transport
        s t
        (poly_to_base p n gn) (poly_to_base p n hn)
        gbar hbar
        (poly_one #(zmod p));
      monic_lift_step_sound p n f gn hn s t;
      (* step gives to_base(n++1)(fst) = to_base(n) gn = gbar (chain), similarly hbar *)
      let gh = monic_lift_step p n f gn hn s t in
      ml_eq_trans3 (poly_to_base p (n ++ 1) (fst gh)) (poly_to_base p n gn) gbar;
      ml_eq_trans3 (poly_to_base p (n ++ 1) (snd gh)) (poly_to_base p n hn) hbar;
      assert (monic_hensel_lift_compute p n f gbar hbar s t
              == monic_lift_step p n f gn hn s t)
    end

(* ================================================================ *)
(*  §12 — Support lemma for the multi-factor MONIC lift.             *)
(*                                                                   *)
(*  To iterate the two-factor monic lift over a LIST of mod-p        *)
(*  factors (mirror of hensel_lift_multi_compute), the running       *)
(*  cofactor  ḡ_tail = poly_prod tail  must be a monic divisor;      *)
(*  this holds because the product of an all_monic list is monic.    *)
(*                                                                   *)
(*  The remaining piece for the full multi-factor wrapper is the     *)
(*  h-SIDE cofactor monicity: the linear step only degree-controls   *)
(*  the g-side, so the running cofactor's monicity must be recovered *)
(*  from  monic f, monic g', f ~ g'·h'  by leading-coefficient       *)
(*  cancellation (poly_eq_lc + monic_deg_mul).  See the module tail  *)
(*  notes.                                                            *)
(* ================================================================ *)

(* poly_prod of an all_monic list is monic. *)
let rec poly_prod_monic (#a:Type) {| cr: commutative_ring a |}
  (nz: squash (not (one #a = (zero <: a))))
  (gs: list (polynomial a))
  : Lemma (requires all_monic gs)
          (ensures  monic (poly_prod gs))
          (decreases gs)
  = H.elim_equatable_laws a ();
    match gs with
    | [] -> monic_one #a nz
    | h :: rest ->
      all_monic_head h rest;
      all_monic_tail h rest;
      poly_prod_monic #a nz rest;                 (* monic (poly_prod rest) *)
      monic_deg_mul h (poly_prod rest);           (* deg (h*pr) >= 0 /\ lc(h*pr) = lc pr *)
      transitivity (poly_lc (h * (poly_prod rest))) (poly_lc (poly_prod rest)) (one <: a)

(* Leading-coefficient cancellation: if  f = gg·hh  with f AND gg monic, then
   the cofactor hh is monic.  (deg f = deg gg + deg hh and lc f = lc gg · lc hh
   = lc hh; monic f forces lc hh = one; deg hh >= 0 because otherwise hh = 0 ⇒
   f = 0 ⇒ deg f = -1, contradicting monic f.)  Needs only a commutative ring. *)
let cofactor_monic (#a:Type) {| cr: commutative_ring a |}
  (nz: squash (not (one #a = (zero <: a))))
  (f gg hh: polynomial a)
  : Lemma (requires monic f /\ monic gg /\ (f = (gg * hh)))
          (ensures  monic hh)
  = H.elim_equatable_laws a ();
    H.elim_equatable_laws (polynomial a) ();
    poly_eq_length f (gg * hh);                    (* deg f == deg (gg*hh) *)
    deg_neg_one_iff_zero hh;
    if deg hh < 0 then begin
      (* hh == poly_zero ⇒ gg*hh = 0 ⇒ f = 0 ⇒ deg f = -1, contra monic f *)
      H.x_mul_zero gg;                             (* gg * zero = zero *)
      poly_eq_transitivity f (gg * hh) (poly_zero #a);
      poly_eq_length f (poly_zero #a)
    end else ();
    monic_deg_mul gg hh;                           (* deg(gg*hh)=deg gg+deg hh /\ lc(gg*hh)=lc hh *)
    poly_eq_lc f (gg * hh);                        (* lc f = lc(gg*hh) *)
    symmetry (poly_lc (gg * hh)) (poly_lc hh);
    transitivity (poly_lc hh) (poly_lc (gg * hh)) (poly_lc f);
    transitivity (poly_lc hh) (poly_lc f) (one <: a)

(* ================================================================ *)
(*  §13 — Multi-factor MONIC lift over a LIST of mod-p factors.      *)
(*                                                                   *)
(*  Mirror of `hensel_lift_multi_compute` (Core.Factor.HenselCompute) *)
(*  but each head factor is lifted against the product-of-the-rest    *)
(*  cofactor via the two-factor MONIC step, so every returned factor  *)
(*  is monic (proved separately in §15).                              *)
(* ================================================================ *)

let rec monic_hensel_lift_multi_compute (p:int{is_prime p}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbars: list (polynomial (zmod p)) {Cons? gbars /\ all_monic gbars})
  (bez: list (bez_pair p))
  : Tot (list (polynomial (zmod (ppow p (n ++ 1)))))
        (decreases gbars)
  = match gbars with
    | [_] -> [f]
    | g_head :: tail ->
      (match bez with
       | [] -> [f]  (* dead under `bezout_chain`; keep Tot total *)
       | (s, t) :: brest ->
         all_monic_head g_head tail;                (* monic g_head *)
         all_monic_tail g_head tail;                (* all_monic tail *)
         let prod_tail = poly_prod #(zmod p) tail in
         let gh = monic_hensel_lift_compute p n f g_head prod_tail s t in
         (fst gh) :: monic_hensel_lift_multi_compute p n (snd gh) tail brest)

(* ---- local replicas of HenselCompute's private assembly helpers ---- *)

private let ml_multi_prod_assemble (p:int{p > 1}) (n:nat)
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

private let ml_multi_index_assemble (p:int{p > 1}) (n:nat)
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

(* ================================================================ *)
(*  §14 — Concrete soundness of the multi-factor MONIC lift.        *)
(*                                                                   *)
(*  Structural mirror of `hensel_lift_multi_compute_correct`, routed  *)
(*  through the monic two-factor step.  This is the drop-in           *)
(*  replacement for `hensel_lift_multi_compute` in the completeness   *)
(*  pipeline (same product/degree postconditions, plus monicity).    *)
(* ================================================================ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 120"
let rec monic_hensel_lift_multi_compute_correct (p:int{is_prime p}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbars: list (polynomial (zmod p)) {Cons? gbars /\ all_monic gbars})
  (bez: list (bez_pair p))
  : Lemma
      (requires
        (poly_to_base p (n ++ 1) f) = (poly_prod #(zmod p) gbars) /\
        bezout_chain p gbars bez)
      (ensures
        (let gs = monic_hensel_lift_multi_compute p n f gbars bez in
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
        all_monic_head g_head tail;
        all_monic_tail g_head tail;
        let prod_tail = poly_prod #(zmod p) tail in
        assert (poly_prod #(zmod p) (g_head :: tail)
                == g_head * (poly_prod #(zmod p) tail))
          by (FStar.Tactics.norm [delta_only [`%poly_prod]; iota; zeta];
              FStar.Tactics.trefl ());
        monic_hensel_lift_compute_correct p n f g_head prod_tail s t;
        let gh = monic_hensel_lift_compute p n f g_head prod_tail s t in
        let glift = fst gh in
        let hh = snd gh in
        H.elim_equatable_laws (zmod p) ();
        H.elim_equatable_laws (zmod (ppow p (n ++ 1))) ();
        monic_hensel_lift_multi_compute_correct p n hh tail brest;
        let gs_tail = monic_hensel_lift_multi_compute p n hh tail brest in
        ml_multi_prod_assemble p n f glift hh gs_tail;
        let tl_ok (i:nat{i < L.length tail})
          : Lemma (poly_eq (poly_to_base p (n ++ 1) (L.index gs_tail i))
                           (L.index tail i))
          = () in
        ml_multi_index_assemble p n g_head tail glift gs_tail tl_ok
#pop-options

(* ---- helpers for the all_monic wrapper ---- *)

(* one <> zero in zmod m for m > 1. *)
let ml_zmod_one_ne_zero (m:int{m > 1})
  : Lemma (not (one #(zmod m) = (zero <: zmod m)))
  = H.elim_equatable_laws (zmod m) ()

(* monic head + all_monic tail ==> all_monic of the cons. *)
private let ml_all_monic_cons (#a:Type) {| cr: commutative_ring a |}
  (h: polynomial a) (rest: list (polynomial a))
  : Lemma (requires monic h /\ all_monic rest)
          (ensures  all_monic (h :: rest))
  = all_monic_elim rest;
    let proof (x: polynomial a {L.memP x (h :: rest)}) : Lemma (monic x)
      = () in
    all_monic_intro (h :: rest) proof

(* ================================================================ *)
(*  §15 — The multi-factor MONIC lift returns an all_monic list.    *)
(*                                                                   *)
(*  The linear step only degree-controls the g-side, so the running  *)
(*  cofactor's monicity is recovered from  monic f, monic g',        *)
(*  f ~ g'·h'  by leading-coefficient cancellation (`cofactor_monic`) *)
(*  and threaded through the recursion via the invariant  monic f.   *)
(* ================================================================ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 120"
let rec monic_hensel_lift_multi_all_monic (p:int{is_prime p}) (n:nat)
  (f: polynomial (zmod (ppow p (n ++ 1))))
  (gbars: list (polynomial (zmod p)) {Cons? gbars /\ all_monic gbars})
  (bez: list (bez_pair p))
  : Lemma
      (requires
        (poly_to_base p (n ++ 1) f) = (poly_prod #(zmod p) gbars) /\
        bezout_chain p gbars bez /\
        monic f)
      (ensures all_monic (monic_hensel_lift_multi_compute p n f gbars bez))
      (decreases gbars)
  = ppow_gt_one p (n ++ 1);
    match gbars with
    | [g] ->
      (* compute returns [f]; all_monic [f] from monic f *)
      all_monic_intro [f] (fun (x:polynomial (zmod (ppow p (n ++ 1))){L.memP x [f]}) -> ())
    | g_head :: tail ->
      match bez with
      | [] -> assert (Cons? tail); assert False
      | (s, t) :: brest ->
        all_monic_head g_head tail;
        all_monic_tail g_head tail;
        let m1 = ppow p (n ++ 1) in
        let prod_tail = poly_prod #(zmod p) tail in
        assert (poly_prod #(zmod p) (g_head :: tail)
                == g_head * (poly_prod #(zmod p) tail))
          by (FStar.Tactics.norm [delta_only [`%poly_prod]; iota; zeta];
              FStar.Tactics.trefl ());
        monic_hensel_lift_compute_correct p n f g_head prod_tail s t;
        let gh = monic_hensel_lift_compute p n f g_head prod_tail s t in
        let glift = fst gh in                       (* monic (return-type refinement) *)
        let hh = snd gh in
        (* monic hh via cofactor cancellation: monic f, monic glift, f = glift*hh *)
        ml_zmod_one_ne_zero m1;
        let nz : squash (not (one #(zmod m1) = (zero <: zmod m1))) = () in
        cofactor_monic #(zmod m1) nz f glift hh;
        (* recurse on hh with tail: poly_to_base hh = prod_tail, bezout tail, monic hh *)
        monic_hensel_lift_multi_all_monic p n hh tail brest;
        let rest = monic_hensel_lift_multi_compute p n hh tail brest in
        ml_all_monic_cons glift rest
#pop-options
