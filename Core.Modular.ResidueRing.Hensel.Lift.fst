module Core.Modular.ResidueRing.Hensel.Lift

(* ================================================================ *)
(*  §C — THE HENSEL LIFT layer (merged).                            *)
(*                                                                   *)
(*  Merged from (in topological order):                              *)
(*    Core.Modular.ResidueRing.HenselBase      (base reduction ℤ/pᵏ → 𝔽_p)  *)
(*    Core.Modular.ResidueRing.HenselBasePoly  (poly base reduction)        *)
(*    Core.Modular.ResidueRing.HenselLift      (lift/section ℤ/pᵏ → ℤ/pᵏ⁺¹) *)
(*    Core.Modular.ResidueRing.HenselStep      (Hensel error term)          *)
(*    Core.Modular.ResidueRing.HenselVanish    (p²ᵏ-vanishing crux)         *)
(*    Core.Modular.ResidueRing.HenselAbsorb    (pᵏ-absorption crux)         *)
(*    Core.Modular.ResidueRing.HenselLiftStep  (the linear Hensel step)     *)
(*                                                                   *)
(*  Depends on the merged foundation Core.Modular.ResidueRing.Hensel.Reduce *)
(*  (reduce_step / poly_reduce / poly_quotient / mulpk / poly_mulpk  *)
(*  / error_reconstruction / ppow…).                                 *)
(*                                                                   *)
(*  NO admit / assume / sorry in the final version.                  *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Modular.ResidueRing
open Core.Modular.ResidueRing.Hensel.Reduce
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Monic
open Core.FinSum
open FStar.Math.Lemmas
open Core.Tactics.CanonRing

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* ================================================================ *)
(*  Crystallized generic commutative-ring assembly lemmas.          *)
(*  These lift the ring-agnostic sub-chains of the Hensel capstones  *)
(*  out of the concrete polynomial (zmod _) type: each abstract      *)
(*  lemma resolves the poly-over-zmod instance ONCE at the call site *)
(*  instead of re-resolving it per explicit poly_eq step.            *)
(* ================================================================ *)

(* R = rf + rmn, rmn = -rm, rm = rlg*rlh, rlg = g, rlh = h, rf = g*h  ⇒  R = 0. *)
private let error_collapse (#t:Type) {| cr: commutative_ring t |}
  (bigr rf rmn rm rlg rlh g h : t)
  : Lemma (requires bigr = (rf + rmn) /\ rmn = (- rm) /\ rm = (rlg * rlh)
                    /\ rlg = g /\ rlh = h /\ rf = (g * h))
          (ensures  bigr = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    mul_congruence rlg rlh g h;
    neg_congruence rm rf;
    add_congruence rf rmn rf (- rf);
    assert ((rf + (- rf)) = zero) by canon_ring ()

(* product-side collapse of the Hensel step:
   pt·ps = 0, lg·ps = bb, lh·pt = cc, bb+cc = pp, ff + (-(lg·lh)) = pp
   ⇒ ff = (lg+pt)·(lh+ps). *)
private let lift_assemble (#t:Type) {| cr: commutative_ring t |}
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
    (* FOIL identity (canon; spell out lg*lh, canon is blind to let-aliases) *)
    assert (((lg + pt) * (lh + ps))
            = ((lg * lh) + ((lg * ps) + ((lh * pt) + (pt * ps))))) by canon_ring ();
    add_congruence (lh * pt) (pt * ps) cc zero;
    assert ((cc + zero) = cc) by canon_ring ();
    add_congruence (lg * ps) ((lh * pt) + (pt * ps)) bb cc;
    add_congruence (lg * lh) ((lg * ps) + ((lh * pt) + (pt * ps))) (lg * lh) pp;
    add_congruence (lg * lh) pp (lg * lh) (ff + (- (lg * lh)));
    assert (((lg * lh) + (ff + (- (lg * lh)))) = ff) by canon_ring ()

(* ================================================================ *)
(*  §1 — HenselBase: the base reduction ring-hom ℤ/pᵏ → 𝔽_p = fp p.  *)
(* ================================================================ *)

(* p | pᵏ :  ppow p k = p · ppow p (k-1)  for k ≥ 1. *)
let ppow_pred (p:int{p > 1}) (k:pos)
  : Lemma (ppow p k == p `Prims.op_Star` ppow p (k - 1))
  = ()

(* the base reduction  a ↦ a mod p : ℤ/pᵏ → zmod p. *)
let to_base (p:int{p > 1}) (k:pos) (a: zmod (ppow p k)) : zmod p
  = lemma_mod_lt (zv a) p; Zm (zv a % p)

(* --- ring-hom laws (mod-p reductions of the mod-pᵏ ops) --- *)

let to_base_zero (p:int{p > 1}) (k:pos)
  : Lemma (to_base p k (zmod_zero (ppow p k)) == zmod_zero p)
  = small_mod 0 p

let to_base_one (p:int{p > 1}) (k:pos)
  : Lemma (to_base p k (zmod_one (ppow p k)) == zmod_one p)
  = small_mod 1 p

let to_base_add (p:int{p > 1}) (k:pos) (a b: zmod (ppow p k))
  : Lemma (to_base p k (zmod_add a b)
           == zmod_add (to_base p k a) (to_base p k b))
  = ppow_gt_one p k;
    ppow_pred p k;
    (* ppow p k = p * ppow p (k-1), so ((a+b) % (p*q)) % p == (a+b) % p. *)
    modulo_modulo_lemma (zv a + zv b) p (ppow p (k - 1));
    (* (a+b) % p == ((a%p) + (b%p)) % p. *)
    modulo_distributivity (zv a) (zv b) p

let to_base_mul (p:int{p > 1}) (k:pos) (a b: zmod (ppow p k))
  : Lemma (to_base p k (zmod_mul a b)
           == zmod_mul (to_base p k a) (to_base p k b))
  = ppow_gt_one p k;
    ppow_pred p k;
    (* ppow p k = p * ppow p (k-1), so ((a*b) % (p*q)) % p == (a*b) % p. *)
    modulo_modulo_lemma (zv a * zv b) p (ppow p (k - 1));
    (* (a*b) % p == ((a%p)*b) % p == ((a%p)*(b%p)) % p. *)
    lemma_mod_mul_distr_l (zv a) (zv b) p;
    lemma_mod_mul_distr_r (zv a % p) (zv b) p

(* ================================================================ *)
(*  §2 — HenselBasePoly: poly_to_base : (fp pᵏ)[X] → (zmod p)[X].      *)
(* ================================================================ *)

(* coefficient-wise base reduction (fp pᵏ)[X] → (zmod p)[X]. *)
let poly_to_base (p:int{p > 1}) (k:pos)
  (g: polynomial (zmod (ppow p k)))
  : polynomial (zmod p)
  = trim #(zmod p) (L.map (to_base p k) g)

(* index of a mapped list:  index (map g l) i = g (index l i). *)
private let rec index_map_lemma (#a:Type) (#b:Type) (g: a -> b) (l: list a) (i:nat{i < L.length l})
  : Lemma (ensures (L.map_lemma g l; L.index (L.map g l) i == g (L.index l i)))
          (decreases i)
  = L.map_lemma g l;
    if i = 0 then ()
    else index_map_lemma g (L.tl l) (i - 1)

(* coeff characterisation:  coeff (poly_to_base g) i = to_base (coeff g i). *)
let poly_to_base_coeff (p:int{p > 1}) (k:pos)
  (g: polynomial (zmod (ppow p k))) (i:int)
  : Lemma (coeff (poly_to_base p k g) i
           == to_base p k (coeff g i))
  = let map_fn = to_base p k in
    let mapped : list (zmod p) = L.map map_fn g in
    L.map_lemma map_fn g;                        (* length (map map_fn g) == length g *)
    (* poly_to_base p k g == trim mapped *)
    if i < 0 then begin
      (* both sides are the zero of fp p:
         lhs = coeff (trim mapped) i = zero (i<0);
         rhs = to_base (zero @ fp (ppow p k)) = to_base (zmod_zero (ppow p k))
             = zmod_zero p = zero. *)
      to_base_zero p k
    end
    else begin
      let i : nat = i in
      coeff_trim #(zmod p) mapped i;
      (* coeff (trim mapped) i = (if i < length mapped then index mapped i else zero) *)
      if i < L.length g then begin
        (* lhs = index mapped i = map_fn (index g i) = to_base (coeff g i) *)
        index_map_lemma map_fn g i
      end
      else begin
        (* lhs = zero = zmod_zero p;
           rhs = to_base (coeff g i) = to_base (zmod_zero (ppow p k)) = zmod_zero p *)
        to_base_zero p k
      end
    end

(* --- ring-hom laws (poly_eq in the target ring (zmod p)[X]) --- *)

(* Bridge: the ring `+` on (zmod m) IS zmod_add (the .add field of fp_acg m). *)
private let zmod_ring_add_reveal (m:int{m > 1}) (a b: zmod m)
  : Lemma (add a b == zmod_add #m a b)
  = ()

(* Bridge: the ring `*` on (zmod m) IS zmod_mul. *)
private let zmod_ring_mul_reveal (m:int{m > 1}) (a b: zmod m)
  : Lemma (mul a b == zmod_mul #m a b)
  = ()

(* Per-coefficient additivity. *)
private let poly_to_base_add_coeff (p:int{p > 1}) (k:pos)
  (g h: polynomial (zmod (ppow p k))) (j:nat)
  : Lemma (coeff
              (poly_to_base p k (g + h)) j
           == coeff
                ((poly_to_base p k g) + (poly_to_base p k h)) j)
  = let m1 = ppow p k in
    let m  = p in
    let cf = coeff g j in
    let cg = coeff h j in
    (* LHS *)
    poly_to_base_coeff p k (g + h) j;
    poly_add_coeff g h j;  (* SMTPat: coeff(g+h) j == cf + cg (ring add) *)
    zmod_ring_add_reveal m1 cf cg;                       (* cf + cg == zmod_add cf cg *)
    to_base_add p k cf cg;                             (* to_base (zmod_add cf cg) == zmod_add (tb cf) (tb cg) *)
    poly_to_base_coeff p k g j;                        (* tb cf == coeff (poly_to_base g) j *)
    poly_to_base_coeff p k h j;                        (* tb cg == coeff (poly_to_base h) j *)
    (* RHS *)
    poly_add_coeff (poly_to_base p k g) (poly_to_base p k h) j;
    zmod_ring_add_reveal m (coeff (poly_to_base p k g) j)
                          (coeff (poly_to_base p k h) j)

let poly_to_base_add (p:int{p > 1}) (k:pos)
  (g h: polynomial (zmod (ppow p k)))
  : Lemma ((poly_to_base p k (g + h))
           = ((poly_to_base p k g) + (poly_to_base p k h)))
  = let lhs : polynomial (zmod p) = poly_to_base p k (g + h) in
    let rhs : polynomial (zmod p) = (poly_to_base p k g) + (poly_to_base p k h) in
    let aux (j:nat)
      : Lemma (coeff lhs j
               = coeff rhs j)
      = poly_to_base_add_coeff p k g h j in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* to_base pushes through a finite sum (additivity ⇒ hom over sum_range).
   `hh` carries the per-term image; the pointwise hypothesis avoids a lambda
   in the signature. *)
private let rec to_base_sum_range (p:int{p > 1}) (k:pos)
  (gg: nat -> zmod (ppow p k)) (hh: nat -> zmod p)
  (pf: (i:nat) -> Lemma (hh i == to_base p k (gg i)))
  (a b: nat)
  : Lemma (ensures to_base p k (sum_range #(zmod (ppow p k)) gg a b)
                   == sum_range #(zmod p) hh a b)
          (decreases (b - a))
  = let m1 = ppow p k in
    let m  = p in
    if a >= b then begin
      sum_range_empty #(zmod m1) gg a b;        (* sum = zero = zmod_zero m1 *)
      sum_range_empty #(zmod m) hh a b;          (* sum = zero = zmod_zero m *)
      to_base_zero p k                              (* to_base (zmod_zero m1) == zmod_zero m *)
    end
    else begin
      let tailsum1 = sum_range #(zmod m1) gg (a ++ 1) b in
      sum_range_unfold_left #(zmod m1) gg a b;  (* sum_range gg a b == gg a `+` tailsum1 *)
      (* ring add m1 == zmod_add *)
      zmod_ring_add_reveal m1 (gg a) tailsum1;        (* gg a + tailsum1 == zmod_add (gg a) tailsum1 *)
      to_base_add p k (gg a) tailsum1;              (* to_base (zmod_add ..) == zmod_add (tb (gg a)) (tb tailsum1) *)
      to_base_sum_range p k gg hh pf (a ++ 1) b;     (* tb tailsum1 == sum_range hh (a+1) b *)
      pf a;                                          (* tb (gg a) == hh a from the per-index proof *)
      sum_range_unfold_left #(zmod m) hh a b;    (* sum_range hh a b == hh a `+` sum_range hh (a+1) b *)
      zmod_ring_add_reveal m (hh a) (sum_range #(zmod m) hh (a ++ 1) b)
    end

(* Convolution summand for g*h at output index j (source ring). *)
private let conv_src (p:int{p > 1}) (k:pos)
  (g h: polynomial (zmod (ppow p k))) (j:nat) (i:nat)
  : zmod (ppow p k)
  = mul
      (coeff g i)
      (coeff h (j - i))

(* Convolution summand for (to_base g)*(to_base h) at output index j (target ring). *)
private let conv_tgt (p:int{p > 1}) (k:pos)
  (g h: polynomial (zmod (ppow p k))) (j:nat) (i:nat)
  : zmod p
  = mul
      (coeff (poly_to_base p k g) i)
      (coeff (poly_to_base p k h) (j - i))

(* Per-term: to_base of a source summand is the target summand. *)
private let conv_term_to_base (p:int{p > 1}) (k:pos)
  (g h: polynomial (zmod (ppow p k))) (j:nat) (i:nat)
  : Lemma (conv_tgt p k g h j i == to_base p k (conv_src p k g h j i))
  = let m1 = ppow p k in
    let m  = p in
    let ji = j - i in
    let cf = coeff g i in
    let cg = coeff h ji in
    (* conv_src = cf * cg (ring mul m1) = zmod_mul cf cg *)
    zmod_ring_mul_reveal m1 cf cg;
    to_base_mul p k cf cg;                      (* to_base (zmod_mul cf cg) == zmod_mul (tb cf) (tb cg) *)
    poly_to_base_coeff p k g i;                 (* tb cf == coeff (poly_to_base g) i *)
    poly_to_base_coeff p k h ji;                (* tb cg == coeff (poly_to_base h) (j-i) *)
    zmod_ring_mul_reveal m
      (coeff (poly_to_base p k g) i)
      (coeff (poly_to_base p k h) ji)

(* The "extra" target summands beyond length (poly_to_base g) vanish:
   coeff (poly_to_base g) i == zero there, so the product is zero. *)
private let conv_tgt_high_zero (p:int{p > 1}) (k:pos)
  (g h: polynomial (zmod (ppow p k))) (j:nat)
  (i:nat{i >= L.length (poly_to_base p k g)})
  : Lemma (eq
              (conv_tgt p k g h j i)
              (zero <: zmod p))
  = let m = p in
    (* coeff (poly_to_base g) i == zero (above length) *)
    let cfr = coeff (poly_to_base p k g) i in
    let cgr = coeff (poly_to_base p k h) (j - i) in
    (* cfr == zero (out of range), so cfr * cgr == zmod_mul 0 cgr == 0 *)
    H.elim_equatable_laws (zmod m) ();
    zmod_ring_mul_reveal m cfr cgr

(* length (poly_to_base p k g) <= length g  (trim_length_le is Core.Polynomial's) *)
private let poly_to_base_length_le (p:int{p > 1}) (k:pos)
  (g: polynomial (zmod (ppow p k)))
  : Lemma (L.length (poly_to_base p k g) <= L.length g)
  = let map_fn = to_base p k in
    L.map_lemma map_fn g;                         (* length (map map_fn g) == length g *)
    trim_length_le #(zmod p) (L.map map_fn g)

(* The convolution target-sum is range-independent above length (poly_to_base g):
   summing conv_tgt to lenf equals summing to lenrf (extra terms are zero). *)
private let sum_range_hh_ranges (p:int{p > 1}) (k:pos)
  (g h: polynomial (zmod (ppow p k))) (j:nat)
  : Lemma (sum_range #(zmod p)
              (conv_tgt p k g h j) 0 (L.length g)
           == sum_range #(zmod p)
                (conv_tgt p k g h j) 0 (L.length (poly_to_base p k g)))
  = let m  = p in
    let hh  = conv_tgt p k g h j in
    let lenf  = L.length g in
    let lenrf = L.length (poly_to_base p k g) in
    poly_to_base_length_le p k g;                 (* lenrf <= lenf *)
    H.elim_equatable_laws (zmod m) ();
    H.trans_for_calc (zmod m) ();
    (* sum 0 lenf == sum 0 lenrf + sum lenrf lenf *)
    sum_range_split #(zmod m) hh 0 lenrf lenf;
    (* sum lenrf lenf == zero *)
    let allzero (i:nat{lenrf <= i /\ i < lenf}) : Lemma (hh i = (zero <: zmod m)) =
      conv_tgt_high_zero p k g h j i in
    sum_range_all_zero #(zmod m) hh lenrf lenf allzero;
    (* (sum 0 lenrf) + zero == sum 0 lenrf *)
    H.x_plus_zero #(zmod m) (sum_range #(zmod m) hh 0 lenrf)

(* Per-coefficient multiplicativity. *)
private let poly_to_base_mul_coeff (p:int{p > 1}) (k:pos)
  (g h: polynomial (zmod (ppow p k))) (j:nat)
  : Lemma (coeff
              (poly_to_base p k (g * h)) j
           == coeff
                ((poly_to_base p k g) * (poly_to_base p k h)) j)
  = let m1 = ppow p k in
    let m  = p in
    let lenf  = L.length g in
    let lenrf = L.length (poly_to_base p k g) in
    let gg = conv_src p k g h j in
    let hh = conv_tgt p k g h j in
    (* ---- LHS ---- *)
    poly_to_base_coeff p k (g * h) j;      (* coeff(to_base(g*h)) j == tb (coeff (g*h) j) *)
    (* coeff_poly_mul_named bridges to the NAMED summand gg internally (sum_range_congruence). *)
    let cong1 (i:nat) : Lemma (gg i = mul (coeff #(zmod m1) g i) (coeff #(zmod m1) h (j - i))) =
      H.elim_equatable_laws (zmod m1) () in
    coeff_poly_mul_named #(zmod m1) g h j gg cong1;           (* coeff (g*h) j == sum_range gg 0 lenf *)
    (* to_base pushes through the sum *)
    let hyp (i:nat) : Lemma (hh i == to_base p k (gg i)) = conv_term_to_base p k g h j i in
    to_base_sum_range p k gg hh hyp 0 lenf;                    (* tb (sum gg 0 lenf) == sum hh 0 lenf *)
    (* ---- RHS ---- *)
    let cong2 (i:nat) : Lemma (hh i = mul (coeff #(zmod m) (poly_to_base p k g) i)
                                          (coeff #(zmod m) (poly_to_base p k h) (j - i))) =
      H.elim_equatable_laws (zmod m) () in
    coeff_poly_mul_named #(zmod m) (poly_to_base p k g) (poly_to_base p k h) j hh cong2; (* coeff(rg*rh) j == sum hh 0 lenrf *)
    (* bridge the two sum ranges: sum hh 0 lenf == sum hh 0 lenrf, extra terms zero *)
    sum_range_hh_ranges p k g h j

let poly_to_base_mul (p:int{p > 1}) (k:pos)
  (g h: polynomial (zmod (ppow p k)))
  : Lemma ((poly_to_base p k (g * h))
           = ((poly_to_base p k g) * (poly_to_base p k h)))
  = let lhs : polynomial (zmod p) = poly_to_base p k (g * h) in
    let rhs : polynomial (zmod p) = (poly_to_base p k g) * (poly_to_base p k h) in
    let aux (j:nat)
      : Lemma (coeff lhs j = coeff rhs j)
      = poly_to_base_mul_coeff p k g h j in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* ================================================================ *)
(*  to_base preserves monicity and degree.                          *)
(*  The leading coefficient is `one`, and the reduction maps         *)
(*  `one ↦ one ≠ zero`, so the top coefficient survives (no trim).   *)
(* ================================================================ *)

let to_base_monic (p:int{p > 1}) (n:pos)
  (g: polynomial (zmod (ppow p n)))
  : Lemma (requires monic g)
          (ensures  monic (poly_to_base p n g) /\
                    deg (poly_to_base p n g) == deg g)
  = ppow_gt_one p n;
    let mn = ppow p n in
    let gb = poly_to_base p n g in
    let d  = deg g in                              (* d >= 0 from monic *)
    H.elim_equatable_laws (zmod mn) ();
    H.elim_equatable_laws (zmod p) ();
    (* coeff g d == poly_lc g == one == zmod_one mn *)
    last_eq_index g d;
    poly_lc_reveal g;
    assert (coeff g d = (one <: zmod mn));         (* coeff g d == poly_lc g = one *)
    (* coeff gb d == to_base (coeff g d) == to_base (zmod_one mn) == zmod_one p *)
    poly_to_base_coeff p n g d;
    to_base_one p n;
    assert (coeff gb d == zmod_one p);
    assert (not ((zmod_one p) = (zmod_zero p)));   (* p > 1 ⇒ 1 ≠ 0 *)
    (* upper: length gb <= length g, so deg gb <= d *)
    L.map_lemma (to_base p n) g;
    trim_length_le #(zmod p) (L.map (to_base p n) g);
    (* lower: nonzero top coeff at d forces deg gb >= d *)
    let _ : squash (deg gb >= d) =
      if deg gb < d then coeff_above_degree gb d else () in
    assert (deg gb == d);
    (* monic gb: poly_lc gb == coeff gb (deg gb) == coeff gb d = one *)
    last_eq_index gb (deg gb);
    poly_lc_reveal gb

(* poly_to_base of poly_one is poly_one. *)
let poly_to_base_one (p:int{p > 1}) (k:pos)
  : Lemma ((poly_to_base p k (poly_one #(zmod (ppow p k))))
           = (poly_one #(zmod p)))
  = ppow_gt_one p k;
    let pk_ = ppow p k in
    let p1  = poly_one #(zmod pk_) in
    let q1  = poly_one #(zmod p) in
    H.elim_equatable_laws (zmod p) ();
    let nz1 : squash (not (one #(zmod pk_) = (zero <: zmod pk_))) = () in
    let nzp : squash (not (one #(zmod p)  = (zero <: zmod p)))  = () in
    one_deg_lc #(zmod pk_) nz1;                    (* deg p1 == 0, lc p1 = one *)
    one_deg_lc #(zmod p)  nzp;                     (* deg q1 == 0, lc q1 = one *)
    let aux (i:nat) : Lemma (coeff (poly_to_base p k p1) i = coeff q1 i)
      = poly_to_base_coeff p k p1 i;               (* coeff(to_base p1) i == to_base (coeff p1 i) *)
        H.elim_equatable_laws (zmod p) ();
        if i = 0 then begin
          last_eq_index p1 0; poly_lc_reveal p1;   (* coeff p1 0 == poly_lc p1 = one = zmod_one pk_ *)
          to_base_one p k;                          (* to_base (zmod_one pk_) == zmod_one p *)
          last_eq_index q1 0; poly_lc_reveal q1     (* coeff q1 0 == poly_lc q1 = one = zmod_one p *)
        end else begin
          coeff_above_degree p1 i;                  (* coeff p1 i = zero = zmod_zero pk_ *)
          to_base_zero p k;                         (* to_base (zmod_zero pk_) == zmod_zero p *)
          coeff_above_degree q1 i                   (* coeff q1 i = zero = zmod_zero p *)
        end in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (poly_to_base p k p1) q1

(* ================================================================ *)
(*  §3 — HenselLift: the lift (section) map ℤ/pᵏ → ℤ/pᵏ⁺¹.          *)
(* ================================================================ *)

(* pᵏ < pᵏ⁺¹ (since pᵏ⁺¹ = pᵏ·p and p > 1). *)
let ppow_lt (p:int{p > 1}) (k:pos)
  : Lemma (ppow p k < ppow p (k ++ 1))
  = ppow_succ p k;                              (* ppow p (k+1) == ppow p k * p *)
    (* ppow p k > 0  and  p > 1  ⇒  ppow p k * 1 < ppow p k * p *)
    FStar.Math.Lemmas.lemma_mult_lt_left (ppow p k) 1 p

(* the lift  a ↦ a : ℤ/pᵏ → ℤ/pᵏ⁺¹  (same integer representative). *)
let lift_step (p:int{p > 1}) (k:pos) (a: zmod (ppow p k)) : zmod (ppow p (k ++ 1))
  = ppow_lt p k; Zm (zv a)

(* reduce ∘ lift = id. *)
let reduce_lift_id (p:int{p > 1}) (k:pos) (a: zmod (ppow p k))
  : Lemma (reduce_step p k (lift_step p k a) == a)
  = ppow_gt_one p k;
    ppow_lt p k;
    (* lift_step p k a is the same int zv a, and zv a < ppow p k,
       so reduce_step p k (lift a) = Zm (zv a % ppow p k) == Zm (zv a) == a. *)
    FStar.Math.Lemmas.small_mod (zv a) (ppow p k)

(* coefficient-wise lift on polynomials. *)
let poly_lift (p:int{p > 1}) (k:pos)
  (g: polynomial (zmod (ppow p k)))
  : polynomial (zmod (ppow p (k ++ 1)))
  = trim #(zmod (ppow p (k ++ 1))) (L.map (lift_step p k) g)

(* lift_step preserves zero (it is the identity int map; zmod_zero = 0). *)
let lift_step_zero (p:int{p > 1}) (k:pos)
  : Lemma (lift_step p k (zmod_zero (ppow p k)) == zmod_zero (ppow p (k ++ 1)))
  = ppow_lt p k

(* coeff characterisation:  coeff (poly_lift g) i = lift_step (coeff g i)
   (the exact analogue of poly_reduce_coeff, with lift_step for reduce_step). *)
let poly_lift_coeff (p:int{p > 1}) (k:pos)
  (g: polynomial (zmod (ppow p k))) (i:int)
  : Lemma (coeff (poly_lift p k g) i
           == lift_step p k (coeff g i))
  = let h = lift_step p k in
    let mapped : list (zmod (ppow p (k ++ 1))) = L.map h g in
    L.map_lemma h g;                            (* length (map h g) == length g *)
    if i < 0 then
      (* lhs = coeff (trim mapped) i = zero (i<0); rhs = lift_step (zero) = zero. *)
      lift_step_zero p k
    else begin
      let i : nat = i in
      coeff_trim #(zmod (ppow p (k ++ 1))) mapped i;
      if i < L.length g then
        (* lhs = index mapped i = h (index g i) = lift_step (coeff g i) *)
        index_map_lemma h g i
      else
        (* lhs = zero; rhs = lift_step (coeff g i) = lift_step zero = zero. *)
        lift_step_zero p k
    end

(* poly_reduce ∘ poly_lift = id  (poly_eq in (fp pᵏ)[X]). *)
let poly_reduce_lift_id (p:int{p > 1}) (k:pos)
  (g: polynomial (zmod (ppow p k)))
  : Lemma ((poly_reduce p k (poly_lift p k g)) = g)
  = let lhs = poly_reduce p k (poly_lift p k g) in
    let aux (i:nat)
      : Lemma (coeff lhs i
               = coeff g i)
      = (* coeff (poly_reduce (poly_lift g)) i
           == reduce_step (coeff (poly_lift g) i)        [poly_reduce_coeff]
           == reduce_step (lift_step (coeff g i))        [poly_lift_coeff]
           == coeff g i                                  [reduce_lift_id] *)
        poly_reduce_coeff p k (poly_lift p k g) i;
        poly_lift_coeff p k g i;
        reduce_lift_id p k (coeff g i);
        H.elim_equatable_laws (zmod (ppow p k)) () in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs g

(* ================================================================ *)
(*  §4 — HenselStep: the Hensel error term.                         *)
(* ================================================================ *)

(* reduce_step preserves negation. *)
let reduce_step_neg (p:int{p > 1}) (k:pos) (a: zmod (ppow p (k ++ 1)))
  : Lemma (reduce_step p k (zmod_neg a)
           == zmod_neg (reduce_step p k a))
  = ppow_gt_one p k;
    ppow_gt_one p (k ++ 1);
    let m  = ppow p k in
    let m1 = ppow p (k ++ 1) in
    ppow_succ p k;                                (* m1 == m * p *)
    let av = zv a in
    (* LHS: reduce_step (zmod_neg a) = ((m1 - av) % m1) % m.
       Since m1 = m*p, modulo_modulo_lemma collapses to (m1 - av) % m. *)
    modulo_modulo_lemma (m1 - av) m p;            (* ((m1-av)%(m*p))%m == (m1-av)%m *)
    (* (m1 - av) = m*p - av; the m*p term vanishes mod m. *)
    lemma_mod_plus (Prims.op_Minus av) p m;                     (* ((-av) + p*m)%m == (-av)%m *)
    assert (m1 - av == (Prims.op_Minus av) `Prims.op_Addition` (p `Prims.op_Star` m));
    (* So LHS == (-av) % m. *)
    (* RHS: zmod_neg (av % m) = (m - (av % m)) % m. *)
    (* (m - av%m) % m == (- (av%m)) % m  via lemma_mod_plus, and == (-av)%m via lemma_mod_sub. *)
    lemma_mod_plus (Prims.op_Minus (av % m)) 1 m;               (* ((-(av%m)) + 1*m)%m == (-(av%m))%m *)
    assert (m - (av % m) == (Prims.op_Minus (av % m)) `Prims.op_Addition` (1 `Prims.op_Star` m));
    (* (-(av%m)) % m == (-av) % m :  -(av%m) == -av + (av/m)*m  (euclidean: av = (av/m)*m + av%m). *)
    lemma_mod_plus (Prims.op_Minus av) (av / m) m;              (* ((-av) + (av/m)*m)%m == (-av)%m *)
    lemma_div_mod av m;                            (* av == (av/m)*m + av%m, so -(av%m) == -av + (av/m)*m *)
    assert ((Prims.op_Minus (av % m)) == (Prims.op_Minus av) `Prims.op_Addition` ((av / m) `Prims.op_Star` m))

(* Bridge: the ring `neg` on (zmod m) IS zmod_neg (the .neg field of zmod_acg m). *)
private let zmod_ring_neg_reveal (m:int{m > 1}) (a: zmod m)
  : Lemma (neg a == zmod_neg #m a)
  = ()

(* Per-coefficient negation law. *)
private let poly_reduce_neg_coeff (p:int{p > 1}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1)))) (j:nat)
  : Lemma (coeff
              (poly_reduce p k (- f)) j
           == coeff
                (- (poly_reduce p k f)) j)
  = let m1 = ppow p (k ++ 1) in
    let m  = ppow p k in
    let cf = coeff f j in
    (* LHS *)
    poly_reduce_coeff p k (- f) j;   (* == reduce_step (coeff (- f) j) *)
    poly_neg_coeff f j;                     (* coeff (- f) j == neg cf *)
    zmod_ring_neg_reveal m1 cf;                             (* neg cf == zmod_neg cf *)
    reduce_step_neg p k cf;                               (* rs (zmod_neg cf) == zmod_neg (rs cf) *)
    poly_reduce_coeff p k f j;                            (* rs cf == coeff (poly_reduce f) j *)
    (* RHS *)
    poly_neg_coeff (poly_reduce p k f) j;     (* coeff (- (reduce f)) j == neg (coeff (reduce f) j) *)
    zmod_ring_neg_reveal m (coeff (poly_reduce p k f) j)

(* poly_reduce preserves negation. *)
let poly_reduce_neg (p:int{p > 1}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  : Lemma ((poly_reduce p k (- f))
           = (- (poly_reduce p k f)))
  = let lhs : polynomial (zmod (ppow p k)) = poly_reduce p k (- f) in
    let rhs : polynomial (zmod (ppow p k)) = - (poly_reduce p k f) in
    let aux (j:nat)
      : Lemma (coeff lhs j
               = coeff rhs j)
      = poly_reduce_neg_coeff p k f j in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* THE error lemma:  reduce(f) = g·h  ⇒  reduce(f − lift g · lift h) = 0. *)
let hensel_error_reduces (p:int{p > 1}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  (g h: polynomial (zmod (ppow p k)))
  : Lemma (requires (poly_reduce p k f)
                    = (g * h))
          (ensures (poly_reduce p k
                      (f + (- ((poly_lift p k g) * (poly_lift p k h)))))
                   = (poly_zero #(zmod (ppow p k))))
  = let m  = ppow p k in
    let lg = poly_lift p k g in
    let lh = poly_lift p k h in
    let mlift = lg * lh in
    let rf  = poly_reduce p k f in                       (* reduce f          *)
    let rmn = poly_reduce p k (- mlift) in               (* reduce (-mlift)   *)
    let rm  = poly_reduce p k mlift in                   (* reduce mlift      *)
    let rlg = poly_reduce p k lg in                      (* reduce (lift g)=g *)
    let rlh = poly_reduce p k lh in                      (* reduce (lift h)=h *)
    let bigr = poly_reduce p k (f + (- mlift)) in
    poly_reduce_add p k f (- mlift);                     (* bigr = rf + rmn   *)
    poly_reduce_neg p k mlift;                           (* rmn = -rm         *)
    poly_reduce_mul p k lg lh;                           (* rm = rlg*rlh      *)
    poly_reduce_lift_id p k g;                           (* rlg = g           *)
    poly_reduce_lift_id p k h;                           (* rlh = h           *)
    (* ring-agnostic collapse (resolves the poly instance once) *)
    error_collapse bigr rf rmn rm rlg rlh g h

(* ================================================================ *)
(*  §5 — HenselVanish: the p²ᵏ-vanishing crux.                      *)
(* ================================================================ *)

(* pᵏ·pᵏ == pᵏ⁺¹·pᵏ⁻¹  (for k ≥ 1). *)
private let ppow_sq (p:int{p > 1}) (k:pos)
  : Lemma (ppow p k `Prims.op_Star` ppow p k == ppow p (k ++ 1) `Prims.op_Star` ppow p (k - 1))
  = ppow_succ p k;                                  (* ppow p (k+1) == ppow p k * p *)
    ppow_pred p k;                                  (* ppow p k == p * ppow p (k-1) *)
    (* ppow p (k+1) * ppow p (k-1)
         == (ppow p k * p) * ppow p (k-1)
         == ppow p k * (p * ppow p (k-1))
         == ppow p k * ppow p k *)
    ()

(* scalar:  (pᵏ·a)·(pᵏ·b) ≡ 0  (mod pᵏ⁺¹). *)
let mulpk_mul_zero (p:int{p > 1}) (k:pos) (a b: zmod p)
  : Lemma (zmod_mul (mulpk p k a) (mulpk p k b) == zmod_zero (ppow p (k ++ 1)))
  = ppow_gt_one p k;
    ppow_gt_one p (k ++ 1);
    let m1 = ppow p (k ++ 1) in
    let pk = ppow p k in
    let av = zv a in
    let bv = zv b in
    (* mulpk p k a == Zm (pk * av), mulpk p k b == Zm (pk * bv) *)
    let pa : nat = pk `Prims.op_Star` av in
    let pb : nat = pk `Prims.op_Star` bv in
    (* (pk*av)*(pk*bv) == (pk*pk)*(av*bv) == (m1 * ppow p (k-1)) * (av*bv)
                     == m1 * (ppow p (k-1) * (av*bv)) *)
    ppow_sq p k;
    assert ((pk `Prims.op_Star` av) `Prims.op_Star` (pk `Prims.op_Star` bv) == (pk `Prims.op_Star` pk) `Prims.op_Star` (av `Prims.op_Star` bv));
    assert (pk `Prims.op_Star` pk == m1 `Prims.op_Star` ppow p (k - 1));
    assert ((pk `Prims.op_Star` av) `Prims.op_Star` (pk `Prims.op_Star` bv) == (ppow p (k - 1) `Prims.op_Star` (av `Prims.op_Star` bv)) `Prims.op_Star` m1);
    (* (X * m1) % m1 == 0 *)
    cancel_mul_mod (ppow p (k - 1) `Prims.op_Star` (av `Prims.op_Star` bv)) m1

(* Convolution summand for (poly_mulpk u)*(poly_mulpk v) at output index j. *)
private let conv_mulpk (p:int{p > 1}) (k:pos)
  (u v: polynomial (zmod p)) (j:nat) (i:nat)
  : zmod (ppow p (k ++ 1))
  = mul
      (coeff (poly_mulpk p k u) i)
      (coeff (poly_mulpk p k v)
         (j - i))

(* Each convolution summand is zero (because pᵏ·pᵏ ≡ 0). *)
private let conv_mulpk_zero (p:int{p > 1}) (k:pos)
  (u v: polynomial (zmod p)) (j:nat) (i:nat)
  : Lemma (conv_mulpk p k u v j i == zmod_zero (ppow p (k ++ 1)))
  = let m1 = ppow p (k ++ 1) in
    let ji = j - i in
    let cu = coeff (poly_mulpk p k u) i in
    let cv = coeff (poly_mulpk p k v) ji in
    (* conv == cu * cv (ring mul) == zmod_mul cu cv *)
    zmod_ring_mul_reveal m1 cu cv;
    (* cu == mulpk (coeff u i),  cv == mulpk (coeff v (j-i)) *)
    poly_mulpk_coeff p k u i;
    poly_mulpk_coeff p k v ji;
    (* zmod_mul (mulpk (coeff u i)) (mulpk (coeff v (j-i))) == zmod_zero m1 *)
    mulpk_mul_zero p k (coeff u i)
                       (coeff v ji)

(* coeff of the product at j is the sum of zero summands == zmod_zero. *)
private let poly_mulpk_mul_coeff (p:int{p > 1}) (k:pos)
  (u v: polynomial (zmod p)) (j:nat)
  : Lemma (coeff
             ((poly_mulpk p k u) * (poly_mulpk p k v)) j
           == zmod_zero (ppow p (k ++ 1)))
  = let m1 = ppow p (k ++ 1) in
    let pu = poly_mulpk p k u in
    let pv = poly_mulpk p k v in
    let gg = conv_mulpk p k u v j in
    H.elim_equatable_laws (zmod m1) ();
    H.trans_for_calc (zmod m1) ();
    (* coeff (pu*pv) j == sum_range gg 0 (len pu), via the named-fn variant. *)
    let hh (i:nat) : Lemma (gg i = coeff pu i
                                  `mul` coeff pv (j - i))
      = H.elim_equatable_laws (zmod m1) () in
    coeff_poly_mul_named #(zmod m1) pu pv j gg hh;
    (* every summand is zero (== zmod_zero m1 == zero) *)
    let allzero (i:nat{0 <= i /\ i < L.length pu}) : Lemma (gg i = (zero <: zmod m1)) =
      conv_mulpk_zero p k u v j i in
    sum_range_all_zero #(zmod m1) gg 0 (L.length pu) allzero

(* poly crux:  (poly_mulpk u) · (poly_mulpk v) = 0  in (fp pᵏ⁺¹)[X]. *)
let poly_mulpk_mul_zero (p:int{p > 1}) (k:pos)
  (u v: polynomial (zmod p))
  : Lemma (((poly_mulpk p k u) * (poly_mulpk p k v))
           = (poly_zero #(zmod (ppow p (k ++ 1)))))
  = let m1 = ppow p (k ++ 1) in
    let lhs : polynomial (zmod m1) = (poly_mulpk p k u) * (poly_mulpk p k v) in
    let rhs = poly_zero #(zmod m1) in
    H.elim_equatable_laws (zmod m1) ();
    let aux (j:int) : Lemma (coeff lhs j = coeff rhs j)
      = if j < 0 then
          (* both coeffs are zero by the coeff refinement *)
          ()
        else begin
          let j : nat = j in
          poly_mulpk_mul_coeff p k u v j
          (* coeff lhs j == zmod_zero m1 == zero; coeff rhs j == zero (rhs == []) *)
        end in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* ================================================================ *)
(*  §6 — HenselAbsorb: the pᵏ-absorption crux.                      *)
(* ================================================================ *)

(* ---------------------------------------------------------------- *)
(*  Bridge:  to_base ∘ lift = to_base   (both are `mod p`).          *)
(* ---------------------------------------------------------------- *)

let to_base_lift (p:int{p > 1}) (k:pos) (a: zmod (ppow p k))
  : Lemma (to_base p (k ++ 1) (lift_step p k a) == to_base p k a)
  = (* lift_step p k a is the SAME integer a, so both sides are a % p. *)
    ()

let poly_to_base_lift (p:int{p > 1}) (k:pos)
  (g: polynomial (zmod (ppow p k)))
  : Lemma ((poly_to_base p (k ++ 1) (poly_lift p k g))
           = (poly_to_base p k g))
  = let lhs = poly_to_base p (k ++ 1) (poly_lift p k g) in
    let rhs = poly_to_base p k g in
    let aux (i:nat)
      : Lemma (coeff lhs i
               = coeff rhs i)
      = (* coeff (poly_to_base (poly_lift g)) i
           == to_base p (k+1) (coeff (poly_lift g) i)     [poly_to_base_coeff @ k+1]
           == to_base p (k+1) (lift_step (coeff g i))     [poly_lift_coeff]
           == to_base p k (coeff g i)                     [to_base_lift]
           == coeff (poly_to_base g) i                    [poly_to_base_coeff @ k] *)
        poly_to_base_coeff p (k ++ 1) (poly_lift p k g) i;
        poly_lift_coeff p k g i;
        to_base_lift p k (coeff g i);
        poly_to_base_coeff p k g i;
        H.elim_equatable_laws (zmod p) () in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* scalar:  mulpk is additive  —  pᵏ·(a+b mod p) = (pᵏa + pᵏb) mod pᵏ⁺¹. *)
let mulpk_additive (p:int{p > 1}) (k:pos) (a b: zmod p)
  : Lemma (mulpk p k (zmod_add a b)
           == zmod_add (mulpk p k a) (mulpk p k b))
  = ppow_gt_one p k;
    ppow_succ p k;                                    (* ppow p (k+1) == ppow p k * p *)
    let pk : pos = ppow p k in
    let m1 : int = ppow p (k ++ 1) in                  (* == pk * p *)
    let av = zv a in
    let bv = zv b in
    (* LHS = mulpk p k ((av+bv)%p) == pk * ((av+bv) % p). *)
    (* RHS = (pk*av + pk*bv) % m1 == (pk*(av+bv)) % (pk*p). *)
    (* scale lemma:  ((av+bv) * pk) % (pk * p) == ((av+bv) % p) * pk. *)
    modulo_scale_lemma (av `Prims.op_Addition` bv) pk p;
    (* (pk*av + pk*bv) % m1 == (pk*(av+bv)) % m1, by distributivity. *)
    assert (pk `Prims.op_Star` av `Prims.op_Addition` (pk `Prims.op_Star` bv) == (av `Prims.op_Addition` bv) `Prims.op_Star` pk);
    assert (m1 == pk `Prims.op_Star` p)

(* scalar absorb:  (pᵏ·a)·w  ≡  pᵏ·(a · (w mod p))   (mod pᵏ⁺¹). *)
let mulpk_mul_w (p:int{p > 1}) (k:pos) (a: zmod p) (w: zmod (ppow p (k ++ 1)))
  : Lemma (zmod_mul (mulpk p k a) w
           == mulpk p k (zmod_mul a (to_base p (k ++ 1) w)))
  = ppow_gt_one p k;
    ppow_succ p k;                                    (* ppow p (k+1) == ppow p k * p *)
    let pk : pos = ppow p k in
    let m1 : int = ppow p (k ++ 1) in                  (* == pk * p *)
    let av = zv a in
    let wv = zv w in
    (* LHS = zmod_mul (pk*av) wv == ((pk*av)*wv) % m1 == (pk*(av*wv)) % (pk*p). *)
    assert ((pk `Prims.op_Star` av) `Prims.op_Star` wv == (av `Prims.op_Star` wv) `Prims.op_Star` pk);
    assert (m1 == pk `Prims.op_Star` p);
    (* scale lemma: ((av*wv) * pk) % (pk*p) == ((av*wv) % p) * pk. *)
    modulo_scale_lemma (av `Prims.op_Star` wv) pk p;
    (* (av*wv) % p == (av*(wv%p)) % p. *)
    lemma_mod_mul_distr_r av wv p;
    (* RHS = mulpk p k ((av*(wv%p))%p) == pk * ((av*(wv%p))%p);  to_base p (k+1) w == Zm (wv % p). *)
    assert (((av `Prims.op_Star` wv) % p) `Prims.op_Star` pk == pk `Prims.op_Star` ((av `Prims.op_Star` (wv % p)) % p))

(* mulpk pushes through a finite sum (it is additive). *)
let rec mulpk_sum_range (p:int{p > 1}) (k:pos)
  (gg: nat -> zmod p) (hh: nat -> zmod (ppow p (k ++ 1)))
  (pf: (i:nat) -> Lemma (hh i == mulpk p k (gg i)))
  (a b: nat)
  : Lemma (ensures mulpk p k (sum_range #(zmod p) gg a b)
                   == sum_range #(zmod (ppow p (k ++ 1))) hh a b)
          (decreases (b - a))
  = let m1 = ppow p (k ++ 1) in
    let m  = p in
    if a >= b then begin
      sum_range_empty #(zmod m) gg a b;          (* sum gg = zero = zmod_zero m *)
      sum_range_empty #(zmod m1) hh a b;        (* sum hh = zero = zmod_zero m1 *)
      mulpk_zero p k                                (* mulpk (zmod_zero m) == zmod_zero m1 *)
    end
    else begin
      let tailsum = sum_range #(zmod m) gg (a ++ 1) b in
      sum_range_unfold_left #(zmod m) gg a b;    (* sum_range gg a b == gg a `+` tailsum *)
      (* ring add m == zmod_add *)
      zmod_ring_add_reveal m (gg a) tailsum;          (* gg a + tailsum == zmod_add (gg a) tailsum *)
      mulpk_additive p k (gg a) tailsum;            (* mulpk (zmod_add ..) == zmod_add (mulpk (gg a)) (mulpk tailsum) *)
      mulpk_sum_range p k gg hh pf (a ++ 1) b;        (* mulpk tailsum == sum_range hh (a+1) b *)
      pf a;                                          (* mulpk (gg a) == hh a from the per-index proof *)
      sum_range_unfold_left #(zmod m1) hh a b;  (* sum_range hh a b == hh a `+` sum_range hh (a+1) b *)
      zmod_ring_add_reveal m1 (hh a) (sum_range #(zmod m1) hh (a ++ 1) b)
    end

(* ---------------------------------------------------------------- *)
(*  THE absorption crux (convolution).                              *)
(* ---------------------------------------------------------------- *)

(* Source convolution summand for (poly_mulpk u) * w at output index j. *)
private let conv_src_absorb (p:int{p > 1}) (k:pos)
  (u: polynomial (zmod p))
  (w: polynomial (zmod (ppow p (k ++ 1)))) (j:nat) (i:nat)
  : zmod (ppow p (k ++ 1))
  = mul
      (coeff (poly_mulpk p k u) i)
      (coeff w (j - i))

(* Base convolution summand for u * (poly_to_base w) at output index j (over fp p). *)
private let conv_base (p:int{p > 1}) (k:pos)
  (u: polynomial (zmod p))
  (w: polynomial (zmod (ppow p (k ++ 1)))) (j:nat) (i:nat)
  : zmod p
  = mul
      (coeff u i)
      (coeff (poly_to_base p (k ++ 1) w) (j - i))

(* Per-term:  each source summand is mulpk of the corresponding base summand. *)
private let conv_term_mulpk (p:int{p > 1}) (k:pos)
  (u: polynomial (zmod p))
  (w: polynomial (zmod (ppow p (k ++ 1)))) (j:nat) (i:nat)
  : Lemma (conv_src_absorb p k u w j i == mulpk p k (conv_base p k u w j i))
  = let m1 = ppow p (k ++ 1) in
    let ji = j - i in
    let cu1 = coeff (poly_mulpk p k u) i in
    let cw  = coeff w ji in
    (* conv_src_absorb == zmod_mul cu1 cw *)
    zmod_ring_mul_reveal m1 cu1 cw;
    (* cu1 == mulpk (coeff u i) *)
    poly_mulpk_coeff p k u i;
    (* zmod_mul (mulpk (coeff u i)) cw == mulpk (zmod_mul (coeff u i) (to_base p (k+1) cw)) *)
    mulpk_mul_w p k (coeff u i) cw;
    (* to_base p (k+1) cw == coeff (poly_to_base p (k+1) w) (j-i) *)
    poly_to_base_coeff p (k ++ 1) w ji;
    (* conv_base == zmod_mul (coeff u i) (coeff (poly_to_base w) (j-i)) *)
    zmod_ring_mul_reveal p
      (coeff u i)
      (coeff (poly_to_base p (k ++ 1) w) ji)

(* length (poly_mulpk p k u) <= length u. *)
private let poly_mulpk_length_le (p:int{p > 1}) (k:pos)
  (u: polynomial (zmod p))
  : Lemma (L.length (poly_mulpk p k u) <= L.length u)
  = let f = mulpk p k in
    L.map_lemma f u;                                (* length (map f u) == length u *)
    trim_length_le #(zmod (ppow p (k ++ 1))) (L.map f u)

(* The "extra" source summands beyond length (poly_mulpk u) vanish:
   coeff (poly_mulpk u) i == zero there, so the product is zero. *)
private let conv_src_high_zero (p:int{p > 1}) (k:pos)
  (u: polynomial (zmod p))
  (w: polynomial (zmod (ppow p (k ++ 1)))) (j:nat)
  (i:nat{i >= L.length (poly_mulpk p k u)})
  : Lemma (eq
              (conv_src_absorb p k u w j i)
              (zero <: zmod (ppow p (k ++ 1))))
  = let m1 = ppow p (k ++ 1) in
    let cu1 = coeff (poly_mulpk p k u) i in
    let cw  = coeff w (j - i) in
    (* cu1 == zero (out of range), so cu1 * cw == zmod_mul 0 cw == 0 *)
    H.elim_equatable_laws (zmod m1) ();
    zmod_ring_mul_reveal m1 cu1 cw

(* The source convolution-sum is range-independent above length (poly_mulpk u):
   summing conv_src_absorb to lenu equals summing to lenpu (extra terms are zero). *)
private let sum_range_gg_ranges (p:int{p > 1}) (k:pos)
  (u: polynomial (zmod p))
  (w: polynomial (zmod (ppow p (k ++ 1)))) (j:nat)
  : Lemma (sum_range #(zmod (ppow p (k ++ 1)))
              (conv_src_absorb p k u w j) 0 (L.length u)
           == sum_range #(zmod (ppow p (k ++ 1)))
                (conv_src_absorb p k u w j) 0 (L.length (poly_mulpk p k u)))
  = let m1 = ppow p (k ++ 1) in
    let gg  = conv_src_absorb p k u w j in
    let lenu  = L.length u in
    let lenpu = L.length (poly_mulpk p k u) in
    poly_mulpk_length_le p k u;                     (* lenpu <= lenu *)
    H.elim_equatable_laws (zmod m1) ();
    H.trans_for_calc (zmod m1) ();
    (* sum 0 lenu == sum 0 lenpu + sum lenpu lenu *)
    sum_range_split #(zmod m1) gg 0 lenpu lenu;
    (* sum lenpu lenu == zero *)
    let allzero (i:nat{lenpu <= i /\ i < lenu}) : Lemma (gg i = (zero <: zmod m1)) =
      conv_src_high_zero p k u w j i in
    sum_range_all_zero #(zmod m1) gg lenpu lenu allzero;
    (* (sum 0 lenpu) + zero == sum 0 lenpu *)
    H.x_plus_zero #(zmod m1) (sum_range #(zmod m1) gg 0 lenpu)

(* Per-coefficient absorption. *)
private let poly_mulpk_absorb_coeff (p:int{p > 1}) (k:pos)
  (u: polynomial (zmod p))
  (w: polynomial (zmod (ppow p (k ++ 1)))) (j:nat)
  : Lemma (coeff
              ((poly_mulpk p k u) * w) j
           == coeff
                (poly_mulpk p k (u * (poly_to_base p (k ++ 1) w))) j)
  = let m1 = ppow p (k ++ 1) in
    let pu = poly_mulpk p k u in
    let wb = poly_to_base p (k ++ 1) w in
    let gg = conv_src_absorb p k u w j in
    let hh = conv_base p k u w j in
    let lenu  = L.length u in
    let lenpu = L.length pu in
    H.elim_equatable_laws (zmod m1) ();
    H.trans_for_calc (zmod m1) ();
    (* ---- LHS:  coeff (pu * w) j == sum_range gg 0 lenpu ---- *)
    let lam1 (i:nat) : Lemma (gg i = mul (coeff pu i)
                                                  (coeff w (j - i)))
      = H.elim_equatable_laws (zmod m1) () in
    coeff_poly_mul_named #(zmod m1) pu w j gg lam1;   (* coeff (pu*w) j == sum gg 0 lenpu *)
    (* extend the source range up to lenu (extra terms vanish) *)
    sum_range_gg_ranges p k u w j;                       (* sum gg 0 lenu == sum gg 0 lenpu *)
    (* ---- BASE:  coeff (u * wb) j == sum_range hh 0 lenu ---- *)
    let lam2 (i:nat) : Lemma (hh i = mul (coeff u i)
                                                 (coeff wb (j - i)))
      = H.elim_equatable_laws (zmod p) () in
    coeff_poly_mul_named #(zmod p) u wb j hh lam2;      (* coeff (u*wb) j == sum hh 0 lenu *)
    (* ---- bridge: each gg i == mulpk (hh i), so mulpk pushes through the sum ---- *)
    let hyp (i:nat) : Lemma (gg i == mulpk p k (hh i)) = conv_term_mulpk p k u w j i in
    mulpk_sum_range p k hh gg hyp 0 lenu;                 (* mulpk (sum hh 0 lenu) == sum gg 0 lenu *)
    (* ---- RHS:  coeff (poly_mulpk (u*wb)) j == mulpk (coeff (u*wb) j) ---- *)
    poly_mulpk_coeff p k (u * wb) j

let poly_mulpk_absorb (p:int{p > 1}) (k:pos)
  (u: polynomial (zmod p))
  (w: polynomial (zmod (ppow p (k ++ 1))))
  : Lemma (((poly_mulpk p k u) * w)
           = (poly_mulpk p k
                (u * (poly_to_base p (k ++ 1) w))))
  = let m1 = ppow p (k ++ 1) in
    let pu = poly_mulpk p k u in
    let wb = poly_to_base p (k ++ 1) w in
    let lhs : polynomial (zmod m1) = pu * w in
    let rhs = poly_mulpk p k (u * wb) in
    let aux (j:nat)
      : Lemma (coeff lhs j = coeff rhs j)
      = poly_mulpk_absorb_coeff p k u w j;
        H.elim_equatable_laws (zmod m1) () in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* ================================================================ *)
(*  §7 — HenselLiftStep: THE linear Hensel lift step.               *)
(* ================================================================ *)

(* scalar:  reduce(pᵏ·a) = 0  (mod pᵏ). *)
let reduce_step_mulpk_zero (p:int{p > 1}) (k:pos) (a: zmod p)
  : Lemma (reduce_step p k (mulpk p k a) == zmod_zero (ppow p k))
  = ppow_gt_one p k;
    let pk : pos = ppow p k in
    let av = zv a in
    (* zv (mulpk p k a) == pk * av;  reduce_step p k x == Zm (zv x % pk);  zmod_zero pk == Zm 0. *)
    assert (zv (mulpk p k a) == pk `Prims.op_Star` av);
    (* (av * pk) % pk == 0, and pk * av == av * pk. *)
    cancel_mul_mod av pk;
    assert (pk `Prims.op_Star` av == av `Prims.op_Star` pk)

(* poly:  reduce (poly_mulpk x) = 0  in (fp pᵏ)[X]. *)
let poly_reduce_mulpk_zero (p:int{p > 1}) (k:pos)
  (x: polynomial (zmod p))
  : Lemma ((poly_reduce p k (poly_mulpk p k x))
           = (poly_zero #(zmod (ppow p k))))
  = let m  = ppow p k in
    let lhs = poly_reduce p k (poly_mulpk p k x) in
    let aux (i:nat)
      : Lemma (coeff lhs i
               = coeff (poly_zero #(zmod m)) i)
      = (* coeff (poly_reduce (poly_mulpk x)) i == reduce_step (coeff (poly_mulpk x) i) *)
        poly_reduce_coeff p k (poly_mulpk p k x) i;
        (* coeff (poly_mulpk x) i == mulpk (coeff x i) *)
        poly_mulpk_coeff p k x i;
        (* reduce_step (mulpk (coeff x i)) == zmod_zero m *)
        reduce_step_mulpk_zero p k (coeff x i);
        (* coeff poly_zero i == zmod_zero m;  equate via reflexivity of equatable. *)
        H.elim_equatable_laws (zmod m) () in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs
      (poly_zero #(zmod m))

(* poly_mulpk is additive. *)
let poly_mulpk_add (p:int{p > 1}) (k:pos)
  (a b: polynomial (zmod p))
  : Lemma ((poly_mulpk p k (a + b))
           = ((poly_mulpk p k a) + (poly_mulpk p k b)))
  = let m1 = ppow p (k ++ 1) in
    let lhs : polynomial (zmod m1) = poly_mulpk p k (a + b) in
    let rhs : polynomial (zmod m1) = (poly_mulpk p k a) + (poly_mulpk p k b) in
    let aux (i:nat)
      : Lemma (coeff lhs i
               = coeff rhs i)
      = let ca = coeff a i in
        let cb = coeff b i in
        (* ---- LHS ---- *)
        (* coeff (poly_mulpk (a+b)) i == mulpk (coeff (a+b) i) *)
        poly_mulpk_coeff p k (a + b) i;
        (* coeff (a+b) i == ca + cb (ring add)  [SMTPat] *)
        poly_add_coeff a b i;
        (* ca + cb == zmod_add ca cb *)
        zmod_ring_add_reveal p ca cb;
        (* mulpk (zmod_add ca cb) == zmod_add (mulpk ca) (mulpk cb) *)
        mulpk_additive p k ca cb;
        (* ---- RHS ---- *)
        (* coeff (poly_mulpk a + poly_mulpk b) i == coeff (poly_mulpk a) i + coeff (poly_mulpk b) i *)
        poly_add_coeff (poly_mulpk p k a) (poly_mulpk p k b) i;
        zmod_ring_add_reveal m1
          (coeff (poly_mulpk p k a) i)
          (coeff (poly_mulpk p k b) i);
        (* coeff (poly_mulpk a) i == mulpk ca;  coeff (poly_mulpk b) i == mulpk cb *)
        poly_mulpk_coeff p k a i;
        poly_mulpk_coeff p k b i in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* poly_mulpk respects poly_eq (congruence). *)
private let poly_mulpk_congr (p:int{p > 1}) (k:pos)
  (a b: polynomial (zmod p))
  : Lemma (requires a = b)
          (ensures (poly_mulpk p k a) = (poly_mulpk p k b))
  = let m1 = ppow p (k ++ 1) in
    let la = poly_mulpk p k a in
    let lb = poly_mulpk p k b in
    let aux (i:nat)
      : Lemma (coeff la i
               = coeff lb i)
      = poly_mulpk_coeff p k a i;
        poly_mulpk_coeff p k b i;
        (* coeff a i == coeff b i (propositional, on fp p) from poly_eq *)
        poly_eq_means_equal_coeffs a b i;
        H.elim_equatable_laws (zmod m1) () in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq la lb

(* ---------------------------------------------------------------- *)
(*  Capstone sub-lemmas.  cr1 = the ring of (fp pᵏ⁺¹)[X].            *)
(* ---------------------------------------------------------------- *)

(* The cross product  lg · (poly_mulpk u)  ≡  poly_mulpk (u · ḡ),       *)
(* where ḡ = poly_to_base p k g and lg = poly_lift p k g.               *)
private let cross_absorb (p:int{p > 1}) (k:pos)
  (g: polynomial (zmod (ppow p k)))
  (u: polynomial (zmod p))
  : Lemma (((poly_lift p k g) * (poly_mulpk p k u))
           = (poly_mulpk p k
                (u * (poly_to_base p k g))))
  = let lg  = poly_lift p k g in
    let pu  = poly_mulpk p k u in
    let blg = poly_to_base p (k ++ 1) lg in       (* poly_to_base of the lift *)
    let bg  = poly_to_base p k g in              (* ḡ *)
    (* lg · pu ~ pu · lg *)
    poly_mul_commutativity lg pu;
    (* pu · lg ~ poly_mulpk (u · blg) *)
    poly_mulpk_absorb p k u lg;
    poly_eq_transitivity
      (lg * pu)
      (pu * lg)
      (poly_mulpk p k (u * blg));
    (* poly_to_base (lift g) ~ poly_to_base g  ⇒  u · blg ~ u · bg *)
    poly_to_base_lift p k g;
    poly_eq_reflexivity u;
    poly_mul_congruence u blg u bg;
    poly_mulpk_congr p k (u * blg) (u * bg);
    poly_eq_transitivity
      (lg * pu)
      (poly_mulpk p k (u * blg))
      (poly_mulpk p k (u * bg))

(* rearrange  x·d ~ d·x  then absorb δ:  (s·δ)·ḡ ~ δ·(s·ḡ). *)
private let regroup_term (p:int{p > 1})
  (d x y: polynomial (zmod p))
  : Lemma (((x * d) * y)
           = (d * (x * y)))
  = (* (x·d)·y ~ x·(d·y)            [assoc] *)
    poly_mul_associativity x d y;
    (* d·y ~ y·d  ⇒  x·(d·y) ~ x·(y·d)   [comm + congr] *)
    poly_mul_commutativity d y;
    poly_eq_reflexivity x;
    poly_mul_congruence x (d * y) x (y * d);
    (* x·(y·d) ~ (x·y)·d            [assoc backwards] *)
    poly_mul_associativity x y d;
    poly_eq_symmetry
      ((x * y) * d)
      (x * (y * d));
    (* (x·y)·d ~ d·(x·y)            [comm] *)
    poly_mul_commutativity (x * y) d;
    (* chain *)
    poly_eq_transitivity
      ((x * d) * y)
      (x * (d * y))
      (x * (y * d));
    poly_eq_transitivity
      ((x * d) * y)
      (x * (y * d))
      ((x * y) * d);
    poly_eq_transitivity
      ((x * d) * y)
      ((x * y) * d)
      (d * (x * y))

(* the Bézout core:  (s·δ)·ḡ + (t·δ)·h̄ ~ δ,  using s·ḡ + t·h̄ ~ 1. *)
private let bezout_core (p:int{p > 1})
  (d sg tg : polynomial (zmod p))
  (s t : polynomial (zmod p))
  : Lemma (requires ((s * sg) + (t * tg))
                    = (poly_one #(zmod p)))
          (ensures (((s * d) * sg) + ((t * d) * tg))
                   = d)
  = (* term1 = (s·d)·sg ~ d·(s·sg) *)
    regroup_term p d s sg;
    (* term2 = (t·d)·tg ~ d·(t·tg) *)
    regroup_term p d t tg;
    (* sum ~ d·(s·sg) + d·(t·tg)   [add_congruence] *)
    poly_add_congruence
      ((s * d) * sg) ((t * d) * tg)
      (d * (s * sg)) (d * (t * tg));
    (* d·(s·sg) + d·(t·tg) ~ d·((s·sg)+(t·tg))   [left_distrib backwards] *)
    poly_left_distributivity d (s * sg) (t * tg);
    poly_eq_symmetry
      (d * ((s * sg) + (t * tg)))
      ((d * (s * sg)) + (d * (t * tg)));
    (* d·((s·sg)+(t·tg)) ~ d·1   [Bézout + congr] *)
    poly_eq_reflexivity d;
    poly_mul_congruence
      d ((s * sg) + (t * tg)) d (poly_one #(zmod p));
    (* d·1 ~ d   [mul_one] *)
    poly_mul_one d;
    (* chain everything *)
    poly_eq_transitivity
      (((s * d) * sg) + ((t * d) * tg))
      ((d * (s * sg)) + (d * (t * tg)))
      (d * ((s * sg) + (t * tg)));
    poly_eq_transitivity
      (((s * d) * sg) + ((t * d) * tg))
      (d * ((s * sg) + (t * tg)))
      (d * (poly_one #(zmod p)));
    poly_eq_transitivity
      (((s * d) * sg) + ((t * d) * tg))
      (d * (poly_one #(zmod p)))
      d

(* reduce (lift g + poly_mulpk w) ~ g. *)
private let reduce_correction (p:int{p > 1}) (k:pos)
  (g: polynomial (zmod (ppow p k)))
  (w: polynomial (zmod p))
  : Lemma ((poly_reduce p k
              ((poly_lift p k g) + (poly_mulpk p k w)))
           = g)
  = let m  = ppow p k in
    let m1 = ppow p (k ++ 1) in
    let lg = poly_lift p k g in
    let pw = poly_mulpk p k w in
    let rlg = poly_reduce p k lg in
    let rpw = poly_reduce p k pw in
    (* reduce (lg + pw) ~ (reduce lg) + (reduce pw) *)
    poly_reduce_add p k lg pw;
    (* reduce lg ~ g ; reduce pw ~ 0 *)
    poly_reduce_lift_id p k g;
    poly_reduce_mulpk_zero p k w;
    (* (reduce lg)+(reduce pw) ~ g + 0 *)
    poly_add_congruence rlg rpw g (poly_zero #(zmod m) );
    (* g + 0 ~ g *)
    poly_add_zero g;
    (* chain *)
    poly_eq_transitivity
      (poly_reduce p k (lg + pw))
      (rlg + rpw)
      (g + (poly_zero #(zmod m) ));
    poly_eq_transitivity
      (poly_reduce p k (lg + pw))
      (g + (poly_zero #(zmod m) ))
      g

(* Focused product helper: proves ONLY the product equality  f ~ g'·h'
   for the computed witnesses g' = lg + poly_mulpk(t·δ), h' = lh + poly_mulpk(s·δ).
   Establishes the poly-specific cross/vanish facts, then hands the pure
   ring-algebra off to `lift_assemble` (one instance resolution). *)
private let lift_product (p:int{p > 1}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  (g h: polynomial (zmod (ppow p k)))
  (s t: polynomial (zmod p))
  : Lemma
      (requires
        (poly_reduce p k f)
        = (g * h) /\
        ((s * (poly_to_base p k g)) + (t * (poly_to_base p k h)))
        = (poly_one #(zmod p)))
      (ensures
        poly_eq f
          ((poly_lift p k g + poly_mulpk p k (t * (poly_quotient p k
             (f + (- ((poly_lift p k g) * (poly_lift p k h)))))))
           * (poly_lift p k h + poly_mulpk p k (s * (poly_quotient p k
             (f + (- ((poly_lift p k g) * (poly_lift p k h)))))))))
  = let m1 = ppow p (k ++ 1) in
    let lg = poly_lift p k g in
    let lh = poly_lift p k h in
    let prod0 : polynomial (zmod m1) = lg * lh in
    let e  : polynomial (zmod m1) = f + (- prod0) in
    let dd = poly_quotient p k e in
    let td : polynomial (zmod p) = t * dd in
    let sd : polynomial (zmod p) = s * dd in
    let pt = poly_mulpk p k td in
    let ps = poly_mulpk p k sd in
    let gbar = poly_to_base p k g in
    let hbar = poly_to_base p k h in
    let bpm = poly_mulpk p k (sd * gbar) in
    let cpm = poly_mulpk p k (td * hbar) in
    let pmd = poly_mulpk p k dd in
    hensel_error_reduces p k f g h;             (* reduce e ~ 0 (error_reconstruction pre) *)
    error_reconstruction p k e;                 (* e = pmd, i.e. (f + (-(lg*lh))) = pmd    *)
    poly_mulpk_mul_zero p k td sd;              (* pt·ps = 0                               *)
    cross_absorb p k g sd;                      (* lg·ps = bpm                             *)
    cross_absorb p k h td;                      (* lh·pt = cpm                             *)
    poly_mulpk_add p k (sd * gbar) (td * hbar); (* q = bpm + cpm  (q = poly_mulpk(sum))    *)
    bezout_core p dd gbar hbar s t;             (* (sd·gbar)+(td·hbar) = dd                *)
    poly_mulpk_congr p k ((sd * gbar) + (td * hbar)) dd;          (* q = pmd                *)
    (* ring-agnostic collapse; the q-relations fold the two poly_eq glue steps inside *)
    lift_assemble lg lh pt ps f bpm cpm
      (poly_mulpk p k ((sd * gbar) + (td * hbar))) pmd

(* Existence postcondition of the Hensel lift step, as an OPAQUE proposition so
   the `exists` never lands in a consumer's SMT context.  Consumers recover the
   existential through `hensel_lift_step_post_elim`. *)
[@@"opaque_to_smt"]
let hensel_lift_step_post (p:int{p > 1}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  (g h: polynomial (zmod (ppow p k)))
  : prop =
  exists (g' h': polynomial (zmod (ppow p (k ++ 1)))).
    poly_eq (poly_reduce p k g') g /\
    poly_eq (poly_reduce p k h') h /\
    poly_eq f (g' * h')

let hensel_lift_step_post_elim (p:int{p > 1}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  (g h: polynomial (zmod (ppow p k)))
  : Lemma (requires hensel_lift_step_post p k f g h)
          (ensures
            (exists (g' h': polynomial (zmod (ppow p (k ++ 1)))).
              poly_eq (poly_reduce p k g') g /\
              poly_eq (poly_reduce p k h') h /\
              poly_eq f (g' * h')))
  = reveal_opaque (`%hensel_lift_step_post) (hensel_lift_step_post p k f g h)

(* THE Hensel lift step (existence). *)
let hensel_lift_step (p:int{p > 1}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  (g h: polynomial (zmod (ppow p k)))
  (s t: polynomial (zmod p))
  : Lemma
      (requires
        (poly_reduce p k f)
        = (g * h) /\
        ((s * (poly_to_base p k g)) + (t * (poly_to_base p k h)))
        = (poly_one #(zmod p)))
      (ensures hensel_lift_step_post p k f g h)
  = let m1 = ppow p (k ++ 1) in
    let lg = poly_lift p k g in
    let lh = poly_lift p k h in
    let dd = poly_quotient p k (f + (- (lg * lh))) in   (* δ *)
    let td : polynomial (zmod p) = t * dd in
    let sd : polynomial (zmod p) = s * dd in
    let g' : polynomial (zmod m1) = lg + poly_mulpk p k td in
    let h' : polynomial (zmod m1) = lh + poly_mulpk p k sd in
    (* reduce g' ~ g , reduce h' ~ h *)
    reduce_correction p k g td;
    reduce_correction p k h sd;
    (* f ~ g'·h'  (crystallized product assembly) *)
    lift_product p k f g h s t;
    (* --- discharge the existential --- *)
    introduce exists (gg' hh': polynomial (zmod m1) ).
        poly_eq (poly_reduce p k gg') g /\
        poly_eq (poly_reduce p k hh') h /\
        poly_eq f (gg' * hh')
    with g' h'
    and ();
    (* re-package the bare existential as the opaque postcondition *)
    reveal_opaque (`%hensel_lift_step_post) (hensel_lift_step_post p k f g h)

(* ================================================================ *)
(*  §S6 — EXECUTABLE (Tot) Hensel step + concrete soundness.        *)
(*                                                                   *)
(*  hensel_lift_step (above) proves EXISTENCE of a lifted pair; the  *)
(*  witnesses g' = lg + Pt, h' = lh + Ps are COMPUTATIONS.  Here we  *)
(*  expose them as a Tot function and prove the CONCRETE soundness   *)
(*  of that specific pair (same proof body as the step, minus the    *)
(*  existential packaging).                                          *)
(* ================================================================ *)

(* The lifted pair (g',h') as an executable computation. *)
let hensel_lift_step_compute (p:int{p > 1}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  (g h: polynomial (zmod (ppow p k)))
  (s t: polynomial (zmod p))
  : tuple2 (polynomial (zmod (ppow p (k ++ 1))))
           (polynomial (zmod (ppow p (k ++ 1))))
  = let lg = poly_lift p k g in
    let lh = poly_lift p k h in
    let prod0 : polynomial (zmod (ppow p (k ++ 1))) = lg * lh in
    let e  : polynomial (zmod (ppow p (k ++ 1))) = f + (- prod0) in
    let dd = poly_quotient p k e in
    let td : polynomial (zmod p) = t * dd in
    let sd : polynomial (zmod p) = s * dd in
    let pt = poly_mulpk p k td in
    let ps = poly_mulpk p k sd in
    (lg + pt, lh + ps)

(* Concrete soundness of the computed pair.  Under `hensel_lift_step`'s
   hypotheses, the SPECIFIC pair returned by `hensel_lift_step_compute`
   reduces to (g,h) and multiplies back to f.  Proof body = the step's,
   without the final existential introduction. *)
let hensel_lift_step_compute_correct (p:int{p > 1}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  (g h: polynomial (zmod (ppow p k)))
  (s t: polynomial (zmod p))
  : Lemma
      (requires
        (poly_reduce p k f)
        = (g * h) /\
        ((s * (poly_to_base p k g)) + (t * (poly_to_base p k h)))
        = (poly_one #(zmod p)))
      (ensures
        (let gh' = hensel_lift_step_compute p k f g h s t in
         poly_eq (poly_reduce p k (fst gh')) g /\
         poly_eq (poly_reduce p k (snd gh')) h /\
         poly_eq f ((fst gh') * (snd gh'))))
  = let lg = poly_lift p k g in
    let lh = poly_lift p k h in
    let dd = poly_quotient p k (f + (- (lg * lh))) in
    (* reduce (fst gh') ~ g , reduce (snd gh') ~ h *)
    reduce_correction p k g (t * dd);
    reduce_correction p k h (s * dd);
    (* f ~ (fst gh')·(snd gh')  (crystallized product assembly) *)
    lift_product p k f g h s t
