module Core.Modular.FpZmodBridge

(* ================================================================ *)
(*  The  fp p  ≅  zmod p  bridge  (task #33 wiring).                  *)
(*                                                                   *)
(*  fp p   (Modular.PrimeField) = n:nat{n < p}, FIELD at is_prime p. *)
(*  zmod p (Modular.ResidueRing) = Zm v, commutative_ring at p > 1.  *)
(*  Both reps are v:nat{v < p}; the cell maps are the identity on    *)
(*  the representative:                                              *)
(*      fz : fp p -> zmod p   (v ↦ Zm v)                             *)
(*      zf : zmod p -> fp p   (Zm v ↦ v)                             *)
(*  Naming: `fz`/`zf` (NOT `to_fp`/`poly_to_fp` — those are the      *)
(*  CenteredPoly ℤ→zmod maps, unrelated to PrimeField.fp).           *)
(*                                                                   *)
(*  Deliverables:                                                    *)
(*   1. cell iso + ring-hom facts (both directions).                 *)
(*   2. poly-level coeffwise maps poly_fz / poly_zf, round-trips,    *)
(*      ring-hom (add/mul/one), congruence, deg/lc/monic transport.  *)
(*   3. structure transport: monic, poly_prod/masked_prod, divides,  *)
(*      Bezout.                                                       *)
(*   4. capstone recombination_complete_fp.                          *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module IR = Core.Polynomial.Irreducible

open Core.Algebra
open Core.Algebra.Notation
open Core.NumberTheory
open FStar.Math.Lemmas
open Core.Modular.PrimeField
open Core.Modular.ResidueRing
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Monic
open Core.Polynomial.Roots
open Core.Polynomial.SubsetProd
open Core.Algebra.Divisibility
open Core.Modular.ResidueRing.CenteredPoly
open Core.FinSum
open Core.Algebra.Int
open Core.Polynomial.Eval
open Core.Modular.ResidueRing.Hensel.Reduce
open Core.Modular.ResidueRing.Hensel.Lift
open Core.Modular.ResidueRing.IntReduce
open Core.Polynomial.KroneckerBound
open Core.Modular.RecombinationComplete

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  1.  Cell isomorphism  fp p  ↔  zmod p.                            *)
(* ================================================================ *)

let fz (#p:int{p > 1}) (v: fp p) : zmod p = Zm v

let zf (#p:int{p > 1}) (x: zmod p) : fp p = zv x

(* round-trips *)
let zf_fz (#p:int{p > 1}) (v: fp p) : Lemma (zf (fz v) == v) = ()

let fz_zf (#p:int{p > 1}) (x: zmod p) : Lemma (fz (zf x) == x)
  = match x with | Zm _ -> ()

(* ---- cell ring-hom facts, fz direction (needs the fp FIELD ops) ---- *)

let fz_zero (p:int{p > 1}) : Lemma (fz (fp_zero p) == zmod_zero p) = ()
let fz_one  (p:int{p > 1}) : Lemma (fz (fp_one p)  == zmod_one p)  = ()

let fz_add (#p:int{is_prime p}) (a b: fp p)
  : Lemma (fz (a + b) == (fz a) + (fz b))
  = ()

let fz_mul (#p:int{is_prime p}) (a b: fp p)
  : Lemma (fz (a * b) == (fz a) * (fz b))
  = ()

let fz_neg (#p:int{is_prime p}) (a: fp p)
  : Lemma (fz (- a) == - (fz a))
  = ()

(* ---- cell ring-hom facts, zf direction ---- *)

let zf_zero (p:int{p > 1}) : Lemma (zf (zmod_zero p) == fp_zero p) = ()
let zf_one  (p:int{p > 1}) : Lemma (zf (zmod_one p)  == fp_one p)  = ()

let zf_add (#p:int{is_prime p}) (a b: zmod p)
  : Lemma (zf (a + b) == (zf a) + (zf b))
  = fz_zf a; fz_zf b; fz_add (zf a) (zf b)

let zf_mul (#p:int{is_prime p}) (a b: zmod p)
  : Lemma (zf (a * b) == (zf a) * (zf b))
  = fz_zf a; fz_zf b; fz_mul (zf a) (zf b)

(* ================================================================ *)
(*  2.  Poly-level coeffwise maps  poly_fz / poly_zf.                 *)
(*      (trim-aware; mirror poly_to_fp / poly_centered.)              *)
(* ================================================================ *)

let poly_fz (#p:int{is_prime p}) (g: polynomial (fp p)) : polynomial (zmod p)
  = trim #(zmod p) (L.map (fz #p) g)

let poly_zf (#p:int{is_prime p}) (x: polynomial (zmod p)) : polynomial (fp p)
  = trim #(fp p) (L.map (zf #p) x)

(* coeff characterisations (mirror poly_to_fp_coeff). *)
let poly_fz_coeff (#p:int{is_prime p}) (g: polynomial (fp p)) (i:int)
  : Lemma (coeff (poly_fz g) i == fz (coeff g i))
  = let fmap = fz #p in
    let mapped : list (zmod p) = L.map fmap g in
    L.map_lemma fmap g;
    H.elim_equatable_laws (zmod p) ();
    if i < 0 then ()
    else begin
      let i : nat = i in
      coeff_trim #(zmod p) mapped i;
      if i < L.length g then index_map_lemma fmap g i
      else ()
    end

let poly_zf_coeff (#p:int{is_prime p}) (x: polynomial (zmod p)) (i:int)
  : Lemma (coeff (poly_zf x) i == zf (coeff x i))
  = let zmap = zf #p in
    let mapped : list (fp p) = L.map zmap x in
    L.map_lemma zmap x;
    H.elim_equatable_laws (fp p) ();
    if i < 0 then ()
    else begin
      let i : nat = i in
      coeff_trim #(fp p) mapped i;
      if i < L.length x then index_map_lemma zmap x i
      else ()
    end

(* congruence:  a = b ==> poly_fz a = poly_fz b  (and zf side). *)
let poly_fz_congr (#p:int{is_prime p}) (a b: polynomial (fp p))
  : Lemma (requires a = b) (ensures (poly_fz a) = (poly_fz b))
  = let lhs = poly_fz a in
    let rhs = poly_fz b in
    let aux (i:nat) : Lemma (coeff lhs i = coeff rhs i)
      = poly_fz_coeff a i;
        poly_fz_coeff b i;
        poly_eq_means_equal_coeffs a b i in   (* coeff a i = coeff b i *)
    poly_eq_by_coeff lhs rhs aux

let poly_zf_congr (#p:int{is_prime p}) (a b: polynomial (zmod p))
  : Lemma (requires a = b) (ensures (poly_zf a) = (poly_zf b))
  = let lhs = poly_zf a in
    let rhs = poly_zf b in
    let aux (i:nat) : Lemma (coeff lhs i = coeff rhs i)
      = poly_zf_coeff a i;
        poly_zf_coeff b i;
        poly_eq_means_equal_coeffs a b i in
    poly_eq_by_coeff lhs rhs aux

(* round-trips at poly level. *)
let poly_zf_fz (#p:int{is_prime p}) (g: polynomial (fp p))
  : Lemma ((poly_zf (poly_fz g)) = g)
  = let lhs = poly_zf (poly_fz g) in
    let aux (i:nat) : Lemma (coeff lhs i = coeff g i)
      = H.elim_equatable_laws (fp p) ();
        poly_zf_coeff (poly_fz g) i;             (* coeff lhs i == zf (coeff (poly_fz g) i) *)
        poly_fz_coeff g i;                        (* coeff (poly_fz g) i == fz (coeff g i) *)
        zf_fz (coeff g i) in              (* zf (fz (coeff g i)) == coeff g i *)
    poly_eq_by_coeff lhs g aux

let poly_fz_zf (#p:int{is_prime p}) (x: polynomial (zmod p))
  : Lemma ((poly_fz (poly_zf x)) = x)
  = let lhs = poly_fz (poly_zf x) in
    let aux (i:nat) : Lemma (coeff lhs i = coeff x i)
      = H.elim_equatable_laws (zmod p) ();
        poly_fz_coeff (poly_zf x) i;
        poly_zf_coeff x i;
        fz_zf (coeff x i) in
    poly_eq_by_coeff lhs x aux

(* ================================================================ *)
(*  3.  Poly-level ring-hom facts  (add / one / mul).                *)
(* ================================================================ *)

let poly_fz_add (#p:int{is_prime p}) (g h: polynomial (fp p))
  : Lemma ((poly_fz (g + h)) = ((poly_fz g) + (poly_fz h)))
  = let lhs : polynomial (zmod p) = poly_fz (g + h) in
    let rhs : polynomial (zmod p) = (poly_fz g) + (poly_fz h) in
    H.elim_equatable_laws (zmod p) ();
    let aux (j:nat) : Lemma (coeff lhs j = coeff rhs j) =
      poly_fz_coeff (g + h) j;                          (* coeff lhs j == fz (coeff (g+h) j) *)
      poly_add_coeff g h j;                             (* coeff (g+h) j = coeff g j + coeff h j *)
      fz_add (coeff g j) (coeff h j);                   (* fz respects fp add *)
      poly_fz_coeff g j;                                (* fz (coeff g j) == coeff (poly_fz g) j *)
      poly_fz_coeff h j;
      poly_add_coeff (poly_fz g) (poly_fz h) j          (* coeff rhs j = ... *)
    in poly_eq_by_coeff lhs rhs aux

(* coeff of poly_one:  one at 0, zero elsewhere (generic helper). *)
let coeff_poly_one_val (#t:Type) {| cr: commutative_ring t |} (j:nat)
  : Lemma (coeff (poly_one #t) j = (if j = 0 then (one <: t) else (zero <: t)))
  = H.elim_equatable_laws t ();
    poly_const_one #t ();
    poly_eq_means_equal_coeffs (poly_const (one <: t)) (poly_one #t) j;
    if j = 0 then poly_const_coeff0 (one <: t)
    else poly_const_coeff_high (one <: t) j

let poly_fz_one (#p:int{is_prime p})
  : Lemma ((poly_fz (poly_one #(fp p))) = (poly_one #(zmod p)))
  = let lhs = poly_fz (poly_one #(fp p)) in
    H.elim_equatable_laws (zmod p) ();
    fz_one p; fz_zero p;
    let aux (j:nat) : Lemma (coeff lhs j = coeff (poly_one #(zmod p)) j) =
      poly_fz_coeff (poly_one #(fp p)) j;
      coeff_poly_one_val #(fp p) j;
      coeff_poly_one_val #(zmod p) j
    in poly_eq_by_coeff lhs (poly_one #(zmod p)) aux

(* ---- multiplicativity via convolution (mirrors poly_to_fp_mul) ---- *)

(* fz pushes through a finite fp-sum. *)
private let rec fz_sum_range (#p:int{is_prime p})
  (gg: nat -> fp p) (hh: nat -> zmod p)
  (pf: (i:nat) -> Lemma (hh i == fz (gg i)))
  (a b: nat)
  : Lemma (ensures fz (sum_range #(fp p) gg a b) == sum_range #(zmod p) hh a b)
          (decreases (b - a))
  = if a >= b then begin
      sum_range_empty #(fp p) gg a b;                (* sum = zero_fp *)
      sum_range_empty #(zmod p) hh a b;              (* sum = zero_zmod *)
      fz_zero p                                       (* fz (zero_fp) == zero_zmod *)
    end
    else begin
      let tailsum = sum_range #(fp p) gg (a ++ 1) b in
      sum_range_unfold_left #(fp p) gg a b;          (* sum gg a b == gg a + tailsum *)
      fz_add (gg a) tailsum;                          (* fz (gg a + tailsum) == fz(gg a) + fz tailsum *)
      pf a;                                           (* hh a == fz (gg a) *)
      fz_sum_range gg hh pf (a ++ 1) b;               (* fz tailsum == sum hh (a+1) b *)
      sum_range_unfold_left #(zmod p) hh a b          (* sum hh a b == hh a + sum hh (a+1) b *)
    end

(* Convolution summand for g*h at output index j (source ring fp p). *)
private let conv_src (#p:int{is_prime p}) (g h: polynomial (fp p)) (j:nat) (i:nat)
  : fp p
  = (coeff g i) * (coeff h (j - i))

(* Convolution summand for (poly_fz g)*(poly_fz h) at output index j. *)
private let conv_tgt (#p:int{is_prime p}) (g h: polynomial (fp p)) (j:nat) (i:nat)
  : zmod p
  = (coeff (poly_fz g) i) * (coeff (poly_fz h) (j - i))

private let conv_src_unfold (#p:int{is_prime p}) (g h: polynomial (fp p)) (j:nat) (i:nat)
  : Lemma (conv_src g h j i == (coeff g i) * (coeff h (j - i)))
  = ()

private let conv_tgt_unfold (#p:int{is_prime p}) (g h: polynomial (fp p)) (j:nat) (i:nat)
  : Lemma (conv_tgt g h j i
           == (coeff (poly_fz g) i) * (coeff (poly_fz h) (j - i)))
  = ()

(* Per-term:  fz of a source summand is the target summand. *)
private let conv_term_reduce (#p:int{is_prime p}) (g h: polynomial (fp p)) (j:nat) (i:nat)
  : Lemma (conv_tgt g h j i == fz (conv_src g h j i))
  = let ji = j - i in
    conv_src_unfold g h j i;
    conv_tgt_unfold g h j i;
    fz_mul (coeff g i) (coeff h ji);                 (* fz(cg*ch) == fz cg * fz ch *)
    poly_fz_coeff g i;                                (* fz cg == coeff (poly_fz g) i *)
    poly_fz_coeff h ji                                (* fz ch == coeff (poly_fz h) (j-i) *)

(* Extra target summands beyond length (poly_fz g) vanish. *)
private let conv_tgt_high_zero (#p:int{is_prime p}) (g h: polynomial (fp p)) (j:nat)
  (i:nat{i >= L.length (poly_fz g)})
  : Lemma (eq (conv_tgt g h j i) (zero <: zmod p))
  = H.elim_equatable_laws (zmod p) ();
    conv_tgt_unfold g h j i                           (* coeff (poly_fz g) i == zero ⟹ product == 0 *)

private let poly_fz_length_le (#p:int{is_prime p}) (g: polynomial (fp p))
  : Lemma (L.length (poly_fz g) <= L.length g)
  = L.map_lemma (fz #p) g;
    trim_length_le #(zmod p) (L.map (fz #p) g)

(* Summing conv_tgt to length g equals summing to length (poly_fz g). *)
private let sum_range_hh_ranges (#p:int{is_prime p}) (g h: polynomial (fp p)) (j:nat)
  : Lemma (sum_range #(zmod p) (conv_tgt g h j) 0 (L.length g)
           == sum_range #(zmod p) (conv_tgt g h j) 0 (L.length (poly_fz g)))
  = let hh  = conv_tgt g h j in
    let lenf  = L.length g in
    let lenrf = L.length (poly_fz g) in
    poly_fz_length_le g;                              (* lenrf <= lenf *)
    H.elim_equatable_laws (zmod p) ();
    H.trans_for_calc (zmod p) ();
    sum_range_split #(zmod p) hh 0 lenrf lenf;
    let allzero (i:nat{lenrf <= i /\ i < lenf}) : Lemma (hh i = (zero <: zmod p)) =
      conv_tgt_high_zero g h j i in
    sum_range_all_zero #(zmod p) hh lenrf lenf allzero;
    H.x_plus_zero #(zmod p) (sum_range #(zmod p) hh 0 lenrf)

private let conv_tgt_is_mul (#p:int{is_prime p}) (g h: polynomial (fp p)) (j:nat) (i:nat)
  : Lemma (eq (conv_tgt g h j i)
              ((coeff (poly_fz g) i) * (coeff (poly_fz h) (j - i))))
  = H.elim_equatable_laws (zmod p) ();
    conv_tgt_unfold g h j i

private let conv_src_is_mul (#p:int{is_prime p}) (g h: polynomial (fp p)) (j:nat) (i:nat)
  : Lemma (eq (conv_src g h j i) ((coeff g i) * (coeff h (j - i))))
  = H.elim_equatable_laws (fp p) ();
    conv_src_unfold g h j i

(* Per-coefficient multiplicativity. *)
private let poly_fz_mul_coeff (#p:int{is_prime p}) (g h: polynomial (fp p)) (j:nat)
  : Lemma (coeff (poly_fz (g * h)) j == coeff ((poly_fz g) * (poly_fz h)) j)
  = let lenf  = L.length g in
    let gg = conv_src g h j in
    let hh = conv_tgt g h j in
    (* ---- LHS ---- *)
    poly_fz_coeff (g * h) j;                          (* coeff(poly_fz(g*h)) j == fz (coeff(g*h) j) *)
    let hsrc (i:nat) : Lemma (eq (gg i) ((coeff g i) * (coeff h (j - i)))) =
      conv_src_is_mul g h j i in
    coeff_poly_mul_named g h j gg hsrc;               (* coeff(g*h) j = sum gg 0 lenf *)
    let hyp (i:nat) : Lemma (hh i == fz (gg i)) = conv_term_reduce g h j i in
    fz_sum_range gg hh hyp 0 lenf;                    (* fz (sum gg 0 lenf) == sum hh 0 lenf *)
    (* ---- RHS ---- *)
    let htgt (i:nat) : Lemma (eq (hh i)
                  ((coeff (poly_fz g) i) * (coeff (poly_fz h) (j - i)))) =
      conv_tgt_is_mul g h j i in
    coeff_poly_mul_named (poly_fz g) (poly_fz h) j hh htgt;  (* coeff(rf*rh) j = sum hh 0 lenrf *)
    sum_range_hh_ranges g h j                          (* sum hh 0 lenf == sum hh 0 lenrf *)

let poly_fz_mul (#p:int{is_prime p}) (g h: polynomial (fp p))
  : Lemma ((poly_fz (g * h)) = ((poly_fz g) * (poly_fz h)))
  = let lhs : polynomial (zmod p) = poly_fz (g * h) in
    let rhs : polynomial (zmod p) = (poly_fz g) * (poly_fz h) in
    H.elim_equatable_laws (zmod p) ();
    let aux (j:nat) : Lemma (coeff lhs j = coeff rhs j) =
      poly_fz_mul_coeff g h j in
    poly_eq_by_coeff lhs rhs aux

(* ================================================================ *)
(*  4.  Degree / leading-coefficient / monic transport.              *)
(*      (fz and zf are injective cell maps preserving zero and one,  *)
(*       so leading coefficients and degree carry across.)           *)
(* ================================================================ *)

let poly_fz_monic (#p:int{is_prime p}) (g: polynomial (fp p))
  : Lemma (requires monic g)
          (ensures  monic (poly_fz g) /\ deg (poly_fz g) == deg g)
  = let gb = poly_fz g in
    let d  = deg g in
    H.elim_equatable_laws (fp p) ();
    H.elim_equatable_laws (zmod p) ();
    last_eq_index g d;
    poly_lc_reveal g;                                 (* coeff g d == one_fp *)
    poly_fz_coeff g d;                                (* coeff gb d == fz (coeff g d) *)
    fz_one p;                                         (* fz one_fp == zmod_one p ≠ 0 *)
    L.map_lemma (fz #p) g;
    trim_length_le #(zmod p) (L.map (fz #p) g);
    let _ : squash (deg gb >= d) =
      if deg gb < d then coeff_above_degree gb d else () in
    last_eq_index gb (deg gb);
    poly_lc_reveal gb

let poly_zf_monic (#p:int{is_prime p}) (x: polynomial (zmod p))
  : Lemma (requires monic x)
          (ensures  monic (poly_zf x) /\ deg (poly_zf x) == deg x)
  = let xb = poly_zf x in
    let d  = deg x in
    H.elim_equatable_laws (fp p) ();
    H.elim_equatable_laws (zmod p) ();
    last_eq_index x d;
    poly_lc_reveal x;                                 (* coeff x d == one_zmod *)
    poly_zf_coeff x d;                                (* coeff xb d == zf (coeff x d) *)
    zf_one p;                                         (* zf one_zmod == fp_one p ≠ 0 *)
    L.map_lemma (zf #p) x;
    trim_length_le #(fp p) (L.map (zf #p) x);
    let _ : squash (deg xb >= d) =
      if deg xb < d then coeff_above_degree xb d else () in
    last_eq_index xb (deg xb);
    poly_lc_reveal xb

(* ================================================================ *)
(*  5.  Structure transport across the bridge.                       *)
(* ================================================================ *)

(* `poly_lc_const` (leading coefficient of a nonzero constant) and
   `monic_assoc_eq` (monic-associate normalisation) now live generically
   in Core.Polynomial.Monic (opened above) and are reused from there. *)

(* poly_fz commutes with masked_prod:
     poly_fz (masked_prod hs mask) = masked_prod (map poly_fz hs) mask. *)
let rec poly_fz_masked_prod (#p:int{is_prime p})
  (hs: list (polynomial (fp p))) (mask: list bool)
  : Lemma (ensures (poly_fz (masked_prod hs mask))
                   = (masked_prod (L.map (poly_fz #p) hs) mask))
          (decreases hs)
  = H.elim_equatable_laws (polynomial (zmod p)) ();
    H.trans_for_calc (polynomial (zmod p)) ();
    match hs, mask with
    | [], _ ->
      masked_prod_nil #(fp p) mask;                   (* masked hs mask == poly_one_fp *)
      poly_fz_one #p;                                  (* poly_fz poly_one_fp = poly_one_zmod *)
      masked_prod_nil #(zmod p) mask                   (* masked [] mask == poly_one_zmod *)
    | h :: hs', [] ->
      masked_prod_mask_nil #(fp p) hs;                 (* masked hs [] == poly_one_fp *)
      poly_fz_one #p;
      masked_prod_mask_nil #(zmod p) (L.map (poly_fz #p) hs)
    | h :: hs', b :: m' ->
      poly_fz_masked_prod hs' m';                      (* IH *)
      if b then begin
        masked_prod_cons_true h hs' m';                (* masked hs mask == h * masked hs' m' *)
        poly_fz_mul h (masked_prod hs' m');            (* poly_fz(h*X) = poly_fz h * poly_fz X *)
        mul_congruence (poly_fz h) (poly_fz (masked_prod hs' m'))
                       (poly_fz h) (masked_prod (L.map (poly_fz #p) hs') m');
        poly_eq_transitivity (poly_fz (masked_prod hs mask))
                             ((poly_fz h) * (poly_fz (masked_prod hs' m')))
                             ((poly_fz h) * (masked_prod (L.map (poly_fz #p) hs') m'));
        masked_prod_cons_true (poly_fz h) (L.map (poly_fz #p) hs') m'
      end else begin
        masked_prod_cons_false h hs' m';               (* masked hs mask == masked hs' m' *)
        masked_prod_cons_false (poly_fz h) (L.map (poly_fz #p) hs') m'
      end

(* poly_fz commutes with poly_prod. *)
let rec poly_fz_poly_prod (#p:int{is_prime p}) (hs: list (polynomial (fp p)))
  : Lemma (ensures (poly_fz (poly_prod hs)) = (poly_prod (L.map (poly_fz #p) hs)))
          (decreases hs)
  = H.elim_equatable_laws (polynomial (zmod p)) ();
    H.trans_for_calc (polynomial (zmod p)) ();
    match hs with
    | [] -> poly_fz_one #p
    | h :: rest ->
      poly_fz_poly_prod rest;                          (* IH *)
      poly_fz_mul h (poly_prod rest);                  (* poly_fz(h*prod rest) = poly_fz h * poly_fz(prod rest) *)
      mul_congruence (poly_fz h) (poly_fz (poly_prod rest))
                     (poly_fz h) (poly_prod (L.map (poly_fz #p) rest));
      poly_eq_transitivity (poly_fz (poly_prod hs))
                           ((poly_fz h) * (poly_fz (poly_prod rest)))
                           ((poly_fz h) * (poly_prod (L.map (poly_fz #p) rest)))

(* divides transport:  a | b  (fp)  ⟹  poly_fz a | poly_fz b  (zmod). *)
let poly_fz_divides (#p:int{is_prime p}) (a b: polynomial (fp p))
  : Lemma (requires divides a b)
          (ensures  divides (poly_fz a) (poly_fz b))
  = H.elim_equatable_laws (polynomial (zmod p)) ();
    H.trans_for_calc (polynomial (zmod p)) ();
    eliminate exists (k: polynomial (fp p)). (eq b (mul a k))
    returns divides (poly_fz a) (poly_fz b)
    with _.
    begin
      poly_fz_congr b (a * k);                         (* poly_fz b = poly_fz(a*k) *)
      poly_fz_mul a k;                                 (* poly_fz(a*k) = poly_fz a * poly_fz k *)
      poly_eq_transitivity (poly_fz b) (poly_fz (a * k))
                           ((poly_fz a) * (poly_fz k));
      divides_intro (poly_fz a) (poly_fz b) (poly_fz k)
    end

(* ================================================================ *)
(*  6.  Bezout transport (fp → zmod), masked form.                   *)
(* ================================================================ *)

(* Crystallized ring-generic glue for the Bezout transport below.
   The homomorphism-transport tail is a pure equatable/commutative_ring fact:
   from  a = o, a = p0 + q0, p0 = sfz*pfa, q0 = tfz*pfb, pfa = ma, pfb = mb
   derive  sfz*ma + tfz*mb = o.  Proven once over abstract {|commutative_ring t|}
   (equatable plumbing resolves the abstract instance), then instantiated once at
   polynomial (zmod p) — instead of re-resolving polynomial_cr per congruence /
   transitivity step inside the big query (1.3s -> ~0.16s). *)
private
let bezout_glue (#t:Type) {| cr: commutative_ring t |}
  (a p0 q0 sfz pfa ma tfz pfb mb o: t)
  : Lemma (requires (a = o) /\ (a = (p0 + q0)) /\
                    (p0 = (sfz * pfa)) /\ (q0 = (tfz * pfb)) /\
                    (pfa = ma) /\ (pfb = mb))
          (ensures  ((sfz * ma) + (tfz * mb)) = o)
  = H.elim_equatable_laws t ();
    mul_congruence sfz pfa sfz ma;              (* sfz*pfa = sfz*ma *)
    mul_congruence tfz pfb tfz mb;              (* tfz*pfb = tfz*mb *)
    transitivity p0 (sfz * pfa) (sfz * ma);     (* p0 = sfz*ma *)
    transitivity q0 (tfz * pfb) (tfz * mb);     (* q0 = tfz*mb *)
    add_congruence p0 q0 (sfz * ma) (tfz * mb); (* p0+q0 = sfz*ma + tfz*mb *)
    transitivity a (p0 + q0) ((sfz * ma) + (tfz * mb)); (* a = sfz*ma + tfz*mb *)
    symmetry a ((sfz * ma) + (tfz * mb));
    transitivity ((sfz * ma) + (tfz * mb)) a o

let bezout_fp_to_zmod (#p:int{is_prime p})
  (gbars_fp: list (polynomial (fp p))) (mask: list bool) (s_fp t_fp: polynomial (fp p))
  : Lemma
      (requires ((s_fp * (masked_prod gbars_fp mask))
                 + (t_fp * (masked_prod gbars_fp (negate_mask mask)))) = (poly_one #(fp p)))
      (ensures (((poly_fz s_fp) * (masked_prod (L.map (poly_fz #p) gbars_fp) mask))
                + ((poly_fz t_fp) * (masked_prod (L.map (poly_fz #p) gbars_fp) (negate_mask mask))))
               = (poly_one #(zmod p)))
  = H.elim_equatable_laws (polynomial (zmod p)) ();
    let a  = masked_prod gbars_fp mask in
    let b  = masked_prod gbars_fp (negate_mask mask) in
    let ma = masked_prod (L.map (poly_fz #p) gbars_fp) mask in
    let mb = masked_prod (L.map (poly_fz #p) gbars_fp) (negate_mask mask) in
    let lhs_fp = (s_fp * a) + (t_fp * b) in
    poly_fz_masked_prod gbars_fp mask;                (* poly_fz a = ma *)
    poly_fz_masked_prod gbars_fp (negate_mask mask);  (* poly_fz b = mb *)
    (* poly_fz lhs_fp = poly_one_zmod *)
    poly_fz_congr lhs_fp (poly_one #(fp p));
    poly_fz_one #p;
    poly_eq_transitivity (poly_fz lhs_fp) (poly_fz (poly_one #(fp p))) (poly_one #(zmod p));
    (* decompose poly_fz lhs_fp *)
    poly_fz_add (s_fp * a) (t_fp * b);
    poly_fz_mul s_fp a;
    poly_fz_mul t_fp b;
    (* crystallized equatable plumbing, resolved once *)
    bezout_glue #(polynomial (zmod p))
      (poly_fz lhs_fp)
      (poly_fz (s_fp * a)) (poly_fz (t_fp * b))
      (poly_fz s_fp) (poly_fz a) ma
      (poly_fz t_fp) (poly_fz b) mb
      (poly_one #(zmod p))

(* opaque universal-Bezout hypothesis on the fp side (mask-agnostic):
   for every mask of the right length the complementary masked products are
   coprime, i.e. possess a Bezout identity.  This is exactly what a field-side
   pairwise-coprime irreducible factorisation supplies; wrapped opaque (Q1). *)
[@@"opaque_to_smt"]
let fp_bezout_all_masks (#p:int{is_prime p}) (gbars_fp: list (polynomial (fp p)))
  : prop =
  forall (m: list bool). L.length m == L.length gbars_fp ==>
    (exists (s_fp t_fp: polynomial (fp p)).
       ((s_fp * (masked_prod gbars_fp m))
        + (t_fp * (masked_prod gbars_fp (negate_mask m)))) = (poly_one #(fp p)))

let fp_bezout_all_masks_elim (#p:int{is_prime p})
  (gbars_fp: list (polynomial (fp p)){fp_bezout_all_masks gbars_fp}) (m: list bool)
  : Lemma (requires L.length m == L.length gbars_fp)
          (ensures  exists (s_fp t_fp: polynomial (fp p)).
             ((s_fp * (masked_prod gbars_fp m))
              + (t_fp * (masked_prod gbars_fp (negate_mask m)))) = (poly_one #(fp p)))
  = reveal_opaque (`%fp_bezout_all_masks) (fp_bezout_all_masks gbars_fp)

(* DISCHARGE: fp_bezout_all_masks is DERIVABLE from a field-side factorisation.
   All-irreducible + pairwise-coprime gbars_fp (exactly Berlekamp's natural
   outputs) give, for every mask, that the complementary masked products are
   coprime (SubsetProd.masked_prod_coprime) hence generate poly_one via a
   Bezout identity (SubsetProd.masked_prod_bezout). *)
let fp_bezout_all_masks_intro (#p:int{is_prime p})
  (gbars_fp: list (polynomial (fp p)))
  : Lemma (requires all_irreducible gbars_fp /\ IR.pairwise_coprime gbars_fp)
          (ensures  fp_bezout_all_masks gbars_fp)
  = reveal_opaque (`%fp_bezout_all_masks) (fp_bezout_all_masks gbars_fp);
    let aux (m: list bool)
      : Lemma (L.length m == L.length gbars_fp ==>
                 (exists (s_fp t_fp: polynomial (fp p)).
                    ((s_fp * (masked_prod gbars_fp m))
                     + (t_fp * (masked_prod gbars_fp (negate_mask m)))) = (poly_one #(fp p))))
      = introduce L.length m == L.length gbars_fp ==>
                    (exists (s_fp t_fp: polynomial (fp p)).
                       ((s_fp * (masked_prod gbars_fp m))
                        + (t_fp * (masked_prod gbars_fp (negate_mask m)))) = (poly_one #(fp p)))
        with _hlen. masked_prod_bezout gbars_fp m
    in
    Classical.forall_intro aux

(* ================================================================ *)
(*  7.  CAPSTONE — recombination_complete restated with the mod-p    *)
(*      inputs given on the FP side (Berlekamp's output).            *)
(*                                                                   *)
(*  gbars_fp : all-irreducible all-monic list over the field fp p.   *)
(*  Its poly_fz-image is the zmod-p reduction of the Hensel factors  *)
(*  (to_base_corr).  The true factor g's mod-p image, pulled back to *)
(*  fp p, divides ∏ gbars_fp, so a subset mask EXISTS (D2b) and is   *)
(*  monic-normalised (monic_assoc_eq).  Threading through poly_fz    *)
(*  delivers RecombinationComplete's mod-p hypotheses; the conclusion *)
(*  is the same centered-subset-product, with the mask existential.   *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let recombination_complete_fp
  (p:int{is_prime p}) (n:nat)
  (bigF g k0: polynomial int)
  (gs: list (polynomial (zmod (ppow p (n ++ 1)))))
  (gbars_fp: list (polynomial (fp p)))
  (int_cs: list int)
  : Lemma
      (requires
        bigF = (g * k0) /\ monic g /\
        (poly_to_fp (ppow p (n ++ 1)) bigF) = (poly_prod gs) /\
        L.length gbars_fp == L.length gs /\
        to_base_corr p (n ++ 1) gs (L.map (poly_fz #p) gbars_fp) /\
        all_monic gs /\
        all_irreducible gbars_fp /\
        all_monic gbars_fp /\
        divides (poly_zf (poly_to_base p (n ++ 1) (poly_to_fp (ppow p (n ++ 1)) g)))
                (poly_prod gbars_fp) /\
        IR.pairwise_coprime gbars_fp /\
        (* Kronecker node conditions (mirror recombination_complete) *)
        all_distinct int_cs /\
        deg g < L.length int_cs /\
        (forall (j:nat). j < L.length int_cs ==>
            poly_eval bigF (L.index int_cs j) <> 0) /\
        (ppow p (n ++ 1)) > 2 * (kbound_rhs bigF int_cs))
      (ensures exists (mask: list bool).
          g = (poly_centered (ppow p (n ++ 1)) (masked_prod gs mask)))
  = let pk1 = ppow p (n ++ 1) in
    ppow_gt_one p (n ++ 1);                            (* pk1 > 1 *)
    fp_bezout_all_masks_intro gbars_fp;               (* Bezout from irreducible + pairwise-coprime *)
    let gbars = L.map (poly_fz #p) gbars_fp in
    let gred  = poly_to_base p (n ++ 1) (poly_to_fp pk1 g) in
    H.elim_equatable_laws (polynomial (zmod p)) ();
    H.trans_for_calc (polynomial (zmod p)) ();
    (* monic gred and monic (poly_zf gred) *)
    poly_to_fp_monic pk1 g;                            (* monic (poly_to_fp pk1 g) *)
    to_base_monic p (n ++ 1) (poly_to_fp pk1 g);       (* monic gred *)
    poly_zf_monic gred;                                (* monic (poly_zf gred) *)
    L.map_lemma (poly_fz #p) gbars_fp;                 (* length gbars == length gbars_fp *)
    (* subset mask from divisor-of-irreducible-product (D2b at fp) *)
    divisor_of_irreducible_prod gbars_fp (poly_zf gred);
    eliminate exists (c: fp p) (mask: list bool).
        (L.length mask == L.length gbars_fp /\ (not (c = zero)) /\
         (poly_zf gred = ((poly_const c) * (masked_prod gbars_fp mask))))
    returns (exists (mask': list bool). g = (poly_centered pk1 (masked_prod gs mask')))
    with _.
    begin
      masked_prod_monic () gbars_fp mask;              (* monic (masked_prod gbars_fp mask) *)
      monic_assoc_eq (poly_zf gred) (masked_prod gbars_fp mask) c;  (* poly_zf gred = masked gbars_fp mask *)
      (* transport to zmod:  gred = masked_prod gbars mask *)
      poly_fz_congr (poly_zf gred) (masked_prod gbars_fp mask);
      poly_fz_zf gred;                                 (* poly_fz(poly_zf gred) = gred *)
      poly_fz_masked_prod gbars_fp mask;               (* poly_fz(masked gbars_fp mask) = masked gbars mask *)
      poly_eq_symmetry (poly_fz (poly_zf gred)) gred;
      poly_eq_transitivity gred (poly_fz (poly_zf gred)) (poly_fz (masked_prod gbars_fp mask));
      poly_eq_transitivity gred (poly_fz (masked_prod gbars_fp mask)) (masked_prod gbars mask);
      (* Bezout at the derived mask, transported to zmod *)
      fp_bezout_all_masks_elim gbars_fp mask;
      eliminate exists (s_fp t_fp: polynomial (fp p)).
          (((s_fp * (masked_prod gbars_fp mask))
            + (t_fp * (masked_prod gbars_fp (negate_mask mask)))) = (poly_one #(fp p)))
      returns (exists (mask': list bool). g = (poly_centered pk1 (masked_prod gs mask')))
      with _.
      begin
        bezout_fp_to_zmod gbars_fp mask s_fp t_fp;
        recombination_complete p n bigF g k0 gs gbars mask (poly_fz s_fp) (poly_fz t_fp) int_cs;
        introduce exists (mask': list bool). g = (poly_centered pk1 (masked_prod gs mask'))
        with mask and ()
      end
    end
#pop-options
