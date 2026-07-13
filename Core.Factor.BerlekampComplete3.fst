module Core.Factor.BerlekampComplete3

(* ================================================================ *)
(*  C5d · PART B — the matrix <-> Frobenius REPRESENTATION.          *)
(*                                                                   *)
(*  Establishes that the (transposed) Berlekamp matrix genuinely     *)
(*  represents the Frobenius(-id) endomorphism  frob h = (h^p mod    *)
(*  fbar) - h  under NS.mat_vec_mul, hence its null space equals the *)
(*  Berlekamp subalgebra  { h : h^p ≡ h (mod fbar) }.                *)
(*                                                                   *)
(*  Mathematical heart:  the ITERATED FRESHMAN'S DREAM               *)
(*     (Σ_i f i)^p  ≡  Σ_i (f i)^p   (mod fbar)                      *)
(*  (frobenius_additive_mod_f iterated over a finite sum_range).     *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L   = FStar.List.Tot
module NS  = Core.LinearAlgebra.FpNullSpace
module BF  = Core.Factor.BerlekampFactor
module FM  = Core.Factor.FrobeniusMatrix
module BK  = Core.Modular.PrimeField.Berlekamp
module CF  = Core.Modular.PrimeField.Frobenius
module CM  = Core.Algebra.CongruenceMod
module CS  = Core.Polynomial.Coeff
module PW  = Core.Algebra.Power
module IR  = Core.Polynomial.Irreducible
module H   = Core.Algebra.Helpers
module EU  = Core.NumberTheory

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div
open Core.FinSum
open Core.Modular.PrimeField

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ================================================================ *)
(*  1.  ITERATED FRESHMAN'S DREAM over a finite sum.                 *)
(*                                                                   *)
(*     poly_power (sum_range f lo hi) p                              *)
(*        ≡  sum_range (fun i -> poly_power (f i) p) lo hi           *)
(*     (mod fbar).                                                   *)
(* ================================================================ *)

let pw (p:int{EU.is_prime p}) (g: polynomial (fp p)) : polynomial (fp p)
  = poly_power #(fp p) g (p <: nat)

(* poly_power = rpow on the fp-polynomial ring (both are the naive fold). *)
let rec pw_is_rpow (p:int{EU.is_prime p}) (g: polynomial (fp p)) (k:nat)
  : Lemma (ensures poly_power #(fp p) g k == PW.rpow #(polynomial (fp p)) g k)
          (decreases k)
  = if k = 0 then () else pw_is_rpow p g (k - 1)

(* freshman's dream modulo fbar:  (a+b)^p ≡ a^p + b^p  (mod fbar). *)
let frob_add_mod (p:int{EU.is_prime p}) (fbar a b: polynomial (fp p))
  : Lemma (CM.cong #(polynomial (fp p)) fbar (pw p (a + b)) ((pw p a) + (pw p b)))
  = CF.frobenius_poly_fp p a b;               (* rpow(a+b) p = rpow a p + rpow b p *)
    pw_is_rpow p (a + b) p;
    pw_is_rpow p a p;
    pw_is_rpow p b p;
    (* pw p (a+b) = pw p a + pw p b  (poly_eq =), hence congruent mod fbar *)
    CM.cong_of_eq #(polynomial (fp p)) fbar (pw p (a + b)) ((pw p a) + (pw p b))

(* base:  poly_power zero p  =  zero  (poly_eq), for p >= 1. *)
let pw_zero (p:int{EU.is_prime p})
  : Lemma (pw p (zero #(polynomial (fp p))) = (zero #(polynomial (fp p))))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    H.trans_for_calc (polynomial (fp p)) ();
    let z : polynomial (fp p) = zero #(polynomial (fp p)) in
    (* p >= 1 : poly_power z p = z * poly_power z (p-1) ; z * _ = zero *)
    assert (pw p z == z * (poly_power #(fp p) z (p - 1)));
    H.x_mul_zero #(polynomial (fp p)) (poly_power #(fp p) z (p - 1));
    (* zero * y = zero ; here z is the LEFT factor: use zero_mul via commutativity *)
    mul_commutativity z (poly_power #(fp p) z (p - 1));
    H.x_mul_zero #(polynomial (fp p)) (poly_power #(fp p) z (p - 1))

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec frob_sum_mod (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  (f: nat -> polynomial (fp p)) (lo hi: nat)
  : Lemma (ensures CM.cong #(polynomial (fp p)) fbar
                     (pw p (sum_range f lo hi))
                     (sum_range (fun (i:nat) -> pw p (f i)) lo hi))
          (decreases (hi - lo))
  = let g (i:nat) : polynomial (fp p) = pw p (f i) in
    if lo >= hi then begin
      sum_range_empty f lo hi;                (* sum_range f lo hi == zero *)
      sum_range_empty g lo hi;                (* sum_range g lo hi == zero *)
      pw_zero p;                              (* pw p zero = zero *)
      (* pw p (sum_range f lo hi) = pw p zero = zero = sum_range g lo hi *)
      CM.cong_of_eq #(polynomial (fp p)) fbar
        (pw p (sum_range f lo hi)) (sum_range g lo hi)
    end
    else begin
      H.elim_equatable_laws (polynomial (fp p)) ();
      let sf : polynomial (fp p) = sum_range f lo hi in
      let sg : polynomial (fp p) = sum_range g lo hi in
      sum_range_unfold_right f lo hi;         (* sf = a + b *)
      sum_range_unfold_right g lo hi;         (* sg = sg' + g (hi-1) *)
      let a : polynomial (fp p) = sum_range f lo (hi - 1) in
      let b : polynomial (fp p) = f (hi - 1) in
      let sg' : polynomial (fp p) = sum_range g lo (hi - 1) in
      (* freshman:  cong fbar (a+b)^p  (a^p + b^p) *)
      frob_add_mod p fbar a b;
      (* IH:  cong fbar (a^p) sg' *)
      frob_sum_mod p fbar f lo (hi - 1);
      (* cong fbar (b^p) (b^p) *)
      CM.cong_refl #(polynomial (fp p)) fbar (pw p b);
      (* cong fbar (a^p + b^p) (sg' + b^p) *)
      CM.cong_add #(polynomial (fp p)) fbar (pw p a) sg' (pw p b) (pw p b);
      (* transitivity: (a+b)^p ≡ a^p+b^p ≡ sg'+b^p *)
      CM.cong_trans #(polynomial (fp p)) fbar
        (pw p (a + b)) ((pw p a) + (pw p b)) (sg' + (pw p b));
      (* bridge LEFT endpoint: sf = a+b (poly_eq)  ==>  pw sf = pw (a+b) *)
      poly_power_congruence #(fp p) sf (a + b) (p <: nat);
      CM.cong_of_eq #(polynomial (fp p)) fbar (pw p sf) (pw p (a + b));
      CM.cong_trans #(polynomial (fp p)) fbar (pw p sf) (pw p (a + b)) (sg' + (pw p b));
      (* bridge RIGHT endpoint: sg' + pw b = sg (poly_eq, since g (hi-1) = pw b) *)
      CM.cong_of_eq #(polynomial (fp p)) fbar (sg' + (pw p b)) sg;
      CM.cong_trans #(polynomial (fp p)) fbar (pw p sf) (sg' + (pw p b)) sg
    end
#pop-options

(* ================================================================ *)
(*  2.  SCALAR pulls out of Frobenius:                              *)
(*        (monomial c i)^p  =  poly_const c * (x^i)^p               *)
(*  (Fermat  c^p = c  makes the leading scalar a fixed point.)      *)
(* ================================================================ *)

(* local copy of Berlekamp.const0_pow (not exported by its interface):
   (poly_const c)^k = poly_const (rpow c k). *)
let rec const_pow_rpow (p:int{EU.is_prime p}) (c: fp p) (k:nat)
  : Lemma (ensures (poly_power #(fp p) (poly_const #(fp p) c) k)
                   = (poly_const #(fp p) (PW.rpow #(fp p) c k)))
          (decreases k)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let c0 = poly_const #(fp p) c in
    if k = 0 then begin
      PW.rpow_zero #(fp p) c;
      poly_const_one #(fp p) ()
    end else begin
      let pk1 = poly_power #(fp p) c0 (k - 1) in
      let rk1 = PW.rpow #(fp p) c (k - 1) in
      PW.rpow_succ #(fp p) c (k - 1);
      const_pow_rpow p c (k - 1);
      poly_mul_congruence c0 pk1 c0 (poly_const #(fp p) rk1);
      poly_const_mul #(fp p) c rk1;
      transitivity (c0 * pk1)
                   (c0 * (poly_const #(fp p) rk1))
                   (poly_const #(fp p) (c * rk1))
    end

(* the constant poly is a Frobenius fixed point:  (poly_const c)^p = poly_const c. *)
let pw_const_fixed (p:int{EU.is_prime p}) (c: fp p)
  : Lemma (pw p (poly_const #(fp p) c) = (poly_const #(fp p) c))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    const_pow_rpow p c p;               (* pw (poly_const c) = poly_const (rpow c p) *)
    CF.fermat_fp p c;                   (* rpow c p == c *)
    poly_const_congr #(fp p) (PW.rpow #(fp p) c p) c;
    transitivity (pw p (poly_const #(fp p) c))
                 (poly_const #(fp p) (PW.rpow #(fp p) c p))
                 (poly_const #(fp p) c)

(* monomial c i  =  poly_const c * x^i. *)
let mono_const_eq (p:int{EU.is_prime p}) (c: fp p) (i:nat)
  : Lemma ((monomial #(fp p) c i) = ((poly_const #(fp p) c) * (BF.mono_x p i)))
  = H.elim_equatable_laws (fp p) ();
    poly_eq_by_coeff #(fp p) (monomial #(fp p) c i) ((poly_const #(fp p) c) * (BF.mono_x p i))
      (fun (j:nat) ->
        H.elim_equatable_laws (fp p) ();
        monomial_coeff #(fp p) c i j;
        monomial_mul_coeff #(fp p) c 0 (BF.mono_x p i) j;   (* coeff rhs j = c * coeff(mono_x i) j *)
        monomial_coeff #(fp p) (fp_one p) i j;              (* coeff(mono_x i) j = fp_one if j=i else 0 *)
        if j = i then fp_mul_one #p c
        else NS.fp_mul_zero #p c)

(* (monomial c i)^p  =  poly_const c * (x^i)^p. *)
let pw_monomial (p:int{EU.is_prime p}) (c: fp p) (i:nat)
  : Lemma (pw p (monomial #(fp p) c i)
           = ((poly_const #(fp p) c) * (pw p (BF.mono_x p i))))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let mci = monomial #(fp p) c i in
    let mx  = BF.mono_x p i in
    let c0  = poly_const #(fp p) c in
    mono_const_eq p c i;                                    (* mci = c0 * mx *)
    poly_power_congruence #(fp p) mci (c0 * mx) (p <: nat); (* pw mci = pw (c0*mx) *)
    IR.poly_power_mul #(fp p) c0 mx (p <: nat);            (* pw (c0*mx) = pw c0 * pw mx *)
    pw_const_fixed p c;                                     (* pw c0 = c0 *)
    poly_mul_congruence (pw p c0) (pw p mx) c0 (pw p mx);   (* pw c0 * pw mx = c0 * pw mx *)
    transitivity (pw p mci) (pw p (c0 * mx)) ((pw p c0) * (pw p mx));
    transitivity (pw p mci) ((pw p c0) * (pw p mx)) (c0 * (pw p mx))
