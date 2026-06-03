module Core.Field.BerlekampFrobenius

(* ================================================================ *)
(*  The Frobenius map  φ(g) = g^p  is ADDITIVE modulo f over        *)
(*  (fp p)[x].  This is the precise fact that makes the Berlekamp    *)
(*  Q matrix 𝔽_p-linear (Q is the matrix of β ↦ β^p on the basis    *)
(*  1, x, …, x^{n-1} of (fp p)[x]/(f)).                              *)
(*                                                                   *)
(*      (a + b)^p ≡ a^p + b^p   (mod f)   in (fp p)[x].             *)
(*                                                                   *)
(*  Bridges Core.Field.Frobenius.frobenius_poly_fp (the genuine      *)
(*  freshman's-dream identity, exact in (fp p)[x]) to the           *)
(*  congruence-modulo-f layer of Core.Field.Berlekamp.               *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module PW = Core.Algebra.Power
module CF = Core.Field.Frobenius
module BK = Core.Field.Berlekamp

open Core.Algebra
open Core.Algebra.Notation
open Core.Field.Fp
open Core.Polynomial
open FStar.Math.Euclid

#set-options "--fuel 1 --ifuel 1 --z3rlimit 30"

(* The polynomial commutative ring over fp p (from Core.Field.Frobenius). *)
let pcr (p:int{p > 1}) : commutative_ring (polynomial (fp p) #(fp_comm_ring p))
  = CF.pcr_fp p

(* ---------------------------------------------------------------- *)
(*  Exact freshman's dream in (fp p)[x]  (re-export, rpow form).    *)
(* ---------------------------------------------------------------- *)

let frobenius_add_exact (p:int{is_prime p})
  (a b: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (poly_eq (PW.rpow #(polynomial (fp p) #(fp_comm_ring p)) #((pcr p).cr_r)
                            (poly_add a b) (p <: nat))
                   (poly_add (PW.rpow #(polynomial (fp p) #(fp_comm_ring p)) #((pcr p).cr_r) a (p <: nat))
                             (PW.rpow #(polynomial (fp p) #(fp_comm_ring p)) #((pcr p).cr_r) b (p <: nat))))
  = CF.frobenius_poly_fp p a b

(* ---------------------------------------------------------------- *)
(*  Bridge: Berlekamp's poly_pow (field-form) = rpow (ring-form).   *)
(* ---------------------------------------------------------------- *)

let rec poly_pow_is_rpow (p:int{is_prime p}) (g: polynomial (fp p) #(fp_comm_ring p)) (k:nat)
  : Lemma (ensures BK.poly_pow #(fp p) #(fp_field p) g k
                   == PW.rpow #(polynomial (fp p) #(fp_comm_ring p)) #((pcr p).cr_r) g k)
          (decreases k)
  = if k = 0 then ()
    else poly_pow_is_rpow p g (k-1)

(* ---------------------------------------------------------------- *)
(*  Frobenius map is additive modulo f  (Berlekamp poly_pow form).  *)
(*                                                                   *)
(*     (a+b)^p ≡ a^p + b^p   (mod f).                               *)
(* ---------------------------------------------------------------- *)

let frobenius_additive_mod_f (p:int{is_prime p})
  (f a b: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (BK.cong #(polynomial (fp p) #(fp_comm_ring p)) #(pcr p)
                   f
                   (BK.poly_pow #(fp p) #(fp_field p) (poly_add a b) (p <: nat))
                   (poly_add (BK.poly_pow #(fp p) #(fp_field p) a (p <: nat))
                             (BK.poly_pow #(fp p) #(fp_field p) b (p <: nat))))
  = let cr = pcr p in
    (* exact freshman's dream:  (a+b)^p  poly_eq  a^p + b^p *)
    CF.frobenius_poly_fp p a b;
    (* rewrite both poly_pow's to rpow's *)
    poly_pow_is_rpow p (poly_add a b) p;
    poly_pow_is_rpow p a p;
    poly_pow_is_rpow p b p;
    (* the two sides are poly_eq (= over the polynomial ring), so congruent mod f *)
    let lhs = BK.poly_pow #(fp p) #(fp_field p) (poly_add a b) (p <: nat) in
    let rhs = poly_add (BK.poly_pow #(fp p) #(fp_field p) a (p <: nat))
                       (BK.poly_pow #(fp p) #(fp_field p) b (p <: nat)) in
    (* lhs = rhs  (poly_eq) ; cong f rhs rhs (refl) ; cong_eq_right gives cong f rhs lhs? we want cong f lhs rhs *)
    BK.cong_refl #(polynomial (fp p) #(fp_comm_ring p)) #cr f lhs;   (* cong f lhs lhs *)
    BK.cong_eq_right #(polynomial (fp p) #(fp_comm_ring p)) #cr f lhs lhs rhs
