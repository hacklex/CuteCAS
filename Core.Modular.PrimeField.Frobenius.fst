module Core.Modular.PrimeField.Frobenius

(* ================================================================ *)
(*  Frobenius additivity instantiated for the finite prime field    *)
(*  fp p and for polynomial (fp p):                                  *)
(*                                                                   *)
(*     (a + b)^p = a^p + b^p     in fp p   and   in (fp p)[x].       *)
(*                                                                   *)
(*  Discharges the characteristic-p hypothesis of                    *)
(*  Core.Algebra.Frobenius.frobenius_add:                            *)
(*    - in fp p:           nat_scale p x = 0   (since (p·x) % p = 0) *)
(*    - in (fp p)[x]:      coefficient-wise from the fp p fact.      *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module H  = Core.Algebra.Helpers
module FR = Core.Algebra.Frobenius
module PW = Core.Algebra.Power
module FM = FStar.Math.Fermat
module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Modular.PrimeField
open Core.Modular.PrimeField.Poly  (* fp_poly_cr : commutative_ring (polynomial (fp p)) *)
open Core.Polynomial
open Core.Polynomial.Derivative   (* nat_scale + laws *)
open Core.NumberTheory
open FStar.Math.Lemmas

#set-options "--fuel 1 --ifuel 1 --z3rlimit 30"

(* ---------------------------------------------------------------- *)
(*  nat_scale in fp p computes (n · x) mod p                         *)
(* ---------------------------------------------------------------- *)

let rec fp_nat_scale_is_mul (p:int{is_prime p}) (n:nat) (x: fp p)
  : Lemma (ensures nat_scale #(fp p) n x == (Prims.op_Star n x) % p)
          (decreases n)
  = if n = 0 then (nat_scale_zero #(fp p) x)
    else begin
      nat_scale_succ #(fp p) (n-1) x;
      fp_nat_scale_is_mul p (n-1) x;
      lemma_mod_add_distr x (Prims.op_Star (n-1) x) p;
      assert (Prims.op_Star n x == x + Prims.op_Star (n-1) x)
    end

(* characteristic p:  nat_scale p x = 0  in fp p. *)
let fp_char_p (p:int{is_prime p}) (x: fp p)
  : Lemma (nat_scale #(fp p) p x == fp_zero p)
  = fp_nat_scale_is_mul p p x;
    cancel_mul_mod x p;
    assert (Prims.op_Star p x == x * p)

(* ---------------------------------------------------------------- *)
(*  Frobenius over fp p                                              *)
(* ---------------------------------------------------------------- *)

let frobenius_fp (p:int{is_prime p}) (a b: fp p)
  : Lemma (PW.rpow #(fp p) (fp_add a b) p
           = fp_add (PW.rpow #(fp p) a p)
                    (PW.rpow #(fp p) b p))
  = let char (y: fp p) : Lemma (nat_scale p y = (zero <: fp p))
      = fp_char_p p y
    in
    FR.frobenius_add p a b char

(* ---------------------------------------------------------------- *)
(*  coeff commutes with nat_scale over the polynomial ring          *)
(* ---------------------------------------------------------------- *)

let rec coeff_nat_scale (#t:Type) {| cr: commutative_ring t |} (n:nat) (pp: polynomial t) (k:nat)
  : Lemma (ensures coeff (nat_scale n pp) k
                   = nat_scale n (coeff pp k))
          (decreases n)
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    if n = 0 then begin
      nat_scale_zero #(polynomial t) pp;
      nat_scale_zero #t (coeff pp k)
    end
    else begin
      nat_scale_succ #(polynomial t) (n-1) pp;
      coeff_nat_scale (n-1) pp k;
      add_congruence (coeff pp k) (coeff (nat_scale #(polynomial t) (n-1) pp) k)
                     (coeff pp k) (nat_scale #t (n-1) (coeff pp k));
      nat_scale_succ #t (n-1) (coeff pp k);
      H.trans3 (coeff (nat_scale #(polynomial t) n pp) k)
               (coeff pp k + coeff (nat_scale #(polynomial t) (n-1) pp) k)
               (coeff pp k + nat_scale #t (n-1) (coeff pp k))
               (nat_scale #t n (coeff pp k))
    end

(* ---------------------------------------------------------------- *)
(*  characteristic p for the polynomial ring over fp p              *)
(* ---------------------------------------------------------------- *)

let poly_fp_char_p (p:int{is_prime p}) (pp: polynomial (fp p))
  : Lemma (nat_scale p pp
           = (zero <: polynomial (fp p)))
  = let ns = nat_scale #(polynomial (fp p)) p pp in
    let coeffs_zero (j:int) : Lemma (coeff ns j = coeff ([] <: polynomial (fp p)) j)
      = if j < 0 then (reflexivity (coeff ns j))
        else begin
          coeff_nat_scale p pp (j <: nat);   (* coeff ns j = nat_scale p (coeff pp j) *)
          fp_char_p p (coeff pp (j <: nat));              (* nat_scale p (coeff pp j) = 0 *)
          assert (coeff ([] <: polynomial (fp p)) j == (zero <: fp p))
        end
    in
    Classical.forall_intro coeffs_zero;
    equal_coeffs_means_poly_eq #(fp p) ns ([] <: polynomial (fp p))

(* ---------------------------------------------------------------- *)
(*  FROBENIUS over (fp p)[x]   (the W1 wall, dissolved)             *)
(*                                                                   *)
(*     (a + b)^p = a^p + b^p   in (fp p)[x].                        *)
(* ---------------------------------------------------------------- *)

let frobenius_poly_fp (p:int{is_prime p})
  (a b: polynomial (fp p))
  : Lemma (PW.rpow #(polynomial (fp p))
                   (a + b) p
           = (PW.rpow #(polynomial (fp p)) a p)
                      + (PW.rpow #(polynomial (fp p)) b p))
  = let char (y: polynomial (fp p))
      : Lemma (nat_scale p y
               = (zero <: polynomial (fp p)))
      = poly_fp_char_p p y
    in
    FR.frobenius_add p a b char

(* ---------------------------------------------------------------- *)
(*  Fermat's little theorem in fp p:   c^p = c.                      *)
(* ---------------------------------------------------------------- *)

(* rpow c n in fp p equals (pow c n) mod p. *)
let rec fp_rpow_is_pow (p:int{is_prime p}) (c: fp p) (n:nat)
  : Lemma (ensures PW.rpow #(fp p) c n == (FM.pow c n) % p)
          (decreases n)
  = if n = 0 then small_mod 1 p
    else begin
      fp_rpow_is_pow p c (n-1);
      lemma_mod_mul_distr_r c (FM.pow c (n-1)) p;
      assert (FM.pow c n == c * FM.pow c (n-1))
    end

(* Fermat:  c^p = c  in fp p. *)
let fermat_fp (p:int{is_prime p}) (c: fp p)
  : Lemma (PW.rpow #(fp p) c p == c)
  = is_prime_to_eu p;            (* NT.is_prime p ==> FStar.Math.Euclid.is_prime p (for FM.fermat) *)
    fp_rpow_is_pow p c p;        (* rpow c p = pow c p % p *)
    FM.fermat p c;               (* pow c p % p = c % p *)
    small_mod c p                (* c % p = c *)
