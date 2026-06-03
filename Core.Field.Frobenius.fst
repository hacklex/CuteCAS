module Core.Field.Frobenius

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

module TC = FStar.Tactics.Typeclasses
module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module FR = Core.Algebra.Frobenius
module PW = Core.Algebra.Power
module FM = FStar.Math.Fermat

open Core.Algebra
open Core.Algebra.Notation
open Core.Field.Fp
open Core.Polynomial
open Core.Polynomial.Derivative   (* nat_scale + laws *)
open FStar.Math.Euclid
open FStar.Math.Lemmas

#set-options "--fuel 1 --ifuel 1 --z3rlimit 30"

(* ---------------------------------------------------------------- *)
(*  nat_scale in fp p computes (n · x) mod p                         *)
(* ---------------------------------------------------------------- *)

let rec fp_nat_scale_is_mul (p:int{p > 1}) (n:nat) (x: fp p)
  : Lemma (ensures nat_scale #(fp p) #(fp_acg p) n x == (Prims.op_Star n x) % p)
          (decreases n)
  = if n = 0 then (nat_scale_zero #(fp p) #(fp_acg p) x)
    else begin
      nat_scale_succ #(fp p) #(fp_acg p) (n-1) x;
      fp_nat_scale_is_mul p (n-1) x;
      lemma_mod_add_distr x (Prims.op_Star (n-1) x) p;
      assert (Prims.op_Star n x == x + Prims.op_Star (n-1) x)
    end

(* characteristic p:  nat_scale p x = 0  in fp p. *)
let fp_char_p (p:int{p > 1}) (x: fp p)
  : Lemma (nat_scale #(fp p) #(fp_acg p) p x == fp_zero p)
  = fp_nat_scale_is_mul p p x;
    cancel_mul_mod x p;
    assert (Prims.op_Star p x == x * p)

(* ---------------------------------------------------------------- *)
(*  Frobenius over fp p                                              *)
(* ---------------------------------------------------------------- *)

let frobenius_fp (p:int{is_prime p}) (a b: fp p)
  : Lemma (PW.rpow #(fp p) #((fp_comm_ring p).cr_r) (fp_add a b) (p <: nat)
           = fp_add (PW.rpow #(fp p) #((fp_comm_ring p).cr_r) a (p <: nat))
                    (PW.rpow #(fp p) #((fp_comm_ring p).cr_r) b (p <: nat)))
  = let cr = fp_comm_ring p in
    let char (y: fp p) : Lemma (nat_scale #(fp p) #(cr.cr_r.r_add) p y = (zero <: fp p))
      = fp_char_p p y
    in
    FR.frobenius_add #(fp p) #cr p a b char

(* ---------------------------------------------------------------- *)
(*  coeff commutes with nat_scale over the polynomial ring          *)
(* ---------------------------------------------------------------- *)

let rec coeff_nat_scale (#t:Type) {| cr: commutative_ring t |} (n:nat) (pp: polynomial t) (k:nat)
  : Lemma (ensures coeff (nat_scale #(polynomial t) #(polynomial_acg cr) n pp) k
                   = nat_scale #t #(cr.cr_r.r_add) n (coeff pp k))
          (decreases n)
  = let pacg = polynomial_acg cr in
    let acg = cr.cr_r.r_add in
    H.elim_equatable_laws t (); H.trans_for_calc t ();
    if n = 0 then begin
      nat_scale_zero #(polynomial t) #pacg pp;
      polynomial_acg_zero_reveal cr;
      nat_scale_zero #t #acg (coeff pp k);
      symmetry (nat_scale #t #acg 0 (coeff pp k)) (zero <: t)
    end
    else begin
      nat_scale_succ #(polynomial t) #pacg (n-1) pp;
      polynomial_acg_add_reveal cr pp (nat_scale #(polynomial t) #pacg (n-1) pp);
      coeff_nat_scale #t #cr (n-1) pp k;
      reflexivity (coeff pp k);
      add_congruence (coeff pp k) (coeff (nat_scale #(polynomial t) #pacg (n-1) pp) k)
                     (coeff pp k) (nat_scale #t #acg (n-1) (coeff pp k));
      nat_scale_succ #t #acg (n-1) (coeff pp k);
      symmetry (nat_scale #t #acg n (coeff pp k))
               (coeff pp k + nat_scale #t #acg (n-1) (coeff pp k));
      H.trans3 (coeff (nat_scale #(polynomial t) #pacg n pp) k)
               (coeff pp k + coeff (nat_scale #(polynomial t) #pacg (n-1) pp) k)
               (coeff pp k + nat_scale #t #acg (n-1) (coeff pp k))
               (nat_scale #t #acg n (coeff pp k))
    end

(* ---------------------------------------------------------------- *)
(*  characteristic p for the polynomial ring over fp p              *)
(* ---------------------------------------------------------------- *)

let poly_fp_char_p (p:int{is_prime p}) (pp: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (nat_scale #(polynomial (fp p) #(fp_comm_ring p)) #(polynomial_acg (fp_comm_ring p)) p pp
           = (zero <: polynomial (fp p) #(fp_comm_ring p)))
  = let cr = fp_comm_ring p in
    let pacg = polynomial_acg cr in
    let ns = nat_scale #(polynomial (fp p)) #pacg p pp in
    let coeffs_zero (j:int) : Lemma (coeff ns j = coeff ([] <: polynomial (fp p)) j)
      = if j < 0 then (reflexivity (coeff ns j))
        else begin
          coeff_nat_scale #(fp p) #cr p pp (j <: nat);   (* coeff ns j = nat_scale p (coeff pp j) *)
          fp_char_p p (coeff pp (j <: nat));              (* nat_scale p (coeff pp j) = 0 *)
          assert (coeff ([] <: polynomial (fp p)) j == (zero <: fp p))
        end
    in
    Classical.forall_intro coeffs_zero;
    equal_coeffs_means_poly_eq #(fp p) #cr ns ([] <: polynomial (fp p));
    polynomial_acg_zero_reveal cr

(* ---------------------------------------------------------------- *)
(*  FROBENIUS over (fp p)[x]   (the W1 wall, dissolved)             *)
(*                                                                   *)
(*     (a + b)^p = a^p + b^p   in (fp p)[x].                        *)
(* ---------------------------------------------------------------- *)

(* the polynomial commutative ring over fp p, built explicitly from fp_comm_ring p. *)
let pcr_fp (p:int{p > 1}) : commutative_ring (polynomial (fp p) #(fp_comm_ring p))
  = (polynomial_commutative_ring_instance #(fp p) #(fp_comm_ring p)).pcr

let frobenius_poly_fp (p:int{is_prime p})
  (a b: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (PW.rpow #(polynomial (fp p) #(fp_comm_ring p)) #((pcr_fp p).cr_r)
                   (poly_add a b) (p <: nat)
           = poly_add (PW.rpow #(polynomial (fp p) #(fp_comm_ring p)) #((pcr_fp p).cr_r) a (p <: nat))
                      (PW.rpow #(polynomial (fp p) #(fp_comm_ring p)) #((pcr_fp p).cr_r) b (p <: nat)))
  = let pcr = pcr_fp p in
    (* pcr.cr_r.r_add IS polynomial_acg (fp_comm_ring p) definitionally *)
    let char (y: polynomial (fp p) #(fp_comm_ring p))
      : Lemma (nat_scale #(polynomial (fp p) #(fp_comm_ring p)) #(pcr.cr_r.r_add) p y
               = (zero <: polynomial (fp p) #(fp_comm_ring p)))
      = poly_fp_char_p p y
    in
    FR.frobenius_add #(polynomial (fp p) #(fp_comm_ring p)) #pcr p a b char

(* ---------------------------------------------------------------- *)
(*  Fermat's little theorem in fp p:   c^p = c.                      *)
(* ---------------------------------------------------------------- *)

(* rpow c n in fp p equals (pow c n) mod p. *)
let rec fp_rpow_is_pow (p:int{p > 1}) (c: fp p) (n:nat)
  : Lemma (ensures PW.rpow #(fp p) #((fp_comm_ring p).cr_r) c n == (FM.pow c n) % p)
          (decreases n)
  = if n = 0 then small_mod 1 p
    else begin
      fp_rpow_is_pow p c (n-1);
      lemma_mod_mul_distr_r c (FM.pow c (n-1)) p;
      assert (FM.pow c n == c * FM.pow c (n-1))
    end

(* Fermat:  c^p = c  in fp p. *)
let fermat_fp (p:int{is_prime p}) (c: fp p)
  : Lemma (PW.rpow #(fp p) #((fp_comm_ring p).cr_r) c (p <: nat) == c)
  = fp_rpow_is_pow p c p;        (* rpow c p = pow c p % p *)
    FM.fermat p c;               (* pow c p % p = c % p *)
    small_mod c p                (* c % p = c *)
