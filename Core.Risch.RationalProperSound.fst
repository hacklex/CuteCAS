module Core.Risch.RationalProperSound

(*
   CAPSTONE (proper-fraction part) of rational-integrator soundness,
   conditional on the single remaining gap-b hypothesis: that the LRT log
   fraction integrates  final/d.

   Given that hypothesis, the full proper part

       nn / d^(n-1)  +  log

   integrates  rem / d^n :

       D( nn / d^(n-1)  +  log )  =  rem / d^n.

   Assembly of three facts over  fraction id_p :
     (1) additivity of D over fraction_add        (rational_deriv_add)
     (2) the hypothesis  D(log) = final/d, lifted by right-congruence
     (3) the Hermite fraction identity             (hermite_fraction_identity)

   NO admit / assume / sorry.
*)

module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree
open Core.Fractions
open Core.Fractions.Derivative
open Core.Fractions.DerivativeSum
open Core.Risch.Hermite
open Core.Risch.HermiteFracLift
open Core.Risch.RTSoundness

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

let proper_part_sound (#t:Type) {| f: field t |}
  (rem d: polynomial t) (n: nat{n >= 1}) (log_frac: rational_function f)
  : Lemma (requires deg d >= 0 /\ square_free d /\ char_zero f /\
                    rational_deriv log_frac
                      = Fraction (snd (hermite_reduce_power rem d n)) d)
          (ensures
            rational_deriv
              (fraction_add
                 (Fraction
                    (combined_num (fst (hermite_reduce_power rem d n)) d)
                    (poly_power d (n - 1)))
                 log_frac)
            = Fraction rem (poly_power d n))
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    let (parts, final) = hermite_reduce_power rem d n in
    let nn   = combined_num parts d in
    let dm   = poly_power d (n - 1) in
    let dn   = poly_power d n in
    let hf   : fraction id_p = Fraction nn dm in
    let ffinal : fraction id_p = Fraction final d in
    let proper = fraction_add hf log_frac in
    (* (1) D(proper) = D(hf) (+) D(log_frac). *)
    rational_deriv_add hf log_frac;
    (* (2) D(log_frac) = final/d  (hypothesis), so by right-congruence
           D(hf) (+) D(log_frac) = D(hf) (+) final/d. *)
    frac_add_cong_r
      (rational_deriv hf) (rational_deriv log_frac) ffinal;
    (* (3) Hermite fraction identity:
           D(hf) (+) final/d = rem / d^n. *)
    hermite_fraction_identity rem d n
