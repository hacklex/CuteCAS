module Core.Risch.RationalSingleSound

(*
   HEADLINE rational-integrator soundness (single-factor case), conditional
   on the single isolated gap-b hypothesis: that the LRT log fraction
   integrates  final/d.

   For the integrand  p / d^n  (d square-free, char 0):  IF  D(log) = final/d
   (where (parts,final) = hermite_reduce_power rem d n,  (quot,rem) = p / d^n),
   THEN the integrator's poly-part derivative plus the proper-part derivative
   equals  p / d^n :

       D( ∫quot )  (+)  D( nn/d^(n-1) (+) log )  =  p / d^n.

   Clean composition of:
     - the Euclidean split  p ~ quot·d^n + rem            (poly_divmod_correct)
     - the proper-part soundness  D(proper) = rem/d^n     (proper_part_sound)
     - the reduction to the proper part                   (rational_split_sound)

   NO admit / assume / sorry.
*)

module H  = Core.Algebra.Helpers
module PA = Core.Risch.PolyAntideriv

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree
open Core.Polynomial.Irreducible
open Core.Fractions
open Core.Fractions.Derivative
open Core.Risch.Hermite
open Core.Risch.RationalProperSound
open Core.Risch.RationalSplit

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* is_nonzero (poly_power d n)  from  deg d >= 0  with  n >= 1. *)
let power_nonzero_from_deg (#t:Type) {| f: field t |}
  (d: polynomial t) (n: nat{n >= 1})
  : Lemma (requires deg d >= 0)
          (ensures  is_nonzero (poly_power d n))
  = poly_power_has_degree d n;                    (* deg dn >= 0 *)
    poly_zero_is_unique (poly_power d n)           (* poly_eq dn 0 <==> dn == [] *)

let rational_single_factor_sound (#t:Type) {| f: field t |}
  (p d: polynomial t) (n: nat{n >= 1}) (log_frac: rational_function f)
  : Lemma (requires deg d >= 0 /\ square_free d /\ char_zero f /\
                    rational_deriv log_frac
                      = Fraction
                          (snd (hermite_reduce_power
                                  (snd (poly_divmod p (poly_power d n))) d n))
                          d)
          (ensures
            (fraction_add
               (rational_deriv
                  (poly_to_rational
                     (PA.antideriv (fst (poly_divmod p (poly_power d n))))))
               (rational_deriv
                  (fraction_add
                     (Fraction
                        (combined_num
                           (fst (hermite_reduce_power
                                   (snd (poly_divmod p (poly_power d n))) d n))
                           d)
                        (poly_power d (n - 1)))
                     log_frac)))
            = Fraction p (poly_power d n))
  = H.elim_equatable_laws (polynomial t) ();
    let dn   = poly_power d n in
    let (quot, rem) = poly_divmod p dn in
    let (parts, final) = hermite_reduce_power rem d n in
    let nn   = combined_num parts d in
    let proper : rational_function f =
      fraction_add
        (Fraction nn (poly_power d (n - 1)))
        log_frac in
    (* (1) Euclidean split, flipped product:  p ~ quot·dn + rem.
           poly_eq p (poly_add (poly_mul dn quot) rem) is auto-adjoined by the
           poly_divmod p dn binding above. *)
    poly_mul_commutativity dn quot;
    (* poly_eq (poly_mul dn quot) (poly_mul quot dn). *)
    poly_add_congruence
      (dn * quot) rem (quot * dn) rem;
    (* poly_eq (poly_add (poly_mul dn quot) rem)
              (poly_add (poly_mul quot dn) rem). *)
    poly_eq_transitivity
      p
      ((dn * quot) + rem)
      ((quot * dn) + rem);
    (* (2) Proper-part soundness:  D(proper) = rem/dn.  Its log-hypothesis is
           exactly this lemma's requires. *)
    proper_part_sound rem d n log_frac;
    (* (3) is_nonzero dn  (needed by rational_split_sound's  is_nonzero q). *)
    power_nonzero_from_deg d n;
    (* (4) Compose:  rational_split_sound's ensures IS this lemma's ensures. *)
    rational_split_sound p dn quot rem proper
