module Core.Risch.RationalEuclid

(* ================================================================ *)
(*  §F — the Euclidean fraction identity for the rational integrator.*)
(*                                                                   *)
(*  If  p = quot·q + rem  (Euclidean division of p by q), then        *)
(*     p/q  =  quot/1  +  rem/q     (as fractions).                   *)
(*                                                                   *)
(*  This splits the integrand p/q into the POLYNOMIAL part (quot,     *)
(*  integrated by `antideriv`) and the PROPER fraction rem/q          *)
(*  (handled by Hermite + LRT).                                       *)
(*                                                                   *)
(*  NO admit / assume / sorry in the final version.                  *)
(* ================================================================ *)

module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Fractions
open Core.Fractions.Derivative

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* The pure polynomial cross-product identity behind the fraction equality.
   Given  p ~ quot*q + rem, we have
     p * (poly_one * q)  ~  q * (quot*q + poly_one*rem)
   because both sides reduce (up to commutativity) to (quot*q + rem) * q. *)
let euclid_cross_product (#t:Type) {| cr: commutative_ring t |}
  (p q quot rem: polynomial t)
  : Lemma (requires p = (quot * q) + rem)
          (ensures  (p * ((poly_one #t) * q))
                      = (q * ((quot * q) + ((poly_one #t) * rem))))
  = H.elim_equatable_laws (polynomial t) ();
    let a  : polynomial t = (quot * q) + rem in
    let oq : polynomial t = (poly_one #t) * q in
    let orr: polynomial t = (poly_one #t) * rem in
    (* poly_one*q ~ q  and  poly_one*rem ~ rem *)
    poly_mul_one q;                          (* poly_mul oq poly_one ~ q AND poly_mul poly_one q ~ q *)
    poly_mul_one rem;                        (* poly_mul poly_one rem ~ rem *)
    (* ---- LHS:  p * oq  ~  a * q ----------------------------------- *)
    (* oq ~ q, p ~ a, so p*oq ~ a*q *)
    poly_mul_congruence p oq a q;            (* needs poly_eq p a /\ poly_eq oq q *)
    (* ---- RHS:  q * (quot*q + orr)  ~  q * a  ~  a * q ------------- *)
    poly_add_congruence (quot * q) orr (quot * q) rem;  (* quot*q + orr ~ quot*q + rem = a *)
    poly_mul_congruence q ((quot * q) + orr) q a;        (* q*(quot*q+orr) ~ q*a *)
    poly_mul_commutativity q a;              (* q*a ~ a*q *)
    poly_eq_transitivity (q * ((quot * q) + orr))
                         (q * a)
                         (a * q);     (* RHS ~ a*q *)
    (* ---- glue: LHS ~ a*q ~ RHS ------------------------------------ *)
    poly_eq_symmetry (q * ((quot * q) + orr)) (a * q);
    poly_eq_transitivity (p * oq)
                         (a * q)
                         (q * ((quot * q) + orr))

let euclid_fraction_identity (#t:Type) {| f: field t |}
  (p q quot rem: polynomial t)
  : Lemma (requires is_nonzero #_ q /\
                    p = ((quot * q) + rem))
          (ensures
            (Fraction p q)
            = (fraction_add
                 (poly_to_rational quot)
                 (Fraction rem q)))
  = let id_p = polynomial_id #t #(id_of_f t) in
    (* poly_to_rational quot == Fraction quot poly_one *)
    polynomial_one_ne_zero #t #(id_of_f t);
    let xq : fraction id_p = Fraction quot (poly_one #t) in
    let yr : fraction id_p = Fraction rem q in
    let lhs : fraction id_p = Fraction p q in
    let rhs : fraction id_p = fraction_add xq yr in
    (* num(rhs) == quot*q + poly_one*rem, den(rhs) == poly_one*q
       (fraction ring ops on `polynomial t` are poly_mul / poly_add) *)
    fraction_add_reveal xq yr;
    (* lhs = rhs  <==>  p * den(rhs) = q * num(rhs) *)
    fraction_eq_reveal lhs rhs;
    (* discharge the cross product as a polynomial identity *)
    euclid_cross_product p q quot rem
