module Core.Polynomial.PartialFraction
(*
   Partial fraction decomposition for univariate polynomials over a field.

   Given coprime d₁, d₂ and a numerator p, computes (a₁, a₂) such that:
     p = a₁·d₂ + a₂·d₁
   i.e., p/(d₁·d₂) = a₁/d₁ + a₂/d₂ as fractions.

   Construction via extended GCD (Bézout identity):
     ext_gcd(d₁, d₂) gives (s, t, g) with s·d₁ + t·d₂ ~ g ~ [c]
     Normalize by c⁻¹: (s/c)·d₁ + (t/c)·d₂ ~ [1]
     Then a₁ = (p · t/c) mod d₁, and a₂ = (p - a₁·d₂) / d₁.
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD

(* ================================================================ *)
(*  Normalization: divide ext_gcd coefficients by the gcd constant  *)
(* ================================================================ *)

let normalize_bezout (#t:Type) {| f: field t |}
  (d1 d2: polynomial t)
  : Pure (polynomial t & polynomial t)
         (requires Some? (poly_deg d1) /\ coprime #t #f d1 d2)
         (ensures fun _ -> True)
  = let (s, tt, g) = poly_ext_gcd #t #f d1 d2 in
    coprime_reveal #t #f d1 d2;
    ext_gcd_is_gcd #t #f d1 d2;
    degree_zero_is_singleton g;
    let c : t = poly_lc g in
    let cinv : t = (f.f_sf.sf_mig).inv c in
    let scale : polynomial t = [cinv] in
    (poly_mul scale s, poly_mul scale tt)

(* ================================================================ *)
(*  Two-factor partial fraction decomposition                       *)
(* ================================================================ *)

let partial_fraction_two (#t:Type) {| f: field t |}
  (p d1 d2: polynomial t)
  : Pure (polynomial t & polynomial t)
         (requires Some? (poly_deg d1) /\ Some? (poly_deg d2) /\
                  coprime #t #f d1 d2)
         (ensures fun _ -> True)
  = let (s_norm, t_norm) = normalize_bezout #t #f d1 d2 in
    let a1_raw = poly_mul p t_norm in
    let a1 = snd (poly_divmod #t #f a1_raw d1) in
    let remainder = poly_sub p (poly_mul a1 d2) in
    let a2 = fst (poly_divmod #t #f remainder d1) in
    (a1, a2)

(* ================================================================ *)
(*  Bezout correctness of normalize_bezout                           *)
(*    For coprime d1 d2, the returned (s,t) satisfy s*d1 + t*d2 = 1   *)
(*    (as polynomials, up to poly_eq).                               *)
(* ================================================================ *)

let normalize_bezout_correct (#t:Type) {| f: field t |}
  (d1 d2: polynomial t)
  : Lemma (requires Some? (poly_deg d1) /\ coprime #t #f d1 d2)
          (ensures (let (s_n, t_n) = normalize_bezout #t #f d1 d2 in
                    poly_eq (poly_add (poly_mul s_n d1) (poly_mul t_n d2))
                            (poly_one #t)))
  = let (s, tt, g) = poly_ext_gcd #t #f d1 d2 in
    coprime_reveal #t #f d1 d2;
    ext_gcd_is_gcd #t #f d1 d2;
    degree_zero_is_singleton g;                 (* g == [poly_lc g], lc g <> 0 *)
    let c : t = poly_lc g in
    let cinv : t = (f.f_sf.sf_mig).inv c in
    let scale : polynomial t = [cinv] in
    ext_gcd_correct #t #f d1 d2;                (* poly_eq (add (mul s d1)(mul tt d2)) g *)
    let xx : polynomial t = poly_mul s d1 in
    let yy : polynomial t = poly_mul tt d2 in
    assert (poly_eq (poly_add xx yy) g);        (* class ops are defeq to poly ops *)
    poly_left_distributivity scale xx yy;
    poly_eq_reflexivity scale;
    poly_mul_congruence scale (poly_add xx yy) scale g;
    poly_mul_associativity scale s d1;
    poly_mul_associativity scale tt d2;
    let a1 : polynomial t = poly_mul (poly_mul scale s) d1 in
    let b1 : polynomial t = poly_mul (poly_mul scale tt) d2 in
    let sxx : polynomial t = poly_mul scale xx in
    let syy : polynomial t = poly_mul scale yy in
    let sadd : polynomial t = poly_mul scale (poly_add xx yy) in
    let sg : polynomial t = poly_mul scale g in
    poly_add_congruence a1 b1 sxx syy;
    poly_eq_symmetry sadd (poly_add sxx syy);
    poly_eq_transitivity (poly_add a1 b1) (poly_add sxx syy) sadd;
    poly_eq_transitivity (poly_add a1 b1) sadd sg;
    singleton_inv_mul_singleton #t #f c;        (* poly_eq (poly_mul [cinv] [c]) poly_one *)
    assert (g == [c]);
    assert (poly_eq sg (poly_one #t));
    poly_eq_transitivity (poly_add a1 b1) sg (poly_one #t)
