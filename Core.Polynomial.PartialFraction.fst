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
         (requires deg d1 >= 0 /\ coprime d1 d2)
         (ensures fun _ -> True)
  = let (s, tt, g) = poly_ext_gcd d1 d2 in
    coprime_reveal d1 d2;
    ext_gcd_is_gcd d1 d2;
    degree_zero_is_singleton g;
    let c : t = poly_lc g in
    let cinv : t = inv c in
    let scale : polynomial t = [cinv] in
    (scale * s, scale * tt)

(* ================================================================ *)
(*  Two-factor partial fraction decomposition                       *)
(* ================================================================ *)

let partial_fraction_two (#t:Type) {| f: field t |}
  (p d1 d2: polynomial t)
  : Pure (polynomial t & polynomial t)
         (requires deg d1 >= 0 /\ deg d2 >= 0 /\
                  coprime d1 d2)
         (ensures fun _ -> True)
  = let (s_norm, t_norm) = normalize_bezout d1 d2 in
    let a1_raw = p * t_norm in
    let a1 = poly_rem a1_raw d1 in
    let remainder = (p -- (a1 * d2)) in
    let a2 = poly_div remainder d1 in
    (a1, a2)

(* ================================================================ *)
(*  Bezout correctness of normalize_bezout                           *)
(*    For coprime d1 d2, the returned (s,t) satisfy s*d1 + t*d2 = 1   *)
(*    (as polynomials, up to poly_eq).                               *)
(* ================================================================ *)

let normalize_bezout_correct (#t:Type) {| f: field t |}
  (d1 d2: polynomial t)
  : Lemma (requires deg d1 >= 0 /\ coprime d1 d2)
          (ensures (let (s_n, t_n) = normalize_bezout d1 d2 in
                    (((s_n * d1) + (t_n * d2)) = (poly_one #t))))
  = let (s, tt, g) = poly_ext_gcd d1 d2 in
    coprime_reveal d1 d2;
    ext_gcd_is_gcd d1 d2;
    degree_zero_is_singleton g;                 (* g == [poly_lc g], lc g <> 0 *)
    let c : t = poly_lc g in
    let cinv : t = inv c in
    let scale : polynomial t = [cinv] in
    ext_gcd_correct d1 d2;                (* poly_eq (add (mul s d1)(mul tt d2)) g *)
    let xx : polynomial t = s * d1 in
    let yy : polynomial t = tt * d2 in
    assert ((xx + yy) = g);        (* class ops are defeq to poly ops *)
    poly_left_distributivity scale xx yy;
    poly_eq_reflexivity scale;
    poly_mul_congruence scale (xx + yy) scale g;
    poly_mul_associativity scale s d1;
    poly_mul_associativity scale tt d2;
    let a1 : polynomial t = ((scale * s) * d1) in
    let b1 : polynomial t = ((scale * tt) * d2) in
    let sxx : polynomial t = (scale * xx) in
    let syy : polynomial t = (scale * yy) in
    let sadd : polynomial t = (scale * (xx + yy)) in
    let sg : polynomial t = (scale * g) in
    poly_add_congruence a1 b1 sxx syy;
    poly_eq_symmetry sadd (sxx + syy);
    poly_eq_transitivity (a1 + b1) (sxx + syy) sadd;
    poly_eq_transitivity (a1 + b1) sadd sg;
    singleton_inv_mul_singleton c;        (* poly_eq (poly_mul [cinv] [c]) poly_one *)
    assert (g == [c]);
    assert (sg = (poly_one #t));
    poly_eq_transitivity (a1 + b1) sg (poly_one #t)

(* ================================================================ *)
(*  Named Bezout cofactors (cf. poly_div / poly_rem for poly_divmod) *)
(*    bezout_left d1 d2  = fst (normalize_bezout d1 d2)   (cofactor of d1) *)
(*    bezout_right d1 d2 = snd (normalize_bezout d1 d2)   (cofactor of d2) *)
(*  characterized by bezout_identity:                                 *)
(*    bezout_left*d1 + bezout_right*d2 ~ 1.                            *)
(* ================================================================ *)

let bezout_left (#t:Type) {| f: field t |} (d1 d2: polynomial t)
  : Pure (polynomial t)
         (requires deg d1 >= 0 /\ coprime d1 d2)
         (ensures fun _ -> True)
  = fst (normalize_bezout d1 d2)

let bezout_right (#t:Type) {| f: field t |} (d1 d2: polynomial t)
  : Pure (polynomial t)
         (requires deg d1 >= 0 /\ coprime d1 d2)
         (ensures fun _ -> True)
  = snd (normalize_bezout d1 d2)

let bezout_left_reveal (#t:Type) {| f: field t |} (d1 d2: polynomial t)
  : Lemma (requires deg d1 >= 0 /\ coprime d1 d2)
          (ensures bezout_left d1 d2 == fst (normalize_bezout d1 d2))
  = ()

let bezout_right_reveal (#t:Type) {| f: field t |} (d1 d2: polynomial t)
  : Lemma (requires deg d1 >= 0 /\ coprime d1 d2)
          (ensures bezout_right d1 d2 == snd (normalize_bezout d1 d2))
  = ()

(* Characterizing identity (cf. poly_divmod_correct). *)
let bezout_identity (#t:Type) {| f: field t |} (d1 d2: polynomial t)
  : Lemma (requires deg d1 >= 0 /\ coprime d1 d2)
          (ensures ((((bezout_left d1 d2) * d1)
                     + ((bezout_right d1 d2) * d2))
                    = (poly_one #t)))
  = normalize_bezout_correct d1 d2
