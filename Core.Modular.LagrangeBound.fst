module Core.Modular.LagrangeBound

(* ================================================================ *)
(*  §D — toward the Lagrange/Kronecker coefficient bound (ℂ-free).    *)
(*                                                                   *)
(*  Foundation:  if  F = G·K  over ℤ then at any integer point c,     *)
(*    F(c) = G(c)·K(c),  so  G(c) | F(c),  hence  |G(c)| ≤ |F(c)|     *)
(*  whenever F(c) ≠ 0.  Evaluating a factor at enough points and      *)
(*  Lagrange-interpolating then bounds the factor's coefficients by   *)
(*  Σ_j |F(cⱼ)|·‖Lⱼ‖ — the integer (Kronecker) factor bound.          *)
(*                                                                   *)
(*  NO admit / assume / sorry in the final version.                  *)
(* ================================================================ *)

module EV = Core.Polynomial.Eval
module DIV = Core.Algebra.Divisibility

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Eval

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* integer absolute value. *)
let iabs (a:int) : int = if a >= 0 then a else - a

(* evaluation is multiplicative on ℤ[X]:  (G·K)(c) = G(c)·K(c). *)
let eval_mul_int (g k: polynomial int #int_cr) (c: int)
  : Lemma (poly_eval #int #int_cr (g * k) c
           == (poly_eval #int #int_cr g c) * (poly_eval #int #int_cr k c))
  = EV.eval_mul g k c

(* |a·k| = |a|·|k| on ℤ, by sign case-analysis. *)
let iabs_mul (a k: int)
  : Lemma (iabs (a * k) == iabs a * iabs k)
  = ()

(* a non-zero integer has absolute value ≥ 1. *)
let iabs_ge_one (a: int)
  : Lemma (requires a <> 0) (ensures iabs a >= 1)
  = ()

(* divisor bound on ℤ:  b = a·k  and  b ≠ 0  ⇒  |a| ≤ |b|. *)
let int_divides_abs_le (a b: int)
  : Lemma (requires DIV.divides #int #int_cr a b /\ b <> 0)
          (ensures iabs a <= iabs b)
  = (* `divides #int #int_cr a b` unfolds to `exists c. eq b (mul a c)`;
       for `int_cr`, `eq` is `( = )` and `mul` is `( * )`, so the witness
       form `b = a * k` matches the predicate body directly. *)
    eliminate exists (k:int). b = a * k
    returns iabs a <= iabs b
    with _.
    begin
      iabs_mul a k;                               (* iabs b == iabs a * iabs k *)
      assert (iabs b == iabs a * iabs k);
      iabs_ge_one k;                              (* iabs k >= 1 *)
      assert (iabs k >= 1);
      FStar.Math.Lemmas.lemma_mult_le_left (iabs a) 1 (iabs k)
                                                  (* iabs a * 1 <= iabs a * iabs k *)
    end

(* the factor evaluation bound:  F = G·K, F(c) ≠ 0  ⇒  |G(c)| ≤ |F(c)|. *)
let eval_factor_abs_le (f g k: polynomial int #int_cr) (c: int)
  : Lemma (requires f = (g * k) /\
                    poly_eval #int #int_cr f c <> 0)
          (ensures iabs (poly_eval #int #int_cr g c) <= iabs (poly_eval #int #int_cr f c))
  = EV.eval_congruence f (g * k) c;
    eval_mul_int g k c;
    (* poly_eval f c == poly_eval g c * poly_eval k c *)
    assert (poly_eval #int #int_cr f c
            == (poly_eval #int #int_cr g c) * (poly_eval #int #int_cr k c));
    DIV.divides_intro #int #int_cr
      (poly_eval #int #int_cr g c) (poly_eval #int #int_cr f c)
      (poly_eval #int #int_cr k c);
    int_divides_abs_le (poly_eval g c) (poly_eval f c)
