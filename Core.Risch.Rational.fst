module Core.Risch.Rational
(*
   Top-level rational integrator: combines Hermite reduction and LRT.

   Given p/q ∈ k(x) with q monic (or at least nonzero), computes:
     ∫ p/q dx = poly_part(x) + rational_part(x) + log_part(x)

   where:
     - poly_part is a polynomial (from Euclidean division of p by q)
     - rational_part is a proper rational function (from Hermite)
     - log_part is a sum of logarithms (from LRT)

   The algorithm:
     1. Euclidean division: p = q·poly_quot + rem, deg(rem) < deg(q)
     2. Hermite reduction on rem/q → rational part + residual/s (s sqfree)
     3. LRT on residual/s → logarithmic part

   Soundness (to be proven):
     D(poly_part + rational_part + log_part) = p/q
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module PA = Core.Risch.PolyAntideriv

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree
open Core.Risch.Hermite
open Core.Risch.LRT

(* ================================================================ *)
(*  Integration result type                                         *)
(* ================================================================ *)

noeq type rational_integral_result (#t:Type) (f: field t) = {
  (* Polynomial part: integral of the polynomial quotient *)
  poly_part: polynomial t;

  (* Rational part from Hermite reduction:
     list of (numerator, factor, power) triples representing
     Σ gᵢ / Dᵢ^(kᵢ) *)
  hermite_rational: list (polynomial t & polynomial t & nat);

  (* Logarithmic part from LRT *)
  log_part: root_sum f;

  (* The square-free denominator for the log part *)
  sqfree_denom: polynomial t;

  (* Numerator remaining after Hermite (input to LRT) *)
  sqfree_num: polynomial t;
}

(* ================================================================ *)
(*  Polynomial antiderivative: ∫ a_n x^n + ... + a_0 dx             *)
(*    = a_n/(n+1) x^(n+1) + ... + a_0 x                            *)
(* ================================================================ *)

let poly_antideriv (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Pure (polynomial t)
         (requires char_zero f)
         (ensures fun _ -> True)
  = let n = L.length p in
    if n = 0 then poly_zero #t
    else
      let rec build_coeffs (k: nat) (fuel: nat)
        : Pure (list t) (requires fuel <= n /\ (k ++ fuel) == n)
               (ensures fun _ -> True)
               (decreases fuel)
        = if fuel = 0 then []
          else
            let ck = coeff p k in
            let kp1_nat : pos = (k ++ 1) in
            let kp1 : t = nat_scale kp1_nat (one #t) in
            (* char_zero ensures nat_scale (k+1) one ≠ zero *)
            assert (is_nonzero kp1);
            let kp1_inv : t = (f.f_sf.sf_mig).inv kp1 in
            let new_coeff : t = ck * kp1_inv in
            new_coeff :: build_coeffs (k ++ 1) (fuel - 1)
      in
      let coeffs = build_coeffs 0 n in
      trim (zero :: coeffs)

(* ================================================================ *)
(*  Single-factor Hermite: reduce A/D^n to rational + A_final/D     *)
(*  and collect the rational-part terms as concrete triples.        *)
(* ================================================================ *)

let hermite_single_factor (#t:Type) {| f: field t |}
  (a_num: polynomial t)
  (d: polynomial t)
  (n: nat{n >= 1})
  : Pure (list (polynomial t & polynomial t & nat) & polynomial t)
         (requires deg d >= 0 /\ square_free d /\
                  char_zero f)
         (ensures fun _ -> True)
  = let (raw_parts, final_num) = hermite_reduce_power a_num d n in
    (* Convert (g_num, power) pairs to (g_num, d, power) triples *)
    let triples = L.map (fun (g, k) -> (g, d, k)) raw_parts in
    (triples, final_num)

(* ================================================================ *)
(*  Top-level rational integration                                  *)
(*                                                                  *)
(*  Simplified version: assumes the denominator is ALREADY given in  *)
(*  square-free factored form (i.e., Yun has been applied upstream). *)
(*  This avoids reimplementing the full multi-factor partial-fraction*)
(*  pipeline (which requires substantial correctness proof work).    *)
(*                                                                  *)
(*  For the single-factor case (q = D^n with D squarefree), this    *)
(*  gives the complete integration.                                  *)
(* ================================================================ *)

let integrate_rational_single_factor (#t:Type) {| f: field t |}
  (p: polynomial t)
  (d: polynomial t)
  (n: nat{n >= 1})
  : Pure (rational_integral_result f)
         (requires deg d >= 1 /\
                  square_free d /\ char_zero f)
         (ensures fun _ -> True)
  = (* Step 1: Euclidean division by D^n to get proper fraction *)
    let d_power = poly_power d n in
    let (quot, rem) = poly_divmod p d_power in
    (* Step 2: Polynomial antiderivative of the quotient (the PROVEN
       top-level `antideriv`, whose D(∫p)=p soundness is `PA.antideriv_correct`). *)
    let poly_int = PA.antideriv quot in
    (* Step 3: Hermite reduction on rem / D^n *)
    let (hermite_parts, residual_num) =
      hermite_single_factor rem d n in
    (* Step 4: LRT on residual_num / D (square-free denominator) *)
    let log = lrt residual_num d in
    { poly_part = poly_int;
      hermite_rational = hermite_parts;
      log_part = log;
      sqfree_denom = d;
      sqfree_num = residual_num; }
