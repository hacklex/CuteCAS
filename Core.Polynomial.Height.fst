module Core.Polynomial.Height

(* ================================================================ *)
(*  Polynomial ∞-norm (height) over ℤ[X].                           *)
(*                                                                   *)
(*    poly_height p = max over coefficients of |coeff p i|.          *)
(*                                                                   *)
(*  Basic bounds toward the §D Kronecker coefficient bound:          *)
(*    - height_nonneg       : poly_height p >= 0                     *)
(*    - coeff_abs_le_height : |coeff p i| <= poly_height p           *)
(*    - height_add_le       : height (p+q) <= height p + height q    *)
(*                                                                   *)
(*  Integer-only.  NO admit / assume / sorry.                        *)
(* ================================================================ *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Int
open Core.Polynomial
open Core.Polynomial.Eval

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* integer absolute value (re-derived locally per scope guidance). *)
let iabs (a:int) : int = if a >= 0 then a else - a

(* ---------------------------------------------------------------- *)
(*  max of |coeff p i| over i < n.                                  *)
(* ---------------------------------------------------------------- *)

let rec max_abs_upto (p: polynomial int) (n: nat) : int =
  if n = 0 then 0
  else
    let m = max_abs_upto p (n - 1) in
    let a = iabs (coeff p (n - 1)) in
    if m >= a then m else a

let poly_height (p: polynomial int) : int =
  max_abs_upto p (L.length p)

(* ---------------------------------------------------------------- *)
(*  max_abs_upto is nonnegative.                                    *)
(* ---------------------------------------------------------------- *)

let rec max_abs_upto_nonneg (p: polynomial int) (n: nat)
  : Lemma (ensures max_abs_upto p n >= 0)
          (decreases n)
  = if n = 0 then ()
    else max_abs_upto_nonneg p (n - 1)

let height_nonneg (p: polynomial int)
  : Lemma (poly_height p >= 0)
  = max_abs_upto_nonneg p (L.length p)

(* ---------------------------------------------------------------- *)
(*  max_abs_upto dominates each |coeff p i| for i < n.              *)
(* ---------------------------------------------------------------- *)

let rec max_abs_upto_dominates (p: polynomial int) (n: nat) (i: nat)
  : Lemma (requires i < n)
          (ensures iabs (coeff p i) <= max_abs_upto p n)
          (decreases n)
  = if n = 0 then ()
    else if i = n - 1 then ()
    else max_abs_upto_dominates p (n - 1) i

let coeff_abs_le_height (p: polynomial int) (i: nat)
  : Lemma (iabs (coeff p i) <= poly_height p)
  = if i < L.length p
    then max_abs_upto_dominates p (L.length p) i
    else begin
      (* coeff p i = 0 (int_cr.zero), so iabs 0 = 0 <= height. *)
      assert (coeff p i == 0);
      height_nonneg p
    end

(* ---------------------------------------------------------------- *)
(*  height_add_le.                                                  *)
(* ---------------------------------------------------------------- *)

(* For each index i, the |coeff (p+q) i| is bounded by the sum of    *)
(* heights, via the triangle inequality and coeff_abs_le_height.     *)
let coeff_add_abs_bound (p q: polynomial int) (i: nat)
  : Lemma (iabs (coeff (poly_add p q) i)
           <= poly_height p + poly_height q)
  = poly_add_coeff p q i;             (* coeff (p+q) i = coeff p i + coeff q i *)
    coeff_abs_le_height p i;
    coeff_abs_le_height q i

(* max_abs_upto (p+q) n <= height p + height q, by induction on n.   *)
let rec max_abs_upto_add_le (p q: polynomial int) (n: nat)
  : Lemma (ensures max_abs_upto (poly_add p q) n
                   <= poly_height p + poly_height q)
          (decreases n)
  = if n = 0 then begin
      height_nonneg p;
      height_nonneg q
    end
    else begin
      max_abs_upto_add_le p q (n - 1);
      coeff_add_abs_bound p q (n - 1)
    end

let height_add_le (p q: polynomial int)
  : Lemma (poly_height (poly_add p q)
           <= poly_height p + poly_height q)
  = max_abs_upto_add_le p q (L.length (poly_add p q))

(* ---------------------------------------------------------------- *)
(*  height_scale: poly_height (poly_scale a p) = |a| * poly_height p *)
(* ---------------------------------------------------------------- *)

module R = Core.Polynomial.Roots

(* |a*k| = |a|*|k| on ℤ, by sign case-analysis. *)
let iabs_mul (a k: int)
  : Lemma (iabs (a * k) == iabs a * iabs k)
  = ()

(* max_abs_upto stabilizes past the polynomial's length: extending n by
   one beyond length adds a zero coefficient, contributing iabs 0 = 0. *)
let rec max_abs_upto_stable (p: polynomial int) (n: nat)
  : Lemma (requires n >= L.length p)
          (ensures max_abs_upto p n == poly_height p)
          (decreases n)
  = if n = L.length p then ()
    else begin
      (* coeff p (n-1) = 0 since n-1 >= length p, so the step contributes 0. *)
      assert (coeff p (n - 1) == 0);
      max_abs_upto_nonneg p (n - 1);
      max_abs_upto_stable p (n - 1)
    end

(* per-index coefficient identity for poly_scale over ℤ. *)
let coeff_scale (a: int) (p: polynomial int) (i: nat)
  : Lemma (coeff (R.poly_scale a p) i == a * coeff p i)
  = poly_mul_singleton_coeff a p i

(* max_abs_upto (poly_scale a p) n = |a| * max_abs_upto p n, for |a| >= 0. *)
let rec max_abs_upto_scale (a: int) (p: polynomial int) (n: nat)
  : Lemma (ensures max_abs_upto (R.poly_scale a p) n
                   == iabs a * max_abs_upto p n)
          (decreases n)
  = if n = 0 then ()
    else begin
      max_abs_upto_scale a p (n - 1);
      coeff_scale a p (n - 1);
      iabs_mul a (coeff p (n - 1));
      max_abs_upto_nonneg p (n - 1)
      (* now: M' = iabs a * M, x' = iabs a * x, iabs a >= 0;
         step picks max; mult by nonneg distributes over max — F* by (). *)
    end

let height_scale (a: int) (p: polynomial int)
  : Lemma (poly_height (R.poly_scale a p) == iabs a * poly_height p)
  = let sp = R.poly_scale a p in
    let n = (if L.length sp >= L.length p then L.length sp else L.length p) in
    max_abs_upto_scale a p n;          (* max_abs_upto sp n == iabs a * max_abs_upto p n *)
    max_abs_upto_stable sp n;          (* max_abs_upto sp n == poly_height sp *)
    max_abs_upto_stable p n            (* max_abs_upto p  n == poly_height p  *)
