module Core.Polynomial.KroneckerHeightBound

(* ================================================================ *)
(*  §D bridge — the WHOLE-FACTOR HEIGHT BOUND.                       *)
(*                                                                   *)
(*  Lifts the per-coefficient Kronecker bound                        *)
(*    |coeff g i| <= kbound_rhs bigF int_cs   (all i)                *)
(*  to the ∞-norm (height) bound                                     *)
(*    poly_height g <= kbound_rhs bigF int_cs                        *)
(*  that the centered-lift recovery (`poly_centered_recovers_small`) *)
(*  needs.                                                           *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Roots
open Core.Polynomial.Eval
open Core.Polynomial.EmbedQProd
open Core.Polynomial.Lagrange
open Core.Polynomial.Height
open Core.Polynomial.KroneckerBound

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------- *)
(*  (1) max_abs_upto_le : a uniform coefficient bound on i < n       *)
(*      (with the bound nonnegative) caps max_abs_upto p n.          *)
(* ---------------------------------------------------------------- *)

#push-options "--fuel 2"
let rec max_abs_upto_le (p: polynomial int) (n: nat) (b: int)
  : Lemma (requires b >= 0 /\
                    (forall (i:nat). i < n ==> iabs (coeff p i) <= b))
          (ensures max_abs_upto p n <= b)
          (decreases n)
  = if n = 0 then ()
    else begin
      max_abs_upto_le p (n - 1) b;                       (* m = max_abs_upto p (n-1) <= b *)
      assert (iabs (coeff p (n - 1)) <= b)               (* a = iabs (coeff p (n-1)) <= b *)
      (* max_abs_upto p n = if m >= a then m else a; both m,a <= b. *)
    end
#pop-options

(* ---------------------------------------------------------------- *)
(*  (2) poly_height_le_of_coeff_bound.                               *)
(* ---------------------------------------------------------------- *)

let poly_height_le_of_coeff_bound (g: polynomial int) (b: int)
  : Lemma (requires b >= 0 /\
                    (forall (i:nat). iabs (coeff g i) <= b))
          (ensures poly_height g <= b)
  = max_abs_upto_le g (L.length g) b

(* ---------------------------------------------------------------- *)
(*  (3a) kbound_rhs is nonnegative.                                 *)
(*       kterm j >= 0 (iabs >= 0, poly_height >= 0, product nonneg)  *)
(*       and int_sum of nonnegatives is nonnegative.                *)
(* ---------------------------------------------------------------- *)

let kterm_nonneg (bigF: polynomial int) (int_cs: list int) (j: nat)
  : Lemma (kterm bigF int_cs j >= 0)
  = if j < L.length int_cs then begin
      Core.Fractions.RationalAbs.iabs_nonneg
        (poly_eval bigF (L.index int_cs j));
      height_nonneg (int_prod_linears (delete_index int_cs j))
    end
    else ()

#push-options "--fuel 2"
let rec int_sum_nonneg (h: nat -> int) (lo hi: nat)
  : Lemma (requires (forall (j:nat). h j >= 0))
          (ensures int_sum h lo hi >= 0)
          (decreases (if hi <= lo then 0 else hi - lo))
  = if hi <= lo then ()
    else int_sum_nonneg h lo (hi - 1)
#pop-options

let kbound_rhs_nonneg (bigF: polynomial int) (int_cs: list int)
  : Lemma (kbound_rhs bigF int_cs >= 0)
  = Classical.forall_intro (kterm_nonneg bigF int_cs);
    int_sum_nonneg (kterm bigF int_cs) 0 (L.length int_cs)

(* ---------------------------------------------------------------- *)
(*  (3) MAIN — the whole-factor height bound.                       *)
(* ---------------------------------------------------------------- *)

let kronecker_height_bound
  (g k bigF: polynomial int) (int_cs: list int)
  : Lemma (requires
        bigF = g * k /\
        all_distinct int_cs /\
        deg g < L.length int_cs /\
        (forall (j:nat). j < L.length int_cs ==>
            poly_eval bigF (L.index int_cs j) <> 0))
      (ensures poly_height g <= kbound_rhs bigF int_cs)
  = let b = kbound_rhs bigF int_cs in
    kbound_rhs_nonneg bigF int_cs;                       (* b >= 0 *)
    (* the requires is i-independent and holds here; discharge it per-i. *)
    introduce forall (i:nat). iabs (coeff g i) <= b
    with begin
      kronecker_coeff_bound g k bigF int_cs i            (* RA.iabs (coeff g i) <= b *)
      (* Height.iabs and RA.iabs are definitionally equal. *)
    end;
    poly_height_le_of_coeff_bound g b
