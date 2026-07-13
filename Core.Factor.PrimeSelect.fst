module Core.Factor.PrimeSelect

(* ================================================================ *)
(*  M2 · S4 — good-prime selection for Zassenhaus factoring.        *)
(*                                                                   *)
(*  For a squarefree primitive  B ∈ ℤ[z]  we pick a prime `p` with   *)
(*    (1)  p ∤ lc(B)          (leading coeff invertible mod p)       *)
(*    (2)  deg B̄ = deg B      (B̄ = B mod p keeps its degree)         *)
(*    (3)  B̄ squarefree over 𝔽ₚ                                       *)
(*  so Berlekamp (S5) may factor B̄ and Hensel-lift (S6/S7) back.     *)
(*                                                                   *)
(*  reduce_to_fp  = poly_zf ∘ poly_to_fp   (ℤ → ℤ/p → 𝔽ₚ, reused).   *)
(*  is_good_prime = executable Tot bool (squarefreeness is decidable *)
(*                  via `coprime B̄ B̄'` in Core.Polynomial.SquareFree)*)
(*  find_good_prime = search over a supplied prime-candidate list;   *)
(*    unconditional termination (decreases list); success guaranteed *)
(*    by a decidable existence witness `good_in_list`.               *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L = FStar.List.Tot

open Core.NumberTheory
open Core.Algebra
open Core.Algebra.Int
open Core.Polynomial
open Core.Polynomial.SquareFree
open Core.Modular.ResidueRing
open Core.Modular.ResidueRing.Centered
open Core.Modular.ResidueRing.CenteredPoly
open Core.Modular.PrimeField
open Core.Modular.FpZmodBridge

#set-options "--fuel 2 --ifuel 1 --z3rlimit 20"

(* ---------------------------------------------------------------- *)
(*  1.  reduce_to_fp : ℤ[z] → 𝔽ₚ[z]  (coefficient-wise a ↦ a mod p). *)
(*      Reuses the existing ℤ→ℤ/p and ℤ/p→𝔽ₚ poly reductions.        *)
(* ---------------------------------------------------------------- *)

let reduce_to_fp (p:int{is_prime p}) (b: polynomial int) : polynomial (fp p)
  = poly_zf #p (poly_to_fp p b)

(* coefficient characterisation:  coeff (B̄) i = (coeff b i) mod p. *)
let reduce_to_fp_coeff (p:int{is_prime p}) (b: polynomial int) (i:int)
  : Lemma (coeff (reduce_to_fp p b) i == zf (to_fp p (coeff b i)))
  = poly_zf_coeff #p (poly_to_fp p b) i;
    poly_to_fp_coeff p b i

(* ---------------------------------------------------------------- *)
(*  2.  is_good_prime : executable Tot bool.                         *)
(* ---------------------------------------------------------------- *)

let is_good_prime (p:int{is_prime p}) (b: polynomial int) : bool
  =    ((poly_lc b) % p <> 0)                     (* (1) p ∤ lc B    *)
    && (deg (reduce_to_fp p b) = deg b)           (* (2) same degree *)
    && square_free (reduce_to_fp p b)             (* (3) squarefree  *)

(* ---------------------------------------------------------------- *)
(*  Soundness — what S5 (Berlekamp) consumes: a good prime yields a  *)
(*  valid B̄ (same degree + squarefree over 𝔽ₚ, lc invertible mod p). *)
(* ---------------------------------------------------------------- *)

let good_prime_sound (p:int{is_prime p}) (b: polynomial int)
  : Lemma (requires is_good_prime p b)
          (ensures  (poly_lc b) % p <> 0 /\
                    deg (reduce_to_fp p b) == deg b /\
                    square_free (reduce_to_fp p b))
  = ()

(* If deg B ≥ 1, a good prime gives a nonzero B̄ of the same degree,
   hence a genuine degree-(deg b) polynomial for Berlekamp. *)
let good_prime_degree (p:int{is_prime p}) (b: polynomial int)
  : Lemma (requires is_good_prime p b /\ deg b >= 1)
          (ensures  deg (reduce_to_fp p b) == deg b /\
                    ~(reduce_to_fp p b == poly_zero #(fp p)))
  = good_prime_sound p b;
    deg_neg_one_iff_zero (reduce_to_fp p b)

(* ---------------------------------------------------------------- *)
(*  3.  find_good_prime : search a candidate prime-list.            *)
(*                                                                   *)
(*  Termination: unconditional (decreases the list).  Success: a     *)
(*  decidable witness `good_in_list` guarantees the returned prime   *)
(*  satisfies `is_good_prime`.  (The number-theoretic fact that a    *)
(*  squarefree primitive B has only finitely many bad primes — the   *)
(*  divisors of lc(B)·disc(B) — hence such a list is always          *)
(*  populatable, is stated for the caller as `good_in_list`.)        *)
(* ---------------------------------------------------------------- *)

let good_in_list (b: polynomial int) (ps: list (p:int{is_prime p})) : bool
  = L.existsb (fun (p:(q:int{is_prime q})) -> is_good_prime p b) ps

let rec find_good_prime (b: polynomial int)
  (ps: list (p:int{is_prime p}))
  (h: squash (good_in_list b ps == true))
  : Tot (p:int{is_prime p /\ is_good_prime p b}) (decreases ps)
  = match ps with
    | [] -> false_elim ()
    | p :: rest ->
        if is_good_prime p b then p
        else find_good_prime b rest ()
