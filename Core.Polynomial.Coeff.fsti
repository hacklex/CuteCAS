module Core.Polynomial.Coeff

(*
   Coefficient-level theory for polynomial multiplication.

   Main results:
     - coeff_poly_mul: convolution identity
     - coeff_sum_range: linearity of coeff over polynomial-valued sum_range
     - monomial_decomposition: p = sum_range (fun i -> monomial (coeff p i) i) 0 n
*)

module L = FStar.List.Tot

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.FinSum

(* ================================================================ *)
(*  Convolution identity                                             *)
(* ================================================================ *)

val coeff_poly_mul (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t) (k: nat)
  : Lemma (ensures coeff (p * q) k
                 = sum_range (fun (i:nat) -> coeff p i * coeff q ((k - i)))
                             0 (L.length p))

(* ================================================================ *)
(*  Linearity of coeff over polynomial-valued sum_range             *)
(* ================================================================ *)

val coeff_sum_range (#t:Type) {| cr: commutative_ring t |}
  (f: nat -> polynomial t) (lo hi: nat) (k: nat)
  : Lemma (ensures coeff (sum_range f lo hi) k
                 = sum_range (fun (i:nat) -> coeff (f i) k) lo hi)
          (decreases (hi - lo))

(* ================================================================ *)
(*  Monomial decomposition                                           *)
(* ================================================================ *)

val monomial_decomposition (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t) (n: nat{n >= L.length p})
  : Lemma (ensures (sum_range
                (fun (i:nat) -> monomial (coeff p i) i) 0 n)
             = p)

(* ================================================================ *)
(*  Named-function variant of coeff_poly_mul                         *)
(* ================================================================ *)

val coeff_poly_mul_named (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t) (k: nat) (g: nat -> t)
  (h: (i:nat) -> Lemma (g i = coeff p i * coeff q ((k - i))))
  : Lemma (ensures coeff (p * q) k = sum_range g 0 (L.length p))
