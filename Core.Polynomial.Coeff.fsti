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
(*  Helpers                                                          *)
(* ================================================================ *)

val sum_range_shift
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (offset lo hi: nat)
  : Lemma (ensures sum_range (fun (j:nat) -> f (Prims.op_Addition j offset)) lo hi
                 = sum_range f (Prims.op_Addition lo offset) (Prims.op_Addition hi offset))
          (decreases (hi - lo))

val sum_range_all_zero
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (lo hi: nat)
  (h: (k: nat{lo <= k /\ k < hi}) -> Lemma (f k = (zero <: t)))
  : Lemma (ensures sum_range f lo hi = (zero <: t))
          (decreases (hi - lo))

(* ================================================================ *)
(*  Convolution identity                                             *)
(* ================================================================ *)

val coeff_poly_mul (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t) (k: nat)
  : Lemma (ensures coeff (poly_mul p q) k
                 = sum_range (fun (i:nat) -> coeff p i * coeff q (Prims.op_Subtraction k i))
                             0 (L.length p))
          (decreases (L.length p))

(* ================================================================ *)
(*  Linearity of coeff over polynomial-valued sum_range             *)
(* ================================================================ *)

val coeff_sum_range (#t:Type) {| cr: commutative_ring t |}
  (f: nat -> polynomial t) (lo hi: nat) (k: nat)
  : Lemma (ensures coeff (sum_range #(polynomial t) #(polynomial_acg cr) f lo hi) k
                 = sum_range (fun (i:nat) -> coeff (f i) k) lo hi)
          (decreases (hi - lo))

(* ================================================================ *)
(*  Monomial decomposition                                           *)
(* ================================================================ *)

val monomial_decomposition (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t) (n: nat{n >= L.length p})
  : Lemma (ensures poly_eq
             (sum_range #(polynomial t) #(polynomial_acg cr)
                (fun (i:nat) -> monomial (coeff p i) i) 0 n)
             p)
