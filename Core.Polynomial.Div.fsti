module Core.Polynomial.Div

(*
   Euclidean division of univariate polynomials over a field, ported to
   the new Core.Polynomial tower.

   Provides:
     - monomial constructor
     - polynomial subtraction (poly_sub)
     - leading-coefficient non-vanishing
     - Euclidean division (poly_divmod) over a field
     - structural correctness: p ~ q * quot + rem
     - degree-bound correctness: deg rem < deg q (or None)
     - polynomial_euclidean_domain_instance assembly
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial

(* ------------------------------------------------------------------ *)
(*  Monomial: monomial c n = c*x^n = [0;...;0;c] with n leading zeros *)
(* ------------------------------------------------------------------ *)

val monomial (#t:Type) {| cr: commutative_ring t |} (c: t) (n: nat)
  : polynomial t

val monomial_zero_n_reveal (#t:Type) {| cr: commutative_ring t |} (c: t)
  : Lemma (monomial c 0 == (if c = zero then [] else [c]))

val monomial_succ_n_reveal (#t:Type) {| cr: commutative_ring t |}
                           (c: t) (n: nat)
  : Lemma (monomial c (Prims.op_Addition n 1) ==
           (if c = zero then []
            else (zero <: t) :: monomial c n))

(* ------------------------------------------------------------------ *)
(*  Polynomial subtraction                                            *)
(* ------------------------------------------------------------------ *)

val poly_sub (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : polynomial t

val poly_sub_reveal (#t:Type) {| cr: commutative_ring t |}
                    (p q: polynomial t)
  : Lemma (poly_sub p q == poly_add p (poly_neg q))

(* p ~ (p - s) + s.  Group-cancellation identity. (Private to .fst — users
   should derive this directly from the commutative_ring axioms.)         *)

(* ------------------------------------------------------------------ *)
(*  Leading coefficient                                               *)
(* ------------------------------------------------------------------ *)

(* If poly_deg p = Some d, then coeff p d is nonzero.                 *)
val leading_coeff_nonzero (#t:Type) {| cr: commutative_ring t |}
                          (p: polynomial t)
  : Lemma (requires Some? (poly_deg p))
          (ensures  not ((coeff p (Some?.v (poly_deg p))) = (zero <: t)))

(* ------------------------------------------------------------------ *)
(*  Coefficient identities (public surface)                           *)
(* ------------------------------------------------------------------ *)

val coeff_above_degree (#t:Type) {| cr: commutative_ring t |}
                       (p: polynomial t) (i: nat)
  : Lemma (requires None? (poly_deg p) \/ Some?.v (poly_deg p) < i)
          (ensures  coeff p i = (zero <: t))

val poly_sub_coeff (#t:Type) {| cr: commutative_ring t |}
                   (p q: polynomial t) (i: nat)
  : Lemma (coeff (poly_sub p q) i = ((coeff p i) + (- (coeff q i))))

(* degree (monomial c n) = if c = zero then None else Some n.         *)
val monomial_deg (#t:Type) {| cr: commutative_ring t |}
                       (c: t) (n: nat)
  : Lemma (ensures (if c = (zero <: t)
                    then poly_deg (monomial c n) == None
                    else poly_deg (monomial c n) == Some n))

(* coeff (monomial c n) i: equals c when i = n, zero otherwise.       *)
val monomial_coeff (#t:Type) {| cr: commutative_ring t |}
                     (c: t) (n: nat) (i: nat)
  : Lemma (ensures (if i = n then coeff (monomial c n) i = c
                    else coeff (monomial c n) i = (zero <: t)))

(* coeff (zero @ p) (i+1) = coeff p i.                                  *)
val zero_shift_coeff (#t:Type) {| cr: commutative_ring t |}
                     (p: polynomial t) (i: nat)
  : Lemma (ensures coeff ((zero <: t) @ p) (Prims.op_Addition i 1) = coeff p i)

(* coeff (poly_mul (monomial c k) q) (k+j) = c * coeff q j.            *)
val monomial_mul_coeff (#t:Type) {| cr: commutative_ring t |}
                          (c: t) (k: nat) (q: polynomial t) (j: nat)
  : Lemma (ensures coeff (poly_mul (monomial c k) q) (Prims.op_Addition k j)
                   = c * (coeff q j))

(* ------------------------------------------------------------------ *)
(*  Degree bounds for poly_neg, poly_add, poly_sub                     *)
(* ------------------------------------------------------------------ *)

val poly_neg_degree (#t:Type) {| cr: commutative_ring t |}
                    (p: polynomial t)
  : Lemma (ensures poly_deg (poly_neg p) == poly_deg p)

val poly_add_degree_bound (#t:Type) {| cr: commutative_ring t |}
                          (p q: polynomial t) (k: nat)
  : Lemma (requires (None? (poly_deg p) \/ Some?.v (poly_deg p) < k) /\
                    (None? (poly_deg q) \/ Some?.v (poly_deg q) < k))
          (ensures  None? (poly_deg (poly_add p q)) \/
                    Some?.v (poly_deg (poly_add p q)) < k)

val poly_sub_degree_bound (#t:Type) {| cr: commutative_ring t |}
                          (p q: polynomial t) (k: nat)
  : Lemma (requires (None? (poly_deg p) \/ Some?.v (poly_deg p) < k) /\
                    (None? (poly_deg q) \/ Some?.v (poly_deg q) < k))
          (ensures  None? (poly_deg (poly_sub p q)) \/
                    Some?.v (poly_deg (poly_sub p q)) < k)

(* ------------------------------------------------------------------ *)
(*  Euclidean division                                                 *)
(* ------------------------------------------------------------------ *)

val poly_divmod (#t:Type) {| f: field t |} (p q: polynomial t)
  : polynomial t & polynomial t

val poly_divmod_correct (#t:Type) {| f: field t |}
                        (p q: polynomial t)
  : Lemma (let (quot, rem) = poly_divmod #t #f p q in
           poly_eq p (poly_add (poly_mul q quot) rem))

val poly_divmod_correct_degree (#t:Type) {| f: field t |}
                               (p q: polynomial t)
  : Lemma (requires Some? (poly_deg q))
          (ensures (let (_, rem) = poly_divmod #t #f p q in
                    None? (poly_deg rem) \/
                    Some?.v (poly_deg rem) < Some?.v (poly_deg q)))

val polynomial_euclidean_domain_instance
    (#t:Type) {| f: field t |}
  : polynomial_euclidean_domain t
       #f
       #(polynomial_commutative_ring_instance #t #(cr_of_id t #(id_of_f t)))
       #(polynomial_integral_domain_instance  #t #(id_of_f t))
