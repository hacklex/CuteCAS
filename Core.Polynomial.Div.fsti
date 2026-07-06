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
(*  Monomial constructor (monomial / monomial_*_reveal) and the basic   *)
(*  monomial/coeff facts (coeff_above_degree, monomial_deg,             *)
(*  monomial_coeff, zero_shift_coeff, monomial_mul_coeff) now live in   *)
(*  Core.Polynomial — they are basic polynomial facts, not division.    *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(*  Polynomial subtraction                                            *)
(* ------------------------------------------------------------------ *)

(* Polynomial subtraction is NOT a primitive: it is exactly the generic
   add-comm-group subtraction `p + (- q)` (= `p -- q` once Notation is open),
   exposed `unfold` so that `poly_sub p q`, `p -- q`, and `poly_add p (poly_neg q)`
   are the SAME term everywhere (no opaque wrapper, no cross-module unification
   gap). Downstream code should prefer the `( -- )` operator; this alias remains
   only until the last call-sites are migrated. *)
unfold let poly_sub (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : polynomial t
  = poly_add p (poly_neg q)


(* p ~ (p - s) + s.  Group-cancellation identity. (Private to .fst — users
   should derive this directly from the commutative_ring axioms.)         *)

(* ------------------------------------------------------------------ *)
(*  Leading coefficient                                               *)
(* ------------------------------------------------------------------ *)

(* If deg p >= 0, then coeff p (deg p) is nonzero.                    *)
val leading_coeff_nonzero (#t:Type) {| cr: commutative_ring t |}
                          (p: polynomial t)
  : Lemma (requires deg p >= 0)
          (ensures  not ((coeff p (deg p)) = zero))

(* ------------------------------------------------------------------ *)
(*  Coefficient identities (public surface)                           *)
(* ------------------------------------------------------------------ *)

val poly_sub_coeff (#t:Type) {| cr: commutative_ring t |}
                   (p q: polynomial t) (i: nat)
  : Lemma (coeff (p -- q) i = ((coeff p i) + (- (coeff q i))))

(* ------------------------------------------------------------------ *)
(*  Degree bounds for poly_neg, poly_add, poly_sub                     *)
(* ------------------------------------------------------------------ *)

val poly_neg_degree (#t:Type) {| cr: commutative_ring t |}
                    (p: polynomial t)
  : Lemma (ensures deg (- p) == deg p)

val poly_add_degree_bound (#t:Type) {| cr: commutative_ring t |}
                          (p q: polynomial t) (k: nat)
  : Lemma (requires deg p < k /\ deg q < k)
          (ensures  deg (p + q) < k)

val poly_sub_degree_bound (#t:Type) {| cr: commutative_ring t |}
                          (p q: polynomial t) (k: nat)
  : Lemma (requires deg p < k /\ deg q < k)
          (ensures  deg (p -- q) < k)

(* ------------------------------------------------------------------ *)
(*  Euclidean division                                                 *)
(* ------------------------------------------------------------------ *)

(* Euclidean division primitive.  Its `Pure` postcondition carries BOTH the
   correctness equation and the degree-decrease, so callers get them by
   destructuring the result — no separate `poly_divmod_correct` /
   `poly_divmod_correct_degree` lemmas to invoke. *)
val poly_divmod (#t:Type) {| f: field t |} (p q: polynomial t)
  : Pure (polynomial t & polynomial t)
         (requires True)
         (ensures fun (quot, rem) -> p = ((q * quot) + rem) /\
                                     (deg q >= 0 ==> deg rem < deg q))

(* Quotient / remainder projections; each restates the spec via the same
   `poly_divmod p q`, so using only one half still adjoins correctness +
   degree-decrease (subsumes the former `poly_div_reveal` / `poly_rem_reveal`). *)
val poly_div (#t:Type) {| f: field t |} (p q: polynomial t)
  : Pure (polynomial t)
         (requires True)
         (ensures fun quot -> quot == fst (poly_divmod p q) /\
                              p = ((q * quot) + (snd (poly_divmod p q))) /\
                              (deg q >= 0 ==> deg (snd (poly_divmod p q)) < deg q))

val poly_rem (#t:Type) {| f: field t |} (p q: polynomial t)
  : Pure (polynomial t)
         (requires True)
         (ensures fun rem -> rem == snd (poly_divmod p q) /\
                             p = ((q * (fst (poly_divmod p q))) + rem) /\
                             (deg q >= 0 ==> deg rem < deg q))
