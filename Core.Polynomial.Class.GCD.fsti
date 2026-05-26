module Core.Polynomial.Class.GCD

(*
   Polynomial GCD via the Euclidean algorithm, ported to the
   `Core.Polynomial.Class` tower.

   Currently exposed (all proven, zero admits/assumes):
     - degree_measure                  (termination measure)
     - poly_gcd                        (Euclidean GCD)
     - poly_gcd_base / poly_gcd_step   (reveal lemmas)
     - gcd_divides_left                (poly_gcd p q divides p)
     - gcd_divides_right               (poly_gcd p q divides q)
     - gcd_is_maximal                  (d | p ∧ d | q ⟹ d | poly_gcd p q)

   Deferred to follow-up sessions (require porting poly_divmod_unique
   and its ~5 supporting lemmas — `poly_mul_sub_distrib`, `degree_sub_bound`,
   `only_mul_zero_decreases_poly_degree`, `degree_none_poly_eq_zero`,
   `sub_zero_implies_eq` — totaling ~300 LOC of additional infrastructure):
     - gcd_congruence
     - polynomial_gcd_domain_instance
     - polynomial_ufd_instance
     - polynomial_euclidean_domain (chain) instance
     - poly_ext_gcd + ext_gcd_correct + ext_gcd_is_gcd (Bézout)
     - coprime + euclid_lemma
*)

module TC = FStar.Tactics.Typeclasses
module L  = FStar.List.Tot

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial.Class
open Core.Polynomial.Class.Div

(* ------------------------------------------------------------------ *)
(*  Termination measure                                               *)
(*    degree_measure p = 0           when poly_deg p = None
                       = n + 1       when poly_deg p = Some n          *)
(* ------------------------------------------------------------------ *)

val degree_measure (#t:Type) {| cr: commutative_ring t |}
                   (p: polynomial t)
  : nat

val degree_measure_zero_iff_zero
    (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (degree_measure p == 0 <==> None? (poly_deg p))

(* ------------------------------------------------------------------ *)
(*  Euclidean GCD                                                     *)
(* ------------------------------------------------------------------ *)

val poly_gcd (#t:Type) {| f: field t |} (p q: polynomial t)
  : polynomial t

(* Reveal: when q has no degree (i.e. q = poly_zero), the GCD is p. *)
val poly_gcd_base (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires None? (poly_deg q))
          (ensures  poly_gcd #t #f p q == p)

(* Reveal: otherwise, the recursion descends as (q, p mod q). *)
val poly_gcd_step (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires Some? (poly_deg q))
          (ensures  (let (_, r) = poly_divmod #t #f p q in
                     poly_gcd #t #f p q == poly_gcd #t #f q r))

(* ------------------------------------------------------------------ *)
(*  GCD divisibility axioms                                           *)
(*                                                                    *)
(*  `divides` is interpreted in `commutative_ring (polynomial t)`,    *)
(*  resolved automatically through `polynomial_commutative_ring_instance`.*)
(* ------------------------------------------------------------------ *)

val gcd_divides_left (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (divides (poly_gcd #t #f p q) p)

val gcd_divides_right (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (divides (poly_gcd #t #f p q) q)

val gcd_is_maximal (#t:Type) {| f: field t |} (p q d: polynomial t)
  : Lemma (requires divides d p /\ divides d q)
          (ensures  divides d (poly_gcd #t #f p q))

(* ------------------------------------------------------------------ *)
(*  Extended GCD (Bézout)                                             *)
(*                                                                    *)
(*  poly_ext_gcd p q returns (a, b, g) with a*p + b*q ~ g ~ gcd p q.  *)
(* ------------------------------------------------------------------ *)

val poly_ext_gcd (#t:Type) {| f: field t |} (p q: polynomial t)
  : Tot (polynomial t & polynomial t & polynomial t)
        (decreases (degree_measure q))

val ext_gcd_correct (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (ensures (let (a, b, g) = poly_ext_gcd #t #f p q in
                    poly_eq (add (mul a p) (mul b q)) g))
          (decreases (degree_measure q))

val ext_gcd_is_gcd (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (ensures (let (_, _, g) = poly_ext_gcd #t #f p q in
                    poly_eq g (poly_gcd #t #f p q)))
          (decreases (degree_measure q))

(* ------------------------------------------------------------------ *)
(*  GCD congruence: poly_gcd respects poly_eq on both arguments       *)
(* ------------------------------------------------------------------ *)

val gcd_congruence (#t:Type) {| f: field t |}
                   (x1 x2 y1 y2: polynomial t)
  : Lemma (requires poly_eq x1 x2 /\ poly_eq y1 y2)
          (ensures  poly_eq (poly_gcd #t #f x1 y1)
                            (poly_gcd #t #f x2 y2))
          (decreases (degree_measure y1))

(* ------------------------------------------------------------------ *)
(*  Chain instances: gcd_domain → ufd → euclidean_domain              *)
(*                                                                    *)
(*  Resolves only over a field-coefficient polynomial ring.           *)
(* ------------------------------------------------------------------ *)

val polynomial_gcd_domain_instance
    (#t:Type) {| f: field t |}
  : gcd_domain (polynomial t)

val polynomial_ufd_instance
    (#t:Type) {| f: field t |}
  : ufd (polynomial t)

val polynomial_euclidean_domain_chain_instance
    (#t:Type) {| f: field t |}
  : euclidean_domain (polynomial t)

(* ------------------------------------------------------------------ *)
(*  Coprimality and Euclid's lemma                                    *)
(* ------------------------------------------------------------------ *)

(* `coprime p q` iff gcd(p, q) is a nonzero constant (degree 0). *)
val coprime (#t:Type) {| f: field t |} (p q: polynomial t) : bool

(* Euclid's lemma: if p and q are coprime and p divides a*q, then p
   divides a. *)
val euclid_lemma (#t:Type) {| f: field t |} (p q a: polynomial t)
  : Lemma (requires Some? (poly_deg p) /\
                    coprime p q /\
                    divides p (poly_mul a q))
          (ensures  divides p a)
