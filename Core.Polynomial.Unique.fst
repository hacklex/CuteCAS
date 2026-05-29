module Core.Polynomial.Unique

module TC = FStar.Tactics.Typeclasses
module L  = FStar.List.Tot

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div
open Core.Tactics.CanonRing

(* ================================================================ *)
(*  Trivial degree lemmas                                           *)
(* ================================================================ *)

let degree_well_defined #t #cr p q
  = poly_eq_length p q

let degree_none_poly_eq_zero #t #cr p
  = assert (L.length p = 0);
    assert (p == ([] <: polynomial t));
    poly_eq_reflexivity #t #cr p

(* ================================================================ *)
(*  Carrier-level helpers (single commutative_ring in scope)        *)
(*                                                                  *)
(*  These are instantiated at #(polynomial t) #cr_p from the        *)
(*  polynomial-level wrappers below, to side-step the canon_ring    *)
(*  carrier-resolution failure that occurs when both `field t` and  *)
(*  `commutative_ring (polynomial t)` are simultaneously in scope.  *)
(* ================================================================ *)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let sub_zero_implies_eq_h
    (#t:Type) {| cr: commutative_ring t |} (a b: t)
  : Lemma (requires eq (add a (neg b)) zero)
          (ensures  eq a b)
  = reflexivity b;
    add_congruence b (add a (neg b)) b zero;
    add_zero b;
    transitivity (add b (add a (neg b))) (add b zero) b;
    assert (eq a (add b (add a (neg b)))) by canon_ring ();
    transitivity a (add b (add a (neg b))) b
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let mul_sub_distrib_h
    (#t:Type) {| cr: commutative_ring t |} (q a b: t)
  : Lemma (eq (mul q (add a (neg b)))
              (add (mul q a) (neg (mul q b))))
  = assert (eq (mul q (add a (neg b)))
               (add (mul q a) (neg (mul q b))))
      by canon_ring ()
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let add_rearrange_h
    (#t:Type) {| cr: commutative_ring t |} (x y r1 r2: t)
  : Lemma (requires eq (add x r1) (add y r2))
          (ensures  eq (add x (neg y)) (add r2 (neg r1)))
  = reflexivity (add (neg y) (neg r1));
    add_congruence (add x r1) (add (neg y) (neg r1))
                   (add y r2) (add (neg y) (neg r1));
    assert (eq (add (add x r1) (add (neg y) (neg r1)))
               (add x (neg y))) by canon_ring ();
    assert (eq (add (add y r2) (add (neg y) (neg r1)))
               (add r2 (neg r1))) by canon_ring ();
    symmetry (add (add x r1) (add (neg y) (neg r1)))
             (add x (neg y));
    transitivity (add x (neg y))
                 (add (add x r1) (add (neg y) (neg r1)))
                 (add (add y r2) (add (neg y) (neg r1)));
    transitivity (add x (neg y))
                 (add (add y r2) (add (neg y) (neg r1)))
                 (add r2 (neg r1))
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let extract_r_helper
    (#t:Type) {| cr: commutative_ring t |} (qa1 qa2 r1 r2: t)
  : Lemma (requires eq (add qa1 r1) (add qa2 r2) /\ eq qa1 qa2)
          (ensures  eq r1 r2)
  = reflexivity r2;
    add_congruence qa1 r2 qa2 r2;
    symmetry (add qa1 r2) (add qa2 r2);
    transitivity (add qa1 r1) (add qa2 r2) (add qa1 r2);
    reflexivity (neg qa1);
    add_congruence (add qa1 r1) (neg qa1) (add qa1 r2) (neg qa1);
    assert (eq r1 (add (add qa1 r1) (neg qa1))) by canon_ring ();
    assert (eq (add (add qa1 r2) (neg qa1)) r2) by canon_ring ();
    transitivity r1 (add (add qa1 r1) (neg qa1))
                    (add (add qa1 r2) (neg qa1));
    transitivity r1 (add (add qa1 r2) (neg qa1)) r2
#pop-options

(* ================================================================ *)
(*  Polynomial wrappers                                             *)
(* ================================================================ *)

(* `poly_eq` IS `eq` at the polynomial commutative_ring instance, and
   `poly_sub a b == add a (neg b)` (poly_sub_reveal). Each wrapper
   instantiates the carrier-level helper at #(polynomial t) #cr_p and
   bridges via the reveal lemmas. *)

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let sub_zero_implies_eq #t #cr (a b: polynomial t)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    poly_sub_reveal a b;
    sub_zero_implies_eq_h #(polynomial t) #cr_p a b
#pop-options

(* ================================================================ *)
(*  degree_mul: direct dispatch to Class.poly_deg_mul               *)
(* ================================================================ *)

let degree_mul #t #id (p q: polynomial t)
  = poly_deg_mul #t #id p q

(* ================================================================ *)
(*  only_mul_zero_decreases_poly_degree                             *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let only_mul_zero_decreases_poly_degree #t #f (q d s: polynomial t)
  = match poly_deg d with
    | None   -> ()
    | Some _ ->
        degree_mul #t #(id_of_f t) q d;
        degree_well_defined #t (poly_mul q d) s
#pop-options

(* ================================================================ *)
(*  poly_mul_sub_distrib, add_rearrange                             *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let poly_mul_sub_distrib #t #cr (q a b: polynomial t)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    poly_sub_reveal a b;
    poly_sub_reveal (poly_mul q a) (poly_mul q b);
    mul_sub_distrib_h #(polynomial t) #cr_p q a b
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let add_rearrange #t #cr (x y r1 r2: polynomial t)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    poly_sub_reveal x y;
    poly_sub_reveal r2 r1;
    add_rearrange_h #(polynomial t) #cr_p x y r1 r2
#pop-options

(* ================================================================ *)
(*  poly_divmod_unique                                              *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let poly_divmod_unique #t #f (q a1 a2 r1 r2: polynomial t)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    let qa1 = poly_mul q a1 in
    let qa2 = poly_mul q a2 in
    (* Part A: prove poly_eq a1 a2 *)
    add_rearrange qa1 qa2 r1 r2;
    (* : poly_eq (poly_sub qa1 qa2) (poly_sub r2 r1) *)
    poly_mul_sub_distrib q a1 a2;
    (* : poly_eq (poly_mul q (poly_sub a1 a2)) (poly_sub qa1 qa2) *)
    let sa = poly_sub a1 a2 in
    let sr = poly_sub r2 r1 in
    poly_eq_transitivity (poly_mul q sa) (poly_sub qa1 qa2) sr;
    (* : poly_eq (poly_mul q sa) sr *)
    poly_sub_degree_bound r2 r1 (Some?.v (poly_deg q));
    (* : None? (poly_deg sr) \/ Some?.v (poly_deg sr) < Some?.v (poly_deg q) *)
    only_mul_zero_decreases_poly_degree #t #f q sa sr;
    (* : None? (poly_deg sa) *)
    degree_none_poly_eq_zero sa;
    (* : poly_eq sa poly_zero *)
    sub_zero_implies_eq a1 a2;
    (* : poly_eq a1 a2 *)
    (* Part B: prove poly_eq r1 r2.
       From poly_eq qa1+r1 ~ qa2+r2 and poly_eq a1~a2:
       (qa1 ~ qa2 via mul_congruence; then cancellation on r1, r2.) *)
    poly_eq_reflexivity q;
    poly_mul_congruence q a1 q a2;
    (* : poly_eq qa1 qa2 *)
    (* Use carrier-level helper to extract r1 ~ r2 from
       qa1+r1 ~ qa2+r2 ∧ qa1 ~ qa2.
       Identity: at carrier polynomial t,
         eq (add qa1 r1) (add qa2 r2) ∧ eq qa1 qa2 ⟹ eq r1 r2.
       Goes through (add r1 (neg r1)) = zero + cancellation. *)
    extract_r_helper #(polynomial t) #cr_p qa1 qa2 r1 r2
#pop-options
