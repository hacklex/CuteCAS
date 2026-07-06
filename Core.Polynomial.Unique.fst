module Core.Polynomial.Unique

module TC = FStar.Tactics.Typeclasses
module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

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

let nonzero_iff_some_deg #t #cr p
  = poly_zero_is_unique p

let degree_none_poly_eq_zero #t #cr p
  = assert (L.length p = 0);
    assert (p == ([] <: polynomial t));
    poly_eq_reflexivity p

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
  : Lemma (requires (a + ((- b))) = zero)
          (ensures  a = b)
  = H.elim_equatable_laws t ();
    add_congruence b ((a + ((- b)))) b zero;
    add_zero b;
    transitivity ((b + ((a + ((- b)))))) ((b + zero)) b;
    assert (a = ((b + ((a + ((- b))))))) by canon_ring ();
    transitivity a ((b + ((a + ((- b)))))) b
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let mul_sub_distrib_h
    (#t:Type) {| cr: commutative_ring t |} (q a b: t)
  : Lemma ((q * ((a + ((- b)))))
              = ((((q * a)) + ((- ((q * b)))))))
  = assert ((q * ((a + ((- b)))))
               = ((((q * a)) + ((- ((q * b)))))))
      by canon_ring ()
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let add_rearrange_h
    (#t:Type) {| cr: commutative_ring t |} (x y r1 r2: t)
  : Lemma (requires (x + r1) = (y + r2))
          (ensures  (x + ((- y))) = (r2 + ((- r1))))
  = H.elim_equatable_laws t ();
    add_congruence ((x + r1)) ((((- y)) + ((- r1))))
                   ((y + r2)) ((((- y)) + ((- r1))));
    assert ((((x + r1)) + ((((- y)) + ((- r1)))))
               = ((x + ((- y))))) by canon_ring ();
    assert ((((y + r2)) + ((((- y)) + ((- r1)))))
               = ((r2 + ((- r1))))) by canon_ring ();
    transitivity ((x + ((- y))))
                 ((((x + r1)) + ((((- y)) + ((- r1))))))
                 ((((y + r2)) + ((((- y)) + ((- r1))))));
    transitivity ((x + ((- y))))
                 ((((y + r2)) + ((((- y)) + ((- r1))))))
                 ((r2 + ((- r1))))
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let extract_r_helper
    (#t:Type) {| cr: commutative_ring t |} (qa1 qa2 r1 r2: t)
  : Lemma (requires (qa1 + r1) = (qa2 + r2) /\ qa1 = qa2)
          (ensures  r1 = r2)
  = H.elim_equatable_laws t ();
    add_congruence qa1 r2 qa2 r2;
    transitivity ((qa1 + r1)) ((qa2 + r2)) ((qa1 + r2));
    add_congruence ((qa1 + r1)) ((- qa1)) ((qa1 + r2)) ((- qa1));
    assert (r1 = ((((qa1 + r1)) + ((- qa1))))) by canon_ring ();
    assert (((((qa1 + r2)) + ((- qa1)))) = r2) by canon_ring ();
    transitivity r1 ((((qa1 + r1)) + ((- qa1))))
                    ((((qa1 + r2)) + ((- qa1))));
    transitivity r1 ((((qa1 + r2)) + ((- qa1)))) r2
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
  =
    sub_zero_implies_eq_h a b
#pop-options

(* ================================================================ *)
(*  degree_mul: direct dispatch to Core.Polynomial.deg_mul          *)
(* ================================================================ *)

let degree_mul #t #id (p q: polynomial t)
  = deg_mul #t #id p q

(* ================================================================ *)
(*  only_mul_zero_decreases_poly_degree                             *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let only_mul_zero_decreases_poly_degree #t #f (q d s: polynomial t)
  = if deg d >= 0 then begin
      degree_mul q d;
      degree_well_defined (q * d) s
    end
#pop-options

(* ================================================================ *)
(*  poly_mul_sub_distrib, add_rearrange                             *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let poly_mul_sub_distrib #t #cr (q a b: polynomial t)
  =
    mul_sub_distrib_h q a b
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let add_rearrange #t #cr (x y r1 r2: polynomial t)
  =
    add_rearrange_h x y r1 r2
#pop-options

(* ================================================================ *)
(*  poly_divmod_unique                                              *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
let poly_divmod_unique #t #f (q a1 a2 r1 r2: polynomial t)
  = 
    let qa1 = (q * a1) in
    let qa2 = (q * a2) in
    (* Part A: prove poly_eq a1 a2 *)
    add_rearrange qa1 qa2 r1 r2;
    (* : poly_eq (poly_sub qa1 qa2) (poly_sub r2 r1) *)
    poly_mul_sub_distrib q a1 a2;
    (* : poly_eq (poly_mul q (poly_sub a1 a2)) (poly_sub qa1 qa2) *)
    let sa = a1 -- a2 in
    let sr = r2 -- r1 in
    poly_eq_transitivity (q * sa) (qa1 -- qa2) sr;
    (* : poly_eq (poly_mul q sa) sr *)
    poly_sub_degree_bound r2 r1 (deg q);
    (* : deg sr < deg q *)
    only_mul_zero_decreases_poly_degree q sa sr;
    (* : deg sa < 0 *)
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
    extract_r_helper qa1 qa2 r1 r2
#pop-options
