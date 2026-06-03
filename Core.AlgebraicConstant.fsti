module Core.AlgebraicConstant

(*
   Algebraic constants: the quotient ring  polynomial t / (r),
   where r is a fixed polynomial over a field t.

   Phase 1.75 scope: COMMUTATIVE RING ONLY.  No field structure,
   no irreducibility hypothesis, no inverse, no factorization.

   Design: quotient-by-equality.  Carrier is a wrapper around
   `polynomial t` (record with one field), and equality is

       AC a == AC b   iff   r divides (a - b)   in polynomial t.

   All ring operations are inherited verbatim from `polynomial t`;
   their congruence under our equality follows from (r) being an
   ideal of the polynomial ring.
*)

module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div

(* ---------------------------------------------------------------- *)
(*  Carrier                                                          *)
(* ---------------------------------------------------------------- *)

noeq type algebraic (t:Type) {| f: field t |}
                    (r: polynomial t {Some? (poly_deg r)}) = {
  ac_rep : polynomial t;
}

(* ---------------------------------------------------------------- *)
(*  Operations                                                       *)
(* ---------------------------------------------------------------- *)

val ac_eq (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
          (a b: algebraic t r) : bool

val ac_zero (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
  : algebraic t r

val ac_one (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
  : algebraic t r

val ac_add (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
           (a b: algebraic t r) : algebraic t r

val ac_neg (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
           (a: algebraic t r) : algebraic t r

val ac_mul (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
           (a b: algebraic t r) : algebraic t r

(* Nullity in the quotient: [a] = 0  iff  r divides a.rep.  The bridge consumed
   by the field construction (inverse via Bezout). *)
val ac_eq_zero_iff_divides (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
    (a: algebraic t r)
  : Lemma (let cr_p : commutative_ring (polynomial t) = TC.solve in
           b2t (ac_eq a (ac_zero #t #f #r)) <==>
             divides #(polynomial t) #cr_p r a.ac_rep)

(* General: [a] = [b]  iff  r divides (a.rep - b.rep).  (Explicit; no SMT pattern.) *)
val ac_eq_divides (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
    (a b: algebraic t r)
  : Lemma (let cr_p : commutative_ring (polynomial t) = TC.solve in
           b2t (ac_eq a b) <==>
             divides #(polynomial t) #cr_p r (poly_sub a.ac_rep b.ac_rep))

(* Representation reveals (the ring operations are abstract through this interface). *)
val ac_mul_rep (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
    (a b: algebraic t r)
  : Lemma ((ac_mul a b).ac_rep == poly_mul a.ac_rep b.ac_rep)

val ac_add_rep (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
    (a b: algebraic t r)
  : Lemma ((ac_add a b).ac_rep == poly_add a.ac_rep b.ac_rep)

val ac_one_rep (#t:Type) {| f: field t |} (r: polynomial t {Some? (poly_deg r)})
  : Lemma ((ac_one #t #f #r).ac_rep == poly_one #t)

(* ---------------------------------------------------------------- *)
(*  Equivalence + ring laws                                          *)
(* ---------------------------------------------------------------- *)

val ac_eq_reflexivity (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
                      (a: algebraic t r)
  : Lemma (ac_eq a a)

val ac_eq_symmetry (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
                   (a b: algebraic t r)
  : Lemma (requires ac_eq a b) (ensures ac_eq b a)

val ac_eq_transitivity (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
                       (a b c: algebraic t r)
  : Lemma (requires ac_eq a b /\ ac_eq b c)
          (ensures  ac_eq a c)

val ac_add_congruence (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
                      (a1 b1 a2 b2: algebraic t r)
  : Lemma (requires ac_eq a1 a2 /\ ac_eq b1 b2)
          (ensures  ac_eq (ac_add a1 b1) (ac_add a2 b2))

val ac_add_associativity (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
                         (a b c: algebraic t r)
  : Lemma (ac_eq (ac_add (ac_add a b) c) (ac_add a (ac_add b c)))

val ac_add_commutativity (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
                         (a b: algebraic t r)
  : Lemma (ac_eq (ac_add a b) (ac_add b a))

val ac_add_zero (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
                (a: algebraic t r)
  : Lemma (ac_eq (ac_add a ac_zero) a /\ ac_eq (ac_add ac_zero a) a)

val ac_neg_congruence (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
                      (a1 a2: algebraic t r)
  : Lemma (requires ac_eq a1 a2)
          (ensures  ac_eq (ac_neg a1) (ac_neg a2))

val ac_add_negation (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
                    (a: algebraic t r)
  : Lemma (ac_eq (ac_add a (ac_neg a)) ac_zero /\
           ac_eq (ac_add (ac_neg a) a) ac_zero)

val ac_mul_congruence (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
                      (a1 b1 a2 b2: algebraic t r)
  : Lemma (requires ac_eq a1 a2 /\ ac_eq b1 b2)
          (ensures  ac_eq (ac_mul a1 b1) (ac_mul a2 b2))

val ac_mul_associativity (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
                         (a b c: algebraic t r)
  : Lemma (ac_eq (ac_mul (ac_mul a b) c) (ac_mul a (ac_mul b c)))

val ac_mul_one (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
               (a: algebraic t r)
  : Lemma (ac_eq (ac_mul a ac_one) a /\ ac_eq (ac_mul ac_one a) a)

val ac_mul_commutativity (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
                         (a b: algebraic t r)
  : Lemma (ac_eq (ac_mul a b) (ac_mul b a))

val ac_left_distributivity (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
                           (a b c: algebraic t r)
  : Lemma (ac_eq (ac_mul a (ac_add b c))
                 (ac_add (ac_mul a b) (ac_mul a c)))

val ac_right_distributivity (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
                            (a b c: algebraic t r)
  : Lemma (ac_eq (ac_mul (ac_add a b) c)
                 (ac_add (ac_mul a c) (ac_mul b c)))

(* ---------------------------------------------------------------- *)
(*  Typeclass instance                                               *)
(* ---------------------------------------------------------------- *)

val algebraic_equatable
    (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
  : equatable (algebraic t r)

val algebraic_commutative_ring
    (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
  : commutative_ring (algebraic t r)

(* Reveal: the commutative-ring instance's operations are the ac_* operations. *)
val algebraic_ring_reveal (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
  : Lemma (
      (let cr = algebraic_commutative_ring #t #f #r in
       cr.cr_r.mul              == ac_mul  #t #f #r /\
       cr.cr_r.one              == ac_one  #t #f #r /\
       cr.cr_r.r_add.add        == ac_add  #t #f #r /\
       cr.cr_r.r_add.neg        == ac_neg  #t #f #r /\
       cr.cr_r.r_add.zero       == ac_zero #t #f #r /\
       cr.cr_r.r_add.acg_eq.eq  == ac_eq   #t #f #r))

let ac_elim_equatable_laws #t {| f: field t |} (r: polynomial t {Some? (poly_deg r)})
  : Lemma ((forall (x:algebraic t r). x `ac_eq` x) /\ (forall (x y:algebraic t r). ac_eq x y <==> ac_eq y x)
          /\ (forall (x y z: algebraic t r). ac_eq x y /\ ac_eq y z ==> ac_eq x z)) =   
  Classical.forall_intro (ac_eq_reflexivity #t #f #r);
  Classical.forall_intro_2 (Classical.move_requires_2 (ac_eq_symmetry #t #f #r));
  Classical.forall_intro_3 (Classical.move_requires_3 (ac_eq_transitivity #t #f #r))


