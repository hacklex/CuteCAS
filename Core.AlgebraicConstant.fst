module Core.AlgebraicConstant

(*
   Implementation of the quotient ring  polynomial t / (r).

   See the .fsti for the public surface.

   Strategy: `ac_eq a b := r | (a - b)` in `polynomial t`.  All ring
   operations are inherited verbatim from `polynomial t`; their
   congruence under `ac_eq` follows because (r) is an ideal.

   The polynomial `commutative_ring (polynomial t)` is reached via
   the `polynomial_commutative_ring_instance` `unfold instance`.
*)

module TC = FStar.Tactics.Typeclasses

module ID = FStar.IndefiniteDescription

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Unique

(* ---------------------------------------------------------------- *)
(*  Internal: a local CR helper for canon_ring identities over a    *)
(*  single-CR context (avoids the field/poly CR diamond).            *)
(* ---------------------------------------------------------------- *)

private let cr_neg_sub_swap
    (#u:Type) {| cr: commutative_ring u |} (x y: u)
  : Lemma (eq (neg (add x (neg y))) (add y (neg x)))
  = assert (eq (neg (add x (neg y))) (add y (neg x)))
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_sub_telescope
    (#u:Type) {| cr: commutative_ring u |} (a b c: u)
  : Lemma (eq (add (add a (neg b)) (add b (neg c)))
              (add a (neg c)))
  = assert (eq (add (add a (neg b)) (add b (neg c)))
               (add a (neg c)))
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_sub_distributes_add
    (#u:Type) {| cr: commutative_ring u |}
    (a1 b1 a2 b2: u)
  : Lemma (eq (add (add a1 b1) (neg (add a2 b2)))
              (add (add a1 (neg a2)) (add b1 (neg b2))))
  = assert (eq (add (add a1 b1) (neg (add a2 b2)))
               (add (add a1 (neg a2)) (add b1 (neg b2))))
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_neg_sub
    (#u:Type) {| cr: commutative_ring u |} (a1 a2: u)
  : Lemma (eq (add (neg a1) (neg (neg a2)))
              (neg (add a1 (neg a2))))
  = assert (eq (add (neg a1) (neg (neg a2)))
               (neg (add a1 (neg a2))))
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_mul_sub_split
    (#u:Type) {| cr: commutative_ring u |}
    (a1 b1 a2 b2: u)
  : Lemma (eq (add (mul a1 b1) (neg (mul a2 b2)))
              (add (mul a1 (add b1 (neg b2)))
                   (mul (add a1 (neg a2)) b2)))
  = assert (eq (add (mul a1 b1) (neg (mul a2 b2)))
               (add (mul a1 (add b1 (neg b2)))
                    (mul (add a1 (neg a2)) b2)))
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_sub_self
    (#u:Type) {| cr: commutative_ring u |} (a: u)
  : Lemma (eq (add a (neg a)) (zero <: u))
  = assert (eq (add a (neg a)) (zero <: u))
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_sub_zero_right
    (#u:Type) {| cr: commutative_ring u |} (a: u)
  : Lemma (eq (add a (neg (zero <: u))) a)
  = assert (eq (add a (neg (zero <: u))) a)
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_sub_zero_left
    (#u:Type) {| cr: commutative_ring u |} (a: u)
  : Lemma (eq (add (zero <: u) (neg a)) (neg a))
  = assert (eq (add (zero <: u) (neg a)) (neg a))
      by Core.Tactics.CanonRing.canon_ring ()

(* ---------------------------------------------------------------- *)
(*  Bridge: poly_eq x y  ⟹  poly_sub x y ~ poly_zero                *)
(* ---------------------------------------------------------------- *)

private let poly_eq_implies_sub_zero
    (#t:Type) {| cr: commutative_ring t |}
    (a b: polynomial t)
  : Lemma (requires poly_eq a b)
          (ensures  poly_eq (poly_sub a b) (poly_zero #t))
  = 
    poly_sub_reveal a b;
    (* poly_sub a b = poly_add a (poly_neg b) *)
    reflexivity #(polynomial t)  (poly_neg b);
    poly_add_congruence a (poly_neg b) b (poly_neg b);
    (* Now poly_add a (poly_neg b) ~ poly_add b (poly_neg b) *)
    cr_sub_self  b;
    (* poly_add b (poly_neg b) ~ poly_zero *)
    transitivity (poly_add a (poly_neg b))
                 (poly_add b (poly_neg b))
                 (poly_zero #t);
    (* And poly_sub a b == poly_add a (poly_neg b) (definitional via reveal) *)
    ()

(* ---------------------------------------------------------------- *)
(*  Operations + equality                                            *)
(* ---------------------------------------------------------------- *)

(* Decidable algebraic-constant equality: take the remainder of (a-b)
   on division by r and check it's zero.  Tot-pure. *)
let ac_eq #t #f (#r: polynomial t {Some? (poly_deg r)})
          (a b: algebraic t r) : bool
  = let (_, rem) = poly_divmod #t #f (poly_sub a.ac_rep b.ac_rep) r in
    poly_eq rem (poly_zero #t)

(* Bridge: ac_eq a b ⟺ r | (a.rep - b.rep)  in polynomial t.
   Equipped with an SMT pattern so users of `ac_eq` automatically get
   the divides interpretation when needed.  This bridge is the only
   way we use SMT patterns in this file — the lemma is a pure
   definitional equivalence. *)
private let ac_eq_iff_divides
    #t {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
    (a b: algebraic t r)
  : Lemma (
           b2t (ac_eq a b) <==>
             divides  r (poly_sub a.ac_rep b.ac_rep))
    [SMTPat (ac_eq a b)]
  = 
    let d = poly_sub a.ac_rep b.ac_rep in
    let (q, rem) = poly_divmod #t #f d r in
    poly_divmod_correct #t #f d r;
    (* Forward: ac_eq ⟹ divides. rem ~ 0 + p_correct: d ~ r*q + rem ~ r*q + 0 ~ r*q. *)
    let fwd () : Lemma (requires b2t (ac_eq a b))
                       (ensures divides  r d)
      = (* rem ~ poly_zero, so d ~ r*q + 0 ~ r*q *)
        
        poly_add_zero (poly_mul r q);
        (* poly_add (poly_mul r q) poly_zero ~ poly_mul r q *)
        poly_add_congruence (poly_mul r q) rem (poly_mul r q) (poly_zero #t);
        reflexivity #(polynomial t)  (poly_mul r q);
        transitivity d (poly_add (poly_mul r q) rem) (poly_add (poly_mul r q) (poly_zero #t));
        transitivity d (poly_add (poly_mul r q) (poly_zero #t)) (poly_mul r q);
        divides_intro  r d q
    in
    (* Backward: divides ⟹ rem ~ 0 via poly_divmod_unique. *)
    let bwd () : Lemma (requires divides  r d)
                       (ensures b2t (ac_eq a b))
      = 
        eliminate exists (k: polynomial t). poly_eq d (poly_mul r k)
        returns b2t (ac_eq a b)
        with hyp.
        begin
          (* Have: d ~ r*k.   Also d ~ r*q + rem.
             Convert to canonical shape: r*k + 0 ~ r*q + rem.
             Then poly_divmod_unique gives rem ~ 0.                    *)
          poly_add_zero (poly_mul r k);
          (* poly_add (poly_mul r k) poly_zero ~ poly_mul r k *)
          symmetry #(polynomial t) 
            (poly_add (poly_mul r k) (poly_zero #t)) (poly_mul r k);
          transitivity d (poly_mul r k) (poly_add (poly_mul r k) (poly_zero #t));
          (* d ~ poly_add (poly_mul r k) poly_zero
             d ~ poly_add (poly_mul r q) rem
             ⟹  poly_add (poly_mul r k) poly_zero ~ poly_add (poly_mul r q) rem *)
          symmetry d (poly_add (poly_mul r k) (poly_zero #t));
          transitivity (poly_add (poly_mul r k) (poly_zero #t))
                       d
                       (poly_add (poly_mul r q) rem);
          poly_deg_zero_is_none #t;
          poly_divmod_correct_degree #t #f d r;
          poly_divmod_unique #t #f r k q (poly_zero #t) rem
        end
    in
    Classical.move_requires fwd ();
    Classical.move_requires bwd ()

let ac_zero #t #f (#r: polynomial t {Some? (poly_deg r)}) : algebraic t r = { ac_rep = poly_zero #t }
let ac_one  #t #f (#r: polynomial t {Some? (poly_deg r)}) : algebraic t r = { ac_rep = poly_one  #t }

let ac_add #t #f (#r: polynomial t {Some? (poly_deg r)}) (a b: algebraic t r) : algebraic t r =
  { ac_rep = poly_add a.ac_rep b.ac_rep }

let ac_neg #t #f (#r: polynomial t {Some? (poly_deg r)}) (a: algebraic t r) : algebraic t r =
  { ac_rep = poly_neg a.ac_rep }

let ac_mul #t #f (#r: polynomial t {Some? (poly_deg r)}) (a b: algebraic t r) : algebraic t r =
  { ac_rep = poly_mul a.ac_rep b.ac_rep }

(* Clean characterization of nullity: [a] = 0 in the quotient iff r divides a.rep.
   This is the bridge the field construction (inverse via Bezout) consumes; it is
   proved here, where the divides<->ac_eq SMT pattern and the poly_eq/eq idiom are
   available, so external callers never need to fight `poly_sub a 0 ~ a`. *)
let ac_eq_zero_iff_divides #t #f (#r: polynomial t {Some? (poly_deg r)}) (a: algebraic t r)
  : Lemma (
           b2t (ac_eq a (ac_zero #t #f #r)) <==>
             divides  r a.ac_rep)
  = 
    let x = a.ac_rep in
    let s = poly_sub x (poly_zero #t) in
    (* SMTPat: ac_eq a 0 <==> divides r (poly_sub x 0) = divides r s. *)
    ac_eq_iff_divides a (ac_zero #t #f #r);
    (* s = poly_sub x 0 ~ x. *)
    poly_sub_reveal x (poly_zero #t);                            (* s == poly_add x (poly_neg 0) *)
    poly_neg_zero #t #(TC.solve <: commutative_ring t);         (* poly_neg 0 == 0 *)
    poly_add_zero x;                                            (* poly_add x 0 ~ x *)
    reflexivity #(polynomial t)  x;
    poly_add_congruence x (poly_neg (poly_zero #t)) x (poly_zero #t);
    transitivity s (poly_add x (poly_zero #t)) x;               (* eq s x *)
    symmetry #(polynomial t)  s x;     (* eq x s *)
    (* divides r s <==> divides r x. *)
    let fwd () : Lemma (requires divides  r s)
                       (ensures  divides  r x)
      = divides_congruence_right  r s x in
    let bwd () : Lemma (requires divides  r x)
                       (ensures  divides  r s)
      = divides_congruence_right  r x s in
    Classical.move_requires fwd ();
    Classical.move_requires bwd ()

(* General characterization (explicit, no SMT pattern): [a] = [b] iff r | (a.rep - b.rep).
   Re-exposes the internal definitional equivalence for external callers (e.g. the
   field inversion identity, which needs ac_eq _ ac_one). *)
let ac_eq_divides #t #f (#r: polynomial t {Some? (poly_deg r)}) (a b: algebraic t r)
  : Lemma (
           b2t (ac_eq a b) <==>
             divides  r (poly_sub a.ac_rep b.ac_rep))
  = ac_eq_iff_divides a b

(* Representation reveals (ops are abstract through the interface). *)
let ac_mul_rep #t #f (#r: polynomial t {Some? (poly_deg r)}) (a b: algebraic t r)
  : Lemma ((ac_mul a b).ac_rep == poly_mul a.ac_rep b.ac_rep) = ()

let ac_add_rep #t #f (#r: polynomial t {Some? (poly_deg r)}) (a b: algebraic t r)
  : Lemma ((ac_add a b).ac_rep == poly_add a.ac_rep b.ac_rep) = ()

let ac_one_rep #t #f (r: polynomial t {Some? (poly_deg r)})
  : Lemma ((ac_one #t #f #r).ac_rep == poly_one #t) = ()

(* ---------------------------------------------------------------- *)
(*  Equivalence laws                                                 *)
(* ---------------------------------------------------------------- *)

let ac_eq_reflexivity #t #f (#r: polynomial t {Some? (poly_deg r)}) (a: algebraic t r)
  : Lemma (ac_eq a a)
  = 
    let x = a.ac_rep in
    (* poly_sub x x ~ poly_zero, r | poly_zero, then divides_congruence_right. *)
    cr_sub_self  x;
    poly_sub_reveal x x;
    (* poly_sub x x = poly_add x (poly_neg x); both directions of eq. *)
    divides_zero  r;
    symmetry #(polynomial t) 
             (poly_add x (poly_neg x)) (poly_zero #t);
    divides_congruence_right  r
                             (poly_zero #t) (poly_add x (poly_neg x))

let ac_eq_symmetry #t #f (#r: polynomial t {Some? (poly_deg r)}) (a b: algebraic t r)
  : Lemma (requires ac_eq a b) (ensures ac_eq b a)
  = 
    let x = a.ac_rep in
    let y = b.ac_rep in
    poly_sub_reveal x y;
    poly_sub_reveal y x;
    (* divides r (x - y).  Negate to get divides r -(x - y).
       -(x - y) ~ y - x.                                              *)
    divides_neg  r (poly_sub x y);
    cr_neg_sub_swap  x y;
    (* neg (poly_sub x y) ~ poly_sub y x *)
    divides_congruence_right  r
      (poly_neg (poly_sub x y)) (poly_sub y x)

let ac_eq_transitivity #t #f (#r: polynomial t {Some? (poly_deg r)}) (a b c: algebraic t r)
  : Lemma (requires ac_eq a b /\ ac_eq b c)
          (ensures  ac_eq a c)
  = 
    let x = a.ac_rep in
    let y = b.ac_rep in
    let z = c.ac_rep in
    poly_sub_reveal x y;
    poly_sub_reveal y z;
    poly_sub_reveal x z;
    divides_add  r (poly_sub x y) (poly_sub y z);
    cr_sub_telescope  x y z;
    divides_congruence_right  r
      (poly_add (poly_sub x y) (poly_sub y z))
      (poly_sub x z)

(* ---------------------------------------------------------------- *)
(*  Bridge: poly_eq → ac_eq                                          *)
(* ---------------------------------------------------------------- *)

private let poly_eq_implies_ac_eq
    #t {| f: field t |} (#r: polynomial t {Some? (poly_deg r)}) (a b: algebraic t r)
  : Lemma (requires poly_eq a.ac_rep b.ac_rep)
          (ensures  ac_eq a b)
  = 
    poly_eq_implies_sub_zero a.ac_rep b.ac_rep;
    divides_zero  r;
    symmetry #(polynomial t) 
             (poly_sub a.ac_rep b.ac_rep) (poly_zero #t);
    divides_congruence_right  r
      (poly_zero #t) (poly_sub a.ac_rep b.ac_rep)

(* ---------------------------------------------------------------- *)
(*  Add congruence + laws                                            *)
(* ---------------------------------------------------------------- *)

let ac_add_congruence #t #f (#r: polynomial t {Some? (poly_deg r)}) (a1 b1 a2 b2: algebraic t r)
  : Lemma (requires ac_eq a1 a2 /\ ac_eq b1 b2)
          (ensures  ac_eq (ac_add a1 b1) (ac_add a2 b2))
  = 
    let x1 = a1.ac_rep in
    let y1 = b1.ac_rep in
    let x2 = a2.ac_rep in
    let y2 = b2.ac_rep in
    poly_sub_reveal x1 x2;
    poly_sub_reveal y1 y2;
    poly_sub_reveal (poly_add x1 y1) (poly_add x2 y2);
    divides_add  r (poly_sub x1 x2) (poly_sub y1 y2);
    cr_sub_distributes_add  x1 y1 x2 y2;
    symmetry #(polynomial t) 
      (poly_sub (poly_add x1 y1) (poly_add x2 y2))
      (poly_add (poly_sub x1 x2) (poly_sub y1 y2));
    divides_congruence_right  r
      (poly_add (poly_sub x1 x2) (poly_sub y1 y2))
      (poly_sub (poly_add x1 y1) (poly_add x2 y2))

let ac_add_associativity #t #f (#r: polynomial t {Some? (poly_deg r)}) (a b c: algebraic t r)
  : Lemma (ac_eq (ac_add (ac_add a b) c) (ac_add a (ac_add b c)))
  = poly_add_associativity a.ac_rep b.ac_rep c.ac_rep;
    poly_eq_implies_ac_eq (ac_add (ac_add a b) c) (ac_add a (ac_add b c))

let ac_add_commutativity #t #f (#r: polynomial t {Some? (poly_deg r)}) (a b: algebraic t r)
  : Lemma (ac_eq (ac_add a b) (ac_add b a))
  = poly_add_commutativity a.ac_rep b.ac_rep;
    poly_eq_implies_ac_eq (ac_add a b) (ac_add b a)

let ac_add_zero #t #f (#r: polynomial t {Some? (poly_deg r)}) (a: algebraic t r)
  : Lemma (ac_eq (ac_add a ac_zero) a /\ ac_eq (ac_add ac_zero a) a)
  = poly_add_zero a.ac_rep;
    poly_eq_implies_ac_eq (ac_add a ac_zero) a;
    poly_eq_implies_ac_eq (ac_add ac_zero a) a

(* ---------------------------------------------------------------- *)
(*  Neg congruence + add_negation                                    *)
(* ---------------------------------------------------------------- *)

let ac_neg_congruence #t #f (#r: polynomial t {Some? (poly_deg r)}) (a1 a2: algebraic t r)
  : Lemma (requires ac_eq a1 a2)
          (ensures  ac_eq (ac_neg a1) (ac_neg a2))
  = 
    let x1 = a1.ac_rep in
    let x2 = a2.ac_rep in
    poly_sub_reveal x1 x2;
    poly_sub_reveal (poly_neg x1) (poly_neg x2);
    divides_neg  r (poly_sub x1 x2);
    (* neg (x1 - x2) ~ -x1 + -(-x2) = -x1 - (-x2) *)
    cr_neg_sub  x1 x2;
    symmetry #(polynomial t) 
      (poly_add (poly_neg x1) (poly_neg (poly_neg x2)))
      (poly_neg (poly_sub x1 x2));
    divides_congruence_right  r
      (poly_neg (poly_sub x1 x2))
      (poly_add (poly_neg x1) (poly_neg (poly_neg x2)))

let ac_add_negation #t #f (#r: polynomial t {Some? (poly_deg r)}) (a: algebraic t r)
  : Lemma (ac_eq (ac_add a (ac_neg a)) ac_zero /\
           ac_eq (ac_add (ac_neg a) a) ac_zero)
  = poly_add_negation a.ac_rep;
    poly_eq_implies_ac_eq (ac_add a (ac_neg a)) ac_zero;
    poly_eq_implies_ac_eq (ac_add (ac_neg a) a) ac_zero

(* ---------------------------------------------------------------- *)
(*  Mul congruence + laws                                            *)
(* ---------------------------------------------------------------- *)

let ac_mul_congruence #t #f (#r: polynomial t {Some? (poly_deg r)}) (a1 b1 a2 b2: algebraic t r)
  : Lemma (requires ac_eq a1 a2 /\ ac_eq b1 b2)
          (ensures  ac_eq (ac_mul a1 b1) (ac_mul a2 b2))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    let x1 = a1.ac_rep in
    let y1 = b1.ac_rep in
    let x2 = a2.ac_rep in
    let y2 = b2.ac_rep in
    poly_sub_reveal x1 x2;
    poly_sub_reveal y1 y2;
    poly_sub_reveal (poly_mul x1 y1) (poly_mul x2 y2);
    (* r | (y1 - y2) ⟹ r | x1*(y1-y2)
       r | (x1 - x2) ⟹ r | (x1-x2)*y2
       Sum: r | x1*(y1-y2) + (x1-x2)*y2  ~  x1*y1 - x2*y2. *)
    divides_mul_left  #(polynomial t) #cr_p r x1 (poly_sub y1 y2);
    divides_mul_right #(polynomial t) #cr_p r (poly_sub x1 x2) y2;
    divides_add #(polynomial t) #cr_p r
      (poly_mul x1 (poly_sub y1 y2))
      (poly_mul (poly_sub x1 x2) y2);
    cr_mul_sub_split #(polynomial t) #cr_p x1 y1 x2 y2;
    symmetry #(polynomial t) #(cr_p.cr_r.r_add.acg_eq)
      (poly_sub (poly_mul x1 y1) (poly_mul x2 y2))
      (poly_add (poly_mul x1 (poly_sub y1 y2))
                (poly_mul (poly_sub x1 x2) y2));
    divides_congruence_right #(polynomial t) #cr_p r
      (poly_add (poly_mul x1 (poly_sub y1 y2))
                (poly_mul (poly_sub x1 x2) y2))
      (poly_sub (poly_mul x1 y1) (poly_mul x2 y2))

let ac_mul_associativity #t #f (#r: polynomial t {Some? (poly_deg r)}) (a b c: algebraic t r)
  : Lemma (ac_eq (ac_mul (ac_mul a b) c) (ac_mul a (ac_mul b c)))
  = poly_mul_associativity a.ac_rep b.ac_rep c.ac_rep;
    poly_eq_implies_ac_eq (ac_mul (ac_mul a b) c) (ac_mul a (ac_mul b c))

let ac_mul_one #t #f (#r: polynomial t {Some? (poly_deg r)}) (a: algebraic t r)
  : Lemma (ac_eq (ac_mul a ac_one) a /\ ac_eq (ac_mul ac_one a) a)
  = poly_mul_one a.ac_rep;
    poly_eq_implies_ac_eq (ac_mul a ac_one) a;
    poly_eq_implies_ac_eq (ac_mul ac_one a) a

let ac_mul_commutativity #t #f (#r: polynomial t {Some? (poly_deg r)}) (a b: algebraic t r)
  : Lemma (ac_eq (ac_mul a b) (ac_mul b a))
  = poly_mul_commutativity a.ac_rep b.ac_rep;
    poly_eq_implies_ac_eq (ac_mul a b) (ac_mul b a)

let ac_left_distributivity #t #f (#r: polynomial t {Some? (poly_deg r)}) (a b c: algebraic t r)
  : Lemma (ac_eq (ac_mul a (ac_add b c))
                 (ac_add (ac_mul a b) (ac_mul a c)))
  = poly_left_distributivity a.ac_rep b.ac_rep c.ac_rep;
    poly_eq_implies_ac_eq
      (ac_mul a (ac_add b c))
      (ac_add (ac_mul a b) (ac_mul a c))

let ac_right_distributivity #t #f (#r: polynomial t {Some? (poly_deg r)}) (a b c: algebraic t r)
  : Lemma (ac_eq (ac_mul (ac_add a b) c)
                 (ac_add (ac_mul a c) (ac_mul b c)))
  = poly_right_distributivity c.ac_rep a.ac_rep b.ac_rep;
    poly_eq_implies_ac_eq
      (ac_mul (ac_add a b) c)
      (ac_add (ac_mul a c) (ac_mul b c))

(* ---------------------------------------------------------------- *)
(*  Typeclass instances                                              *)
(* ---------------------------------------------------------------- *)

instance algebraic_equatable
    (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
  : equatable (algebraic t r)
  = {
    eq            = ac_eq #t #f #r;
    reflexivity   = ac_eq_reflexivity #t #f #r;
    symmetry      = (fun x y ->
                      Classical.move_requires
                        (ac_eq_symmetry #t #f #r x) y;
                      Classical.move_requires
                        (ac_eq_symmetry #t #f #r y) x);
    transitivity  = ac_eq_transitivity #t #f #r;
  }

instance algebraic_commutative_ring
    (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
  : commutative_ring (algebraic t r)
  = {
    cr_r = {
      r_add = {
        acg_eq           = algebraic_equatable #t #f #r;
        zero             = ac_zero #t #f #r;
        add              = ac_add #t #f #r;
        add_congruence   = ac_add_congruence #t #f #r;
        add_commutativity= ac_add_commutativity #t #f #r;
        add_associativity= ac_add_associativity #t #f #r;
        add_zero         = ac_add_zero #t #f #r;
        neg              = ac_neg #t #f #r;
        neg_congruence   = ac_neg_congruence #t #f #r;
        add_negation     = ac_add_negation #t #f #r;
      };
      one                  = ac_one #t #f #r;
      mul                  = ac_mul #t #f #r;
      mul_congruence       = ac_mul_congruence #t #f #r;
      mul_associativity    = ac_mul_associativity #t #f #r;
      mul_one              = ac_mul_one #t #f #r;
      left_distributivity  = ac_left_distributivity #t #f #r;
      right_distributivity = (fun x y z -> ac_right_distributivity #t #f #r y z x);
    };
    cr_mic = {
      mul_commutativity = ac_mul_commutativity #t #f #r;
    };
  }

(* Reveal that the commutative-ring instance's operations are exactly the
   ac_* operations.  Needed by clients (e.g. the field construction) because
   the instance is not `unfold`, so its projections do not reduce in SMT. *)
let algebraic_ring_reveal (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
  : Lemma (
      (let cr = algebraic_commutative_ring #t #f #r in
       cr.cr_r.mul              == ac_mul  #t #f #r /\
       cr.cr_r.one              == ac_one  #t #f #r /\
       cr.cr_r.r_add.add        == ac_add  #t #f #r /\
       cr.cr_r.r_add.neg        == ac_neg  #t #f #r /\
       cr.cr_r.r_add.zero       == ac_zero #t #f #r /\
       cr.cr_r.r_add.acg_eq.eq  == ac_eq   #t #f #r))
  = ()
