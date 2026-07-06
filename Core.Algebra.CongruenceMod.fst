module Core.Algebra.CongruenceMod

(* ================================================================ *)
(*  Congruence modulo m in a commutative ring                        *)
(*      cong m x y  :=  m | (x - y)                                  *)
(*                                                                   *)
(*  This is the general divisibility-level notion; it was formerly   *)
(*  defined inside the Berlekamp consumer.  Named with *Mod* so it   *)
(*  is not confused with the ring `mul_congruence`/`add_congruence`  *)
(*  lemmas (those are equality-congruence of the operations; this is *)
(*  congruence *modulo* an element).                                 *)
(* ================================================================ *)

module H = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Divisibility
open Core.Tactics.CanonRing
open Core.Algebra.Notation

let cong (#a:Type) {| cr: commutative_ring a |} (m x y: a) : prop =
  m `divides` (x + (- y))

let cong_reveal (#a:Type) {| cr: commutative_ring a |} (m x y: a)
  : Lemma (cong m x y <==> m `divides` (x + (- y)))
  = ()

let cong_refl (#a:Type) {| cr: commutative_ring a |} (m x: a)
  : Lemma (cong m x x)
  = H.elim_equatable_laws a ();
    H.x_plus_neg_x x;
    divides_zero m;
    divides_congruence_right m zero (x + (- x))

let cong_sym (#a:Type) {| cr: commutative_ring a |} (m x y: a)
  : Lemma (requires cong m x y) (ensures cong m y x)
  = H.elim_equatable_laws a ();
    divides_neg m (x + (- y));
    assert (eq (- (x + (- y))) (y + (- x))) by (Core.Tactics.CanonRing.canon_ring ());
    divides_congruence_right m (- (x + (- y))) (y + (- x))

let cong_trans (#a:Type) {| cr: commutative_ring a |} (m x y z: a)
  : Lemma (requires cong m x y /\ cong m y z) (ensures cong m x z)
  = H.elim_equatable_laws a ();
    divides_add m (x + (- y)) (y + (- z));
    assert (eq ((x + (- y)) + (y + (- z))) (x + (- z))) by (Core.Tactics.CanonRing.canon_ring ());
    divides_congruence_right m ((x + (- y)) + (y + (- z))) (x + (- z))

(* multiplicative compatibility *)
let cong_mul (#a:Type) {| cr: commutative_ring a |} (m x1 x2 y1 y2: a)
  : Lemma (requires cong m x1 x2 /\ cong m y1 y2)
          (ensures  cong m (x1 * y1) (x2 * y2))
  = H.elim_equatable_laws a ();
    divides_mul_right m (x1 + (- x2)) y1;
    divides_mul_left  m x2 (y1 + (- y2));
    divides_add m ((x1 + (- x2)) * y1) (x2 * (y1 + (- y2)));
    assert (eq (((x1 + (- x2)) * y1) + (x2 * (y1 + (- y2)))) ((x1 * y1) + (- (x2 * y2))))
      by (Core.Tactics.CanonRing.canon_ring ());
    divides_congruence_right m (((x1 + (- x2)) * y1) + (x2 * (y1 + (- y2))))
                               ((x1 * y1) + (- (x2 * y2)))

(* additive compatibility *)
let cong_add (#a:Type) {| cr: commutative_ring a |} (m x1 y1 x2 y2: a)
  : Lemma (requires cong m x1 y1 /\ cong m x2 y2)
          (ensures  cong m (x1 + x2) (y1 + y2))
  = H.elim_equatable_laws a ();
    divides_add m (x1 + (- y1)) (x2 + (- y2));
    assert (eq ((x1 + (- y1)) + (x2 + (- y2))) ((x1 + x2) + (- (y1 + y2))))
      by (Core.Tactics.CanonRing.canon_ring ());
    divides_congruence_right m ((x1 + (- y1)) + (x2 + (- y2)))
                               ((x1 + x2) + (- (y1 + y2)))

(* exact ring equality implies congruence *)
let cong_of_eq (#a:Type) {| cr: commutative_ring a |} (m x y: a)
  : Lemma (requires x = y) (ensures cong m x y)
  = H.elim_equatable_laws a ();
    reflexivity (- y);
    add_congruence x (- y) y (- y);          (* x + (- y) ~ y + (- y) *)
    H.x_plus_neg_x y;                         (* y + (- y) ~ zero *)
    transitivity (x + (- y)) (y + (- y)) zero;
    divides_zero m;
    symmetry (x + (- y)) zero;
    divides_congruence_right m zero (x + (- y))

(* congruence respects ring equality on the right operand *)
let cong_eq_right (#a:Type) {| cr: commutative_ring a |} (m x y y': a)
  : Lemma (requires cong m x y /\ eq y y') (ensures cong m x y')
  = H.elim_equatable_laws a ();
    neg_congruence y y';                          (* neg y = neg y' *)
    add_congruence x (- y) x (- y');          (* x + neg y = x + neg y' *)
    divides_congruence_right m (x + (- y)) (x + (- y'))

(* helper:  p = m*q + r  ==>  m | (p - r)  ==>  cong m p r *)
let cong_of_divmod (#a:Type) {| cr: commutative_ring a |} (p m q r: a)
  : Lemma (requires p `eq` ((m * q) + r))
          (ensures  cong m p r)
  = H.elim_equatable_laws a ();
    H.trans_for_calc a ();
    let mq = m * q in
    add_congruence p (- r) (mq + r) (- r);
    add_associativity mq r (- r);
    H.x_plus_neg_x r;
    add_congruence mq (r + (- r)) mq zero;
    H.x_plus_zero mq;
    H.trans3 (p + (- r)) ((mq + r) + (- r)) (mq + (r + (- r))) mq;
    divides_intro m (p + (- r)) q
