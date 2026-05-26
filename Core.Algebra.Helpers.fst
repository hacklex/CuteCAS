module Core.Algebra.Helpers

(*
   Derived helpers around the Core.Algebra tower.

   These are convenience aliases / lemma reformulations that downstream
   modules use frequently. All are derivable from the bundled laws in
   Core.Algebra; we re-export them with single-fact statements for SMT
   convenience.
*)

open Core.Algebra
open Core.Algebra.Notation
module TC = FStar.Tactics.Typeclasses

(* ---------------------------------------------------------------- *)
(* equatable                                                        *)
(* ---------------------------------------------------------------- *)

let elim_equatable_laws (t:Type) {| equatable t |} (_: unit)
  : Lemma ((forall (x:t). x = x) /\ (forall (x y:t). x = y <==> y = x))
  = Classical.forall_intro (reflexivity #t);
    Classical.forall_intro_2 (symmetry #t)

let leibniz_to_eq (#t:Type) {| equatable t |} (a b: t)
  : Lemma (requires a == b) (ensures a = b)
  = reflexivity a

let leibniz_then_eq (#t:Type) {| equatable t |} (a b c: t)
  : Lemma (requires a == b /\ b = c) (ensures a = c)
  = reflexivity a; transitivity a b c

let eq_then_leibniz (#t:Type) {| equatable t |} (a b c: t)
  : Lemma (requires a = b /\ b == c) (ensures a = c)
  = reflexivity c; transitivity a b c

let trans_for_calc (t:Type) {| equatable t |} (_: unit)
  : Lemma (forall (x y z: t). x = y /\ y = z ==> x = z)
  = let aux (x y z: t) : Lemma (x = y /\ y = z ==> x = z)
      = Classical.move_requires_3 (transitivity #t) x y z
    in Classical.forall_intro_3 aux

let trans2 (#t:Type) {| equatable t |} (a b c: t)
  : Lemma (requires a = b /\ b = c) (ensures a = c)
  = transitivity a b c

let trans3 (#t:Type) {| equatable t |} (a b c d: t)
  : Lemma (requires a = b /\ b = c /\ c = d) (ensures a = d)
  = transitivity a b c; transitivity a c d

let trans4 (#t:Type) {| equatable t |} (a b c d e: t)
  : Lemma (requires a = b /\ b = c /\ c = d /\ d = e) (ensures a = e)
  = transitivity a b c; transitivity a c d; transitivity a d e

let trans5 (#t:Type) {| equatable t |} (a b c d e g: t)
  : Lemma (requires a = b /\ b = c /\ c = d /\ d = e /\ e = g) (ensures a = g)
  = transitivity a b c; transitivity a c d; transitivity a d e; transitivity a e g

(* ---------------------------------------------------------------- *)
(* add_comm_group: single-fact projections                          *)
(* ---------------------------------------------------------------- *)

let zero_plus_x (#t:Type) {| add_comm_group t |} (x:t)
  : Lemma (zero + x = x) = add_zero x

let x_plus_zero (#t:Type) {| add_comm_group t |} (x:t)
  : Lemma (x + zero = x) = add_zero x

let neg_x_plus_x (#t:Type) {| add_comm_group t |} (x:t)
  : Lemma (neg x + x = zero) = add_negation x

let x_plus_neg_x (#t:Type) {| add_comm_group t |} (x:t)
  : Lemma (x + neg x = zero) = add_negation x

(* ---------------------------------------------------------------- *)
(* ring: single-fact projections                                    *)
(* ---------------------------------------------------------------- *)

let one_mul_x (#t:Type) {| ring t |} (x:t)
  : Lemma (one * x = x) = mul_one x

let x_mul_one (#t:Type) {| ring t |} (x:t)
  : Lemma (x * one = x) = mul_one x

(* Bridge for commutative_ring: the marker-class field with a dependent
   parameter is awkward to invoke directly; this helper exposes
   commutativity as an ordinary lemma. *)
let mul_commutativity_cr (#t:Type) {| cr: commutative_ring t |} (x y: t)
  : Lemma (x * y = y * x)
  = cr.cr_mic.mul_commutativity x y

(* ---------------------------------------------------------------- *)
(* basic AC patterns                                                *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 30"
let group_cancel_left (#t:Type) {| add_comm_group t |} (a b c: t)
  : Lemma (requires a + b = a + c) (ensures b = c)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    neg_x_plus_x a;
    add_associativity (neg a) a b;
    add_associativity (neg a) a c;
    zero_plus_x b;
    zero_plus_x c;
    reflexivity (neg a);
    add_congruence (neg a) (a + b) (neg a) (a + c);
    add_congruence (neg a + a) b zero b;
    add_congruence (neg a + a) c zero c
#pop-options

(* neg_zero: zero = neg zero.
   Proof: neg zero = neg zero + zero    (x_plus_zero on neg zero)
                   = zero               (neg_x_plus_x with x=zero)  *)
let neg_zero (#t:Type) {| add_comm_group t |} (_: unit)
  : Lemma ((zero #t) = neg zero)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    x_plus_zero (neg (zero #t));         (* neg 0 + 0 = neg 0 *)
    neg_x_plus_x (zero #t);              (* neg 0 + 0 = 0 *)
    symmetry (neg (zero #t)) (neg zero + zero);
    transitivity (neg (zero #t)) (neg zero + zero) zero;
    symmetry (neg (zero #t)) zero

(* neg_neg: neg (neg x) = x.
   Proof: (neg (neg x) + neg x) + x = neg (neg x) + (neg x + x)
                                    = neg (neg x) + zero
                                    = neg (neg x).
          (neg (neg x) + neg x) + x = zero + x = x.
          So neg (neg x) = x. *)
let neg_neg (#t:Type) {| add_comm_group t |} (x: t)
  : Lemma (neg (neg x) = x)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let nx = neg x in
    let nnx = neg nx in
    add_associativity nnx nx x;          (* (nnx + nx) + x = nnx + (nx + x) *)
    neg_x_plus_x x;                      (* nx + x = 0 *)
    reflexivity nnx;
    add_congruence nnx (nx + x) nnx (zero #t);
    x_plus_zero nnx;                     (* nnx + 0 = nnx *)
    transitivity (nnx + (nx + x)) (nnx + zero) nnx;
    symmetry ((nnx + nx) + x) (nnx + (nx + x));
    transitivity ((nnx + nx) + x) (nnx + (nx + x)) nnx;
    neg_x_plus_x nx;                     (* nnx + nx = 0 *)
    reflexivity x;
    add_congruence (nnx + nx) x (zero #t) x;
    zero_plus_x x;                       (* 0 + x = x *)
    transitivity ((nnx + nx) + x) (zero + x) x;
    symmetry ((nnx + nx) + x) nnx;
    transitivity nnx ((nnx + nx) + x) x

(* If x = zero then neg x = zero. *)
let neg_of_zero (#t:Type) {| add_comm_group t |} (x: t)
  : Lemma (requires x = zero) (ensures neg x = zero)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    neg_congruence x (zero #t);          (* neg x = neg zero *)
    neg_zero #t ();                      (* zero = neg zero *)
    symmetry (zero #t) (neg zero);       (* neg zero = zero *)
    transitivity (neg x) (neg zero) zero

(* If neg x = zero then x = zero. *)
let zero_of_neg (#t:Type) {| add_comm_group t |} (x: t)
  : Lemma (requires neg x = zero) (ensures x = zero)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    neg_of_zero (neg x);                 (* neg (neg x) = zero *)
    neg_neg x;                           (* neg (neg x) = x *)
    symmetry (neg (neg x)) x;            (* x = neg (neg x) *)
    transitivity x (neg (neg x)) zero

(* neg_of_sum: neg (x+y) = neg y + neg x.
   Proof skeleton:
     neg y + neg x
     = (neg y + neg x) + 0
     = (neg y + neg x) + ((x+y) + neg(x+y))
     = ((neg y + neg x) + (x+y)) + neg(x+y)
     = (neg y + (neg x + (x+y))) + neg(x+y)
     = (neg y + ((neg x + x) + y)) + neg(x+y)
     = (neg y + (0 + y)) + neg(x+y)
     = (neg y + y) + neg(x+y)
     = 0 + neg(x+y)
     = neg(x+y). *)
#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let neg_of_sum (#t:Type) {| g: add_comm_group t |} (x y: t)
  : Lemma (neg (x + y) = neg y + neg x)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let s : t = x + y in
    let ny : t = neg y in
    let nx : t = neg x in
    let ns : t = neg s in
    (* Strategy: build the RHS expression step-by-step into ns using
       reflexivity-witnessed AC rewrites. Each step is one lemma. *)
    (* e0: ny + nx  *)
    (* e1: (ny + nx) + 0 *)
    x_plus_zero (ny + nx);
    assert ((ny + nx) + zero = ny + nx);
    symmetry ((ny + nx) + zero) (ny + nx);
    (* 0 = s + ns *)
    x_plus_neg_x s;
    symmetry (s + ns) zero;
    (* (ny + nx) + 0 = (ny + nx) + (s + ns) *)
    reflexivity (ny + nx);
    add_congruence (ny + nx) (zero #t) (ny + nx) (s + ns);
    assert ((ny + nx) + zero = (ny + nx) + (s + ns));
    (* e2: ((ny + nx) + s) + ns  by assoc symm *)
    add_associativity (ny + nx) s ns;
    symmetry ((ny + nx) + s + ns) ((ny + nx) + (s + ns));
    assert ((ny + nx) + (s + ns) = ((ny + nx) + s) + ns);
    (* e3: (ny + (nx + s)) + ns by assoc on first part, then cong with refl ns *)
    add_associativity ny nx s;
    reflexivity ns;
    add_congruence ((ny + nx) + s) ns (ny + (nx + s)) ns;
    assert (((ny + nx) + s) + ns = (ny + (nx + s)) + ns);
    (* e4: (ny + ((nx + x) + y)) + ns:  inside, nx + s = nx + (x+y) = (nx + x) + y *)
    add_associativity nx x y;
    symmetry (nx + x + y) (nx + (x + y));
    reflexivity ny;
    add_congruence ny (nx + s) ny (nx + x + y);
    add_congruence (ny + (nx + s)) ns (ny + (nx + x + y)) ns;
    assert ((ny + (nx + s)) + ns = (ny + (nx + x + y)) + ns);
    (* e5: (ny + (0 + y)) + ns  via neg_x_plus_x x *)
    neg_x_plus_x x;                          (* nx + x = 0 *)
    reflexivity y;
    add_congruence (nx + x) y (zero #t) y;
    reflexivity ny;
    add_congruence ny (nx + x + y) ny (zero + y);
    reflexivity ns;
    add_congruence (ny + (nx + x + y)) ns (ny + (zero + y)) ns;
    assert ((ny + (nx + x + y)) + ns = (ny + (zero + y)) + ns);
    (* e6: (ny + y) + ns  via zero_plus_x y *)
    zero_plus_x y;
    add_congruence ny (zero + y) ny y;
    add_congruence (ny + (zero + y)) ns (ny + y) ns;
    assert ((ny + (zero + y)) + ns = (ny + y) + ns);
    (* e7: 0 + ns  via neg_x_plus_x y *)
    neg_x_plus_x y;
    add_congruence (ny + y) ns (zero #t) ns;
    assert ((ny + y) + ns = zero + ns);
    (* e8: ns  via zero_plus_x ns *)
    zero_plus_x ns;
    assert (zero + ns = ns);
    (* chain everything together by repeated trans *)
    transitivity (ny + nx) ((ny + nx) + zero) ((ny + nx) + (s + ns));
    transitivity (ny + nx) ((ny + nx) + (s + ns)) (((ny + nx) + s) + ns);
    transitivity (ny + nx) (((ny + nx) + s) + ns) ((ny + (nx + s)) + ns);
    transitivity (ny + nx) ((ny + (nx + s)) + ns) ((ny + (nx + x + y)) + ns);
    transitivity (ny + nx) ((ny + (nx + x + y)) + ns) ((ny + (zero + y)) + ns);
    transitivity (ny + nx) ((ny + (zero + y)) + ns) ((ny + y) + ns);
    transitivity (ny + nx) ((ny + y) + ns) (zero + ns);
    transitivity (ny + nx) (zero + ns) ns;
    symmetry (ny + nx) ns
#pop-options

(* ---------------------------------------------------------------- *)
(* ring: zero is absorbing                                          *)
(* ---------------------------------------------------------------- *)

let zero_mul_x (#t:Type) {| ring t |} (x:t)
  : Lemma (zero * x = zero)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    add_zero (zero #t);                              (* 0 + 0 = 0 *)
    reflexivity x;
    right_distributivity x zero zero;                (* (0+0)*x = 0*x + 0*x *)
    mul_congruence (zero + zero) x zero x;           (* (0+0)*x = 0*x *)
    (* so 0*x = 0*x + 0*x; cancel: 0 = 0*x *)
    x_plus_zero (zero * x);                          (* 0*x + 0 = 0*x *)
    group_cancel_left (zero * x) zero (zero * x);
    symmetry (zero * x) zero

let x_mul_zero (#t:Type) {| ring t |} (x:t)
  : Lemma (x * zero = zero)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    add_zero (zero #t);
    reflexivity x;
    left_distributivity x zero zero;
    mul_congruence x (zero + zero) x zero;
    x_plus_zero (x * zero);
    group_cancel_left (x * zero) zero (x * zero);
    symmetry (x * zero) zero

(* neg_mul_l: (-x)*y = -(x*y).
   Proof: 0 = 0*y = (x + (-x))*y = x*y + (-x)*y, so (-x)*y = -(x*y). *)
#push-options "--z3rlimit 40"
let neg_mul_l (#t:Type) {| ring t |} (x y: t)
  : Lemma (neg x * y = neg (x * y))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    add_negation x;                                  (* x + neg x = 0 *)
    reflexivity y;
    right_distributivity y x (neg x);                (* (x + neg x) * y = x*y + neg x*y *)
    mul_congruence (x + neg x) y (zero #t) y;        (* (x + neg x)*y = 0*y *)
    zero_mul_x y;                                    (* 0*y = 0 *)
    (* so x*y + (neg x)*y = 0; conclude (neg x)*y = neg (x*y) *)
    (* Use add_negation on x*y: x*y + neg (x*y) = 0 *)
    x_plus_neg_x (x * y);                            (* x*y + neg (x*y) = 0 *)
    (* Combine via group_cancel_left on x*y: 
       x*y + (neg x*y) = 0 = x*y + neg (x*y) ⇒ neg x*y = neg (x*y) *)
    transitivity ((x + neg x) * y) ((zero <: t) * y) (zero <: t);
    transitivity ((x + neg x) * y) (x * y + neg x * y) (zero <: t);
    symmetry ((x + neg x) * y) (x * y + neg x * y);
    (* So x*y + (neg x)*y = 0. *)
    symmetry ((x + neg x) * y) (zero <: t);
    transitivity (x*y + neg x * y) ((x + neg x) * y) (zero <: t);
    (* Likewise x*y + neg (x*y) = 0. So x*y + neg x*y = x*y + neg (x*y). *)
    symmetry (x*y + neg (x*y)) (zero <: t);
    transitivity (x*y + neg x * y) (zero <: t) (x*y + neg (x*y));
    group_cancel_left (x * y) (neg x * y) (neg (x * y))
#pop-options

(* neg_mul_r: x*(-y) = -(x*y).
   Proof: x*y + x*(-y) = x*(y + (-y)) = x*0 = 0, so x*(-y) = -(x*y). *)
#push-options "--z3rlimit 40"
let neg_mul_r (#t:Type) {| ring t |} (x y: t)
  : Lemma (x * neg y = neg (x * y))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    add_negation y;                                  (* y + neg y = 0 *)
    reflexivity x;
    left_distributivity x y (neg y);                 (* x * (y + neg y) = x*y + x*neg y *)
    mul_congruence x (y + neg y) x (zero <: t);
    x_mul_zero x;                                    (* x*0 = 0 *)
    x_plus_neg_x (x * y);                            (* x*y + neg (x*y) = 0 *)
    transitivity (x * (y + neg y)) (x * (zero <: t)) (zero <: t);
    symmetry (x * (y + neg y)) (x*y + x*neg y);
    transitivity (x*y + x*neg y) (x * (y + neg y)) (zero <: t);
    symmetry (x*y + neg (x*y)) (zero <: t);
    transitivity (x*y + x*neg y) (zero <: t) (x*y + neg (x*y));
    group_cancel_left (x * y) (x * neg y) (neg (x * y))
#pop-options
