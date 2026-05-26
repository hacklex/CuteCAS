module Core.Algebra.Divisibility

(*
   Divisibility refinement chain (§1.4 of AGENTS.md):

       integral_domain  ←  gcd_domain  ←  ufd  ←  euclidean_domain

   Linear chain off `integral_domain`. Each class stores its
   immediate parent as a `@@@TC.no_method` field and declares
   exactly one `instance` for its edge. Skip-level instances are
   forbidden.

   `field` is NOT on the chain — a `field_to_ed` plain function will
   live in a downstream module once its full axioms are discharged.

   This module currently exposes the class skeletons + the three
   linear-chain projection instances. Substantive `gcd` lemma bodies
   for concrete carriers (field, polynomial-over-field) ship in
   downstream modules.
*)

module TC = FStar.Tactics.Typeclasses

open Core.Algebra
module H = Core.Algebra.Helpers
open Core.Tactics.CanonRing

(* ------------------------------------------------------------------ *)
(*  Divisibility predicate                                            *)
(*                                                                    *)
(*  `divides x y` iff there exists `c` with `y = x * c`.              *)
(* ------------------------------------------------------------------ *)

let divides (#t:Type) {| cr: commutative_ring t |} (x y: t) : prop =
  exists (c: t). eq y (mul x c)

let divides_intro (#t:Type) {| cr: commutative_ring t |}
                  (x y c: t)
  : Lemma (requires eq y (mul x c))
          (ensures  divides x y)
  = ()

(* Helper used inside class signatures so the projection chain
   `integral_domain → commutative_ring` is reusable without inlining. *)
unfold let cr_of_id_arg (#t:Type) (i: integral_domain t) : commutative_ring t =
  cr_of_id t #i

(* Underlying add_comm_group reached through `integral_domain`. *)
unfold let acg_of_id_arg (#t:Type) (i: integral_domain t) : add_comm_group t =
  acg_of_r t #(r_of_cr t #(cr_of_id t #i))

(* ------------------------------------------------------------------ *)
(*  gcd_domain                                                        *)
(* ------------------------------------------------------------------ *)

class gcd_domain (t:Type) = {
  [@@@TC.no_method] gcd_id: integral_domain t;
  gcd: t -> t -> t;
  gcd_congruence:
    (x1:t) -> (x2:t) -> (y1:t) -> (y2:t) ->
    Lemma (requires eq x1 x2 /\ eq y1 y2)
          (ensures  eq (gcd x1 y1) (gcd x2 y2));
  gcd_divides_left:
    (x:t) -> (y:t) ->
    Lemma (divides #t #(cr_of_id_arg gcd_id) (gcd x y) x);
  gcd_divides_right:
    (x:t) -> (y:t) ->
    Lemma (divides #t #(cr_of_id_arg gcd_id) (gcd x y) y);
  gcd_is_maximal:
    (x:t) -> (y:t) -> (d:t) ->
    Lemma (requires divides #t #(cr_of_id_arg gcd_id) d x /\
                    divides #t #(cr_of_id_arg gcd_id) d y)
          (ensures  divides #t #(cr_of_id_arg gcd_id) d (gcd x y));
}

instance id_of_gcdd (t:Type) {| g: gcd_domain t |} : integral_domain t = g.gcd_id

(* ------------------------------------------------------------------ *)
(*  ufd                                                               *)
(*                                                                    *)
(*  Marker class on the chain — substantive UFD axioms (irreducible   *)
(*  existence + uniqueness up to units) are deferred. For the         *)
(*  divisibility chain we only need the linear projection so that     *)
(*  any function with `{| ufd t |}` constraint is callable from an    *)
(*  `{| euclidean_domain t |}` site.                                  *)
(* ------------------------------------------------------------------ *)

class ufd (t:Type) = {
  [@@@TC.no_method] ufd_gd: gcd_domain t;
}

instance gcdd_of_ufd (t:Type) {| u: ufd t |} : gcd_domain t = u.ufd_gd

(* ------------------------------------------------------------------ *)
(*  euclidean_domain                                                  *)
(* ------------------------------------------------------------------ *)

class euclidean_domain (t:Type) = {
  [@@@TC.no_method] ed_ufd: ufd t;
  euclidean_norm: t -> nat;
  ed_divmod:
    (a:t) -> (b:t) ->
    Pure (t & t)
         (requires is_nonzero #t #(acg_of_id_arg (id_of_gcdd t
                                    #(gcdd_of_ufd t #ed_ufd))) b)
         (ensures  fun _ -> True);
  ed_divmod_correct:
    (a:t) -> (b:t) ->
    Lemma (requires is_nonzero #t #(acg_of_id_arg (id_of_gcdd t
                                     #(gcdd_of_ufd t #ed_ufd))) b)
          (ensures  (let (q, r) = ed_divmod a b in
                     eq a (add (mul b q) r)));
  ed_divmod_decreasing:
    (a:t) -> (b:t) ->
    Lemma (requires is_nonzero #t #(acg_of_id_arg (id_of_gcdd t
                                     #(gcdd_of_ufd t #ed_ufd))) b)
          (ensures  (let (q, r) = ed_divmod a b in
                     is_nonzero #t #(acg_of_id_arg (id_of_gcdd t
                                      #(gcdd_of_ufd t #ed_ufd))) r ==>
                     euclidean_norm r < euclidean_norm b));
}

instance ufd_of_ed (t:Type) {| e: euclidean_domain t |} : ufd t = e.ed_ufd

(* ------------------------------------------------------------------ *)
(*  Basic derived lemmas                                              *)
(* ------------------------------------------------------------------ *)

let divides_refl (#t:Type) {| cr: commutative_ring t |} (x: t)
  : Lemma (divides x x)
  = mul_one x;
    assert (eq (mul x one) x);
    symmetry (mul x one) x;
    divides_intro x x one

let divides_trans (#t:Type) {| cr: commutative_ring t |} (a b c: t)
  : Lemma (requires divides a b /\ divides b c)
          (ensures  divides a c)
  = eliminate exists (k1: t). eq b (mul a k1)
    returns divides a c
    with hyp1.
    begin
      eliminate exists (k2: t). eq c (mul b k2)
      returns divides a c
      with hyp2.
      begin
        let k = mul k1 k2 in
        reflexivity k2;
        assert (eq k2 k2);
        assert (eq b (mul a k1));
        mul_congruence b k2 (mul a k1) k2;
        assert (eq (mul b k2) (mul (mul a k1) k2));
        assert (eq c (mul b k2));
        transitivity c (mul b k2) (mul (mul a k1) k2);
        mul_associativity a k1 k2;
        transitivity c (mul (mul a k1) k2) (mul a k);
        divides_intro a c k
      end
    end

(* ------------------------------------------------------------------ *)
(*  Divisibility — derived lemmas for GCD machinery                   *)
(* ------------------------------------------------------------------ *)

let divides_zero (#t:Type) {| cr: commutative_ring t |} (d: t)
  : Lemma (divides d (zero <: t))
  = H.x_mul_zero d;
    symmetry (mul d (zero <: t)) (zero <: t);
    divides_intro d (zero <: t) (zero <: t)

let divides_congruence_right
    (#t:Type) {| cr: commutative_ring t |} (d a b: t)
  : Lemma (requires divides d a /\ eq a b)
          (ensures  divides d b)
  = eliminate exists (k: t). eq a (mul d k)
    returns divides d b
    with hyp.
    begin
      symmetry a b;
      transitivity b a (mul d k);
      divides_intro d b k
    end

let divides_congruence_left
    (#t:Type) {| cr: commutative_ring t |} (d1 d2 a: t)
  : Lemma (requires divides d1 a /\ eq d1 d2)
          (ensures  divides d2 a)
  = eliminate exists (k: t). eq a (mul d1 k)
    returns divides d2 a
    with hyp.
    begin
      reflexivity k;
      mul_congruence d1 k d2 k;
      assert (eq (mul d1 k) (mul d2 k));
      transitivity a (mul d1 k) (mul d2 k);
      divides_intro d2 a k
    end

let divides_neg (#t:Type) {| cr: commutative_ring t |} (d a: t)
  : Lemma (requires divides d a)
          (ensures  divides d (neg a))
  = eliminate exists (k: t). eq a (mul d k)
    returns divides d (neg a)
    with hyp.
    begin
      (* a = d * k  ⇒  -a = -(d*k) = d*(-k) *)
      neg_congruence a (mul d k);
      assert (eq (neg a) (neg (mul d k)));
      (* Ring identity: -(d*k) = d * (-k). canon_ring closes this. *)
      assert (eq (neg (mul d k)) (mul d (neg k))) by canon_ring ();
      transitivity (neg a) (neg (mul d k)) (mul d (neg k));
      divides_intro d (neg a) (neg k)
    end

let divides_add (#t:Type) {| cr: commutative_ring t |} (d a b: t)
  : Lemma (requires divides d a /\ divides d b)
          (ensures  divides d (add a b))
  = eliminate exists (k1: t). eq a (mul d k1)
    returns divides d (add a b)
    with hyp1.
    begin
      eliminate exists (k2: t). eq b (mul d k2)
      returns divides d (add a b)
      with hyp2.
      begin
        let k = add k1 k2 in
        (* d * (k1 + k2) = d*k1 + d*k2 *)
        left_distributivity d k1 k2;
        symmetry (mul d (add k1 k2)) (add (mul d k1) (mul d k2));
        (* a + b ~ d*k1 + d*k2 *)
        add_congruence a b (mul d k1) (mul d k2);
        transitivity (add a b) (add (mul d k1) (mul d k2)) (mul d k);
        divides_intro d (add a b) k
      end
    end

let divides_sub (#t:Type) {| cr: commutative_ring t |} (d a b: t)
  : Lemma (requires divides d a /\ divides d b)
          (ensures  divides d (add a (neg b)))
  = divides_neg d b;
    divides_add d a (neg b)

let divides_mul_right (#t:Type) {| cr: commutative_ring t |} (d a c: t)
  : Lemma (requires divides d a)
          (ensures  divides d (mul a c))
  = eliminate exists (k: t). eq a (mul d k)
    returns divides d (mul a c)
    with hyp.
    begin
      reflexivity c;
      mul_congruence a c (mul d k) c;
      mul_associativity d k c;
      transitivity (mul a c) (mul (mul d k) c) (mul d (mul k c));
      divides_intro d (mul a c) (mul k c)
    end

let divides_mul_left (#t:Type) {| cr: commutative_ring t |} (d a c: t)
  : Lemma (requires divides d c)
          (ensures  divides d (mul a c))
  = divides_mul_right d c a;
    cr.cr_mic.mul_commutativity c a;
    divides_congruence_right d (mul c a) (mul a c)
