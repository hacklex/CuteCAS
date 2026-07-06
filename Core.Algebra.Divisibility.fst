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
open Core.Algebra.Notation
module H = Core.Algebra.Helpers
open Core.Tactics.CanonRing

(* ------------------------------------------------------------------ *)
(*  Divisibility predicate                                            *)
(*                                                                    *)
(*  `divides x y` iff there exists `c` with `y = x * c`.              *)
(* ------------------------------------------------------------------ *)

(* NOTE: the `divides` predicate body and `divides_intro`'s `requires` are kept
   spelled (`eq`/`mul`) rather than `=`/`*`. Although the two forms are
   definitionally equal, `divides` underpins Berlekamp's SMT-fragile `cong` /
   `cong_prod_iff` congruence proofs, and the notation surface form perturbs
   their (already tight) SMT encoding enough to break them. The rest of the
   module is migrated to notation. *)
let divides (#t:Type) {| cr: commutative_ring t |} (x y: t) : prop =
  exists (c: t). eq y (mul x c)

let divides_intro (#t:Type) {| cr: commutative_ring t |}
                  (x y c: t)
  : Lemma (requires eq y (mul x c))
          (ensures  divides x y) = ()

(* Helper used inside class signatures so the projection chain
   `integral_domain → commutative_ring` is reusable without inlining. *)

// unfold let cr_of_id_arg (#t:Type) (i: integral_domain t) : commutative_ring t =
//   cr_of_id t #i

(* Underlying add_comm_group reached through `integral_domain`. *)

// unfold let acg_of_id_arg (#t:Type) (i: integral_domain t) : add_comm_group t =
//   acg_of_r t #(r_of_cr t #(cr_of_id t #i))

(* ------------------------------------------------------------------ *)
(*  gcd_domain                                                        *)
(* ------------------------------------------------------------------ *)

class gcd_domain (t:Type) = {
  [@@@TC.no_method] gcd_id: integral_domain t;
  gcd: t -> t -> t;
  gcd_congruence:
    (x1:t) -> (x2:t) -> (y1:t) -> (y2:t) ->
    Lemma (requires x1 = x2 /\ y1 = y2)
          (ensures  gcd x1 y1 = gcd x2 y2);
  gcd_divides_left:
    (x:t) -> (y:t) ->
    Lemma (divides (gcd x y) x);
  gcd_divides_right:
    (x:t) -> (y:t) ->
    Lemma (divides (gcd x y) y);
  gcd_is_maximal:
    (x:t) -> (y:t) -> (d:t) ->
    Lemma (requires divides d x /\
                    divides d y)
          (ensures  divides d (gcd x y));
}

unfold instance id_of_gcdd (t:Type) {| g: gcd_domain t |} : integral_domain t = g.gcd_id

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

unfold instance gcdd_of_ufd (t:Type) {| u: ufd t |} : gcd_domain t = u.ufd_gd

(* ------------------------------------------------------------------ *)
(*  euclidean_domain                                                  *)
(* ------------------------------------------------------------------ *)

class euclidean_domain (t:Type) = {
  [@@@TC.no_method] ed_ufd: ufd t;
  euclidean_norm: t -> nat;
  (* The norm is a genuine Euclidean function: monotone non-decreasing under
     multiplication by a nonzero element.  NOT derivable from `divmod` (which
     only ever yields `norm remainder < norm divisor`); it is the independent
     second Euclidean-domain axiom.  Gives `a | b /\ is_nonzero b ==> norm a <= norm b`. *)
  norm_monotonicity:
    (x:t) -> (y:t) ->
    Lemma (requires is_nonzero x /\ is_nonzero y)
          (ensures  euclidean_norm x <= euclidean_norm (x * y));
  (* Single division primitive.  Its `Pure` postcondition carries BOTH the
     correctness equation and the strict norm-decrease, so consumers get them
     by destructuring the result — no separate `_correct` / `_decreasing`
     lemmas to invoke. *)
  divmod:
    (a:t) -> (b:t) ->
    Pure (t & t)
         (requires is_nonzero b)
         (ensures  fun (q, r) -> a = (b * q) + r /\
                                 (is_nonzero r ==> euclidean_norm r < euclidean_norm b));
}

unfold instance ufd_of_ed (t:Type) {| e: euclidean_domain t |} : ufd t = e.ed_ufd

(* Quotient / remainder shorthands.  `unfold` so `div a b` / `mod a b` reduce to
   the matching projection of the *same* `divmod a b` call; the `Pure`
   postcondition (correctness equation + norm-decrease) is restated on each so a
   caller that needs only one half gets it adjoined WITHOUT binding
   `let (q, r) = divmod a b`.  Both specs reference `divmod a b` directly, so
   `div a b` and `mod a b` used together provably come from one division. *)
unfold let div (#t:Type) {| e: euclidean_domain t |} (a b: t)
  : Pure t (requires is_nonzero b)
           (ensures fun q -> a = (b * q) + snd (divmod a b) /\
                             (is_nonzero (snd (divmod a b)) ==>
                              euclidean_norm (snd (divmod a b)) < euclidean_norm b))
  = fst (divmod a b)

unfold let mod (#t:Type) {| e: euclidean_domain t |} (a b: t)
  : Pure t (requires is_nonzero b)
           (ensures fun r -> a = (b * fst (divmod a b)) + r /\
                             (is_nonzero r ==> euclidean_norm r < euclidean_norm b))
  = snd (divmod a b)

(* ------------------------------------------------------------------ *)
(*  Basic derived lemmas                                              *)
(* ------------------------------------------------------------------ *)

let divides_refl (#t:Type) {| cr: commutative_ring t |} (x: t)
  : Lemma (divides x x)
  = H.elim_equatable_laws t ();
    mul_one x;
    divides_intro x x one

let divides_trans (#t:Type) {| cr: commutative_ring t |} (a b c: t)
  : Lemma (requires divides a b /\ divides b c)
          (ensures  divides a c)
  = H.elim_equatable_laws t ();
    eliminate exists k1. b = a * k1
    returns divides a c
    with hyp1.
    begin
      eliminate exists (k2: t). c = b * k2
      returns divides a c
      with hyp2.
      begin
        let k = k1 * k2 in
        mul_congruence b k2 (a * k1) k2;
        transitivity c (b * k2) ((a * k1) * k2);
        mul_associativity a k1 k2;
        transitivity c ((a * k1) * k2) (a * k);
        divides_intro a c k
      end
    end

(* ------------------------------------------------------------------ *)
(*  Divisibility — derived lemmas for GCD machinery                   *)
(* ------------------------------------------------------------------ *)

let divides_zero (#t:Type) {| cr: commutative_ring t |} (d: t)
  : Lemma (divides d zero)
  = H.elim_equatable_laws t ();
    H.x_mul_zero d;
    divides_intro d zero zero

let divides_congruence_right
    (#t:Type) {| cr: commutative_ring t |} (d a b: t)
  : Lemma (requires divides d a /\ a = b)
          (ensures  divides d b)
  = H.elim_equatable_laws t ();
    eliminate exists (k: t). a = d * k
    returns divides d b
    with hyp.
    begin
      transitivity b a (d * k);
      divides_intro d b k
    end

let divides_congruence_left
    (#t:Type) {| cr: commutative_ring t |} (d1 d2 a: t)
  : Lemma (requires divides d1 a /\ d1 = d2)
          (ensures  divides d2 a)
  = H.elim_equatable_laws t ();
    eliminate exists (k: t). a = d1 * k
    returns divides d2 a
    with hyp.
    begin
      mul_congruence d1 k d2 k;
      transitivity a (d1 * k) (d2 * k);
      divides_intro d2 a k
    end

let divides_neg (#t:Type) {| cr: commutative_ring t |} (d a: t)
  : Lemma (requires divides d a)
          (ensures  divides d (- a))
  = eliminate exists (k: t). a = d * k
    returns divides d (- a)
    with hyp.
    begin
      neg_congruence a (d * k);
      assert (-(d * k) = d * (-k)) by canon_ring ();
      transitivity (-a) (-(d * k)) (d * (-k));
      divides_intro d (-a) (-k)
    end

let divides_add (#t:Type) {| cr: commutative_ring t |} (d a b: t)
  : Lemma (requires divides d a /\ divides d b)
          (ensures  divides d (a + b))
  = H.elim_equatable_laws t ();
    eliminate exists (k1: t). a = d * k1
    returns divides d (a + b)
    with hyp1.
    begin
      eliminate exists (k2: t). b = d * k2
      returns divides d (a + b)
      with hyp2.
      begin
        let k = k1 + k2 in
        left_distributivity d k1 k2;
        add_congruence a b (d * k1) (d * k2);
        transitivity (a + b) ((d * k1) + (d * k2)) (d * k);
        divides_intro d (a + b) k
      end
    end

let divides_sub (#t:Type) {| cr: commutative_ring t |} (d a b: t)
  : Lemma (requires divides d a /\ divides d b)
          (ensures  divides d (a -- b))
  = divides_neg d b;
    divides_add d a (- b)

let divides_mul_right (#t:Type) {| cr: commutative_ring t |} (d a c: t)
  : Lemma (requires divides d a)
          (ensures  divides d (a * c))
  = H.elim_equatable_laws t ();
    eliminate exists (k: t). a = d * k
    returns divides d (a * c)
    with hyp.
    begin
      mul_congruence a c (d * k) c;
      mul_associativity d k c;
      transitivity (a * c) ((d * k) * c) (d * (k * c));
      divides_intro d (a * c) (k * c)
    end

let divides_mul_left (#t:Type) {| cr: commutative_ring t |} (d a c: t)
  : Lemma (requires divides d c)
          (ensures  divides d (a * c))
  = divides_mul_right d c a;
    mul_commutativity c a;
    divides_congruence_right d (c * a) (a * c)
