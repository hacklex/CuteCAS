module FStar.Algebra.Classes.Polynomial

(*
  Univariate polynomials over an additive/ring structure — public interface.

  Representation: a list of coefficients, index 0 = constant term. Trailing
  zeros are permitted; `poly_eq` ignores them. Phase 1 deliverable: full ring
  structure on `polynomial t` for a `ring t` (no admits).
*)

module TC = FStar.Tactics.Typeclasses
module L = FStar.List.Tot

open FStar.Algebra.Classes.Equatable
open FStar.Algebra.Classes.Grouplikes
open FStar.Algebra.Classes.Ringlikes

(* ------------------------------------------------------------------------ *)
(*  Representation                                                          *)
(* ------------------------------------------------------------------------ *)

type polynomial (t:Type) = list t

val coeff (#t:Type) {| h: has_zero t |} (p: polynomial t) (i: nat) : t

val poly_zero (#t:Type) : polynomial t

val poly_one (#t:Type) {| h: has_one t |} : polynomial t

(* ------------------------------------------------------------------------ *)
(*  Coefficient-wise equality (trailing zeros ignored)                      *)
(* ------------------------------------------------------------------------ *)

val all_zero (#t:Type) {| h: has_zero t |} (p: polynomial t) : bool

val poly_eq (#t:Type) {| h: has_zero t |} (p q: polynomial t) : bool

val poly_eq_reflexivity (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (ensures poly_eq p p)

val poly_eq_symmetry (#t:Type) {| h: has_zero t |} (p q: polynomial t)
  : Lemma (ensures poly_eq p q <==> poly_eq q p)

val poly_eq_transitivity (#t:Type) {| h: has_zero t |} (p q r: polynomial t)
  : Lemma (requires poly_eq p q /\ poly_eq q r) (ensures poly_eq p r)

instance val polynomial_equatable (#t:Type) {| h: has_zero t |}
  : equatable (polynomial t)

(* ------------------------------------------------------------------------ *)
(*  Addition                                                                *)
(* ------------------------------------------------------------------------ *)

val poly_add (#t:Type) {| m: add_monoid t |} (p q: polynomial t) : polynomial t

val poly_add_left_all_zero (#t:Type) {| m: add_monoid t |} (p q: polynomial t)
  : Lemma (requires all_zero #t #m.has_zero p)
          (ensures poly_eq #t #m.has_zero (poly_add p q) q)

val poly_add_right_all_zero (#t:Type) {| m: add_monoid t |} (p q: polynomial t)
  : Lemma (requires all_zero #t #m.has_zero q)
          (ensures poly_eq #t #m.has_zero (poly_add p q) p)

val poly_add_congruence (#t:Type) {| m: add_monoid t |}
                        (p1 q1 p2 q2: polynomial t)
  : Lemma (requires poly_eq #t #m.has_zero p1 p2 /\ poly_eq #t #m.has_zero q1 q2)
          (ensures poly_eq #t #m.has_zero (poly_add p1 q1) (poly_add p2 q2))

val poly_add_left_identity (#t:Type) {| m: add_monoid t |} (p: polynomial t)
  : Lemma (poly_eq #t #m.has_zero (poly_add (poly_zero #t) p) p)

val poly_add_right_identity (#t:Type) {| m: add_monoid t |} (p: polynomial t)
  : Lemma (poly_eq #t #m.has_zero (poly_add p (poly_zero #t)) p)

val poly_add_associative (#t:Type) {| m: add_monoid t |} (p q r: polynomial t)
  : Lemma (poly_eq #t #m.has_zero
            (poly_add (poly_add p q) r) (poly_add p (poly_add q r)))

val poly_add_commutative (#t:Type) {| m: add_comm_monoid t |} (p q: polynomial t)
  : Lemma (poly_eq #t #m.add_monoid.has_zero (poly_add p q) (poly_add q p))

(* ------------------------------------------------------------------------ *)
(*  Additive instances                                                      *)
(* ------------------------------------------------------------------------ *)

instance val polynomial_has_zero (#t:Type) {| h: has_zero t |}
  : has_zero (polynomial t)

instance val polynomial_has_add (#t:Type) {| m: add_monoid t |}
  : has_add (polynomial t)

instance val polynomial_add_semigroup (#t:Type) {| m: add_monoid t |}
  : add_semigroup (polynomial t)

instance val polynomial_add_monoid (#t:Type) {| m: add_monoid t |}
  : add_monoid (polynomial t)

instance val polynomial_add_comm_magma (#t:Type) {| m: add_comm_monoid t |}
  : add_comm_magma (polynomial t)

instance val polynomial_add_comm_semigroup (#t:Type) {| m: add_comm_monoid t |}
  : add_comm_semigroup (polynomial t)

instance val polynomial_add_comm_monoid (#t:Type) {| m: add_comm_monoid t |}
  : add_comm_monoid (polynomial t)

(* ------------------------------------------------------------------------ *)
(*  Negation                                                                *)
(* ------------------------------------------------------------------------ *)

val poly_neg (#t:Type) {| g: add_comm_group t |} (p: polynomial t) : polynomial t

val poly_sub (#t:Type) {| g: add_comm_group t |} (p q: polynomial t)
  : polynomial t

val poly_neg_congruence (#t:Type) {| g: add_comm_group t |} (p q: polynomial t)
  : Lemma (requires poly_eq #t #g.add_group.add_monoid.has_zero p q)
          (ensures poly_eq #t #g.add_group.add_monoid.has_zero (poly_neg p) (poly_neg q))

instance val polynomial_has_neg (#t:Type) {| g: add_comm_group t |}
  : has_neg (polynomial t)

instance val polynomial_has_sub (#t:Type) {| g: add_comm_group t |}
  : has_sub (polynomial t)

val poly_neg_inversion (#t:Type) {| g: add_comm_group t |} (p: polynomial t)
  : Lemma (poly_eq #t #g.add_group.add_monoid.has_zero (poly_add p (poly_neg p)) poly_zero
        /\ poly_eq #t #g.add_group.add_monoid.has_zero (poly_add (poly_neg p) p) poly_zero)

val poly_sub_def (#t:Type) {| g: add_comm_group t |} (p q: polynomial t)
  : Lemma (poly_eq #t #g.add_group.add_monoid.has_zero
            (poly_sub p q) (poly_add p (poly_neg q)))

instance val polynomial_add_group (#t:Type) {| g: add_comm_group t |}
  : add_group (polynomial t)

instance val polynomial_add_comm_group (#t:Type) {| g: add_comm_group t |}
  : add_comm_group (polynomial t)

(* ------------------------------------------------------------------------ *)
(*  Multiplication                                                          *)
(* ------------------------------------------------------------------------ *)

val scalar_mul (#t:Type) {| r: semiring t |} (a: t) (q: polynomial t) : polynomial t

val poly_mul (#t:Type) {| r: semiring t |} (p q: polynomial t) : polynomial t

val semiring_has_zero (#t:Type) (r: semiring t) : has_zero t

val poly_mul_all_zero_left (#t:Type) {| r: semiring t |} (p q: polynomial t)
  : Lemma (requires all_zero #t #(semiring_has_zero r) p)
          (ensures all_zero #t #(semiring_has_zero r) (poly_mul p q))

val poly_mul_all_zero_right (#t:Type) {| r: semiring t |} (p q: polynomial t)
  : Lemma (requires all_zero #t #(semiring_has_zero r) q)
          (ensures all_zero #t #(semiring_has_zero r) (poly_mul p q))

val poly_mul_congruence (#t:Type) {| r: semiring t |} (p1 q1 p2 q2: polynomial t)
  : Lemma (requires poly_eq #t #(semiring_has_zero r) p1 p2 /\
                    poly_eq #t #(semiring_has_zero r) q1 q2)
          (ensures poly_eq #t #(semiring_has_zero r) (poly_mul p1 q1) (poly_mul p2 q2))

val poly_mul_right_distrib (#t:Type) {| r: semiring t |} (p q1 q2: polynomial t)
  : Lemma (poly_eq #t #(semiring_has_zero r)
            (poly_mul p (poly_add q1 q2))
            (poly_add (poly_mul p q1) (poly_mul p q2)))

val poly_mul_left_distrib (#t:Type) {| r: semiring t |} (p1 p2 q: polynomial t)
  : Lemma (poly_eq #t #(semiring_has_zero r)
            (poly_mul (poly_add p1 p2) q)
            (poly_add (poly_mul p1 q) (poly_mul p2 q)))

val poly_mul_one_left (#t:Type) {| r: semiring t |} (q: polynomial t)
  : Lemma (poly_eq #t #(semiring_has_zero r) (poly_mul (poly_one #t) q) q)

val poly_mul_one_right (#t:Type) {| r: semiring t |} (q: polynomial t)
  : Lemma (poly_eq #t #(semiring_has_zero r) (poly_mul q (poly_one #t)) q)

val poly_mul_associative (#t:Type) {| r: semiring t |} (p q s: polynomial t)
  : Lemma (poly_eq #t #(semiring_has_zero r)
            (poly_mul (poly_mul p q) s) (poly_mul p (poly_mul q s)))

val poly_mul_zero_left (#t:Type) {| r: semiring t |} (q: polynomial t)
  : Lemma (poly_eq #t #(semiring_has_zero r) (poly_mul (poly_zero #t) q) (poly_zero #t))

val poly_mul_zero_right (#t:Type) {| r: semiring t |} (q: polynomial t)
  : Lemma (poly_eq #t #(semiring_has_zero r) (poly_mul q (poly_zero #t)) (poly_zero #t))

(* ------------------------------------------------------------------------ *)
(*  Multiplicative + ring instances                                         *)
(* ------------------------------------------------------------------------ *)

instance val polynomial_has_one (#t:Type) {| r: semiring t |}
  : has_one (polynomial t)

instance val polynomial_has_mul (#t:Type) {| r: semiring t |}
  : has_mul (polynomial t)

instance val polynomial_mul_semigroup (#t:Type) {| r: semiring t |}
  : mul_semigroup (polynomial t)

instance val polynomial_mul_monoid (#t:Type) {| r: semiring t |}
  : mul_monoid (polynomial t)

instance val polynomial_semiring (#t:Type) {| r: semiring t |}
  : semiring (polynomial t)

instance val polynomial_ring (#t:Type) {| r: ring t |}
  : ring (polynomial t)
