module FStar.CAS.Polynomial

(*
  Univariate polynomials over an additive/ring structure — public interface.

  Representation: a list of coefficients, index 0 = constant term. Trailing
  zeros are permitted; `poly_eq` ignores them. Phase 1 deliverable: full ring
  structure on `polynomial t` for a `ring t` (no admits).
*)

module TC = FStar.Tactics.Typeclasses
module L = FStar.List.Tot

open FStar.CAS.Equatable
open FStar.CAS.Grouplikes
open FStar.CAS.Ringlikes

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

val poly_add_sub_cancel (#t:Type) {| g: add_comm_group t |} (t_poly p: polynomial t)
  : Lemma (poly_eq #t #g.add_group.add_monoid.has_zero
             (poly_add t_poly (poly_sub p t_poly)) p)

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

val semiring_has_zero_unfold (#t:Type) (r: semiring t)
  : Lemma (ensures semiring_has_zero r == r.add_comm_monoid.add_monoid.has_zero)

val scalar_mul_zero (#t:Type) {| r: semiring t |} (q: polynomial t)
  : Lemma (ensures all_zero #t #(semiring_has_zero r) (scalar_mul zero q))

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

val cons_congruence (#t:Type) {| h: has_zero t |} (a b: t) (p q: polynomial t)
  : Lemma (requires a = b /\ poly_eq p q) (ensures poly_eq (a :: p) (b :: q))

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

val scalar_mul_cons_zero (#t:Type) {| r: semiring t |} (a: t) (p: polynomial t)
  : Lemma (poly_eq #t #(semiring_has_zero r)
            (scalar_mul a (zero :: p))
            (zero :: scalar_mul a p))

val poly_mul_cons_zero (#t:Type) {| r: semiring t |} (x s: polynomial t)
  : Lemma (poly_eq #t #(semiring_has_zero r)
            (poly_mul (zero :: x) s)
            (zero :: poly_mul x s))

val poly_mul_singleton (#t:Type) {| r: semiring t |} (c: t) (q: polynomial t)
  : Lemma (poly_eq #t #(semiring_has_zero r) (poly_mul [c] q) (scalar_mul c q))

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

(* ------------------------------------------------------------------------ *)
(*  Canonical form, degree, leading coefficient, evaluation                 *)
(* ------------------------------------------------------------------------ *)

val poly_normalize (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : polynomial t

val poly_normalize_no_trailing_zero
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (ensures (let np = poly_normalize p in
                    L.length np = 0 \/
                    ~ (L.index np (Prims.op_Subtraction (L.length np) 1) = zero)))

val poly_normalize_all_zero_is_empty
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (requires all_zero p)
          (ensures L.length (poly_normalize p) = 0)

val poly_eq_self_normalize
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (ensures poly_eq p (poly_normalize p))

val degree (#t:Type) {| h: has_zero t |} (p: polynomial t) : option nat

val leading_coefficient (#t:Type) {| h: has_zero t |} (p: polynomial t) : t

val eval (#t:Type) {| r: semiring t |} (p: polynomial t) (x: t) : t

val eval_all_zero (#t:Type) {| r: semiring t |} (p: polynomial t) (x: t)
  : Lemma (requires all_zero #t #(semiring_has_zero r) p)
          (ensures eval p x = zero)

val eval_well_defined (#t:Type) {| r: semiring t |} (p q: polynomial t) (x: t)
  : Lemma (requires poly_eq #t #(semiring_has_zero r) p q)
          (ensures eval p x = eval q x)

val eval_poly_zero (#t:Type) {| r: semiring t |} (x: t)
  : Lemma (eval #t #r poly_zero x = zero)

val eval_poly_one (#t:Type) {| r: semiring t |} (x: t)
  : Lemma (eval #t #r poly_one x = one)

val poly_mul_commutative (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma (ensures poly_eq #t #(semiring_has_zero cr.ring.semiring) (poly_mul p q) (poly_mul q p))

instance val polynomial_mul_comm_magma (#t:Type) {| cr: commutative_ring t |}
  : mul_comm_magma (polynomial t)

instance val polynomial_mul_comm_semigroup (#t:Type) {| cr: commutative_ring t |}
  : mul_comm_semigroup (polynomial t)

instance val polynomial_mul_comm_monoid (#t:Type) {| cr: commutative_ring t |}
  : mul_comm_monoid (polynomial t)

instance val polynomial_commutative_ring (#t:Type) {| cr: commutative_ring t |}
  : commutative_ring (polynomial t)

instance val polynomial_zero_ne_one_semiring (#t:Type) {| z: zero_ne_one_semiring t |}
  : zero_ne_one_semiring (polynomial t)

instance val polynomial_domain (#t:Type) {| d: domain t |}
  : domain (polynomial t)

instance val polynomial_integral_domain (#t:Type) {| id: integral_domain t |}
  : integral_domain (polynomial t)


(* Evaluation homomorphism. *)
val eval_add (#t:Type) {| r: semiring t |} (p q: polynomial t) (x: t)
  : Lemma (eval (poly_add #t #r.add_comm_monoid.add_monoid p q) x
           = eval p x + eval q x)

val eval_cons_zero (#t:Type) {| r: semiring t |} (p: polynomial t) (x: t)
  : Lemma (eval ((zero #t) :: p) x = x * eval p x)

val eval_scalar_mul (#t:Type) {| cr: commutative_ring t |} (a: t) (q: polynomial t) (x: t)
  : Lemma (eval #t #cr.ring.semiring (scalar_mul a q) x = a * eval q x)

val eval_mul (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) (x: t)
  : Lemma (eval #t #cr.ring.semiring (poly_mul p q) x = eval p x * eval q x)

(* ====================================================================== *)
(*  degree(p*q) and lc(p*q) over an integral domain                        *)
(* ====================================================================== *)

val degree_poly_zero (#t:Type) {| h: has_zero t |} (u: unit)
  : Lemma (degree #t #h (poly_zero #t) == None)

val degree_well_defined
  (#t:Type) {| h: has_zero t |} (p q: polynomial t)
  : Lemma (requires poly_eq p q)
          (ensures degree p == degree q)

val poly_normalize_idempotent_when_last_nonzero
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (requires Cons? p /\
                    ~ (L.index p (Prims.op_Subtraction (L.length p) 1) = zero))
          (ensures poly_normalize p == p)

val degree_mul
  (#t:Type) {| id: integral_domain t |} (p q: polynomial t)
  : Lemma (requires Some? (degree #t #(semiring_has_zero id.commutative_ring.ring.semiring) p) /\
                    Some? (degree #t #(semiring_has_zero id.commutative_ring.ring.semiring) q))
          (ensures (let ha = semiring_has_zero id.commutative_ring.ring.semiring in
                    degree #t #ha (poly_mul p q) ==
                    Some (Prims.op_Addition
                            (Some?.v (degree #t #ha p))
                            (Some?.v (degree #t #ha q)))))

val poly_normalize_index_eq_index
  (#t:Type) {| h: has_zero t |} (p: polynomial t) (i: nat)
  : Lemma (requires i < L.length (poly_normalize p))
          (ensures L.length (poly_normalize p) <= L.length p /\
                   L.index (poly_normalize p) i == L.index p i)

val coeff_at (#t:Type) {| h: has_zero t |} (p: polynomial t) (i: nat) : t

val poly_eq_coeff_at
  (#t:Type) {| h: has_zero t |} (p q: polynomial t) (i: nat)
  : Lemma (requires poly_eq p q)
          (ensures coeff_at p i = coeff_at q i)

val lc_well_defined
  (#t:Type) {| h: has_zero t |} (p q: polynomial t)
  : Lemma (requires poly_eq p q)
          (ensures leading_coefficient p = leading_coefficient q)

val lc_mul
  (#t:Type) {| id: integral_domain t |} (p q: polynomial t)
  : Lemma (requires Some? (degree #t #(semiring_has_zero id.commutative_ring.ring.semiring) p) /\
                    Some? (degree #t #(semiring_has_zero id.commutative_ring.ring.semiring) q))
          (ensures (let ha = semiring_has_zero id.commutative_ring.ring.semiring in
                    leading_coefficient #t #ha (poly_mul p q) =
                    leading_coefficient #t #ha p * leading_coefficient #t #ha q))

val coeff_at_unfold
  (#t:Type) {| h: has_zero t |} (p: polynomial t) (i: nat)
  : Lemma (ensures coeff_at p i ==
                   (if i < L.length p then L.index p i else zero))


val poly_add_nil_left (#t:Type) {| m: add_monoid t |} (q: polynomial t)
  : Lemma (ensures poly_add #t #m [] q == q)

val poly_add_nil_right (#t:Type) {| m: add_monoid t |} (p: polynomial t)
  : Lemma (ensures poly_add #t #m p [] == p)

val poly_add_cons_cons (#t:Type) {| m: add_monoid t |}
                       (a: t) (p': polynomial t) (b: t) (q': polynomial t)
  : Lemma (ensures poly_add #t #m (a :: p') (b :: q') == (a + b) :: poly_add p' q')

val scalar_mul_nil (#t:Type) {| r: semiring t |} (a: t)
  : Lemma (ensures scalar_mul a ([] <: polynomial t) == [])

val scalar_mul_cons (#t:Type) {| r: semiring t |} (a: t) (b: t) (q': polynomial t)
  : Lemma (ensures scalar_mul a (b :: q') == (a * b) :: scalar_mul a q')

val poly_neg_nil (#t:Type) {| g: add_comm_group t |} (u: unit)
  : Lemma (ensures poly_neg #t #g [] == [])

val poly_neg_cons (#t:Type) {| g: add_comm_group t |} (a: t) (p': polynomial t)
  : Lemma (ensures poly_neg (a :: p') == (-a) :: poly_neg p')

val all_zero_nil (#t:Type) {| h: has_zero t |} (u: unit)
  : Lemma (ensures all_zero #t #h [] == true)

val all_zero_cons (#t:Type) {| h: has_zero t |} (a: t) (p': polynomial t)
  : Lemma (ensures all_zero (a :: p') == ((a = zero) && all_zero p'))

val poly_eq_nil_left (#t:Type) {| h: has_zero t |} (q: polynomial t)
  : Lemma (ensures poly_eq ([] <: polynomial t) q == all_zero q)

val poly_eq_nil_right (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (ensures poly_eq p ([] <: polynomial t) == all_zero p)

val poly_eq_cons_cons (#t:Type) {| h: has_zero t |}
                      (a: t) (p': polynomial t) (b: t) (q': polynomial t)
  : Lemma (ensures poly_eq (a :: p') (b :: q') == ((a = b) && poly_eq p' q'))

val poly_sub_unfold (#t:Type) {| g: add_comm_group t |} (p q: polynomial t)
  : Lemma (ensures poly_sub p q == poly_add p (poly_neg q))
val all_zero_of_coeff_zero (#t:Type) {| h: has_zero t |} (q: polynomial t)
  : Lemma (requires forall (i: nat). coeff_at q i = zero)
          (ensures all_zero q)

val coeff_at_to_poly_eq (#t:Type) {| h: has_zero t |} (p q: polynomial t)
  : Lemma (requires forall (i: nat). coeff_at p i = coeff_at q i)
          (ensures poly_eq p q)

(* Euclidean-division helpers *)
val lc_nonzero_of_degree_some (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (requires Some? (degree p))
          (ensures ~(leading_coefficient p = zero))

val coeff_at_degree_eq_lc (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (requires Some? (degree p))
          (ensures coeff_at p (Some?.v (degree p)) = leading_coefficient p)

val coeff_above_degree_is_zero (#t:Type) {| h: has_zero t |} (p: polynomial t) (i: nat)
  : Lemma (requires (degree p == None \/ (Some? (degree p) /\ i > Some?.v (degree p))))
          (ensures coeff_at p i = zero)

val degree_lt_from_coeff_zero (#t:Type) {| h: has_zero t |} (p: polynomial t) (n: nat)
  : Lemma (requires (forall (i:nat). i >= n ==> coeff_at p i = zero))
          (ensures (degree p == None \/ (Some? (degree p) /\ Some?.v (degree p) < n)))