module FStar.CAS.Ringlikes

(*
  Public interface for the ring-like typeclass tower:

    semiring → ring → comm_ring → domain → integral_domain
                                  → zero_ne_one_semiring
                                  → division_ring → field

  Implementation in `FStar.CAS.Ringlikes.fst`.
*)

module TC = FStar.Tactics.Typeclasses

open FStar.CAS.Equatable
open FStar.CAS.Grouplikes

(* ------------------------------------------------------------------------ *)
(*  Auxiliary types                                                         *)
(* ------------------------------------------------------------------------ *)

type left_distributivity_lemma (#t:Type) {| equatable t |} (mul add: t->t->t)
  = x:t -> y:t -> z:t -> Lemma (mul x (add y z) = add (mul x y) (mul x z))

type right_distributivity_lemma (#t:Type) {| equatable t |} (mul add: t->t->t)
  = x:t -> y:t -> z:t -> Lemma (mul (add x y) z = add (mul x z) (mul y z))

type valuation =
  | Value of nat
  | Nothing

unfold let add_of t {| has_add t |} = let add (x y:t) = x+y in add
unfold let mul_of t {| has_mul t |} = let mul (x y:t) = x*y in mul

instance mul_of_mul_monoid (#t:Type) {| m: mul_monoid t |} : has_mul t
  = m.mul_semigroup.has_mul

(* ------------------------------------------------------------------------ *)
(*  Semiring                                                                *)
(* ------------------------------------------------------------------------ *)

class semiring (t:Type) = {
  [@@@TC.no_method] add_comm_monoid: add_comm_monoid t;
  [@@@TC.no_method] mul_monoid: (z:mul_monoid t{ z.mul_semigroup.has_mul.eq ==
                                                 add_comm_monoid.add_monoid.add_semigroup.has_add.eq });
  left_absorption      : left_absorber_lemma (mul_of t #mul_monoid.mul_semigroup.has_mul) zero;
  right_absorption     : right_absorber_lemma (mul_of t #mul_monoid.mul_semigroup.has_mul) zero;
  left_distributivity  : left_distributivity_lemma #t (mul_of t #mul_monoid.mul_semigroup.has_mul) ( + );
  right_distributivity : right_distributivity_lemma #t (mul_of t #mul_monoid.mul_semigroup.has_mul) ( + );
}

instance add_cm_of_semiring (t:Type) (r: semiring t) : add_comm_monoid t = r.add_comm_monoid
instance mul_m_of_semiring  (t:Type) (r: semiring t) : mul_monoid t = r.mul_monoid

instance eq_of_acg (#t:Type) {| g: add_comm_group t |} : equatable t
  = g.add_group.add_monoid.add_semigroup.has_add.eq

instance hm_r (#t:Type) (r: semiring t) : has_mul t = r.mul_monoid.mul_semigroup.has_mul
instance ha_r (#t:Type) (r: semiring t) : has_add t = r.add_comm_monoid.add_monoid.add_semigroup.has_add
instance he_r (#t:Type) (r: semiring t) : equatable t = r.mul_monoid.mul_semigroup.has_mul.eq

val absorption (#t:Type) {| r: semiring t |} (z x:t)
  : Lemma (requires z=zero) (ensures (z*x = zero) /\ (x*z = zero))

val absorber_is_two_sided_from_lemmas (#t:Type) {| r: semiring t |} (#z1 #z2: t)
  (z1_is_absorber: left_absorber_lemma ( * ) z1)
  (z2_is_absorber: right_absorber_lemma ( * ) z2)
  : Lemma (z1 = z2)

val absorber_is_two_sided_from_forall (#t:Type) {| r: semiring t |} (z1 z2:t)
  : Lemma (requires (forall (x:t). z1*x = z1 /\ x*z2 = z2))
          (ensures z1 = z2)

(* ------------------------------------------------------------------------ *)
(*  Ring                                                                    *)
(* ------------------------------------------------------------------------ *)

class ring (t:Type) = {
  [@@@TC.no_method] semiring: semiring t;
  [@@@TC.no_method] add_comm_group: (z:add_comm_group t{z.add_comm_monoid == semiring.add_comm_monoid});
}

instance add_comm_group_of_ring (t:Type) (r: ring t) : add_comm_group t = r.add_comm_group
instance semiring_of_ring (t:Type) (r: ring t) : semiring t = r.semiring

val ring_add_left_cancellation (#t:Type) {| r: ring t |} (x y z: t)
  : Lemma (requires x+y=x+z) (ensures y=z)

val ring_add_right_cancellation (#t:Type) {| r: ring t |} (x y z: t)
  : Lemma (requires y+x=z+x) (ensures y=z)

val ring_zero_is_right_absorber (#t:Type) {| r: ring t |} (x:t)
  : Lemma (x * zero = zero)

val ring_zero_is_left_absorber (#t:Type) {| r: ring t |} (x:t)
  : Lemma (zero * x = zero)

val ring_zero_is_absorber (#t:Type) {| r: ring t |} (x:t)
  : Lemma (zero * x = zero /\ x * zero = zero)

val ring_neg_x_is_minus_one_times_x (#t:Type) {| r: ring t |} (x:t)
  : Lemma (-x = (-one)*x)

val ring_neg_x_is_x_times_minus_one (#t:Type) {| r: ring t |} (x:t)
  : Lemma (-x = x*(-one))

val ring_neg_one_commutes_with_everything (#t:Type) {| r: ring t |} (x:t)
  : Lemma (x*(-one) = (-one)*x)

val ring_neg_xy_is_x_times_neg_y (#t:Type) {| r: ring t |} (x y: t)
  : Lemma (-(x*y) = x*(-y))

val ring_neg_xy_is_neg_x_times_y (#t:Type) {| r: ring t |} (x y: t)
  : Lemma (-(x*y) = (-x)*y)

val ring_neg_flip_in_product (#t:Type) {| r: ring t |} (x y: t)
  : Lemma ((-x)*y = x*(-y))

val ring_neg_left_distributivity (#t:Type) {| r: ring t |} (x y z: t)
  : Lemma (x*(y + -z) = x*y + -(x*z))

val ring_neg_right_distributivity (#t:Type) {| r: ring t |} (x y z: t)
  : Lemma ((x + -y) * z = x*z + -(y*z))

(* ------------------------------------------------------------------------ *)
(*  Zero ≠ one, domain                                                      *)
(* ------------------------------------------------------------------------ *)

class zero_ne_one_semiring (t:Type) = {
  [@@@TC.no_method] semiring: (r:semiring t{ zero <> r.mul_monoid.has_one.one });
}

instance semiring_of_zero_ne_one (t:Type) {| r: zero_ne_one_semiring t |} : semiring t = r.semiring

class domain (t:Type) = {
  [@@@TC.no_method] ring: ring t;
  [@@@TC.no_method] zero_ne_one_semiring: r:zero_ne_one_semiring t{r.semiring == ring.semiring};
  domain_law: (x:t -> y:t -> Lemma (requires x*y = zero) (ensures (x=zero) || (y=zero)))
}

instance ring_of_domain (t:Type) {| d: domain t |} : ring t = d.ring
instance zero_ne_one_semiring_of_domain (t:Type) {| d: domain t |} : zero_ne_one_semiring t = d.zero_ne_one_semiring

val left_cancellation (#t:Type) {| d: domain t |} (x y z: t)
  : Lemma (requires (x*y = x*z) /\ (x<>zero)) (ensures y=z)

val right_cancellation (#t:Type) {| d: domain t |} (x y z: t)
  : Lemma (requires (y*x = z*x) /\ (x<>zero)) (ensures y=z)

val semiring_nonzero_product_means_nonzero_factors
  (#t:Type) {| r: semiring t |} (x y:t)
  : Lemma (requires x*y <> zero) (ensures x <> zero /\ y <> zero)

val domain_nonzero_factors_means_nonzero_product
  (#t:Type) {| d: domain t |} (x y: t)
  : Lemma (requires (x<>zero) /\ (y<>zero)) (ensures x*y <> zero)

val domain_pq_eq_pr_lemma (#t:Type) {| d: domain t |} (p q r: t)
  : Lemma (requires p*q = p*r) (ensures (p=zero) \/ (q=r))

(* ------------------------------------------------------------------------ *)
(*  Commutative ring                                                        *)
(* ------------------------------------------------------------------------ *)

class commutative_ring (t:Type) = {
  [@@@TC.no_method] ring: ring t;
  [@@@TC.no_method] mul_comm_monoid: (m:mul_comm_monoid t{m.mul_monoid == ring.semiring.mul_monoid});
}

instance ring_of_commutative_ring (t:Type) (r: commutative_ring t) : ring t = r.ring
instance mul_comm_monoid_of_comm_ring (t:Type) (r: commutative_ring t) : mul_comm_monoid t = r.mul_comm_monoid

(* ------------------------------------------------------------------------ *)
(*  Natural-number norm helpers                                             *)
(* ------------------------------------------------------------------------ *)

unfold let nat_norm (t:Type) = t -> option nat

val test_nf (#t:Type) (nf: nat_norm t) (z:t) (x:t) : prop

val make_trivial_eq_instance (#t:Type) (eq: t->t->bool)
  : Pure (equatable t)
         (requires (forall x. eq x x) /\
                   (forall x y. eq x y <==> eq y x) /\
                   (forall x y z. (eq x y /\ eq y z) ==> eq x z))
         (ensures fun _ -> True)

instance option_nat_eq : equatable (option nat) = make_trivial_eq_instance op_Equality

unfold let nat_norm_property (#t:Type) {| r: ring t |} (nf: nat_norm t) (x:t)
  = (x = zero) <==> ((nf x) = None)

instance eq_of_mul_monoid (#t:Type) (m: mul_monoid t) : equatable t = m.mul_semigroup.has_mul.eq

(* ------------------------------------------------------------------------ *)
(*  Multiplicative-monoid predicates                                        *)
(* ------------------------------------------------------------------------ *)

unfold let is_unit (#t:Type) {| h: mul_monoid t |} (x:t)
  = exists (x':t). x' * x = one

unfold let is_divisor_of (#t:Type) {| h: mul_monoid t |} (divisor dividend: t)
  = exists (quotient: t). quotient * divisor = dividend

unfold let are_associates (#t:Type) {| h: mul_monoid t |} (p q: t)
  = is_divisor_of p q /\ is_divisor_of q p

unfold let is_irreducible (#t:Type) {| h: mul_monoid t |} (x:t) =
  (~(is_unit x)) /\
  (forall (p q:t). ((q*p = x) ==> ((are_associates p x /\ is_unit q) \/
                                   (are_associates q x /\ is_unit p))))

unfold let is_prime (#t:Type) {| h: mul_monoid t |} (p:t) =
  (~(is_unit p)) /\ (forall (m n:t). (is_divisor_of p (m*n) ==>
                                      (is_divisor_of p m \/ is_divisor_of p n)))

type units_of t {| h: mul_monoid t |} = x:t{is_unit x}

val unit_product_is_unit (#t:Type) {| h: mul_monoid t |} (x y: units_of t)
  : Lemma (is_unit #t (x*y))

(* ------------------------------------------------------------------------ *)
(*  Integral domain, division ring, field                                   *)
(* ------------------------------------------------------------------------ *)

class integral_domain (t:Type) = {
  [@@@TC.no_method] commutative_ring: commutative_ring t;
  [@@@TC.no_method] domain: (d:domain t{d.ring == commutative_ring.ring});
}

instance comm_ring_of_id (t:Type) (id: integral_domain t) : commutative_ring t = id.commutative_ring
instance domain_of_id (t:Type) (id: integral_domain t) : domain t = id.domain

class division_ring (t:Type) = {
  [@@@TC.no_method] domain: domain t;
  inv: (x:t{x <> zero}) -> (x':t{(x' * x = one) /\ (x * x' = one)});
}

instance domain_of_div_ring (t:Type) (dr: division_ring t) : domain t = dr.domain

class field (t:Type) = {
  [@@@TC.no_method] division_ring: division_ring t;
  [@@@TC.no_method] commutative_ring: c:commutative_ring t{c.ring == division_ring.domain.ring};
}

instance dr_of_field (t:Type) (f: field t) : division_ring t = f.division_ring
instance comm_ring_of_field (t:Type) (f: field t) : commutative_ring t = f.commutative_ring

(* ------------------------------------------------------------------------ *)
(*  Ideals (forward-looking, used by future modules)                        *)
(* ------------------------------------------------------------------------ *)

unfold let survives_addition (#t:Type) {|r:ring t|} (f: t->bool)
  = forall (x y: (q:t{f q})). f (x + y)

unfold let survives_rmul (#t:Type) {|r:ring t|} (f:t->bool)
  = forall (x:t{f x}) (y:t). f (x*y)

unfold let survives_lmul (#t:Type) {|r:ring t|} (f:t->bool)
  = forall (x:t{f x}) (y:t). f (y*x)

type left_ideal_func t {| r: ring t |} =
  (f:(t -> bool) { survives_addition f /\ survives_lmul f })

type right_ideal_func t {| r: ring t |} =
  (f:(t -> bool) { survives_addition f /\ survives_rmul f })

type ideal_func t {|r: ring t|} = (m:left_ideal_func t{survives_rmul m})

type ideal #t {|r:ring t|} (f:ideal_func t) = x:t{f x}
type left_ideal #t {|r:ring t|} (f:left_ideal_func t) = x:t{f x}
type right_ideal #t {|r:ring t|} (f:right_ideal_func t) = x:t{f x}

type principal_left_ideal #t {|r: ring t|} (x:t) = p:t{exists (q:t). q*x = p}
type principal_right_ideal #t {|r: ring t|} (x:t) = p:t{exists (q:t). x*q = p}

unfold let eq_prop (#t:Type) {| equatable t |} (x y:t) : prop = (x=y) == true

val principal_left_ideal_multiplier
  (#t:Type) {|r:ring t|} (x:t) (p:principal_left_ideal x)
  : GTot(z:t{z*x = p})

val principal_right_ideal_multiplier
  (#t:Type) {|r:ring t|} (x:t) (p: principal_right_ideal x)
  : GTot(z:t{x*z = p})
