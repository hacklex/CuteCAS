module FStar.Algebra.Classes.Ringlikes

module TC = FStar.Tactics.Typeclasses

open FStar.Algebra.Classes.Equatable
open FStar.Algebra.Classes.Grouplikes
 
type left_distributivity_lemma (#t:Type) {| equatable t |} (mul add: t->t->t) = 
  x:t -> y:t -> z:t -> Lemma (mul x (add y z) = add (mul x y) (mul x z))

type right_distributivity_lemma (#t:Type) {| equatable t |} (mul add: t->t->t) = 
  x:t -> y:t -> z:t -> Lemma (mul (add x y) z = add (mul x z) (mul y z))
  
class semiring (t:Type) = {
  [@@@TC.no_method] add_comm_monoid: add_comm_monoid t;
  [@@@TC.no_method] mul_monoid: mul_monoid t;
  equality_consistence : squash (add_comm_monoid.add_monoid.add_semigroup.has_add.eq ==
                                 mul_monoid.mul_semigroup.has_mul.eq);
  left_absorption : left_absorber_lemma mul_monoid.mul_semigroup.has_mul.mul zero;
  right_absorption : right_absorber_lemma mul_monoid.mul_semigroup.has_mul.mul zero;
  left_distributivity : left_distributivity_lemma mul_monoid.mul_semigroup.has_mul.mul 
                                                  add_comm_monoid.add_monoid.add_semigroup.has_add.add;
  right_distributivity : right_distributivity_lemma mul_monoid.mul_semigroup.has_mul.mul 
                                                  add_comm_monoid.add_monoid.add_semigroup.has_add.add;
}
 
instance add_cm_of_semiring (t:Type) ( r: semiring t) = r.add_comm_monoid
instance mul_m_of_semiring (t:Type) (r: semiring t) = r.mul_monoid


instance hm_r #t (r: semiring t) = r.mul_monoid.mul_semigroup.has_mul
instance ha_r #t (r: semiring t) = r.add_comm_monoid.add_monoid.add_semigroup.has_add
instance he_r #t (r: semiring t) = r.mul_monoid.mul_semigroup.has_mul.eq 


let absorber_is_two_sided_from_lemmas #t {| r: semiring t |} (#z1 #z2: t)
  (z1_is_absorber: left_absorber_lemma r.mul_monoid.mul_semigroup.has_mul.mul z1)
  (z2_is_absorber: right_absorber_lemma r.mul_monoid.mul_semigroup.has_mul.mul z2)
  : Lemma (z1 = z2) = 
  z1_is_absorber z2;
  z2_is_absorber z1;
  symmetry (z1*z2) z1;
  transitivity z1 (z1*z2) z2

let absorber_is_two_sided_from_forall (#t:Type) {| r: semiring t |} (z1 z2:t)
  : Lemma (requires (forall (x:t). z1*x = z1 /\ x*z2 = z2))
          (ensures z1 = z2) = 
  symmetry (z1*z2) z1;
  transitivity z1 (z1*z2) z2

class ring (t:Type) = {
  [@@@TC.no_method] add_comm_group: add_comm_group t;
  [@@@TC.no_method] semiring: semiring t;
  [@@@TC.no_method] add_comm_group_consistency: squash (semiring.add_comm_monoid == add_comm_group.add_comm_monoid);
}

instance add_comm_group_of_ring (t:Type) (r: ring t) = r.add_comm_group 
instance semiring_of_ring (t:Type) (r: ring t) = r.semiring

//instance hm_rr #t (r: ring t) = r.semiring.mul_monoid.mul_semigroup.has_mul
//instance ha_rr #t (r: ring t) = r.semiring.add_comm_monoid.add_monoid.add_semigroup.has_add

let ring_add_left_cancellation (#t:Type) {| r: ring t |} (x y z: t)
  : Lemma (requires x+y=x+z) (ensures y=z) = group_cancelation_left x y z
  
let ring_add_right_cancellation (#t:Type) {| r: ring t |} (x y z: t)
  : Lemma (requires y+x=z+x) (ensures y=z) = group_cancelation_right x y z

let ring_zero_is_right_absorber (#t:Type) {| r: ring t |} (x:t)
  : Lemma (x * zero = zero) = 
  let (l,o): t&t = one, zero in
  elim_equatable_laws t;
  left_distributivity x o l; 
  left_add_identity l;
  right_mul_identity x;
  mul_congruence x (o+l) x l;
  add_congruence (x*o) (x*l) (x*o) x;
  trans_lemma [ x; (x*l); (x*(o+l)); (x*o+x*l); (x*o+x) ];
  add_congruence x (-x) (x*o + x) (-x);
  negation x;
  add_associativity (x*o) x (-x);
  add_congruence (x*o) (x + -x) (x*o) o;
  right_add_identity (x*o);
  trans_lemma [ o; (x + -x); (x*o + x + -x); (x*o + (x + -x)); (x*o + o); (x*o) ]
 
let ring_zero_is_left_absorber (#t:Type) {| r: ring t |} (x:t)
  : Lemma (zero * x = zero) = 
  let (l,o): t&t = one, zero in
  elim_equatable_laws t;
  right_distributivity o l x;
  left_mul_identity x;
  left_add_identity l;
  mul_congruence l x (o+l) x;
  add_congruence (o*x) (l*x) (o*x) x;
  trans_lemma [ x; (l*x); ((o+l)*x); (o*x+l*x); (o*x+x) ];
  add_congruence x (-x) (o*x+x) (-x);
  negation x;
  add_associativity (o*x) x (-x);
  add_congruence (o*x) (x + -x) (o*x) o;
  right_add_identity (o*x);
  trans_lemma [ o; (x + -x); (o*x + x + -x); (o*x + (x + -x)); (o*x + o); (o*x) ]
 
let ring_zero_is_absorber (#t:Type) {| r: ring t |} (x:t)
  : Lemma (zero * x = zero /\ x * zero = zero) = 
  ring_zero_is_left_absorber x;
  ring_zero_is_right_absorber x


let ring_neg_x_is_minus_one_times_x (#t:Type) {| r: ring t |} (x:t) 
  : Lemma (-x = (-one)*x) = 
  let (l, o) : t&t = one, zero in
  elim_equatable_laws t; //symmetry and reflexivity
  transitivity_for_calc_proofs t; // forall-based transitivity for calc to work
  calc (=) {
    o; = { ring_zero_is_left_absorber x }
    o*x; = { negation l; mul_congruence o x (l + -l) x }
    (l + -l)*x; = { right_distributivity l (-l) x }
    l*x + (-l)*x; = { left_mul_identity x; add_congruence (l*x) ((-l)*x) x ((-l)*x) }
    x + (-l)*x;
  };
  add_congruence (-x) o (-x) (x + (-l)*x);
  calc (=) {
    -x; = { right_add_identity (-x) }
    -x+o; = {}
    -x + (x + (-l)*x); = { add_associativity (-x) x ((-l)*x) }
    -x + x + ((-l)*x); = { negation x; add_congruence (-x+x) ((-l)*x) o ((-l)*x) }
    o + (-l)*x; = { left_add_identity ((-l)*x) }
    (-l)*x;
  }
 
private let alternative_above_lemma (#t:Type) {| r: ring t |} (x:t)
  : Lemma (-x = (-one)*x) = 
  let (l, o) : t&t = one, zero in 
  elim_equatable_laws t;
  ring_zero_is_absorber x;
  negation l;
  right_distributivity l (-l) x;
  left_mul_identity x;
  add_congruence (l*x) ((-l)*x) x ((-l)*x);
  mul_congruence o x (l + -l) x;
  trans_lemma [ o; 
                (o*x); 
                ((l + -l)*x); 
                (l*x + (-l)*x); 
                (x + (-l)*x) ];
  add_congruence (-x) o (-x) (x + (-l)*x);
  right_add_identity (-x);
  add_associativity (-x) x ((-l)*x);
  negation x;
  add_congruence (-x + x) ((-l)*x) o ((-l)*x);
  left_add_identity ((-l)*x);
  trans_lemma [ (-x); 
                (-x+o); 
                (-x + (x + (-l)*x)); 
                (-x + x + (-l)*x); 
                (o + (-l)*x); 
                ((-l)*x) ]
 
let ring_neg_x_is_x_times_minus_one (#t:Type) {| r: ring t |} (x:t) 
  : Lemma (-x = x*(-one)) = 
  let (l, o) : t&t = one, zero in
  elim_equatable_laws t; //symmetry and reflexivity
  transitivity_for_calc_proofs t; // forall-based transitivity for calc to work
  calc (=) {
    o; = { ring_zero_is_right_absorber x }
    x*o; = { negation l; mul_congruence x o x (l + -l) }
    x*(l + -l); = { left_distributivity x l (-l) }
    x*l + x*(-l); = { right_mul_identity x; add_congruence (x*l) (x*(-l)) x (x*(-l)) }
    x + x*(-l);
  };
  add_congruence (-x) o (-x) (x + x*(-l));
  calc (=) {
    -x; = { right_add_identity (-x) }
    -x+o; = {}
    -x + (x + x*(-l)); = { add_associativity (-x) x (x*(-l)) }
    -x + x + (x*(-l)); = { negation x; add_congruence (-x+x) (x*(-l)) o (x*(-l)) }
    o + x*(-l); = { left_add_identity (x*(-l)) }
    x*(-l);
  }
  
let ring_neg_one_commutes_with_everything #t {| r: ring t |} (x:t)
  : Lemma (x*(-one) = (-one)*x) = 
  ring_neg_x_is_x_times_minus_one x;
  symmetry (-x) (x*(-one));
  ring_neg_x_is_minus_one_times_x x;
  transitivity (x*(-one)) (-x) ((-one)*x)

let ring_neg_xy_is_x_times_neg_y #t {| r: ring t |} (x y: t)
  : Lemma (-(x*y) = x*(-y)) =  
  transitivity_for_calc_proofs t;
  elim_equatable_laws t;
  calc (=) {
    -(x*y); = { ring_neg_x_is_x_times_minus_one (x*y) }
    x*y*(-one); = { mul_associativity x y (-one) }
    x*(y*(-one)); = { ring_neg_x_is_x_times_minus_one y; 
                      mul_congruence x (y*(-one)) x (-y) }
    x*(-y);
  }

let ring_neg_xy_is_neg_x_times_y #t {| r: ring t |} (x y: t)
  : Lemma (-(x*y) = (-x)*y) = 
  transitivity_for_calc_proofs t;
  elim_equatable_laws t;
  calc (=) {
    -(x*y); = { ring_neg_x_is_minus_one_times_x (x*y) }
    (-one)*(x*y); = { mul_associativity (-one) x y }
    ((-one)*x)*y; = { ring_neg_x_is_minus_one_times_x x; 
                      mul_congruence ((-one)*x) y (-x) y }
    (-x)*y;
  }

let ring_neg_flip_in_product #t {| r: ring t |} (x y: t)
  : Lemma ((-x)*y = x*(-y)) = 
  elim_equatable_laws t;
  transitivity_for_calc_proofs t;
  ring_neg_xy_is_neg_x_times_y x y;
  ring_neg_xy_is_x_times_neg_y x y 

let ring_neg_left_distributivity #t {| r: ring t |} (x y z: t)
  : Lemma (x*(y + -z) = x*y + -(x*z)) = 
  elim_equatable_laws t;
  transitivity_for_calc_proofs t;
  left_distributivity x y (-z);
  ring_neg_xy_is_x_times_neg_y x z; 
  add_congruence (x*y) (x*(-z)) (x*y) (-(x*z))

let elim_ring_eq_laws #t (r: ring t) : squash (
  (forall (x:t). x=x) /\
  (forall (x y:t). (x=y) == (y=x))
) = elim_equatable_laws t #TC.solve

let elim_ring_trans #t (r: ring t) : Lemma (forall (x y z: t). x=y /\ y=z ==> x=z)
  = 
  let eq : equatable t = TC.solve in
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity)

let ring_neg_right_distributivity #t {| r: ring t |} (x y z: t)
  : Lemma ((x + -y) * z = x*z + -(y*z)) =
  elim_equatable_laws t;
  transitivity_for_calc_proofs t;   
  right_distributivity x (-y) z;
  ring_neg_xy_is_neg_x_times_y y z; 
  add_congruence (x*z) ((-y)*z) (x*z) (-(y*z)) 


class zero_ne_one_semiring (t:Type) = {
  [@@@TC.no_method] semiring: semiring t;
  zero_is_not_one: squash (semiring.add_comm_monoid.add_monoid.has_zero.zero <> semiring.mul_monoid.has_one.one);
}

instance semiring_of_zero_ne_one (t:Type) {| r: zero_ne_one_semiring t |} = r.semiring

class domain (t:Type) = {
  [@@@TC.no_method] ring: ring t;
  [@@@TC.no_method] zero_ne_one_semiring: zero_ne_one_semiring t;
  [@@@TC.no_method] consistency: squash (ring.semiring == zero_ne_one_semiring.semiring);  
  domain_law: (x:t -> y:t -> Lemma (requires x*y = zero) (ensures (x=zero) || (y=zero)))
}

instance ring_of_domain (t:Type) {| d: domain t |} = d.ring
instance zero_ne_one_semiring_of_domain (t:Type) {| d: domain t |} = d.zero_ne_one_semiring

let semiring_nonzero_product_means_nonzero_factors #t {| r: semiring t |} (x y:t)
  : Lemma (requires x*y <> zero) (ensures x <> zero /\ y <> zero) = 
  elim_equatable_laws t; 
  transitivity_for_calc_proofs t;
  if x=zero then (left_absorption y; mul_congruence x y zero y);  
  if y=zero then (right_absorption x; mul_congruence x y x zero)

let domain_nonzero_factors_means_nonzero_product #t {| d: domain t |} (x y: t)
  : Lemma (requires (x<>zero) /\ (y<>zero)) (ensures x*y <> zero) 
  = Classical.move_requires_2 domain_law x y

let domain_pq_eq_pr_lemma #t {| d: domain t |} (p q r: t) 
  : Lemma (requires p*q = p*r) (ensures (p=zero) \/ (q=r)) = 
  elim_equatable_laws t;
  transitivity_for_calc_proofs t;
  add_congruence (p*q) (-(p*r)) (p*r) (-(p*r));
  negation (p*r);
  ring_neg_xy_is_x_times_neg_y p r;
  add_congruence (p*q) (-(p*r)) (p*q) (p*(-r));
  ring_neg_left_distributivity p q r;
  domain_law p (q + -r);
  equality_is_zero_sum q r

class commutative_ring (t:Type) = {
  [@@@TC.no_method] ring: ring t;
  [@@@TC.no_method] mul_comm_monoid: mul_comm_monoid t;
  [@@@TC.no_method] consistency: squash (ring.semiring.mul_monoid == mul_comm_monoid.mul_monoid)
}

instance ring_of_commutative_ring (t:Type) (r: commutative_ring t) = r.ring
instance mul_comm_monoid_of_comm_ring (t:Type) (r: commutative_ring t) = r.mul_comm_monoid

let nat_norm (t:Type) = t -> option nat

#push-options "--z3rlimit 1 --ifuel 0 --fuel 0"
#restart-solver
let test_nf #t (nf: nat_norm t) (z:t) (x:t)
  = ((x==z) <==> ((nf x) == None))
#pop-options

let make_trivial_eq_instance #t (eq: t->t->bool)
  : Pure (equatable t)
         (requires (forall x. eq x x) /\
                   (forall x y. eq x y <==> eq y x) /\
                   (forall x y z. (eq x y /\ eq y z) ==> eq x z))
         (ensures fun _ -> True) = 
  { eq = eq; reflexivity = (fun _ -> ()); symmetry = (fun _ _ -> ()); transitivity = (fun _ _ _ -> ()) }

// This one speeds up nat_norm_property below tremendously.
instance option_nat_eq : equatable (option nat) = make_trivial_eq_instance op_Equality
  
let nat_norm_property (#t:Type) {| r: ring t |} (nf: nat_norm t) (x:t) 
  = (x = zero) <==> ((nf x) = None)

// This one is redundant, but if I comment this, the following 
// definitions will be really slow to verify.
instance eq_of_mul_monoid #t (m: mul_monoid t) = m.mul_semigroup.has_mul.eq

let is_unit #t {| h: mul_monoid t |} (x:t) = exists (x':t). x' * x = one

let is_divisor_of #t {| h: mul_monoid t |} (divisor dividend: t) 
  = exists (quotient: t). quotient * divisor = dividend

let are_associates #t {| h: mul_monoid t |} (p q: t)
  = is_divisor_of p q /\ is_divisor_of q p

let is_irreducible #t {| h: mul_monoid t |} (x:t) = 
  (~(is_unit x)) /\
  (forall (p q:t). ((q*p = x) ==> ((are_associates p x /\ is_unit q) \/
                             (are_associates q x /\ is_unit p))))

let is_prime #t {| h: mul_monoid t |} (p:t) = 
  (~(is_unit p)) /\ (forall (m n:t). (is_divisor_of p (m*n) ==>
                                (is_divisor_of p m \/ is_divisor_of p n)))

type units_of t {| h: mul_monoid t |} = x:t{is_unit x}

// fstar-mode isn't happy with the definition, but fstar is somehow...
let unit_product_is_unit #t {| h: mul_monoid t |} (x y: units_of t)
  : Lemma (is_unit #t (x*y)) =
  let x:t = x in
  let y:t = y in
// uncommenting these two  makes verification a lot faster 
  let ( * ) = h.mul_semigroup.has_mul.mul in
  let ( = ) = h.mul_semigroup.has_mul.eq.eq in
// But even with these two, fstar takes several seconds longer than it should...
  eliminate exists (x' y':t). (x'*x=one /\ y'*y=one)
    returns is_unit (x*y) with _.  
    begin 
      elim_equatable_laws t;
      transitivity_for_calc_proofs t;
      calc (=) {
        (y'*x')*(x*y); = { mul_associativity y' x' (x*y) }
        y' * (x' * (x*y)); = { mul_associativity x' x y; 
                               mul_congruence y' (x'*(x*y)) y' ((x'*x)*y) }
        y' * ((x'*x)*y); = { mul_congruence (x'*x) y one y;
                             mul_congruence y' ((x'*x)*y) y' (one*y);
                             left_mul_identity y;
                             mul_congruence y' (one*y) y' y }
        one;
      }
    end
