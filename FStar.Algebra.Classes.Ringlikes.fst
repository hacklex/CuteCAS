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

instance add_cm_of_semiring (t:Type) {| r: semiring t |} = r.add_comm_monoid
instance mul_m_of_semiring (t:Type) {| r: semiring t |} = r.mul_monoid

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
  [@@@TC.no_method] semiring: (r:semiring t { r.add_comm_monoid == add_comm_group.add_comm_monoid });
}

instance add_monoid_of_semiring (t:Type) {| r: semiring t |} = r.add_comm_monoid.add_monoid

instance add_comm_group_of_ring (t:Type) {| r: ring t |} = r.add_comm_group 


instance mul_of_ring (t:Type) {| r: ring t |} = r.semiring.mul_monoid
instance equatable_of_semiring (t:Type) {| r: semiring t |} = r.mul_monoid.mul_semigroup.has_mul.eq

instance has_neg_of_ring (t:Type) {| r: ring t |} = r.add_comm_group.add_group.has_neg

instance semiring_of_ring (t:Type) {| r: ring t |} = r.semiring


let ring_add_left_cancellation (#t:Type) {| r: ring t |} (x y z: t)
  : Lemma (requires x+y=x+z) (ensures y=z) = group_cancelation_left x y z
  
let ring_add_right_cancellation (#t:Type) {| r: ring t |} (x y z: t)
  : Lemma (requires y+x=z+x) (ensures y=z) = group_cancelation_right x y z

let ring_zero_is_absorber (#t:Type) {| r: ring t |} (x:t)
  : Lemma (zero * x = zero /\ x * zero = zero) = 
  let one: t = one in
  let rr : semiring t = r.semiring in
  let ha : has_add t = TC.solve in
  let asg: add_semigroup t = TC.solve in
  let hm : has_mul t = TC.solve in 
  left_add_identity one; 
  left_distributivity x zero one;
  symmetry (x*(zero+one)) (x*zero + x*one); 
  reflexivity (x*zero);
  reflexivity x;
  reflexivity (-(x*one));
  right_mul_identity x;
  ha.congruence (x*zero) (x*one) (x*zero) x;
  hm.congruence x (zero+one) x one;
  transitivity (x*zero + x*one) (x*(zero+one)) (x*one);
  ha.congruence (x*zero + x*one) (-(x*one)) (x*one) (-(x*one)); 
  negation (x*one); 
  asg.associativity (x*zero) (x*one) (-(x*one)); 
  ha.congruence (x*zero) (x*one + -(x*one)) (x*zero) zero;
  transitivity (x*zero+x*one + -(x*one)) (x*zero+(x*one + -(x*one))) (x*zero + zero);
  right_add_identity (x*zero); 
  transitivity (x*zero + x*one + -(x*one)) (x*zero + zero) (x*zero);
  symmetry (x*zero + x*one + -(x*one)) (x*zero);
  transitivity (x*zero) (x*zero + x*one + -(x*one)) (x*one + -(x*one));
  transitivity (x*zero) (x*one + -(x*one)) zero; 

  right_distributivity zero one x; 
  hm.congruence (zero+one) x one x;
  left_mul_identity x;
  transitivity ((zero+one)*x) (one*x) x;
  symmetry ((zero+one)*x) x;
  transitivity x ((zero+one)*x) (zero*x+one*x);
  reflexivity (zero*x);
  ha.congruence (zero*x) (one*x) (zero*x) x;
  transitivity x (zero*x+one*x) (zero*x + x);
  reflexivity (-x);
  ha.congruence x (-x) (zero*x+x) (-x); 
  symmetry (x + -x) (zero*x + x + -x);
  negation x; 
  symmetry (x + -x) zero;
  transitivity zero (x + -x) (zero*x + x + -x);
  asg.associativity (zero*x) x (-x);
  ha.congruence (zero*x) (x + -x) (zero*x) zero;
  transitivity (zero*x + x + -x) (zero*x + (x + -x)) (zero*x + zero);
  right_add_identity (zero*x);
  transitivity (zero*x + x + -x) (zero*x + zero) (zero*x);
  transitivity zero (zero*x + x + -x) (zero*x);
  symmetry zero (zero*x); 
()

let double_negation_lemma (#t:Type) {| g: add_group t |} (x:t) 
  : Lemma (-(-x) = x) = 
  let ha : has_add t = TC.solve in
  let sg : add_semigroup t =  TC.solve in
  negation (-x);
  reflexivity x;
  ha.congruence (-(-x) + -x) x zero x;
  left_add_identity x;
  sg.associativity (-(-x)) (-x) x;
  negation x;
  reflexivity (-(-x));
  ha.congruence (-(-x)) (-x + x) (-(-x)) zero;
  symmetry (-(-x)+(-x+x)) (-(-x)+zero);
  right_add_identity (-(-x));
  symmetry (-(-x) + zero) (-(-x));
  transitivity (-(-x)) (-(-x)+zero) (-(-x) + (-x+x));
  symmetry (-(-x) + (-x) + x) (-(-x) + (-x + x));
  transitivity (-(-x)) (-(-x) + (-x+x)) (-(-x) + (-x) + x);
  transitivity (-(-x)) (-(-x) + (-x) + x) (zero + x);
  transitivity (-(-x)) (zero + x) x

let equal_elements_have_equal_inverses (#t:Type) {| g: add_group t |} (x y:t)
  : Lemma (requires x=y) (ensures -x = -y) = 
  let ha : has_add t = TC.solve in
  let sg : add_semigroup t =  TC.solve in
  negation x; negation y;
  reflexivity (-x);
  reflexivity (-y);
  ha.congruence x (-x) y (-x);
  ha.congruence (-y) (x + -x) (-y) (y + -x);
  ha.congruence (-y) (x + -x) (-y) zero;
  right_add_identity (-y);
  transitivity (-y + (x + -x)) (-y + zero) (-y);
  symmetry (-y + (x + -x)) (-y);
  sg.associativity (-y) y (-x);
  symmetry (-y + y + -x) (-y + (y + -x));
  transitivity (-y) (-y + (x + -x)) (-y + (y + -x));
  transitivity (-y) (-y + (y + -x)) (-y + y + -x);
  ha.congruence (-y+y) (-x) zero (-x);
  left_add_identity (-x);
  transitivity (-y + y + -x) (zero + -x) (-x);
  transitivity (-y) (-y + y + -x) (-x);
  symmetry (-y) (-x)
  
