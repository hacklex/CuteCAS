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
  [@@@TC.no_method] semiring: semiring t;
  [@@@TC.no_method] add_comm_group_consistency: squash (semiring.add_comm_monoid == add_comm_group.add_comm_monoid);
}

instance add_comm_group_of_ring (t:Type) {| r: ring t |} = r.add_comm_group 
instance semiring_of_ring (t:Type) {| r: ring t |} = r.semiring

let ring_add_left_cancellation (#t:Type) {| r: ring t |} (x y z: t)
  : Lemma (requires x+y=x+z) (ensures y=z) = group_cancelation_left x y z
  
let ring_add_right_cancellation (#t:Type) {| r: ring t |} (x y z: t)
  : Lemma (requires y+x=z+x) (ensures y=z) = group_cancelation_right x y z

open FStar.List.Tot.Base

let rec trans_condition (#t:Type) {| equatable t |} (l: list t{length l > 1})
  : bool
  = match l with
  | h1::tail -> match tail with  
    | h2::Nil -> h1=h2
    | h2::t2 -> h1=h2 && trans_condition tail

let rec trans_lemma (#t:Type) {| equatable t |} (expressions: list t{length expressions > 1})
  : Lemma (requires trans_condition expressions)
          (ensures hd expressions = last expressions) = 
  match expressions with
  | h1::h2::Nil -> ()
  | h1::h2::t2 -> trans_lemma (h2::t2);
               transitivity h1 h2 (last t2)
 
let mul_associativity #t {| sg: mul_semigroup t |} : associativity_lemma ( * ) = sg.associativity 
let add_associativity #t {| sg: add_semigroup t |} : associativity_lemma ( + ) = sg.associativity
let mul_congruence #t {| hm: has_mul t |} : congruence_lemma ( * ) = hm.congruence 
let add_congruence #t {| ha: has_add t |} : congruence_lemma ( + ) = ha.congruence 

let elim_equatable_laws (#t:Type) (r: ring t)
  : Lemma ((forall (x:t). x=x) /\ (forall (x y: t). x=y <==> y=x)) = 
  Classical.forall_intro (reflexivity #t);
  Classical.forall_intro_2 (Classical.move_requires_2 (symmetry #t))

let ring_zero_is_right_absorber (#t:Type) {| r: ring t |} (x:t)
  : Lemma (x * zero = zero) = 
  let (l,o): t&t = one, zero in
  elim_equatable_laws r;
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
  elim_equatable_laws r;
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

let transitivity_for_calc_proofs (#t:Type) (r: ring t)
  : Lemma (forall (x y z:t). x=y /\ y=z ==> x=z) = 
  Classical.forall_intro_3 (Classical.move_requires_3 (transitivity #t))

let ring_neg_x_is_minus_one_times_x (#t:Type) {| r: ring t |} (x:t) 
  : Lemma (-x = (-one)*x) = 
  let (l, o) : t&t = one, zero in
  elim_equatable_laws r;
  transitivity_for_calc_proofs r;
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
   
let aux_neg (#t:Type) {| r: ring t |} (x:t)
  : Lemma (-x = (-one)*x) = 
  let (l, o) : t&t = one, zero in 
  elim_equatable_laws r;
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
  
let ring_neg_one_commutes_with_everything #t {| r: ring t |} (x:t)
  : Lemma (x*(-one) = (-one)*x) = 
  let one: t = one in
  let rr : semiring t = r.semiring in
  let ha : has_add t = TC.solve in
  let asg: add_semigroup t = TC.solve in
  let hm : has_mul t = TC.solve in 
  left_distributivity x (-one) one;
  negation one;
  negation x;
  reflexivity x;
  reflexivity (-x);
  hm.congruence x (-one + one) x zero;
  right_absorption x;
  symmetry (x*zero) zero;
  symmetry (x*(-one + one)) (x*zero);
  transitivity zero (x*zero) (x*(-one+one));
  transitivity (x*(-one + one)) (x*zero) zero;
  right_mul_identity x;
  reflexivity (x*(-one));
  ha.congruence (x*(-one)) (x*one) (x*(-one)) x;
  transitivity zero (x*(-one + one)) (x*(-one) + x*one);
  transitivity zero (x*(-one) + x*one) (x*(-one) + x);
  ha.congruence zero (-x) (x*(-one)+x) (-x);
  left_add_identity (-x);
  symmetry (zero + -x) (-x);
  transitivity (-x) (zero + -x) (x*(-one) + x + -x);
  asg.associativity (x*(-one)) x (-x);
  transitivity (-x) (x*(-one) + x + -x) (x*(-one) + (x + -x));
  ha.congruence (x*(-one)) (x + -x) (x*(-one)) zero;
  transitivity (-x) (x*(-one) + (x + -x)) (x*(-one) + zero);
  right_add_identity (x*(-one));
  transitivity (-x) (x*(-one) + zero) (x*(-one));
  symmetry (-x) (x*(-one));
  ring_neg_x_is_minus_one_times_x x;
  transitivity (x*(-one)) (-x) ((-one)*x) 
 
let ring_neg_xy_is_x_times_neg_y #t {| r: ring t |} (x y: t)
  : Lemma (-(x*y) = x*(-y)) =  
  ring_neg_x_is_minus_one_times_x y;
  reflexivity x;
  reflexivity y;
  mul_congruence x (-y) x ((-one)*y);
  mul_associativity x (-one) y;
  symmetry (x * (-one) * y) (x * ((-one) * y));
  ring_neg_one_commutes_with_everything x;
  mul_congruence (x * (-one)) y ((-one)*x) y;
  mul_associativity (-one) x y;
  transitivity (x * (-one) * y) ((-one) * x * y) ((-one) * (x * y));
  ring_neg_x_is_minus_one_times_x (x*y);
  symmetry (-(x*y)) ((-one)*(x*y));
  trans_lemma [ (x*(-y)); (x * ((-one)*y)); (x * (-one) * y);  ((-one) * (x*y)); (-(x*y)) ];
  symmetry (x*(-y)) (-(x*y)) 
