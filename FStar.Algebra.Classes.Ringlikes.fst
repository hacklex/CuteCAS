module FStar.Algebra.Classes.Ringlikes

module TC = FStar.Tactics.Typeclasses

open FStar.Algebra.Classes.Equatable
open FStar.Algebra.Classes.Grouplikes
 
type left_distributivity_lemma (#t:Type) {| equatable t |} (mul add: t->t->t)
  = x:t -> y:t -> z:t -> Lemma (mul x (add y z) = add (mul x y) (mul x z))

type right_distributivity_lemma (#t:Type) {| equatable t |} (mul add: t->t->t) 
  = x:t -> y:t -> z:t -> Lemma (mul (add x y) z = add (mul x z) (mul y z))

type valuation =
  | Value of nat
  | Nothing 
  
class semiring (t:Type) = {
  [@@@TC.no_method] add_comm_monoid: add_comm_monoid t;
  [@@@TC.no_method] mul_monoid: (z:mul_monoid t{ z.mul_semigroup.has_mul.eq == 
                                                 add_comm_monoid.add_monoid.add_semigroup.has_add.eq });  
  left_absorption      : left_absorber_lemma mul_monoid.mul_semigroup.has_mul.mul zero;
  right_absorption     : right_absorber_lemma mul_monoid.mul_semigroup.has_mul.mul zero;
  left_distributivity  : left_distributivity_lemma mul_monoid.mul_semigroup.has_mul.mul add_comm_monoid.add_monoid.add_semigroup.has_add.add;
  right_distributivity : right_distributivity_lemma mul_monoid.mul_semigroup.has_mul.mul 
                                                  add_comm_monoid.add_monoid.add_semigroup.has_add.add;
  
}

instance add_cm_of_semiring (t:Type) (r: semiring t) = r.add_comm_monoid
instance mul_m_of_semiring  (t:Type) (r: semiring t) = r.mul_monoid <: mul_monoid t
  
instance hm_r #t (r: semiring t) = r.mul_monoid.mul_semigroup.has_mul
instance ha_r #t (r: semiring t) = r.add_comm_monoid.add_monoid.add_semigroup.has_add
instance he_r #t (r: semiring t) = r.mul_monoid.mul_semigroup.has_mul.eq 

let absorption #t {| r: semiring t |} (z x:t)
  : Lemma (requires z=zero) (ensures (z*x = zero) /\ (x*z = zero)) = 
  let eq : equatable t = TC.solve in
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  Classical.forall_intro eq.reflexivity;
  mul_congruence z x zero x;
  mul_congruence x z x zero;
  left_absorption x;
  right_absorption x

let absorber_is_two_sided_from_lemmas #t {| r: semiring t |} (#z1 #z2: t)
  (z1_is_absorber: left_absorber_lemma  r.mul_monoid.mul_semigroup.has_mul.mul z1)
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
  [@@@TC.no_method] semiring: semiring t;
  [@@@TC.no_method] add_comm_group: (z:add_comm_group t{z.add_comm_monoid == semiring.add_comm_monoid});
}

instance add_comm_group_of_ring (t:Type) (r: ring t) = r.add_comm_group <: add_comm_group t
instance semiring_of_ring (t:Type) (r: ring t) = r.semiring

//instance hm_rr #t (r: ring t) = r.semiring.mul_monoid.mul_semigroup.has_mul
//instance ha_rr #t (r: ring t) = r.semiring.add_comm_monoid.add_monoid.add_semigroup.has_add

let ring_add_left_cancellation (#t:Type) {| r: ring t |} (x y z: t)
  : Lemma (requires x+y=x+z) (ensures y=z) = group_cancellation_left x y z
  
let ring_add_right_cancellation (#t:Type) {| r: ring t |} (x y z: t)
  : Lemma (requires y+x=z+x) (ensures y=z) = group_cancellation_right x y z

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
  [@@@TC.no_method] semiring: (r:semiring t{ zero <> r.mul_monoid.has_one.one });
}

instance semiring_of_zero_ne_one (t:Type) {| r: zero_ne_one_semiring t |} = r.semiring <: semiring t

class domain (t:Type) = {
  [@@@TC.no_method] ring: ring t;
  [@@@TC.no_method] zero_ne_one_semiring: r:zero_ne_one_semiring t{r.semiring == ring.semiring};
  domain_law: (x:t -> y:t -> Lemma (requires x*y = zero) (ensures (x=zero) || (y=zero)))
}
 
instance ring_of_domain (t:Type) {| d: domain t |} = d.ring
instance zero_ne_one_semiring_of_domain (t:Type) {| d: domain t |} = d.zero_ne_one_semiring <: zero_ne_one_semiring t

let left_cancellation #t {| d: domain t |} (x y z: t)
  : Lemma (requires (x*y = x*z) /\ (x<>zero)) (ensures y=z) = 
  let teq : equatable t = TC.solve in
  Classical.forall_intro teq.reflexivity;
  Classical.forall_intro_2 teq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 teq.transitivity);
  add_congruence (x*y) (-(x*z)) (x*z) (-(x*z));
  negation (x*z); 
  ring_neg_xy_is_x_times_neg_y x z; 
  left_distributivity x y (-z);
  add_congruence (x*y) (x*(-z)) (x*y) (-(x*z));
  trans_lemma [(x*(y + -z));
               (x*y + x*(-z));
               ((x*y) + -(x*z));
               (x*z + -(x*z));
               zero ];
  domain_law x (y + -z);
  add_congruence (y + -z) z zero z; 
  left_add_identity z; 
  calc (=) {
    z;            = { left_add_identity z }
    zero + z;     = { }    
    y + -z + z;   = { add_associativity y (-z) z }
    y + (-z + z); = { negation z; 
                      add_congruence y (-z + z) y zero;
                      right_add_identity y }
    y;
  }

let right_cancellation #t {| d: domain t |} (x y z: t)
  : Lemma (requires (y*x = z*x) /\ (x<>zero)) (ensures y=z) = 
  let teq : equatable t = TC.solve in
  Classical.forall_intro teq.reflexivity;
  Classical.forall_intro_2 teq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 teq.transitivity);
  add_congruence (y*x) (-(z*x)) (z*x) (-(z*x));
  negation (z*x); 
  ring_neg_xy_is_neg_x_times_y z x;
  right_distributivity y (-z) x;
  add_congruence (y*x) ((-z)*x) (y*x) (-(z*x));
  trans_lemma [((y + -z)*x);
               (y*x + (-z)*x);
               ((y*x) + -(z*x));
               (z*x + -(z*x));
               zero ];
  domain_law (y + -z) x;
  add_congruence (y + -z) z zero z; 
  left_add_identity z; 
  calc (=) {
    z;            = { left_add_identity z }
    zero + z;     = { }    
    y + -z + z;   = { add_associativity y (-z) z }
    y + (-z + z); = { negation z; 
                      add_congruence y (-z + z) y zero;
                      right_add_identity y }
    y;
  }


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
  [@@@TC.no_method] mul_comm_monoid: (m:mul_comm_monoid t{m.mul_monoid == ring.semiring.mul_monoid});
}

instance ring_of_commutative_ring (t:Type) (r: commutative_ring t) = r.ring
instance mul_comm_monoid_of_comm_ring (t:Type) (r: commutative_ring t) = r.mul_comm_monoid <: mul_comm_monoid t

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
        (y'*x')*(x*y);     = { mul_associativity y' x' (x*y) }
        y' * (x' * (x*y)); = { mul_associativity x' x y; 
                               mul_congruence y' (x'*(x*y)) y' ((x'*x)*y) }
        y' * ((x'*x)*y);   = { mul_congruence (x'*x) y one y;
                               mul_congruence y' ((x'*x)*y) y' (one*y);
                               left_mul_identity y;
                               mul_congruence y' (one*y) y' y }
        one;
      }
    end

class integral_domain (t:Type) = { 
  [@@@TC.no_method] commutative_ring: commutative_ring t;
  [@@@TC.no_method] domain: (d:domain t{d.ring == commutative_ring.ring});
}

instance comm_ring_of_id (t:Type) (id: integral_domain t) = id.commutative_ring
instance domain_of_id (t:Type) (id: integral_domain t) = id.domain <: domain t

class division_ring (t:Type) = {
  [@@@TC.no_method] domain: domain t; 
  inv: (x:t{x <> zero}) -> (x':t{(x' * x = one) /\ (x * x' = one)});   
}

instance domain_of_div_ring (t:Type) (dr: division_ring t) = dr.domain

class field (t:Type) = {
  [@@@TC.no_method] division_ring: division_ring t; 
  [@@@TC.no_method] commutative_ring: c:commutative_ring t{c.ring == division_ring.domain.ring};
} 

instance dr_of_field (t:Type) (f: field t) = f.division_ring
instance comm_ring_of_field (t:Type) (f: field t) = f.commutative_ring <: commutative_ring t



class left_module (vector: Type) 
                  (scalar: Type) 
                  (r: ring scalar) 
                  (cm: add_comm_group vector) = {
  s_mul_v: (x:scalar) -> (y: vector) -> vector;
  s_left_associativity: (x: scalar) -> (y: scalar) -> (z: vector) -> Lemma (s_mul_v x (s_mul_v y z) = s_mul_v (x*y) z); 
  s_left_distributivity: (x: scalar) -> (y: vector) -> (z: vector) -> Lemma (s_mul_v x (y + z) = s_mul_v x y + s_mul_v x z); 
}




class right_module (vector: Type) 
                  (scalar: Type) 
                  (r: ring scalar) 
                  (cm: add_comm_group vector) = {
  v_mul_s: (x:vector) -> (y: scalar) -> vector;
  right_associativity: (x: vector) -> (y: scalar) -> (z: scalar) -> Lemma (s_mul_v x (s_mul_v y z) = s_mul_v (x*y) z);
}


let survives_addition #t {|r:ring t|} (f: t->bool) = 
  forall (x y: (q:t{f q})). f (x + y) 

let survives_rmul #t {|r:ring t|} (f:t->bool) = 
  forall (x:t{f x}) (y:t). f (x*y)  

let survives_lmul #t {|r:ring t|} (f:t->bool) = 
  forall (x:t{f x}) (y:t). f (y*x)  
  
type left_ideal_func t {| r: ring t |} = 
  (f:(t -> bool) {
    survives_addition f /\ 
    survives_lmul f  
  })

type right_ideal_func t {| r: ring t |} = 
  (f:(t -> bool) {
    survives_addition f /\ 
    survives_rmul f  
  })

type ideal_func t {|r: ring t|} = (m:left_ideal_func t{survives_rmul m})

type ideal #t {|r:ring t|} (f:ideal_func t) = x:t{f x}

type left_ideal #t {|r:ring t|} (f:left_ideal_func t) = x:t{f x}
type right_ideal #t {|r:ring t|} (f:right_ideal_func t) = x:t{f x}
 
type principal_left_ideal #t {|r: ring t|} (x:t) = p:t{exists (q:t). q*x = p}
type principal_right_ideal #t {|r: ring t|} (x:t) = p:t{exists (q:t). x*q = p}
 
let eq_prop #t {| equatable t |} (x y:t) : prop = (x=y) == true

let principal_left_ideal_multiplier #t {|r:ring t|} (x:t) (p:principal_left_ideal x)
  : GTot(z:t{z*x = p}) = 
  let condition (z:t) : prop = ((z*x) `eq_prop` p) in 
  IndefiniteDescription.indefinite_description_ghost t condition

let principal_right_ideal_multiplier #t {|r:ring t|} (x:t) (p: principal_right_ideal x) 
  : GTot(z:t{x*z = p}) = 
  IndefiniteDescription.indefinite_description_ghost t (fun q -> (x*q) = p == true) 
 
open FStar.Squash
open FStar.Classical

let principal_left_ideal_func #t {|r:ring t|} (x:t) : GTot (left_ideal_func t) =   
  let test (p:t) : GTot(bool) = IndefiniteDescription.strong_excluded_middle (exists (q:t). x*q = p) in
  IndefiniteDescription.indefinite_description_ghost (left_ideal_func t)
    (fun f -> (forall (p:t). (f p <==> test p)))
 

    
(*
let principal_ideal_func #t {|r:ring t|} (x:t) : GTot (left_ideal_func t) =   
  let logical_condition p = exists q. (q*x) = p  in  
  let indicator_function_property (f: (t->bool)) = forall z. f z <==> logical_condition z in  
  let aux () : Lemma (exists (f:(t->bool)). indicator_function_property f) = 
    let f (z:t) : (fz:bool{fz <==> logical_condition z}) = 
      admit();
    false in 
//    admit(); //uncomment this and everything is fine again 0_0
    assert (indicator_function_property f);
  () in aux(); 
  assert (exists f. indicator_function_property f);
  let indicator =
    IndefiniteDescription.indefinite_description_ghost (t->bool) (fun f -> indicator_function_property f) in
  admit();
  indicator
    
*)
