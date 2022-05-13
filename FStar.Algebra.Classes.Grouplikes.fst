module FStar.Algebra.Classes.Grouplikes

module TC=FStar.Tactics.Typeclasses

open FStar.Algebra.Classes.Equatable


type associativity_lemma (#t:Type) {| equatable t |} (op: t->t->t) = 
  x:t -> y:t -> z:t -> Lemma (op (op x y) z = op x (op y z))

type commutativity_lemma (#t:Type) {| equatable t |} (op: t->t->t) = 
  x:t -> y:t -> Lemma (op x y = op y x)

type congruence_lemma (#t:Type) {| equatable t |} (op: t->t->t) = 
  x:t -> y:t -> z:t -> w:t -> Lemma (requires x=z /\ y=w) (ensures op x y = op z w)
   
type left_identity_lemma #t {| equatable t |} (op: t->t->t) (zero: t) = 
  x:t -> Lemma (op zero x = x)
  
type right_identity_lemma #t {| equatable t |} (op: t->t->t) (zero: t) = 
  x:t -> Lemma (op x zero = x)
 
type left_absorber_lemma #t {| equatable t |} (op: t->t->t) (zero: t) = 
  x:t -> Lemma (op zero x = zero)
  
type right_absorber_lemma #t {| equatable t |} (op: t->t->t) (zero: t) = 
  x:t -> Lemma (op x zero = zero)

type inversion_lemma #t {| equatable t |} (op: t->t->t) (zero:t) (inv: t->t) = 
  x:t -> Lemma (op x (inv x) = zero /\ op (inv x) x = zero)
 
class has_mul (t:Type) = { 
  mul : t -> t -> t;
  [@@@TC.no_method] eq: equatable t;
  [@@@TC.no_method] congruence: congruence_lemma mul;
} 

instance eq_of_mul (t:Type) {| h: has_mul t |} : equatable t = h.eq 

let ( * ) (#t:Type) {|m: has_mul t|} = m.mul

class has_add (t:Type) = {  
  add : t -> t -> t;
  [@@@TC.no_method] eq: equatable t;
  [@@@TC.no_method] congruence: congruence_lemma add;
} 

instance eq_of_add (t:Type) {| h: has_add t |} : equatable t = h.eq 
 
let ( + ) (#t:Type) {|a: has_add t|} = a.add

instance int_equatable : equatable int = {
  eq = op_Equality;
  reflexivity = (fun _ -> ());
  symmetry = (fun _ _ -> ());
  transitivity = (fun _ _ _ -> ());
} 

class mul_semigroup (t:Type) = {  
  [@@@TC.no_method] has_mul : has_mul t; 
  [@@@TC.no_method] associativity: associativity_lemma has_mul.mul;
}
instance has_mul_of_sg (t:Type) {| h: mul_semigroup t |} = h.has_mul

class add_semigroup (t:Type) = {
  [@@@TC.no_method] has_add : has_add t; 
  [@@@TC.no_method] associativity: associativity_lemma has_add.add;
}

instance has_add_of_sg (t:Type) {| h: add_semigroup t |} = h.has_add
 
class has_zero (t:Type) = { zero: t }

class add_monoid (t:Type) = {
  [@@@TC.no_method] add_semigroup: add_semigroup t;
  [@@@TC.no_method] has_zero: has_zero t;
  left_add_identity : left_identity_lemma add_semigroup.has_add.add zero;
  right_add_identity : right_identity_lemma add_semigroup.has_add.add zero;
}

instance sg_of_add_monoid (t:Type) {| h: add_monoid t |} = h.add_semigroup
instance has_zero_of_monoid (t:Type) {| h: add_monoid t |} = h.has_zero

class has_one (t:Type) = { one: t }

class mul_monoid (t:Type) = {
  [@@@TC.no_method] mul_semigroup: mul_semigroup t;
  [@@@TC.no_method] has_one: has_one t;
  left_mul_identity : left_identity_lemma mul_semigroup.has_mul.mul one;
  right_mul_identity : right_identity_lemma mul_semigroup.has_mul.mul one;
}

instance sg_of_mul_monoid (t:Type) {| h: mul_monoid t |} = h.mul_semigroup
instance has_one_of_monoid (t:Type) {| h: mul_monoid t |} = h.has_one

class add_comm_magma (t:Type) = {
  [@@@TC.no_method] has_add : has_add t;
  add_commutativity: commutativity_lemma has_add.add; 
}
class mul_comm_magma (t:Type) = {
  [@@@TC.no_method] has_mul : has_mul t;
  mul_commutativity: commutativity_lemma has_mul.mul; 
}

instance has_add_of_comm_magma (t:Type) {| m: add_comm_magma t |} = m.has_add
instance has_mul_of_comm_magma (t:Type) {| m: mul_comm_magma t |} = m.has_mul

class add_comm_semigroup (t:Type) = {
  [@@@TC.no_method] add_semigroup: add_semigroup t;
  [@@@TC.no_method] add_comm_magma : add_comm_magma t;
  [@@@TC.no_method] consistency : squash (add_semigroup.has_add == add_comm_magma.has_add);  
}

instance sg_of_add_comm_semigroup (t:Type) {| h: add_comm_semigroup t |} = h.add_semigroup
instance add_comm_magma_of_comm_sg (t:Type) {| h: add_comm_semigroup t |} = h.add_comm_magma

class mul_comm_semigroup (t:Type) = {
  [@@@TC.no_method] mul_semigroup: mul_semigroup t;
  [@@@TC.no_method] mul_comm_magma : mul_comm_magma t;
  [@@@TC.no_method] consistency : squash (mul_semigroup.has_mul == mul_comm_magma.has_mul);
}

instance sg_of_mul_comm_semigroup (t:Type) {| h: mul_comm_semigroup t |} = h.mul_semigroup
instance mul_comm_magma_of_comm_sg (t:Type) {| h: mul_comm_semigroup t |} = h.mul_comm_magma
 
class add_comm_monoid (t:Type) = {
  [@@@TC.no_method] add_monoid: add_monoid t;
  [@@@TC.no_method] add_comm_semigroup: add_comm_semigroup t;
  [@@@TC.no_method] consistency : squash (add_monoid.add_semigroup == add_comm_semigroup.add_semigroup);
}
 
instance add_monoid_of_comm_monoid (t:Type) {| h: add_comm_monoid t |} = h.add_monoid
instance add_comm_sg_of_comm_monoid (t:Type) {| h: add_comm_monoid t |} = h.add_comm_semigroup
 
class mul_comm_monoid (t:Type) = {
  [@@@TC.no_method] mul_monoid: mul_monoid t;
  [@@@TC.no_method] mul_comm_semigroup: mul_comm_semigroup t;
  [@@@TC.no_method] consistency : squash (mul_monoid.mul_semigroup == mul_comm_semigroup.mul_semigroup);
}
 
instance mul_monoid_of_comm_monoid (t:Type) {| h: mul_comm_monoid t |} = h.mul_monoid
instance mul_comm_sg_of_comm_monoid (t:Type) {| h: mul_comm_monoid t |} = h.mul_comm_semigroup

class has_neg (t:Type) = {
  neg: t -> t
}

private let old_int_minus = op_Minus

let op_Minus (#t:Type) {| h: has_neg t |} = h.neg

private let old_int_sub = op_Subtraction
 
class has_sub (t:Type) = {
  sub: t -> t -> t
}

let op_Subtraction (#t:Type) {| h: has_sub t |} = h.sub

instance int_sub : has_sub int = { sub = old_int_sub }
instance int_neg : has_neg int = { neg = old_int_minus }

class add_group (t:Type) = {
  [@@@TC.no_method] add_monoid: add_monoid t;
  [@@@TC.no_method] has_neg: has_neg t;
  [@@@TC.no_method] has_sub: has_sub t;
  subtraction_definition : (x:t -> y:t -> Lemma ((x - y) = (x + (-y))));
  negation: inversion_lemma add_monoid.add_semigroup.has_add.add zero neg;
}

class add_comm_group (t:Type) = {
  [@@@TC.no_method] add_group: add_group t;
  [@@@TC.no_method] add_comm_monoid: add_comm_monoid t;
  [@@@TC.no_method] consistence : squash (add_group.add_monoid == add_comm_monoid.add_monoid);
}

instance add_monoid_of_group (t:Type) {| h: add_group t |} = h.add_monoid
instance neg_of_add_group (t:Type) {| h: add_group t |} = h.has_neg
instance sub_of_add_group (t:Type) {| h: add_group t |} = h.has_sub

instance add_group_of_comm_group (t:Type) {| h: add_comm_group t |} = h.add_group
instance add_comm_monoid_of_comm_group (t:Type) {| h: add_comm_group t |} = h.add_comm_monoid

 
let group_cancelation_left (#t:Type) {| g: add_group t |} (x y z: t)
  : Lemma (requires (x+y)=(x+z)) (ensures y=z) = 
  let ha : has_add t = TC.solve in
  let he : equatable t = TC.solve in
  let sg : add_semigroup t = TC.solve in 
  he.reflexivity (-x);
  ha.congruence (-x) (x+y) (-x) (x+z);
  Classical.forall_intro_3 (Classical.move_requires_3 he.transitivity);
  let aux (p: t) : Lemma ((-x)+(x+p) = p) =
    calc (=) {
      (-x)+(x+p); = { sg.associativity (-x) x p; he.symmetry ((-x)+x+p) ((-x)+(x+p)) }
      ((-x)+x)+p; = { negation x; he.reflexivity p; ha.congruence ((-x)+x) p zero p }
      zero+p; = { left_add_identity p }
      p;
    } in
  aux y; aux z;
  he.symmetry ((-x)+(x+y)) y

let group_cancelation_right (#t:Type) {| g: add_group t |} (x y z: t)
  : Lemma (requires (y+x)=(z+x)) (ensures y=z) = 
  let ha : has_add t = TC.solve in
  let he : equatable t = TC.solve in
  let sg : add_semigroup t = TC.solve in
  he.reflexivity (-x);
  ha.congruence (y+x) (-x) (z+x) (-x);
  Classical.forall_intro_3 (Classical.move_requires_3 he.transitivity);
  let aux (p: t) : Lemma ((p+x)+(-x) = p) =
    calc (=) {
      (p+x)+(-x); = { sg.associativity p x (-x) }
      p+(x+(-x)); = { negation x; he.reflexivity p; ha.congruence p (x+(-x)) p zero }
      p+zero; = { right_add_identity p }
      p;
    } in
  aux y; aux z;
  he.symmetry ((y+x)+(-x)) y 

let is_right_factor_of (#t:Type) {| m: has_mul t |} (product factor:t) = 
  exists c. c*factor = product

let is_left_factor_of (#t:Type) {| m: has_mul t |} (product factor:t) =
  exists c. factor*c = product

let is_factor_of (#t:Type) {| m: mul_comm_magma t |} (product factor: t) = 
  is_right_factor_of product factor \/ is_left_factor_of product factor

let left_factor_is_right_factor_if_commutative (#t:Type) 
                                               {| m: mul_comm_magma t |} 
                                               (product factor: t)
  : Lemma (is_left_factor_of product factor <==> is_right_factor_of product factor) =   
  let aux_1 () : Lemma (requires is_left_factor_of product factor) 
                       (ensures is_right_factor_of product factor) =                        
    eliminate exists c. (factor*c=product)
    returns is_right_factor_of product factor with _. 
    begin
      mul_commutativity factor c;
      symmetry (factor*c) (c*factor);
      transitivity (c*factor) (factor*c) product
    end in Classical.move_requires aux_1 ();
  let aux_2 () : Lemma (requires is_right_factor_of product factor) 
                       (ensures is_left_factor_of product factor) =                        
    eliminate exists c. (c*factor=product)
    returns is_left_factor_of product factor with _.  
    begin
      mul_commutativity c factor;
      symmetry (c*factor) (factor*c);
      transitivity (factor*c) (c*factor) product
    end in Classical.move_requires aux_2 ()  
