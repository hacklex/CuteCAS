module FStar.Algebra.Classes.Multiplicative

module TC=FStar.Tactics.Typeclasses

open FStar.Algebra.Classes.Equatable

type heterogenous_congruence_lemma (#a #b #c: Type) 
                                   {| equatable a |} 
                                   {| equatable b |} 
                                   {| equatable c |} (op: a->b->c) =
  x:a -> y:b -> z:a -> w:b -> Lemma (requires x=z /\ y=w) (ensures op x y = op z w)
  
class mul_defined (a b c: Type) = {
  mul: a -> b -> c;
  [@@@TC.no_method] eq_a: equatable a;
  [@@@TC.no_method] eq_b: equatable b;
  [@@@TC.no_method] eq_c: equatable c;
  [@@@TC.no_method] congruence: heterogenous_congruence_lemma mul;  
}

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
 
type left_absorber_lemma #t (op: t->t->t) {| equatable t |} (zero: t) = 
  x:t -> Lemma (op zero x = zero)
  
type right_absorber_lemma #t (op: t->t->t) {| equatable t |} (zero: t) = 
  x:t -> Lemma (op x zero = zero)

type inversion_lemma #t {| equatable t |} (op: t->t->t) (zero:t) (inv: t->t) = 
  x:t -> Lemma (op x (inv x) = zero /\ op (inv x) x = zero)

let ( * ) #a #b #c {| m: mul_defined a b c |} = m.mul

class has_s_mul (s v:Type) = { 
  [@@@TC.no_method] smul: (z:mul_defined s v v{ z.eq_b == z.eq_c })
}

instance mul_of_smul s v (h: has_s_mul s v) : mul_defined s v v = h.smul

class has_mul_s (v s:Type) = { 
  [@@@TC.no_method] muls: (z:mul_defined v s v{ z.eq_a == z.eq_c })
}

instance mul_of_muls v s (h: has_mul_s v s) : mul_defined v s v = h.muls

class has_mul (t:Type) = {
  [@@@TC.no_method] mul: (z: mul_defined t t t { z.eq_a == z.eq_b /\ z.eq_a == z.eq_c })
}

instance mul_of_hm t (h: has_mul t) : mul_defined t t t = h.mul

instance eq_of_mul (t:Type) (h: has_mul t) : equatable t = h.mul.eq_a

let mul_congruence (#t:Type) {| m: has_mul t |} : congruence_lemma m.mul.mul = m.mul.congruence

type left_mul_absorber_lemma #t {| m: has_mul t |} (zero: t) = left_absorber_lemma ( * ) zero
type right_mul_absorber_lemma #t {| m: has_mul t |} (zero: t) = right_absorber_lemma ( * ) zero
   
instance int_equatable : equatable int = {
  eq = op_Equality;
  reflexivity = (fun _ -> ());
  symmetry = (fun _ _ -> ());
  transitivity = (fun _ _ _ -> ());
} 

instance int_mul_defined : mul_defined int int int = {
  mul = op_Multiply;
  eq_a = int_equatable;
  eq_b = int_equatable;
  eq_c = int_equatable;
  congruence = fun _ _ _ _ -> ()
}

instance int_mul : has_mul int = {
  mul = int_mul_defined 
}
 
class mul_semigroup (t:Type) = {  
  [@@@TC.no_method] has_mul : has_mul t; 
  [@@@TC.no_method] associativity: associativity_lemma has_mul.mul.mul;
}

instance has_mul_of_sg (t:Type) {| h: mul_semigroup t |} = h.has_mul

let mul_associativity #t {| sg: mul_semigroup t |} : associativity_lemma ( * ) = sg.associativity 
 
class has_one (t:Type) = {
  [@@@TC.no_method] eq: equatable t;
  one: t 
}

instance eq_of_ho (t:Type) (h: has_one t) = h.eq

class mul_monoid (t:Type) = {
  [@@@TC.no_method] has_one: has_one t;
  [@@@TC.no_method] mul_semigroup: (m:mul_semigroup t{has_one.eq == m.has_mul.mul.eq_a});
  left_mul_identity : left_identity_lemma mul_semigroup.has_mul.mul.mul one;
  right_mul_identity : right_identity_lemma mul_semigroup.has_mul.mul.mul one;
}

instance sg_of_mul_monoid (t:Type) {| h: mul_monoid t |} = h.mul_semigroup <: mul_semigroup t
instance has_one_of_monoid (t:Type) {| h: mul_monoid t |} = h.has_one

class mul_comm_magma (t:Type) = {
  [@@@TC.no_method] has_mul : has_mul t;
  mul_commutativity: commutativity_lemma has_mul.mul.mul; 
}

instance has_mul_of_comm_magma (t:Type) {| m: mul_comm_magma t |} = m.has_mul
 
class mul_comm_semigroup (t:Type) = {
  [@@@TC.no_method] mul_semigroup: mul_semigroup t;
  [@@@TC.no_method] mul_comm_magma : (m:mul_comm_magma t{m.has_mul == mul_semigroup.has_mul});
  dvd: x:t -> y:t -> (p:bool{ p <==> (exists (c:t). y = c*x) });
}

let ( |: ) #t {| mul_comm_semigroup t |} (x y: t) = dvd x y

instance sg_of_mul_comm_semigroup (t:Type) {| h: mul_comm_semigroup t |} = h.mul_semigroup
instance mul_comm_magma_of_comm_sg (t:Type) {| h: mul_comm_semigroup t |} = h.mul_comm_magma <: mul_comm_magma t
 
class mul_comm_monoid (t:Type) = {
  [@@@TC.no_method] mul_monoid: mul_monoid t;
  [@@@TC.no_method] mul_comm_semigroup: (z:mul_comm_semigroup t{z.mul_semigroup == mul_monoid.mul_semigroup}); 
}

instance mul_monoid_of_comm_monoid (t:Type) {| h: mul_comm_monoid t |} = h.mul_monoid

instance mul_comm_sg_of_comm_monoid (t:Type) {| h: mul_comm_monoid t |} = h.mul_comm_semigroup <: mul_comm_semigroup t

let is_right_factor_of (#t:Type) {| m: has_mul t |} (product factor:t) = 
  exists (c:t). c*factor = product

let is_left_factor_of (#t:Type) {| m: has_mul t |} (product factor:t) =
  exists (c:t). factor*c = product

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
      symmetry #t (factor*c) (c*factor);
      transitivity (c*factor) (factor*c) product
    end in Classical.move_requires aux_1 ();
  let aux_2 () : Lemma (requires is_right_factor_of product factor) 
                       (ensures is_left_factor_of product factor) =                        
    eliminate exists c. (c*factor=product)
    returns is_left_factor_of product factor with _.  
    begin
      mul_commutativity c factor;
      symmetry #t (c*factor) (factor*c);
      transitivity (factor*c) (c*factor) product
    end in Classical.move_requires aux_2 ()  
