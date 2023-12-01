module FStar.Algebra.Classes.Multiplicative

module TC=FStar.Tactics.Typeclasses

open FStar.Algebra.Classes.Equatable

type either_of (a b: Type0) = c:Type {c==a \/ c==b}

class mul_def (l r: Type0) = {
  mul_result: Type0;
  op: l -> r -> mul_result
}

let ( * ) #l #r {| md: mul_def l r |} (x:l) (y:r) : md.mul_result = md.op x y

type heterogenous_congruence_lemma (#a #b: Type) 
                                   (#c: either_of a b)
                                   {| ea: equatable a |} 
                                   {| eb: equatable b |}                                    
                                   {| ec: equatable c |} (op: a->b->c) =
  x:a -> y:b -> z:a -> w:b -> Lemma (requires x `ea.eq` z /\ y `eb.eq` w) (ensures op x y `ec.eq` op z w)

class has_smul (scalar vector: Type0) = {
  [@@@TC.no_method] s_eq : equatable scalar;
  [@@@TC.no_method] v_eq : equatable vector;
  smul: (md: mul_def scalar vector{md.mul_result == vector});
  smul_congruence : heterogenous_congruence_lemma #scalar #vector #vector smul.op
}

class has_muls (vector scalar: Type0) = {  
  [@@@TC.no_method] s_eq : equatable scalar;
  [@@@TC.no_method] v_eq : equatable vector;
  muls: (md: mul_def vector scalar{md.mul_result == vector});
  muls_congruence : heterogenous_congruence_lemma #vector #scalar #vector muls.op
}

class has_mul (vector: Type0) = {
  [@@@TC.no_method] eq : equatable vector;
  mul: (md: mul_def vector vector{md.mul_result == vector});
  mul_congruence : heterogenous_congruence_lemma #vector #vector #vector mul.op
}

instance smul_of_hm s v (h: has_smul s v) : mul_def s v = h.smul
instance muls_of_hm v s (h: has_muls v s) : mul_def v s = h.muls
instance mul_of_hm v (h: has_mul v) : mul_def v v = h.mul

type associativity_lemma (#t:Type) {| equatable t |} (op: t->t->t) = 
  x:t -> y:t -> z:t -> Lemma (op (op x y) z = op x (op y z))

type commutativity_lemma (#t:Type) {| equatable t |} (op: t->t->t) = 
  x:t -> y:t -> Lemma (op x y = op y x)

type congruence_lemma (#t:Type) {| equatable t |} (op: t->t->t) = heterogenous_congruence_lemma op

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
  
instance scalar_eq_of_smul s v (h: has_smul s v) : equatable s = h.s_eq
instance vector_eq_of_smul s v (h: has_smul s v) : equatable v = h.v_eq
instance scalar_eq_of_muls v s (h: has_muls v s) : equatable s = h.s_eq
instance vector_eq_of_muls v s (h: has_muls v s) : equatable v = h.v_eq
instance vector_eq_of_mul v (h: has_mul v) : equatable v = h.eq
 
type left_mul_absorber_lemma #t {| m: has_mul t |} (zero: t) = left_absorber_lemma m.mul.op zero
type right_mul_absorber_lemma #t {| m: has_mul t |} (zero: t) = right_absorber_lemma m.mul.op zero
   
instance int_equatable : equatable int = {
  eq = op_Equality;
  reflexivity = (fun _ -> ());
  symmetry = (fun _ _ -> ());
  transitivity = (fun _ _ _ -> ());
} 

instance int_mul_def : mul_def int int = {
  mul_result = int;
  op = op_Multiply;
}

instance int_mul : has_mul int = {
  mul = int_mul_def;
  eq = int_equatable;
  mul_congruence = fun _ _ _ _ -> ()
}
 
class mul_semigroup (t:Type) = {  
  [@@@TC.no_method] has_mul : has_mul t; 
  [@@@TC.no_method] associativity: associativity_lemma has_mul.mul.op;
}

instance has_mul_of_sg (t:Type) {| h: mul_semigroup t |} = h.has_mul

let mul_associativity #t {| sg: mul_semigroup t |} : associativity_lemma sg.has_mul.mul.op = sg.associativity 
 
class has_one (t:Type) = {
  [@@@TC.no_method] eq: equatable t;
  one: t 
}

instance eq_of_ho (t:Type) (h: has_one t) = h.eq

class mul_monoid (t:Type) = {
  [@@@TC.no_method] has_one: has_one t;
  [@@@TC.no_method] mul_semigroup: (m:mul_semigroup t{has_one.eq == m.has_mul.eq});
  left_mul_identity : left_identity_lemma mul_semigroup.has_mul.mul.op one;
  right_mul_identity : right_identity_lemma mul_semigroup.has_mul.mul.op one;
}

instance sg_of_mul_monoid (t:Type) {| h: mul_monoid t |} = h.mul_semigroup <: mul_semigroup t
instance has_one_of_monoid (t:Type) {| h: mul_monoid t |} = h.has_one

class mul_comm_magma (t:Type) = {
  [@@@TC.no_method] has_mul : has_mul t;
  mul_commutativity: commutativity_lemma has_mul.mul.op; 
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
  let ( * ) x y : t = x * y in
  let aux_1 () : Lemma (requires is_left_factor_of product factor) 
                       (ensures is_right_factor_of product factor) =     
    eliminate exists c. (factor*c=product)
    returns is_right_factor_of product factor with _. 
    begin
      mul_commutativity factor c;
      symmetry  (factor*c) (c*factor);
      transitivity (c*factor) (factor*c) product
    end in Classical.move_requires aux_1 ();
  let aux_2 () : Lemma (requires is_right_factor_of product factor) 
                       (ensures is_left_factor_of product factor) =                        
    eliminate exists c. (c*factor=product)
    returns is_left_factor_of product factor with _.  
    begin
      mul_commutativity c factor;
      symmetry  (c*factor) (factor*c);
      transitivity (factor*c) (c*factor) product
    end in Classical.move_requires aux_2 ()  

assume 
  val ghost_of_fun_from_fun_of_ghost (#t:Type) (f: t -> GTot bool) 
    : GTot (g:(t -> bool){forall (x:t). g x = f x })
