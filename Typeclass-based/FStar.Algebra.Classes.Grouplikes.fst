module FStar.Algebra.Classes.Grouplikes

module TC=FStar.Tactics.Typeclasses

open FStar.Algebra.Classes.Equatable


type associativity_lemma (#t:Type) {| equatable t |} (op: t->t->t) = 
  x:t -> y:t -> z:t -> Lemma (op (op x y) z = op x (op y z))

type commutativity_lemma (#t:Type) {| equatable t |} (op: t->t->t) = 
  x:t -> y:t -> Lemma (op x y = op y x)

type congruence_lemma (#t:Type) {| equatable t |} (op: t->t->t) = 
  x:t -> y:t -> z:t -> w:t -> Lemma (requires x=z /\ y=w) (ensures op x y = op z w)

type heterogenous_congruence_lemma (#a #b #c: Type) 
                                   {| equatable a |} 
                                   {| equatable b |} 
                                   {| equatable c |} (op: a->b->c) =
  x:a -> y:b -> z:a -> w:b -> Lemma (requires x=z /\ y=w) (ensures op x y = op z w)

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
 
class has_mul (t:Type) = { 
  [@@@TC.no_method] eq: equatable t;
  ( * ): t -> t -> t; //(z:mul_defined t t t{z.eq_a == z.eq_b /\ z.eq_b == z.eq_c })
  [@@@TC.no_method] congruence : congruence_lemma ( * );  
}
 
instance eq_of_mul (t:Type) {| h: has_mul t |} : equatable t = h.eq

let mul_congruence (#t:Type) {| m: has_mul t |} : congruence_lemma ( * ) = m.congruence

type left_mul_absorber_lemma #t {| m: has_mul t |} (zero: t) = left_absorber_lemma ( * ) zero
type right_mul_absorber_lemma #t {| m: has_mul t |} (zero: t) = right_absorber_lemma ( * ) zero
   
class has_add (t:Type) = {  
  ( + ) : t -> t -> t;
  [@@@TC.no_method] eq: equatable t;
  [@@@TC.no_method] congruence: congruence_lemma ( + );
} 

instance eq_of_add (t:Type) {| h: has_add t |} : equatable t = h.eq 
  
 
instance int_mul : has_mul int = {
  ( * ) = op_Multiply;
  eq = TC.solve;
  congruence = fun _ _ _ _ -> ()
}
 
instance int_add : has_add int = {
  ( + ) = op_Addition;
  eq = TC.solve;
  congruence = fun _ _ _ _ -> ()
}

class mul_semigroup (t:Type) = {  
  [@@@TC.no_method] has_mul : has_mul t; 
  [@@@TC.no_method] associativity: associativity_lemma #t ( * );
}

instance has_mul_of_sg (t:Type) {| h: mul_semigroup t |} = h.has_mul

class add_semigroup (t:Type) = {
  [@@@TC.no_method] has_add : has_add t; 
  [@@@TC.no_method] associativity: associativity_lemma #t (+);
}

let mul_associativity #t {| sg: mul_semigroup t |} : associativity_lemma ( * ) = sg.associativity 
let add_associativity #t {| sg: add_semigroup t |} : associativity_lemma ( + ) = sg.associativity
 
let add_congruence #t {| ha: has_add t |} : congruence_lemma ( + ) = ha.congruence 


instance has_add_of_sg (t:Type) {| h: add_semigroup t |} : has_add t = h.has_add
 
class has_zero (t:Type) = { 
  [@@@TC.no_method] eq: equatable t;
  zero: t
}

instance eq_of_hz (t:Type) (h: has_zero t) = h.eq

class add_monoid (t:Type) = {
  [@@@TC.no_method] has_zero: has_zero t;
  [@@@TC.no_method] add_semigroup: (a:add_semigroup t{has_zero.eq == a.has_add.eq});
  left_add_identity  : left_identity_lemma #t (let ha : has_add t = has_add_of_sg t #add_semigroup in ( + ) ) zero;
  right_add_identity : right_identity_lemma #t (let ha : has_add t = has_add_of_sg t #add_semigroup in ( + ) ) zero;
}

instance sg_of_add_monoid (t:Type) {| h: add_monoid t |} = h.add_semigroup <: add_semigroup t
instance has_zero_of_monoid (t:Type) {| h: add_monoid t |} = h.has_zero

class has_one (t:Type) = {
  [@@@TC.no_method] eq: equatable t;
  one: t 
}

instance eq_of_ho (t:Type) (h: has_one t) = h.eq

class mul_monoid (t:Type) = {
  [@@@TC.no_method] has_one: has_one t;
  [@@@TC.no_method] mul_semigroup: (m:mul_semigroup t{has_one.eq == m.has_mul.eq});
  left_mul_identity : left_identity_lemma #t (let hm : has_mul t = has_mul_of_sg t #mul_semigroup in ( * )) one;
  right_mul_identity : right_identity_lemma #t (let hm : has_mul t = has_mul_of_sg t #mul_semigroup in ( * )) one;
}

instance sg_of_mul_monoid (t:Type) {| h: mul_monoid t |} = h.mul_semigroup <: mul_semigroup t
instance has_one_of_monoid (t:Type) {| h: mul_monoid t |} = h.has_one

class add_comm_magma (t:Type) = {
  [@@@TC.no_method] has_add : has_add t;
  add_commutativity: commutativity_lemma #t ( + ); 
}

class mul_comm_magma (t:Type) = {
  [@@@TC.no_method] has_mul : has_mul t;
  mul_commutativity: commutativity_lemma #t ( * ); 
}

instance has_add_of_comm_magma (t:Type) {| m: add_comm_magma t |} = m.has_add
instance has_mul_of_comm_magma (t:Type) {| m: mul_comm_magma t |} = m.has_mul

class add_comm_semigroup (t:Type) = {
  [@@@TC.no_method] add_semigroup: add_semigroup t;
  [@@@TC.no_method] add_comm_magma : (m:add_comm_magma t{m.has_add == add_semigroup.has_add});
}

instance sg_of_add_comm_semigroup (t:Type) {| h: add_comm_semigroup t |} = h.add_semigroup
instance add_comm_magma_of_comm_sg (t:Type) {| h: add_comm_semigroup t |} = h.add_comm_magma <: add_comm_magma t

class mul_comm_semigroup (t:Type) = {
  [@@@TC.no_method] mul_semigroup: mul_semigroup t;
  [@@@TC.no_method] mul_comm_magma : (m:mul_comm_magma t{m.has_mul == mul_semigroup.has_mul});
  dvd: x:t -> y:t -> (p:bool{ p <==> (exists (c:t). y = c*x) });
}

let ( |: ) #t {| mul_comm_semigroup t |} (x y: t) = dvd x y

instance sg_of_mul_comm_semigroup (t:Type) {| h: mul_comm_semigroup t |} = h.mul_semigroup
instance mul_comm_magma_of_comm_sg (t:Type) {| h: mul_comm_semigroup t |} = h.mul_comm_magma <: mul_comm_magma t
 
class add_comm_monoid (t:Type) = {
  [@@@TC.no_method] add_monoid: add_monoid t;
  [@@@TC.no_method] add_comm_semigroup: (z:add_comm_semigroup t{z.add_semigroup == add_monoid.add_semigroup});
}
  
instance add_monoid_of_comm_monoid (t:Type) {| h: add_comm_monoid t |} = h.add_monoid
instance add_comm_sg_of_comm_monoid (t:Type) {| h: add_comm_monoid t |} = h.add_comm_semigroup <: add_comm_semigroup t
 
class mul_comm_monoid (t:Type) = {
  [@@@TC.no_method] mul_monoid: mul_monoid t;
  [@@@TC.no_method] mul_comm_semigroup: (z:mul_comm_semigroup t{z.mul_semigroup == mul_monoid.mul_semigroup}); 
}
 
instance mul_monoid_of_comm_monoid (t:Type) {| h: mul_comm_monoid t |} = h.mul_monoid
instance mul_comm_sg_of_comm_monoid (t:Type) {| h: mul_comm_monoid t |} = h.mul_comm_semigroup <: mul_comm_semigroup t

let old_int_minus = op_Minus

class has_neg (t:Type) = {
  op_Minus: t -> t
}

//let op_Minus (#t:Type) {| h: has_neg t |} = h.neg

let old_int_sub = op_Subtraction
 
class has_sub (t:Type) = {
  op_Subtraction : t -> t -> t
}

//let op_Subtraction (#t:Type) {| h: has_sub t |} = h.sub

instance int_sub : has_sub int = { op_Subtraction = old_int_sub }
instance int_neg : has_neg int = { op_Minus = old_int_minus }

class add_group (t:Type) = {
  [@@@TC.no_method] add_monoid: add_monoid t;
  [@@@TC.no_method] has_neg: has_neg t;
  [@@@TC.no_method] has_sub: has_sub t;
  subtraction_definition : (x:t -> y:t -> Lemma ((x - y) = (x + (-y))));
  negation: inversion_lemma #t ( + ) zero op_Minus;
}

class add_comm_group (t:Type) = {
  [@@@TC.no_method] add_group: add_group t;
  [@@@TC.no_method] add_comm_monoid: (z:add_comm_monoid t{z.add_monoid == add_group.add_monoid});
}

instance add_monoid_of_group (t:Type) {| h: add_group t |} = h.add_monoid
instance neg_of_add_group (t:Type) {| h: add_group t |} = h.has_neg
instance sub_of_add_group (t:Type) {| h: add_group t |} = h.has_sub

instance add_group_of_comm_group (t:Type) {| h: add_comm_group t |} = h.add_group
instance add_comm_monoid_of_comm_group (t:Type) {| h: add_comm_group t |} = h.add_comm_monoid <: add_comm_monoid t


/// Now we construct typeclass-less versions of the lemmas in parallel,
/// to compare the verification speeds



type binary_op a = a -> a -> a
type unary_op a = a -> a
type predicate a = a -> bool
type binary_relation a = a -> a -> bool
 
[@@"opaque_to_smt"]
let is_reflexive #a (op_Equals: binary_relation a) = forall (x:a).     x = x
[@@"opaque_to_smt"]
let is_symmetric #a (op_Equals: binary_relation a) = forall (x y:a).   (x = y) == (y = x)
[@@"opaque_to_smt"]
let is_transitive #a (op_Equals: binary_relation a) = forall (x y z:a). x = y /\ y = z ==> x = z 


type equivalence_relation a = r:binary_relation a { is_reflexive r /\ is_symmetric r /\ is_transitive r }

[@@"opaque_to_smt"]
let congruence_condition #a (op_Equals: equivalence_relation a) (op_Star: binary_op a) 
  = forall (x y z:a). (x = y) ==> (x * z = y * z) && (z * x = z * y)

[@@"opaque_to_smt"]
let unary_congruence_condition #a (op_Equals: equivalence_relation a) (op: unary_op a)
  = forall (x y: a). (x = y) ==> (op x = op y) && (op y = op x)

type op_with_congruence #a (eq: equivalence_relation a)
  = op:binary_op a{congruence_condition eq op}

type unary_op_with_congruence #a (eq: equivalence_relation a)
  = op:unary_op a{unary_congruence_condition eq op}

let trans_lemma #a (op_Equals: equivalence_relation a) (x y z:a)
  : Lemma (requires (x=y \/ y=x) /\ (y=z \/ z=y))  
          (ensures (x=z) && (z=x))   
  = reveal_opaque (`%is_transitive) (is_transitive (=));
    reveal_opaque (`%is_symmetric) (is_symmetric (=))
 
let trans_lemma_4 #a (op_Equals: equivalence_relation a) (x y z w:a)
  : Lemma (requires (x=y \/ y=x) /\ (y=z \/ z=y) /\ (z=w \/ w=z))
          (ensures x = w && w = x) = 
  trans_lemma (=) x y z;
  trans_lemma (=) x z w

let trans_lemma_5 #a (op_Equals: equivalence_relation a) (x y z w v: a)                            
  : Lemma (requires (x = y \/ y = x) /\ 
                    (y = z \/ z = y) /\ 
                    (z = w \/ w = z) /\
                    (w = v \/ v = w))
          (ensures x = v && v = x) = 
  trans_lemma (=) x y z;
  trans_lemma_4 (=) x z w v

let refl_lemma #a (#op_Equals:equivalence_relation a) (x:a) 
  : Lemma (x = x) = reveal_opaque (`%is_reflexive) (is_reflexive #a) 

let symm_lemma #a (#op_Equals:equivalence_relation a) (x y:a) 
  : Lemma ((x=y) == (y=x)) = reveal_opaque (`%is_symmetric) (is_symmetric (=)) 

let congruence_lemma_3 #a (#op_Equals: equivalence_relation a) (op_Star: op_with_congruence op_Equals) (e1 e2 z: a)
  : Lemma 
  (requires e1 = e2 \/ e2 = e1) 
  (ensures ((e1 * z = e2 * z) /\    
            (e2 * z = e1 * z) /\    
            (z * e1 = z * e2) /\
            (z * e2 = z * e1)))
  = reveal_opaque (`%congruence_condition) (congruence_condition (=) ( * ));
    reveal_opaque (`%is_symmetric) (is_symmetric (=)) 

let congruence_lemma_4 #a
                       (#op_Equals: equivalence_relation a) 
                       (op_Star: op_with_congruence (=))
                       (x y p q: a) 
  : Lemma (requires (x = p \/ p = x) /\ (y = q \/ q = y))
          (ensures  (x * y = p * q) /\ (y * x = q * p)) =          
  reveal_opaque (`%congruence_condition) (congruence_condition (=) ( * ));
  reveal_opaque (`%is_transitive) (is_transitive (=));
  congruence_lemma_3 ( * ) x p y;
  congruence_lemma_3 ( * ) y q p  
    

let zero_equals_minus_zero #t {| a: add_group t |} 
  : Lemma (a.add_monoid.has_zero.zero = -a.add_monoid.has_zero.zero) = 
  let zero : t = zero in
  let ha = a.add_monoid.add_semigroup.has_add in
  //let (=) = ha.eq.eq in
  //let (+) = ha.add in
  //let op_Minus = a.has_neg.neg in
  Classical.forall_intro_2 ha.eq.symmetry;
  left_add_identity (-zero);
  assert (zero + -zero = -zero);
  negation zero;
  assert (zero + -zero = zero);
  transitivity zero (zero + -zero) (-zero)

 
let group_cancellation_left (#t:Type) {| g: add_group t |} (x y z: t)
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

let group_cancellation_right (#t:Type) {| g: add_group t |} (x y z: t)
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
    returns is_right_factor_of #t product factor with _. 
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
  symmetry (-(-x) + (-x + x)) (-(-x) + zero);
  right_add_identity (-(-x));
  symmetry (-(-x) + zero) (-(-x));
  transitivity (-(-x)) (-(-x) + zero) (-(-x) + (-x+x));
  symmetry (-(-x) + (-x) + x) (-(-x) + (-x + x));
  transitivity (-(-x)) (-(-x) + (-x+x)) (-(-x) + -x + x);
  transitivity (-(-x)) (-(-x) + -x + x) (zero + x);
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
   
let equal_elements_means_equal_inverses (#t:Type) {| g: add_group t |} (x y:t) 
  : Lemma ((x=y) == (-x = -y)) =   
    let aux_1 (p q:t) : Lemma (requires p=q) (ensures -p = -q) =
      equal_elements_have_equal_inverses p q in
    let aux_2 (p q:t) : Lemma (requires -p = -q) (ensures p=q) = 
      double_negation_lemma p;
      double_negation_lemma q;
      equal_elements_have_equal_inverses (-p) (-q);
      symmetry (-(-p)) p;
      transitivity p (-(-p)) (-(-q));
      transitivity p (-(-q)) q in
    if (x=y && -x <> -y) then aux_1 x y
    else if (x <> y && -x = -y) then aux_2 x y

let equality_is_zero_diff (#t:Type) {| add_group t |} (x y: t)
  : Lemma ((x=y) <==> (x + -y = zero)) = 
  elim_equatable_laws t;
  transitivity_for_calc_proofs t;
  negation y;
  let aux_1 (x y:t) : Lemma (requires x=y) (ensures x + -y = zero) =
    negation y;
    add_congruence x (-y) y (-y)
    in Classical.move_requires_2 aux_1 x y;    
  let aux_2 (x y:t) : Lemma (requires x + -y = zero) (ensures x=y) =  
    negation y;
    add_congruence (x + -y) y zero y;
    add_associativity x (-y) y;
    add_congruence x (-y + y) x zero;
    right_add_identity x;
    left_add_identity y
    in Classical.move_requires_2 aux_2 x y
 
let neg_of_sum #t {| g: add_group t |} (x y:t)
  : Lemma (-(x+y) = -y + -x) = 
  let e : equatable t = TC.solve in
  //Classical.forall_intro e.reflexivity;
  Classical.forall_intro_2 e.symmetry;
  transitivity_for_calc_proofs t;
  e.reflexivity x;
  e.reflexivity (-x);
  calc (=) {
    (x+y) + (-y + -x); = { add_associativity x y (-y + -x) }
    x + (y + (-y + -x)); = { add_associativity y (-y) (-x);
                             add_congruence x (y + (-y + -x)) x ((y + -y) + -x) }
    x + ((y + -y) + -x); =  { negation y;
                              add_congruence (y + -y) (-x) zero (-x);
                              left_add_identity (-x);                              
                              add_congruence x ((y + -y) + -x) x (-x) }
    x + -x; = { negation x } 
    zero;
  };
  negation (x+y); 
  group_cancellation_left (x+y) (-y + -x) (-(x+y)) 
