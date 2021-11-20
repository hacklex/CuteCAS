module Sandbox
 

assume val f : int -> Pure int True (fun r -> r == 7)  
effect Pr (a:Type) = Pure a True (fun _ -> True)
let g x = f x
let h x : Pure int True (fun r -> r < 8) = g x




type binary_op (a:Type) = a -> a -> a
type unary_op (a:Type) = a -> a
type predicate (a:Type) = a -> bool
type binary_relation (a: Type) = a -> a -> bool
 
[@@"opaque_to_smt"]
let is_reflexive  (#a:Type) (r: binary_relation a) = forall (x:a).     x `r` x
[@@"opaque_to_smt"]
let is_symmetric  (#a:Type) (r: binary_relation a) = forall (x y:a).   x `r` y == y `r` x
[@@"opaque_to_smt"]
let is_transitive (#a:Type) (r: binary_relation a) = forall (x y z:a). x `r` y /\ y `r` z ==> x `r` z 


let something x = Reflection.nameof (`x)

type equivalence_relation (a: Type) = r:binary_relation a{is_reflexive r /\ is_symmetric r /\ is_transitive r}

[@@"opaque_to_smt"]
let is_associative (#a:Type) (op:binary_op a) (eq: equivalence_relation a) = forall (x y z:a). ((x `op` y) `op` z) `eq` (x `op` (y `op` z))
[@@"opaque_to_smt"]
let is_commutative (#a:Type) (op:binary_op a) (eq: equivalence_relation a) = forall (x y:a). (x `op` y) `eq` (y `op` x)
 
[@@"opaque_to_smt"]
let is_idempotent (#a:Type) (r: unary_op a) (eq: equivalence_relation a)  = forall (x:a). (r x) `eq` (r (r x))
 
[@@"opaque_to_smt"]
let equivalence_wrt_condition (#a: Type) (op: binary_op a) (eq: equivalence_relation a) = 
  (forall (x y z:a). (x `eq` y) ==> ((x `op` z) `eq` (y `op` z))  /\ (z `op` x) `eq` (z `op` y))
  
type equivalence_wrt (#a: Type) (op: binary_op a) = eq:equivalence_relation a{equivalence_wrt_condition op eq}

[@@"opaque_to_smt"]
let is_left_id_of  (#a:Type) (u:a) (op:binary_op a) (eq: equivalence_relation a) = forall (x:a). (u `op` x) `eq` x // left identity
[@@"opaque_to_smt"]
let is_right_id_of (#a:Type) (u:a) (op:binary_op a) (eq: equivalence_relation a) = forall (x:a). (x `op` u) `eq` x // right identity
[@@"opaque_to_smt"]
let is_neutral_of  (#a:Type) (u:a) (op:binary_op a) (eq: equivalence_relation a) = is_left_id_of u op eq /\ is_right_id_of u op eq // neutral element

[@@"opaque_to_smt"]
let is_unit (#a: Type) (x: a) (op:binary_op a) (eq: equivalence_relation a) 
  = exists (y:a). (is_neutral_of (x `op` y) op eq /\ is_neutral_of (y `op` x) op eq)

[@@"opaque_to_smt"]  
let respects_equivalence (#a:Type) (f: unary_op a) (eq: equivalence_relation a) = forall (x y:a). (x `eq` y) ==> (f x) `eq` (f y)

type units_of (#a: Type) (mul: binary_op a) (eq: equivalence_relation a) = x:a{is_unit x mul eq}

[@@"opaque_to_smt"]
let is_inverse_operation_for (#a: Type) (inv: unary_op a) (op: binary_op a) (eq: equivalence_relation a) 
  = (forall (x:a). is_neutral_of (op x (inv x)) op eq /\ is_neutral_of (op (inv x) x) op eq)

/// The inverse operation type is also a refinement for arbitrary unary operation 
type inverse_op_for (#a: Type) (op: binary_op a) (eq: equivalence_relation a) 
  = (inv:unary_op a{is_inverse_operation_for inv op eq})

type pure_abs_func = int -> Pure(int) (requires True) (ensures fun x -> x>=0)

type pure_any_func = int -> Pure(int) (requires True) (ensures fun x -> true)

let abs (x : int) : Pure (int) (requires True) (ensures fun t -> t >= 0) = if x < 0 then -x else x

let abs2 (x: int) : (t:int{t>=0}) = if x<0 then -x else x

let accepts_any_function (q: pure_any_func) (v: int) = q v

let ax = accepts_any_function abs 4

let accepts_nonnegative_function (q: pure_abs_func) (v:int) = q v

let afn2 = accepts_nonnegative_function (fun x -> abs x) 4

let afn = accepts_nonnegative_function abs 4

type unary_op_on_units_of (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) = f:((x: a) -> Pure(a) (requires is_unit x op eq) (ensures (fun (n:a) -> is_unit n op eq)))
  { respects_equivalence #(units_of op eq) (fun q -> f q) (    
     reveal_opaque (`%is_reflexive) (is_reflexive #a); 
     reveal_opaque (`%is_reflexive) (is_reflexive #(units_of op eq)); 
     reveal_opaque (`%is_symmetric) (is_symmetric #a);   
     reveal_opaque (`%is_symmetric) (is_symmetric #(units_of op eq));   
     reveal_opaque (`%is_transitive) (is_transitive #a);
     reveal_opaque (`%is_transitive) (is_transitive #(units_of op eq));
     eq
   ) }

(*
type unary_op_on_units_of (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) =
  f:unary_op(units_of op eq){
   respects_equivalence f (    
     reveal_opaque (`%is_reflexive) (is_reflexive #a); 
     reveal_opaque (`%is_reflexive) (is_reflexive #(units_of op eq)); 
     reveal_opaque (`%is_symmetric) (is_symmetric #a);   
     reveal_opaque (`%is_symmetric) (is_symmetric #(units_of op eq));   
     reveal_opaque (`%is_transitive) (is_transitive #a);
     reveal_opaque (`%is_transitive) (is_transitive #(units_of op eq));
     eq
   )
  } *)

let yields_inverses_for_units (#a:Type) (op: binary_op a) (eq: (t: equivalence_wrt op {is_associative op t})) (inv: unary_op_on_units_of op eq) = 
  forall (x: units_of op eq). is_neutral_of (op (inv x) x) op eq /\ is_neutral_of (op x (inv x)) op eq

type partial_inverse_op_for (#a:Type) (op: binary_op a) (eq: (t: equivalence_wrt op {is_associative op t})) = (f: unary_op_on_units_of op eq{yields_inverses_for_units op eq f})

let inverse_is_unique (#a:Type) (op: binary_op a) 
                                (eq: (t: equivalence_wrt op {is_associative op t})) 
                                (inv: partial_inverse_op_for op eq)
                                (x inv1 inv2: a) : Lemma
                                (requires is_neutral_of (inv1 `op` x) op eq 
                                        /\ is_neutral_of (x `op` inv1) op eq 
                                        /\ is_neutral_of (inv2 `op` x) op eq
                                        /\ is_neutral_of (x `op` inv2) op eq)
                                (ensures (eq inv1 inv2 /\ eq inv2 inv1)) =  
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  reveal_opaque (`%is_transitive) (is_transitive #a);
  reveal_opaque (`%is_associative) (is_associative #a); 
  reveal_opaque (`%is_commutative) (is_commutative #a);
  reveal_opaque (`%is_left_id_of) (is_left_id_of #a);
  reveal_opaque (`%is_right_id_of) (is_right_id_of #a);
  reveal_opaque (`%is_neutral_of) (is_neutral_of #a);
  ()
                            
let unit_inverse_is_unit (#a:Type) (op: binary_op a) 
                                   (eq: (t: equivalence_wrt op {is_associative op t}))
                                   (inv: partial_inverse_op_for op eq)
                                   (x: units_of op eq)
                                   : Lemma (is_unit (inv x) op eq) = reveal_opaque (`%is_unit) (is_unit #a)

let all_are_units (#a:Type) (op: binary_op a) (eq: equivalence_wrt op {is_associative op eq}) = 
  forall (x:a). is_unit x op eq
  
noeq type magma (#a: Type) =  
{
  op: binary_op a;
  eq: equivalence_wrt op;
  inv: unary_op_on_units_of op eq;
  neutral: a
}

let magma_inv_respects_eq (#a:Type) (m: magma #a) : Lemma (  
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  reveal_opaque (`%is_reflexive) (is_reflexive #(units_of m.op m.eq)); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  reveal_opaque (`%is_symmetric) (is_symmetric #(units_of m.op m.eq));   
  reveal_opaque (`%is_transitive) (is_transitive #a);
  reveal_opaque (`%is_transitive) (is_transitive #(units_of m.op m.eq));
  reveal_opaque (`%is_unit) (is_unit #a);
  respects_equivalence #(units_of m.op m.eq) m.inv m.eq) = ()

type semigroup (#a:Type)             = g: magma #a{is_associative g.op g.eq /\ yields_inverses_for_units #a g.op g.eq g.inv}
type commutative_magma (#a:Type)     = g: magma #a{is_commutative g.op g.eq}
type commutative_semigroup (#a:Type) = g: semigroup #a{is_commutative g.op g.eq}
type monoid (#a:Type)                = g: semigroup #a{is_neutral_of g.neutral g.op g.eq}
type commutative_monoid (#a:Type)    = g: monoid #a{is_commutative g.op g.eq}
type group (#a:Type)                 = g: monoid #a{all_are_units g.op g.eq}
type commutative_group (#a:Type)     = g: group #a{is_commutative g.op g.eq}

let g_inv_as_full_inv (#a:Type) (g: group #a) : inverse_op_for g.op g.eq = 
  reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #a);
  g.inv
