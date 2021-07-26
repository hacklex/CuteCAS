module Sandbox
 
open FStar.Math.Lemmas

let trivial_statement = fun () -> ()
let trivial_unary_lemma = fun x -> ()
let trivial_binary_lemma = fun x y -> ()
let trivial_ternary_lemma = fun x y z -> ()

type predicate (#a:Type) = a -> Tot bool
type binary_op (#a:Type) = a -> a -> Tot a
type unary_op (#a:Type) = a -> Tot a
type binary_relation (#a:Type) = a -> a -> Tot bool

let is_symmetric (#a: Type) (rel: binary_relation #a) = forall (x y: a). (rel x y ==> rel y x)
let is_reflexive (#a: Type) (rel: binary_relation #a) = forall (x: a). (rel x x)
let is_transitive (#a: Type) (rel: binary_relation #a) = forall (x y z: a). (rel x y /\ rel y z) ==> rel x z
type equivalence_relation (#a:Type) = (eq:binary_relation #a{is_symmetric eq /\ is_reflexive eq /\ is_transitive eq})

let associativity_condition (#a: Type) (op: binary_op #a) (eq: equivalence_relation #a) (x: a) (y: a) (z: a) = eq (op x (op y z)) (op (op x y) z)
let commutativity_condition (#a: Type) (op: binary_op #a) (eq: equivalence_relation #a) (x: a) (y: a) = eq (op x y) (op y x)
let neutral_element_condition (#a: Type) (op: binary_op #a) (eq: equivalence_relation #a) (neutral: a) (x: a) = eq (op neutral x) x /\ eq (op x neutral) x
let inverse_element_condition (#a: Type) (op: binary_op #a) (inv: unary_op #a) (eq: equivalence_relation #a) (neutral: a) (x: a) 
  = eq (op (inv x) x) neutral /\ eq (op x (inv x)) neutral

let associativity_property (#a: Type) (op: binary_op #a) (eq: equivalence_relation #a) = forall (x y z: a). associativity_condition op eq x y z
let commutativity_property (#a: Type) (op: binary_op #a) (eq: equivalence_relation #a) = forall (x y: a). commutativity_condition op eq x y
let neutral_element_property (#a: Type) (op: binary_op #a) (eq: equivalence_relation #a) (neutral: a) = forall (x: a). neutral_element_condition op eq neutral x

type neutral_element_for (#a: Type) (op: binary_op #a) (eq: equivalence_relation #a) = (x:a{neutral_element_property op eq x})
let inverse_operation_property (#a: Type) (op: binary_op #a) (inv: unary_op #a) (eq: equivalence_relation #a) (neutral: neutral_element_for op eq) = forall (x:a). inverse_element_condition op inv eq neutral x
type inverse_operation_for (#a: Type) (op: binary_op #a) (eq: equivalence_relation #a) (neutral: neutral_element_for op eq) = (inv: unary_op #a { inverse_operation_property op inv eq neutral })

type commutativity_lemma  (#a: Type) (op: binary_op #a) (eq: equivalence_relation #a) = (x:a) -> (y:a) -> Lemma(commutativity_condition op eq x y)
type associativity_lemma (#a: Type) (op: binary_op #a) (eq: equivalence_relation #a) =  (x:a) -> (y:a) -> (z:a) -> Lemma(associativity_condition op eq x y z)
type element_neutrality_lemma (#a: Type) (op: binary_op #a) (eq: equivalence_relation #a) (neutral: a) = (x:a) -> Lemma(neutral_element_condition op eq neutral x)
type inverse_lemma (#a: Type) (op: binary_op #a) (inv: unary_op #a) (eq: equivalence_relation #a) (neutral: a) = (x:a) -> Lemma(inverse_element_condition op inv eq neutral x)

let neutral_uniqueness_lemma (#a: Type) (op: binary_op #a) (eq: equivalence_relation #a) (x: neutral_element_for op eq) (y: neutral_element_for op eq) : Lemma (eq x y) = ()

noeq type magma (#a: Type) = { op: binary_op #a; eq: equivalence_relation #a }

let op_of (#a: Type) (m: magma #a) = m.op
let eq_of (#a: Type) (m: magma #a) = m.eq

class semigroup_class (#a: Type) (sg: magma #a) = { op_is_associative: associativity_lemma sg.op sg.eq }
class commutative_magma_class (#a: Type) (sg: magma #a) = { op_is_commutative: commutativity_lemma sg.op sg.eq }
class monoid_class (#a: Type) (sg: magma #a)  = { is_semigroup: semigroup_class sg; neutral: neutral_element_for sg.op sg.eq; }

let neutral_of (#a: Type) (m: magma #a) {| mon: monoid_class m |} = mon.neutral

class commutative_monoid_class (#a: Type) (sg: magma #a) = { cm_is_monoid: monoid_class sg; cm_is_commutative_magma: commutative_magma_class sg }
class group_class (#a: Type) (sg: magma #a) = { g_is_monoid: monoid_class sg; inverse: inverse_operation_for sg.op sg.eq g_is_monoid.neutral; }

let inverse_of (#a: Type) (m: magma #a) {| g: group_class m |} = g.inverse


class commutative_group_class (#a: Type) (sg: magma #a) = {  cg_is_commutative : commutative_magma_class sg; cg_is_group: group_class sg; }

type triple 'a 'b 'c = { fst:'a; snd:'b; third:'c }
type distrinct_triple 'a = (t: triple 'a 'a 'a { t.fst =!= t.snd /\ t. fst =!= t.third /\ t.snd =!= t.third })
 
type semigroup (#a:Type) = x:magma #a{semigroup_class x}
type commutative_semigroup (#a: Type) = x:semigroup #a{commutative_magma_class x}
type monoid (#a: Type) = x:semigroup #a{monoid_class x}
type commutative_monoid (#a: Type) = x:monoid #a{commutative_magma_class x}
type group (#a: Type) = x:monoid #a{group_class x}
type commutative_group (#a: Type) = x:group #a{commutative_magma_class x}

noeq type amon = 
 | Mkamon : (#a: Type) 
    -> (op: binary_op #a) 
    -> (eq: equivalence_relation #a) 
    -> (#[Tactics.Typeclasses.tcresolve ()] mon: monoid_class (Mkmagma op eq)) 
    -> amon

noeq type agrp = 
 | Mkagrp : (#a: Type)
    -> (op: binary_op #a) 
    -> (eq: equivalence_relation #a) 
    -> (#[Tactics.Typeclasses.tcresolve ()] mon: monoid_class (Mkmagma op eq)) 
    -> (#[Tactics.Typeclasses.tcresolve ()] grp: group_class (Mkmagma op eq)) 
    -> agrp

instance ints_sg : semigroup_class (Mkmagma #int (+) (=)) = { op_is_associative = trivial_ternary_lemma }
instance ints_mo : monoid_class (Mkmagma #int (+) (=)) = { is_semigroup = ints_sg; neutral = 0 }

let ints = Mkamon (+) (=)
let neut = (Mkamon?.mon ints).neutral

let mag : magma #int = Mkmagma ints.op ints.eq

let right_distributive_over (#a: Type) (eq: equivalence_relation #a) (multiplication: semigroup #a) (addition: commutative_group #a)
  = forall (x y z: a). (eq (multiplication.op (addition.op y z) x) (addition.op (multiplication.op y x) (multiplication.op z x)))
let left_distributive_over (#a: Type) (eq: equivalence_relation #a) (multiplication: semigroup #a) (addition: commutative_group #a)
  = forall (x y z: a). (eq (multiplication.op x (addition.op y z)) (addition.op (multiplication.op x y) (multiplication.op x z)))
let fully_distributive_over (#a: Type) (eq: equivalence_relation #a) (mul: semigroup #a) (add: commutative_group #a)
  = (left_distributive_over eq mul add /\ right_distributive_over eq mul add)

noeq type ring (#a: Type) = {
  eq: equivalence_relation #a;
  addition: (t:commutative_group #a{eq == t.eq});
  multiplication: (m:monoid #a{eq == m.eq /\ fully_distributive_over eq m addition });
}

let zero_of (#a: Type) (r: ring #a) {| m: monoid_class r.addition |} = m.neutral
let one_of (#a: Type) (r: ring #a) {| m: monoid_class r.multiplication |} = m.neutral
let add_of (#a: Type) (r: ring #a) : binary_op #a = r.addition.op
let mul_of (#a: Type) (r: ring #a) : binary_op #a = r.multiplication.op
let is_zero_of (#a:Type) (r: ring #a) {| m: monoid_class r.addition |} (x: a) = r.eq m.neutral x
let is_one_of (#a:Type) (r: ring #a) {| m: monoid_class r.multiplication |} (x: a) = r.eq m.neutral x

let is_domain (#a: Type) (r: ring #a) {| m: monoid_class r.addition |} = 
  forall (x y: a). (is_zero_of r (mul_of r x y)) ==> (is_zero_of r x) \/ (is_zero_of r y)


type domain (#a: Type) = (z:(x: ring #a {monoid_class x.addition}){is_domain z})
//type domain (#a: Type) = x: ring #a{}


let list_cat (a: list int) (b: list int) : list int = a @ b
let list_sg : magma #(list int) = { op = list_cat; eq = (=) }

let assoc_cat_lemma (x: list int) (y: list int) (z: list int) 
  : Lemma (x @ (y @ z) == (x @ y) @ z) 
  = FStar.List.Tot.Properties.append_assoc x y z;  ()
let assoc_forall_lemma = Classical.forall_intro_3 assoc_cat_lemma    
 
instance list_semi : semigroup_class list_sg = { op_is_associative = assoc_cat_lemma  }

let list_sg_sg : semigroup #(list int) = 
  let make_semigroup (#a: Type) (m: magma #a) {| semigroup_class m |} : semigroup #a = m in
  make_semigroup list_sg

instance trivially_proven_semigroup (#a: Type) (sg: magma #a{associativity_property sg.op}) : semigroup sg = { op_is_associative = trivial_ternary_lemma }
instance trivially_proven_commutative (#a: Type) (sg: magma #a{commutativity_property sg.op}) : commutative_magma sg = { op_is_commutative = trivial_binary_lemma }
instance trivially_proven_monoid (#a: Type) (sg: magma #a) {|sg_class: semigroup sg|} (neutral: a{neutral_element_property sg.op neutral}) : monoid sg = 
{ 
  is_semigroup = sg_class; 
  neutral = neutral; 
}
instance trivially_proven_group (#a: Type) (sg: magma #a) {|m: monoid sg|} (inv: unary_op #a{inverse_operation_property sg.op inv m.neutral })
  : group sg = { g_is_monoid = m; inverse = inv }

let group_inverse (#a: Type) (sg: magma #a) {| g: group sg |} (x: a) = g.inverse x
let neutral_of (#a: Type) (sg: magma #a) {| m: monoid sg |} : neutral_element_for sg.op = m.neutral

let group_is_monoid (#a: Type) (sg: magma #a) {| g: group sg |} : Lemma (monoid sg) = ()

let distributive_left (#a:Type) (op_mul:binary_op #a) (op_add:binary_op #a) =
  forall (x y z:a). x `op_mul` (y `op_add` z) == (x `op_mul` y) `op_add` (x `op_mul` z)
let distributive_right (#a:Type) (op_mul:binary_op #a) (op_add:binary_op #a) =
  forall (x y z:a). (x `op_add` y) `op_mul` z == (x `op_mul` z) `op_add` (y `op_mul` z)
let fully_distributive (#a:Type) (op_mul:binary_op #a) (op_add:binary_op #a) =
  (distributive_left op_mul op_add) /\ (distributive_right op_mul op_add) 

noeq type ring (#a: Type) = 
{
  addition: (x:magma #a {commutative_group x});
  multiplication: (x: magma #a {semigroup x /\ fully_distributive x.op addition.op});
}

let ring_zero (#a: Type) (r: ring #a) {| m: monoid r.addition |} : neutral_element_for r.addition.op = m.neutral

class commutative_ring (#a: Type) (r: ring #a) = 
{
  cr_is_commutative: commutativity_lemma r.multiplication.op
}

class domain (#a: Type) (r: ring #a{ monoid r.addition })  = 
{ 
  d_no_zero_divisors : (x: a) -> (y: a) -> Lemma(
    let rz = ring_zero r in
    (r.multiplication.op x y == rz) ==> (x == rz \/ y == rz)  
  )   
}


let ints : magma #int = { op = op_Addition }
instance i1_sg : semigroup ints = trivially_proven_semigroup ints
instance i1_mo : monoid ints = trivially_proven_monoid ints 0
instance i1_g : group ints = trivially_proven_group ints op_Minus

  
type int_units = (p:int{p=1 \/ p=(-1)})
let ints_mul_subgroup : magma #int_units = {
  op = (fun (x:int_units) (y:int_units) -> x `op_Multiply` y)
}

let ints_mul : magma #int = { op = (fun x y -> x `op_Multiply` y) }

type vertex = {
  x: int;
  y: int
}

let rec insert' (x:vertex) (s: list vertex{has_unique_elem s}) : Tot (l : list vertex {has_unique_elem l}) =
 match s with
 | []        -> [x]
 | (hd :: tl) -> if x = hd then hd :: tl 
                else
                let _ = assert (x <> hd) in
                let l = hd :: (insert' x tl) in
                let _ = assert (has_unique_elem tl) in
                let _ = assert (has_unique_elem l) in
                l
