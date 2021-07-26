module ExtractedSandbox

type predicate (#a:Type) = a -> Tot bool
type binary_op (#a:Type) = a -> a -> Tot a
type unary_op (#a:Type) = a -> Tot a
type binary_relation (#a:Type) = a -> a -> Tot bool

/// Even though the name is longer than the definition,
/// reading the name is more convenient
let trivial_statement = fun () -> ()
let trivial_unary_lemma = fun x -> ()
let trivial_binary_lemma = fun x y -> ()
let trivial_ternary_lemma = fun x y z -> ()

let is_symmetric (#a: Type) (rel: binary_relation #a) = forall (x y: a). (rel x y ==> rel y x)
let is_reflexive (#a: Type) (rel: binary_relation #a) = forall (x: a). (rel x x)
let is_transitive (#a: Type) (rel: binary_relation #a) = forall (x y z: a). (rel x y /\ rel y z) ==> rel x z
type equivalence_relation (#a: Type) = (eq: binary_relation #a{is_symmetric eq /\ is_reflexive eq /\ is_transitive eq})

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

/// Base type for all algebraic structures with 1 operation.
/// Poses no restrictions on said operation, and thus is usually
/// not used on its own, but rather as a base type for more well-structured
/// entities like semigroups
noeq type magma (#a: Type) = { op: binary_op #a; eq: equivalence_relation #a }

let eq_of (#a: Type) (m: magma #a) = m.eq

/// A class saying "this magma's operation is associative
class semigroup_class (#a: Type) (sg: magma #a) = { op_is_associative: associativity_lemma sg.op sg.eq }
/// A class saying "this one's commutative (though not necessarily associative
class commutative_magma_class (#a: Type) (sg: magma #a) = { op_is_commutative: commutativity_lemma sg.op sg.eq }
/// A class saying "this one's got a neutral element" by storing that element 
class monoid_class (#a: Type) (sg: magma #a)  = { is_semigroup: semigroup_class sg; neutral: neutral_element_for sg.op sg.eq; }

let cm_neutral (#a:Type) (#m: magma #a) (mc: monoid_class m) = mc.neutral

/// Shorthand to retrieve the neutral element for an at-least-a-monoid
/// Supposed to automatically work with magmas that are {| groups |} of course
let neutral_of (#a: Type) (m: magma #a) {| mon: monoid_class m |} = mon.neutral

/// Similarly defined stuff for the rest of group-likes
class commutative_monoid_class (#a: Type) (sg: magma #a) = { cm_is_monoid: monoid_class sg; cm_is_commutative_magma: commutative_magma_class sg }
class group_class (#a: Type) (sg: magma #a) = { g_is_monoid: monoid_class sg; inverse: inverse_operation_for sg.op sg.eq g_is_monoid.neutral; }

let inverse_of (#a: Type) (m: magma #a) {| g: group_class m |} = g.inverse

class commutative_group_class (#a: Type) (sg: magma #a) = {  cg_is_commutative : commutative_magma_class sg; cg_is_group: group_class sg; }

/// Now the types defined as magma refinements:
///
/// Magma that is associative is a semigroup
type semigroup (#a:Type) = x:magma #a{semigroup_class x}
/// Semigroup that is commutative is, naturally a commutative semigroup
type commutative_semigroup (#a: Type) = x:semigroup #a{commutative_magma_class x}
/// Semigroup with neutral element is a monoid
type monoid (#a: Type) = x:semigroup #a{monoid_class x}
/// And so on...
type commutative_monoid (#a: Type) = x:monoid #a{commutative_magma_class x}
type group (#a: Type) = x:monoid #a{group_class x}
type commutative_group (#a: Type) = x:group #a{commutative_magma_class x}

let make_semigroup (#a: Type) (m: magma #a) {| semigroup_class m |} : semigroup #a = m
let make_monoid (#a: Type) (m: magma #a) {| semigroup_class m |} {| monoid_class m |} : monoid #a = m
let make_commutative_group (#a: Type) (m: magma #a) {| semigroup_class m |} {| commutative_magma_class m |} {| monoid_instance: monoid_class m |} {| group_class m |} : commutative_group #a = m

/// Left, right, and full distributivity
let right_distributive_over (#a: Type) (eq: equivalence_relation #a) (multiplication: semigroup #a) (addition: commutative_group #a)
  = forall (x y z: a). (eq (multiplication.op (addition.op y z) x) (addition.op (multiplication.op y x) (multiplication.op z x)))
let left_distributive_over (#a: Type) (eq: equivalence_relation #a) (multiplication: semigroup #a) (addition: commutative_group #a)
  = forall (x y z: a). (eq (multiplication.op x (addition.op y z)) (addition.op (multiplication.op x y) (multiplication.op x z)))
let fully_distributive_over (#a: Type) (eq: equivalence_relation #a) (mul: semigroup #a) (add: commutative_group #a)
  = (left_distributive_over eq mul add /\ right_distributive_over eq mul add)

/// Let's ignore RNGs, non-associative rings etc, and consider this the most basic of ringlikes
noeq type ring (#a: Type) = 
 | Ring: (eq: equivalence_relation #a) -> 
         (addition: (t:commutative_group #a{eq == t.eq})) ->
         (multiplication: (m:monoid #a{eq == m.eq /\ fully_distributive_over eq m addition })) ->
         (#[Tactics.Typeclasses.tcresolve ()] addition_monoid_class: monoid_class addition) ->
         (#[Tactics.Typeclasses.tcresolve ()] multiplication_monoid_class: monoid_class multiplication) ->
         ring #a
 
/// Now we would very much like to get ring 0 and ring 1
let zero_of (#a: Type) (r: ring #a) : neutral_element_for #a r.addition.op r.eq = r.addition_monoid_class.neutral
let one_of  (#a: Type) (r: ring #a) : neutral_element_for #a r.multiplication.op r.eq = r.multiplication_monoid_class.neutral
let is_zero_of (#a: Type) (r: ring #a) (x: a) = r.eq x (zero_of r)
let is_one_of (#a: Type) (r: ring #a) (x: a) = r.eq x (one_of r)
type nonzeros_of (#a:Type) (r: ring #a) = (x:a{~(is_zero_of r x)})

class domain_class (#a: Type) (r: ring #a) =
{
  one_is_not_zero : unit -> Lemma (~ (r.eq (zero_of r) (one_of r)));
  no_zero_divisors_p : (x: a) -> (y: a) -> Lemma (requires (is_zero_of r (r.multiplication.op x y)))
                                               (ensures (is_zero_of r x \/ is_zero_of r y));
  no_zero_divisors : unit -> Lemma(forall(x y: a). (is_zero_of r (r.multiplication.op x y)) ==> (is_zero_of r x) \/ (is_zero_of r y))
}

type domain (#a: Type) = x:ring #a{domain_class x}
type commutative_domain (#a: Type) = x:domain #a{commutative_magma_class x.multiplication}

type nonzero_defined_func (#a: Type) (d: commutative_domain #a) = f:(a -> option nat){ forall(x:a). ((f x) == None <==> (is_zero_of d x)) }

type domain_restricted_func (#a: Type) (pred: predicate #a) (f: a -> nat) = 
  fun (x:a) -> if pred x then Some (f x) else None





type euclidean_norm_func (#a: Type) (d: commutative_domain #a) = f: nonzero_defined_func d{
  (forall (x y: nonzeros_of d). Some?.v (f x) >= 0   )
 }

class euclidean_domain_class (#a: Type) (d: domain #a{commutative_magma_class d.multiplication}) =
{
  euclidean_norm: (f: (a -> option nat){forall(z:a). (f z) == None ==> d.eq d.addition_monoid_class.neutral z })
}


type euclidean_domain (#a: Type) = x:commutative_domain #a{euclidean_domain_class x}

let gcd (#a: Type) (d: euclidean_domain #a) {| euclidean_domain_class d |} {| group_class d.addition |} = 
  d.addition_monoid_class.neutral

type denominator_type (#a: Type) (d: ring #a) = 
  t:a{~(d.eq d.addition_monoid_class.neutral t)}
  
let inverse_condition_lemma p1 p2 (q:unit -> Lemma (requires p1) (ensures p2))
  : Lemma (requires ~p2) (ensures ~p1)
  = FStar.Classical.move_requires q ()
  
let domain_lemma (#a: Type) (d: domain #a) {| dc: domain_class d |} (x: denominator_type d) (y: denominator_type d) : Lemma (~(d.eq d.addition_monoid_class.neutral (d.multiplication.op x y))) = 
  let zero = d.addition_monoid_class.neutral in
  let f_lem = dc.no_zero_divisors() in
  let direct_lemma (p: a) (q: a) : Lemma (d.eq zero (d.multiplication.op p q) ==>  (d.eq p zero) \/ (d.eq q zero)) = () in
  let inv_lemma = inverse_condition_lemma ((d.eq x zero) \/ (d.eq y zero)) (d.eq zero (d.multiplication.op x y)) in  
()
 
type fraction (#a: Type) (dom: commutative_domain #a) = 
{
  numerator: a;
  denominator: denominator_type #a dom
}

 
let frac_add (#a: Type) (#d: commutative_domain #a) {| dc: domain_class d |} (x: fraction #a d) (y: fraction #a d) : fraction #a d =
  let ( * ) = d.multiplication.op in
  let ( + ) = d.addition.op in 
  let _ = domain_lemma d x.denominator y.denominator in
  { 
    numerator = (x.numerator * y.denominator) + (y.numerator * x.denominator);
    denominator = (x.denominator * y.denominator)
  }

let frac_add_inv (#a: Type) (#d: commutative_domain #a) {| ag: group_class d.addition |} (x: fraction d) : fraction d = 
  { numerator = ag.inverse x.numerator; denominator = x.denominator }

let frac_sub (#a: Type) (#d: commutative_domain #a) {| dc: domain_class d |} {| ag: group_class d.addition |} (x: fraction #a d) (y: fraction #a d) : (t: fraction d{ d.eq t.numerator ((x.numerator `d.multiplication.op` y.denominator) `d.addition.op` (ag.inverse (y.numerator `d.multiplication.op` x.denominator))) /\ d.eq t.denominator (x.denominator `d.multiplication.op` y.denominator)  }) =
  let ( * ) = d.multiplication.op in
  let ( + ) = d.addition.op in 
  let _ = domain_lemma d x.denominator y.denominator in
  { 
    numerator = (x.numerator * y.denominator) + (ag.inverse (y.numerator * x.denominator));
    denominator = (x.denominator * y.denominator)
  }

let frac_sub_numerator_expression (#a: Type) (#d: commutative_domain #a) {| ag: group_class d.addition |} (x: fraction d) (y: fraction d) = 
  (x.numerator `d.multiplication.op` y.denominator) `d.addition.op` (ag.inverse (x.denominator `d.multiplication.op` y.numerator))


let frac_mul (#a: Type) (#d: commutative_domain #a) {| dc: domain_class d |} (x: fraction d) (y: fraction d) : fraction d =
  let ( * ) = d.multiplication.op in
  let _ = domain_lemma d x.denominator y.denominator in
  {
    numerator = x.numerator * y.numerator;
    denominator = x.denominator * y.denominator
  }

let frac_eq (#a: Type) (#d: commutative_domain #a) {| dc: domain_class d |} {| ag: group_class d.addition |} : (fraction d -> fraction d -> bool) = 
  fun f1 f2 -> 
    let diff = frac_sub f1 f2 in
   // d.eq diff.numerator d.addition_monoid_class.neutral
    d.eq (d.multiplication.op f1.numerator f2.denominator) (d.multiplication.op f2.numerator f1.denominator)

let frac_eq_is_symmetric (#a: Type) (#d: commutative_domain #a) {| dc: domain_class d |} {| ag: group_class d.addition |} 
  : Lemma(is_symmetric (frac_eq #a #d)) = ()

let frac_eq_is_reflexive (#a: Type) (#d: commutative_domain #a) {| dc: domain_class d |} {| ag: group_class d.addition |} 
  : Lemma(is_reflexive (frac_eq #a #d)) = ()

let frac_eq_is_transitive (#a: Type) (#d: commutative_domain #a) {| dc: domain_class d |} {| ag: group_class d.addition |} 
  : Lemma(is_transitive (frac_eq #a #d)) = 
    let fraction = fraction #a d in
    let eq = frac_eq #a #d #dc #ag in
    let add = frac_add #a #d #dc in
    let aux (x: fraction) (y: fraction{eq x y}) (z: fraction{eq y z}) : Lemma (eq x z) =    
      admit(); //why can't F* admit this?      
      () in
  ()



/// Below we test things against integers

let int_add : magma #int = Mkmagma (+) (=)
instance ints_add_sg : semigroup_class int_add = { op_is_associative = trivial_ternary_lemma }
instance ints_add_co : commutative_magma_class int_add = { op_is_commutative = trivial_binary_lemma }
instance ints_add_mo : monoid_class int_add = { is_semigroup = ints_add_sg; neutral = 0 }
instance ints_add_gr : group_class int_add = Mkgroup_class ints_add_mo (fun x -> (-x))
instance ints_add_cg : commutative_group_class int_add = Mkcommutative_group_class ints_add_co ints_add_gr
let ints_add_cg_e = make_commutative_group int_add

let int_mul : magma #int = Mkmagma op_Multiply (=)
instance ints_mul_sg : semigroup_class int_mul = { op_is_associative = trivial_ternary_lemma }
instance ints_mul_mo : monoid_class int_mul = { is_semigroup = ints_mul_sg; neutral = 1 }
let ints_mul_mo_e : (t:monoid #int{(eq_of t) == (=)}) = make_monoid int_mul

let _ = assert (eq_of ints_add_cg_e == eq_of ints_mul_mo_e)
let left_d = left_distributive_over (=) ints_mul_mo_e ints_add_cg_e
let right_d = right_distributive_over (=) ints_mul_mo_e ints_add_cg_e
let fully_d = fully_distributive_over (=) ints_mul_mo_e ints_add_cg_e

let rdd () : Lemma (right_d) = FStar.Classical.forall_intro_3 (fun x y z -> FStar.Math.Lemmas.distributivity_add_left x y z)
let ldd () : Lemma (left_d) = FStar.Classical.forall_intro_3 (fun x y z -> FStar.Math.Lemmas.distributivity_add_right x y z)
//let follow() : Lemma (left_d /\ right_d ==> fully_d) = ()
//let fdd() : squash(fully_d) = ldd(); rdd() //;  follow()

let cond : squash(fully_distributive_over (=) ints_mul_mo_e ints_add_cg_e) = rdd(); ldd(); ()
let int_ring = Ring (=) ints_add_cg_e ints_mul_mo_e 

let int_is_dom (x: int) (y: int) : Lemma (x `op_Multiply` y = 0 ==> (x = 0) \/ (y = 0)) = ()

instance int_domain_class : domain_class int_ring = { 
  no_zero_divisors = (fun () -> ()); 
  no_zero_divisors_p = (fun x y -> int_is_dom x y); 
  one_is_not_zero = (fun () -> assert(~(0=1)); ())
}
let int_domain {| d: domain_class int_ring |} : domain #int = int_ring 

let int_norm (x: int) : option nat = if x = 0 then None else Some (if x<0 then (-x) else x)

instance ints_mul_co : commutative_magma_class int_domain.multiplication = { op_is_commutative = trivial_binary_lemma }

let int_comm_dom {| commutative_magma_class int_domain.multiplication |} : commutative_domain #int = int_domain

let int_comm_dom_val = int_comm_dom

instance int_euc_dom_inst : euclidean_domain_class int_comm_dom_val = { euclidean_norm = int_norm }

let int_euc_dom {| euclidean_domain_class int_comm_dom_val |} : euclidean_domain #int = int_comm_dom_val

let int_euc_dom_val = int_euc_dom

type rat = fraction #int int_euc_dom_val
//let frac_ring (#a: Type) (#d: commutative_domain #a) {| dc: domain_class d |} : ring #(fraction d) = Ring  
