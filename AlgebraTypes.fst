module AlgebraTypes

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1"

type binary_op (a:Type) = a -> a -> a
type unary_op (a:Type) = a -> a
type predicate (a:Type) = a -> bool
type binary_relation (a: Type) = a -> a -> bool

let is_reflexive  (#a:Type) (r: binary_relation a) = forall (x:a).     x `r` x
let is_symmetric  (#a:Type) (r: binary_relation a) = forall (x y:a).   x `r` y           <==> y `r` x
let is_transitive (#a:Type) (r: binary_relation a) = forall (x y z:a). x `r` y /\ y `r` z ==> x `r` z 

/// We do this for future work with fractions over arbitrary domains.
/// Where there is no GCD computation, there's no reducing a/a to 1/1
/// (or 0/a to 0/1), and we'll use the custom equivalence relation,
/// (a/b)=(c/d) ==def== (ad=bc). The three properties shall be then proven explicitly.
type equivalence_relation (a: Type) = r:binary_relation a{is_reflexive r /\ is_symmetric r /\ is_transitive r}

let equivalence_wrt_condition (#a: Type) (op: binary_op a) (eq: equivalence_relation a) = 
  (forall (x y z:a). (x `eq` y) <==> ((x `op` z) `eq` (y `op` z))) /\
  (forall (x y z:a). (x `eq` y) <==> ((z `op` x) `eq` (z `op` y)))
  
type equivalence_wrt (#a: Type) (op: binary_op a) = eq:equivalence_relation a{equivalence_wrt_condition op eq}

let equivalence_is_symmetric (#a:Type) (eq: equivalence_relation a) (x:a) (y:a{x `eq` y})
  : Lemma (x `eq` y == y `eq` x) = ()

/// Here, we define basic axioms of algebraic structures in form of propositions
/// about operations and elements. 
///
/// The forall part has precisely the meaning we expect it to have :)
/// From here, one can deduce what an exists statement would look like...
let is_associative (#a:Type) (op:binary_op a) (eq: equivalence_relation a) = forall (x y z:a). ((x `op` y) `op` z) `eq` (x `op` (y `op` z))
let is_commutative (#a:Type) (op:binary_op a) (eq: equivalence_relation a) = forall (x y:a). (x `op` y) `eq` (y `op` x)

let associative_operation_lemma (#a:Type) (eq: equivalence_relation a) (op:binary_op a{is_associative op eq}) (x y z:a) : Lemma (((x `op` y) `op` z) `eq` (x `op` (y `op` z)))
  = ()

let commutative_substitution_lemma (#a:Type) (#eq: equivalence_relation a) (op: binary_op a{is_commutative op eq}) 
  (x y z: a) : Lemma (x `eq` (y `op` z) == x `eq` (z `op` y)) = ()

let associative_lemma_for_substitution (#a:Type) (eq: equivalence_relation a)
  (op: binary_op a{is_associative op eq}) (x y z w: a)
  : Lemma ( ((x `op` y) `op` z) `eq` w == (x `op` (y `op` z)) `eq` w) = ()

let is_idempotent (#a:Type) (r: unary_op a) (eq: equivalence_relation a)  = forall (x:a). (r x) `eq` (r (r x))

/// Things quickly get funny if we consider non-associative structures (magmas etc).
/// Therefore we don't, not because we dislike fun, but because we strive for sanity.

let is_left_id_of  (#a:Type) (u:a) (op:binary_op a) (eq: equivalence_relation a) = forall (x:a). (u `op` x) `eq` x // left identity
let is_right_id_of (#a:Type) (u:a) (op:binary_op a) (eq: equivalence_relation a) = forall (x:a). (x `op` u) `eq` x // right identity
let is_neutral_of  (#a:Type) (u:a) (op:binary_op a) (eq: equivalence_relation a) = is_left_id_of u op eq /\ is_right_id_of u op eq // neutral element
let is_inverse_element_of (#a: Type) (op: binary_op a) (eq: equivalence_relation a) (neutral: a) (x: a) (y: a) 
  = ((x `op` y) `eq` neutral) /\ ((y `op` x) `eq` neutral)
let is_invertible_element_of (#a: Type) (op: binary_op a) (eq: equivalence_relation a) (neutral: a) (x: a) 
  = exists (y: a). (is_inverse_element_of op eq neutral x y)
type neutral_element_of (#a: Type) (op: binary_op a) (eq: equivalence_relation a) = (x:a{is_neutral_of x op eq})

/// The notion of absorbing element, or absorber, is the generalization of integer zero with respect to multiplication
/// That is, 0x = x0 = 0. Other exmaples are the empty set w.r.t. intersection, 1 w.r.t. GCD in naturals, etc.
let is_absorber_of (#a:Type) (z:a) (op:binary_op a) (eq: equivalence_relation a) = forall (x:a). ((x `op` z) `eq` z) && ((z `op` x) `eq` z)
type absorber_of (#a:Type) (op:binary_op a) (eq: equivalence_relation a) = z:a{is_absorber_of z op eq}
type non_absorber_of (#a:Type) (op: binary_op a) (eq: equivalence_relation a) = z:a{~(is_absorber_of z op eq)}

let absorber_lemma (#a:Type) (op:binary_op a) (eq: equivalence_relation a) (z: a{is_absorber_of z op eq}) (x:a)
  : Lemma ((z `op` x) `eq` z /\ (x `op` z) `eq` z) = ()

/// Proving that in any magma, there may not be 2 distinct absorbers, is left as an exercise to both Z3 and the reader.
/// And Z3 is doing fine on that account, just saying.
let absorber_is_unique (#a:Type) (op: binary_op a) (eq: equivalence_relation a) (z1 z2: absorber_of op eq) : Lemma (eq z1 z2) = ()

let absorber_eq_is_also_absorber (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) (absorber: absorber_of op eq)
(other:a{eq other absorber}) : Lemma (is_absorber_of other op eq) = ()

/// Since we are using custom equivalence relation, we specifically assure the existence of
/// the unit. We also write "forall" since, for example, for fractions, there'll also be neutral
/// elements of type a/a, b/b... for nonzero (a, b...), unless we operate in a euclidean domain
/// that offers the algorithm for GCD computation and thus the notion of reduced fractions.
///
/// For arbitrary domains, there is no hope of reduced fractions, so the notions for inverses and neutrals
/// stays in its most general form.
let is_inverse_operation_for (#a: Type) (inv: unary_op a) (op: binary_op a) (eq: equivalence_relation a) 
  = (exists (at_least_one_neutral: a). is_neutral_of at_least_one_neutral op eq) /\
    (forall (u: neutral_element_of op eq) (x: a). ((x `op` (inv x)) `eq` u) /\ (((inv x) `op` x) `eq` u))

/// The inverse operation type is also a refinement for arbitrary unary operation 
type inverse_op_for (#a: Type) (op: binary_op a) (eq: equivalence_relation a) 
  = (inv:unary_op a{is_inverse_operation_for inv op eq})

/// We shall generally keep in mind that distributivity laws must be considered separately
/// If in future we consider K[x] with multiplication f(x)*g(x) defined as composition f(g(x)),
/// we will do well to remember that only one of the two distributivities holds there.
let is_right_distributive (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) (eq: equivalence_relation a) =
  forall (x y z:a). (x `op_mul` (y `op_add` z)) `eq` ((x `op_mul` y) `op_add` (x `op_mul` z))
let is_left_distributive (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) (eq: equivalence_relation a) =
  forall (x y z:a). ((x `op_add` y) `op_mul` z) `eq` ((x `op_mul` z) `op_add` (y `op_mul` z))
let is_fully_distributive (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) (eq: equivalence_relation a) =
  (is_right_distributive op_mul op_add eq) /\ (is_left_distributive op_mul op_add eq) 

/// Domain defining property (the alternative form is the Cancellation Law, (ax=bx ==> (x=0 \/ a=b)
let has_no_zero_divisors (#a:Type) (zero:a) (op_mul: binary_op a) (eq: equivalence_relation a)=
  forall (x y:a). ((x `op_mul` y) `eq` zero) ==> (x `eq` zero) \/ (y `eq` zero)
/// For future reference, we difine what it means for divisor to divide dividend
let is_divisor_of (#a:Type) (op_mul: binary_op a) (eq: equivalence_relation a) (divisor: a) (dividend: a) = 
  exists (quotient: a). (quotient `op_mul` divisor) `eq` dividend


/// We provide the two lemmas that ensure divides, second one purely to
/// demonstrate how one uses exists_intro. Usually you're fine with '= ()'.
let inst_divides (#a:Type) (op_mul: binary_op a) (eq: equivalence_relation a) (y: a) (x: a) (z:a{(z `op_mul` y) `eq` x})
  : Lemma (is_divisor_of op_mul eq y x) = ()
/// explicitly stated version showcases FStar.Classical.exists_intro
let inst_divides_2 (#a:Type) (op_mul: binary_op a) (eq: equivalence_relation a) (y: a) (x: a) (z:a{(z `op_mul` y) `eq` x})
  : Lemma (is_divisor_of op_mul eq y x) = FStar.Classical.exists_intro (fun z -> (z `op_mul` y) `eq` x) z

/// This will soon be used as we'll represent elements in form of x=(unit_part)*(normal_part)
/// where (unit_part) is a ring unit, and (normal_part) is, roughly speaking, (unit_part⁻¹ * x),
/// so that normal part would represent absolute value, monic polynomial, etc.
/// If you're curious as to where did these (not so often used!) notions came from,
/// see the book "Algorithms for Computer Algebra" by Geddes, Czapor, Labahn.
/// You'll find quite a lot of interesting notions there.
///
/// we denote the unit u, because the word `unit` is reserved in F*
/// Invertible elements in a ring are called units, and here's their defining condition
let is_unit (#a: Type) (x: a) (op:binary_op a) (eq: equivalence_relation a) 
  = exists (y:a). (is_neutral_of (x `op` y) op eq /\ is_neutral_of (y `op` x) op eq)
/// A zero of a ring is the neutral element of the ring's additive group,
/// and here's the special property we might need in the future
let is_zero (#a: Type) (z: a) (op_mul: binary_op a) (eq: equivalence_relation a) = forall (x: a). ((x `op_mul` z) `eq` z) /\ ((z `op_mul` x) `eq` z)
/// We call the two elements associated if they divide each other
let are_associated (#a: Type) (p: a) (q: a) (op_mul: binary_op a) (eq: equivalence_relation a) = (is_divisor_of op_mul eq p q) /\ (is_divisor_of op_mul eq q p) 

/// We also define in advance the notions of irreducibles and primes
/// We don't tell one from the other in Z, but in general, they are not the same thing.
let is_irreducible (#a: Type) (x: a) (op_mul: binary_op a) (eq: equivalence_relation a) = 
  (~(is_unit x op_mul eq)) /\
  (exists (neutral: a). is_neutral_of neutral op_mul eq) /\  
  (forall (p q: a). ((q `op_mul` p) `eq` x) ==> ( (are_associated p x op_mul eq) /\ (is_unit q op_mul eq)) 
                                      \/ ((are_associated q x op_mul eq) /\ (is_unit p op_mul eq)))
                                      
let is_prime (#a: Type) (p: a) (one: a) (op_mul: binary_op a) (eq: equivalence_relation a) = 
  (~(is_unit p op_mul eq)) /\ (forall (m n: a). (is_divisor_of op_mul eq p (m `op_mul` n)) ==> ((is_divisor_of op_mul eq p m) \/ (is_divisor_of op_mul eq p n)))

let respects_equivalence (#a:Type) (f: unary_op a) (eq: equivalence_relation a) = 
  forall (x y:a). (x `eq` y) ==> (f x) `eq` (f y)

noeq type magma (#a: Type) = 
{
  op: binary_op a;
  eq: equivalence_wrt op;
  inv: (t:unary_op a{ respects_equivalence t eq });
  neutral: a
}
type semigroup (#a:Type)             = g: magma #a{is_associative g.op g.eq}
type commutative_magma (#a:Type)     = g: magma #a{is_commutative g.op g.eq}
type commutative_semigroup (#a:Type) = g: semigroup #a{is_commutative g.op g.eq}
type monoid (#a:Type)                = g: semigroup #a{is_neutral_of g.neutral g.op g.eq}
type commutative_monoid (#a:Type)    = g: monoid #a{is_commutative g.op g.eq}
type group (#a:Type)                 = g: monoid #a{is_inverse_operation_for g.inv g.op g.eq}
type commutative_group (#a:Type)     = g: group #a{is_commutative g.op g.eq}


/// If you see something trivial, then it is either here to reduce the rlimit for some bigger lemma,
/// or a leftover from time where something didn't verify and I made more and more explicit lemmas,
/// or it should be deleted. I periodically cleanup this file and remove unused lemmas.
/// Nothing big gets removed anyway.

let neutral_is_unique (#a:Type) (g: semigroup #a) (u: neutral_element_of g.op g.eq) (v: neutral_element_of g.op g.eq) : Lemma (g.eq u v) = ()

let neutral_equivalent_is_neutral (#a:Type) (op: binary_op a) (eq: equivalence_wrt op ) (x: neutral_element_of op eq) (y: a{y `eq` x}) : Lemma (is_neutral_of y op eq) = 
  let aux_right (t: a) : Lemma ((t `op` y) `eq` t) = 
    assert (y `eq` x);
    assert (forall (p q r:a). (p `eq` q) <==> ((p `op` r) `eq` (q `op` r)));
    assert (t `op` x `eq` t);
    assert ((t `op` y) `eq` (t `op` x));
    assert ((t `op` y) `eq` t);
    () in
  let aux_left (t: a) : Lemma ((y `op` t) `eq` t) = 
    assert (y `eq` x);
    assert (forall (p q r:a). (p `eq` q) <==> ((r `op` p) `eq` (r `op` q)));
    assert (x `op` t `eq` t);
    assert ((y `op` t) `eq` (x `op` t));
    assert ((y `op` t) `eq` t);
    () in
  FStar.Classical.forall_intro aux_left;
  FStar.Classical.forall_intro aux_right;
  assert (is_neutral_of y op eq);
  ()
/// FStar does not automatically apply lemmas on equivalence being symmetric reflexive and transitive.
/// So, I at least make my lemmas such that I care about `eq` operand order as little as possible
let equivalence_wrt_operation_lemma (#a: Type) (#op: binary_op a) (eq: equivalence_wrt op) (e1 e2 z: a)
  : Lemma 
  (requires e1 `eq` e2 \/ e2 `eq` e1) 
  (ensures 
    (e1 `op` z) `eq` (e2 `op` z) /\    
    (e2 `op` z) `eq` (e1 `op` z) /\    
    (z `op` e1) `eq` (z `op` e2) /\
    (z `op` e2) `eq` (z `op` e1)) = ()
let equivalence_wrt_operation_lemma_inverse (#a: Type) (#op: binary_op a) (eq: equivalence_wrt op) (e1 e2 z: a)
  : Lemma 
  (requires 
    ((e1 `op` z) `eq` (e2 `op` z) \/ (e2 `op` z) `eq` (e1 `op` z)) /\ 
    ((z `op` e1) `eq` (z `op` e2) \/ (z `op` e2) `eq` (z `op` e1))) 
  (ensures e1 `eq` e2 /\ e2 `eq` e1) = ()
let equivalence_wrt_operation_lemma_twoway (#a: Type) (#op: binary_op a) (eq: equivalence_wrt op) (e1 e2 z: a)
  : Lemma ((e1 `op` z) `eq` (e2 `op` z) /\    
           (e2 `op` z) `eq` (e1 `op` z) /\    
           (z `op` e1) `eq` (z `op` e2) /\
           (z `op` e2) `eq` (z `op` e1)
           <==> 
            e1 `eq` e2 /\ e2 `eq` e1) = ()

/// When I try to keep the rlimit at minimum, lemmas like this one sometimes help
let neutral_inverse_is_neutral (#a:Type) (g: group #a) : Lemma (g.neutral `g.eq` (g.inv g.neutral)) =  
  assert ((g.neutral `g.op` (g.inv g.neutral)) `g.eq` g.neutral)

/// In our pursuit of sanity, we only consider ring-like structures that are at least rigs,
/// with addition forming a commutative group, and multiplication forming a semigroup that
/// is fully (left and right) distributive over addition
/// 
/// Notice how, just like inverse group operation, the euclidean_norm field holds little meaning
/// until we get to Euclidean Domains, but we shall keep the record field in the base type
/// because there is no inheritance in F*. Unfortunately so, to say the least.

let nat_function_defined_on_non_absorbers (#a:Type) (op: binary_op a) (eq: equivalence_relation a) = f: (a -> (option nat)){ forall (x:a). (f x)=None ==> is_absorber_of x op eq }

#push-options "--ifuel 1 --fuel 0 --z3rlimit 1"
let nat_function_value (#a:Type) (op: binary_op a) (eq: equivalence_relation a) (f: nat_function_defined_on_non_absorbers op eq) (x: non_absorber_of op eq) : nat =   
  Some?.v (f x)
#pop-options

let has_no_absorber_divisors (#a:Type) (op: binary_op a) (eq: equivalence_relation a) = forall (x y: a). is_absorber_of (op x y) op eq <==> (is_absorber_of x op eq) \/ (is_absorber_of y op eq)

let domain_multiplication_law (#a:Type) (eq: equivalence_relation a) (mul: binary_op a{has_no_absorber_divisors mul eq}) (x y: non_absorber_of mul eq)
  : Lemma ( ~ (is_absorber_of (mul x y) mul eq) ) = ()
 
let euclidean_norm_property (#a:Type) (eq: equivalence_relation a) (mul: binary_op a{has_no_absorber_divisors mul eq}) (x y: non_absorber_of mul eq) (f: nat_function_defined_on_non_absorbers mul eq) = 
  domain_multiplication_law eq mul x y;
  nat_function_value mul eq f (mul x y) >= nat_function_value mul eq f x 

let euclidean_norm_forall_property (#a:Type) (eq: equivalence_relation a) (mul: binary_op a{has_no_absorber_divisors mul eq}) (f: nat_function_defined_on_non_absorbers mul eq)
  = forall (x y: non_absorber_of mul eq). euclidean_norm_property eq mul x y f

type norm_function (#a:Type) (eq: equivalence_relation a) (mul: binary_op a{has_no_absorber_divisors mul eq})
  = f: nat_function_defined_on_non_absorbers mul eq{ forall (x y: non_absorber_of mul eq). euclidean_norm_property eq mul x y f }

#push-options "--ifuel 1 --fuel 0 --z3rlimit 1"
let euclidean_norm_main_lemma (#a: Type) (eq: equivalence_relation a) (mul: binary_op a{has_no_absorber_divisors mul eq}) (f: norm_function eq mul) (x y: non_absorber_of mul eq)
  : Lemma (Some?.v (f (mul x y)) >= Some?.v (f x)) = assert (euclidean_norm_property eq mul x y f)
let test (a:Type) (eq:equivalence_relation a) (mul: binary_op a{has_no_absorber_divisors mul eq}) (f:norm_function eq mul) : Lemma ( 
  forall (x y: non_absorber_of mul eq). Some?.v (f (mul x y)) >= Some?.v (f x) ) = FStar.Classical.forall_intro_2 (euclidean_norm_main_lemma eq mul f)
#pop-options

let eq_of (p: magma) = p.eq

//#push-options "--ifuel 4 --fuel 4 --z3rlimit 15"

let yields_units (#a: Type) (f: a->a) (mul: binary_op a) (eq: equivalence_relation a) = 
  forall (x:a). is_unit (f x) mul eq

let unary_distributivity (#a: Type) (f: a->a) (op: binary_op a) (eq: equivalence_relation a) (x y: a)
 = (f (x `op` y)) `eq` ((f x) `op` (f y))

let unary_distributes_over (#a: Type) (f: a->a) (op: binary_op a) (eq: equivalence_relation a) = 
  forall (x y: a). unary_distributivity f op eq x y

let unary_over_nonzeros_distributes_over (#a: Type) (f: a->a) (op: binary_op a) (eq: equivalence_relation a) = 
  forall (x y: non_absorber_of op eq). unary_distributivity f op eq x y

let un_distr_l (#a: Type) (op: binary_op a) (eq: equivalence_relation a) (f: (t:(a->a){ unary_over_nonzeros_distributes_over t op eq})) (x y: non_absorber_of op eq)  : Lemma (unary_distributivity f op eq x y) = ()

type units_of (#a: Type) (mul: binary_op a) (eq: equivalence_relation a) = x:a{is_unit x mul eq}

let is_unit_part_function (#a: Type) (#mul: binary_op a) (#eq: equivalence_wrt mul) (f: a -> units_of mul eq) = 
  is_idempotent f eq /\
  yields_units f mul eq /\
  respects_equivalence f eq /\
  unary_over_nonzeros_distributes_over f mul eq

type unit_part_function (#a: Type) (mul: binary_op a) (eq: equivalence_wrt mul) = f:(a -> units_of mul eq){ is_unit_part_function f }

let un_op_distr_lemma (#a:Type) (mul: binary_op a) (eq: equivalence_wrt mul) (f: unit_part_function mul eq)
  : Lemma (unary_over_nonzeros_distributes_over f mul eq) = ()

let un_op_distr_lemma_p (#a:Type) (mul: binary_op a) (eq: equivalence_wrt mul) (f: unit_part_function mul eq) (x y: non_absorber_of mul eq)
  : Lemma (unary_distributivity f mul eq x y) = un_op_distr_lemma mul eq f

let is_unit_normal (#a:Type) (mul: binary_op a) (eq: equivalence_wrt mul) (unit_part_func: a -> a) (x:a) = is_neutral_of (unit_part_func x) mul eq

let yields_unit_normals (#a:Type) (mul: binary_op a) (eq: equivalence_wrt mul) (unit_part_func: a -> a) (f: a -> a) =
  forall (x:a). is_unit_normal mul eq unit_part_func (f x)

type unit_normals_of (#a: Type) (mul: binary_op a) (eq: equivalence_wrt mul) (unit_part_func: a -> a) = x:a { is_unit_normal mul eq unit_part_func x }

let is_normal_part_function (#a:Type) (#mul: binary_op a) (#eq: equivalence_wrt mul) (unit_part_func: a -> a) (f: a -> unit_normals_of mul eq unit_part_func) = 
  is_idempotent f eq /\
  respects_equivalence f eq /\
  yields_unit_normals mul eq unit_part_func f /\
  unary_distributes_over f mul eq


type normal_part_function (#a: Type) (#mul: binary_op a) (#eq: equivalence_wrt mul) (unit_part_func: a -> a)
  = f:(a -> (unit_normals_of mul eq unit_part_func)){ is_normal_part_function unit_part_func f }


let unit_part_func_of_product_is_product_of_unit_parts (#a: Type) (#mul: binary_op a) (#eq: equivalence_wrt mul)
  (unit_part_func: unit_part_function mul eq) (x y: non_absorber_of mul eq) 
  : Lemma((unit_part_func (x `mul` y)) `eq` ((unit_part_func x) `mul` (unit_part_func y))) = 
  un_op_distr_lemma_p mul eq unit_part_func x y;
  ()

#push-options "--ifuel 0 --fuel 0 --z3rlimit 2"
let product_of_unit_normals_is_normal (#a: Type) (#mul: binary_op a) (#eq: equivalence_wrt mul)
  (unit_part_func: unit_part_function mul eq)
  (x y: (t:unit_normals_of mul eq unit_part_func{~(is_absorber_of t mul eq) }))
  : Lemma (is_unit_normal mul eq unit_part_func (x `mul` y)) =
  // assert (is_neutral_of (unit_part_func x) mul eq);
  // assert (is_neutral_of (unit_part_func y) mul eq);
  // assert (~(is_absorber_of x mul eq));
  // assert (~(is_absorber_of y mul eq));
  un_op_distr_lemma_p mul eq unit_part_func x y;
  assert (unit_part_func (mul x y) `eq` (mul (unit_part_func x) (unit_part_func y)));
  neutral_equivalent_is_neutral mul eq (unit_part_func x) (unit_part_func (mul x y)) ;
  // assert (is_neutral_of (unit_part_func (mul x y)) mul eq);
  assert_spinoff (is_unit_normal mul eq unit_part_func (x `mul` y))
#pop-options

type test_unit_part_func (#a: Type) (mul: binary_op a) (eq: equivalence_wrt mul) = unit_part_function mul eq

#push-options "--ifuel 0 --fuel 0 --z3rlimit 5"
noeq type ring (#a: Type) = {
  addition: commutative_group #a;
  multiplication: (t: monoid #a {is_fully_distributive t.op addition.op t.eq /\ is_absorber_of addition.neutral t.op t.eq });
  eq: (t:equivalence_relation a{ equivalence_wrt_condition addition.op t /\ equivalence_wrt_condition multiplication.op t /\ t===addition.eq /\ t===multiplication.eq });
  unit_part_of: a -> units_of multiplication.op eq;
  normal_part_of: a -> unit_normals_of multiplication.op eq unit_part_of; // normal_part_function #a #multiplication.op #eq unit_part_of;
  euclidean_norm: nat_function_defined_on_non_absorbers multiplication.op eq 
}

let neut_lemma (#a: Type) (r: ring #a) : Lemma (is_neutral_of r.multiplication.neutral r.multiplication.op r.eq) = ()


#push-options "--ifuel 2 --fuel 2 --z3rlimit 10"
let mul_neutral_lemma (#a: Type) (r: ring #a) (x: a{is_neutral_of x r.multiplication.op r.eq})
  : Lemma (r.eq x r.multiplication.neutral)
  = 
    neut_lemma r;
    assert (is_neutral_of r.multiplication.neutral r.multiplication.op r.eq);
    neutral_equivalent_is_neutral r.multiplication.op r.eq r.multiplication.neutral x;
    ()
    

let is_zero_of (#a: Type) (r: ring #a) (x: a) = is_absorber_of x r.multiplication.op r.eq

let two_zeros_are_equal (#a:Type) (r: ring #a) (x y: (t:a{r.eq t r.addition.neutral})) 
  : Lemma (x `r.eq` y) = ()

let zero_is_equal_to_add_neutral (#a:Type) (r: ring #a) 
  : Lemma (forall (x:a). is_zero_of r x <==> r.eq x r.addition.neutral) = ()

let nonzero_is_equal_to_add_neutral (#a:Type) (r: ring #a) 
  : Lemma (forall (x:a). ~(is_zero_of r x) <==> ~(r.eq x r.addition.neutral)) = ()
  
let zero_is_equal_to_add_neutral_p (#a:Type) (r: ring #a) (z: a)
  : Lemma (is_absorber_of z r.multiplication.op r.eq <==> r.eq z r.addition.neutral) = zero_is_equal_to_add_neutral r

let nonzero_is_not_equal_to_add_neutral_p (#a:Type) (r: ring #a) (z: a)
  : Lemma (~(is_absorber_of z r.multiplication.op r.eq) <==> ~(r.eq z r.addition.neutral)) = zero_is_equal_to_add_neutral r

type domain (#a: Type) = r:ring #a { has_no_absorber_divisors r.multiplication.op r.eq }


let dom_prod_zero_lemma (#a:Type) (dom: domain #a) (p q: a) 
  : Lemma (requires (p `dom.multiplication.op` q) `dom.eq` dom.addition.neutral)
          (ensures (p `dom.eq` dom.addition.neutral \/ q `dom.eq` dom.addition.neutral)) =           
          ()

type commutative_ring (#a: Type) = r:ring #a { is_commutative r.multiplication.op r.eq }

/// I'm not 100% sure, but somehow I think that PERHAPS unit/normal part functions
/// are safe to expect to be defined over any integral domain. Still, for safety sake,
/// I restricted all that to euclidean domains.
///
/// When I lift that restriction, the fraction library will of course move from
/// using euclidean domains to using arbitrary integral domains.
///
/// The special case of euclidean domains, which allows for reduced fractions, will be handled
/// differently, and all arithmetics will also account for the gcd/eea availability.
/// 
type integral_domain (#a: Type) = r:domain #a { is_commutative r.multiplication.op r.eq }

type euclidean_domain (#a:Type) = r:integral_domain #a 
{ 
  euclidean_norm_forall_property r.eq r.multiplication.op r.euclidean_norm /\
  is_unit_part_function r.unit_part_of /\
  is_normal_part_function r.unit_part_of r.normal_part_of  
}

