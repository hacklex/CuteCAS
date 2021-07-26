module RefinedAlgebra

open FStar.Math.Lemmas

/// We will actively use these when working with our abstract algebra structures
/// You might want to compare the arrow types to those from F#, for example
type binary_op (a:Type) = a -> a -> a
type unary_op (a:Type) = a -> a
type predicate (a:Type) = a -> bool
type binary_relation (a: Type) = a -> a -> bool

let is_reflexive (#a:Type) (r: binary_relation a) = forall (x:a). r x x
let is_symmetric (#a:Type) (r: binary_relation a) = forall (x y:a). r x y <==> r y x
let is_transitive (#a:Type) (r: binary_relation a) = forall (x y z:a). r x y /\ r y z ==> r x z 

type equivalence_relation (a: Type) = r:binary_relation a{is_reflexive r /\ is_symmetric r /\ is_transitive r}

/// Base for all group-like structures. Before we get to groups, inverse operation holds little meaning...
///
/// The prefix "noeq" means we can only compare semigroup-like structure instances (not the elements!)
/// with propositional equality [==], but not with [=].
///
/// Note that the element type #a is a special "implicit" parameter prefixed with "#".
/// That means you'll omit it when constructing the type whenever possible, and whenever
/// you NEED to specify a value, you'll write the value with the "#" prefix as well,
/// e.g. let integers : semigroup_like #int = { neutral=0; op=fun a b -> a+b; inverse = fun x = (-x) }
noeq
type semigroup_like (#a: Type) = {  
  neutral: a;
  op : binary_op a;
  inverse : unary_op a;
}

/// Here, we define basic axioms of algebraic structures in form of propositions
/// about operations and elements.
///
/// The forall part has precisely the meaning we expect it to have :)
/// From here, one can deduce what an exists statement would look like...
let associative (#a:Type) (op:binary_op a) = forall (x y z:a). (x `op` y) `op` z == x `op` (y `op` z)
let commutative (#a:Type) (op:binary_op a) = forall (x y:a). x `op` y == y `op` x

/// Things quickly get funny if we consider non-associative structures (magmas etc).
/// Therefore we don't, not because we dislike fun, but because we strive for sanity.

let left_id_of  (#a:Type) (u:a) (op:binary_op a) = forall (x:a). u `op` x == x // left identity
let right_id_of (#a:Type) (u:a) (op:binary_op a) = forall (x:a). x `op` u == x // right identity
let neutral_of  (#a:Type) (u:a) (op:binary_op a) = left_id_of u op /\ right_id_of u op // neutral element
let inverse_element_of (#a: Type) (op: binary_op a) (neutral: a) (x: a) (y: a) 
  = (x `op` y == neutral /\ y `op` x == neutral)
let invertible_element_of (#a: Type) (op: binary_op a) (neutral: a) (x: a) 
  = exists (y: a). (inverse_element_of op neutral x y)

/// Previous statements characterized the elements; the following two desribe the operations themselves.
let inverse_of (#a: Type) (op: binary_op a) (neutral: a) (invop: unary_op a) = 
  forall (x: a{invertible_element_of op neutral x}). (inverse_element_of op neutral x (invop x))
/// We define non-total inverses primarily because we'll be working with fields later,
/// and field's multiplicative group does not contain the field's zero
let total_inverse_of (#a: Type) (op: binary_op a) (neutral: a) (inverse: unary_op a) = 
  forall (x: a). (op x (inverse x)) == neutral /\ (op (inverse x) x) == neutral

/// We shall generally keep in mind that distributivity laws must be considered separately
/// If in future we consider K[x] with multiplication f(x)*g(x) defined as composition f(g(x)),
/// we will do well to remember that only one of the two distributivities holds there.
let distributive_left (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) =
  forall (x y z:a). x `op_mul` (y `op_add` z) == (x `op_mul` y) `op_add` (x `op_mul` z)
let distributive_right (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) =
  forall (x y z:a). (x `op_add` y) `op_mul` z == (x `op_mul` z) `op_add` (y `op_mul` z)
let fully_distributive (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) =
  (distributive_left op_mul op_add) /\ (distributive_right op_mul op_add) 
let no_zero_divisors (#a:Type) (zero:a) (op_mul: binary_op a) =
  forall (x y:a). (x `op_mul` y == zero) ==> (x == zero) \/ (y == zero)
let divides (#a:Type) (op_mul: binary_op a) (divisor: a) (dividend: a) = 
  exists (quotient: a). quotient `op_mul` divisor == dividend

/// We provide the two lemmas that ensure divides
let inst_divides (#a:Type) (op_mul: binary_op a) (y: a) (x: a) (z:a{z `op_mul` y == x})
  : Lemma (divides op_mul y x) = ()
/// explicitly stated version showcases FStar.Classical.exists_intro
let inst_divides_2 (#a:Type) (op_mul: binary_op a) (y: a) (x: a) (z:a{z `op_mul` y == x})
  : Lemma (divides op_mul y x) = FStar.Classical.exists_intro (fun z -> z `op_mul` y == x) z

/// This will soon be used as we'll represent elements in form of x=(unit_part)*(normal_part)
/// where (unit_part) is a ring unit, and (normal_part) is, roughly speaking, (unit_part⁻¹ * x),
/// so that normal part would represent absolute value, monic polynomial, etc.
/// If you're curious as to where did these (not so often used!) notions came from,
/// see the book "Algorithms for Computer Algebra" by Geddes, Czapor, Labahn.
/// You'll find quite a lot of interesting notions there.
///
/// we denote the unit u, because the word `unit` is reserved in F*
/// Invertible elements in a ring are called units, and here's their defining condition
let is_unit (#a: Type) (u: a) (neutral: a) (op_mul: binary_op a) = invertible_element_of op_mul neutral u
/// A zero of a ring is the neutral element of the ring's additive group,
/// and here's the special property we might need in the future
let is_zero (#a: Type) (z: a) (op_mul: binary_op a) = forall (x: a). ((x `op_mul` z) == z) /\ ((z `op_mul` x) == z)
/// We call the two elements associated if they divide each other
let are_associated (#a: Type) (p: a) (q: a) (op_mul: binary_op a) = (divides op_mul p q) /\ (divides op_mul q p) 

/// We also define in advance the notions of irreducibles and primes
/// We don't tell one from the other in Z, but in general, they are not the same thing.
let is_irreducible (#a: Type) (x: a) (one: a) (op_mul: binary_op a) = 
  (~(is_unit x one op_mul)) /\
  (forall (p q: a). (q `op_mul` p == x) ==> ( (are_associated p x op_mul) /\ (is_unit q one op_mul)) 
                                      \/ ((are_associated q x op_mul) /\ (is_unit p one op_mul)))
let is_prime (#a: Type) (p: a) (one: a) (op_mul: binary_op a) = 
  (~(is_unit p one op_mul)) /\ (forall (m n: a). (divides op_mul p (m `op_mul` n)) ==> ((divides op_mul p m) \/ (divides op_mul p n)))

/// Group-like structures are defined in a very straightforward fashion,
/// by refining semigroup_like with previously defined conditions
type semigroup (#a: Type) = x:semigroup_like #a {associative x.op}
type commutative_semigroup (#a: Type) = x:semigroup #a {commutative x.op}
type monoid (#a: Type) = x:semigroup #a {neutral_of x.neutral x.op}
type commutative_monoid (#a: Type) = x:monoid #a {commutative x.op}
type group (#a: Type) = x:monoid #a {total_inverse_of x.op x.neutral x.inverse }
type commutative_group (#a: Type) = x:group #a {commutative x.op}

/// For associative operations, should both left and right neutrals exist, they are bound to coincide.
///
/// Notice how the lemma goal expression (x==y) is assumed FOR ALL possible parameter values,
/// i.e. the actual lemma statement can be rewritten as
/// let _ (#a: Type) (g: semigroup #a) : Lemma(forall (x y: (t:a{neutral_of t g.op})). x==y)
///
/// Generally, whenever we have the choice, we prefer the the statement WITHOUT forall.
let neutral_element_is_unique (#a: Type) (g: semigroup #a) (x:a{neutral_of x g.op}) (y:a{neutral_of y g.op}) : Lemma (x==y) = ()
/// Another trivial lemma example is (-0=0), and that's not a smiley.
let neutral_inverse_is_neutral (#a: Type) (g: group #a) : Lemma (g.neutral == (g.inverse g.neutral)) = ()

/// We should keep in mind that in K[x], deg(0) = -infinity.
/// Option here emulates just that.
/// in future, I may reconsider this and introduce a more fitting notation... 
type euclidean_norm_value = option nat 
let is_euclidean_norm (#a: Type) (zero: a) (f: a -> euclidean_norm_value) = forall (q: a). ((f q)==None) <==> (q==zero) 
type euclidean_norm (#a: Type) (zero: a) = f:(a -> euclidean_norm_value){ is_euclidean_norm zero f }
let trivial_euclidean_norm (#a: Type) (zeroEl: a) (x: a) = match x with | zeroEl -> None | _ -> Some(0)

/// In our pursuit of sanity, we only consider ring-like structures that are at least rigs,
/// with addition forming a commutative group, and multiplication forming a semigroup that
/// is fully (left and right) distributive over addition
/// 
/// Notice how, just like inverse group operation, the euclidean_norm field holds little meaning
/// until we get to Euclidean Domains, but we shall keep the record field in the base type
/// because there is no inheritance in F*. Unfortunately so, to say the least.
///
/// Just like we did with semigroup_like, we prefix ring_like definition with "noeq" to explicitly state
/// that we only allow propositional equality to work with ring instances (not the elements!)
noeq
type ring_like (#a: Type) = {
  addition: commutative_group #a;
  multiplication: p:semigroup #a { fully_distributive p.op addition.op };
  unit_and_normal_parts: a -> ( (x:a{invertible_element_of multiplication.op multiplication.neutral x}) * a);
  euclidean_norm: a -> euclidean_norm_value
} 

/// Ring-like structure definitions are just as straightforward as group-likes,
/// thanks to our above definitions
type ring (#a: Type) = x:ring_like #a { neutral_of x.multiplication.neutral x.multiplication.op } 
type commutative_ring (#a: Type) = x:ring #a { commutative x.multiplication.op }
type domain (#a: Type) = x:ring #a { no_zero_divisors x.addition.neutral x.multiplication.op }
type integral_domain (#a: Type) = x:domain #a { commutative x.multiplication.op /\ x.addition.neutral =!= x.multiplication.neutral }

let zero_of (#a: Type) (r: ring_like #a) = r.addition.neutral
let one_of (#a: Type) (r: ring #a) = r.multiplication.neutral 
let add_of (#a: Type) (r: ring #a) (x: a) (y: a) = r.addition.op x y
let mul_of (#a: Type) (r: ring #a) (x: a) (y: a) = r.multiplication.op x y
let neg_of (#a: Type) (r: ring #a) (x: a) = r.addition.inverse x 
let inv_of (#a: Type) (r: ring #a) (x: a{invertible_element_of (mul_of r) (one_of r) x}) = r.multiplication.inverse x 

/// No matter how trivial, these two lemmas will soon come in handy!
/// Addition is commutative:              (a+b)+c = a+b+c = a+(b+c)
/// Neutral element is indeed neutral:    (0+a) = a = (a+0)
let ring_addition_is_associative (#a: Type) (r: ring #a) 
  : Lemma (forall (x y z: a). r.addition.op (r.addition.op x y) z == r.addition.op x (r.addition.op y z)) = ()
let ring_addition_eliminate_neutral (#a: Type) (r: ring #a) (x: a) 
  : Lemma (r.addition.op r.addition.neutral x == x) = () 

/// We would want subgroup-defining predicates later,  when we consider ideals,
/// and much later, when I finally get to add an alternative proof that Z is PID
/// using the fact that all Z ideals form cyclic subgroups under (+)
let characterizes_subgroup (#a : Type) (g : group #a) (p : predicate a) = 
    ( forall (x y: (t:a{p t})). (p (g.op x y)))
  /\ ( forall (x : a{p x}). forall (y:a {inverse_element_of g.op g.neutral y x}). (p y))
/// Multiplicative ideal properties
let survives_left_multiplication (#a: Type) (mul: semigroup #a) (p: predicate a) = 
  forall (x : a{p x}). forall (y : a). (p (mul.op y x))
let survives_right_multiplication (#a: Type) (mul: semigroup #a) (p: predicate a) = 
  forall (x : a{p x}). forall (y : a). (p (mul.op x y))

/// The special case of zero ideal, sometimes we find having this definition useful
let is_zero_ideal (#a: Type) (r: ring #a) (condition: predicate a) = 
    (condition r.addition.neutral) 
  /\ ( forall (x: a{condition x}). x == r.addition.neutral)

/// Even though we don't intend to dive deep into the non-commutative algebra now,
/// we define left and right ideals separately to keep things clean and transparent
let is_left_ideal (#a: Type) (r: ring #a) (condition: predicate a) =  
    (condition r.addition.neutral)
  /\ (characterizes_subgroup r.addition condition)                             // (x y in I) ==> (x+y in I)
  /\ (survives_right_multiplication r.multiplication condition)                // (x in I)   ==> (p*x in I) forall p

let is_right_ideal (#a: Type) (r: ring #a) (condition: predicate a) =  
    (condition r.addition.neutral)
  /\ (characterizes_subgroup r.addition condition)                             // (x y in I) ==> (x+y in I)
  /\ (survives_left_multiplication r.multiplication condition)                 // (x in I)   ==> (p*x in I) forall p

/// We define two-sided ideals like this to reduce redundancy
/// although it is fully safe to define it as both left and right, since F* will
/// deduce the same thing automatically anyway
let is_ideal (#a : Type) (r: ring #a) (condition: predicate a) = 
    (condition r.addition.neutral)                                            // zero in I
  /\ (characterizes_subgroup r.addition condition)                             // (x y in I) ==> (x+y in I)
  /\ (survives_left_multiplication r.multiplication condition)                 // (x in I)   ==> (r*x in I) forall r
  /\ (survives_right_multiplication r.multiplication condition)                // (x in I)   ==> (x*r in I) forall r

/// This may be not obvious, but we can refine arrow types just as easily as we
/// did with records and primitive types. Check out this arrow type describing
/// all predicates that indicate ideals in a given ring 
type ideal_predicate (#a:Type) (r: ring #a) = pred : (predicate a){is_ideal r pred}

/// Notice also how you no longer need the ring parameter to be explicit if you
/// also pass ideal predicate, as the ideal_predicate "fixes" the ring anyway.
/// 
/// ...Remember how unification is done in Prolog eh?
let nonzero_ideal_lemma (#a: Type) (#r: ring #a) (p: ideal_predicate r{~(is_zero_ideal r p)}) 
  : Lemma (exists (x: a{x =!= r.addition.neutral}). p x) = 
    assert (p r.addition.neutral);
    assert (~(is_zero_ideal r p));
  ()

/// In case you haven't noticed yet, Captain Obvious is the most respectable person
/// in the entire kingdom of computer-assisted provers.
///
/// Now he strikes again...
let full_ideal_is_both_left_and_right (#a: Type) (#r : ring #a) (pred : ideal_predicate r) 
  : Lemma (is_left_ideal r pred /\ is_right_ideal r pred) = ()
let left_ideal_is_full_ideal_in_commutative_rings (#a: Type) (r: commutative_ring #a) (pred: predicate a{is_left_ideal r pred})
  : Lemma (is_ideal r pred) = ()
let right_ideal_is_full_ideal_in_commutative_rings (#a: Type) (r: commutative_ring #a) (pred: predicate a{is_right_ideal r pred})
  : Lemma (is_ideal r pred) = ()

/// Thankfully we don't need to explicitly convince F* that a zero ideal is indeed an ideal
let zero_ideal_is_ideal (#a: Type) (r: ring #a) (condition: (p:predicate a{is_zero_ideal r p})) 
  : Lemma (is_ideal r condition) = ()
/// ...nor that for any x in I, (-x) should also be in I. 
let ideal_contains_additive_inverses (#a: Type) (#r: ring #a) (condition: ideal_predicate r) (element: a{condition element}) 
  : Lemma (condition (r.addition.inverse element)) = ()
/// We also basically duplicate the additive subgroup part of ideal definition in form of a lemma,
/// just for good measure. You'll quickly realize that having lemmas like this one helps you to
/// keep your proofs clean, beautiful and, most importantly, reader-friendly.
let ideal_contains_sums (#a: Type) (#r: ring #a) (pred: ideal_predicate r) (x: (t:a{pred t})) (y: (t:a{pred t})) 
  : Lemma (pred (r.addition.op x y)) = ()

/// Alright, here comes the first non-trivial lemma with a manual proof.
/// Or should I say, semi-automatic? I dare not call anything that took a
/// good couple of hours for me to write down, a semi-automatic proof.
///
/// We prove that if a is in I, and (a+b) is in I, then surely b must be in I too.
/// In human language, this must be very simple to show:
///   a in I ==> (-a) in I by the definition of ideal
///   (-a) in I and (a+b) in I ==> (-a)+(a+b), again, by the definition of ideal
///       then, by associativity, (-a)+(a+b) is also equal to (-a+a)+b, and we remember
///       that it is still in I.
///   But (-a+a) is zero, and (0+b), which is in I, is also b, which implies b is in I.
/// As for the FStar language, the proof is surprisingly similar:
let ideal_sum_part_lemma (#a: Type) //ring element type, implicit argument
    (#r: ring #a) //ring itself
    (pred: ideal_predicate r) //predicate serving as ideal indicator function
    (x: a{pred x}) //element that is known to belong to ideal
    (y: a) //element that we prove to also belong to ideal
    (sum: a{(sum == (r.addition.op x y)) /\ (pred sum)}) //sum (x+y) that is known to belong to ideal    
    : Lemma (ensures (pred y)) = //we prove that (forall x in I, forall y in R), (x+y) in I ==> (y in I)
  let op = r.addition.op in //shortcuts to operations and constants
  let inv = r.addition.inverse in

  // Notice how we embed one assignment into another via in. We keep the indentation
  // level unchanged though, because we do not want to waste screen space too much

  let i_xy = inv x `op` (x `op` y) in  //shortcuts explicitly written to apply lemmas
  let ix_y = (inv x `op` x) `op` y in 

  ideal_contains_additive_inverses pred x;    // (pred x)                            ==> (pred i)
  ideal_contains_sums pred (inv x) sum;       // (pred (inv x)) /\ (pred sum)        ==> (pred i_xy)   
  ring_addition_is_associative r;               // (a(bc) == (ab)c)                    ==> (i_xy == ix_y)
  assert (pred ix_y);                           // (i_xy==ix_y) /\ (pred i_xy)         ==> (pred ix_y)
  ring_addition_eliminate_neutral r y;          // (for all x)                         ==> (0+x == x)
  ()                                            // (pred ix_y) /\ (ix_y == 0+y == y)   ==> (pred y)

/// Now we're approaching the notion of principal ideal, which will be useful when we
/// get to work with unique factorization domains, since PID implies UFD, and boy we need
/// UFDs a lot in computer algebra... way more than we need PIDs themselves probably :

/// First, we define what it means that an ideal element x is generated by some generator g in I.
/// Precisely, it means there exists some element y in the ring (not necessarily in I) such that x == g*y.
let commutative_ideal_element_is_generated_by (#a: Type) (#r: commutative_ring #a) (condition: ideal_predicate r) (generator: a{condition generator}) (x: a{condition x})
  = exists (y: a). (r.multiplication.op generator y) == x

/// ...and when we say the whole ideal is generated by some generator g in I, we mean that for any
/// element x in the ideal, there exist an element y in the ring (not necessarily in I), such that x == g*y
let commutative_ideal_is_generated_by (#a: Type) (#r: commutative_ring #a) (condition: ideal_predicate r) (generator: a{condition generator}) = 
  (forall (x : a{condition x}). (commutative_ideal_element_is_generated_by condition generator x))

/// An ideal is called principal if it is generated by a single element. The definition below is
/// an exists definition, therefore we will be proving it by constructing the generator g and proving
/// the condition (commutative_ideal_is_generated_by...) with our generator g
let commutative_ideal_is_principal (#a: Type) (#r: commutative_ring #a) (condition: ideal_predicate r) = 
  (exists (generator: a{condition generator}). (commutative_ideal_is_generated_by condition generator))

/// Zero ideal is always generated by the ring zero, and we do not need to prove it manually, thankfully
let zero_ideal_is_principal (#a: Type) (#r: commutative_ring #a) (zi : ideal_predicate r{is_zero_ideal r zi}) 
  : Lemma (commutative_ideal_is_principal zi) = 
  assert (commutative_ideal_is_generated_by zi r.addition.neutral);
  ()

/// For good measure, I have also written that in forall fashion 
let any_zero_ideal_is_principal (#a: Type) (r: commutative_ring #a)
  : Lemma (forall (p : ideal_predicate r{is_zero_ideal r p}). commutative_ideal_is_principal p) = ()

/// This lemma is our shorthand to proving an ideal to be principal when we've found its generator already
let generator_means_principal_ideal (#a : Type) (#r: commutative_ring #a) (condition: ideal_predicate r) (generator: a{condition generator}) 
  : Lemma (requires (commutative_ideal_is_generated_by condition generator))
          (ensures (commutative_ideal_is_principal condition)) = ()

/// So now, we can define what a PID is.
/// Precisely, a PID is a domain where every ideal can be generated from just one ring element.
type principal_ideal_domain (#a: Type) = x:integral_domain #a { forall (pred: ideal_predicate x). (commutative_ideal_is_principal pred) }

/// Eventually we'll proceed with constructing more advanced structures, but currently, I've stopped at integers being a PID.
/// Still, here go the definitions for euclidean domains and fields, for future use :)
type euclidean_domain (#a: Type) = x:principal_ideal_domain #a { is_euclidean_norm x.addition.neutral x.euclidean_norm }

//let euclidean_unit_part (#a: Type) (d: euclidean_domain #a) (x: a) = 
  
//let euclidean_greater_value (#a: Type) (d: euclidean_domain #a) 

type field (#a: Type) = x:euclidean_domain #a 
{ 
  (inverse_of x.multiplication.op x.multiplication.neutral x.multiplication.inverse)
  // Surely there must be a more beautiful way of writing this!
  /\ (forall (q:a{q =!= x.addition.neutral}). (invertible_element_of x.multiplication.op x.multiplication.neutral q))
}

/// Now, we're about to construct the ring of integers and prove it to be a PID
/// Notice how you don't need to prove anything before PIDs, as Z3 proves that
/// integers form an integral domain automatically!
/// 
let int_add (a: int) (b: int) = a+b
let int_mul (a: int) (b: int) = op_Multiply a b
let int_inverse (a: int) = (-a)

/// Sometimes Z3 just fails to deduce this fact, so I've written it down explicitly.
/// But since I didn't observe such weird things, this probably had something to do
/// with the fact that my initial proofs were often unstable and approached the resource limit,
/// thus easily failing in random unobvious places :)
let int_negate_equals_zero_minus_val (a: int) : Lemma ((-a) == (0-a)) = ()

/// A simple lemma that we need to prove Z is ring-like at all 
let fd_mul_add : squash (fully_distributive int_mul int_add) = assert (fully_distributive int_mul int_add)

/// We define the absolute value like this in order to stay euclidean_norm-compliant
let integers_abs : (a: int) -> euclidean_norm_value = fun a -> if a<>0 then Some (if a<0 then -a else a) else None 
let integers_sign (a: int) = if a < 0 then (-1) else 1
/// We construct the additive group automatically, the system proves all conditions on its own
let integers_add : commutative_group = { op = int_add; neutral = 0; inverse = int_inverse; }
/// Multiplicative group comes for free as well
let integers_multiply = { neutral = 1; op = int_mul; inverse=int_inverse }
/// Moreover, we don't even need to prove Z to be an integral domain!
let integers_have_no_zero_divisors : squash (no_zero_divisors 0 int_mul) = assert (no_zero_divisors 0 int_mul)

let integers_unit_and_normal (x: int) : (u:int{invertible_element_of int_mul 1 u} * int) = ((integers_sign x) , (if x<0 then (-x) else x))

/// And thus we construct our first integral domain, the domain of integers.
let integers_domain : integral_domain = { addition = integers_add; multiplication = integers_multiply; euclidean_norm = integers_abs; unit_and_normal_parts = integers_unit_and_normal  }

/// It is often convenient to obtain both (x/y) and (x%y) at the same time
/// And while we're at it, we shall make sure the TYPES in our definition
/// are as precise as possible!
let div_rem (x:int{x>=0}) (y:int{y>0}) // we expect the dividend to be non-negative, the divisor to be strictly positive,
  // and we're about to return a pair of values such that 
  // (a) the quotient a is non-negative,
  // (b) the remainder b is non-negative and is strictly less than the divisor
  // (c) the pair should indeed satisfy x = a*y+b
  : (pair: ((a:int{a>=0}) * (b:int{b>=0/\b<y})) {x=(((fst pair) `op_Multiply` y)+(snd pair))})
  = (x/y , x%y) 

/// Here we demonstrate that for any subset of Z given by some predicate `pred`,
/// if there exists a positive element in that subset, there also exists the
/// minimal positive element. Captain obvious to the rescue, but this time it
/// is not so obvious to Z3, so we have to get rigorous again :)
let rec min_val_finder (pred: predicate int)
                       (any_positive) 
                       (n: nat{n<=any_positive}) 
                       (cur_min: pos{(pred cur_min)/\(cur_min>=n) /\ (forall (s:pos). s > n /\ s < cur_min ==> not (pred s))}) 
                       : (q:pos{(pred q)/\(q<=cur_min) /\ (forall (s:pos). s < q ==> not (pred s))}) =
                         if (n=0) then cur_min
                         else if (pred n)
                              then min_val_finder pred any_positive (n-1) n
                              else min_val_finder pred any_positive (n-1) cur_min
                              
/// So, here's our function that returns the minimal positive integer for which predicate `pred` holds
/// if we know there's at least some positive integer for which `pred` holds
let get_minimum_positive_for (pred: predicate int) (any_positive: pos{pred any_positive}) 
  : (t:pos{pred t /\ (forall (s:pos). s < t ==> not (pred s))}) 
  = (min_val_finder pred any_positive any_positive any_positive)

/// Usually I don't need to be this explicit. But back when I only started proving stuff,
/// proofs were often unstable and invoking this reduced the usage of resources
let law_of_excluded_middle (#a : Type) (cond: a -> prop) (stat: a -> prop)
    : Lemma 
      (requires ( (forall (x: a{cond x}). stat x) /\ (forall (x: a{~(cond x)}). stat x)))
      (ensures (forall (x: a). stat x)) = () 

/// Shorthand for absolute value function  
let abs (x: int) : nat = if x<=0 then -x else x 
/// Shorthand for |x| when x is known to be non-zero
let abs_nonzero (x: int{x<>0}) : pos = abs x
/// A lemma that says "if x is in ideal, then |x| is also there",
/// a simple consequence of ideal_contains_additive_inverses
let abs_preserves_ideal (p: ideal_predicate integers_domain) (x: int{p x}) : Lemma (p (abs x)) = 
  let r = integers_domain in
  assert ((-x) == r.addition.inverse x);
  ideal_contains_additive_inverses p x;
  ()
/// A specific type of all non-zero integers satisfying arbitrary predicate p
type nonzero_satisfying (p : predicate int) = (t:int{p t /\ t<>0})

/// This may look ridiculous, but invoking this speeds up the lemma below!
let modulo_works (a: nat) (b: pos) (q: nat) (r: nat) : Lemma 
    (requires (q==(a/b) /\ r==(a%b)))
    (ensures ((b `op_Multiply` q) + r)==a) = ()

/// This may look puzzling, but the lemma below fails if you don't invoke this explicitly!
let simple_negation_lemma (x: int) (y: (t:int{t == -x})) : Lemma (x = -y) = ()

/// Here we prove that any ideal in Z is generated by its smallest positive member.
/// In earlier lemmas and definitions, I removed most of redunant assertions if removing them
/// did not increase the time needed to prove the statements TOO MUCH.
///
/// Here, I did not remove anything, only commented out what was redundant.
/// I left them in order to make it easier to understand my reasoning 
/// and how (and from what) I composed the proof
let int_ideal_is_generated_by_smallest_positive_member 
  (p : ideal_predicate integers_domain)
  (min_pos : pos{p min_pos /\ (forall (s:pos{p s}). s>=min_pos)})
  : Lemma (commutative_ideal_is_generated_by p min_pos) =   
    let r = integers_domain in //just a shorthand, I can't bear writing r everywhere    
    assert (p min_pos);
    assert (min_pos > 0);
    assert (forall (i: pos{p i}). i >= min_pos);
    assert (forall (i: int{i>0 /\ i<min_pos}). ~(p i));
    assert (forall (i: int{i>=0 /\ i<min_pos}). (p i) ==> i=0); 
    let get_multiplier (x:nat{p x}) : (t:nat{x == t `op_Multiply` min_pos}) =       
        //assert (p x);             
        //assert (min_pos > 0);
        //assert (x >= 0);         
        let (multiplier,remainder) = div_rem x min_pos in         
        //let a1 : squash (multiplier==(x/min_pos)) = () in
        //let a2 : squash (remainder==(x%min_pos)) = () in
        modulo_works x min_pos multiplier remainder;
        //assert ((integers_domain.multiplication.op min_pos multiplier)+remainder = x);
        //assert (p (integers_domain.multiplication.op min_pos multiplier));
        ideal_sum_part_lemma p (integers_domain.multiplication.op min_pos multiplier) remainder x;
        //assert (p remainder);
        //assert (remainder<min_pos);
        //assert (remainder>=0);
        //assert (remainder==0);
        //assert (x == multiplier `op_Multiply` min_pos + remainder);
        let partial_product = (r.multiplication.op multiplier min_pos) in
        //assert (x == r.addition.op remainder part_prod);
        ring_addition_eliminate_neutral r partial_product;
        //assert (x == part_prod);
        //assert (x == multiplier `op_Multiply` min_pos);
        multiplier in

    // we split the proof in two, first proving the statement for positives,
    let lemma_for_positives (x: int) : Lemma
      (requires p x /\ x>=0)
      (ensures (exists (y: int). x = (y `op_Multiply` min_pos)))
      = let _ = get_multiplier x in () in        
    // then doing the same stuff for negatives, with just a little trick to flip the sign
    let lemma_for_negatives (nx: int) : Lemma
      (requires p nx /\ nx<0)
      (ensures (exists (y: int). nx = (y `op_Multiply` min_pos))) =
        ideal_contains_additive_inverses p nx;
        let x :(t:pos{p t}) = -nx in
        simple_negation_lemma nx x;
        //assert (-x = nx);
        let multiplier = get_multiplier x in
        //assert (x = multiplier `op_Multiply` min_pos);        
        //assert (-x = -(multiplier `op_Multiply` min_pos));
        neg_mul_left multiplier min_pos;
        //assert (-x = (-multiplier) `op_Multiply` min_pos);
        () 
      in    
    // and then, by the law of excluded middle, we get the full statement from two halves.
    // One might possibly argue about negatives being the smaller half for not containing the zero,
    // but as we all know, they're both of aleph-zero cardinality, so the halves are equal after all...
    let lemma_total (x: int{p x}) : Lemma (exists (y: int). x = (y `op_Multiply` min_pos)) =    
      if x<0 then (lemma_for_negatives x; ())
      else (lemma_for_positives x; ()) in
    // We convert the combined lemma into a forall-proposition and  thus finally prove the whole theorem, Z is PID. 
    FStar.Classical.forall_intro lemma_total;
    // we assert that we have proven the commutative_ideal_element_is_generated_by condition for all ideal elements,
    // let valid_dor_all() : Lemma (forall (x:int{p x}). exists (y: int). (integers_domain.multiplication.op min_pos y) == x) = () in
    // above is the condition written explicitly instead of invoking the definition 
    let goal_lemma(x: int{p x}) : Lemma (commutative_ideal_element_is_generated_by p min_pos x) = () in
    // but this is not enough! we should construct a forall proposition manually, and invoke it,
    // for z3 to finally be happy with the proof.
    let goal () : Lemma (commutative_ideal_is_generated_by p min_pos) = FStar.Classical.forall_intro goal_lemma;  () in
    goal() 

/// At this point, proving that any nonzero ideal in Z is principal becomes trivial:
let int_ideal_with_nonzero_member_is_principal (p: ideal_predicate integers_domain) (existing_nonzero: nonzero {p existing_nonzero})
  : Lemma (commutative_ideal_is_principal p) = 
      let positive_member = abs_nonzero existing_nonzero in // we ensure there's a strictly positive element in I
      ideal_contains_additive_inverses p existing_nonzero;  // we prove that (x in I) ==> (|x| in I) by invoking a lemma from before
      let min_pos : (t:pos{p t /\ (forall (s:pos{p s}). s>=t)})            // we construct the minimal positive element of I
                  = get_minimum_positive_for p positive_member in   // because we know we always could do that
      int_ideal_is_generated_by_smallest_positive_member p min_pos; // and finally we invoke our big lemma here.
    ()

/// In fact, we don't need to know the value of a positive element of I,
/// it is sufficient to know that a positive element exists.
let int_nonzero_ideal_is_principal (p: ideal_predicate integers_domain{~(is_zero_ideal integers_domain p)}) 
  : Lemma (commutative_ideal_is_principal p) =
    // So, we should remember the following trick of the trade.
    // This is what we do when we know some object exists, but we don't care or/and can't know 
    // what is it equal to. We introduce a ghost variable, of which we only know that 
    // it exists and it satisfies some condition. Just remember the syntax and the library function name :)
    let assert_existence () : squash (exists (i:int). p i /\ i<>0) = nonzero_ideal_lemma p; () in //up to here is 60ms
    let existing_nonzero : nonzero_satisfying p = //insta-200ms       
      FStar.IndefiniteDescription.indefinite_description_ghost int (fun x -> p x /\ x<>0) in
    // And here we pretend we know the value of our positive ideal element, and thus invoke the previous lemma freely
    int_ideal_with_nonzero_member_is_principal p existing_nonzero; () 

/// In our last lemma, we again use the similar trick, splitting our proof into
/// 2 parts, the trivial is_zero_ideal part that is proven automatically, and
/// the non-trivial nonzero_ideal part which we were busy proving the entire time.
let all_integer_ideals_are_principal (pred: ideal_predicate integers_domain) : Lemma (commutative_ideal_is_principal pred) =   
  let r = integers_domain in 
  let first_half_lemma (p: ideal_predicate r{is_zero_ideal r p}) : Lemma (commutative_ideal_is_principal p) = () in  
  let second_half_lemma (p: ideal_predicate r{~(is_zero_ideal r p)}) : Lemma (commutative_ideal_is_principal p) = int_nonzero_ideal_is_principal p in  
  
  FStar.Classical.forall_intro first_half_lemma;  // we can omit first_half_lemma, but the code will look uglier without it!
  FStar.Classical.forall_intro second_half_lemma; // as for second_half_lemma, we can't omit it. We're asserting a forall, after all :)
  // The following two assertions is our real goal if we expand the definition of commutative_ideal_is_principal.
  // assert (forall (p: ideal_predicate integers_domain{is_zero_ideal r p}). commutative_ideal_is_principal p);
  // assert (forall (p: ideal_predicate integers_domain{~(is_zero_ideal r p)}). commutative_ideal_is_principal p);      
  // law of excluded middle is applied automatically here.
  ()  

/// And this is a good place to stop.
let pid_int : principal_ideal_domain #int = FStar.Classical.forall_intro all_integer_ideals_are_principal; integers_domain

let gcd (#e: Type) (d: euclidean_domain #e) (a: e) (b: e) = 


let euclidean_int : euclidean_domain #int = pid_int

//let rec gcd (#a: Type) (d: euclidean_domain #a) (x: a) (y: a) : a = 
//  match (mul_of d x y) with
//  | zero_of d -> 

type unit_of (#a: Type) (d: ring #a) = (x:a{invertible_element_of (mul_of d) (one_of d) x})
type denominator_type (#a : eqtype) (domain: integral_domain #a) = (x:a{x <> domain.addition.neutral})
 
type fraction (#a : eqtype) (domain: integral_domain #a) = 
{
  numerator : a;
  denominator : denominator_type domain // (x:denominator_type domain{numerator<>domain.addition.neutral || x=domain.multiplication.neutral});
}
  
let num (#a: eqtype) (#domain: integral_domain #a) (x: fraction domain) = x.numerator
let den (#a: eqtype) (#domain: integral_domain #a) (x: fraction domain) = x.denominator
#push-options "--query_stats --z3rlimit 5 --fuel 8 --ifuel 8"

let make_fraction (#a: eqtype) 
                  (domain: integral_domain #a) 
                  (n: a) 
                  (d: denominator_type domain) 
                  : fraction domain =
  if n=(zero_of domain) then { numerator = n; denominator = one_of domain }
  else { numerator = n; denominator = d }
  

let fraction_simple_add (#e: eqtype) (#domain: integral_domain #e) (a: fraction domain) (b: fraction domain)
  : fraction domain = 
  let full_num = (domain.addition.op (domain.multiplication.op (num a) (den b)) (domain.multiplication.op (num b) (den a))) in
  let full_den = (domain.multiplication.op (den a) (den b)) in
  assert (full_den <> domain.addition.neutral);  
  { numerator = full_num; denominator = full_den }
  //make_fraction domain full_num full_den

let smart_frac_add (#e: eqtype) (#domain: integral_domain #e) (a: fraction domain) (b: fraction domain) : fraction domain = 
  let simple_sum = fraction_simple_add a b in
  make_fraction domain simple_sum.numerator simple_sum.denominator



let fraction_zero (#e: eqtype) (domain: integral_domain #e) = make_fraction domain (zero_of domain) (one_of domain)

let fraction_additive_inverse (#e: eqtype) (#domain: integral_domain #e) (a: fraction domain) : fraction domain = make_fraction domain (neg_of domain (num a)) (den a)

let simpler_eq (#e: eqtype) (#domain: integral_domain #e) (x: e) : Lemma (domain.addition.op domain.addition.neutral x == x) = ()

let frac_add_zero_lemma (#e: eqtype) (#domain: integral_domain #e) (x: fraction domain) : Lemma ((fraction_simple_add (fraction_zero domain) x) = x) = ()
let frac_add_zero_lemma2 (#e: eqtype) (#domain: integral_domain #e) (x: fraction domain) : Lemma ((fraction_simple_add x (fraction_zero domain)) = x) = ()

//let frac_zero_num_means_fraction_zero (#e: eqtype) (#domain: integral_domain #e) (x: fraction domain{x.numerator=(zero_of domain)}) 
//  : Lemma(x=fraction_zero domain) = ()

//let frac_nonzero_means_num_nonzero (#e: eqtype) (#domain: integral_domain #e) (x: fraction domain{x<>fraction_zero domain}) 
 // : Lemma(x.numerator<>zero_of domain) = ()

let frac_com (#e: eqtype) (#domain: integral_domain #e) (x: fraction domain) (y: fraction domain) : Lemma (fraction_simple_add x y = fraction_simple_add y x) = ()


#push-options "--query_stats --z3rlimit 10 --fuel 8 --ifuel 8"
let frac_assoc_lemma (#e: eqtype) (#domain: integral_domain #e) (x: fraction domain) (y: fraction domain) (z: fraction domain)
  : Lemma (fraction_simple_add (fraction_simple_add x y) z == fraction_simple_add x (fraction_simple_add y z)) 
  = ()
  (*
    let zero = fraction_zero domain in
    if (x=zero) then ( 
      assert (fraction_simple_add x y = y);
      let tmp = (fraction_simple_add y z) in
      frac_add_zero_lemma tmp;
      () 
    ) else (
      let nonzero_x_num() : Lemma (x.numerator<>zero) = frac_nonzero_means_num_nonzero x in
      if (y=zero) then (      
        assert (fraction_simple_add x y = x);
        assert (fraction_simple_add (fraction_simple_add x y) z == fraction_simple_add x z);
        assert (fraction_simple_add x (fraction_simple_add y z) == fraction_simple_add x z);
        ()
      ) else (
        if (z=zero) then (
          let lmma () : Lemma (fraction_simple_add z y = fraction_simple_add y z) =
            frac_com z y;
            ()
            in  
          assert (fraction_simple_add z y = y);
          let tmp = (fraction_simple_add x y) in
          frac_add_zero_lemma2 tmp;          
          ()
        ) else (
          admit();
          let xy = fraction_simple_add x y in
          assert (xy.numerator <> zero);
          let frac_denom_xy = mul_of domain x.denominator y.denominator in
          assert(frac_denom_xy = xy.denominator) ;
          ()
        )
      )
    ) 
    *)

let fraction_simple_mul (#e: eqtype) (#domain: integral_domain #e) (a: fraction domain) (b: fraction domain) = 
  make_fraction domain (mul_of domain (num a) (num b)) (mul_of domain (den a) (den b))

let fraction_multiplicative_inverse (#e: eqtype) (#domain: integral_domain #e) (a: fraction domain{a.numerator <> domain.addition.neutral}) = 
  make_fraction domain a.denominator a.numerator
  
let simple_add_is_associative (#e: eqtype) (#domain: integral_domain #e) (x: fraction domain) (y: fraction domain) (z: fraction domain) 
  : Lemma ((fraction_simple_add x (fraction_simple_add y z)) = fraction_simple_add (fraction_simple_add x y) z) = 
  let zero = (zero_of domain) in
  assert ((fraction_simple_add zero (fraction_simple_add y z)) = fraction_simple_add (fraction_simple_add zero y) z);
  admit();
  ()

let simple_add_is_commutative (#e: eqtype) (#domain: integral_domain #e) : Lemma (commutative (fraction_simple_add #e #domain)) = ()

let simple_inverse_is_inverse (#e: eqtype) (#domain: integral_domain #e) 
  : Lemma (total_inverse_of (fraction_simple_add #e #domain) (fraction_zero #e #domain) (fraction_additive_inverse #e #domain))  
  = 
    let aux (a: fraction domain) : Lemma ( fraction_simple_add a (fraction_additive_inverse a) == fraction_zero domain) = () in
  ()

let rationals_add_group : commutative_monoid #(fraction integers_domain) = 
{
    op = fraction_simple_add #int #integers_domain;
    inverse = fraction_additive_inverse #int #integers_domain;
    neutral = make_fraction integers_domain 0 1
}

let fraction_add_group (#e: Type) (#domain: integral_domain #e) : semigroup_like #e = 
  let mul_nonzero_lemma (x: denominator_type domain) (y: denominator_type domain)
    : Lemma (domain.multiplication.op x y =!= domain.addition.neutral) = 
    admit();
    () in  
  let zero_is_not_one () : Lemma (domain.addition.neutral =!= domain.multiplication.neutral) = () in
  {
    op = fraction_simple_add #e #domain;
    inverse = fraction_additive_inverse #e #domain;
    neutral = make_fraction domain domain.addition.neutral domain.multiplication.neutral
  }


type quotient_field (#a: Type) (domain: integral_domain #a) : (ring #(fraction #a domain)) = 
{
  addition = { 
    neutral = make_fraction domain domain.addition.neutral domain.multiplication.neutral;
    op = fraction_simple_add;
    inverse = fraction_additive_inverse
  };
  multiplication = {
    neutral = make_fraction domain domain.multiplication.neutral domain.multiplication.neutral;
    op = fraction_simple_mul;
    inverse = fraction_multiplicative_inverse
  };
  euclidean_norm = trivial_euclidean_norm (make_fraction domain domain.addition.neutral domain.multiplication.neutral)
}
