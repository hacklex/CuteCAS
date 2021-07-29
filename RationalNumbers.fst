module RationalNumbers

open AlgebraTypes

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1"

let is_valid_denominator_of (#a:Type) (d: euclidean_domain #a) (x: a) = 
  is_unit_normal d.multiplication.op d.eq d.unit_part_of x /\ ~(is_zero_of d x)

type valid_denominator_of (#a:Type) (d: euclidean_domain #a) = (t: a{is_valid_denominator_of d t})

private type commutative_ring_mul (#a:Type) (r: commutative_ring #a) = (op:binary_op a{
  is_commutative op r.eq /\ 
  is_associative op r.eq /\ 
  is_neutral_of r.multiplication.neutral op r.eq /\
  is_absorber_of r.addition.neutral op r.eq /\
  equivalence_wrt_condition op r.eq
})

private type commutative_ring_add (#a:Type) (r: commutative_ring #a) = (op:binary_op a{
  is_commutative op r.eq /\ 
  is_associative op r.eq /\ 
  is_neutral_of r.addition.neutral op r.eq /\
  is_absorber_of r.addition.neutral r.multiplication.op r.eq /\
  equivalence_wrt_condition op r.eq
})

/// This one is made private because we only work with commutative multiplication here
private let mul_of (#a:Type) (r: commutative_ring #a) : commutative_ring_mul r = r.multiplication.op

/// And this one is made private just for the sake of symmetry with mul_of
private let add_of (#a:Type) (r: commutative_ring #a) : commutative_ring_add r = r.addition.op

/// We construct fractions in such a way that denominators are always unit normal.
/// To better understand the notion of x=u(x)n(x), take a look at the book
/// by Geddes, Czapor & Labahn, Algorithms for Computer Algebra
let denominator_is_unit_normal (#a: Type) (#d: euclidean_domain #a) (x: valid_denominator_of d)
  : Lemma (is_unit_normal d.multiplication.op d.eq d.unit_part_of x) = ()

/// Fraction denominators are nonzero by definition
/// Zero is always the absorber of domain's multiplication
/// Or, equivalently, the domain addition's neutral element
let denominator_is_nonzero (#a:Type) (d: euclidean_domain #a) (x:a{is_valid_denominator_of d x})
  : Lemma (~(is_absorber_of x d.multiplication.op d.eq)) = ()

/// We construct the fractions without much sophistication
type fraction (#a:Type) (d: euclidean_domain #a) = 
 | Fraction : (num: a) -> (den: valid_denominator_of d) -> fraction d

/// We define the comparison function in a way that takes the least effort to prove the properties for.
/// If we were to define as (x - y) `eq` zero, we'd need to also manually prove is_reflexive and is_symmetric.
/// Do not want.
private let fractions_equal (#a: Type) (#d: euclidean_domain #a) (x: fraction d) (y: fraction d) = 
   ((x.num `mul_of d` y.den) `d.eq` (x.den `mul_of d` y.num)) 

/// This even pleases the eye. Especially when the lengths match.
private let equality_is_reflexive (#a:Type) (d: euclidean_domain #a) : Lemma (is_reflexive (fractions_equal #a #d)) = ()
private let equality_is_symmetric (#a:Type) (d: euclidean_domain #a) : Lemma (is_symmetric (fractions_equal #a #d)) = ()

/// Below are some leftovers from the times when the prover refused to verify even the obvious things
/// partly due to some arcane reasons (at rlimit 50+), and partly due to just going out of resources.
/// Well, currently the lemmas are written with certain amount of rigor, and mostly require minimal rlimit.
/// Still, I keep these just in case :)

let domain_law (#a:Type) (d: integral_domain #a) (x y: a)
  : Lemma (is_absorber_of (x `d.multiplication.op` y) d.multiplication.op d.eq 
       ==> (is_absorber_of x d.multiplication.op d.eq) \/ (is_absorber_of y d.multiplication.op d.eq)) 
  = assert (has_no_absorber_divisors d.multiplication.op d.eq)

let domain_law_other_zero (#a:Type) (d: integral_domain #a) (x y: a)
  : Lemma (is_absorber_of (x `d.multiplication.op` y) d.multiplication.op d.eq /\ ~(is_absorber_of y d.multiplication.op d.eq) ==> is_absorber_of x d.multiplication.op d.eq) = ()

#push-options "--ifuel 1 --fuel 0 --z3rlimit 1"
/// I experimentally established that we need ifuel=1 for the following 3 lemmas to be proven automatically.
/// Well, if you see how to make this tick with 0/0/1, please do tell me :)

let mul_cancelation_law (#a:Type) (#d: integral_domain #a) (x y: a) (z: non_absorber_of d.multiplication.op d.eq) 
  : Lemma (((x `d.multiplication.op` z) `d.eq` (y `d.multiplication.op` z)) <==> (x `d.eq` y)) = () 

let domain_law_fork (#a:Type) (d: integral_domain #a) (x y z:a) 
  : Lemma ( ((x `d.multiplication.op` y) `d.eq` (x `d.multiplication.op` z)) <==>
            (is_absorber_of x d.multiplication.op d.eq \/ (y `d.eq` z))) = ()

/// This one is still actually used in several places.
/// Basically it's a shorthand to the AlgebraTypes library lemma.
/// Note how this one is proved automatically, but proving the post-condition
/// where the callers called this is a pain.
let product_of_denominators_is_denominator (#a:Type) (#d: euclidean_domain #a) (x y: fraction d)
  : Lemma (is_valid_denominator_of d (d.multiplication.op x.den y.den)) = 
   product_of_unit_normals_is_normal d.unit_part_of x.den y.den
   
#pop-options

/// One of the most used lemmas when proving stuff involving custom equality relation.
/// This one ensures that if x `eq` y and y `eq` z, then x `eq z.
/// Keep in mind that if you have proved x `eq` (a `add` b), and then y `eq` (a `add` b),
/// you still need to call trans_lemma to obtain x `eq` y.
/// The proofs can probably be made cleaner with patterns, but I'm yet to learn how.
/// Also, I'm getting told that using patterns decreases prover's performance, so
/// I'm not sure I should.
let trans_lemma (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) (x:a) (y:a{x `eq` y \/ y `eq` x}) (z:a{y `eq` z \/ z `eq` y})
  : Lemma (x `eq` z /\ z `eq` x) = ()

/// Regular associativity lemma, straightforward and with minimal possible requirements.
let assoc_lemma3 (#a:Type) (eq: equivalence_relation a) (op: binary_op a{is_associative op eq}) (x y z: a) 
  : Lemma (((x `op` y) `op` z) `eq` (x `op` (y `op` z)) /\ (x `op` (y `op` z)) `eq` ((x `op` y) `op` z)) = ()

/// Associativity for all possible parentheses configurations between 4 terms.
/// This one's a bit monstrous, but it comes in handy later. 
let assoc_lemma4 (#a:Type) (eq: equivalence_relation a) (op: binary_op a{is_associative op eq /\ equivalence_wrt_condition op eq }) (x y z w: a) 
  : Lemma (
     (((x `op` y) `op` z) `op` w) `eq` (x `op` (y `op` (z `op` w))) /\
     (((x `op` y) `op` z) `op` w) `eq` ((x `op` y) `op` (z `op` w)) /\
     (((x `op` y) `op` z) `op` w) `eq` ((x `op` (y `op` z)) `op` w) /\
     
     (x `op` (y `op` (z `op` w))) `eq` (((x `op` y) `op` z) `op` w) /\
     ((x `op` y) `op` (z `op` w)) `eq` (((x `op` y) `op` z) `op` w) /\     
     ((x `op` (y `op` z)) `op` w) `eq` (((x `op` y) `op` z) `op` w) 
    ) = //I didn't remove the assertions entirely, as they show the intent behind the invoked lemmas
      assoc_lemma3 eq op x y z;
      //assert (((x `op` y) `op` z) `eq` (x `op` (y `op` z)));
      equivalence_wrt_operation_lemma_twoway #a #op eq ((x `op` y) `op` z) (x `op` (y `op` z)) w
      //assert ((((x `op` y) `op` z) `op` w) `eq` (((x `op` (y `op` z)) `op` w)));
    
/// I strive to remove the usages of this one, but it persists.
/// This one is used when F* fails to understand that (a `eq` b) <==> (b `eq` a)
/// This screams for a pattern, but I'm not sure how to do it right, and whether
/// the performance drop will be big or not
let symm_lemma (#a: Type) (eq: equivalence_relation a) (x:a) (y:(t:a{t `eq` x \/ x `eq` t})) : Lemma (x `eq` y /\ y `eq` x) = ()
/// This one is used to assert commutativity (works with both add and mul.
let comm_lemma (#a:Type) (eq: equivalence_relation a) (op: binary_op a{is_commutative op eq}) (x y: a)
  : Lemma ( (x `op` y) `eq` (y `op` x) /\ (y `op` x) `eq` (x `op` y)) = ()

/// These four are necessary in some spots where F* forgets these properties of + and *,
/// totally ignoring the type refinements written for the domain type in AlgebraTypes...
private let dom_mul_assoc (#a:Type) (d: domain #a) : Lemma (is_associative d.multiplication.op d.eq) = ()
private let dom_mul_comm (#a:Type) (d: domain #a) : Lemma (is_commutative d.multiplication.op d.eq) = ()
private let dom_add_assoc (#a:Type) (d: domain #a) : Lemma (is_associative d.addition.op d.eq) = ()
private let dom_add_comm (#a:Type) (d: domain #a) : Lemma (is_commutative d.addition.op d.eq) = ()

/// This is used to prove (ad cf) = (cd af) for a commutative and associative operation
/// The parameter is called mul, but it can be used with addition as well.
/// I removed the assertions, so tracing the train of thought behind the proof
/// might be a bit difficult...
private let auxiliary_flip_lemma (#p: Type)
  (eq: equivalence_relation p) 
  (mul: binary_op p { is_associative mul eq /\ is_commutative mul eq /\ equivalence_wrt_condition mul eq })
  (a d c f: p) 
  : Lemma (((a `mul` d) `mul` (c `mul` f)) `eq` ((c `mul` d) `mul` (a `mul` f))) =
  let eq : equivalence_wrt mul = eq in
  assoc_lemma4 eq mul a d c f;
  comm_lemma eq mul d c; // dc = cd 
  equivalence_wrt_operation_lemma eq (d `mul` c) (c `mul` d) a; // a dc = a cd
  symm_lemma eq (a `mul` (c `mul` d)) (a `mul` (d `mul` c)); 
  equivalence_wrt_operation_lemma eq (a `mul` (d `mul` c)) (a `mul` (c `mul` d)) f; //(a dc)f = ((cd)a)f
  comm_lemma eq mul a (mul c d);
  equivalence_wrt_operation_lemma eq  (a `mul` (c `mul` d)) ((c `mul` d) `mul` a) f;   
  assoc_lemma4 eq mul c d a f

/// This is used to prove (ab cd)=(ba dc).
private let auxiliary_add_flip_lemma (#p: Type)
  (eq: equivalence_relation p) 
  (mul: binary_op p { is_associative mul eq /\ is_commutative mul eq /\ equivalence_wrt_condition mul eq })
  (add: (q:binary_op p { is_associative q eq /\ is_commutative q eq /\ equivalence_wrt_condition q eq }))
  (a b c d: p) : Lemma (((a `mul` b) `add` (c `mul` d)) `eq` ((b `mul` a) `add` (d `mul` c))) 
  = let eq : equivalence_wrt mul = eq in // a trick to refine the type enough to invoke the library lemma
    equivalence_wrt_operation_lemma eq (mul a b) (mul b a) (mul c d);
    equivalence_wrt_operation_lemma eq (mul c d) (mul d c) (mul b a);
    trans_lemma add eq ((a `mul` b) `add` (c `mul` d)) ((b `mul` a) `add` (c `mul` d)) ((b `mul` a) `add` (d `mul` c))

/// The first big lemma is the proof of fraction equality transitivity.
/// Basically, we're proving that ad=bc && cf=de ==> af=be.
/// I left the assertions intact because the proof is otherwise even harder to understand.
private let fractions_equality_transitivity_lemma (#p: Type) (dom: euclidean_domain #p) 
  (x: fraction dom) 
  (y: (t:fraction dom{fractions_equal x t}))
  (z: (t:fraction dom{fractions_equal y t})) : Lemma (fractions_equal x z) =   
    // FStar somehow loves to forget the refinements back from the type (domain #p)
    let mul : (t:binary_op p{is_commutative t dom.eq /\ is_associative t dom.eq}) 
            = dom_mul_assoc dom; dom_mul_comm dom; dom.multiplication.op in
    let eq : equivalence_wrt mul = dom.eq in // so we provide our types explicitly to invoke the required lemmas 
    let (a,b,c,d,e,f) = (x.num, x.den, y.num, y.den, z.num, z.den) in // one composite let is faster than six :)
    assert ((a `mul` d) `eq` (b `mul` c));
    equivalence_wrt_operation_lemma eq (c `mul` f) (d `mul` e) (a `mul` d);
    assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((a `mul` d) `mul` (d `mul` e)));
    equivalence_wrt_operation_lemma eq (mul a d) (mul b c) (mul d e);
    trans_lemma mul eq ((a `mul` d) `mul` (c `mul` f)) ((a `mul` d) `mul` (d `mul` e)) ((b `mul` c) `mul` (d `mul` e));
    assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((b `mul` c) `mul` (d `mul` e)));  
    assoc_lemma4 eq mul b c d e;     
    assert ((((b `mul` c) `mul` d) `mul` e ) `eq` ((b `mul` c) `mul` (d `mul` e))); 
    assert ((((b `mul` c) `mul` d) `mul` e ) `eq` ((b `mul` (c `mul` d)) `mul` e)); 
    comm_lemma eq mul b (mul c d);
    equivalence_wrt_operation_lemma eq (b `mul` (c `mul` d)) ((c `mul` d) `mul` b) e;
    assert (((b `mul` (c `mul` d)) `mul` e ) `eq` (((c `mul` d) `mul` b) `mul` e));    
    trans_lemma mul eq (((b `mul` c) `mul` d) `mul` e ) ((b `mul` (c `mul` d)) `mul` e) (((c `mul` d) `mul` b) `mul` e);
    trans_lemma mul eq ((b `mul` c) `mul` (d `mul` e)) (((b `mul` c) `mul` d) `mul` e) (((c `mul` d) `mul` b) `mul` e); 
    assoc_lemma4 eq mul c d b e;     
    trans_lemma mul eq ((b `mul` c) `mul` (d `mul` e)) (((c `mul` d) `mul` b) `mul` e) ((c `mul` d) `mul` (b `mul` e)); 
    trans_lemma mul eq ((a `mul` d) `mul` (c `mul` f)) ((b `mul` c) `mul` (d `mul` e)) ((c `mul` d) `mul` (b `mul` e)); 
    assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((c `mul` d) `mul` (b `mul` e)));   
    auxiliary_flip_lemma eq mul a d c f;
    assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((c `mul` d) `mul` (b `mul` e))); 
    symm_lemma eq ((c `mul` d) `mul` (b `mul` e)) ((a `mul` d) `mul` (c `mul` f));
    assert (((c `mul` d) `mul` (b `mul` e)) `eq` ((a `mul` d) `mul` (c `mul` f)));         
    assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((c `mul` d) `mul` (a `mul` f)));
    trans_lemma mul eq ((c `mul` d) `mul` (b `mul` e)) ((a `mul` d) `mul` (c `mul` f)) ((c `mul` d) `mul` (a `mul` f)); 
    assert (((c `mul` d) `mul` (b `mul` e)) `eq` ((c `mul` d) `mul` (a `mul` f)));
    ()

/// We convert the above lemma into an implication to invoke Classical.forall_intro_3 and get the
/// forall version of transitivity lemma for free
private let fractions_equality_transitivity_implication_lemma (#a:Type) (d: euclidean_domain #a) (x y z: fraction d) 
  : Lemma (fractions_equal x y /\ fractions_equal y z ==> fractions_equal x z) = 
  if (fractions_equal x y && fractions_equal y z) 
  then fractions_equality_transitivity_lemma d x y z

/// This one is used to construct the equivalence_relation out of fractions_equal
/// Otherwise we can't construct the ring, never mind the field.
private let equality_is_transitive (#a:Type) (d: euclidean_domain #a) : Lemma (is_transitive (fractions_equal #a #d)) 
  = Classical.forall_intro_3 (fractions_equality_transitivity_implication_lemma d)
  
/// Once all the necessary lemmas are proven, we've got the equivalence_relation for fractions
private let equiv (#a:Type) (d: euclidean_domain #a) : equivalence_relation (fraction d) = 
  equality_is_transitive d; fractions_equal

#push-options "--ifuel 1 --fuel 0 --z3rlimit 1"
/// This one is used in algebraic operation properties proofs
/// (see commutativity, associativity proofs below)
/// If the numerators and the denominators of the two fractions are equal
/// wrt. the underlying domain's equality, then the fractions are equal.
///
/// Note that this is not the only case, as without reduced fractions,
/// we can still have fractions like 1/2 and 2/4 which are syntactically not equal,
/// but the (ad=bc) equality will still hold.
///
/// PS. No idea why, but this one also wants ifuel 1
private let equal_early_escape_lemma (#a:Type) (#d: euclidean_domain #a) (x y: fraction d) 
  : Lemma 
    (requires ((y.num `d.eq` x.num) \/ (x.num `d.eq` y.num)) /\ 
              ((y.den `d.eq` x.den) \/ (x.den `d.eq` y.den)))
    (ensures equiv d x y) = 
  let eq : equivalence_wrt d.multiplication.op = d.eq in // mul_of d is needed for lemmas below
  equivalence_wrt_operation_lemma eq y.den x.den y.num; // we need exactly equivalence wrt. mul,
  equivalence_wrt_operation_lemma eq x.num y.num y.den  // in order to prove this lemma
#pop-options
 
/// We declare the type of fractions_add heavily refined so that our
/// future lemmas will not have it too rough proving stuff
private let fractions_add (#a: Type) (d: euclidean_domain #a) (x y: fraction d)
  : (t: fraction d
     {
       t.num `d.eq` ((x.num `d.multiplication.op` y.den) `d.addition.op` (x.den `d.multiplication.op` y.num)) /\
       t.den `d.eq` (x.den `d.multiplication.op` y.den) 
     }) = 
   product_of_denominators_is_denominator x y;
   let res = Fraction ((x.num `d.multiplication.op` y.den) `d.addition.op` (x.den `d.multiplication.op` y.num))
            (x.den `d.multiplication.op` y.den) in   
   let rn = res.num in
   let rd = res.den in 
   assert_spinoff (rn `d.eq` ((x.num `d.multiplication.op` y.den) `d.addition.op` (x.den `d.multiplication.op` y.num))); 
   assert_spinoff (rd `d.eq` (x.den `d.multiplication.op` y.den));   
   res // Don't know why this does not work without spinoff.
 
/// These two lemmas may look obvious, but proofs below fail without calling it.
private let fractions_add_num_lemma (#a:Type) (d:euclidean_domain #a) (x y: fraction d)
  : Lemma ((fractions_add d x y).num `d.eq` ((x.num `d.multiplication.op` y.den) `d.addition.op` (x.den `d.multiplication.op` y.num))) = ()
private let fractions_add_den_lemma (#a:Type) (d:euclidean_domain #a) (x y: fraction d)
  : Lemma ((fractions_add d x y).den `d.eq` (x.den `d.multiplication.op` y.den)) = ()
 
private let numerator_commutativity_lemma (#a:Type) (d: euclidean_domain #a) (x y z w: a) 
  : Lemma ( ( (x `d.multiplication.op` w) `d.addition.op` (y `d.multiplication.op` z)) `d.eq`
            ( (w `d.multiplication.op` x) `d.addition.op` (z `d.multiplication.op` y))) = 
   dom_add_assoc d;
   auxiliary_add_flip_lemma d.eq d.multiplication.op d.addition.op x w y z

private let denominator_commutativity_lemma (#a:Type) (d: euclidean_domain #a) (x y: a) 
  : Lemma ((x `d.multiplication.op` y) `d.eq` (y `d.multiplication.op` x)) = ()

#push-options "--ifuel 2 --fuel 0 --z3rlimit 2"
private let fractions_add_is_commutative (#a:Type) (#d: euclidean_domain #a) (x y: fraction d) 
  : Lemma (equiv d (fractions_add d x y) (fractions_add d y x)) 
  = 
   let dom = d in
   let eq : equivalence_wrt d.addition.op = d.eq in   
   // Here comes the massive riddle.
   // If we remove the type annotation and leave just "let add = add_of d in", the proof will fail.
   // If we specify the type (commutative_ring_add d), the proof will fail.
   // If we add the refinement (add == d.addition.op), the proof will still fail.
   // If we make all the assertions manually instead of adding the type annotation, guess what.
   // ...
   // I don't know, why. 
   // PS. Getting the same error message whenever something goes wrong does not help, either.
   let add 
   : (q:binary_op a 
   { 
     is_associative q eq /\ 
     is_commutative q eq /\ 
     equivalence_wrt_condition q eq /\
     q == d.addition.op      
   })  
   = add_of d in
   let mul 
   : (m:binary_op a 
   { 
     is_associative m eq /\ 
     is_commutative m eq /\ 
     equivalence_wrt_condition m eq /\
     m == d.multiplication.op      
   }) 
   = mul_of d in 
   
   let x_plus_y = fractions_add d x y in
   let y_plus_x = fractions_add d y x in
   // Here goes another riddle. You can comment or remove any single one
   // of the two asserts below, and the proof will succeed.
   // But if you remove BOTH, the proof will fail.
   assert (x_plus_y.num `eq` ((x.num `mul` y.den) `add` (x.den `mul` y.num)));
   assert (x_plus_y.den `eq` ((x.den) `mul` (y.den)));
   numerator_commutativity_lemma dom x.num x.den y.num y.den;
   denominator_commutativity_lemma dom x.den y.den;
   equal_early_escape_lemma x_plus_y y_plus_x;
  ()

private let distributivity_lemma_right (#a:Type) (eq: equivalence_relation a) (mul: binary_op a) (add: binary_op a{is_fully_distributive mul add eq}) (x y z: a)
  : Lemma (((x `add` y) `mul` z) `eq` ((x `mul` z) `add` (y `mul` z))) = ()
private let distributivity_lemma_left (#a:Type) (eq: equivalence_relation a) (mul: binary_op a) (add: binary_op a{is_fully_distributive mul add eq}) (x y z: a)
  : Lemma ((x `mul` (y `add` z)) `eq` ((x `mul` y) `add` (x `mul` z))) = ()

#push-options "--ifuel 2 --fuel 0 --z3rlimit 3 --query_stats"
private let fractions_add_is_associative (#a:Type) (d: euclidean_domain #a) (x y z: fraction d) 
  : Lemma ((fractions_add d (fractions_add d x y) z) `equiv d` (fractions_add d x (fractions_add d y z))) = 
   //we calculate the sum of three fractions in 2 different orders,
   //and prove the results (sum_1 and sum_2) to be equal wrt. domain equality relation
   let eq = d.eq in 
   let add = d.addition.op in
   let mul = d.multiplication.op in
   dom_mul_assoc d; //we explicitly ensure (AGAIN!) associativity of domain multiplication
   dom_add_assoc d; //...and addition. Remove this and lemma calls below will fail.
   let sum_1 = fractions_add d (fractions_add d x y) z in
   fractions_add_num_lemma d (fractions_add d x y) z; // we ensure the numerator value explicitly. Remove this and the lemma will fail :)
   distributivity_lemma_right eq mul add (x.num `mul` y.den) (x.den `mul` y.num) z.den; // (ad+bc)f   
   equivalence_wrt_operation_lemma #a #add eq (((x.num `mul` y.den) `add` (x.den `mul` y.num)) `mul` z.den) 
                                              (((x.num `mul` y.den) `mul` z.den) `add` ((x.den `mul` y.num) `mul` z.den)) 
                                              ((x.den `mul` y.den) `mul` z.num); //substitute (ad+bc)f + (bd)e ==> (ad)f+(bc)f+(bd)e
   //just to keep track of what sum_1.num is currently known to be equal to
   //assert (sum_1.num `eq` ((((x.num `mul` y.den) `mul` z.den) `add` ((x.den `mul` y.num) `mul` z.den)) `add` ((x.den `mul` y.den) `mul` z.num)) );
     
   let sum_2 = fractions_add d x (fractions_add d y z) in
   fractions_add_den_lemma d x (fractions_add d y z);
   assert (sum_1.den `eq` ((x.den `mul` y.den) `mul` z.den));
   assert (sum_2.den `eq` (x.den `mul` (y.den `mul` z.den)));
  // assert (sum_1.den `eq` sum_2.den);
  // symm_lemma eq sum_2.den sum_1.den;
  // assert (sum_2.den `eq` sum_1.den);
   
   fractions_add_num_lemma d x (fractions_add d y z);
   distributivity_lemma_left eq mul add x.den (y.num `mul` z.den) (y.den `mul` z.num); // b(cf+de) = b(cf)+b(de)
   equivalence_wrt_operation_lemma #a #add eq (x.den `mul` ((y.num `mul` z.den) `add` (y.den `mul` z.num))) // b*(cf+de)
                                              ((x.den `mul` (y.num `mul` z.den)) `add` (x.den `mul` (y.den `mul` z.num))) 
                                              (x.num `mul` (y.den `mul` z.den));   
   assert (sum_2.num `eq` ((x.num `mul` (y.den `mul` z.den)) `add` ((x.den `mul` (y.num `mul` z.den)) `add`(x.den `mul` (y.den `mul` z.num))) ) );
   (* Yet another arcane part of the proof. If we replace the following 6 declarations with one composite,
      the proof will mysteriously fail! Uncomment if you want to see the world burning:
   let (part_1, part_1_r, part_2, part_2_r, part_3, part_3_r) = 
     ((x.num `mul` (y.den `mul` z.den)), ((x.num `mul` y.den) `mul` z.den),
     (x.den `mul` (y.num `mul` z.den)), ((x.den `mul` y.num) `mul` z.den),
     (x.den `mul` (y.den `mul` z.num)), ((x.den `mul` y.den) `mul` z.num)) in *)
   let part_1 = (x.num `mul` (y.den `mul` z.den)) in   // a(df)
   let part_1_r = ((x.num `mul` y.den) `mul` z.den) in // (ad)f
   let part_2 = (x.den `mul` (y.num `mul` z.den)) in   // b(cf)
   let part_2_r = ((x.den `mul` y.num) `mul` z.den) in // (bc)f
   let part_3 = (x.den `mul` (y.den `mul` z.num)) in   // b(de)
   let part_3_r = ((x.den `mul` y.den) `mul` z.num) in // (bd)e
   assoc_lemma3 eq mul x.num y.den z.den; //shuffle the parentheses in all three.
   assoc_lemma3 eq mul x.den y.num z.den; //grouped the calls for better readability.
   assoc_lemma3 eq mul x.den y.den z.num; 
   // now we operate on the scale of summands of the numerator, since the above lemmas established the parts equalities already
   assert (sum_1.num `eq` (part_1_r `add` part_2_r `add` part_3_r));
   assert (part_1 `eq` part_1_r /\ part_2 `eq` part_2_r /\ part_3 `eq` part_3_r);
   assert (sum_2.num `eq` (part_1 `add` (part_2 `add` part_3)));
   equivalence_wrt_operation_lemma #a #add eq part_1 part_1_r (part_2 `add` part_3);
   assert ((part_1 `add` (part_2 `add` part_3)) `eq` (part_1_r `add` (part_2 `add` part_3)));
   trans_lemma add eq sum_2.num (part_1 `add` (part_2 `add` part_3)) (part_1_r `add` (part_2 `add` part_3));
   assert (sum_2.num `eq` (part_1_r `add` (part_2 `add` part_3)));
   equivalence_wrt_operation_lemma #a #add eq part_2 part_2_r part_3;
   assert ((part_2 `add` part_3) `eq` (part_2_r `add` part_3)); 
   equivalence_wrt_operation_lemma #a #add eq part_3 part_3_r part_2_r;
   assert ((part_2_r `add` part_3) `eq` (part_2_r `add` part_3_r)); 
   trans_lemma add eq (part_2 `add` part_3) (part_2_r `add` part_3) (part_2_r `add` part_3_r);
   equivalence_wrt_operation_lemma #a #add eq (part_2 `add` part_3) (part_2_r `add` part_3_r) part_1_r;
   trans_lemma add eq sum_2.num (part_1_r `add` (part_2 `add` part_3)) (part_1_r `add` (part_2_r `add` part_3_r));
   assert (sum_2.num `eq` (part_1_r `add` (part_2_r `add` part_3_r)));
   assoc_lemma3 eq add part_1_r part_2_r part_3_r;  
   assert ((part_1_r `add` (part_2_r `add` part_3_r)) `eq` ((part_1_r `add` part_2_r) `add` part_3_r));
   trans_lemma add eq sum_2.num (part_1_r `add` (part_2_r `add` part_3_r)) ((part_1_r `add` part_2_r) `add` part_3_r);
   assert (sum_2.num `eq` (part_1_r `add` part_2_r `add` part_3_r));
   trans_lemma add eq sum_1.num (part_1_r `add` part_2_r `add` part_3_r) sum_2.num;
   // assert (sum_1.num `eq` sum_2.num);
   // assert (sum_1.den `eq` sum_2.den);
   equal_early_escape_lemma sum_1 sum_2;
   assert (equiv d sum_1 sum_2); // production variant will only contain the lemma invocations of course :)
   ()  

private let fractions_addition_is_associative_lemma (#a:Type) (d: euclidean_domain #a) 
  : Lemma (is_associative (fractions_add d) (equiv d)) = Classical.forall_intro_3 (fractions_add_is_associative d)

let def_eq_means_eq (#a:Type) (eq: equivalence_relation a) (x:a) (y:a{y==x}) : Lemma (x `eq` y) = ()

private let fraction_neg (#a:Type) (d: euclidean_domain #a) (x: fraction d) : 
  (t: fraction d{ t.num `d.eq` (d.addition.inv x.num) /\ t.den `d.eq` x.den }) 
  = let frac = Fraction (d.addition.inv x.num) (x.den) in
    def_eq_means_eq d.eq frac.num (d.addition.inv x.num);
    def_eq_means_eq d.eq frac.den x.den;
    frac

private let eq_of (#a:Type) (d: ring #a) : (eq:equivalence_wrt d.multiplication.op{equivalence_wrt_condition d.addition.op eq}) = d.eq



#push-options "--ifuel 0 --fuel 0 --z3rlimit 10 --query_stats"
private let is_fraction_additive_neutral (#a:Type) (d: euclidean_domain #a) (x: fraction d{is_neutral_of x.num d.addition.op d.eq}) (y: fraction d) : Lemma ((x `fractions_add d` y) `equiv d` y) 
  = 
  let mul = d.multiplication.op in
  let add = d.addition.op in  
  let eq = d.eq in
  let sum = fractions_add d x y in
  fractions_add_num_lemma d x y;
  assert (equivalence_wrt_condition add eq);
  assert (equivalence_wrt_condition mul eq);
  let eq_add : equivalence_wrt add = eq in
  let eq_mul : equivalence_wrt mul = eq in
  assert(is_absorber_of d.addition.neutral mul eq); 
  neut_add_lemma d;
  assert(is_neutral_of d.addition.neutral d.addition.op d.eq);
  neutral_is_unique d.addition x.num d.addition.neutral;
  neutral_equivalent_is_neutral add eq d.addition.neutral x.num;
  absorber_eq_is_also_absorber mul eq d.addition.neutral x.num;
  assert(is_absorber_of x.num mul eq);
  assert((x.num `mul` y.den) `eq` x.num);
  symm_lemma eq x.num (x.num `mul` y.den);
  eq_wrt_emulated #a #add eq x.num (x.num `mul` y.den) (x.den `mul` y.num); 
  equivalence_wrt_operation_lemma #a #add eq x.num (x.num `mul` y.den) (x.den `mul` y.num); 
  admit();
  assert (((x.num `mul` y.den) `add` (x.den `mul` y.num)) `eq` (x.num `add` (x.den `mul` y.num)));
  assert_spinoff(sum.num `eq` ((x.num `mul` y.den) `add` (x.den `mul` y.num)));
  trans_lemma  add eq sum.num ((x.num `mul` y.den) `add` (x.den `mul` y.num)) (x.num `add` (x.den `mul` y.num)); 
  ()
