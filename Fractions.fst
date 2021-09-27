module Fractions

open AlgebraTypes

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1"

let is_valid_denominator_of (#a:Type) (d: integral_domain #a) (x: a) = 
  is_unit_normal d.multiplication.op d.eq d.unit_part_of x /\ ~(is_zero_of d x)

type valid_denominator_of (#a:Type) (d: integral_domain #a) = (t: a{is_valid_denominator_of d t})

let normal_of_nonabs_is_abs_is_wtf (#a:Type) (d: integral_domain #a) (x: non_absorber_of d.multiplication.op d.eq) : Lemma (requires is_absorber_of (d.normal_part_of x) d.multiplication.op d.eq) (ensures False) =
  unit_and_normal_decomposition_lemma d.multiplication.op d.eq d.unit_part_of d.normal_part_of x;
  reveal_opaque (`%is_reflexive) (is_reflexive #a);  
  reveal_opaque (`%is_symmetric) (is_symmetric #a);  
  reveal_opaque (`%is_transitive) (is_transitive #a);  
  absorber_lemma d.multiplication.op d.eq (d.normal_part_of x) (d.unit_part_of x);
  assert (x `d.eq` d.normal_part_of x);
  absorber_equal_is_absorber d.multiplication.op d.eq (d.normal_part_of x) x; 
  ()

let normal_part_of_non_absorber_is_nonabsorber (#a:Type) (#d: integral_domain #a) (x: non_absorber_of d.multiplication.op d.eq) 
  : Lemma (~(is_absorber_of (d.normal_part_of x) d.multiplication.op d.eq)) = Classical.move_requires (normal_of_nonabs_is_abs_is_wtf d) x

let normal_part_of_non_absorber_is_valid_denominator (#a:Type) (#d: integral_domain #a) (x: non_absorber_of d.multiplication.op d.eq) 
  : Lemma (is_valid_denominator_of d (d.normal_part_of x)) = normal_part_of_non_absorber_is_nonabsorber x

let one_is_valid_denominator (#a:Type) (d: integral_domain #a) : Lemma (is_valid_denominator_of d d.multiplication.neutral) = 
  reveal_opaque (`%is_neutral_invariant) (is_neutral_invariant #a);  
  //ring_addition_neutral_is_multiplication_absorber d;
  assert (d.unit_part_of d.multiplication.neutral `d.eq` d.multiplication.neutral);
  neutral_equivalent_is_neutral d.multiplication.op d.eq d.multiplication.neutral (d.unit_part_of d.multiplication.neutral);
  assert (is_unit_normal d.multiplication.op d.eq d.unit_part_of d.multiplication.neutral);
  assert (~(d.multiplication.neutral `d.eq` d.addition.neutral));
  absorber_nonequal_is_nonabsorber d.multiplication.op d.eq d.addition.neutral d.multiplication.neutral;
  ()

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
unfold private let mul_of (#a:Type) (r: commutative_ring #a) : commutative_ring_mul r = r.multiplication.op

/// And this one is made private just for the sake of symmetry with mul_of
unfold private let add_of (#a:Type) (r: commutative_ring #a) : commutative_ring_add r = r.addition.op

/// We construct fractions in such a way that denominators are always unit normal.
/// To better understand the notion of x=u(x)n(x), take a look at the book
/// by Geddes, Czapor & Labahn, Algorithms for Computer Algebra
let denominator_is_unit_normal (#a: Type) (#d: integral_domain #a) (x: valid_denominator_of d)
  : Lemma (is_unit_normal d.multiplication.op d.eq d.unit_part_of x) = ()

/// Fraction denominators are nonzero by definition
/// Zero is always the absorber of domain's multiplication
/// Or, equivalently, the domain addition's neutral element
let denominator_is_nonzero (#a:Type) (d: integral_domain #a) (x:a{is_valid_denominator_of d x})
  : Lemma (~(is_absorber_of x d.multiplication.op d.eq)) = ()

/// We construct the fractions without much sophistication
type fraction (#a:Type) (d: integral_domain #a) = 
 | Fraction : (num: a) -> (den: valid_denominator_of d) -> fraction d

/// We define the comparison function in a way that takes the least effort to prove the properties for.
/// If we were to define as (x - y) `eq` zero, we'd need to also manually prove is_reflexive and is_symmetric.
/// Do not want.
unfold private let fractions_are_equal (#a: Type) (#d: integral_domain #a) (x: fraction d) (y: fraction d) = 
   ((x.num `mul_of d` y.den) `d.eq` (x.den `mul_of d` y.num)) 

private let equality_is_symmetric_lemma_oneway (#a:Type) (d: integral_domain #a) (x y: fraction d)
  : Lemma (fractions_are_equal x y ==> fractions_are_equal y x) = 
  if (fractions_are_equal x y) then (
    reveal_opaque (`%is_commutative) (is_commutative #a);   
    trans_lemma_4 d.eq (d.multiplication.op y.num x.den)
                       (d.multiplication.op x.den y.num) //commutative
                       (d.multiplication.op x.num y.den) //commutative
                       (d.multiplication.op y.den x.num) //what we needed
  )  
  
private let equality_is_symmetric_lemma (#a:Type) (d: integral_domain #a) (x y: fraction d)
  : Lemma (fractions_are_equal x y == fractions_are_equal y x) =  
  equality_is_symmetric_lemma_oneway d x y;  
  equality_is_symmetric_lemma_oneway d y x 

private let equality_is_symmetric (#a:Type) (d: integral_domain #a) 
  : Lemma (is_symmetric (fractions_are_equal #a #d)) = 
  Classical.forall_intro_2 (equality_is_symmetric_lemma d);
  reveal_opaque (`%is_symmetric) (is_symmetric #(fraction d))

/// This even pleases the eye. Especially when the lengths match.
private let equality_is_reflexive (#a:Type) (d: integral_domain #a) 
  : Lemma (is_reflexive (fractions_are_equal #a #d)) =   
    reveal_opaque (`%is_commutative) (is_commutative #a);
    reveal_opaque (`%is_reflexive) (is_reflexive #(fraction d))
    

/// Below are some leftovers from the times when the prover refused to verify even the obvious things
/// partly due to some arcane reasons (at rlimit 50+), and partly due to just going out of resources.
/// Well, currently the lemmas are written with certain amount of rigor, and mostly require minimal rlimit.
/// Still, I keep these just in case :)

private let domain_law (#a:Type) (d: integral_domain #a) (x y: a)
  : Lemma (is_absorber_of (x `d.multiplication.op` y) d.multiplication.op d.eq 
       ==> (is_absorber_of x d.multiplication.op d.eq) \/ (is_absorber_of y d.multiplication.op d.eq)) 
  = reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #a)

private let domain_law_other_zero (#a:Type) (d: integral_domain #a) (x y: a)
  : Lemma (is_absorber_of (x `d.multiplication.op` y) d.multiplication.op d.eq 
       /\ ~(is_absorber_of y d.multiplication.op d.eq)
       ==> is_absorber_of x d.multiplication.op d.eq) 
  = reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #a) 
  
(*
let ltr (#a:Type) (d: domain #a) (p q r:a) : Lemma (requires (p `d.multiplication.op` q) `d.eq` (p `d.multiplication.op` r)) (ensures ((p `d.multiplication.op` q) `d.addition.op` (d.addition.inv (p `d.multiplication.op` r))) `d.eq` d.addition.neutral) = 
  let mul = d.multiplication.op in
  let eq = d.eq in
  let add = d.addition.op in
  let neg = d.addition.inv in
  let zero = d.addition.neutral in
  equal_elements_means_equal_inverses d (p `mul` q) (p `mul` r);
  inverses_produce_neutral eq add neg (p `mul` q) (neg (p `mul` r));
  ()
*)

private let symm_lemma_follow (#a:Type) (eq: equivalence_relation a) (x:a) (y:a{y `eq` x}) 
  : Lemma (x `eq` y) = reveal_opaque (`%is_symmetric) (is_symmetric #a) 

private let logical_elim p q : Lemma (requires (p \/ q)) (ensures ~p ==> q) = ()

(*
//#push-options "--ifuel 2 --fuel 0 --z3rlimit 15"
let ring_element_equality_condition (#a:Type) (r: ring #a) (x y: a) : Lemma (x `r.eq` y <==> r.addition.op x (r.addition.inv y) `r.eq` r.addition.neutral) = 
  if (x `r.eq` y) then (  
    equal_elements_means_equal_inverses r x y;
    assert (x `r.addition.op` r.addition.inv x `r.eq` r.addition.neutral);
    equivalence_wrt_operation_lemma #a #r.addition.op r.eq (r.addition.inv x) (r.addition.inv y) x;
    assert (x `r.addition.op` (r.addition.inv y) `r.eq` r.addition.neutral)
  ) else (
    if ((r.addition.op x (r.addition.inv y)) `r.eq` r.addition.neutral) then 
    (
      neutral_equivalent_is_neutral r.addition.op r.eq r.addition.neutral (r.addition.op x (r.addition.inv y));
      assert (is_neutral_of (r.addition.op x (r.addition.inv y)) r.addition.op r.eq);
      producing_neutral_means_inverses r.eq r.addition.op r.addition.inv x (r.addition.inv y);
      assert (r.addition.inv x `r.eq` r.addition.inv y);
      equal_elements_means_equal_inverses r x y;
      ()
    ) else (
      ()
    )
  )
   
//#push-options "--ifuel 4 --fuel 0 --z3rlimit 15"
let domain_law_fork (#a:Type) (d: integral_domain #a) (x y z:a) 
  : Lemma ( ((x `d.multiplication.op` y) `d.eq` (x `d.multiplication.op` z)) <==>
            (is_absorber_of x d.multiplication.op d.eq \/ (y `d.eq` z))) = 
  let mul = d.multiplication.op in
  let eq = d.eq in
  let add = d.addition.op in
  let neg = d.addition.inv in
  let zero = d.addition.neutral in
  let ltr (p q r:a) : Lemma (requires (p `mul` q) `eq` (p `mul` r)) (ensures is_absorber_of p mul eq \/ (q `eq` r)) = 
    equal_elements_means_equal_inverses d (p `mul` q) (p `mul` r);
    inverses_produce_neutral eq add neg (p `mul` q) (neg (p `mul` r));
    assert (is_neutral_of ((p `mul` q) `add` (neg (p `mul` r))) add eq);
    ring_x_times_minus_y_is_minus_xy d p r;
    symm_lemma eq (mul p (neg r)) (neg (mul p r));
    assert (neg (mul p r) `eq` mul p (neg r));
    equivalence_wrt_operation_lemma #a #add eq (neg (mul p r)) (mul p (neg r)) (mul p q);
    assert (((mul p q) `add` (neg (mul p r))) `eq` ((mul p q) `add` (mul p (neg r))));
    assert (is_fully_distributive mul add eq);
    left_distributivity_lemma mul add eq p q (neg r);
    assert (eq (mul p (add q (neg r)))  (((mul p q) `add` (mul p (neg r)))));
    symm_lemma eq (mul p q `add` mul p (neg r)) (mul p (add q (neg r)));
    assert (eq ((mul p q) `add` (neg (mul p r))) (add (mul p q) (mul p (neg r))));
    trans_lemma eq (add (mul p q) (neg (mul p r))) (add (mul p q) (mul p (neg r))) (mul p (add q (neg r)));
    assert (is_neutral_of (mul p q `add` neg (mul p r)) add eq);
    assert (eq (mul p q `add` neg (mul p r)) (mul p (add q (neg r))));
    neutral_equivalent_is_neutral add eq ((p `mul` q) `add` (neg (mul p r))) (mul p (add q (neg r)));
    neutral_is_unique add eq (mul p (add q (neg r))) zero;
    domain_characterizing_lemma d p (add q (neg r));
    producing_neutral_means_inverses eq add neg q (neg r);
    
    admit();
    () in
  admit();
  ()
            
let mul_cancelation_law (#a:Type) (#d: integral_domain #a) (x y: a) (z: non_absorber_of d.multiplication.op d.eq) 
  : Lemma (((x `d.multiplication.op` z) `d.eq` (y `d.multiplication.op` z)) <==> (x `d.eq` y)) = () 
 *)

/// This one is still actually used in several places.
/// Basically it's a shorthand to the AlgebraTypes library lemma.
/// Note how this one is proved automatically, but proving the post-condition
/// where the callers called this is a pain.
let product_of_denominators_is_denominator (#a:Type) (#d: integral_domain #a) (x y: fraction d)
  : Lemma (is_valid_denominator_of d (d.multiplication.op x.den y.den)) = 
  reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #a);  
  product_of_unit_normals_is_normal d.unit_part_of x.den y.den

/// One of the most used lemmas when proving stuff involving custom equality relation.
/// This one ensures that if x `eq` y and y `eq` z, then x `eq z.
/// Keep in mind that if you have proved x `eq` (a `add` b), and then y `eq` (a `add` b),
/// you still need to call trans_lemma to obtain x `eq` y.
/// The proofs can probably be made cleaner with patterns, but I'm yet to learn how.
/// Also, I'm getting told that using patterns decreases prover's performance, so
/// I'm not sure I should.
 
/// Regular associativity lemma, straightforward and with minimal possible requirements.
let assoc_lemma3 (#a:Type) (eq: equivalence_relation a) (op: binary_op a{is_associative op eq}) (x y z: a) 
  : Lemma (((x `op` y) `op` z) `eq` (x `op` (y `op` z)) /\ (x `op` (y `op` z)) `eq` ((x `op` y) `op` z)) 
  = reveal_opaque (`%is_associative) (is_associative #a);
    reveal_opaque (`%is_symmetric) (is_symmetric #a)

/// This one is only needed for the lemma below to turn 12 lines of equality into just 4.
unfold private let eq_twoway (#a:Type) (eq: equivalence_relation a) (x y: a) = (x `eq` y) && (y `eq` x)

unfold private let multi_equality_5 (#a: Type) (eq: equivalence_relation a) (e1 e2 e3 e4 e5: a) = 
  e1 `eq` e2 && e1 `eq` e3 && e1 `eq` e4 && e1 `eq` e5 &&
  e2 `eq` e1 && e2 `eq` e3 && e2 `eq` e4 && e2 `eq` e5 &&
  e3 `eq` e1 && e3 `eq` e2 && e3 `eq` e4 && e3 `eq` e5 &&
  e4 `eq` e1 && e4 `eq` e2 && e4 `eq` e3 && e4 `eq` e5 &&
  e5 `eq` e1 && e5 `eq` e2 && e5 `eq` e3 && e5 `eq` e4 
  

/// Associativity for all possible parentheses configurations between 4 terms.
/// This one's a bit monstrous, but it comes in handy later. 
let assoc_lemma4 (#a:Type) (eq: equivalence_relation a) (op: binary_op a{is_associative op eq /\ equivalence_wrt_condition op eq }) (x y z w: a) 
  : Lemma (
     multi_equality_5 eq 
     (((x `op` y) `op` z) `op` w)
     (x `op` (y `op` (z `op` w)))
     ((x `op` y) `op` (z `op` w))
     ((x `op` (y `op` z)) `op` w)
     (x `op` ((y `op` z) `op` w))    //231
    ) = 
    reveal_opaque (`%is_associative) (is_associative #a);
    reveal_opaque (`%is_transitive) (is_transitive #a);
    reveal_opaque (`%is_symmetric) (is_symmetric #a);
    reveal_opaque (`%equivalence_wrt_condition) (equivalence_wrt_condition #a) 
    //opaques eliminate the need for additional instructions to the prover, but what's written
    //below was necessary to prove the lemma BEFORE the opaques were introduced.    
    //I didn't remove the assertions entirely, as they show the intent behind the invoked lemmas
    //assoc_lemma3 eq op x y z;
    //assert (((x `op` y) `op` z) `eq` (x `op` (y `op` z)));
    //equivalence_wrt_operation_lemma   #a #op eq ((x `op` y) `op` z) (x `op` (y `op` z)) w
    //assert ((((x `op` y) `op` z) `op` w) `eq` (((x `op` (y `op` z)) `op` w)));

/// This one is used to assert commutativity (works with both add and mul.
let comm_lemma (#a:Type) (eq: equivalence_relation a) (op: binary_op a{is_commutative op eq}) (x y: a)
  : Lemma ( (x `op` y) `eq` (y `op` x) /\ (y `op` x) `eq` (x `op` y)) = 
    reveal_opaque (`%is_commutative) (is_commutative #a)
  

/// These four are necessary in some spots where F* forgets these properties of + and *,
/// totally ignoring the type refinements written for the domain type in AlgebraTypes...
private let dom_mul_assoc (#a:Type) (d: domain #a) : Lemma (is_associative d.multiplication.op d.eq) = ()
private let dom_mul_comm (#a:Type) (d: commutative_ring #a) : Lemma (is_commutative d.multiplication.op d.eq) = ()
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
  reveal_opaque (`%is_transitive) (is_transitive #p);
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
    reveal_opaque (`%equivalence_wrt_condition) (equivalence_wrt_condition #p);
    reveal_opaque (`%is_commutative) (is_commutative #p);
    equivalence_wrt_operation_lemma eq (mul a b) (mul b a) (mul c d);
    equivalence_wrt_operation_lemma eq (mul c d) (mul d c) (mul b a);
    trans_lemma eq ((a `mul` b) `add` (c `mul` d)) ((b `mul` a) `add` (c `mul` d)) ((b `mul` a) `add` (d `mul` c))
 
private let final_step (#p:Type) (dom: integral_domain #p) (a c e: p) (b d f: valid_denominator_of dom)
  : Lemma (requires (((c `dom.multiplication.op` d) `dom.multiplication.op` (b `dom.multiplication.op` e)) `dom.eq` ((c `dom.multiplication.op` d) `dom.multiplication.op` (a `dom.multiplication.op` f))) /\
                    ((dom.multiplication.op a d) `dom.eq` (dom.multiplication.op b c)) /\
                    ((dom.multiplication.op c f) `dom.eq` (dom.multiplication.op d e)) 
          )
          (ensures dom.multiplication.op a f `dom.eq` dom.multiplication.op b e) =    
  reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #p); 
  domain_law_from_pq_eq_pr dom (c `dom.multiplication.op` d) (b `dom.multiplication.op` e) (a `dom.multiplication.op` f);             
  if (c `dom.multiplication.op` d `dom.eq` dom.addition.neutral) then (
    absorber_equal_is_absorber dom.multiplication.op dom.eq dom.addition.neutral (dom.multiplication.op c d);
    domain_law_other_zero dom c d;
    absorber_lemma dom.multiplication.op dom.eq c b; //bc=0
    absorber_equal_is_absorber dom.multiplication.op dom.eq (dom.multiplication.op b c) (dom.multiplication.op a d); //ad=bc=0
    domain_law_other_zero dom a d; //ad=0 ==> a=0
    absorber_lemma dom.multiplication.op dom.eq c f; //c=0 ==> cf=0
    absorber_lemma dom.multiplication.op dom.eq a f; //a=0 ==> af=0
    symm_lemma dom.eq (dom.multiplication.op d e) (dom.multiplication.op c f); //de=cf
    absorber_equal_is_absorber dom.multiplication.op dom.eq (dom.multiplication.op c f) (dom.multiplication.op d e); //0=de=cf
    domain_law_other_zero dom d e; //de=0 => e=0
    absorber_lemma dom.multiplication.op dom.eq e b; //e=0 ==> eb=0
    absorber_is_unique dom.multiplication.op dom.eq (dom.multiplication.op a f) (dom.multiplication.op b e) //eb=0 & af=0 ==> af=be
  ) else symm_lemma dom.eq (dom.multiplication.op a f) (dom.multiplication.op b e)

/// The first big lemma is the proof of fraction equality transitivity.
/// Basically, we're proving that ad=bc && cf=de ==> af=be.
/// I left the assertions intact because the proof is otherwise even harder to understand.
private let fraction_equality_transitivity_lemma (#p: Type) (dom: integral_domain #p) 
  (x: fraction dom) 
  (y: (t:fraction dom{fractions_are_equal x t}))
  (z: (t:fraction dom{fractions_are_equal y t})) : Lemma (fractions_are_equal x z) =  
   // reveal_opaque (`%is_commutative) (is_commutative #p); 
    reveal_opaque (`%is_associative) (is_associative #p);
    reveal_opaque (`%is_transitive) (is_transitive #p);
    reveal_opaque (`%is_symmetric) (is_symmetric #p);
    reveal_opaque (`%is_reflexive) (is_reflexive #p);
    reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #p);
    // FStar somehow loves to forget the refinements back from the type (domain #p)

    //let mul : (t:binary_op p{is_commutative t dom.eq /\ is_associative t dom.eq}) 
     //       = dom_mul_assoc dom; dom_mul_comm dom; dom.multiplication.op in
    let mul = dom.multiplication.op in        
    dom_mul_comm dom;
    let eq : equivalence_wrt mul = dom.eq in // so we provide our types explicitly to invoke the required lemmas 
    let (a,b,c,d,e,f) = (x.num, x.den, y.num, y.den, z.num, z.den) in // one composite let is faster than six :)
    let abso_lemma (known_absorber: absorber_of mul eq) (unk: p) : Lemma (is_absorber_of (mul known_absorber unk) mul eq) = absorber_lemma mul eq known_absorber unk in 
  //  assert (is_absorber_of dom.addition.neutral mul eq);
  //  assert ((a `mul` d) `eq` (b `mul` c));
    equivalence_wrt_operation_lemma eq (c `mul` f) (d `mul` e) (a `mul` d);
  //  assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((a `mul` d) `mul` (d `mul` e)));
    equivalence_wrt_operation_lemma eq (mul a d) (mul b c) (mul d e);
    trans_lemma eq ((a `mul` d) `mul` (c `mul` f)) ((a `mul` d) `mul` (d `mul` e)) ((b `mul` c) `mul` (d `mul` e));
  //  assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((b `mul` c) `mul` (d `mul` e)));  
    assoc_lemma4 eq mul b c d e;     
  //  assert ((((b `mul` c) `mul` d) `mul` e ) `eq` ((b `mul` c) `mul` (d `mul` e))); 
  //  assert ((((b `mul` c) `mul` d) `mul` e ) `eq` ((b `mul` (c `mul` d)) `mul` e)); 

    comm_lemma eq mul b (mul c d);
    equivalence_wrt_operation_lemma eq (b `mul` (c `mul` d)) ((c `mul` d) `mul` b) e;
  //  assert (((b `mul` (c `mul` d)) `mul` e ) `eq` (((c `mul` d) `mul` b) `mul` e));    
    trans_lemma eq (((b `mul` c) `mul` d) `mul` e ) ((b `mul` (c `mul` d)) `mul` e) (((c `mul` d) `mul` b) `mul` e);
    trans_lemma eq ((b `mul` c) `mul` (d `mul` e)) (((b `mul` c) `mul` d) `mul` e) (((c `mul` d) `mul` b) `mul` e); 
    assoc_lemma4 eq mul c d b e;   
    trans_lemma eq ((b `mul` c) `mul` (d `mul` e)) (((c `mul` d) `mul` b) `mul` e) ((c `mul` d) `mul` (b `mul` e)); 
    trans_lemma eq ((a `mul` d) `mul` (c `mul` f)) ((b `mul` c) `mul` (d `mul` e)) ((c `mul` d) `mul` (b `mul` e)); 
  //  assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((c `mul` d) `mul` (b `mul` e)));   
    auxiliary_flip_lemma eq mul a d c f;
  //  assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((c `mul` d) `mul` (b `mul` e))); 
    symm_lemma eq ((c `mul` d) `mul` (b `mul` e)) ((a `mul` d) `mul` (c `mul` f));
  //  assert (((c `mul` d) `mul` (b `mul` e)) `eq` ((a `mul` d) `mul` (c `mul` f)));         
  //  assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((c `mul` d) `mul` (a `mul` f)));
    trans_lemma eq ((c `mul` d) `mul` (b `mul` e)) ((a `mul` d) `mul` (c `mul` f)) ((c `mul` d) `mul` (a `mul` f)); 
  //  assert (((c `mul` d) `mul` (b `mul` e)) `eq` ((c `mul` d) `mul` (a `mul` f)));
    final_step dom a c e b d f;   
 ()


/// We convert the above lemma into an implication to invoke Classical.forall_intro_3 and get the
/// forall version of transitivity lemma for free
private let fraction_equality_transitivity_implication_lemma (#a:Type) (d: integral_domain #a) (x y z: fraction d) 
  : Lemma (fractions_are_equal x y /\ fractions_are_equal y z ==> fractions_are_equal x z) = 
  if (fractions_are_equal x y && fractions_are_equal y z) 
  then fraction_equality_transitivity_lemma d x y z

/// This one is used to construct the equivalence_relation out of fractions_equal
/// Otherwise we can't construct the ring, never mind the field.
private let equality_is_transitive (#p:Type) (d: integral_domain #p) : Lemma (is_transitive (fractions_are_equal #p #d)) = 
  reveal_opaque (`%is_transitive) (is_transitive #(fraction d));
  Classical.forall_intro_3 (fraction_equality_transitivity_implication_lemma d)
  
/// Once all the necessary lemmas are proven, we've got the equivalence_relation for fractions
private let fraction_eq (#a:Type) (#d: integral_domain #a) : equivalence_relation (fraction d) = 
  equality_is_reflexive d;
  equality_is_symmetric d;
  equality_is_transitive d; 
  fractions_are_equal
 
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
private let equal_early_escape_lemma (#a:Type) (#d: integral_domain #a) (x y: fraction d) 
  : Lemma 
    (requires ((y.num `d.eq` x.num) \/ (x.num `d.eq` y.num)) /\ 
              ((y.den `d.eq` x.den) \/ (x.den `d.eq` y.den)))
    (ensures fraction_eq x y) = 
  reveal_opaque (`%is_commutative) (is_commutative #a); 
  reveal_opaque (`%is_transitive) (is_transitive #a);
  let eq : equivalence_wrt d.multiplication.op = d.eq in // mul_of d is needed for lemmas below
  equivalence_wrt_operation_lemma eq y.den x.den y.num; // we need exactly equivalence wrt. mul,
  equivalence_wrt_operation_lemma eq x.num y.num y.den  // in order to prove this lemma
 
private let sys_eq_means_eq (#a:Type) (eq: equivalence_relation a) (x y: a) : Lemma (x == y ==> x `eq` y) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #a)

/// We declare the type of fractions_add heavily refined so that our
/// future lemmas will not have it too rough proving stuff
private let fraction_add (#a: Type) (#d: integral_domain #a) (x y: fraction d)
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
   sys_eq_means_eq d.eq rn ((x.num `d.multiplication.op` y.den) `d.addition.op` (x.den `d.multiplication.op` y.num));
   sys_eq_means_eq d.eq rd (x.den `d.multiplication.op` y.den);
 //  assert (rn `d.eq` ((x.num `d.multiplication.op` y.den) `d.addition.op` (x.den `d.multiplication.op` y.num))); 
 //  assert (rd `d.eq` (x.den `d.multiplication.op` y.den));   
   res // == does not mean `d.eq`, surprisingly so. Proved automatically above tho...
 
/// These two lemmas may look obvious, but proofs below fail without calling it.
private let fraction_add_num_lemma (#a:Type) (d:integral_domain #a) (x y: fraction d)
  : Lemma ((fraction_add x y).num `d.eq` ((x.num `d.multiplication.op` y.den) `d.addition.op` (x.den `d.multiplication.op` y.num))) = ()
private let fraction_add_den_lemma (#a:Type) (d:integral_domain #a) (x y: fraction d)
  : Lemma ((fraction_add x y).den `d.eq` (x.den `d.multiplication.op` y.den)) = ()
 
private let numerator_commutativity_lemma (#a:Type) (d: integral_domain #a) (x y z w: a) 
  : Lemma ( ( (x `d.multiplication.op` w) `d.addition.op` (y `d.multiplication.op` z)) `d.eq`
            ( (w `d.multiplication.op` x) `d.addition.op` (z `d.multiplication.op` y))) = 
   dom_add_assoc d;
   dom_mul_assoc d;
   auxiliary_add_flip_lemma d.eq d.multiplication.op d.addition.op x w y z

private let denominator_commutativity_lemma (#a:Type) (d: integral_domain #a) (x y: a) 
  : Lemma ((x `d.multiplication.op` y) `d.eq` (y `d.multiplication.op` x)) = 
  reveal_opaque (`%is_commutative) (is_commutative #a) 
 
private let fraction_add_is_commutative (#a:Type) (#d: integral_domain #a) (x y: fraction d) 
  : Lemma (fraction_eq (fraction_add x y) (fraction_add y x)) 
  = 
   reveal_opaque (`%is_commutative) (is_commutative #a); 
   reveal_opaque (`%is_transitive) (is_transitive #a);
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
   
   let x_plus_y = fraction_add x y in
   let y_plus_x = fraction_add y x in
   // Here goes another riddle. You can comment or remove any single one
   // of the two asserts below, and the proof will succeed.
   // But if you remove BOTH, the proof will fail.
   assert (x_plus_y.num `eq` ((x.num `mul` y.den) `add` (x.den `mul` y.num)));
   assert (x_plus_y.den `eq` ((x.den) `mul` (y.den)));
   numerator_commutativity_lemma dom x.num x.den y.num y.den;
   denominator_commutativity_lemma dom x.den y.den;
   equal_early_escape_lemma x_plus_y y_plus_x;
  ()

let fraction_addition_is_commutative (#a:Type) (#d: integral_domain) : Lemma (is_commutative #(fraction d) fraction_add fraction_eq) =   
   reveal_opaque (`%is_commutative) (is_commutative #(fraction d)); 
   Classical.forall_intro_2 (fraction_add_is_commutative #a #d)

private let distributivity_lemma_right (#a:Type) (eq: equivalence_relation a) (mul: binary_op a) (add: binary_op a{is_fully_distributive mul add eq}) (x y z: a)
  : Lemma (((x `add` y) `mul` z) `eq` ((x `mul` z) `add` (y `mul` z))) = 
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a) 
    
private let distributivity_lemma_left (#a:Type) (eq: equivalence_relation a) (mul: binary_op a) (add: binary_op a{is_fully_distributive mul add eq}) (x y z: a)
  : Lemma ((x `mul` (y `add` z)) `eq` ((x `mul` y) `add` (x `mul` z))) =  
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a) 

#push-options "--using_facts_from '* -*_smt_lemma*' --query_stats"
private let fraction_add_is_associative (#a:Type) (d: integral_domain #a) (x y z: fraction d) 
  : Lemma ((fraction_add (fraction_add x y) z) `fraction_eq` (fraction_add x (fraction_add y z))) = 
   reveal_opaque (`%is_associative) (is_associative #a); 
   //we calculate the sum of three fractions in 2 different orders,
   //and prove the results (sum_1 and sum_2) to be equal wrt. domain equality relation
   let eq = d.eq in 
   let add = d.addition.op in
   let mul = d.multiplication.op in
   dom_mul_assoc d; //we explicitly ensure (AGAIN!) associativity of domain multiplication
   dom_add_assoc d; //...and addition. Remove this and lemma calls below will fail.
   let sum_1 = fraction_add  (fraction_add x y) z in
   fraction_add_num_lemma d (fraction_add x y) z; // we ensure the numerator value explicitly. Remove this and the lemma will fail :)
   distributivity_lemma_right eq mul add (x.num `mul` y.den) (x.den `mul` y.num) z.den; // (ad+bc)f   
   equivalence_wrt_operation_lemma #a #add eq (((x.num `mul` y.den) `add` (x.den `mul` y.num)) `mul` z.den) 
                                              (((x.num `mul` y.den) `mul` z.den) `add` ((x.den `mul` y.num) `mul` z.den)) 
                                              ((x.den `mul` y.den) `mul` z.num); //substitute (ad+bc)f + (bd)e ==> (ad)f+(bc)f+(bd)e
   //just to keep track of what sum_1.num is currently known to be equal to
   //assert (sum_1.num `eq` ((((x.num `mul` y.den) `mul` z.den) `add` ((x.den `mul` y.num) `mul` z.den)) `add` ((x.den `mul` y.den) `mul` z.num)) );
     
   let sum_2 = fraction_add x (fraction_add y z) in
   fraction_add_den_lemma d x (fraction_add y z);
   assert (sum_1.den `eq` ((x.den `mul` y.den) `mul` z.den));
   assert (sum_2.den `eq` (x.den `mul` (y.den `mul` z.den)));
  // assert (sum_1.den `eq` sum_2.den);
  // symm_lemma eq sum_2.den sum_1.den;
  // assert (sum_2.den `eq` sum_1.den);
   
   fraction_add_num_lemma d x (fraction_add  y z);
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
   trans_lemma eq sum_2.num (part_1 `add` (part_2 `add` part_3)) (part_1_r `add` (part_2 `add` part_3));
   assert (sum_2.num `eq` (part_1_r `add` (part_2 `add` part_3)));
   equivalence_wrt_operation_lemma #a #add eq part_2 part_2_r part_3;
   assert ((part_2 `add` part_3) `eq` (part_2_r `add` part_3)); 
   equivalence_wrt_operation_lemma #a #add eq part_3 part_3_r part_2_r;
   assert ((part_2_r `add` part_3) `eq` (part_2_r `add` part_3_r)); 
   trans_lemma eq (part_2 `add` part_3) (part_2_r `add` part_3) (part_2_r `add` part_3_r);
   equivalence_wrt_operation_lemma #a #add eq (part_2 `add` part_3) (part_2_r `add` part_3_r) part_1_r;
   trans_lemma eq sum_2.num (part_1_r `add` (part_2 `add` part_3)) (part_1_r `add` (part_2_r `add` part_3_r));
   assert (sum_2.num `eq` (part_1_r `add` (part_2_r `add` part_3_r)));
   assoc_lemma3 eq add part_1_r part_2_r part_3_r;  
   assert ((part_1_r `add` (part_2_r `add` part_3_r)) `eq` ((part_1_r `add` part_2_r) `add` part_3_r));
   trans_lemma eq sum_2.num (part_1_r `add` (part_2_r `add` part_3_r)) ((part_1_r `add` part_2_r) `add` part_3_r);
   assert (sum_2.num `eq` (part_1_r `add` part_2_r `add` part_3_r));
   trans_lemma eq sum_1.num (part_1_r `add` part_2_r `add` part_3_r) sum_2.num;
   // assert (sum_1.num `eq` sum_2.num);
   // assert (sum_1.den `eq` sum_2.den);
   equal_early_escape_lemma sum_1 sum_2;
   assert (fraction_eq sum_1 sum_2) // production variant will only contain the lemma invocations of course :)
#pop-options

private let fraction_addition_is_associative_lemma (#a:Type) (d: integral_domain #a) 
  : Lemma (is_associative #(fraction d) (fraction_add  #a) (fraction_eq #a)) = 
  reveal_opaque (`%is_associative) (is_associative #(fraction d));   
  Classical.forall_intro_3 (fraction_add_is_associative d)

let def_eq_means_eq (#a:Type) (eq: equivalence_relation a) (x:a) (y:a{y==x}) : Lemma (x `eq` y) = reveal_opaque (`%is_reflexive) (is_reflexive #a)

private let fraction_neg (#a:Type) (#d: integral_domain #a) (x: fraction d) : 
  (t: fraction d{ t.num `d.eq` (d.addition.inv x.num) /\ t.den `d.eq` x.den })    
  = let frac = Fraction (d.addition.inv x.num) (x.den) in
    def_eq_means_eq d.eq frac.num (d.addition.inv x.num);
    def_eq_means_eq d.eq frac.den x.den;
    frac

private let eq_of (#a:Type) (d: ring #a) : (eq:equivalence_wrt d.multiplication.op{equivalence_wrt_condition d.addition.op eq}) = d.eq



#push-options "--ifuel 0 --fuel 0 --z3rlimit 2 --using_facts_from '* -*_smt_lemma*' --query_stats"
private let fraction_additive_neutral_lemma (#a:Type) (d: integral_domain #a) (x: fraction d{is_neutral_of x.num d.addition.op d.eq}) (y: fraction d) 
  : Lemma ((x `fraction_add` y) `fraction_eq` y /\ (y `fraction_add` x `fraction_eq` y))
  = 
//  ring_addition_neutral_is_multiplication_absorber d;
//  reveal_opaque (`%is_absorber_of) (is_absorber_of #a); 
//  reveal_opaque (`%is_neutral_of) (is_neutral_of #a); 
//  reveal_opaque (`%is_associative) (is_associative #a); 
//  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
 // reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  let mul = d.multiplication.op in
  let add = d.addition.op in  
  let eq = d.eq in
  let sum = fraction_add x y in 
// assert (is_absorber_of d.addition.neutral mul eq); 
//  assert (is_neutral_of d.addition.neutral d.addition.op d.eq);  
  neutral_is_unique add eq x.num d.addition.neutral; 
//  assert (eq x.num d.addition.neutral);  
  absorber_equal_is_absorber mul eq d.addition.neutral x.num;
//  fraction_add_num_lemma d x y;
//  assert (sum.num `eq` ((x.num `mul` y.den) `add` (x.den `mul` y.num)));
//  absorber_lemma mul eq x.num y.den;
  absorber_equal_is_absorber mul eq x.num (x.num `mul` y.den); 
  absorber_is_unique mul eq d.addition.neutral (x.num `mul` y.den);
  neutral_equivalent_is_neutral add eq d.addition.neutral (x.num `mul` y.den);
//  neutral_is_unique add eq d.addition.neutral (x.num `mul` y.den);
//  neutral_lemma add eq (x.num `mul` y.den) (x.den `mul` y.num);
//  assert ((x.num `mul` y.den) `add` (x.den `mul` y.num) `eq` (x.den `mul` y.num));
  equivalence_wrt_operation_lemma #a #mul eq  ((x.num `mul` y.den) `add` (x.den `mul` y.num)) (x.den `mul` y.num) y.den;
//  assert (((x.den `mul` y.num) `mul` y.den) `eq` (x.den `mul` (y.num `mul` y.den))); 
//  comm_lemma eq mul y.den y.num;
//  equivalence_wrt_operation_lemma #a #mul eq (y.num `mul` y.den) (y.den `mul` y.num) x.den;
  trans_lemma_4 eq (((x.num `mul` y.den) `add` (x.den `mul` y.num)) `mul` y.den)  ((x.den `mul` y.num) `mul` y.den) (x.den `mul` (y.num `mul` y.den)) (x.den `mul` (y.den `mul` y.num));
 // assert ((x.den `mul` (y.den `mul` y.num)) `eq` ((x.den `mul` y.den) `mul` y.num));
  trans_lemma eq (((x.num `mul` y.den) `add` (x.den `mul` y.num)) `mul` y.den) (x.den `mul` (y.den `mul` y.num)) ((x.den `mul` y.den) `mul` y.num);
  fraction_add_is_commutative y x;
//  assert (fraction_eq (y `fraction_add` x) (x `fraction_add` y));
//  assert (fraction_eq (x `fraction_add` y) y);
  trans_lemma fraction_eq (y `fraction_add` x) (x `fraction_add` y) y;
  ()
#pop-options 

let fraction_additive_neutral_condition (#a:Type) (d: integral_domain #a) (x: fraction d{is_neutral_of x.num d.addition.op d.eq})
  : Lemma (is_neutral_of x fraction_add fraction_eq) = 
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d));
  reveal_opaque (`%is_left_id_of) (is_left_id_of #(fraction d));
  reveal_opaque (`%is_right_id_of) (is_right_id_of #(fraction d));
  Classical.forall_intro (fraction_additive_neutral_lemma d x) 
    
private let fraction_mul (#a:Type) (#d: integral_domain #a) (x y: fraction d) : (t: fraction d{
  t.num `d.eq` (x.num `d.multiplication.op` y.num) /\
  t.den `d.eq` (x.den `d.multiplication.op` y.den) 
}) = 
  product_of_denominators_is_denominator x y;
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  Fraction (x.num `d.multiplication.op` y.num) (x.den `d.multiplication.op` y.den)
 
private let fraction_mul_is_commutative (#a:Type) (#d: integral_domain #a) (x y: fraction d) : Lemma (  fraction_mul x y `fraction_eq` fraction_mul y x) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  reveal_opaque (`%is_commutative) (is_commutative #a);  
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a); 
  reveal_opaque (`%is_neutral_of) (is_neutral_of #a); 
  reveal_opaque (`%is_associative) (is_associative #a);  
  reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  let xy = fraction_mul x y in
  let yx = fraction_mul y x in
  let mul = d.multiplication.op in
  let eq = d.eq in
  comm_lemma eq mul (x.num `mul` y.num)  (y.den `mul` x.den) ;
  assert ( ( (x.num `mul` y.num) `mul` (y.den `mul` x.den)) `eq`( (y.den `mul` x.den) `mul` (x.num `mul` y.num)));
  assert (x.num `mul` y.num `eq` (y.num `mul` x.num));
  equivalence_wrt_operation_lemma #a #mul eq (x.num `mul` y.num) (y.num `mul` x.num) (y.den `mul` x.den);
  assert (( (y.den `mul` x.den) `mul` (x.num `mul` y.num)) `eq`  ( (y.den `mul` x.den) `mul` (y.num `mul` x.num))  );
  equivalence_wrt_operation_lemma #a #mul eq (y.den `mul` x.den) (x.den `mul` y.den) (y.num `mul` x.num);
  trans_lemma_4 eq ( (x.num `mul` y.num) `mul` (y.den `mul` x.den))  ( (y.den `mul` x.den) `mul` (x.num `mul` y.num)) ( (y.den `mul` x.den) `mul` (y.num `mul` x.num)) ( (x.den `mul` y.den) `mul` (y.num `mul` x.num)) ;
  ()

let absorber_numerator_means_absorber_fraction (#a:Type) (#d: integral_domain #a) (z x: fraction d) 
  : Lemma (requires is_absorber_of z.num d.multiplication.op d.eq)
          (ensures fraction_eq (fraction_mul x z) z && fraction_eq (fraction_mul z x) z) =
//          (ensures z `fraction_mul` x `fraction_eq` z /\ x `fraction_mul` z `fraction_eq` z) = 
  let mul = d.multiplication.op in  
  let add = d.addition.op in  
  let eq = d.eq in   
  // Uncomment these two and the proof will fail!
  // reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  // reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  absorber_lemma mul eq z.num x.num;
  //assert ((z `fraction_mul` x).num `eq` (z.num));
  //assert ((x `fraction_mul` z).num `eq` (z.num));
  //ring_addition_neutral_is_multiplication_absorber d;
  absorber_equal_is_absorber mul eq z.num (z `fraction_mul` x).num;
  absorber_equal_is_absorber mul eq z.num (x `fraction_mul` z).num;
  absorber_lemma mul eq (z `fraction_mul` x).num z.den;
  absorber_lemma mul eq (x `fraction_mul` z).num z.den;
  absorber_lemma mul eq z.num (z `fraction_mul` x).den;
  absorber_lemma mul eq z.num (x `fraction_mul` z).den;
  //assert (((z `fraction_mul` x).num `mul` z.den) `eq` (z `fraction_mul` x).num);
  //assert ((z `fraction_mul` x).num `eq` z.num);
  trans_lemma_4 eq ((z `fraction_mul` x).num `mul` z.den) (z `fraction_mul` x).num z.num ((z `fraction_mul` x).den `mul` z.num);
  trans_lemma_4 eq ((x `fraction_mul` z).num `mul` z.den) (x `fraction_mul` z).num z.num ((x `fraction_mul` z).den `mul` z.num);
  //assert (((z `fraction_mul` x).num `mul` z.den) `eq` ((z `fraction_mul` x).den `mul` z.num));
  //assert (fraction_eq (fraction_mul z x) z);
  fraction_mul_is_commutative x z;
  //assert (fraction_eq (fraction_mul x z) (fraction_mul z x));
  trans_lemma fraction_eq (fraction_mul x z) (fraction_mul z x) z;
  () 

let fraction_absorber_condition (#a:Type) (#d: integral_domain #a) (z: fraction d)
  : Lemma (requires is_absorber_of z.num d.multiplication.op d.eq)
          (ensures is_absorber_of z fraction_mul fraction_eq) = 
  reveal_opaque (`%is_absorber_of) (is_absorber_of #(fraction d)); 
  let aux (x: fraction d) : Lemma (fraction_eq (fraction_mul x z) z && fraction_eq (fraction_mul z x) z) 
    = absorber_numerator_means_absorber_fraction z x in
  FStar.Classical.forall_intro aux

let non_absorber_fraction_has_nonzero_numerator (#a:Type) (#d: integral_domain #a) (x: fraction d) 
  : Lemma (requires ~(is_absorber_of x fraction_mul fraction_eq)) 
          (ensures ~(is_absorber_of x.num d.multiplication.op d.eq)) = 
  Classical.move_requires fraction_absorber_condition x

private let fraction_mul_is_associative (#a:Type) (#d: integral_domain #a) (x y z: fraction d) : Lemma (fraction_mul (fraction_mul x y) z `fraction_eq` fraction_mul x (fraction_mul y z)) = 
  reveal_opaque (`%is_associative) (is_associative #a);  
  reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  let xy_z = (fraction_mul x y `fraction_mul` z)  in
  let x_yz = fraction_mul x (fraction_mul y z) in
  let mul = d.multiplication.op in
  let eq = d.eq in
  assert (eq xy_z.num x_yz.num);
  assert (eq xy_z.den  (x.den `mul` y.den `mul` z.den    ));
  assert (eq x_yz.den  (x.den `mul` y.den `mul` z.den    ));
  trans_lemma eq x_yz.den (x.den `mul` y.den `mul` z.den) xy_z.den;
  assert (eq xy_z.den x_yz.den);
  equal_early_escape_lemma xy_z x_yz; 
()

private let fraction_mul_neutral_lemma (#a:Type) (#d: integral_domain #a) (x: fraction d{d.eq x.num x.den \/ d.eq x.den x.num}) (y: fraction d)
  : Lemma (x `fraction_mul` y `fraction_eq` y /\ y `fraction_mul` x `fraction_eq` y) =   
  reveal_opaque (`%is_transitive) (is_transitive #a)

private let fraction_zero_is_neutral_lemma (#a:Type) (#d: integral_domain #a) (x: fraction d{is_neutral_of x.num d.addition.op d.eq})  
  : Lemma (is_neutral_of x fraction_add fraction_eq) =   
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d)); 
  reveal_opaque (`%is_left_id_of) (is_left_id_of #(fraction d)); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #(fraction d)); 
  Classical.forall_intro (fraction_additive_neutral_lemma d x)

let fraction_is_mul_neutral (#a:Type) (#d: integral_domain #a) (x: fraction d{d.eq x.num x.den \/ d.eq x.den x.num})
  : Lemma (is_neutral_of x fraction_mul fraction_eq) =  
  reveal_opaque (`%is_left_id_of) (is_left_id_of #(fraction d)); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #(fraction d)); 
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d)); 
  Classical.forall_intro (fraction_mul_neutral_lemma x)  

#push-options "--ifuel 1 --fuel 0 --z3rlimit 2 --using_facts_from '* -*_smt_lemma*' --query_stats"
private let fraction_one_is_neutral_lemma (#a:Type) (#d: integral_domain #a) (x: fraction d{is_neutral_of x.num d.multiplication.op d.eq /\ is_neutral_of x.den d.multiplication.op d.eq}) : Lemma (is_neutral_of x (fraction_mul) fraction_eq) =
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d)); 
  reveal_opaque (`%is_left_id_of) (is_left_id_of #(fraction d)); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #(fraction d)); 
  neutral_is_unique d.multiplication.op d.eq x.num x.den;
  symm_lemma d.eq x.den x.num;
  Classical.forall_intro (fraction_mul_neutral_lemma x)
#pop-options

private let fraction_zero (#a:Type) (#d: integral_domain #a) : (z:neutral_element_of #(fraction d) fraction_add fraction_eq { is_absorber_of z fraction_mul fraction_eq 
                                                                                                                            /\ d.eq z.num d.addition.neutral
                                                                                                                            /\ d.eq z.den d.multiplication.neutral })
  = 
  one_is_valid_denominator d;
  let zero = Fraction d.addition.neutral d.multiplication.neutral in
  fraction_zero_is_neutral_lemma zero;
  fraction_absorber_condition zero;
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  zero

private let fraction_one (#a:Type) (#d: integral_domain #a) : (u: neutral_element_of #(fraction d) fraction_mul fraction_eq { (u.num `d.eq` d.multiplication.neutral) /\ (u.den `d.eq` d.multiplication.neutral) }) = 
  one_is_valid_denominator d;
  let one = Fraction d.multiplication.neutral d.multiplication.neutral in
  fraction_one_is_neutral_lemma one;
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  one

let fraction_eq_means_expr (#a:Type) (#d:integral_domain #a) (x y: fraction d) : Lemma (requires fraction_eq x y) (ensures d.eq (d.multiplication.op x.num y.den) (d.multiplication.op x.den y.num)) = ()

let fraction_one_eq_zero_means_wtf (#a: Type) (d: integral_domain #a) : Lemma (requires fraction_eq (fraction_one #a #d) (fraction_zero #a #d)) (ensures False) = 
  let one = fraction_one #a #d in
  let zero = fraction_zero #a #d in
  reveal_opaque (`%is_reflexive) (is_reflexive #a);
  reveal_opaque (`%is_transitive) (is_transitive #a);
  reveal_opaque (`%is_symmetric) (is_symmetric #a);
  neutral_lemma d.multiplication.op d.eq d.multiplication.neutral d.multiplication.neutral;
  ()

let fraction_one_is_not_equal_to_fraction_zero (#a: Type) (#d: integral_domain #a) 
  : Lemma (~(fraction_eq (fraction_one #a #d) (fraction_zero #a #d)) /\ ~(fraction_eq (fraction_zero #a #d) (fraction_one #a #d))) = 
  reveal_opaque (`%is_symmetric) (is_symmetric #(fraction d)); 
  Classical.move_requires (fraction_one_eq_zero_means_wtf #a) d;
  ()

let equal_means_eq (#a:Type) (#d: integral_domain #a) (x y: a) : Lemma (requires (x == y)) (ensures d.eq x y /\ d.eq y x) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #a) 
  
private let ring_distributivity_lemma (#a:Type) (r: ring #a) : Lemma (is_right_distributive r.multiplication.op r.addition.op r.eq /\ is_left_distributive r.multiplication.op r.addition.op r.eq) = 
  reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a);
  reveal_opaque (`%is_right_distributive) (is_right_distributive #a); 
  reveal_opaque (`%is_left_distributive) (is_left_distributive #a) 

/// Proof that fraction addition respects fraction equality is lengthy, so I only commented out the intermediate asserts,
/// but dare not remove them, as they help understanding the purpose of the proof steps 
#push-options "--ifuel 0 --fuel 0 --z3rlimit 3 --query_stats"
private let fraction_equivalence_respects_add (#a:Type) (#d: integral_domain #a) (e1: fraction d) (e2: fraction d{e1 `fraction_eq` e2 }) (x: fraction d) 
  : Lemma ((x `fraction_add` e1) `fraction_eq` (x `fraction_add` e2) /\ (e1 `fraction_add` x ) `fraction_eq` (e2 `fraction_add` x)) = 
  let mul = d.multiplication.op in
  let eq = d.eq in
  let add = d.addition.op in 
  //reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  //reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  ring_distributivity_lemma d; 
  //assert ((x `fraction_add` e1).num `d.eq`  ((x.num `mul` e1.den) `add` (x.den `mul` e1.num)));
  //assert ((x `fraction_add` e2).num `d.eq`  ((x.num `mul` e2.den) `add` (x.den `mul` e2.num)));
  //assert ((x `fraction_add` e1).den `d.eq` (x.den `mul` e1.den));
  //assert ((x `fraction_add` e2).den `d.eq` (x.den `mul` e2.den));
  right_distributivity_lemma mul add d.eq (x.num `mul` e1.den) (x.den `mul` e1.num) (x.den `mul` e2.den);
  assert ( (((x.num `mul` e1.den) `add` (x.den `mul` e1.num)) `mul` (x.den `mul` e2.den)) `d.eq`  (((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) 
                                                                                            `add`  ((x.den `mul` e1.num) `mul` (x.den `mul` e2.den))));
  //we will carefully transform ad into bc, as (a/b=c/d) is defined as (ad=bc)
  let left_side = (fraction_add x e1).num `mul` (fraction_add x e2).den in
  //let right_side = (fraction_add x e1).den `mul` (fraction_add x e2).num in
  assert (left_side `eq` ( ( (x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) `add` ( (x.den `mul` e1.num) `mul` (x.den `mul` e2.den))));
  assert ((fraction_add x e1).den `eq` (x.den `mul` e1.den));
  assert ((fraction_add x e2).num `eq` ((x.num `mul` e2.den) `add` (x.den `mul` e2.num)));  
  //assert (right_side `eq` ( (x.den `mul` e1.den) `mul` ((x.num `mul` e2.den) `add` (x.den `mul` e2.num)) ));
  comm_lemma eq mul x.den e2.den;
  //assert (mul x.den e2.den `d.eq` mul e2.den x.den /\ mul e2.den x.den `d.eq` mul x.den e2.den );
  equivalence_wrt_operation_lemma #a #mul d.eq (x.den `mul` e2.den) (e2.den `mul` x.den) (x.den `mul` e1.num);
  //assert ( ( (x.den `mul` e1.num) `mul` (x.den `mul` e2.den)) `eq` ((x.den `mul` e1.num) `mul` (e2.den `mul` x.den)));
  assoc_lemma4 d.eq mul x.den e1.num e2.den x.den;
  trans_lemma eq ((x.den `mul` e1.num) `mul` (e2.den `mul` x.den)) (((x.den `mul` e1.num) `mul` e2.den) `mul` x.den) ((x.den `mul` (e1.num `mul` e2.den)) `mul` x.den);
  //assert ( ((x.den `mul` e1.num) `mul` (e2.den `mul` x.den)) `eq` ((x.den `mul` (e1.num `mul` e2.den)) `mul` x.den)); 
  //assert ((e1.num `mul` e2.den) `eq` (e1.den `mul` e2.num));
  equivalence_wrt_operation_lemma #a #mul eq (e1.num `mul` e2.den) (e1.den `mul` e2.num) x.den;
  equivalence_wrt_operation_lemma #a #mul eq (x.den `mul` (e1.num `mul` e2.den)) (x.den `mul` (e1.den `mul` e2.num)) x.den;
  //assert ( ((x.den `mul` (e1.num `mul` e2.den)) `mul` x.den) `eq` ((x.den `mul` (e1.den `mul` e2.num)) `mul` x.den)); // need (x.den e1.den)(x.den e2.num)
  assoc_lemma4 d.eq mul x.den e1.den e2.num x.den;
  assert ( ((x.den `mul` (e1.den `mul` e2.num)) `mul` x.den) `eq` ((x.den `mul` e1.den) `mul` (e2.num `mul` x.den)));
  comm_lemma eq mul e2.num x.den;
  //equivalence_wrt_operation_lemma #a #mul eq (mul e2.num x.den) (mul x.den e2.num) (x.den `mul` e1.den); 
  trans_lemma_4 eq  ((x.den `mul` (e1.num `mul` e2.den)) `mul` x.den)
                    ((x.den `mul` (e1.den `mul` e2.num)) `mul` x.den)
                    ((x.den `mul` e1.den) `mul` (e2.num `mul` x.den))
                    ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num));
  //assert (eq  ((x.den `mul` e1.num) `mul` (x.den `mul` e2.den)) ((x.den `mul` e1.num) `mul` (e2.den `mul` x.den)));
  assert (eq  ((x.den `mul` e1.num) `mul` (e2.den `mul` x.den)) ((x.den `mul` (e1.num `mul` e2.den)) `mul` x.den));
  trans_lemma_4 eq  ((x.den `mul` e1.num) `mul` (x.den `mul` e2.den))
                    ((x.den `mul` e1.num) `mul` (e2.den `mul` x.den))  
                    ((x.den `mul` (e1.num `mul` e2.den)) `mul` x.den)
                    ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num));
  //equivalence_wrt_operation_lemma #a #add eq ((x.den `mul` e1.num) `mul` (x.den `mul` e2.den))
    //                                         ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num))
      //                                       ((x.num `mul` e1.den) `mul` (x.den `mul` e2.den));
  trans_lemma eq left_side  ( ((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) `add` ((x.den `mul` e1.num) `mul` (x.den `mul` e2.den)))
                            ( ((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) `add` ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num)));                        
  //assert (left_side `eq` ( ((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) `add` ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num))));
  assoc_lemma4 eq mul x.num e1.den x.den e2.den;
  comm_lemma eq mul e1.den x.den;
  //equivalence_wrt_operation_lemma #a #mul eq (e1.den `mul` x.den) (x.den `mul` e1.den) x.num;
  equivalence_wrt_operation_lemma #a #mul eq (x.num `mul` (e1.den `mul` x.den)) (x.num `mul` (x.den `mul` e1.den)) e2.den;
  assoc_lemma4 eq mul x.num x.den e1.den e2.den;
  trans_lemma   eq ((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) //assoc
                   ((x.num `mul` (e1.den `mul` x.den)) `mul` e2.den) //comm
                   ((x.num `mul` (x.den `mul` e1.den)) `mul` e2.den);
  comm_lemma eq mul x.num (x.den `mul` e1.den);
  //equivalence_wrt_operation_lemma #a #mul eq (mul x.num (mul x.den e1.den)) (mul (mul x.den e1.den) x.num) e2.den;
  //assert ( eq ((x.num `mul` (x.den `mul` e1.den)) `mul` e2.den) (((x.den `mul` e1.den) `mul` x.num) `mul` e2.den));
  assoc_lemma4 eq mul x.den e1.den x.num e2.den;
  trans_lemma_4 eq ((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) 
                   ((x.num `mul` (x.den `mul` e1.den)) `mul` e2.den)
                   (((x.den `mul` e1.den) `mul` x.num) `mul` e2.den)
                   ((x.den `mul` e1.den) `mul` (x.num `mul` e2.den));
  //equivalence_wrt_operation_lemma #a #add eq  ((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) 
    //                                          ((x.den `mul` e1.den) `mul` (x.num `mul` e2.den))
      //                                        ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num));
  trans_lemma eq left_side (((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) `add` ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num)))
                           (((x.den `mul` e1.den) `mul` (x.num `mul` e2.den)) `add` ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num)));
  symm_lemma eq (((x.den `mul` e1.den) `mul` (x.num `mul` e2.den)) `add` ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num))) ((x.den `mul` e1.den) `mul` ((x.num `mul` e2.den) `add` (x.den `mul` e2.num)));
  left_distributivity_lemma mul add eq (mul x.den e1.den) (mul x.num e2.den) (mul x.den e2.num);
  trans_lemma eq left_side (((x.den `mul` e1.den) `mul` (x.num `mul` e2.den)) `add` ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num)))
                           ((x.den `mul` e1.den) `mul` ((x.num `mul` e2.den) `add` (x.den `mul` e2.num)));
  assert (fraction_eq (fraction_add x e1) (fraction_add x e2));
  //assert (left_side `eq` right_side);
  assert (fraction_eq (fraction_add x e1) (fraction_add x e2));
  //The rest is trivial, just using commutativity again.
  fraction_add_is_commutative x e1;
  reveal_opaque (`%is_symmetric) (is_symmetric #(fraction d));
  fraction_add_is_commutative x e2;
  assert (fraction_eq (fraction_add x e1) (fraction_add x e2));
  trans_lemma_4 fraction_eq (fraction_add e1 x) (fraction_add x e1) (fraction_add x e2) (fraction_add e2 x);
() 
#pop-options 

let fraction_equivalence_respects_addition (#a:Type) (#d: integral_domain #a) : Lemma(equivalence_wrt_condition #(fraction d) (fraction_add #a) (fraction_eq #a)) = 
  reveal_opaque (`%equivalence_wrt_condition) (equivalence_wrt_condition #(fraction d)); 
  Classical.forall_intro_3 (fraction_equivalence_respects_add #a #d)


/// Proof that fraction multiplication respects fraction equality is shorter compared to its addition counterpart, 
/// so I did not leave many assertions as trans_lemmas give enough clues to what's happening under the hood.
private let fraction_equivalence_respects_mul (#a:Type) (#d: integral_domain #a) (e1: fraction d) (e2: fraction d{e1 `fraction_eq` e2 }) (x: fraction d) 
  : Lemma ((x `fraction_mul` e1) `fraction_eq` (x `fraction_mul` e2) /\ (e1 `fraction_mul` x ) `fraction_eq` (e2 `fraction_mul` x)) =  
  let mul = d.multiplication.op in
  let eq = d.eq in
  comm_lemma eq mul x.den e2.den;
  equivalence_wrt_operation_lemma #a #mul eq (mul x.den e2.den) (mul e2.den x.den) (mul x.num e1.num);
  assoc_lemma4 eq mul x.num e1.num e2.den x.den;
  trans_lemma eq ((x.num `mul` e1.num) `mul` (x.den `mul` e2.den))
                   ((x.num `mul` e1.num) `mul` (e2.den `mul` x.den)) 
                   ((x.num `mul` (e1.num `mul` e2.den)) `mul` x.den);
  // we remember that from e1=e2, we get ((e1.num `mul` e2.den) `eq` (e1.den `mul` e2.num))
  equivalence_wrt_operation_lemma #a #mul eq (mul e1.num e2.den) (mul e1.den e2.num) x.num;
  equivalence_wrt_operation_lemma #a #mul eq (x.num `mul` (e1.num `mul` e2.den)) (x.num `mul` (e1.den `mul` e2.num)) x.den;  
  trans_lemma eq ((x.num `mul` e1.num) `mul` (x.den `mul` e2.den))
                 ((x.num `mul` (e1.num `mul` e2.den)) `mul` x.den)
                 ((x.num `mul` (e1.den `mul` e2.num)) `mul` x.den);
  comm_lemma eq mul e1.den e2.num;  
  equivalence_wrt_operation_lemma #a #mul eq (e1.den `mul` e2.num) (e2.num `mul` e1.den) x.num;
  equivalence_wrt_operation_lemma #a #mul eq (x.num `mul` (e1.den `mul` e2.num)) (x.num `mul` (e2.num `mul` e1.den)) x.den;
  assoc_lemma4 eq mul x.num e2.num e1.den x.den;
  trans_lemma_4 eq  ((x.num `mul` e1.num) `mul` (x.den `mul` e2.den))
                    ((x.num `mul` (e1.den `mul` e2.num)) `mul` x.den) 
                    ((x.num `mul` (e2.num `mul` e1.den)) `mul` x.den) 
                    ((x.num `mul` e2.num) `mul` (e1.den `mul` x.den));
  comm_lemma eq mul e1.den x.den;
  equivalence_wrt_operation_lemma #a #mul eq (e1.den `mul` x.den) (x.den `mul` e1.den) (x.num `mul` e2.num);  
  comm_lemma eq mul (x.num `mul` e2.num) (x.den `mul` e1.den);
  trans_lemma_4 eq ((x.num `mul` e1.num) `mul` (x.den `mul` e2.den))
                   ((x.num `mul` e2.num) `mul` (e1.den `mul` x.den))
                   ((x.num `mul` e2.num) `mul` (x.den `mul` e1.den)) 
                   ((x.den `mul` e1.den) `mul` (x.num `mul` e2.num));
  assert (fraction_eq (fraction_mul x e1) (fraction_mul x e2));
  fraction_mul_is_commutative x e1;
  fraction_mul_is_commutative x e2;
  trans_lemma_4 fraction_eq (fraction_mul e1 x) (fraction_mul x e1) (fraction_mul x e2) (fraction_mul e2 x); 
  ()

let fraction_equivalence_respects_multiplication (#a:Type) (#d: integral_domain #a) : Lemma(equivalence_wrt_condition #(fraction d) (fraction_mul #a) (fraction_eq #a)) = 
  reveal_opaque (`%equivalence_wrt_condition) (equivalence_wrt_condition #(fraction d)); 
  Classical.forall_intro_3 (fraction_equivalence_respects_mul #a #d)

let fraction_eq_means_condition (#a:Type) (#d: integral_domain #a) (x y: fraction d)
  : Lemma (requires fraction_eq x y)
          (ensures (d.multiplication.op x.num y.den `d.eq` d.multiplication.op x.den y.num)) = ()

let domain_pr_eq_pq_means_r_eq_q (#a:Type) (d: integral_domain #a) (p q r: a)
  : Lemma (requires d.eq (d.multiplication.op p q) (d.multiplication.op p r) /\ ~(is_absorber_of p d.multiplication.op d.eq))
          (ensures d.eq q r) = 
          domain_law_from_pq_eq_pr d p q r;
          nonzero_is_not_equal_to_add_neutral_p d p;
          ()
 
let fraction_absorber_means_numerator_absorber (#a:Type) (#d: integral_domain #a) (x: fraction d)  
  : Lemma (requires is_absorber_of x fraction_mul fraction_eq)
          (ensures is_absorber_of x.num d.multiplication.op d.eq) = 
          let p = x.num in                    
          let aux (q: a) : Lemma (d.eq p (d.multiplication.op p q) /\ d.eq p (d.multiplication.op q p) /\ d.eq (d.multiplication.op p q) p /\ d.eq (d.multiplication.op q p) p) = 
            one_is_valid_denominator d;
            let qf : fraction d = Fraction q d.multiplication.neutral in
            let xqf = fraction_mul x qf in
            let ( *) = d.multiplication.op in
            reveal_opaque (`%is_reflexive) (is_reflexive #a); 
            reveal_opaque (`%is_transitive) (is_transitive #a); 
            reveal_opaque (`%is_symmetric) (is_symmetric #a); 
            reveal_opaque (`%is_commutative) (is_commutative #a); 
            assert (p `d.eq` x.num);       
            assert (xqf.den `d.eq` (x.den * d.multiplication.neutral));
            assert (xqf.den `d.eq` x.den);
            assert (xqf.num `d.eq` (p `d.multiplication.op` q));
            assert (xqf.den `d.eq` (x.den `d.multiplication.op` d.multiplication.neutral));
            neutral_lemma d.multiplication.op d.eq d.multiplication.neutral x.den;
            assert (xqf.den `d.eq` x.den);
            assert (is_absorber_of x fraction_mul fraction_eq);
            fraction_equivalence_respects_multiplication #a #d;
            absorber_lemma fraction_mul fraction_eq x qf;
            assert (fraction_eq xqf x);
            fraction_eq_means_condition xqf x;
            assert ((xqf.num * x.den) `d.eq` (x.den * x.num));            
            assert ((x.den * xqf.num) `d.eq` (x.den * x.num));
            denominator_is_nonzero d x.den;
            assert (~(is_absorber_of x.den d.multiplication.op d.eq));
            domain_pr_eq_pq_means_r_eq_q d x.den xqf.num x.num; 
            assert ((p * q) `d.eq` p);
            assert ((q * p) `d.eq` p);
            symm_lemma d.eq p (p*q);
            symm_lemma d.eq p (q*p);
          () in
          reveal_opaque (`%is_absorber_of) (is_absorber_of #a); 
          Classical.forall_intro aux

let frac_abs_cond (#a:Type) (#d: integral_domain #a) (x: non_absorber_of #(fraction d) fraction_mul fraction_eq) : Lemma (~(is_absorber_of x.num d.multiplication.op d.eq)) = 
    (Classical.move_requires (fraction_absorber_condition)) x;
    ()

let frac_nonabs_cond (#a:Type) (#d: integral_domain #a) (x: fraction d)
  : Lemma (requires ~(is_absorber_of x.num d.multiplication.op d.eq))
          (ensures ~(is_absorber_of x fraction_mul fraction_eq)) =           
          Classical.move_requires (fraction_absorber_means_numerator_absorber) x

#push-options "--ifuel 2 --fuel 0 --z3rlimit 3 --query_stats"
private let fraction_mul_domain_law (#a:Type) (#d: integral_domain #a) (p q: non_absorber_of #(fraction d) fraction_mul fraction_eq)
  : Lemma (~(is_absorber_of (fraction_mul p q) fraction_mul fraction_eq)) = 
  let pq = fraction_mul p q in    
  assert (pq.num `d.eq` d.multiplication.op p.num q.num);
  frac_abs_cond p;
  frac_abs_cond q;
  domain_multiplication_law d.eq d.multiplication.op p.num q.num;
  assert (~(is_absorber_of pq.num d.multiplication.op d.eq));
  frac_nonabs_cond pq;
  (Classical.move_requires fraction_absorber_condition) pq
  

//let is_inverse_operation_for (#a: Type) (inv: unary_op a) (op: binary_op a) (eq: equivalence_relation a) 
//  = (forall (x:a). is_neutral_of (op x (inv x)) op eq /\ is_neutral_of (op (inv x) x) op eq)

#push-options "--ifuel 1 --fuel 0 --z3rlimit 3 --query_stats"
private let fraction_neg_is_inverse_for_add (#a:Type) (#d: integral_domain #a) (x: fraction d) : Lemma (
  is_neutral_of (fraction_add x (fraction_neg x)) fraction_add fraction_eq /\
  is_neutral_of (fraction_add (fraction_neg x) x) fraction_add fraction_eq) = 
  ring_distributivity_lemma d;
  let add = d.addition.op in
  let neg = d.addition.inv in
  let mul = d.multiplication.op in  
  let eq = d.eq in  
  assert ((fraction_neg x).num `eq` neg x.num);
  assert ((fraction_neg x).den `eq` x.den);
//  fraction_add_num_lemma d x (fraction_neg x);
  assert ((fraction_add x (fraction_neg x)).den `eq` (fraction_add (fraction_neg x) x).den);
  assert (((fraction_add x (fraction_neg x)).num) `eq` ((x.num `mul` x.den) `add` (x.den `mul`  neg x.num))); 
  comm_lemma eq mul x.num x.den;
  equivalence_wrt_operation_lemma #a #add eq (x.num `mul` x.den) (x.den `mul` x.num) (x.den `mul` neg x.num);
  trans_lemma eq (fraction_add x (fraction_neg x)).num  
                 ((x.num `mul` x.den) `add` (x.den `mul` neg x.num))
                 ((x.den `mul` x.num) `add` (x.den `mul` neg x.num));   
 // reveal_opaque (`%is_neutral_of) (is_neutral_of #a); 
  left_distributivity_lemma mul add eq x.den x.num (neg x.num);
  trans_lemma eq (fraction_add x (fraction_neg x)).num 
                 ((x.den `mul` x.num) `add` (x.den `mul` neg x.num)) 
                 (x.den `mul` (x.num `add` neg x.num));
  inverse_operation_lemma add eq neg x.num;
  assert (is_neutral_of (x.num `add` neg x.num) add eq);
  neutral_is_unique add eq d.addition.neutral (x.num `add` neg x.num);
  assert (d.addition.neutral `eq` (x.num `add` neg x.num));
  symm_lemma eq (x.num `add` neg x.num) d.addition.neutral;
  absorber_equal_is_absorber mul eq d.addition.neutral (x.num `add` neg x.num);
  absorber_lemma mul eq (x.num `add` neg x.num) x.den;
  absorber_equal_is_absorber mul eq (x.num `add` neg x.num) (x.den `mul` (x.num `add` neg x.num)); 
  assert (is_absorber_of (x.den `mul` (x.num `add` neg x.num)) mul eq); 
  absorber_is_unique mul eq (x.den `mul` (x.num `add` neg x.num)) d.addition.neutral;
  neutral_equivalent_is_neutral add eq d.addition.neutral (x.den `mul` (x.num `add` neg x.num));
  symm_lemma eq (x.den `mul` (x.num `add` neg x.num)) d.addition.neutral;
  trans_lemma eq (fraction_add x (fraction_neg x)).num
                 (x.den `mul` (x.num `add` neg x.num))
                 d.addition.neutral;
  neutral_equivalent_is_neutral add eq d.addition.neutral (fraction_add x (fraction_neg x)).num;
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d)); 
  reveal_opaque (`%is_left_id_of) (is_left_id_of #(fraction d)); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #(fraction d)); 
  Classical.forall_intro (fraction_additive_neutral_lemma d (x `fraction_add` fraction_neg x));
  assert (is_neutral_of (fraction_add x (fraction_neg x)) fraction_add fraction_eq);
  fraction_add_is_commutative x (fraction_neg x);
  assert (fraction_add x (fraction_neg x) `fraction_eq` fraction_add (fraction_neg x) x);
  symm_lemma fraction_eq (fraction_add (fraction_neg x) x) (fraction_add x (fraction_neg x));
  assert (fraction_eq (fraction_add (fraction_neg x) x) (fraction_add x (fraction_neg x)));
  fraction_equivalence_respects_addition #a #d;
  neutral_equivalent_is_neutral  fraction_add fraction_eq (x `fraction_add` fraction_neg x) (fraction_neg x `fraction_add` x); 
  ()
#pop-options

let fraction_neg_is_inverse_for_addition (#a:Type) (#d: integral_domain #a) : Lemma (is_inverse_operation_for (fraction_neg #a #d) fraction_add fraction_eq) =  
  reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #(fraction d)); 
  Classical.forall_intro (fraction_neg_is_inverse_for_add #a #d)

private let fraction_negation_lemma (#a:Type) (#d: integral_domain #a) (x: fraction d) 
  : Lemma (is_neutral_of (x `fraction_add` (fraction_neg x)) fraction_add fraction_eq /\
           is_neutral_of ((fraction_neg x) `fraction_add` x) (fraction_add) (fraction_eq)) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a); 
  reveal_opaque (`%is_right_distributive) (is_right_distributive #a); 
  let add = d.addition.op in
  let neg = d.addition.inv in
  let mul = d.multiplication.op in  
  let x' = fraction_neg x in
  let s = x `fraction_add` x' in
  assert (s.num `d.eq` ((x.num `mul` x.den) `add` (x.den `mul` neg x.num)));
  comm_lemma d.eq mul  x.den (neg x.num);
  equivalence_wrt_operation_lemma #a #add d.eq (x.den `mul` neg x.num) (neg x.num `mul` x.den) (x.num `mul` x.den);
  assert (s.num `d.eq` ((x.num `mul` x.den) `add` (neg x.num `mul` x.den)));
  right_distributivity_lemma mul add d.eq x.num (neg x.num) x.den;
  trans_lemma d.eq s.num ((x.num `mul` x.den) `add` (neg x.num `mul` x.den)) ((x.num `add` neg x.num) `mul` x.den);
  inverse_operation_lemma add d.eq neg x.num;
  assert (is_neutral_of (x.num `add` neg x.num) add d.eq);
  neutral_is_unique add d.eq d.addition.neutral (x.num `add` neg x.num);
  symm_lemma d.eq (x.num `add` neg x.num) d.addition.neutral;
  absorber_equal_is_absorber mul d.eq d.addition.neutral (x.num `add` neg x.num);
  absorber_lemma mul d.eq (x.num `add` neg x.num) x.den;  
  absorber_equal_is_absorber mul d.eq (x.num `add` neg x.num) ((x.num `add` neg x.num) `mul` x.den);
  assert (d.eq s.num ((x.num `add` neg x.num) `mul` x.den));
  absorber_is_unique mul d.eq ((x.num `add` neg x.num) `mul` x.den) d.addition.neutral;
  trans_lemma d.eq s.num ((x.num `add` neg x.num) `mul` x.den) d.addition.neutral;
  assert (s.num `d.eq` d.addition.neutral);
  neutral_equivalent_is_neutral add d.eq d.addition.neutral s.num;
  assert (is_neutral_of s.num add d.eq);
  fraction_zero_is_neutral_lemma s; 
  fraction_add_is_commutative x (fraction_neg x);
  fraction_equivalence_respects_addition #a #d;
  fraction_neg_is_inverse_for_addition #a #d;
  inverse_operation_lemma fraction_add fraction_eq fraction_neg x;
  fraction_add_is_commutative x (fraction_neg x);
  symm_lemma fraction_eq (x `fraction_add` fraction_neg x) (fraction_neg x `fraction_add` x);
  neutral_equivalent_is_neutral fraction_add fraction_eq (x `fraction_add` fraction_neg x) (fraction_neg x `fraction_add` x)

private let fraction_neg_respects_equivalence (#a:Type) (#d: integral_domain #a) (x y: fraction d) : Lemma (x `fraction_eq` y ==> (fraction_neg x `fraction_eq` fraction_neg y)) 
  = 
  let neg = d.addition.inv in
  let mul = d.multiplication.op in 
  if (fraction_eq x y) then (
    assert ((fraction_neg x).num `d.eq` d.addition.inv x.num);
    ring_x_times_minus_y_is_minus_x_times_y d x.num y.den;
    ring_x_times_minus_y_is_minus_xy d x.num y.den;
    trans_lemma d.eq (neg x.num `mul` y.den) 
                     (x.num `mul` neg y.den)
                     (neg (x.num `mul` y.den));
    assert ((x.num `mul` y.den) `d.eq` (x.den `mul` y.num));
    equal_elements_means_equal_inverses d (x.num `mul` y.den) (x.den `mul` y.num);
    assert (neg (x.num `mul` y.den) `d.eq` neg (x.den `mul` y.num));
    ring_x_times_minus_y_is_minus_xy d x.den y.num;
    symm_lemma d.eq (neg (mul x.den y.num)) (mul x.den (neg y.num));
    assert (neg (x.den `mul` y.num) `d.eq` (x.den `mul` neg y.num));
    trans_lemma_4 d.eq (neg x.num `mul` y.den)
                       (neg (x.num `mul` y.den))
                       (neg (x.den `mul` y.num))
                       (x.den `mul` neg y.num);
    () 
  )

let fraction_negation_respects_equivalence (#a:Type) (#d: integral_domain #a) : Lemma (respects_equivalence #(fraction d) fraction_neg fraction_eq) = 
  reveal_opaque (`%respects_equivalence) (respects_equivalence #(fraction d)); 
  Classical.forall_intro_2 (fraction_neg_respects_equivalence #a #d)
 
   
let fraction_eq_properties (#a:Type) (d: integral_domain #a) : Lemma (
  equivalence_wrt_condition (fraction_add #a #d) fraction_eq /\
  equivalence_wrt_condition (fraction_mul #a #d) fraction_eq /\
  is_associative (fraction_add #a #d) fraction_eq /\
  is_associative (fraction_mul #a #d) fraction_eq)
  [SMTPat(fraction_eq #a #d)]
  = 
  reveal_opaque (`%is_associative) (is_associative #(fraction d));   
  fraction_addition_is_associative_lemma d;
  Classical.forall_intro_3 (fraction_mul_is_associative #a #d);
  fraction_equivalence_respects_addition #a #d; 
  fraction_equivalence_respects_multiplication #a #d
   
let any_fraction_is_additive_unit (#a:Type) (#d: integral_domain #a) (x: fraction d) : Lemma (is_unit x fraction_add fraction_eq) =
  reveal_opaque (`%is_unit) (is_unit #(fraction d));   
  fraction_neg_is_inverse_for_add x

let unit_from_any_frac (#a:Type) (#d: integral_domain #a) (x: fraction d) : (units_of (fraction_add #a #d) (fraction_eq)) = 
  any_fraction_is_additive_unit x;
  x

let fraction_add_all_are_units (#a:Type) (#d: integral_domain #a) 
  : Lemma (all_are_units #(fraction d) fraction_add fraction_eq) 
  = Classical.forall_intro (any_fraction_is_additive_unit #a #d)
 
let fraction_neg_eq_property (#a:Type) (#d: integral_domain #a) 
  : Lemma (respects_equivalence #(fraction d) 
                                fraction_neg 
                                fraction_eq) 
  [SMTPat(fraction_neg #a #d)]
  = 
    fraction_negation_respects_equivalence #a #d;
    fraction_add_all_are_units #a #d;
    ()

let fraction_neg_respects_equivalence_of_units (#a:Type) (#d: integral_domain #a) 
                                               (x y: units_of #(fraction d) fraction_add fraction_eq) 
  : Lemma(fraction_eq x y ==> fraction_eq (fraction_neg x) (fraction_neg y)) = 
  fraction_neg_respects_equivalence x y
 
let fraction_neg_units (#a:Type) (#d: integral_domain #a) : (unary_op_on_units_of (fraction_add #a #d) fraction_eq) = 
  fraction_negation_respects_equivalence #a #d;
  fraction_add_all_are_units #a #d;  
//  assert (equivalence_wrt_condition #(fraction d) fraction_add fraction_eq);
//  assert (all_are_units #(fraction d) fraction_add fraction_eq);
//  reveal_opaque (`%is_reflexive) (is_reflexive #(fraction d)); 
  reveal_opaque (`%is_reflexive) (is_reflexive #(units_of #(fraction d) fraction_add fraction_eq)); 
  reveal_opaque (`%is_symmetric) (is_symmetric #(fraction d));   
  reveal_opaque (`%is_symmetric) (is_symmetric #(units_of #(fraction d) fraction_add fraction_eq));   
  reveal_opaque (`%is_transitive) (is_transitive #(fraction d));
  reveal_opaque (`%is_transitive) (is_transitive #(units_of #(fraction d) fraction_add fraction_eq));
//  reveal_opaque (`%is_unit) (is_unit #(fraction d));
  reveal_opaque (`%respects_equivalence) (respects_equivalence #(units_of #(fraction d) fraction_add fraction_eq));
  assert (respects_equivalence #(fraction d) fraction_neg fraction_eq);
  Classical.forall_intro_2 (fraction_neg_respects_equivalence_of_units #a #d);
  assert (respects_equivalence #(units_of #(fraction d) fraction_add fraction_eq) fraction_neg fraction_eq);
  fraction_neg

let fraction_neg_yields_inverses_for_units (#a:Type) (#d: integral_domain #a) (x: units_of #(fraction d) fraction_add fraction_eq)
  : Lemma (is_neutral_of (fraction_add (fraction_neg x) x) fraction_add fraction_eq /\
           is_neutral_of (fraction_add x (fraction_neg x)) fraction_add fraction_eq) = 
           fraction_neg_is_inverse_for_add x           
 
let fraction_neg_properties (#a:Type) (d: integral_domain #a) : Lemma (
  equivalence_wrt_condition (fraction_add #a #d) fraction_eq /\
  respects_equivalence (fraction_neg #a #d) fraction_eq /\ 
  all_are_units (fraction_add #a #d) fraction_eq /\
  yields_inverses_for_units (fraction_add #a #d) fraction_eq (    
      Classical.forall_intro_2 (fraction_neg_respects_equivalence_of_units #a #d);
      reveal_opaque (`%respects_equivalence) (respects_equivalence #(units_of #(fraction d) fraction_add fraction_eq));
    fraction_neg)) = 
    
    assert (equivalence_wrt_condition (fraction_add #a #d) fraction_eq);
    assert (respects_equivalence (fraction_neg #a #d) fraction_eq);
    fraction_add_all_are_units #a #d;
    assert (all_are_units (fraction_add #a #d) fraction_eq);
    Classical.forall_intro (fraction_neg_yields_inverses_for_units #a #d);
    fraction_negation_respects_equivalence #a #d;
    Classical.forall_intro_2 (fraction_neg_respects_equivalence_of_units #a #d);
    reveal_opaque (`%is_reflexive) (is_reflexive #(units_of #(fraction d) fraction_add fraction_eq)); 
    reveal_opaque (`%is_symmetric) (is_symmetric #(fraction d));   
    reveal_opaque (`%is_symmetric) (is_symmetric #(units_of #(fraction d) fraction_add fraction_eq));   
    reveal_opaque (`%is_transitive) (is_transitive #(fraction d));
    reveal_opaque (`%is_transitive) (is_transitive #(units_of #(fraction d) fraction_add fraction_eq));
    reveal_opaque (`%respects_equivalence) (respects_equivalence #(units_of #(fraction d) fraction_add fraction_eq)); 
    assert (yields_inverses_for_units (fraction_add #a #d) fraction_eq fraction_neg);
    ()

let fraction_neg_u (#a:Type) (#d: integral_domain #a) (x: units_of (fraction_add #a #d) (fraction_eq)) : (units_of (fraction_add #a #d) (fraction_eq)) =
  any_fraction_is_additive_unit (fraction_neg x);
  fraction_neg x

let fraction_neg_uo (#a:Type) (#d: integral_domain #a) : (unary_op_on_units_of #(fraction d) fraction_add fraction_eq) = 
  fraction_neg_properties d;
  reveal_opaque (`%respects_equivalence) (respects_equivalence #(units_of #(fraction d) fraction_add fraction_eq)); 
  Classical.forall_intro_2 (fraction_neg_respects_equivalence_of_units #a #d);
  fraction_add_all_are_units #a #d;
  fraction_neg_u #a #d
 
let fraction_neg_yields_inverses_for_units_forall (#a:Type) (d: integral_domain #a) : Lemma (
  (
    fraction_addition_is_associative_lemma d;
    fraction_equivalence_respects_addition #a #d;
    fraction_add_all_are_units #a #d;
    yields_inverses_for_units #(fraction d) fraction_add fraction_eq (
      reveal_opaque (`%respects_equivalence) (respects_equivalence #(units_of #(fraction d) fraction_add fraction_eq));
      Classical.forall_intro_2 (fraction_neg_respects_equivalence_of_units #a #d);
      fraction_neg))
  ) =                                     
  reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #(fraction d));  
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d));  
  reveal_opaque (`%is_left_id_of) (is_left_id_of #(fraction d));  
  reveal_opaque (`%is_right_id_of) (is_right_id_of #(fraction d));  
  reveal_opaque (`%is_unit) (is_unit #(fraction d));  
  fraction_neg_is_inverse_for_addition #a #d; 
  ()
 
let fraction_additive_group (#a:Type) (#d: integral_domain #a) : commutative_group #(fraction d) = 
  fraction_equivalence_respects_addition #a #d;
  fraction_neg_is_inverse_for_addition #a #d;
  fraction_addition_is_associative_lemma d;
  fraction_negation_respects_equivalence #a #d;
  fraction_add_all_are_units #a #d;
  fraction_addition_is_associative_lemma d; 
  reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #(fraction d));   
  one_is_valid_denominator d;
  let zero = (Fraction d.addition.neutral d.multiplication.neutral) in
  fraction_additive_neutral_condition d zero;
  fraction_addition_is_commutative #a #d;
  fraction_neg_yields_inverses_for_units_forall d; 
  assert (all_are_units #(fraction d) fraction_add fraction_eq);
  Mkmagma #(fraction d) fraction_add fraction_eq (
      reveal_opaque (`%respects_equivalence) (respects_equivalence #(units_of #(fraction d) fraction_add fraction_eq));
      Classical.forall_intro_2 (fraction_neg_respects_equivalence_of_units #a #d);    
  fraction_neg) zero

let frac_eq_mul (#a:Type) (#d: integral_domain #a) : equivalence_wrt #(fraction d) fraction_mul = fraction_eq

private let fraction_unit_and_absorber_is_wtf (#a:Type) (#d: integral_domain #a) (x: fraction d) 
  : Lemma (requires is_unit x fraction_mul fraction_eq /\ is_absorber_of x fraction_mul fraction_eq) (ensures False) =   
  let ( *) = fraction_mul #a #d in
  let eq = fraction_eq #a #d in
  reveal_opaque (`%is_unit) (is_unit #(fraction d)); 
  reveal_opaque (`%is_symmetric) (is_symmetric #(fraction d)); 
  reveal_opaque (`%is_transitive) (is_transitive #(fraction d)); 
  let x' = IndefiniteDescription.indefinite_description_ghost (units_of ( *) eq) (fun x' -> (is_neutral_of (x * x') ( *) eq /\ is_neutral_of (x' * x) ( *) eq)) in
  let xx' = x * x' in
  let one = fraction_one #a #d in
  let zero = fraction_zero #a #d in
  assert (is_neutral_of xx' ( *) eq);
  assert (is_neutral_of one ( *) eq);
  neutral_is_unique ( *) eq one xx'; 
  assert (eq xx' one);
  absorber_lemma ( *) eq x x'; 
  assert (is_absorber_of xx' ( *) eq);
  absorber_is_unique ( *) eq zero xx';
  assert (eq xx' zero); 
  fraction_one_eq_zero_means_wtf #a d;
  ()

let fraction_nonabsorber_means_numerator_nonabsorber  (#a:Type) (#d: integral_domain #a) (x: fraction d) : Lemma (requires ~(is_absorber_of x fraction_mul fraction_eq)) (ensures ~(is_absorber_of x.num d.multiplication.op d.eq)) = frac_abs_cond x

let fraction_eq_condition (#a:Type) (#d: integral_domain #a) (x y: fraction d) : Lemma (requires d.eq (d.multiplication.op x.num y.den) (d.multiplication.op x.den y.num)) (ensures fraction_eq x y) = ()

#push-options "--ifuel 4 --fuel 2 --z3rlimit 30 --query_stats"
let fraction_nonabsorber_is_unit (#a:Type) (#d: integral_domain #a) (x: non_absorber_of (fraction_mul #a #d) (fraction_eq #a #d)) : Lemma (is_unit x fraction_mul fraction_eq) = 
  fraction_nonabsorber_means_numerator_nonabsorber x;
  assert (~(is_absorber_of x.num d.multiplication.op d.eq)); 
  let ( *) = d.multiplication.op in  
  let inv = d.multiplication.inv in  
  let eq : equivalence_wrt d.multiplication.op = d.eq in
  let up = d.unit_part_of in
  let np = d.normal_part_of in 
  let u = x.num in
  let v = x.den in
  let one = fraction_one #a #d in
  let d_one = d.multiplication.neutral in
  assert (one.num `d.eq` d_one);
  unit_and_normal_decomposition_lemma ( *) eq up np u;
  normal_part_of_non_absorber_is_valid_denominator #a #d x.num;
  let xsden : valid_denominator_of d = np x.num in
  let x' = Fraction (x.den * inv (up x.num)) xsden in
  let xx' = fraction_mul x x' in
  assert (xx'.num `eq` (x.num * (x.den * inv (up x.num))));
  assert (xx'.den `eq` (x.den * np x.num));
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  reveal_opaque (`%is_transitive) (is_transitive #a);  

  unit_and_normal_decomposition_lemma ( *) eq up np x.num;
  
  assert (xx'.num `eq` ((up x.num * np x.num) * (x.den * inv (up x.num)))); 
  comm_lemma eq ( *) (up x.num * np x.num) (x.den * inv (up x.num));
  assert (eq ((up x.num * np x.num) * (x.den * inv (up x.num))) ((x.den * inv (up x.num)) * (up x.num * np x.num)));
  assoc_lemma4 eq ( *) x.den (inv (up x.num)) (up x.num) (np x.num);
  assert (eq ((x.den * inv (up x.num)) * (up x.num * np x.num)) ( (x.den * (inv (up x.num) * up x.num)) * (np x.num)));
  assert (is_neutral_of (inv (up x.num) * up x.num) ( *) eq);
  neutral_lemma ( *) eq (inv (up x.num) * up x.num) x.den;
  equivalence_wrt_operation_lemma eq (x.den * (inv (up x.num) * up x.num)) x.den (np x.num);
   
  trans_lemma_4 eq xx'.num
                   ((x.den * inv (up x.num)) * (up x.num * np x.num))
                   ((x.den * (inv (up x.num) * up x.num)) * (np x.num))
                   xx'.den;
   
  assert ((xx'.num * d_one) `eq` (xx'.den * d_one)); 
  assert (fraction_eq xx' one);
  neutral_equivalent_is_neutral fraction_mul fraction_eq one xx';
  reveal_opaque (`%is_reflexive) (is_reflexive #(fraction d)); 
  reveal_opaque (`%is_symmetric) (is_symmetric #(fraction d)); 
  reveal_opaque (`%is_transitive) (is_transitive #(fraction d)); 
  assert (is_neutral_of (fraction_mul x x') fraction_mul fraction_eq); 
  fraction_mul_is_commutative x x';
  assert (fraction_eq (fraction_mul x x') (fraction_mul x' x));
  neutral_equivalent_is_neutral fraction_mul fraction_eq (fraction_mul x x') (fraction_mul x' x);
  assert (is_neutral_of (fraction_mul x' x) fraction_mul fraction_eq); 
  let ex_fun (ix) = is_neutral_of (x `fraction_mul` ix) fraction_mul fraction_eq /\ is_neutral_of (ix `fraction_mul` x) fraction_mul fraction_eq in
  
  assert (ex_fun x'); 
  Classical.exists_intro ex_fun x';
  reveal_opaque (`%is_unit) (is_unit #(fraction d)); 
  assert_spinoff (is_unit x fraction_mul fraction_eq); 
  ()
#pop-options


let fraction_unit_cant_be_absorber (#a:Type) (#d: integral_domain #a) (x: units_of fraction_mul fraction_eq) : Lemma (~(is_absorber_of x fraction_mul fraction_eq)) = 
  Classical.move_requires (fraction_unit_and_absorber_is_wtf #a #d) x

let fraction_absorber_cant_be_unit (#a:Type) (#d: integral_domain #a) (x: absorber_of fraction_mul fraction_eq) : Lemma (~(is_unit x fraction_mul fraction_eq)) =
  Classical.move_requires (fraction_unit_and_absorber_is_wtf #a #d) x

private let domain_unit_and_absorber_is_wtf (#a:Type) (#d: integral_domain #a) (x: a) 
  : Lemma (requires is_unit x d.multiplication.op d.eq /\ is_absorber_of x d.multiplication.op d.eq) (ensures False) =   
  let ( *) = d.multiplication.op in
  let eq = d.eq in
  reveal_opaque (`%is_unit) (is_unit #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  let x' = IndefiniteDescription.indefinite_description_ghost (units_of ( *) eq) (fun x' -> (is_neutral_of (x * x') ( *) eq /\ is_neutral_of (x' * x) ( *) eq)) in
  let xx' = x * x' in
  assert (is_neutral_of xx' ( *) eq);
  assert (is_neutral_of d.multiplication.neutral d.multiplication.op d.eq);
  neutral_is_unique ( *) eq d.multiplication.neutral xx'; 
  assert (eq xx' d.multiplication.neutral);
  absorber_lemma ( *) eq x x'; 
  assert (is_absorber_of xx' ( *) eq);
  absorber_is_unique ( *) eq d.addition.neutral xx';
  assert (eq xx' d.addition.neutral); 
  ()

let domain_unit_cant_be_absorber (#a:Type) (#d: integral_domain #a) (x: units_of d.multiplication.op d.eq) : Lemma (~(is_absorber_of x d.multiplication.op d.eq)) = 
  Classical.move_requires (domain_unit_and_absorber_is_wtf #a #d) x

let domain_absorber_cant_be_unit (#a:Type) (#d: integral_domain #a) (x: absorber_of d.multiplication.op d.eq) : Lemma (~(is_unit x d.multiplication.op d.eq)) =
  Classical.move_requires (domain_unit_and_absorber_is_wtf #a #d) x
 
#push-options "--ifuel 1 --fuel 0 --z3rlimit 3 --query_stats"
let fraction_inv (#a:Type) (#d: integral_domain #a) (x: units_of fraction_mul fraction_eq) 
  : (t:units_of fraction_mul fraction_eq{ is_neutral_of (t `fraction_mul` x) fraction_mul fraction_eq /\ 
                   is_neutral_of (x `fraction_mul` t) fraction_mul fraction_eq /\
                   t.num `d.eq` (d.multiplication.inv (d.unit_part_of x.num) `d.multiplication.op` x.den) /\
                   t.den `d.eq` (d.normal_part_of x.num)  }) = 
  fraction_unit_cant_be_absorber x;
  reveal_opaque (`%is_absorber_of) (is_absorber_of #(fraction d)); 
  reveal_opaque (`%is_unit) (is_unit #(fraction d)); 
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  reveal_opaque (`%equivalence_wrt_condition) (equivalence_wrt_condition #a); 
  non_absorber_fraction_has_nonzero_numerator x;  
  let ( *) = d.multiplication.op in
  let (+) = d.addition.op in
  let inv = d.multiplication.inv in
  let eq = d.eq in
  let up = d.unit_part_of in
  let np = d.normal_part_of in  
  assert (is_unit (up x.num) ( *) eq); 
  unit_inverse_is_unit ( *) d.eq d.multiplication.inv (up x.num);
  assert (is_unit (d.multiplication.inv (up x.num)) ( *) eq);
  let numerator : a = x.den * (inv (up x.num)) in
  unit_and_normal_decomposition_lemma ( *) eq up np x.num;
  assert (((up x.num) * (np x.num)) `eq` x.num);
  nonabsorber_equal_is_nonabsorber ( *) eq x.num (up x.num * np x.num);
  assert (~(is_absorber_of x.num ( *) eq));
  domain_nonzero_product_means_nonzero_factors d (up x.num) (np x.num);
  assert (~(is_zero_of d (d.normal_part_of x.num)));
  let denominator : valid_denominator_of d = d.normal_part_of x.num in
  let invfrac = Fraction numerator denominator in
  let xx' = fraction_mul x invfrac in
  let x'x = fraction_mul invfrac x in
  assert (xx'.num `eq` (x.den * (inv (up x.num) * x.num)));
  assert (xx'.num `eq` (x.den * (inv (up x.num) * (up x.num * np x.num))));
  assert ((inv (up x.num) * (up x.num * np x.num)) `eq` ((inv (up x.num) * up x.num) * (np x.num)));
  assert (xx'.num `eq` (x.den * (inv (up x.num) * up x.num) * np x.num));
  assert (is_neutral_of (inv (up x.num) * up x.num) ( *) eq);
  assert (xx'.num `eq` (x.den * np x.num));
  assert (xx'.den `eq` (x.den * np x.num));
  fraction_is_mul_neutral xx';
  fraction_is_mul_neutral x'x;   
  invfrac
#pop-options
  
let fraction_equality_lemma (#a: Type) (#d: integral_domain #a) (x y: fraction d)
  : Lemma (requires ((x.num `d.multiplication.op` y.den) `d.eq` (x.den `d.multiplication.op` y.num)))
          (ensures (fraction_eq x y /\ fraction_eq y x)) = symm_lemma fraction_eq y x

#push-options "--ifuel 4 --fuel 2 --z3rlimit 10 --query_stats"
let fraction_inv_respects_equivalence (#p:Type) (#d: integral_domain #p) (x y: non_absorber_of fraction_mul fraction_eq) 
  : Lemma (requires fraction_eq #p #d x y)
          (ensures fraction_eq #p #d (fraction_inv x) (fraction_inv y) /\ fraction_eq #p #d (fraction_inv y) (fraction_inv x)) = 
  let ( *) = d.multiplication.op in
  let inv = d.multiplication.inv in
  let eq : equivalence_wrt ( *) = d.eq in
  let up = d.unit_part_of in
  let np = d.normal_part_of in  
  let a = x.num in
  let b = x.den in
  let c = y.num in
  let d = y.den in  

  assert (((fraction_inv x).num * (fraction_inv y).den) `eq` (((inv (up a)) * b) * np c));
  assert (((fraction_inv x).den * (fraction_inv y).num) `eq` (np a * (inv (up c) * d)));

  symm_lemma eq (b*c) (a*d);
  assert ((b*c) `eq` (a*d));
  unit_and_normal_decomposition_lemma ( *) eq up np c;
  equivalence_wrt_operation_lemma eq c (up c * np c) b;
  trans_lemma eq (a * d) (b * c) (b * (up c * np c));
  assert ((b * (up c * np c)) `eq` (a * d));  
  equivalence_wrt_operation_lemma eq (b * (up c * np c)) (a*d) (inv (up c));
  comm_lemma eq ( *) (a*d) (inv (up c));
  trans_lemma eq (inv (up c) * (b * (up c * np c))) (inv (up c) * (a * d)) ((a*d) * (inv (up c)));
  assert ((inv (up c) * (b * (up c * np c))) `eq` (a * d * (inv (up c))));
  assoc_lemma3 eq ( *) b (up c) (np c);
  assert ((inv (up c) * (b * (up c * np c))) `eq` (inv (up c) * ((b * up c) * np c)));
  comm_lemma eq ( *) b (up c);
  assert ((inv (up c) * ((b * up c) * np c)) `eq` (inv (up c) * ((up c * b) * np c)));
  assoc_lemma4 eq ( *) (inv (up c)) (up c) b (np c);
  assert ((inv (up c) * ((up c * b) * np c)) `eq` ((inv (up c) * up c) * (b * np c)));
  trans_lemma_4 eq (inv (up c) * (b * (up c * np c)))
                   (inv (up c) * ((b * up c) * np c))
                   (inv (up c) * ((up c * b) * np c))
                   ((inv (up c) * up c) * (b * np c));
  partial_inverse_lemma ( *) eq inv (up c);
  partial_inverse_lemma ( *) eq inv (up a);
  assert (((inv (up c) * up c) * (b * np c)) `eq` (b * np c));
  trans_lemma_4 eq (b * np c) 
                   ((inv (up c) * up c) * (b * np c))  
                   (inv (up c) * (b * (up c * np c))) 
                   (a * d * (inv (up c)));
  assoc_lemma3 eq ( *) a d (inv (up c));
  trans_lemma eq (b * np c) (a * d * (inv (up c))) (a * (d * (inv (up c))));
  assert ((b * np c) `eq` (a * (d * inv (up c))));
  unit_and_normal_decomposition_lemma ( *) eq up np a;
  equivalence_wrt_operation_lemma eq (up a * np a) a (d * inv (up c));
  assert ((a * (d * inv (up c))) `eq` ((up a * np a) * (d * inv (up c))));
  trans_lemma eq (b * np c) (a * (d * inv (up c))) ((up a * np a) * (d * inv (up c)));
  assert ((b * np c) `eq` ((up a * np a) * (d * inv (up c))));
  assoc_lemma4 eq ( *) (up a) (np a) d (inv (up c));
  trans_lemma eq (b * np c)
                 ((up a * np a) * (d * inv (up c)))
                 (up a * (np a * (d * inv (up c))));
  assert ((b * np c) `eq` (up a * (np a * (d * inv (up c)))));

  equivalence_wrt_operation_lemma eq (b * np c) (up a * (np a * (d * inv (up c)))) (inv (up a));
  assert ((inv (up a) * (b * np c)) `eq` (inv (up a) * (up a * (np a * (d * inv (up c))))));
  assoc_lemma3 eq ( *) (inv (up a)) (up a) (np a * (d * (inv (up c))));
  assert ((inv (up a) * (up a * (np a * (d * inv (up c))))) `eq` ((inv (up a) * up a) * (np a * (d * (inv (up c))))));
  assert (is_neutral_of (inv (up a) * up a) ( *) eq);
  neutral_lemma ( *) eq (inv (up a) * up a) (np a * (d * (inv (up c))));
  assert (((inv (up a) * up a) * (np a * (d * (inv (up c))))) `eq` (np a * (d * (inv (up c))))); 
  comm_lemma eq ( *) d (inv (up c));
  equivalence_wrt_operation_lemma eq (d * (inv (up c))) (inv (up c) * d) (np a);
  trans_lemma eq ((inv (up a) * up a) * (np a * (d * (inv (up c))))) 
                 (np a * (d * inv (up c)))
                 (np a * (inv (up c) * d));
  trans_lemma_4 eq (inv (up a) * (b * np c))
                   (inv (up a) * (up a * (np a * (d * inv (up c)))))
                   ((inv (up a) * up a) * (np a * (d * (inv (up c)))))
                   (np a * (inv (up c) * d));
  assoc_lemma3 eq ( *) (inv (up a)) b (np c);
  trans_lemma eq (((inv (up a)) * b) * np c) 
                 (inv (up a) * (b * np c))
                 (np a * (inv (up c) * d));  
  assert  ( (((inv (up a)) * b) * np c) `eq` (np a * (inv (up c) * d)));
  trans_lemma_4 eq ((fraction_inv x).num * (fraction_inv y).den)
                   (((inv (up a)) * b) * np c)
                   (np a * (inv (up c) * d))
                   ((fraction_inv x).den * (fraction_inv y).num);
                   
  assert ( ((fraction_inv x).num * (fraction_inv y).den) `eq` ((fraction_inv x).den * (fraction_inv y).num) );
  fraction_equality_lemma (fraction_inv x) (fraction_inv y);
  ()

let fraction_nonabsorber_is_unit (#a:Type) (#d: integral_domain #a) (x: fraction d) : Lemma (requires ~(is_absorber_of x fraction_mul fraction_eq))
                                                                                            (ensures is_unit x fraction_mul fraction_eq) = admit()

let fraction_mul_cm (#a:Type) (#d: integral_domain #a) : commutative_monoid #(fraction d) = 
  Classical.forall_intro_2 (fraction_mul_is_commutative #a #d);
  let op : binary_op (fraction d) = fraction_mul in
  let eq : equivalence_wrt op = fraction_eq in
  let inv : unary_op_on_units_of op eq = fraction_inv in
  admit();

  Mkmagma op eq fraction_inv (fraction_one #a #d)  


unfold let invertible_mul (#a:Type) (#d: integral_domain #a) (x y: non_absorber_of #(fraction d) fraction_mul fraction_eq)
                       : non_absorber_of #(fraction d) fraction_mul fraction_eq = 
                       fraction_mul_domain_law x y;
                       fraction_mul x y

unfold let inv_mul (#a:Type) (#d: integral_domain #a) : binary_op (non_absorber_of #(fraction d) fraction_mul fraction_eq) = invertible_mul

let fraction_inverse_respects_equivalence (#a: Type) (#d: integral_domain #a) 
  : Lemma (respects_equivalence #(non_absorber_of #(fraction d) inv_mul fraction_eq) fraction_inv fraction_eq) = 

  admit();
  ()

let frac_inv2 (#a:Type) (#d: integral_domain #a) : partial_inverse_op_for #(fraction d) fraction_mul fraction_eq = 
  Classical.forall_intro_2 (fraction_inv_respects_equivalence #a #d);
  admit();
  fraction_inv

let fraction_eq_nonabs (#a:Type) (d: integral_domain #a) (x y: non_absorber_of #(fraction d) fraction_mul fraction_eq)=
  fraction_eq #a #d
  
let fraction_inverse_respects_equivalence (#a:Type) (d: integral_domain #a) : Lemma (respects_equivalence #(non_absorber_of #(fraction d) fraction_mul fraction_eq) fraction_inv (
    reveal_opaque (`%is_absorber_of) (is_absorber_of #(fraction d));
    let f_eq : equivalence_relation (non_absorber_of #(fraction d) fraction_mul fraction_eq) = fraction_eq in
    f_eq)) 
  = 
  
  admit()



let fraction_multiplicative_almost_group (#a:Type) (#d: integral_domain #a) : commutative_monoid #(fraction d) = 
  fraction_equivalence_respects_multiplication #a #d;
  Classical.forall_intro_2 (fraction_inv_respects_equivalence #a #d);
  admit();
  Classical.forall_intro_3 (fraction_mul_is_associative #a #d);
  Classical.forall_intro_2 (fraction_mul_is_commutative #a #d);

  let one = (Fraction d.multiplication.neutral d.multiplication.neutral) in
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d));
  Classical.forall_intro (fraction_mul_neutral_lemma one);
//  fraction_inv_yields_inverses_for_units

  Mkmagma #(fraction d) fraction_add fraction_eq (
      reveal_opaque (`%respects_equivalence) (respects_equivalence #(units_of #(fraction d) fraction_add fraction_eq));
      Classical.forall_intro_2 (fraction_neg_respects_equivalence_of_units #a #d);    
  fraction_neg) one


let fraction_multiplicative_group (#a:Type) (#d: integral_domain #a) : commutative_monoid #(fraction d) = 
  fraction_equivalence_respects_multiplication #a #d;
  Classical.forall_intro_2 (fraction_mul_is_commutative #a #d); 
  Classical.forall_intro_3 (fraction_mul_is_associative #a #d); 

  reveal_opaque (`%is_reflexive) (is_reflexive #a);   
  reveal_opaque (`%is_reflexive) (is_reflexive #(fraction d));   
  reveal_opaque (`%is_associative) (is_associative #(fraction d));   
  reveal_opaque (`%is_symmetric) (is_symmetric #(fraction d));   
  reveal_opaque (`%is_commutative) (is_commutative #(fraction d));   
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d));   
  reveal_opaque (`%is_left_id_of) (is_left_id_of #(fraction d));   
  reveal_opaque (`%is_right_id_of) (is_right_id_of #(fraction d));   
  reveal_opaque (`%equivalence_wrt_condition) (equivalence_wrt_condition #(fraction d));   
  reveal_opaque (`%respects_equivalence) (respects_equivalence #(fraction d));   
  reveal_opaque (`%yields_inverses_for_units) (yields_inverses_for_units #(fraction d));   
  one_is_valid_denominator d;
  let l = d.multiplication.neutral in
  let one = (Fraction l l) in
  fraction_is_mul_neutral #a #d one;
  assert (is_commutative #(fraction d) fraction_mul fraction_eq);
  assert (is_associative #(fraction d) fraction_mul fraction_eq);
  let aux() : Lemma(respects_equivalence #(units_of #(fraction d) fraction_mul fraction_eq) fraction_inv fraction_eq) = 
    Classical.forall_intro_2 (fraction_inv_respects_equivalence #a #d) in
//  Classical.forall_intro_2 (fraction_inv_respects_equivalence #a #d);
//  assert (respects_equivalence #(units_of #(fraction d) fraction_mul fraction_eq) fraction_inv fraction_eq);
  admit();  
  Mkmagma (fraction_mul #a #d) (fraction_eq #a #d) (fraction_inv #a #d) one
  //assert (equivalence_wrt_condition #(fraction d) fraction_mul fraction_eq); 
 
  //fraction_is_mul_neutral one;

