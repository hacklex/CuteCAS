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
unfold private let mul_of (#a:Type) (r: commutative_ring #a) : commutative_ring_mul r = r.multiplication.op

/// And this one is made private just for the sake of symmetry with mul_of
unfold private let add_of (#a:Type) (r: commutative_ring #a) : commutative_ring_add r = r.addition.op

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
unfold private let fractions_equal (#a: Type) (#d: euclidean_domain #a) (x: fraction d) (y: fraction d) = 
   ((x.num `mul_of d` y.den) `d.eq` (x.den `mul_of d` y.num)) 
 
private let equality_is_symmetric_lemma_oneway (#a:Type) (d: euclidean_domain #a) (x y: fraction d)
  : Lemma (fractions_equal x y ==> fractions_equal y x) = 
  if (fractions_equal x y) then (
    reveal_opaque (`%is_commutative) (is_commutative #a);   
    trans_lemma_4 d.eq (d.multiplication.op y.num x.den)
                       (d.multiplication.op x.den y.num) //commutative
                       (d.multiplication.op x.num y.den) //commutative
                       (d.multiplication.op y.den x.num) //what we needed
  )  
  
private let equality_is_symmetric_lemma (#a:Type) (d: euclidean_domain #a) (x y: fraction d)
  : Lemma (fractions_equal x y == fractions_equal y x) =  
  equality_is_symmetric_lemma_oneway d x y;  
  equality_is_symmetric_lemma_oneway d y x 

private let equality_is_symmetric (#a:Type) (d: euclidean_domain #a) 
  : Lemma (is_symmetric (fractions_equal #a #d)) = 
  Classical.forall_intro_2 (equality_is_symmetric_lemma d);
  reveal_opaque (`%is_symmetric) (is_symmetric #(fraction d))

/// This even pleases the eye. Especially when the lengths match.
private let equality_is_reflexive (#a:Type) (d: euclidean_domain #a) 
  : Lemma (is_reflexive (fractions_equal #a #d)) =   
    reveal_opaque (`%is_commutative) (is_commutative #a);
    reveal_opaque (`%is_reflexive) (is_reflexive #(fraction d))
    

/// Below are some leftovers from the times when the prover refused to verify even the obvious things
/// partly due to some arcane reasons (at rlimit 50+), and partly due to just going out of resources.
/// Well, currently the lemmas are written with certain amount of rigor, and mostly require minimal rlimit.
/// Still, I keep these just in case :)

let domain_law (#a:Type) (d: integral_domain #a) (x y: a)
  : Lemma (is_absorber_of (x `d.multiplication.op` y) d.multiplication.op d.eq 
       ==> (is_absorber_of x d.multiplication.op d.eq) \/ (is_absorber_of y d.multiplication.op d.eq)) 
  = reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #a)

let domain_law_other_zero (#a:Type) (d: integral_domain #a) (x y: a)
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
#push-options "--ifuel 2 --fuel 0 --z3rlimit 15"
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
   
#push-options "--ifuel 4 --fuel 0 --z3rlimit 15"
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
let product_of_denominators_is_denominator (#a:Type) (#d: euclidean_domain #a) (x y: fraction d)
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
    ) = 
    reveal_opaque (`%is_associative) (is_associative #a);
    reveal_opaque (`%is_transitive) (is_transitive #a);
    reveal_opaque (`%is_symmetric) (is_symmetric #a);
    //I didn't remove the assertions entirely, as they show the intent behind the invoked lemmas
    assoc_lemma3 eq op x y z;
    //assert (((x `op` y) `op` z) `eq` (x `op` (y `op` z)));
    equivalence_wrt_operation_lemma   #a #op eq ((x `op` y) `op` z) (x `op` (y `op` z)) w
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
 
private let final_step (#p:Type) (dom: euclidean_domain #p) (a c e: p) (b d f: valid_denominator_of dom)
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
private let fractions_equality_transitivity_lemma (#p: Type) (dom: euclidean_domain #p) 
  (x: fraction dom) 
  (y: (t:fraction dom{fractions_equal x t}))
  (z: (t:fraction dom{fractions_equal y t})) : Lemma (fractions_equal x z) =  
    reveal_opaque (`%is_commutative) (is_commutative #p); 
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
private let fractions_equality_transitivity_implication_lemma (#a:Type) (d: euclidean_domain #a) (x y z: fraction d) 
  : Lemma (fractions_equal x y /\ fractions_equal y z ==> fractions_equal x z) = 
  if (fractions_equal x y && fractions_equal y z) 
  then fractions_equality_transitivity_lemma d x y z

/// This one is used to construct the equivalence_relation out of fractions_equal
/// Otherwise we can't construct the ring, never mind the field.
private let equality_is_transitive (#p:Type) (d: euclidean_domain #p) : Lemma (is_transitive (fractions_equal #p #d)) = 
  reveal_opaque (`%is_transitive) (is_transitive #(fraction d));
  Classical.forall_intro_3 (fractions_equality_transitivity_implication_lemma d)
  
/// Once all the necessary lemmas are proven, we've got the equivalence_relation for fractions
private let equiv (#a:Type) (d: euclidean_domain #a) : equivalence_relation (fraction d) = 
  equality_is_reflexive d;
  equality_is_symmetric d;
  equality_is_transitive d; 
  fractions_equal
 
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
  reveal_opaque (`%is_commutative) (is_commutative #a); 
  reveal_opaque (`%is_transitive) (is_transitive #a);
  let eq : equivalence_wrt d.multiplication.op = d.eq in // mul_of d is needed for lemmas below
  equivalence_wrt_operation_lemma eq y.den x.den y.num; // we need exactly equivalence wrt. mul,
  equivalence_wrt_operation_lemma eq x.num y.num y.den  // in order to prove this lemma
 
private let sys_eq_means_eq (#a:Type) (eq: equivalence_relation a) (x y: a) : Lemma (x == y ==> x `eq` y) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #a)

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
   sys_eq_means_eq d.eq rn ((x.num `d.multiplication.op` y.den) `d.addition.op` (x.den `d.multiplication.op` y.num));
   sys_eq_means_eq d.eq rd (x.den `d.multiplication.op` y.den);
 //  assert (rn `d.eq` ((x.num `d.multiplication.op` y.den) `d.addition.op` (x.den `d.multiplication.op` y.num))); 
 //  assert (rd `d.eq` (x.den `d.multiplication.op` y.den));   
   res // == does not mean `d.eq`, surprisingly so. Proved automatically above tho...
 
/// These two lemmas may look obvious, but proofs below fail without calling it.
private let fractions_add_num_lemma (#a:Type) (d:euclidean_domain #a) (x y: fraction d)
  : Lemma ((fractions_add d x y).num `d.eq` ((x.num `d.multiplication.op` y.den) `d.addition.op` (x.den `d.multiplication.op` y.num))) = ()
private let fractions_add_den_lemma (#a:Type) (d:euclidean_domain #a) (x y: fraction d)
  : Lemma ((fractions_add d x y).den `d.eq` (x.den `d.multiplication.op` y.den)) = ()
 
private let numerator_commutativity_lemma (#a:Type) (d: euclidean_domain #a) (x y z w: a) 
  : Lemma ( ( (x `d.multiplication.op` w) `d.addition.op` (y `d.multiplication.op` z)) `d.eq`
            ( (w `d.multiplication.op` x) `d.addition.op` (z `d.multiplication.op` y))) = 
   dom_add_assoc d;
   dom_mul_assoc d;
   auxiliary_add_flip_lemma d.eq d.multiplication.op d.addition.op x w y z

private let denominator_commutativity_lemma (#a:Type) (d: euclidean_domain #a) (x y: a) 
  : Lemma ((x `d.multiplication.op` y) `d.eq` (y `d.multiplication.op` x)) = 
  reveal_opaque (`%is_commutative) (is_commutative #a) 
 
private let fractions_add_is_commutative (#a:Type) (#d: euclidean_domain #a) (x y: fraction d) 
  : Lemma (equiv d (fractions_add d x y) (fractions_add d y x)) 
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
  : Lemma (((x `add` y) `mul` z) `eq` ((x `mul` z) `add` (y `mul` z))) = 
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a) 
    
private let distributivity_lemma_left (#a:Type) (eq: equivalence_relation a) (mul: binary_op a) (add: binary_op a{is_fully_distributive mul add eq}) (x y z: a)
  : Lemma ((x `mul` (y `add` z)) `eq` ((x `mul` y) `add` (x `mul` z))) =  
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a) 
 
private let fractions_add_is_associative (#a:Type) (d: euclidean_domain #a) (x y z: fraction d) 
  : Lemma ((fractions_add d (fractions_add d x y) z) `equiv d` (fractions_add d x (fractions_add d y z))) = 
   reveal_opaque (`%is_associative) (is_associative #a); 
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
   assert (equiv d sum_1 sum_2); // production variant will only contain the lemma invocations of course :)
   ()  

private let fractions_addition_is_associative_lemma (#a:Type) (d: euclidean_domain #a) 
  : Lemma (is_associative (fractions_add d) (equiv d)) = 
  reveal_opaque (`%is_associative) (is_associative #(fraction d));   
  Classical.forall_intro_3 (fractions_add_is_associative d)

let def_eq_means_eq (#a:Type) (eq: equivalence_relation a) (x:a) (y:a{y==x}) : Lemma (x `eq` y) = reveal_opaque (`%is_reflexive) (is_reflexive #a)

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
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a); 
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
  neutral_is_unique d.addition.op d.eq x.num d.addition.neutral;
  neutral_equivalent_is_neutral add eq d.addition.neutral x.num;
  absorber_equal_is_absorber mul eq d.addition.neutral x.num;
  assert(is_absorber_of x.num mul eq);
  assert((x.num `mul` y.den) `eq` x.num);
  symm_lemma eq x.num (x.num `mul` y.den);
  eq_wrt_emulated #a #add eq x.num (x.num `mul` y.den) (x.den `mul` y.num); 
  equivalence_wrt_operation_lemma #a #add eq x.num (x.num `mul` y.den) (x.den `mul` y.num); 
  admit();
  assert (((x.num `mul` y.den) `add` (x.den `mul` y.num)) `eq` (x.num `add` (x.den `mul` y.num)));
  assert_spinoff(sum.num `eq` ((x.num `mul` y.den) `add` (x.den `mul` y.num)));
  trans_lemma eq sum.num ((x.num `mul` y.den) `add` (x.den `mul` y.num)) (x.num `add` (x.den `mul` y.num)); 
  ()
