module RationalNumbers

open AlgebraTypes

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1"

let is_valid_denominator_of (#a:Type) (d: integral_domain #a) (x: a) = 
  is_unit_normal d.multiplication.op d.eq d.unit_part_of x /\ ~(is_zero_of d x)

type valid_denominator_of (#a:Type) (d: integral_domain #a) = (t: a{is_valid_denominator_of d t})

let one_is_valid_denominator (#a:Type) (d: integral_domain #a) : Lemma (is_valid_denominator_of d d.multiplication.neutral) = 
  reveal_opaque (`%is_neutral_invariant) (is_neutral_invariant #a);  
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

private let distributivity_lemma_right (#a:Type) (eq: equivalence_relation a) (mul: binary_op a) (add: binary_op a{is_fully_distributive mul add eq}) (x y z: a)
  : Lemma (((x `add` y) `mul` z) `eq` ((x `mul` z) `add` (y `mul` z))) = 
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a) 
    
private let distributivity_lemma_left (#a:Type) (eq: equivalence_relation a) (mul: binary_op a) (add: binary_op a{is_fully_distributive mul add eq}) (x y z: a)
  : Lemma ((x `mul` (y `add` z)) `eq` ((x `mul` y) `add` (x `mul` z))) =  
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a) 
 
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



#push-options "--ifuel 0 --fuel 0 --z3rlimit 1 --query_stats"
private let fraction_additive_neutral_lemma (#a:Type) (d: integral_domain #a) (x: fraction d{is_neutral_of x.num d.addition.op d.eq}) (y: fraction d) 
  : Lemma ((x `fraction_add` y) `fraction_eq` y /\ (y `fraction_add` x `fraction_eq` y))
  = 
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a); 
  reveal_opaque (`%is_neutral_of) (is_neutral_of #a); 
   reveal_opaque (`%is_associative) (is_associative #a); 
   reveal_opaque (`%is_reflexive) (is_reflexive #a); 
   reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  let mul = d.multiplication.op in
  let add = d.addition.op in  
  let eq = d.eq in
  let sum = fraction_add x y in 
// assert (is_absorber_of d.addition.neutral mul eq); 
//  assert (is_neutral_of d.addition.neutral d.addition.op d.eq);  
  neutral_is_unique add eq x.num d.addition.neutral; 
//  assert (eq x.num d.addition.neutral);  
  absorber_equal_is_absorber mul eq d.addition.neutral x.num;
  fraction_add_num_lemma d x y;
//  assert (sum.num `eq` ((x.num `mul` y.den) `add` (x.den `mul` y.num)));
  absorber_lemma mul eq x.num y.den;
  absorber_equal_is_absorber mul eq x.num (x.num `mul` y.den); 
  absorber_is_unique mul eq d.addition.neutral (x.num `mul` y.den);
  neutral_equivalent_is_neutral add eq d.addition.neutral (x.num `mul` y.den);
  neutral_is_unique add eq d.addition.neutral (x.num `mul` y.den);
  neutral_lemma add eq (x.num `mul` y.den) (x.den `mul` y.num);
//  assert ((x.num `mul` y.den) `add` (x.den `mul` y.num) `eq` (x.den `mul` y.num));
  equivalence_wrt_operation_lemma #a #mul eq  ((x.num `mul` y.den) `add` (x.den `mul` y.num)) (x.den `mul` y.num) y.den;
//  assert (((x.den `mul` y.num) `mul` y.den) `eq` (x.den `mul` (y.num `mul` y.den))); 
  comm_lemma eq mul y.den y.num;
  equivalence_wrt_operation_lemma #a #mul eq (y.num `mul` y.den) (y.den `mul` y.num) x.den;
  trans_lemma_4 eq (((x.num `mul` y.den) `add` (x.den `mul` y.num)) `mul` y.den)  ((x.den `mul` y.num) `mul` y.den) (x.den `mul` (y.num `mul` y.den)) (x.den `mul` (y.den `mul` y.num));
 // assert ((x.den `mul` (y.den `mul` y.num)) `eq` ((x.den `mul` y.den) `mul` y.num));
  trans_lemma eq (((x.num `mul` y.den) `add` (x.den `mul` y.num)) `mul` y.den) (x.den `mul` (y.den `mul` y.num)) ((x.den `mul` y.den) `mul` y.num);
  fraction_add_is_commutative y x;
  trans_lemma fraction_eq (y `fraction_add` x) (x `fraction_add` y) y;
  ()

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

private let fraction_mul_neutral_lemma (#a:Type) (#d: integral_domain #a) (x: fraction d{is_neutral_of x.num d.multiplication.op d.eq /\ is_neutral_of x.den d.multiplication.op d.eq}) (y: fraction d)
  : Lemma (x `fraction_mul` y `fraction_eq` y /\ y `fraction_mul` x `fraction_eq` y) =   
  neutral_lemma d.multiplication.op d.eq x.num y.num;
  neutral_lemma d.multiplication.op d.eq x.den y.den; 
  equal_early_escape_lemma (fraction_mul x y) y;
  fraction_mul_is_commutative x y;
  trans_lemma fraction_eq (y `fraction_mul` x) (x `fraction_mul` y) y  
  

private let fraction_zero_is_neutral_lemma (#a:Type) (#d: integral_domain #a) (x: fraction d{is_neutral_of x.num d.addition.op d.eq})  
  : Lemma (is_neutral_of x fraction_add fraction_eq) =   
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d)); 
  reveal_opaque (`%is_left_id_of) (is_left_id_of #(fraction d)); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #(fraction d)); 
  Classical.forall_intro (fraction_additive_neutral_lemma d x)

private let fraction_one_is_neutral_lemma (#a:Type) (#d: integral_domain #a) (x: fraction d{is_neutral_of x.num d.multiplication.op d.eq /\ is_neutral_of x.den d.multiplication.op d.eq}) : Lemma (is_neutral_of x (fraction_mul) fraction_eq) =
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d)); 
  reveal_opaque (`%is_left_id_of) (is_left_id_of #(fraction d)); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #(fraction d)); 
  Classical.forall_intro (fraction_mul_neutral_lemma x)

/// Proof that fraction addition respects fraction equality is lengthy, so I only commented out the intermediate asserts,
/// but dare not remove them, as they help understanding the purpose of the proof steps 
private let fraction_equivalence_respects_add (#a:Type) (#d: integral_domain #a) (e1: fraction d) (e2: fraction d{e1 `fraction_eq` e2 }) (x: fraction d) 
  : Lemma ((x `fraction_add` e1) `fraction_eq` (x `fraction_add` e2) /\ (e1 `fraction_add` x ) `fraction_eq` (e2 `fraction_add` x)) = 
  let mul = d.multiplication.op in
  let eq = d.eq in
  let add = d.addition.op in 
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a); 
  reveal_opaque (`%is_right_distributive) (is_right_distributive #a); 
  reveal_opaque (`%is_left_distributive) (is_left_distributive #a); 
  //assert ((x `fraction_add` e1).num `d.eq`  ((x.num `mul` e1.den) `add` (x.den `mul` e1.num)));
  //assert ((x `fraction_add` e2).num `d.eq`  ((x.num `mul` e2.den) `add` (x.den `mul` e2.num)));
  //assert ((x `fraction_add` e1).den `d.eq` (x.den `mul` e1.den));
  //assert ((x `fraction_add` e2).den `d.eq` (x.den `mul` e2.den));
  right_distributivity_lemma mul add d.eq (x.num `mul` e1.den) (x.den `mul` e1.num) (x.den `mul` e2.den);
  //assert ( (((x.num `mul` e1.den) `add` (x.den `mul` e1.num)) `mul` (x.den `mul` e2.den)) `d.eq`  (((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) 
  //                                                                                          `add`  ((x.den `mul` e1.num) `mul` (x.den `mul` e2.den))));
  //we will carefully transform ad into bc, as (a/b=c/d) is defined as (ad=bc)
  let left_side = (fraction_add x e1).num `mul` (fraction_add x e2).den in
  //let right_side = (fraction_add x e1).den `mul` (fraction_add x e2).num in

  //assert (left_side `eq` ( ( (x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) `add` ( (x.den `mul` e1.num) `mul` (x.den `mul` e2.den))));
  //assert ((fraction_add x e1).den `eq` (x.den `mul` e1.den));
  //assert ((fraction_add x e2).num `eq` ((x.num `mul` e2.den) `add` (x.den `mul` e2.num)));
  
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
  //assert ( ((x.den `mul` (e1.den `mul` e2.num)) `mul` x.den) `eq` ((x.den `mul` e1.den) `mul` (e2.num `mul` x.den)));
  comm_lemma eq mul e2.num x.den;
  equivalence_wrt_operation_lemma #a #mul eq (mul e2.num x.den) (mul x.den e2.num) (x.den `mul` e1.den); 
  trans_lemma_4 eq  ((x.den `mul` (e1.num `mul` e2.den)) `mul` x.den)
                    ((x.den `mul` (e1.den `mul` e2.num)) `mul` x.den)
                    ((x.den `mul` e1.den) `mul` (e2.num `mul` x.den))
                    ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num));
  //assert (eq  ((x.den `mul` e1.num) `mul` (x.den `mul` e2.den)) ((x.den `mul` e1.num) `mul` (e2.den `mul` x.den)));
  //assert (eq  ((x.den `mul` e1.num) `mul` (e2.den `mul` x.den)) ((x.den `mul` (e1.num `mul` e2.den)) `mul` x.den));
  trans_lemma_4 eq  ((x.den `mul` e1.num) `mul` (x.den `mul` e2.den))
                    ((x.den `mul` e1.num) `mul` (e2.den `mul` x.den))  
                    ((x.den `mul` (e1.num `mul` e2.den)) `mul` x.den)
                    ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num));
  equivalence_wrt_operation_lemma #a #add eq ((x.den `mul` e1.num) `mul` (x.den `mul` e2.den))
                                             ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num))
                                             ((x.num `mul` e1.den) `mul` (x.den `mul` e2.den));
  trans_lemma eq left_side  ( ((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) `add` ((x.den `mul` e1.num) `mul` (x.den `mul` e2.den)))
                            ( ((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) `add` ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num)));                        
  //assert (left_side `eq` ( ((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) `add` ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num))));
  assoc_lemma4 eq mul x.num e1.den x.den e2.den;
  comm_lemma eq mul e1.den x.den;
  equivalence_wrt_operation_lemma #a #mul eq (e1.den `mul` x.den) (x.den `mul` e1.den) x.num;
  equivalence_wrt_operation_lemma #a #mul eq (x.num `mul` (e1.den `mul` x.den)) (x.num `mul` (x.den `mul` e1.den)) e2.den;
  assoc_lemma4 eq mul x.num x.den e1.den e2.den;
  trans_lemma   eq ((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) //assoc
                   ((x.num `mul` (e1.den `mul` x.den)) `mul` e2.den) //comm
                   ((x.num `mul` (x.den `mul` e1.den)) `mul` e2.den);
  comm_lemma eq mul x.num (x.den `mul` e1.den);
  equivalence_wrt_operation_lemma #a #mul eq (mul x.num (mul x.den e1.den)) (mul (mul x.den e1.den) x.num) e2.den;
  //assert ( eq ((x.num `mul` (x.den `mul` e1.den)) `mul` e2.den) (((x.den `mul` e1.den) `mul` x.num) `mul` e2.den));
  assoc_lemma4 eq mul x.den e1.den x.num e2.den;
  trans_lemma_4 eq ((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) 
                   ((x.num `mul` (x.den `mul` e1.den)) `mul` e2.den)
                   (((x.den `mul` e1.den) `mul` x.num) `mul` e2.den)
                   ((x.den `mul` e1.den) `mul` (x.num `mul` e2.den));
  equivalence_wrt_operation_lemma #a #add eq  ((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) 
                                              ((x.den `mul` e1.den) `mul` (x.num `mul` e2.den))
                                              ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num));
  trans_lemma eq left_side (((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) `add` ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num)))
                           (((x.den `mul` e1.den) `mul` (x.num `mul` e2.den)) `add` ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num)));
  left_distributivity_lemma mul add eq (mul x.den e1.den) (mul x.num e2.den) (mul x.den e2.num);
  symm_lemma eq (((x.den `mul` e1.den) `mul` (x.num `mul` e2.den)) `add` ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num))) ((x.den `mul` e1.den) `mul` ((x.num `mul` e2.den) `add` (x.den `mul` e2.num)));
  trans_lemma eq left_side (((x.den `mul` e1.den) `mul` (x.num `mul` e2.den)) `add` ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num)))
                           ((x.den `mul` e1.den) `mul` ((x.num `mul` e2.den) `add` (x.den `mul` e2.num)));
  //assert (left_side `eq` right_side);
  //assert (fraction_eq (fraction_add x e1) (fraction_add x e2));
  // The rest is trivial, just using commutativity again.
  fraction_add_is_commutative x e1;
  fraction_add_is_commutative x e2;
  trans_lemma_4 fraction_eq (fraction_add e1 x) (fraction_add x e1) (fraction_add x e2) (fraction_add e2 x);
() 

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

//let is_inverse_operation_for (#a: Type) (inv: unary_op a) (op: binary_op a) (eq: equivalence_relation a) 
//  = (forall (x:a). is_neutral_of (op x (inv x)) op eq /\ is_neutral_of (op (inv x) x) op eq)

private let fraction_neg_is_inverse_for_add (#a:Type) (#d: integral_domain #a) (x: fraction d) : Lemma (
  is_neutral_of (fraction_add x (fraction_neg x)) fraction_add fraction_eq /\
  is_neutral_of (fraction_add (fraction_neg x) x) fraction_add fraction_eq) = 
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
  reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a); 
  reveal_opaque (`%is_left_distributive) (is_left_distributive #a); 
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

let fraction_additive_group (#a:Type) (#d: integral_domain #a) : commutative_group #(fraction d) = 
  fraction_equivalence_respects_addition #a #d;
  fraction_neg_is_inverse_for_addition #a #d;
  fraction_negation_respects_equivalence #a #d;
  fraction_addition_is_associative_lemma d;  
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d)); 
  reveal_opaque (`%is_left_id_of) (is_left_id_of #(fraction d)); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #(fraction d)); 
  one_is_valid_denominator d;
  let zero = (Fraction d.addition.neutral d.multiplication.neutral) in
  Classical.forall_intro (fraction_additive_neutral_lemma d zero);
  Classical.forall_intro_2 (fraction_add_is_commutative #a #d);
  reveal_opaque (`%is_commutative) (is_commutative #(fraction d)); 
  Mkmagma (fraction_add #a #d) (fraction_eq #a #d) (fraction_neg #a #d) (Fraction d.addition.neutral d.multiplication.neutral)
