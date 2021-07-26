module RationalNumbers

open AlgebraTypes

let is_valid_denominator_of (#a:Type) (d: euclidean_domain #a) (x: a) = 
  is_unit_normal d.multiplication.op d.eq d.unit_part_of x /\
  ~(is_zero_of d x)

type valid_denominator_of (#a:Type) (d: euclidean_domain #a) = (t: a{is_valid_denominator_of d t})

let denominator_is_unit_normal (#a: Type) (#d: euclidean_domain #a) (x: valid_denominator_of d)
  : Lemma (is_unit_normal d.multiplication.op d.eq d.unit_part_of x) = ()

let denominator_is_nonzero (#a:Type) (d: euclidean_domain #a) (x:a{is_valid_denominator_of d x})
  : Lemma (~(is_absorber_of x d.multiplication.op d.eq)) = ()


type fraction (#a:Type) (d: euclidean_domain #a) = 
 | Fraction : (num: a) -> (den: valid_denominator_of d) -> fraction d

let den_is_valid (#a:Type) (#d: euclidean_domain #a) (x: fraction d) : Lemma (is_valid_denominator_of d x.den) = ()

let fractions_equal (#a: Type) (#d: euclidean_domain #a) (x: fraction d) (y: fraction d) = 
   let mul = d.multiplication.op in
   let add = d.addition.op in 
   let inv = d.addition.inv in
   ((x.num `mul` y.den) `d.eq` (x.den `mul` y.num)) 

let equality_is_reflexive (#a:Type) (d: euclidean_domain #a) : Lemma (is_reflexive (fractions_equal #a #d)) = ()
let equality_is_symmetric (#a:Type) (d: euclidean_domain #a) : Lemma (is_symmetric (fractions_equal #a #d)) = ()

let mul_cancelation_law (#a:Type) (#d: integral_domain #a) (x y: a) (z: non_absorber_of d.multiplication.op d.eq) 
  : Lemma (((x `d.multiplication.op` z) `d.eq` (y `d.multiplication.op` z)) <==> (x `d.eq` y))
  = ()

let domain_law (#a:Type) (d: integral_domain #a) (x y: a)
  : Lemma (is_absorber_of (x `d.multiplication.op` y) d.multiplication.op d.eq ==> (is_absorber_of x d.multiplication.op d.eq) \/ (is_absorber_of y d.multiplication.op d.eq)) 
  = assert (has_no_absorber_divisors d.multiplication.op d.eq)

let domain_law_other_zero (#a:Type) (d: integral_domain #a) (x y: a)
  : Lemma (is_absorber_of (x `d.multiplication.op` y) d.multiplication.op d.eq /\ ~(is_absorber_of y d.multiplication.op d.eq) ==> is_absorber_of x d.multiplication.op d.eq) = ()


let domain_law_fork (#a:Type) (d: integral_domain #a) (x y z:a) 
  : Lemma ( ((x `d.multiplication.op` y) `d.eq` (x `d.multiplication.op` z)) <==>
            (is_absorber_of x d.multiplication.op d.eq \/ (y `d.eq` z)))
  = ()

let prod_of_nonzeros_is_nonzero (#a: Type) (#d: integral_domain #a) (x y: non_absorber_of d.multiplication.op d.eq) 
  : Lemma (~(is_absorber_of (x `d.multiplication.op` y) d.multiplication.op d.eq)) = ()


let product_of_denominators_is_denominator (#a:Type) (#d: euclidean_domain #a) (x y: fraction d)
  : Lemma (is_valid_denominator_of d (d.multiplication.op x.den y.den)) = 
   let mul = d.multiplication.op in
   let eq = d.eq in
   assert (~(is_absorber_of (x.den `mul` y.den) mul eq));
   product_of_unit_normals_is_normal d.unit_part_of x.den y.den;
   assert (is_unit_normal mul eq d.unit_part_of (x.den `mul` y.den));
  ()


let eq_respect_lemma (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) (x y z w: a) 
  : Lemma (requires x `eq` w /\ (x `op` y) `eq` z) (ensures (w `op` y) `eq` z) = equivalence_wrt_operation_lemma_twoway #a #op eq x w y 

let eq_respect_lemma_r (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) (x y z w: a) 
  : Lemma (requires x `eq` w /\ (y `op` x) `eq` z) (ensures (y `op` w) `eq` z) = equivalence_wrt_operation_lemma_twoway #a #op eq x w y 

let trans_lemma (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) (x:a) (y:a{x `eq` y}) (z:a{y `eq` z})
  : Lemma (x `eq` z) = ()

let assoc_lemma3 (#a:Type) (eq: equivalence_relation a) (op: binary_op a{is_associative op eq}) (x y z: a) 
  : Lemma (((x `op` y) `op` z) `eq` (x `op` (y `op` z))) = ()

let assoc_lemma (#a:Type) (eq: equivalence_relation a) (op: binary_op a{is_associative op eq /\ equivalence_wrt_condition op eq }) (x y z w: a) 
  : Lemma (
     (((x `op` y) `op` z) `op` w) `eq` (x `op` (y `op` (z `op` w))) /\
     (((x `op` y) `op` z) `op` w) `eq` ((x `op` y) `op` (z `op` w)) /\
     (((x `op` y) `op` z) `op` w) `eq` (((x `op` (y `op` z)) `op` w))
    ) = 
      assoc_lemma3 eq op x y z;
      assert (((x `op` y) `op` z) `eq` (x `op` (y `op` z)));
      equivalence_wrt_operation_lemma_twoway #a #op eq ((x `op` y) `op` z) (x `op` (y `op` z)) w;
      assert ((((x `op` y) `op` z) `op` w) `eq` (((x `op` (y `op` z)) `op` w)));
    ()

let symm_lemma (#a: Type) (eq: equivalence_relation a) (x:a) (y:(t:a{t `eq` x})) : Lemma (x `eq` y /\ y `eq` x) = ()

let comm_lemma (#a:Type) (eq: equivalence_relation a) (op: binary_op a{is_commutative op eq}) (x y: a)
  : Lemma ( (x `op` y) `eq` (y `op` x)) = ()

let assoc_forall_lemma (#a:Type) (eq: equivalence_relation a) (op: binary_op a{is_associative op eq})
  : Lemma (is_associative op eq) = ()

let pure_nonzero (#a:Type) (d: euclidean_domain #a) (x: non_absorber_of d.multiplication.op d.eq) : (t:a{~(t `d.eq` d.addition.neutral)}) = nonzero_is_not_equal_to_add_neutral_p d x; x

let dom_zero_absorbing_lemma (#a:Type) (dom: euclidean_domain #a) (z: a{dom.eq z dom.addition.neutral}) (p:a)
  : Lemma ((z `dom.multiplication.op` p) `dom.eq` z /\ (p `dom.multiplication.op` z) `dom.eq` z) = 
    assert(is_absorber_of dom.addition.neutral dom.multiplication.op dom.eq); 
    absorber_eq_is_also_absorber dom.multiplication.op dom.eq dom.addition.neutral z;
    assert (is_absorber_of z dom.multiplication.op dom.eq);       
    ()
let dom_zero_absorbing_lemma_neut (#a:Type) (dom: euclidean_domain #a) (z: a{dom.eq z dom.addition.neutral}) (p:a)
  : Lemma ((z `dom.multiplication.op` p) `dom.eq` dom.addition.neutral /\ (p `dom.multiplication.op` z) `dom.eq` dom.addition.neutral) = 
    dom_zero_absorbing_lemma dom z p;
    trans_lemma dom.multiplication.op dom.eq (z `dom.multiplication.op` p) z dom.addition.neutral;
    trans_lemma dom.multiplication.op dom.eq (p `dom.multiplication.op` z) z dom.addition.neutral;
    ()
 
#push-options "--ifuel 4 --fuel 4 --z3rlimit 15"
let auxiliary_eq_lemma (#p: Type) (dom: euclidean_domain #p) 
  (a:p) (b: valid_denominator_of dom)
  (c:p) (d: (t:valid_denominator_of dom{(dom.multiplication.op a t) `dom.eq` (dom.multiplication.op b c)  }))
  (e:p) (f: (t:valid_denominator_of dom{(dom.multiplication.op c t) `dom.eq` (dom.multiplication.op d e)  })) 
  : Lemma (requires 
    (((c `dom.multiplication.op` d) `dom.multiplication.op` (b `dom.multiplication.op` e))  `dom.eq`  
     ((c `dom.multiplication.op` d) `dom.multiplication.op` (a `dom.multiplication.op` f))))
          (ensures (b `dom.multiplication.op` e) `dom.eq` (a `dom.multiplication.op` f)) = 
    
    let mul = dom.multiplication.op in
    let zero = dom.addition.neutral in
    let eq = dom.eq in 
     
    domain_law_fork dom (c `mul` d) (b `mul` e) (a `mul` f);
    zero_is_equal_to_add_neutral_p dom (c `mul` d) ;
    assert ((b `mul` e) `eq` (a `mul` f) || ((c `mul` d) `eq` zero));
    if (not((c `mul` d) `eq` zero)) then () else (
      assert (is_absorber_of (c `mul` d) mul eq <==> ((c `mul` d) `eq` zero));
      assert (is_valid_denominator_of dom d);
      denominator_is_nonzero dom d;
      assert (~(is_absorber_of d mul eq));   
      nonzero_is_not_equal_to_add_neutral_p dom d;
      assert (~(d `eq` zero));
      assert ((c `mul` d) `eq` zero);
      domain_law_other_zero dom c d;      
      assert (is_absorber_of c mul eq); 
      zero_is_equal_to_add_neutral_p dom c;
      assert (c `eq` zero);
      dom_zero_absorbing_lemma_neut dom c b;
      assert ((c `mul` b) `eq` zero);
      assert ((b `mul` c) `eq` (c `mul` b));
      trans_lemma mul eq (b `mul` c) (c `mul` b) zero;      
      assert ((a `mul` d) `eq` (b `mul` c));
      assert ((b `mul` c) `eq` zero);
      trans_lemma mul eq (a `mul` d) (b `mul` c) zero;      
      assert ((a `mul` d) `eq` zero);
      dom_prod_zero_lemma dom a d;
      assert (a `eq` zero \/ d `eq` zero);
      denominator_is_nonzero dom d;
      assert (~( d `eq` zero));
      assert (a `eq` zero);
      assert ((c `mul` f) `eq` (d `mul` e));
      dom_zero_absorbing_lemma_neut dom c f;
      assert ((c `mul` f) `eq` zero);
      symm_lemma eq (d `mul` e) (c `mul` f);
      assert ((d `mul` e) `eq` (c `mul` f));
      trans_lemma mul eq (d `mul` e) (c `mul` f) zero;
      assert ((d `mul` e) `eq` zero);
      dom_prod_zero_lemma dom d e;
      assert (e `eq` zero);
      dom_zero_absorbing_lemma_neut dom e b;
      assert ((b `mul` e) `eq` zero);
      dom_zero_absorbing_lemma_neut dom a f;
      assert ((a `mul` f) `eq` zero);
      two_zeros_are_equal dom (b `mul` e) (a `mul` f); 
      ()
    )

    
#push-options "--ifuel 4 --fuel 4 --z3rlimit 25"
let transitivity_lemma (#p:Type) (d: euclidean_domain #p) 
  (x: fraction d) 
  (y: (t:fraction d{fractions_equal x t}))
  (z: (t:fraction d{fractions_equal y t})) : Lemma (fractions_equal x z) =   
    let mul = d.multiplication.op in
    let dom = d in
    let zero = d.addition.neutral in
    let eq = d.eq in
    let a = x.num in
    let b = x.den in
    let c = y.num in
    let d = y.den in
    let e = z.num in
    let f = z.den in 
    let nz_means_ne_z (t: p) 
      : squash (~(is_absorber_of t mul eq) <==> ~(t `eq` zero)) 
      = nonzero_is_not_equal_to_add_neutral_p dom t in
    assert ((c `mul` f) `eq` (d `mul` e));
    assert (fractions_equal x y);
    assert (fractions_equal y z); 
    equivalence_wrt_operation_lemma #p #mul eq (c `mul` f) (d `mul` e) (a `mul` d);
    assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((a `mul` d) `mul` (d `mul` e)));
    equivalence_wrt_operation_lemma #p #mul eq (a `mul` d) (b `mul` c) (d `mul` e);    
    assert (((a `mul` d) `mul` (d `mul` e)) `eq` ((b `mul` c) `mul` (d `mul` e)));
    trans_lemma mul eq ((a `mul` d) `mul` (c `mul` f)) ((a `mul` d) `mul` (d `mul` e)) ((b `mul` c) `mul` (d `mul` e));    
    assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((b `mul` c) `mul` (d `mul` e)));
    //adcf == bcde
    assert_spinoff (is_associative mul eq);
    assoc_lemma eq mul a d c f;
    //(a(dc))f = ((bc)(de))
    assert ( ((a `mul` (d `mul` c)) `mul` f) `eq` ((b `mul` c) `mul` (d `mul` e)));
    comm_lemma eq mul d c;
    // dc=cd
    assert ((d `mul` c) `eq` (c `mul` d));
    equivalence_wrt_operation_lemma #p #mul eq (d `mul` c) (c `mul` d) a;
    // a(dc) = a(cd)
    assert ((a `mul` (d `mul` c)) `eq` (a `mul` (c `mul` d)));
    equivalence_wrt_operation_lemma #p #mul eq (a `mul` (d `mul` c)) (a `mul` (c `mul` d)) f;
    // (a(dc))f = (a(cd))f
    assert ( ((a `mul` (d `mul` c)) `mul` f) `eq` ((a `mul` (c `mul` d)) `mul` f));   
    comm_lemma eq mul a (c `mul` d);
    assert ( (a `mul` (c `mul` d)) `eq` ((c `mul` d) `mul` a));
    equivalence_wrt_operation_lemma #p #mul eq (a `mul` (c `mul` d)) ((c `mul` d) `mul` a) f;
    
    assert ( ((a `mul` (c `mul` d)) `mul` f) `eq` (((c `mul` d) `mul` a) `mul` f) );    
    assert ( ((a `mul` (d `mul` c)) `mul` f) `eq` ((a `mul` (c `mul` d)) `mul` f));      
    trans_lemma mul eq ((a `mul` (d `mul` c)) `mul` f) ((a `mul` (c `mul` d)) `mul` f) (((c `mul` d) `mul` a) `mul` f);
    
    assert ( ((a `mul` (d `mul` c)) `mul` f) `eq` (((c `mul` d) `mul` a) `mul` f) ); 
    symm_lemma eq (((c `mul` d) `mul` a) `mul` f) ((a `mul` (d `mul` c)) `mul` f); 
    assert ( (((c `mul` d) `mul` a) `mul` f) `eq` ((a `mul` (d `mul` c)) `mul` f) );    
    assert ( ((a `mul` (d `mul` c)) `mul` f) `eq` ((b `mul` c) `mul` (d `mul` e)));
    trans_lemma mul eq (((c `mul` d) `mul` a) `mul` f) ((a `mul` (d `mul` c)) `mul` f) ((b `mul` c) `mul` (d `mul` e));

    assert ( (((c `mul` d) `mul` a) `mul` f) `eq`  ((b `mul` c) `mul` (d `mul` e)));  //cd a f = bc de    
 
    assoc_lemma3 eq mul (c `mul` d) a f; 
    assert ((((c `mul` d) `mul` a) `mul` f) `eq` ( (c `mul` d) `mul` (a `mul` f)));
 
    symm_lemma eq ((b `mul` c) `mul` (d `mul` e)) (((c `mul` d) `mul` a) `mul` f);  
    trans_lemma mul eq  ((b `mul` c) `mul` (d `mul` e))  (((c `mul` d) `mul` a) `mul` f) ((c `mul` d) `mul` (a `mul` f)) ;
    
   
    assert (  ((b `mul` c) `mul` (d `mul` e)) `eq` ((c `mul` d) `mul` (a `mul` f))  ); //bc de = cd af
   
    assoc_lemma eq mul b c d e;
    assert ( ((b `mul` c) `mul` (d `mul` e)) `eq` ( ( ( b `mul` c) `mul` d) `mul` e));    
    assert ( ( ( ( b `mul` c) `mul` d) `mul` e)  `eq` ( (b `mul` (c `mul` d)) `mul` e ));  
    trans_lemma mul eq ((b `mul` c) `mul` (d `mul` e))  (((b `mul` c) `mul` d) `mul` e) ((b `mul` (c `mul` d)) `mul` e);
    assert ( ((b `mul` c) `mul` (d `mul` e))  `eq` ((b `mul` (c `mul` d)) `mul` e) );    
    assert (  (b `mul` (c `mul` d)) `eq` ( (c `mul` d) `mul` b) );
    equivalence_wrt_operation_lemma #p #mul eq (b `mul` (c `mul` d)) ( (c `mul` d) `mul` b) e;  
    assert ( ( (b `mul` (c `mul` d)) `mul` e ) `eq`  (  ( (c `mul` d) `mul` b)  `mul` e ));
    trans_lemma mul eq ((b `mul` c) `mul` (d `mul` e)) ((b `mul` (c `mul` d)) `mul` e)  (  ( (c `mul` d) `mul` b)  `mul` e );    
    assert ( ((b `mul` c) `mul` (d `mul` e))  `eq` (((c `mul` d) `mul` b) `mul` e) );   
    assoc_lemma3 eq mul (c `mul` d) b e;
    assert ( (  ( (c `mul` d) `mul` b)  `mul` e ) `eq`  ((c `mul` d) `mul` (b `mul` e))   );
    trans_lemma mul eq  ((b `mul` c) `mul` (d `mul` e)) (((c `mul` d) `mul` b) `mul` e)  ((c `mul` d) `mul` (b `mul` e));  
    assert ( ((b `mul` c) `mul` (d `mul` e)) `eq` ((c `mul` d) `mul` (b `mul` e)) ) ;
    symm_lemma eq  ((c `mul` d) `mul` (b `mul` e))  ((b `mul` c) `mul` (d `mul` e)) ;
    assert (  ((c `mul` d) `mul` (b `mul` e)) `eq` ((b `mul` c) `mul` (d `mul` e)) );
    assert (  ((b `mul` c) `mul` (d `mul` e)) `eq` ((c `mul` d) `mul` (a `mul` f))  );
    trans_lemma mul eq  ((c `mul` d) `mul` (b `mul` e)) ((b `mul` c) `mul` (d `mul` e)) ((c `mul` d) `mul` (a `mul` f));  

    assert (  ((c `mul` d) `mul` (b `mul` e))  `eq`  ((c `mul` d) `mul` (a `mul` f)) );

    auxiliary_eq_lemma dom a b c d e f;
    assert_spinoff ( (a `mul` f) `eq` (b `mul` e));     
    assert_spinoff (fractions_equal x z);    
    ()

#pop-options
#pop-options

let aux_eq_parametrized (#a:Type) (d: euclidean_domain #a) (x y z: fraction d) 
  : Lemma (fractions_equal x y /\ fractions_equal y z ==> fractions_equal x z) = 
  if (fractions_equal x y && fractions_equal y z) 
  then transitivity_lemma d x y z
  else ()

let equality_is_transitive (#a:Type) (d: euclidean_domain #a) : Lemma (is_transitive (fractions_equal #a #d)) 
  = Classical.forall_intro_3 (aux_eq_parametrized d)
  

let equiv (#a:Type) (d: euclidean_domain #a) : equivalence_relation (fraction d) = 
  equality_is_transitive d;
  fractions_equal

let fractions_add (#a: Type) (#d: euclidean_domain #a) (x: fraction d) (y: fraction d) = 
   let mul = d.multiplication.op in
   let add = d.addition.op in 
   product_of_denominators_is_denominator #a #d x y;
   let frac : fraction d = Fraction ((x.num `mul` y.den) `add` (x.den `mul` y.num)) (x.den `mul` y.den) in
   frac
