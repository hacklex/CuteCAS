module Fractions.Equivalence

open AlgebraTypes

open Fractions.Definition

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1"
 
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
     
/// The first big lemma is the proof of fraction equality transitivity.
/// Basically, we're proving that ad=bc && cf=de ==> af=be.
/// I left the assertions intact because the proof is otherwise even harder to understand. 
#push-options "--ifuel 0 --fuel 0 --z3rlimit 2"
private let fraction_equality_transitivity_lemma (#p: Type) (dom: integral_domain #p) 
  (x: fraction dom) 
  (y: (t:fraction dom{fractions_are_equal x t}))
  (z: (t:fraction dom{fractions_are_equal y t})) : Lemma (fractions_are_equal x z) =  
  
    //reveal_opaque (`%is_commutative) (is_commutative #p); //this one wastes rlimit beyond given bounds 
    reveal_opaque (`%is_associative) (is_associative #p);
    reveal_opaque (`%is_transitive) (is_transitive #p);
    reveal_opaque (`%is_symmetric) (is_symmetric #p);
    reveal_opaque (`%is_reflexive) (is_reflexive #p);
    reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #p); 
    let mul = dom.multiplication.op in  
    let eq : equivalence_wrt mul = dom.eq in // so we provide our types explicitly to invoke the required lemmas 
    let (a,b,c,d,e,f) = (x.num, x.den, y.num, y.den, z.num, z.den) in // one composite let is faster than six :) 
  //  assert (is_absorber_of dom.addition.neutral mul eq);
  //  assert ((a `mul` d) `eq` (b `mul` c));
    equivalence_wrt_operation_lemma eq (c `mul` f) (d `mul` e) (a `mul` d);
  //  assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((a `mul` d) `mul` (d `mul` e)));
    equivalence_wrt_operation_lemma eq (mul a d) (mul b c) (mul d e);
  //  trans_lemma eq ((a `mul` d) `mul` (c `mul` f)) ((a `mul` d) `mul` (d `mul` e)) ((b `mul` c) `mul` (d `mul` e));
  //  assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((b `mul` c) `mul` (d `mul` e)));  
    assoc_lemma4 eq mul b c d e;     
  //  assert ((((b `mul` c) `mul` d) `mul` e ) `eq` ((b `mul` c) `mul` (d `mul` e))); 
  //  assert ((((b `mul` c) `mul` d) `mul` e ) `eq` ((b `mul` (c `mul` d)) `mul` e)); 

    comm_lemma eq mul b (mul c d);
    equivalence_wrt_operation_lemma eq (b `mul` (c `mul` d)) ((c `mul` d) `mul` b) e;
  //  assert (((b `mul` (c `mul` d)) `mul` e ) `eq` (((c `mul` d) `mul` b) `mul` e));    
  //  trans_lemma eq (((b `mul` c) `mul` d) `mul` e ) ((b `mul` (c `mul` d)) `mul` e) (((c `mul` d) `mul` b) `mul` e);
  //  trans_lemma eq ((b `mul` c) `mul` (d `mul` e)) (((b `mul` c) `mul` d) `mul` e) (((c `mul` d) `mul` b) `mul` e); 
    assoc_lemma4 eq mul c d b e;   
  //  trans_lemma eq ((b `mul` c) `mul` (d `mul` e)) (((c `mul` d) `mul` b) `mul` e) ((c `mul` d) `mul` (b `mul` e)); 
  //  trans_lemma eq ((a `mul` d) `mul` (c `mul` f)) ((b `mul` c) `mul` (d `mul` e)) ((c `mul` d) `mul` (b `mul` e)); 
  //  assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((c `mul` d) `mul` (b `mul` e)));   
  let ad_cf_equals_cd_af (#p: Type) 
    (eq: equivalence_relation p) 
    (mul: binary_op p { is_associative mul eq /\ is_commutative mul eq /\ equivalence_wrt_condition mul eq })
    (a d c f: p) 
    : Lemma (((a `mul` d) `mul` (c `mul` f)) `eq` ((c `mul` d) `mul` (a `mul` f))) =
    reveal_opaque (`%is_transitive) (is_transitive #p);
    reveal_opaque (`%is_commutative) (is_commutative #p);
    reveal_opaque (`%is_symmetric) (is_symmetric #p);
    let eq : equivalence_wrt mul = eq in
    assoc_lemma4 eq mul a d c f;
    //comm_lemma eq mul d c; // dc = cd 
    equivalence_wrt_operation_lemma eq (d `mul` c) (c `mul` d) a; // a dc = a cd
    //symm_lemma eq (a `mul` (c `mul` d)) (a `mul` (d `mul` c)); 
    equivalence_wrt_operation_lemma eq (a `mul` (d `mul` c)) (a `mul` (c `mul` d)) f; //(a dc)f = ((cd)a)f
    //comm_lemma eq mul a (mul c d);
    equivalence_wrt_operation_lemma eq  (a `mul` (c `mul` d)) ((c `mul` d) `mul` a) f;   
    assoc_lemma4 eq mul c d a f in

    ad_cf_equals_cd_af eq mul a d c f;
    
  let af_equals_be (#p:Type) (dom: integral_domain #p) (a c e: p) (b d f: valid_denominator_of dom)
    : Lemma (requires (((c `dom.multiplication.op` d) `dom.multiplication.op` (b `dom.multiplication.op` e)) `dom.eq` ((c `dom.multiplication.op` d) `dom.multiplication.op` (a `dom.multiplication.op` f))) /\
                      ((dom.multiplication.op a d) `dom.eq` (dom.multiplication.op b c)) /\
                      ((dom.multiplication.op c f) `dom.eq` (dom.multiplication.op d e)) 
            )
            (ensures dom.multiplication.op a f `dom.eq` dom.multiplication.op b e) =    
    reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #p); 
    domain_law_from_pq_eq_pr dom (c `dom.multiplication.op` d) (b `dom.multiplication.op` e) (a `dom.multiplication.op` f);             
    if (c `dom.multiplication.op` d `dom.eq` dom.addition.neutral) then (
      absorber_equal_is_absorber dom.multiplication.op dom.eq dom.addition.neutral (dom.multiplication.op c d);
      domain_deduce_zero_factor_from_zero_product_and_nonzero_factor dom c d;
      absorber_lemma dom.multiplication.op dom.eq c b; //bc=0
      absorber_equal_is_absorber dom.multiplication.op dom.eq (dom.multiplication.op b c) (dom.multiplication.op a d); //ad=bc=0
      domain_deduce_zero_factor_from_zero_product_and_nonzero_factor dom a d; //ad=0 ==> a=0
      absorber_lemma dom.multiplication.op dom.eq c f; //c=0 ==> cf=0
      absorber_lemma dom.multiplication.op dom.eq a f; //a=0 ==> af=0
      symm_lemma dom.eq (dom.multiplication.op d e) (dom.multiplication.op c f); //de=cf
      absorber_equal_is_absorber dom.multiplication.op dom.eq (dom.multiplication.op c f) (dom.multiplication.op d e); //0=de=cf
      domain_deduce_zero_factor_from_zero_product_and_nonzero_factor dom d e; //de=0 => e=0
      absorber_lemma dom.multiplication.op dom.eq e b; //e=0 ==> eb=0
      absorber_is_unique dom.multiplication.op dom.eq (dom.multiplication.op a f) (dom.multiplication.op b e) //eb=0 & af=0 ==> af=be
    ) else symm_lemma dom.eq (dom.multiplication.op a f) (dom.multiplication.op b e) in
    //assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((c `mul` d) `mul` (b `mul` e))); 
    //symm_lemma eq ((c `mul` d) `mul` (b `mul` e)) ((a `mul` d) `mul` (c `mul` f));
    //assert (((c `mul` d) `mul` (b `mul` e)) `eq` ((a `mul` d) `mul` (c `mul` f)));         
    //assert (((a `mul` d) `mul` (c `mul` f)) `eq` ((c `mul` d) `mul` (a `mul` f)));
    //trans_lemma eq ((c `mul` d) `mul` (b `mul` e)) ((a `mul` d) `mul` (c `mul` f)) ((c `mul` d) `mul` (a `mul` f)); 
    //assert (((c `mul` d) `mul` (b `mul` e)) `eq` ((c `mul` d) `mul` (a `mul` f)));
    af_equals_be dom a c e b d f;   
 ()
#pop-options

/// This one is used to construct the equivalence_relation out of fractions_equal
/// Otherwise we can't construct the ring, never mind the field.
private let equality_is_transitive (#p:Type) (d: integral_domain #p) : Lemma (is_transitive (fractions_are_equal #p #d)) = 
  let fraction_equality_transitivity_implication_lemma (#a:Type) (d: integral_domain #a) (x y z: fraction d) 
    : Lemma (fractions_are_equal x y /\ fractions_are_equal y z ==> fractions_are_equal x z) = 
      if (fractions_are_equal x y && fractions_are_equal y z) 
      then fraction_equality_transitivity_lemma d x y z in
  reveal_opaque (`%is_transitive) (is_transitive #(fraction d));
  Classical.forall_intro_3 (fraction_equality_transitivity_implication_lemma d)
  
/// Once all the necessary lemmas are proven, we've got the equivalence_relation for fractions
let fraction_eq (#a:Type) (#d: integral_domain #a) : equivalence_relation (fraction d) = 
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
let fraction_equality_early_escape (#a:Type) (#d: integral_domain #a) (x y: fraction d) 
  : Lemma 
    (requires ((y.num `d.eq` x.num) \/ (x.num `d.eq` y.num)) /\ 
              ((y.den `d.eq` x.den) \/ (x.den `d.eq` y.den)))
    (ensures fraction_eq x y) = 
  reveal_opaque (`%is_commutative) (is_commutative #a); 
  reveal_opaque (`%is_transitive) (is_transitive #a);
  let eq : equivalence_wrt d.multiplication.op = d.eq in // mul_of d is needed for lemmas below
  equivalence_wrt_operation_lemma eq y.den x.den y.num; // we need exactly equivalence wrt. mul,
  equivalence_wrt_operation_lemma eq x.num y.num y.den  // in order to prove this lemma

let fraction_equality_from_known_factor (#a:Type) (#d: integral_domain #a) (x y: fraction d) (f: non_absorber_of d.multiplication.op d.eq)
 : Lemma (requires (   ((y.num `d.eq` (x.num `d.multiplication.op` f)) || (y.num `d.eq` (f `d.multiplication.op` x.num)))
                     /\ ((y.den `d.eq` (x.den `d.multiplication.op` f)) || (y.den `d.eq` (f `d.multiplication.op` x.den)))))
         (ensures fraction_eq x y) = 
  reveal_opaque (`%is_commutative) (is_commutative #a); 
  reveal_opaque (`%is_transitive) (is_transitive #a)
#pop-options
