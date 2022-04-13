module Fractions.Equivalence

open AlgebraTypes

open Fractions.Definition

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1"
 
/// We define the comparison function in a way that takes the least effort to prove the properties for.
/// If we were to define as (x - y) `eq` zero, we'd need to also manually prove is_reflexive and is_symmetric.
/// Do not want.
unfold private let fractions_are_equal 
  (#a: Type) (#d: integral_domain a) 
  (x: fraction d) (y: fraction d) = 
   ((x.num `mul_of d` y.den) `d.eq` (x.den `mul_of d` y.num)) 

private let equality_is_symmetric_lemma_oneway (#a:Type) (d: integral_domain a) (x y: fraction d)
  : Lemma (fractions_are_equal x y ==> fractions_are_equal y x) = 
  if (fractions_are_equal x y) then 
    let mul = d.multiplication.op in
    reveal_opaque (`%is_commutative) (is_commutative mul);   
    trans_lemma_4 d.eq (mul y.num x.den)
                       (mul x.den y.num) //commutative
                       (mul x.num y.den) //commutative
                       (mul y.den x.num) //what we needed
  
  
private let equality_is_symmetric_lemma (#a:Type) (d: integral_domain a) (x y: fraction d)
  : Lemma (fractions_are_equal x y == fractions_are_equal y x) =  
  equality_is_symmetric_lemma_oneway d x y;  
  equality_is_symmetric_lemma_oneway d y x 

private let equality_is_symmetric (#a:Type) (d: integral_domain a) 
  : Lemma (is_symmetric (fractions_are_equal #a #d)) = 
  Classical.forall_intro_2 (equality_is_symmetric_lemma d);
  reveal_opaque (`%is_symmetric) (is_symmetric #(fraction d))

/// This even pleases the eye. Especially when the lengths match.
private let equality_is_reflexive (#a:Type) (d: integral_domain a) 
  : Lemma (is_reflexive (fractions_are_equal #a #d)) =   
    reveal_opaque (`%is_commutative) (is_commutative d.multiplication.op);
    reveal_opaque (`%is_reflexive) (is_reflexive #(fraction d))


/// The first big lemma is the proof of fraction equality transitivity.
/// Basically, we're proving that ad=bc && cf=de ==> af=be.
#push-options "--ifuel 0 --fuel 0 --z3rlimit 5"
private let fraction_equality_transitivity_lemma (#p: Type) (dom: integral_domain p) 
                                                 (x y z: fraction dom) 
  : Lemma (requires fractions_are_equal x y /\ fractions_are_equal y z)
          (ensures fractions_are_equal x z) =    
    //reveal_opaque (`%is_commutative) (is_commutative #p); //this one wastes rlimit beyond given bounds 
  let eq = dom.eq in // so we provide our types explicitly to invoke the required lemmas 
  let mul = dom.multiplication.op in  
  let zero = dom.addition.neutral in
  reveal_opaque (`%is_associative) (is_associative mul); 
  reveal_opaque (`%is_associative) (is_associative dom.addition.op);
  reveal_opaque (`%is_transitive) (is_transitive eq);
  reveal_opaque (`%is_symmetric) (is_symmetric eq);
  reveal_opaque (`%is_reflexive) (is_reflexive eq);
  reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors mul); 
  let (a,b,c,d,e,f) = (x.num, x.den, y.num, y.den, z.num, z.den) in // one composite let is faster than six :) 
  congruence_lemma_3 mul (c `mul` f) (d `mul` e) (a `mul` d);
  congruence_lemma_3 mul (mul a d) (mul b c) (mul d e); 
  assoc_lemma_4 mul b c d e;
  comm_lemma mul b (mul c d);
  congruence_lemma_3 mul (b `mul` (c `mul` d)) ((c `mul` d) `mul` b) e;
  assoc_lemma_4 mul c d b e;     
  let ad_cf_equals_cd_af #p (#eq: equivalence_relation p) 
                               (mul: op_with_congruence eq{is_associative mul /\ is_commutative mul})
                               (a d c f: p) 
    : Lemma (((a `mul` d) `mul` (c `mul` f)) `eq` ((c `mul` d) `mul` (a `mul` f))) =
    reveal_opaque (`%is_transitive) (is_transitive #p);  
    reveal_opaque (`%is_commutative) (is_commutative mul);
    assoc_lemma_4 mul a d c f; 
    congruence_lemma_3 mul (d `mul` c) (c `mul` d) a; 
    congruence_lemma_3 mul (a `mul` (d `mul` c)) (a `mul` (c `mul` d)) f; //(a dc)f = ((cd)a)f
    congruence_lemma_3 mul  (a `mul` (c `mul` d)) ((c `mul` d) `mul` a) f;   
    assoc_lemma_4 mul c d a f in ad_cf_equals_cd_af mul a d c f; 
  let af_equals_be (a c e: p) (b d f: valid_denominator_of dom)
    : Lemma (requires ((mul c d `mul` mul b e) `eq` (mul c d `mul` mul a f)) /\
                      ((mul a d) `eq` (mul b c)) /\
                      ((mul c f) `eq` (mul d e)))
            (ensures mul a f `eq` mul b e) =     
    domain_law_from_pq_eq_pr dom (c `mul` d) (b `mul` e) (a `mul` f);             
    if (c `mul` d `eq` zero) then begin
      absorber_equal_is_absorber mul zero (mul c d);
      domain_deduce_zero_factor_from_zero_product_and_nonzero_factor dom c d;
      absorber_lemma mul c b; //bc=0
      absorber_equal_is_absorber mul (mul b c) (mul a d); //ad=bc=0
      domain_deduce_zero_factor_from_zero_product_and_nonzero_factor dom a d; //ad=0 ==> a=0
      absorber_lemma dom.multiplication.op c f; //c=0 ==> cf=0
      absorber_lemma dom.multiplication.op a f; //a=0 ==> af=0
      symm_lemma dom.eq (mul d e) (mul c f); //de=cf
      absorber_equal_is_absorber mul (mul c f) (mul d e); //0=de=cf
      domain_deduce_zero_factor_from_zero_product_and_nonzero_factor dom d e; //de=0 => e=0
      absorber_lemma mul e b; //e=0 ==> eb=0
      absorber_is_unique mul (mul a f) (mul b e) //eb=0 & af=0 ==> af=be
    end else symm_lemma dom.eq (mul a f) (mul b e) in af_equals_be a c e b d f 
#pop-options

private let fraction_equality_transitivity_implication_lemma 
  (#p:Type) (d: integral_domain p) (x y z: fraction d) 
  : Lemma (fractions_are_equal x y /\ fractions_are_equal y z ==> fractions_are_equal x z) = 
    if (fractions_are_equal x y && fractions_are_equal y z) 
    then fraction_equality_transitivity_lemma d x y z

/// This one is used to construct the equivalence_relation out of fractions_equal
/// Otherwise we can't construct the ring, never mind the field.
private let equality_is_transitive (#p:Type) (d: integral_domain p) 
  : Lemma (is_transitive (fractions_are_equal #p #d)) = 
  reveal_opaque (`%is_transitive) (is_transitive #(fraction d));
  Classical.forall_intro_3 (fraction_equality_transitivity_implication_lemma d)

/// Once all the necessary lemmas are proven, we've got the equivalence_relation for fractions
let fraction_eq (#a:Type) (#d: integral_domain a) : equivalence_relation (fraction d) = 
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
/// UPD 2022-03-13: it no longer wants ifuel 1. 
let fraction_equality_early_escape (#a:Type) (#d: integral_domain a) (x y: fraction d) 
  : Lemma 
    (requires ((y.num `d.eq` x.num) \/ (x.num `d.eq` y.num)) /\ 
              ((y.den `d.eq` x.den) \/ (x.den `d.eq` y.den)))
    (ensures fraction_eq x y) = 
  reveal_opaque (`%is_transitive) (is_transitive #a);
  congruence_lemma_3 (mul_of d) y.den x.den y.num; // we need exactly equivalence wrt. mul,
  congruence_lemma_3 (mul_of d) x.num y.num y.den  // in order to prove this lemma

let fraction_equality_from_known_factor (#a:Type) (#d: integral_domain a) (x y: fraction d) (f: non_absorber_of d.multiplication.op)
 : Lemma (requires (   ((y.num `d.eq` (x.num `d.multiplication.op` f)) || (y.num `d.eq` (f `d.multiplication.op` x.num)))
                     /\ ((y.den `d.eq` (x.den `d.multiplication.op` f)) || (y.den `d.eq` (f `d.multiplication.op` x.den)))))
         (ensures fraction_eq x y) = 
  reveal_opaque (`%is_commutative) (is_commutative d.multiplication.op); 
  reveal_opaque (`%is_transitive) (is_transitive #a)
#pop-options
