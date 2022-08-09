module Fractions.Addition

open AlgebraTypes
open Fractions.Definition
open Fractions.Equivalence

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1 --split_queries"

/// We declare the type of fractions_add heavily refined so that our
/// future lemmas will not have it too rough proving stuff
private let fraction_add_op (#a: Type) (#d: integral_domain a) (x y: fraction d)
  : (t: fraction d
     {
       t.num `d.eq` ((x.num `d.multiplication.op` y.den) `d.addition.op` (x.den `d.multiplication.op` y.num)) /\
       t.den `d.eq` (x.den `d.multiplication.op` y.den) 
     }) = 
   reveal_opaque (`%is_reflexive) (is_reflexive #a);
   product_of_denominators_is_denominator x y;
   Fraction ((x.num `d.multiplication.op` y.den) `d.addition.op` (x.den `d.multiplication.op` y.num))
            (x.den `d.multiplication.op` y.den) 

private let fraction_add_is_commutative (#a:Type) (#d: integral_domain a) (x y: fraction d) 
  : Lemma (fraction_eq (fraction_add_op x y) (fraction_add_op y x)) =
  reveal_opaque (`%is_commutative) (is_commutative d.multiplication.op); 
  reveal_opaque (`%is_transitive) (is_transitive #a)
(* for some reason, this verbose proof is now redundant.
  let eq = d.eq in   
  let add = add_of d in
  let mul = mul_of d in    
  let x_plus_y = fraction_add x y in
  let y_plus_x = fraction_add y x in
  fraction_equality_early_escape x_plus_y y_plus_x;
*)

let fraction_addition_is_commutative (#a:Type) (#d: integral_domain a) 
  : Lemma (forall (x y: fraction d). fraction_add_op x y `fraction_eq` fraction_add_op y x)=   
   reveal_opaque (`%is_commutative) (is_commutative #(fraction d) #(fraction_eq #a #d)); 
   Classical.forall_intro_2 (fraction_add_is_commutative #a #d)
 
private let fraction_add_is_associative (#a:Type) (#d: integral_domain a) (x y z: fraction d) 
  : Lemma ((fraction_add_op (fraction_add_op x y) z) `fraction_eq` (fraction_add_op x (fraction_add_op y z))) = 
   //we calculate the sum of three fractions in 2 different orders,
   //and prove the results (sum_1 and sum_2) to be equal wrt. domain equality relation
   let eq = d.eq in 
   let add = d.addition.op in
   let mul = d.multiplication.op in 
   let sum_1 = fraction_add_op  (fraction_add_op x y) z in 
   d.right_distributivity (x.num `mul` y.den) (x.den `mul` y.num) z.den; // (ad+bc)f   
   congruence_lemma_3 add (((x.num `mul` y.den) `add` (x.den `mul` y.num)) `mul` z.den) 
                                              (((x.num `mul` y.den) `mul` z.den) `add` ((x.den `mul` y.num) `mul` z.den)) 
                                              ((x.den `mul` y.den) `mul` z.num); //substitute (ad+bc)f + (bd)e ==> (ad)f+(bc)f+(bd)e
   //just to keep track of what sum_1.num is currently known to be equal to
   //assert (sum_1.num `eq` ((((x.num `mul` y.den) `mul` z.den) `add` ((x.den `mul` y.num) `mul` z.den)) `add` ((x.den `mul` y.den) `mul` z.num)) );
     
   let sum_2 = fraction_add_op x (fraction_add_op y z) in  
    
   d.left_distributivity x.den (y.num `mul` z.den) (y.den `mul` z.num); // b(cf+de) = b(cf)+b(de)
   congruence_lemma_3 add (x.den `mul` ((y.num `mul` z.den) `add` (y.den `mul` z.num))) // b*(cf+de)
                                              ((x.den `mul` (y.num `mul` z.den)) `add` (x.den `mul` (y.den `mul` z.num))) 
                                              (x.num `mul` (y.den `mul` z.den));   
   //assert (sum_2.num `eq` ((x.num `mul` (y.den `mul` z.den)) `add` ((x.den `mul` (y.num `mul` z.den)) `add`(x.den `mul` (y.den `mul` z.num))) ) );
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
   //assoc_lemma3 eq mul x.num y.den z.den; //shuffle the parentheses in all three.
   //assoc_lemma3 eq mul x.den y.num z.den; //grouped the calls for better readability.
   //assoc_lemma3 eq mul x.den y.den z.num; 
   // now we operate on the scale of summands of the numerator, since the above lemmas established the parts equalities already
   //assert (sum_1.num `eq` (part_1_r `add` part_2_r `add` part_3_r));
   //assert (part_1 `eq` part_1_r /\ part_2 `eq` part_2_r /\ part_3 `eq` part_3_r);
   //assert (sum_2.num `eq` (part_1 `add` (part_2 `add` part_3)));
   congruence_lemma_3 add  part_1 part_1_r (part_2 `add` part_3);
   //assert ((part_1 `add` (part_2 `add` part_3)) `eq` (part_1_r `add` (part_2 `add` part_3)));
   trans_lemma eq sum_2.num (part_1 `add` (part_2 `add` part_3)) (part_1_r `add` (part_2 `add` part_3));
   //assert (sum_2.num `eq` (part_1_r `add` (part_2 `add` part_3)));
   congruence_lemma_3 add part_2 part_2_r part_3;
   //assert ((part_2 `add` part_3) `eq` (part_2_r `add` part_3)); 
   congruence_lemma_3 add part_3 part_3_r part_2_r;
   //assert ((part_2_r `add` part_3) `eq` (part_2_r `add` part_3_r)); 
   trans_lemma eq (part_2 `add` part_3) (part_2_r `add` part_3) (part_2_r `add` part_3_r);
   congruence_lemma_3 add (part_2 `add` part_3) (part_2_r `add` part_3_r) part_1_r;
   trans_lemma eq sum_2.num (part_1_r `add` (part_2 `add` part_3)) (part_1_r `add` (part_2_r `add` part_3_r));
   //assert (sum_2.num `eq` (part_1_r `add` (part_2_r `add` part_3_r)));
   assoc_lemma_3 add part_1_r part_2_r part_3_r;  
   //assert ((part_1_r `add` (part_2_r `add` part_3_r)) `eq` ((part_1_r `add` part_2_r) `add` part_3_r));
   trans_lemma eq sum_2.num (part_1_r `add` (part_2_r `add` part_3_r)) ((part_1_r `add` part_2_r) `add` part_3_r);
   //assert (sum_2.num `eq` (part_1_r `add` part_2_r `add` part_3_r));
   trans_lemma eq sum_1.num (part_1_r `add` part_2_r `add` part_3_r) sum_2.num;
   //assert (sum_1.num `eq` sum_2.num);
   //assert (sum_1.den `eq` sum_2.den);
   fraction_equality_early_escape sum_1 sum_2
   //assert (fraction_eq sum_1 sum_2) // production variant will only contain the lemma invocations of course :)
  
private let fraction_addition_is_associative (#a:Type) (d: integral_domain a) 
  : Lemma (forall (x y z: fraction d). (fraction_add_op x (fraction_add_op y z) `fraction_eq` fraction_add_op (fraction_add_op x y) z)) = 
  Classical.forall_intro_2 (symm_lemma (fraction_eq #a #d));
  Classical.forall_intro_3 (fraction_add_is_associative #a #d)
  
private let fraction_additive_neutral_lemma (#a:Type) (#d: integral_domain a) 
                                            (x: fraction d{is_neutral_of x.num d.addition.op}) (y: fraction d) 
  : Lemma ((x `fraction_add_op` y) `fraction_eq` y /\ ((y `fraction_add_op` x) `fraction_eq` y)) = 
  let mul = d.multiplication.op in
  let add = d.addition.op in  
  let eq = d.eq in
  let sum = fraction_add_op x y in   
  neutral_is_unique add x.num d.addition.neutral;  
  absorber_equal_is_absorber mul d.addition.neutral x.num;
  absorber_equal_is_absorber mul x.num (x.num `mul` y.den); 
  absorber_is_unique mul d.addition.neutral (x.num `mul` y.den);
  neutral_equivalent_is_neutral add d.addition.neutral (x.num `mul` y.den);
  congruence_lemma_3 mul ((x.num `mul` y.den) `add` (x.den `mul` y.num)) (x.den `mul` y.num) y.den;
  trans_lemma_4 eq (((x.num `mul` y.den) `add` (x.den `mul` y.num)) `mul` y.den)  
                   ((x.den `mul` y.num) `mul` y.den) 
                   (x.den `mul` (y.num `mul` y.den)) 
                   (x.den `mul` (y.den `mul` y.num)); 
  trans_lemma eq (((x.num `mul` y.den) `add` (x.den `mul` y.num)) `mul` y.den) 
                 (x.den `mul` (y.den `mul` y.num))
                 ((x.den `mul` y.den) `mul` y.num);
  fraction_add_is_commutative y x;
  trans_lemma fraction_eq (y `fraction_add_op` x) (x `fraction_add_op` y) y 

/// Proof that fraction addition respects fraction equality is lengthy, so I only commented out the intermediate asserts,
/// but dare not remove them, as they help understanding the purpose of the proof steps 
private let fraction_equivalence_respects_add (#a:Type) (d: integral_domain a) 
                                              (e1: fraction d) (e2: fraction d{e1 `fraction_eq` e2 }) 
                                              (x: fraction d) 
  : Lemma ((x `fraction_add_op` e1) `fraction_eq` (x `fraction_add_op` e2) /\ 
           (e1 `fraction_add_op` x ) `fraction_eq` (e2 `fraction_add_op` x)) = 
  let mul = d.multiplication.op in
  let eq = d.eq in
  let add = d.addition.op in    
  d.right_distributivity (x.num `mul` e1.den) (x.den `mul` e1.num) (x.den `mul` e2.den);
  assert ( (((x.num `mul` e1.den) `add` (x.den `mul` e1.num)) `mul` (x.den `mul` e2.den)) `d.eq`  
           (((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) `add` ((x.den `mul` e1.num) `mul` (x.den `mul` e2.den))));
  //we will carefully transform ad into bc, as (a/b=c/d) is defined as (ad=bc)
  let left_side = (fraction_add_op x e1).num `mul` (fraction_add_op x e2).den in
  //let right_side = (fraction_add x e1).den `mul` (fraction_add x e2).num in
  assert (left_side `eq` ( ( (x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) `add` ( (x.den `mul` e1.num) `mul` (x.den `mul` e2.den))));
  assert ((fraction_add_op x e1).den `eq` (x.den `mul` e1.den));
  assert ((fraction_add_op x e2).num `eq` ((x.num `mul` e2.den) `add` (x.den `mul` e2.num)));  
  //assert (right_side `eq` ( (x.den `mul` e1.den) `mul` ((x.num `mul` e2.den) `add` (x.den `mul` e2.num)) ));
  comm_lemma mul x.den e2.den;
  //assert (mul x.den e2.den `d.eq` mul e2.den x.den /\ mul e2.den x.den `d.eq` mul x.den e2.den );
  congruence_lemma_3 mul (x.den `mul` e2.den) (e2.den `mul` x.den) (x.den `mul` e1.num);
  //assert ( ( (x.den `mul` e1.num) `mul` (x.den `mul` e2.den)) `eq` ((x.den `mul` e1.num) `mul` (e2.den `mul` x.den)));
  assoc_lemma_4 mul x.den e1.num e2.den x.den;
  trans_lemma eq ((x.den `mul` e1.num) `mul` (e2.den `mul` x.den)) (((x.den `mul` e1.num) `mul` e2.den) `mul` x.den) ((x.den `mul` (e1.num `mul` e2.den)) `mul` x.den);
  //assert ( ((x.den `mul` e1.num) `mul` (e2.den `mul` x.den)) `eq` ((x.den `mul` (e1.num `mul` e2.den)) `mul` x.den)); 
  //assert ((e1.num `mul` e2.den) `eq` (e1.den `mul` e2.num));
  congruence_lemma_3 mul (e1.num `mul` e2.den) (e1.den `mul` e2.num) x.den;
  congruence_lemma_3 mul (x.den `mul` (e1.num `mul` e2.den)) (x.den `mul` (e1.den `mul` e2.num)) x.den;
  //assert ( ((x.den `mul` (e1.num `mul` e2.den)) `mul` x.den) `eq` ((x.den `mul` (e1.den `mul` e2.num)) `mul` x.den)); // need (x.den e1.den)(x.den e2.num)
  assoc_lemma_4 mul x.den e1.den e2.num x.den;
  assert ( ((x.den `mul` (e1.den `mul` e2.num)) `mul` x.den) `eq` ((x.den `mul` e1.den) `mul` (e2.num `mul` x.den)));
  comm_lemma mul e2.num x.den;
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
  assoc_lemma_4 mul x.num e1.den x.den e2.den;
  comm_lemma mul e1.den x.den;
  //equivalence_wrt_operation_lemma #a #mul eq (e1.den `mul` x.den) (x.den `mul` e1.den) x.num;
  congruence_lemma_3 mul (x.num `mul` (e1.den `mul` x.den)) (x.num `mul` (x.den `mul` e1.den)) e2.den;
  assoc_lemma_4 mul x.num x.den e1.den e2.den;
  trans_lemma   eq ((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) //assoc
                   ((x.num `mul` (e1.den `mul` x.den)) `mul` e2.den) //comm
                   ((x.num `mul` (x.den `mul` e1.den)) `mul` e2.den);
  comm_lemma mul x.num (x.den `mul` e1.den);
  //equivalence_wrt_operation_lemma #a #mul eq (mul x.num (mul x.den e1.den)) (mul (mul x.den e1.den) x.num) e2.den;
  //assert ( eq ((x.num `mul` (x.den `mul` e1.den)) `mul` e2.den) (((x.den `mul` e1.den) `mul` x.num) `mul` e2.den));
  assoc_lemma_4 mul x.den e1.den x.num e2.den;
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
  d.left_distributivity (mul x.den e1.den) (mul x.num e2.den) (mul x.den e2.num);
  trans_lemma eq left_side (((x.den `mul` e1.den) `mul` (x.num `mul` e2.den)) `add` ((x.den `mul` e1.den) `mul` (x.den `mul` e2.num)))
                           ((x.den `mul` e1.den) `mul` ((x.num `mul` e2.den) `add` (x.den `mul` e2.num)));
  assert (fraction_eq (fraction_add_op x e1) (fraction_add_op x e2));
  //assert (left_side `eq` right_side);
  assert (fraction_eq (fraction_add_op x e1) (fraction_add_op x e2));
  //The rest is trivial, just using commutativity again.
  fraction_add_is_commutative x e1;
  reveal_opaque (`%is_symmetric) (is_symmetric #(fraction d));
  fraction_add_is_commutative x e2;
  assert (fraction_eq (fraction_add_op x e1) (fraction_add_op x e2));
  trans_lemma_4 fraction_eq (fraction_add_op e1 x) (fraction_add_op x e1) (fraction_add_op x e2) (fraction_add_op e2 x);
()  

let fraction_equivalence_respects_addition (#a:Type) (#d: integral_domain a) 
  : Lemma(congruence_condition #(fraction d) (fraction_add_op #a #d) (fraction_eq #a #d)) = 
  reveal_opaque (`%congruence_condition) (congruence_condition #(fraction d)); 
  Classical.forall_intro_3 (fraction_equivalence_respects_add d)

let fraction_add (#a:Type) (#d: integral_domain a) : Pure (op_with_congruence (fraction_eq))
  (requires True) (ensures (fun fadd -> is_associative fadd /\ is_commutative fadd)) = 
  fraction_equivalence_respects_addition #a #d;
  fraction_addition_is_commutative #a #d;
  fraction_addition_is_associative d;
  reveal_opaque (`%is_symmetric) (is_symmetric (fraction_eq #a #d)); 
  reveal_opaque (`%is_commutative) (is_commutative #(fraction d) #(fraction_eq #a #d)); 
  reveal_opaque (`%is_associative) (is_associative #(fraction d) #(fraction_eq #a #d)); 
  fraction_add_op #a #d

private let fraction_zero_is_neutral_lemma (#a:Type) (#d: integral_domain a) (x: fraction d{is_neutral_of x.num d.addition.op})  
  : Lemma (is_neutral_of x (fraction_add #a #d)) 
  = is_neutral_from_lemma (fraction_add #a #d) x (fraction_additive_neutral_lemma x)

private let fraction_zero (#a:Type) (d: integral_domain a) 
  : (x:fraction d { is_neutral_of x (fraction_add #a #d) /\ 
                    d.eq x.den d.multiplication.neutral }) = 
  one_is_valid_denominator d;
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  let zero = Fraction d.addition.neutral d.multiplication.neutral in
  fraction_zero_is_neutral_lemma zero;  
  zero

let fraction_additive_neutral_condition (#a:Type) (d: integral_domain a) 
                                        (x: fraction d{is_neutral_of x.num d.addition.op})
  : Lemma (is_neutral_of x (fraction_add #a #d)) = 
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d) #(fraction_eq #a #d));
  reveal_opaque (`%is_left_id_of) (is_left_id_of #(fraction d) #(fraction_eq #a #d));
  reveal_opaque (`%is_right_id_of) (is_right_id_of #(fraction d) #(fraction_eq #a #d));
  Classical.forall_intro (fraction_additive_neutral_lemma x) 

private let fraction_neg_op (#a:Type) (#d: integral_domain a) (x: fraction d) 
  : (t: fraction d{ d.eq t.num (d.addition.inv x.num) /\ d.eq t.den x.den }) = 
    reveal_opaque (`%is_reflexive) (is_reflexive #a);
    Fraction (d.addition.inv x.num) (x.den) 
  
#push-options "--ifuel 1 --z3rlimit 3"
private let fraction_neg_is_inverse_for_add (#a:Type) (#d: integral_domain a) (x: fraction d) : Lemma (
  is_neutral_of (fraction_add x (fraction_neg_op x)) (fraction_add #a #d) /\
  is_neutral_of (fraction_add (fraction_neg_op x) x) (fraction_add #a #d)) = 
  ring_distributivity_lemma d;
  let add = d.addition.op in
  let neg = neg_of d in
  let mul = d.multiplication.op in  
  let eq = d.eq in  
  let fraction_neg = fraction_neg_op in
  assert ((fraction_neg x).num `eq` neg x.num);
  assert ((fraction_neg x).den `eq` x.den); 
  assert ((fraction_add x (fraction_neg x)).den `eq` (fraction_add (fraction_neg x) x).den);
  assert (((fraction_add x (fraction_neg x)).num) `eq` ((x.num `mul` x.den) `add` (x.den `mul`  neg x.num))); 
  comm_lemma mul x.num x.den;
  congruence_lemma_3 add (x.num `mul` x.den) (x.den `mul` x.num) (x.den `mul` neg x.num);
  trans_lemma eq (fraction_add x (fraction_neg x)).num  
                 ((x.num `mul` x.den) `add` (x.den `mul` neg x.num))
                 ((x.den `mul` x.num) `add` (x.den `mul` neg x.num)); 
  left_distributivity_lemma mul add x.den x.num (neg x.num);
  trans_lemma eq (fraction_add x (fraction_neg x)).num 
                 ((x.den `mul` x.num) `add` (x.den `mul` neg x.num)) 
                 (x.den `mul` (x.num `add` neg x.num));
  inverse_operation_lemma neg x.num;
  assert (is_neutral_of (x.num `add` neg x.num) add);
  neutral_is_unique add d.addition.neutral (x.num `add` neg x.num);
  assert (d.addition.neutral `eq` (x.num `add` neg x.num));
  symm_lemma eq (x.num `add` neg x.num) d.addition.neutral;
  absorber_equal_is_absorber mul d.addition.neutral (x.num `add` neg x.num);
  absorber_lemma mul (x.num `add` neg x.num) x.den;
  absorber_equal_is_absorber mul (x.num `add` neg x.num) (x.den `mul` (x.num `add` neg x.num)); 
  assert (is_absorber_of (x.den `mul` (x.num `add` neg x.num)) mul); 
  absorber_is_unique mul (x.den `mul` (x.num `add` neg x.num)) d.addition.neutral;
  neutral_equivalent_is_neutral add d.addition.neutral (x.den `mul` (x.num `add` neg x.num));
  symm_lemma eq (x.den `mul` (x.num `add` neg x.num)) d.addition.neutral;
  trans_lemma eq (fraction_add x (fraction_neg x)).num
                 (x.den `mul` (x.num `add` neg x.num))
                 d.addition.neutral;
  neutral_equivalent_is_neutral add d.addition.neutral (fraction_add x (fraction_neg x)).num;
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d) #(fraction_eq #a #d)); 
  reveal_opaque (`%is_left_id_of) (is_left_id_of #(fraction d) #(fraction_eq #a #d)); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #(fraction d) #(fraction_eq #a #d)); 
  is_neutral_from_lemma (fraction_add #a #d) 
                        (fraction_add x (fraction_neg x)) 
                        (fraction_additive_neutral_lemma (fraction_add x (fraction_neg x)));

  assert (is_neutral_of (fraction_add x (fraction_neg x)) (fraction_add #a #d));
  fraction_add_is_commutative x (fraction_neg x);
  assert (fraction_add x (fraction_neg x) `fraction_eq` fraction_add (fraction_neg x) x);
  symm_lemma fraction_eq (fraction_add (fraction_neg x) x) (fraction_add x (fraction_neg x));
  assert (fraction_eq (fraction_add (fraction_neg x) x) (fraction_add x (fraction_neg x)));
  fraction_equivalence_respects_addition #a #d;
  neutral_equivalent_is_neutral (fraction_add #a #d) (x `fraction_add` fraction_neg x) (fraction_neg x `fraction_add` x); 
  ()
#pop-options
 
private let fraction_neg_respects_equivalence (#a:Type) (#d: integral_domain a) (x y: fraction d) : Lemma (x `fraction_eq` y ==> 
        ((fraction_neg_op x `fraction_eq` fraction_neg_op y) 
      && (fraction_neg_op y `fraction_eq` fraction_neg_op x))) 
  = 
  let neg = d.addition.inv in
  if (fraction_eq x y) then 
    let mul = d.multiplication.op in 
    assert ((fraction_neg_op x).num `d.eq` d.addition.inv x.num);
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
    symm_lemma fraction_eq (fraction_neg_op y) (fraction_neg_op x)
  
  
let fraction_negation_respects_equivalence (#a:Type) (#d: integral_domain a) 
  : Lemma (unary_congruence_condition #(fraction d) fraction_neg_op fraction_eq) 
  = reveal_opaque (`%unary_congruence_condition) 
                  (unary_congruence_condition (fraction_neg_op #a #d) fraction_eq);  
    Classical.forall_intro_2 (fraction_neg_respects_equivalence #a #d)
 
private let fraction_neg #a (#d: integral_domain a) : inverse_op_for (fraction_add #a #d) =
  Classical.forall_intro (fraction_neg_is_inverse_for_add #a #d);  
  reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #(fraction d) #(fraction_eq)); 
  fraction_negation_respects_equivalence #a #d;
  fraction_neg_op #a #d

let fraction_neg_is_inverse_for_addition (#a:Type) (#d: integral_domain a) : Lemma (is_inverse_operation_for (fraction_neg #a #d) (fraction_add #a #d)) =  
  reveal_opaque (`%is_inverse_operation_for) 
                (is_inverse_operation_for #(fraction d) #fraction_eq); 
  Classical.forall_intro (fraction_neg_is_inverse_for_add #a #d)

private let fraction_negation_lemma (#a:Type) (#d: integral_domain a) (x: fraction d) 
  : Lemma (is_neutral_of (x `fraction_add` (fraction_neg x)) (fraction_add #a #d) /\
           is_neutral_of ((fraction_neg x) `fraction_add` x) (fraction_add #a #d)) =  
  let add = d.addition.op in
  let neg = neg_of d in
  let mul = d.multiplication.op in  
  let x' = fraction_neg x in
  let s = x `fraction_add` x' in 
  comm_lemma mul x.den (neg x.num);
  congruence_lemma_3 add (x.den `mul` neg x.num) (neg x.num `mul` x.den) (x.num `mul` x.den); 
  d.right_distributivity x.num (neg x.num) x.den;
  trans_lemma d.eq s.num ((x.num `mul` x.den) `add` (neg x.num `mul` x.den)) ((x.num `add` neg x.num) `mul` x.den);
  inverse_operation_lemma neg x.num; 
  neutral_is_unique add d.addition.neutral (x.num `add` neg x.num);
  symm_lemma d.eq (x.num `add` neg x.num) d.addition.neutral;
  absorber_equal_is_absorber mul d.addition.neutral (x.num `add` neg x.num);
  absorber_lemma mul (x.num `add` neg x.num) x.den;  
  absorber_equal_is_absorber mul (x.num `add` neg x.num) ((x.num `add` neg x.num) `mul` x.den); 
  absorber_is_unique mul ((x.num `add` neg x.num) `mul` x.den) d.addition.neutral;
  trans_lemma d.eq s.num ((x.num `add` neg x.num) `mul` x.den) d.addition.neutral; 
  neutral_equivalent_is_neutral add d.addition.neutral s.num; 
  fraction_zero_is_neutral_lemma s; 
  fraction_add_is_commutative x (fraction_neg x);
  fraction_equivalence_respects_addition #a #d;
  fraction_neg_is_inverse_for_addition #a #d;
  inverse_operation_lemma fraction_neg x;
  fraction_add_is_commutative x (fraction_neg x);
  symm_lemma fraction_eq (x `fraction_add` fraction_neg x) (fraction_neg x `fraction_add` x);
  neutral_equivalent_is_neutral (fraction_add #a #d) (x `fraction_add` fraction_neg x) (fraction_neg x `fraction_add` x)

let fraction_addition_properties (#a:Type) (d: integral_domain a) 
  : Lemma (congruence_condition (fraction_add #a #d) fraction_eq /\ 
           is_associative (fraction_add #a #d) /\
           is_commutative (fraction_add #a #d)) [SMTPat(fraction_eq #a #d)] =
  fraction_addition_is_associative d; 
  fraction_addition_is_commutative #a #d;
  fraction_equivalence_respects_addition #a #d 
    
let any_fraction_is_additive_unit (#a:Type) (#d: integral_domain a) (x: fraction d) 
  : Lemma (is_unit x (fraction_add #a #d)) =
  reveal_opaque (`%is_unit) (is_unit #(fraction d) #(fraction_eq #a #d));   
  fraction_neg_is_inverse_for_add x

let unit_from_any_frac (#a:Type) (#d: integral_domain a) (x: fraction d) 
  : (units_of (fraction_add #a #d)) = any_fraction_is_additive_unit x; x

let fraction_add_all_are_units (#a:Type) (#d: integral_domain a) 
  : Lemma (all_are_units #(fraction d) (fraction_add #a #d)) 
  = Classical.forall_intro (any_fraction_is_additive_unit #a #d)
 
let fraction_neg_eq_property (#a:Type) (#d: integral_domain a) 
  : Lemma (unary_congruence_condition #(fraction d) fraction_neg fraction_eq) 
  [SMTPat(fraction_neg #a #d)] = 
  fraction_negation_respects_equivalence #a #d;
  fraction_add_all_are_units #a #d

let fraction_neg_respects_equivalence_of_units (#a:Type) (#d: integral_domain a) 
                                               (x y: units_of #(fraction d) (fraction_add #a #d)) 
  : Lemma(fraction_eq x y ==> fraction_eq (fraction_neg x) (fraction_neg y)) = 
  fraction_neg_respects_equivalence x y
 
let fraction_neg_units (#a:Type) (#d: integral_domain a) : unary_op_on_units_of (fraction_add #a #d) = 
  fraction_add_all_are_units #a #d;    
  reveal_opaque (`%is_symmetric) (is_symmetric #(fraction d));       
  reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #(units_of (fraction_add #a #d)));
  Classical.forall_intro_2 (fraction_neg_respects_equivalence_of_units #a #d);
  assert (unary_congruence_condition #(fraction d) fraction_neg fraction_eq);
  fun (f: fraction d) ->   
    fraction_neg_op f

(*
  fraction_negation_respects_equivalence #a #d;
  fraction_add_all_are_units #a #d;  
//  assert (equivalence_wrt_condition #(fraction d) fraction_add fraction_eq);
//  assert (all_are_units #(fraction d) fraction_add fraction_eq);
//  reveal_opaque (`%is_reflexive) (is_reflexive #(fraction d)); 
  reveal_opaque (`%is_reflexive) (is_reflexive #(units_of #(fraction d) fraction_add)); 
  reveal_opaque (`%is_symmetric) (is_symmetric #(fraction d));   
  reveal_opaque (`%is_symmetric) (is_symmetric #(units_of #(fraction d) fraction_add));   
  reveal_opaque (`%is_transitive) (is_transitive #(fraction d));
  reveal_opaque (`%is_transitive) (is_transitive #(units_of #(fraction d) fraction_add));
//  reveal_opaque (`%is_unit) (is_unit #(fraction d));
  reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #(units_of #(fraction d) fraction_add));
  assert (unary_congruence_condition #(fraction d) fraction_neg fraction_eq);
  Classical.forall_intro_2 (fraction_neg_respects_equivalence_of_units #a #d);
  assert (unary_congruence_condition #(units_of #(fraction d) fraction_add) fraction_neg fraction_eq);
  fun x -> fraction_neg x

*)

let fraction_neg_yields_inverses_for_units (#a:Type) (#d: integral_domain a) 
                                           (x: units_of #(fraction d) (fraction_add #a #d))
  : Lemma (is_neutral_of (fraction_add (fraction_neg x) x) (fraction_add #a #d) /\
           is_neutral_of (fraction_add x (fraction_neg x)) (fraction_add #a #d)) = 
           fraction_neg_is_inverse_for_add x           
 
 
let fraction_neg_u (#a:Type) (#d: integral_domain a) : unary_op_on_units_of (fraction_add #a #d) = 
  fraction_neg_units
 

let fraction_neg_uo (#a:Type) (#d: integral_domain a) 
  : (unary_op_on_units_of #(fraction d) (fraction_add #a #d)) =  
  reveal_opaque (`%unary_congruence_condition) 
                (unary_congruence_condition #(units_of (fraction_add #a #d)) fraction_neg_u); 
  Classical.forall_intro_2 (fraction_neg_respects_equivalence_of_units #a #d);
  fraction_add_all_are_units #a #d;
  fraction_neg_u #a #d
  
let fraction_neg_properties (#a:Type) (d: integral_domain a) : Lemma (
     congruence_condition (fraction_add #a #d) fraction_eq /\
     all_are_units (fraction_add #a #d) /\
     unary_congruence_condition (fraction_neg #a #d) (fraction_eq) /\ 
     yields_inverses_for_units #(fraction d) #fraction_eq #(fraction_add #a #d) fraction_neg_uo) = 
     
    assert (congruence_condition (fraction_add #a #d) fraction_eq);
    assert (unary_congruence_condition (fraction_neg #a #d) fraction_eq);
    fraction_add_all_are_units #a #d;
    assert (all_are_units (fraction_add #a #d));
    Classical.forall_intro (fraction_neg_yields_inverses_for_units #a #d);
    fraction_negation_respects_equivalence #a #d;
    Classical.forall_intro_2 (fraction_neg_respects_equivalence_of_units #a #d);
    reveal_opaque (`%is_reflexive) (is_reflexive #(units_of #(fraction d) (fraction_add #a #d))); 
    reveal_opaque (`%is_symmetric) (is_symmetric #(fraction d));   
    reveal_opaque (`%is_symmetric) (is_symmetric #(units_of #(fraction d) (fraction_add #a #d)));   
    reveal_opaque (`%is_transitive) (is_transitive #(fraction d));
    reveal_opaque (`%is_transitive) (is_transitive #(units_of #(fraction d) (fraction_add #a #d)));
    reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #(units_of #(fraction d) (fraction_add #a #d))); 
    assert (yields_inverses_for_units #(fraction d) #(fraction_eq #a #d) #(fraction_add #a #d) fraction_neg_uo);
    ()  
    
let fraction_neg_yields_inverses_for_units_forall (#a:Type) (d: integral_domain a) : Lemma (
    yields_inverses_for_units #(fraction d) #(fraction_eq) #(fraction_add #a #d) fraction_neg_uo) =  
  fraction_neg_properties d 
 
let fraction_additive_group (#a:Type) (d: integral_domain a) : commutative_group (fraction d) = 
  fraction_add_all_are_units #a #d; 
  fraction_neg_yields_inverses_for_units_forall d;  
  fraction_neg_properties d; 
  Classical.forall_intro_2 (fraction_neg_respects_equivalence #a #d);
  Classical.forall_intro_2 (fraction_neg_respects_equivalence_of_units #a #d);
  let zero = fraction_zero d in
  let fadd = fraction_add #a #d in
  let fneg = fun (x: units_of (fraction_add #a #d)) -> fraction_neg x in
  let aux (p: fraction d) : Lemma (
    is_neutral_of (fraction_add p (fneg p)) (fraction_add #a #d) /\
    is_neutral_of (fraction_add (fneg p) p) (fraction_add #a #d) 
  ) = fraction_neg_is_inverse_for_add p in Classical.forall_intro aux;
  reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #(fraction d) #(fraction_eq #a #d));
  reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #(fraction d)); 
  assert (is_inverse_operation_for fneg fadd); 
  reveal_opaque (`%unary_congruence_condition) 
                (unary_congruence_condition #(units_of #(fraction d) (fraction_add #a #d))); 
  Mkmagma (fraction_eq #a #d) fadd fneg zero 
#pop-options 

