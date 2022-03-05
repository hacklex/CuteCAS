module Fractions.Addition

open AlgebraTypes
open Fractions.Definition
open Fractions.Equivalence

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1"

/// We declare the type of fractions_add heavily refined so that our
/// future lemmas will not have it too rough proving stuff
let fraction_add (#a: Type) (#d: integral_domain #a) (x y: fraction d)
  : (t: fraction d
     {
       t.num `d.eq` ((x.num `d.multiplication.op` y.den) `d.addition.op` (x.den `d.multiplication.op` y.num)) /\
       t.den `d.eq` (x.den `d.multiplication.op` y.den) 
     }) = 
   reveal_opaque (`%is_reflexive) (is_reflexive #a);
   product_of_denominators_is_denominator x y;
   Fraction ((x.num `d.multiplication.op` y.den) `d.addition.op` (x.den `d.multiplication.op` y.num))
            (x.den `d.multiplication.op` y.den) 

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
   fraction_equality_early_escape x_plus_y y_plus_x;
  ()

let fraction_addition_is_commutative (#a:Type) (#d: integral_domain) : Lemma (is_commutative #(fraction d) fraction_add fraction_eq) =   
   reveal_opaque (`%is_commutative) (is_commutative #(fraction d)); 
   Classical.forall_intro_2 (fraction_add_is_commutative #a #d)
 
private let fraction_add_is_associative (#a:Type) (d: integral_domain #a) (x y z: fraction d) 
  : Lemma ((fraction_add (fraction_add x y) z) `fraction_eq` (fraction_add x (fraction_add y z))) = 
   reveal_opaque (`%is_left_distributive) (is_left_distributive #a); 
   reveal_opaque (`%is_right_distributive) (is_right_distributive #a); 
   reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a); 
   //we calculate the sum of three fractions in 2 different orders,
   //and prove the results (sum_1 and sum_2) to be equal wrt. domain equality relation
   let eq = d.eq in 
   let add = d.addition.op in
   let mul = d.multiplication.op in 
   let sum_1 = fraction_add  (fraction_add x y) z in 
   right_distributivity_lemma mul add eq (x.num `mul` y.den) (x.den `mul` y.num) z.den; // (ad+bc)f   
   equivalence_wrt_operation_lemma #a #add eq (((x.num `mul` y.den) `add` (x.den `mul` y.num)) `mul` z.den) 
                                              (((x.num `mul` y.den) `mul` z.den) `add` ((x.den `mul` y.num) `mul` z.den)) 
                                              ((x.den `mul` y.den) `mul` z.num); //substitute (ad+bc)f + (bd)e ==> (ad)f+(bc)f+(bd)e
   //just to keep track of what sum_1.num is currently known to be equal to
   //assert (sum_1.num `eq` ((((x.num `mul` y.den) `mul` z.den) `add` ((x.den `mul` y.num) `mul` z.den)) `add` ((x.den `mul` y.den) `mul` z.num)) );
     
   let sum_2 = fraction_add x (fraction_add y z) in 
   //assert (sum_1.den `eq` ((x.den `mul` y.den) `mul` z.den));
   //assert (sum_2.den `eq` (x.den `mul` (y.den `mul` z.den)));
   //assert (sum_1.den `eq` sum_2.den);
   //symm_lemma eq sum_2.den sum_1.den;
   //assert (sum_2.den `eq` sum_1.den);
    
   left_distributivity_lemma mul add eq x.den (y.num `mul` z.den) (y.den `mul` z.num); // b(cf+de) = b(cf)+b(de)
   equivalence_wrt_operation_lemma #a #add eq (x.den `mul` ((y.num `mul` z.den) `add` (y.den `mul` z.num))) // b*(cf+de)
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
   equivalence_wrt_operation_lemma #a #add eq part_1 part_1_r (part_2 `add` part_3);
   //assert ((part_1 `add` (part_2 `add` part_3)) `eq` (part_1_r `add` (part_2 `add` part_3)));
   trans_lemma eq sum_2.num (part_1 `add` (part_2 `add` part_3)) (part_1_r `add` (part_2 `add` part_3));
   //assert (sum_2.num `eq` (part_1_r `add` (part_2 `add` part_3)));
   equivalence_wrt_operation_lemma #a #add eq part_2 part_2_r part_3;
   //assert ((part_2 `add` part_3) `eq` (part_2_r `add` part_3)); 
   equivalence_wrt_operation_lemma #a #add eq part_3 part_3_r part_2_r;
   //assert ((part_2_r `add` part_3) `eq` (part_2_r `add` part_3_r)); 
   trans_lemma eq (part_2 `add` part_3) (part_2_r `add` part_3) (part_2_r `add` part_3_r);
   equivalence_wrt_operation_lemma #a #add eq (part_2 `add` part_3) (part_2_r `add` part_3_r) part_1_r;
   trans_lemma eq sum_2.num (part_1_r `add` (part_2 `add` part_3)) (part_1_r `add` (part_2_r `add` part_3_r));
   //assert (sum_2.num `eq` (part_1_r `add` (part_2_r `add` part_3_r)));
   assoc_lemma3 eq add part_1_r part_2_r part_3_r;  
   //assert ((part_1_r `add` (part_2_r `add` part_3_r)) `eq` ((part_1_r `add` part_2_r) `add` part_3_r));
   trans_lemma eq sum_2.num (part_1_r `add` (part_2_r `add` part_3_r)) ((part_1_r `add` part_2_r) `add` part_3_r);
   //assert (sum_2.num `eq` (part_1_r `add` part_2_r `add` part_3_r));
   trans_lemma eq sum_1.num (part_1_r `add` part_2_r `add` part_3_r) sum_2.num;
   //assert (sum_1.num `eq` sum_2.num);
   //assert (sum_1.den `eq` sum_2.den);
   fraction_equality_early_escape sum_1 sum_2
   //assert (fraction_eq sum_1 sum_2) // production variant will only contain the lemma invocations of course :)
  
private let fraction_addition_is_associative (#a:Type) (d: integral_domain #a) 
  : Lemma (is_associative #(fraction d) (fraction_add  #a) (fraction_eq #a)) = 
  reveal_opaque (`%is_associative) (is_associative #(fraction d));   
  Classical.forall_intro_3 (fraction_add_is_associative d)
 
private let fraction_neg (#a:Type) (#d: integral_domain #a) (x: fraction d) : (t: fraction d{ d.eq t.num (d.addition.inv x.num) /\ d.eq t.den x.den }) = 
    reveal_opaque (`%is_reflexive) (is_reflexive #a);
    Fraction (d.addition.inv x.num) (x.den) 
  
#push-options "--z3rlimit 2"
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

private let fraction_zero_is_neutral_lemma (#a:Type) (#d: integral_domain #a) (x: fraction d{is_neutral_of x.num d.addition.op d.eq})  
  : Lemma (is_neutral_of x fraction_add fraction_eq) =   
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d)); 
  reveal_opaque (`%is_left_id_of) (is_left_id_of #(fraction d)); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #(fraction d)); 
  Classical.forall_intro (fraction_additive_neutral_lemma d x)

private let fraction_zero (#a:Type) (d: integral_domain #a) : (z:neutral_element_of #(fraction d) fraction_add fraction_eq { d.eq z.num d.addition.neutral
                                                                                                                            /\ d.eq z.den d.multiplication.neutral })
  = 
  one_is_valid_denominator d;
  let zero = Fraction d.addition.neutral d.multiplication.neutral in
  fraction_zero_is_neutral_lemma zero;
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  zero

let fraction_additive_neutral_condition (#a:Type) (d: integral_domain #a) (x: fraction d{is_neutral_of x.num d.addition.op d.eq})
  : Lemma (is_neutral_of x fraction_add fraction_eq) = 
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d));
  reveal_opaque (`%is_left_id_of) (is_left_id_of #(fraction d));
  reveal_opaque (`%is_right_id_of) (is_right_id_of #(fraction d));
  Classical.forall_intro (fraction_additive_neutral_lemma d x) 


/// Proof that fraction addition respects fraction equality is lengthy, so I only commented out the intermediate asserts,
/// but dare not remove them, as they help understanding the purpose of the proof steps 
#push-options "--z3rlimit 3"
private let fraction_equivalence_respects_add (#a:Type) (d: integral_domain #a) (e1: fraction d) (e2: fraction d{e1 `fraction_eq` e2 }) (x: fraction d) 
  : Lemma ((x `fraction_add` e1) `fraction_eq` (x `fraction_add` e2) /\ (e1 `fraction_add` x ) `fraction_eq` (e2 `fraction_add` x)) = 
  let mul = d.multiplication.op in
  let eq = d.eq in
  let add = d.addition.op in 
  //reveal_opaque (`%is_reflexive) (is_reflexive #a); 
 
  ring_distributivity_lemma d;  
  //assert ((x `fraction_add` e1).num `d.eq`  ((x.num `mul` e1.den) `add` (x.den `mul` e1.num)));
  //assert ((x `fraction_add` e2).num `d.eq`  ((x.num `mul` e2.den) `add` (x.den `mul` e2.num)));
  //assert ((x `fraction_add` e1).den `d.eq` (x.den `mul` e1.den));
  //assert ((x `fraction_add` e2).den `d.eq` (x.den `mul` e2.den));
  right_distributivity_lemma mul add d.eq (x.num `mul` e1.den) (x.den `mul` e1.num) (x.den `mul` e2.den);
  assert ( (((x.num `mul` e1.den) `add` (x.den `mul` e1.num)) `mul` (x.den `mul` e2.den)) `d.eq`  
           (((x.num `mul` e1.den) `mul` (x.den `mul` e2.den)) `add` ((x.den `mul` e1.num) `mul` (x.den `mul` e2.den))));
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
  Classical.forall_intro_3 (fraction_equivalence_respects_add d)

#push-options "--ifuel 1 --z3rlimit 3"
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

let fraction_negation_respects_equivalence (#a:Type) (#d: integral_domain #a) 
  : Lemma (respects_equivalence #(fraction d) fraction_neg fraction_eq) 
  = reveal_opaque (`%respects_equivalence) (respects_equivalence #(fraction d)); 
    Classical.forall_intro_2 (fraction_neg_respects_equivalence #a #d)

let fraction_addition_properties (#a:Type) (d: integral_domain #a) 
  : Lemma (equivalence_wrt_condition (fraction_add #a #d) fraction_eq /\ 
           is_associative (fraction_add #a #d) fraction_eq /\
           is_commutative (fraction_add #a #d) fraction_eq)
    [SMTPat(fraction_eq #a #d)] =
  fraction_addition_is_associative d; 
  fraction_addition_is_commutative #a #d;
  fraction_equivalence_respects_addition #a #d 
    
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
    fraction_addition_is_associative d;
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
  fraction_addition_is_associative d;
  fraction_add_all_are_units #a #d; 
  fraction_equivalence_respects_addition #a #d;
  fraction_neg_is_inverse_for_addition #a #d;
  fraction_negation_respects_equivalence #a #d;
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
#pop-options

