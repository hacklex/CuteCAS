module Fractions.Multiplication
open AlgebraTypes
open Fractions.Definition
open Fractions.Equivalence

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1"

let fraction_mul (#a:Type) (#d: integral_domain #a) (x y: fraction d) : (t: fraction d{
  t.num `d.eq` (x.num `d.multiplication.op` y.num) /\
  t.den `d.eq` (x.den `d.multiplication.op` y.den)}) = 
  product_of_denominators_is_denominator x y;
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  Fraction (x.num `d.multiplication.op` y.num) (x.den `d.multiplication.op` y.den)
 
let fraction_mul_is_commutative (#a:Type) (#d: integral_domain #a) (x y: fraction d) : Lemma (fraction_mul x y `fraction_eq` fraction_mul y x) = 
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

let fraction_mul_is_associative (#a:Type) (#d: integral_domain #a) (x y z: fraction d) : Lemma (fraction_mul (fraction_mul x y) z `fraction_eq` fraction_mul x (fraction_mul y z)) = 
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
  fraction_equality_early_escape xy_z x_yz; 
()

let fraction_mul_neutral_lemma (#a:Type) (#d: integral_domain #a) (x: fraction d{d.eq x.num x.den \/ d.eq x.den x.num}) (y: fraction d)
  : Lemma (x `fraction_mul` y `fraction_eq` y /\ y `fraction_mul` x `fraction_eq` y) =   
  reveal_opaque (`%is_transitive) (is_transitive #a)

let fraction_mul_neutral_condition (#a:Type) (#d: integral_domain #a) (x: fraction d)
  : Lemma (requires d.eq x.num x.den) (ensures is_neutral_of x fraction_mul fraction_eq) = 
  Classical.forall_intro (fraction_mul_neutral_lemma x);
  reveal_opaque (`%is_left_id_of) (is_left_id_of #(fraction d)); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #(fraction d)); 
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d));
  assert_spinoff (is_neutral_of x fraction_mul fraction_eq)

let fraction_is_mul_neutral (#a:Type) (#d: integral_domain #a) (x: fraction d{d.eq x.num x.den \/ d.eq x.den x.num})
  : Lemma (is_neutral_of x fraction_mul fraction_eq) =  
  reveal_opaque (`%is_left_id_of) (is_left_id_of #(fraction d)); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #(fraction d)); 
  reveal_opaque (`%is_neutral_of) (is_neutral_of #(fraction d)); 
  Classical.forall_intro (fraction_mul_neutral_lemma x)  

let fraction_one_is_neutral_lemma (#a:Type) 
                                          (#d: integral_domain #a) 
                                          (x: fraction d{is_neutral_of x.num d.multiplication.op d.eq /\ is_neutral_of x.den d.multiplication.op d.eq}) 
  : Lemma (is_neutral_of x (fraction_mul) fraction_eq) =
  neutral_is_unique d.multiplication.op d.eq x.num x.den;
  fraction_mul_neutral_condition x

let fraction_absorber (#a:Type) (d: integral_domain #a) : absorber_of #(fraction d) fraction_mul fraction_eq = 
  one_is_valid_denominator d;
  let zero = Fraction d.addition.neutral d.multiplication.neutral in
  fraction_absorber_condition zero;
  zero


let fraction_one (#a:Type) (d: integral_domain #a) 
  : (u: neutral_element_of #(fraction d) fraction_mul fraction_eq { 
        (u.num `d.eq` d.multiplication.neutral) 
      /\ (u.den `d.eq` d.multiplication.neutral)
      /\ is_unit u fraction_mul fraction_eq }) =       
  one_is_valid_denominator d;
  let one = Fraction d.multiplication.neutral d.multiplication.neutral in
  fraction_one_is_neutral_lemma one;
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  reveal_opaque (`%is_unit) (is_unit #(fraction d)); 
  fraction_mul_neutral_condition (fraction_mul one one);
  one
 
let fraction_one_eq_absorber_is_nonsense (#a: Type) (d: integral_domain #a) : Lemma (requires fraction_eq (fraction_one d) (fraction_absorber d)) (ensures False) = 
  let one = fraction_one d in
  let zero = fraction_absorber d in
  reveal_opaque (`%is_reflexive) (is_reflexive #a);
  reveal_opaque (`%is_transitive) (is_transitive #a);
  reveal_opaque (`%is_symmetric) (is_symmetric #a);
  neutral_lemma d.multiplication.op d.eq d.multiplication.neutral d.multiplication.neutral 

let fraction_one_is_not_equal_to_fraction_zero (#a: Type) (#d: integral_domain #a) 
  : Lemma (~(fraction_eq (fraction_one d) (fraction_absorber d)) /\ ~(fraction_eq (fraction_absorber d) (fraction_one d))) = 
  reveal_opaque (`%is_symmetric) (is_symmetric #(fraction d)); 
  Classical.move_requires (fraction_one_eq_absorber_is_nonsense #a) d 

/// Proof that fraction multiplication respects fraction equality is shorter compared to its addition counterpart, 
/// so I did not leave many assertions as trans_lemmas give enough clues to what's happening under the hood.
let fraction_equivalence_respects_mul (#a:Type) (#d: integral_domain #a) (e1: fraction d) (e2: fraction d{e1 `fraction_eq` e2 }) (x: fraction d) 
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
  trans_lemma_4 fraction_eq (fraction_mul e1 x) (fraction_mul x e1) (fraction_mul x e2) (fraction_mul e2 x) 

let fraction_equivalence_respects_multiplication (#a:Type) (#d: integral_domain #a) : Lemma(equivalence_wrt_condition #(fraction d) (fraction_mul #a) (fraction_eq #a)) = 
  reveal_opaque (`%equivalence_wrt_condition) (equivalence_wrt_condition #(fraction d)); 
  Classical.forall_intro_3 (fraction_equivalence_respects_mul #a #d)
 
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
            assert ((xqf.num * x.den) `d.eq` (x.den * x.num));            
            assert ((x.den * xqf.num) `d.eq` (x.den * x.num));
            denominator_is_nonzero d x.den;
            assert (~(is_absorber_of x.den d.multiplication.op d.eq));
            //domain_law_from_pq_eq_pr d x.den xqf.num x.num;
            domain_cancellation_law d x.den xqf.num x.num; 
            assert ((p * q) `d.eq` p);
            assert ((q * p) `d.eq` p);
            symm_lemma d.eq p (p*q);
            symm_lemma d.eq p (q*p);
          () in
          reveal_opaque (`%is_absorber_of) (is_absorber_of #a); 
          Classical.forall_intro aux

let nonabsorber_fraction_means_nonabsorber_enumerator (#a:Type) (#d: integral_domain #a) (x: fraction d) 
  : Lemma (requires ~(is_absorber_of x fraction_mul fraction_eq))
          (ensures ~(is_absorber_of x.num d.multiplication.op d.eq)) 
  = (Classical.move_requires (fraction_absorber_condition)) x
    
let nonabsorber_enumerator_means_nonabsorber_fraction (#a:Type) (#d: integral_domain #a) (x: fraction d)
  : Lemma (requires ~(is_absorber_of x.num d.multiplication.op d.eq))
          (ensures ~(is_absorber_of x fraction_mul fraction_eq)) =           
          Classical.move_requires (fraction_absorber_means_numerator_absorber) x

let fraction_mul_domain_law (#a:Type) (#d: integral_domain #a) (p q: non_absorber_of #(fraction d) fraction_mul fraction_eq)
  : Lemma (~(is_absorber_of (fraction_mul p q) fraction_mul fraction_eq)) = 
  let pq = fraction_mul p q in    
  nonabsorber_fraction_means_nonabsorber_enumerator p;
  nonabsorber_fraction_means_nonabsorber_enumerator q;
  domain_multiplication_law d.eq d.multiplication.op p.num q.num;
  nonabsorber_enumerator_means_nonabsorber_fraction pq

let fraction_multiplication_properties (#a:Type) (d: integral_domain #a) 
  : Lemma (equivalence_wrt_condition (fraction_mul #a #d) fraction_eq /\ 
           is_associative (fraction_mul #a #d) fraction_eq /\
           is_commutative (fraction_mul #a #d) fraction_eq)
    [SMTPat(fraction_eq #a #d)] =
  reveal_opaque (`%is_associative) (is_associative #(fraction d)); 
  reveal_opaque (`%is_commutative) (is_commutative #(fraction d)); 
  Classical.forall_intro_2 (fraction_mul_is_commutative #a #d);
  Classical.forall_intro_3 (fraction_mul_is_associative #a #d);
  fraction_equivalence_respects_multiplication #a #d 
 
let fraction_unit_and_absorber_is_nonsense (#a:Type) (#d: integral_domain #a) (x: fraction d) 
  : Lemma (requires is_unit x fraction_mul fraction_eq /\ is_absorber_of x fraction_mul fraction_eq) (ensures False) =   
  let ( *) = fraction_mul #a #d in
  let eq = fraction_eq #a #d in
  reveal_opaque (`%is_unit) (is_unit #(fraction d)); 
  let x' = IndefiniteDescription.indefinite_description_ghost (units_of ( *) eq) (fun x' -> (is_neutral_of (x * x') ( *) eq /\ is_neutral_of (x' * x) ( *) eq)) in
  let xx' = x * x' in
  let one = fraction_one d in
  let zero = fraction_absorber d in   
  neutral_is_unique ( *) eq xx' one;
  absorber_lemma ( *) eq x x'; 
  absorber_is_unique ( *) eq zero xx';
  trans_lemma eq one xx' zero;
  fraction_one_eq_absorber_is_nonsense d 

let fraction_nonabsorber_means_numerator_nonabsorber  (#a:Type) (#d: integral_domain #a) (x: fraction d) 
  : Lemma (requires ~(is_absorber_of x fraction_mul fraction_eq)) 
          (ensures ~(is_absorber_of x.num d.multiplication.op d.eq))
  = nonabsorber_fraction_means_nonabsorber_enumerator x
 
#push-options "--z3rlimit 2"
let fraction_nonabsorber_is_unit (#a:Type) (#d: integral_domain #a) (x: non_absorber_of #(fraction d) fraction_mul fraction_eq) 
  : Lemma 
       (ensures is_unit x fraction_mul fraction_eq) = 
  
  fraction_nonabsorber_means_numerator_nonabsorber x;
  assert (~(is_absorber_of x.num d.multiplication.op d.eq)); 
  let ( *) = d.multiplication.op in  
  let inv = d.multiplication.inv in  
  let eq : equivalence_wrt d.multiplication.op = d.eq in
  let up = d.unit_part_of in
  let np = d.normal_part_of in 
  let u = x.num in
  let v = x.den in
  let one = fraction_one d in
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

  unit_and_normal_decomposition_lemma ( *) eq up np x.num;
  
  assert (xx'.num `eq` ((up x.num * np x.num) * (x.den * inv (up x.num)))); 
  comm_lemma eq ( *) (up x.num * np x.num) (x.den * inv (up x.num));
  assert (eq ((up x.num * np x.num) * (x.den * inv (up x.num))) ((x.den * inv (up x.num)) * (up x.num * np x.num)));
  assoc_lemma4 eq ( *) x.den (inv (up x.num)) (up x.num) (np x.num);
  assert (eq ((x.den * inv (up x.num)) * (up x.num * np x.num)) ( (x.den * (inv (up x.num) * up x.num)) * (np x.num)));
  assert (is_neutral_of (inv (up x.num) * up x.num) ( *) eq);
  neutral_lemma ( *) eq (inv (up x.num) * up x.num) x.den;
  equivalence_wrt_operation_lemma eq (x.den * (inv (up x.num) * up x.num)) x.den (np x.num);
  trans_lemma eq xx'.num 
                 ((up x.num * np x.num) * (x.den * inv (up x.num)))
                 ((x.den * inv (up x.num)) * (up x.num * np x.num));
                 
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
  assert_spinoff (is_unit x fraction_mul fraction_eq)
#pop-options


let fraction_unit_cant_be_absorber (#a:Type) (#d: integral_domain #a) (x: units_of fraction_mul fraction_eq) : Lemma (~(is_absorber_of x fraction_mul fraction_eq)) = 
  Classical.move_requires (fraction_unit_and_absorber_is_nonsense #a #d) x

let fraction_absorber_cant_be_unit (#a:Type) (#d: integral_domain #a) (x: absorber_of fraction_mul fraction_eq) : Lemma (~(is_unit x fraction_mul fraction_eq)) =
  Classical.move_requires (fraction_unit_and_absorber_is_nonsense #a #d) x
 
let fraction_inv (#a:Type) (#d: integral_domain #a) (x: units_of fraction_mul fraction_eq) 
  : (t:units_of fraction_mul fraction_eq{ is_neutral_of (t `fraction_mul` x) fraction_mul fraction_eq /\ 
                   is_neutral_of (x `fraction_mul` t) fraction_mul fraction_eq /\
                   t.num `d.eq` (d.multiplication.inv (d.unit_part_of x.num) `d.multiplication.op` x.den) /\
                   t.den `d.eq` (d.normal_part_of x.num)  }) = 
  fraction_unit_cant_be_absorber x;
  reveal_opaque (`%is_unit) (is_unit #(fraction d)); 
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  reveal_opaque (`%is_transitive) (is_transitive #a); 
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
  //things are working faster with those three assertions commented out :)
  //assert (xx'.num `eq` (x.den * (inv (up x.num) * x.num)));
  assert (xx'.num `eq` (x.den * (inv (up x.num) * (up x.num * np x.num))));
  assert ((inv (up x.num) * (up x.num * np x.num)) `eq` ((inv (up x.num) * up x.num) * (np x.num)));
  //assert (xx'.num `eq` (x.den * (inv (up x.num) * up x.num) * np x.num));
  //assert (is_neutral_of (inv (up x.num) * up x.num) ( *) eq);
  //assert (xx'.num `eq` (x.den * np x.num));
  assert (xx'.den `eq` (x.den * np x.num));  
  fraction_is_mul_neutral xx'; 
  fraction_is_mul_neutral x'x;   
  invfrac
   
#push-options "--z3rlimit 4"
let fraction_inv_respects_equivalence (#p:Type) (#d: integral_domain #p) (x y: units_of fraction_mul fraction_eq) 
  : Lemma (requires fraction_eq #p #d x y)
          (ensures (fraction_eq #p #d (fraction_inv x) (fraction_inv y) /\ fraction_eq #p #d (fraction_inv y) (fraction_inv x))) = 
  let ( *) = d.multiplication.op in
  let inv = d.multiplication.inv in
  let eq : equivalence_wrt ( *) = d.eq in
  let up = d.unit_part_of in
  let np = d.normal_part_of in  
  let a = x.num in
  let b = x.den in
  let c = y.num in
  let d = y.den in   
  fraction_unit_cant_be_absorber x;
  fraction_unit_cant_be_absorber y;
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
  symm_lemma fraction_eq (fraction_inv y) (fraction_inv x)
#pop-options
  
let fraction_multiplicative_almost_group (#a:Type) (#d: integral_domain #a) : commutative_monoid #(fraction d) = 
  let aux_mul_is_comm () : Lemma (is_commutative #(fraction d) fraction_mul fraction_eq) = 
    reveal_opaque (`%is_commutative) (is_commutative #(fraction d)); 
    Classical.forall_intro_2 (fraction_mul_is_commutative #a #d) in
  aux_mul_is_comm();
  let op : binary_op (fraction d) = fraction_mul in
  let eq : equivalence_wrt op = fraction_eq in
  let fme : equivalence_relation (units_of #(fraction d) fraction_mul fraction_eq) = 
    reveal_opaque (`%is_reflexive) (is_reflexive #(fraction d)); 
    reveal_opaque (`%is_reflexive) (is_reflexive #(units_of #(fraction d) fraction_mul fraction_eq)); 
    reveal_opaque (`%is_symmetric) (is_symmetric #(fraction d)); 
    reveal_opaque (`%is_symmetric) (is_symmetric #(units_of #(fraction d) fraction_mul fraction_eq)); 
    reveal_opaque (`%is_transitive) (is_transitive #(fraction d)); 
    reveal_opaque (`%is_transitive) (is_transitive #(units_of #(fraction d) fraction_mul fraction_eq)); 
    fraction_eq in
  let inv : unary_op_on_units_of op eq =    
    let aux_inv_resp_eq () : Lemma (respects_equivalence #(units_of #(fraction d) fraction_mul fraction_eq) fraction_inv fraction_eq) = 
      reveal_opaque (`%respects_equivalence) (respects_equivalence #(units_of #(fraction d) fraction_mul fraction_eq));  
      reveal_opaque (`%respects_equivalence) (respects_equivalence #(fraction d));  
      reveal_opaque (`%respects_equivalence) (respects_equivalence #(units_of #(fraction d) fraction_mul fraction_eq));  
      reveal_opaque (`%respects_equivalence) (respects_equivalence #(fraction d));  
      Classical.forall_intro (fraction_nonabsorber_is_unit #a #d);
      Classical.forall_intro_2 (Classical.move_requires_2 (fraction_inv_respects_equivalence #a #d));
      () in
    aux_inv_resp_eq();
    fraction_inv in  
  Mkmagma op eq inv (fraction_one d)  

#pop-options
