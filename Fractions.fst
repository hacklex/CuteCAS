module Fractions

open AlgebraTypes
open Fractions.Definition
open Fractions.Equivalence
open Fractions.Addition
open Fractions.Multiplication

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1"

/// Here, we construct the field of fractions for an arbitrary integral domain.
/// We utilize the algebraic structures of (+) and (*) defined in Fractions.Addition
/// and Fractions.Multiplication respectively. All that is left is proving the
/// lemmas 

/// The field of fractions has no use for unit/normal decomposition since all nonzero elements are units anyway.
/// Still, since the algebraic structure demands it, we provide the trivial decomposition and the zero norm.
private let fraction_unit_part (#a: Type) (#d: integral_domain a) (x: fraction d) : units_of (fraction_mul #a #d) = fraction_one d

private let fraction_unit_part_f (#a: Type) (d: integral_domain a) : (fraction d) -> units_of (fraction_mul #a #d)
  = fraction_unit_part

private let fraction_normal_part (#a: Type) (#d: integral_domain a) (x: fraction d) = x

private let fraction_normal_part_f #a (d: integral_domain a) 
  : (fraction d) -> unit_normal_of (fraction_mul #a #d) (fraction_unit_part_f d)
  = fraction_normal_part

private let fraction_norm (#a: Type) (#d: integral_domain a) (x: fraction d) 
  : (v:option nat { v == None ==> is_absorber_of x fraction_mul }) = 
  if (x.num `d.eq` d.addition.neutral) 
  then (absorber_equal_is_absorber d.multiplication.op d.addition.neutral x.num;
        fraction_absorber_condition x;
        None)
  else Some 0

private let fraction_norm_f (#a:Type) (d: integral_domain a) 
  : nat_function_defined_on_non_absorbers (fraction_mul #a #d) = fraction_norm

/// This is only left to demonstrate just how much better the calc approach is,
/// when it comes to proving identities by transforming LHS all the way to RHS.
///
/// Notice how it takes much more resources from the prover, and is actually
/// way less readable than the proof below. And to top it off, it is not even shorter!
#push-options "--z3rlimit 10"
private let left_distributivity_nocalc (#p: Type) (#dom: integral_domain p) 
                                       (x y z: fraction dom) 
  : Lemma (fraction_eq (fraction_mul x (fraction_add y z)) (fraction_add (fraction_mul x y) (fraction_mul x z))) =
    reveal_opaque (`%is_reflexive) (is_reflexive #p); 
    reveal_opaque (`%is_symmetric) (is_symmetric #p); 
    reveal_opaque (`%is_transitive) (is_transitive #p);
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive dom.multiplication.op);     
    let ( *) = dom.multiplication.op in
    let (+) = dom.addition.op in
    let mul = dom.multiplication.op in //because ( *) is uglier than mul
    let eq = dom.eq in   
    let (a,b,c,d,e,f) = (x.num,x.den,y.num,y.den,z.num,z.den) in   
    assoc_lemma_4 mul a c b f;                                                         // (ac)(bf)   =>   a (cbf)
    bring_any_operand_forth mul a c b f;                                              // a(cbf)     =>   b(acf)
    congruence_lemma_3 (+) ((a*c)*(b*f)) (b*(a*(c*f))) ((b*d)*(a*e)); // acbf+bdae  =>   bacf+bdae
    assoc_lemma_4 mul b d a e;                                                         // (bd)(ae)   =>   b(d(ae))
    assoc_lemma_3 mul d a e;                                                           // d(ae)      =>   (da)e
    comm_lemma mul d a;                                                               // da         =>   ad 
    congruence_lemma_3 mul (d*a) (a*d) e;                            // (da)e      =>   (ad)e
    assoc_lemma_3 mul a d e;                                                           // (ad)e      =>   a(de)     
    congruence_lemma_3 mul ((d*a)*e) (a*(d*e)) b;                    // b(d(ae))   =>   b(a(de))
    congruence_lemma_3 (+) ((b*d)*(a*e)) (b*(a*(d*e))) (b*(a*(c*f))); // bacf+bdae  =>   b(acf)+b(ade)
    trans_lemma_4 eq (fraction_add (fraction_mul x y) (fraction_mul x z)).num
                     (((a*c)*(b*f)) + ((b*d)*(a*e)))
                     ((b*(a*(c*f))) + ((b*d)*(a*e)))
                     ((b*(a*(c*f))) + (b*(a*(d*e))));
    assoc_lemma_4 mul b d b f; 
    bring_any_operand_forth mul b d b f; 
    assoc_lemma_4 mul b b d f;     
    trans_lemma eq (fraction_add (fraction_mul x y) (fraction_mul x z)).den
                   ((b*d)*(b*f))
                   (b*(b*(d*f)));
                   
    dom.left_distributivity b (a*(c*f)) (a*(d*e));
    dom.left_distributivity a (c*f) (d*e);
    congruence_lemma_3 mul ((a*(c*f))+(a*(d*e))) (fraction_mul x (fraction_add y z)).num b;
    congruence_lemma_3 mul (b*(d*f)) (fraction_mul x (fraction_add y z)).den b;     
    fraction_equality_from_known_factor (fraction_mul x (fraction_add y z)) (fraction_add (fraction_mul x y) (fraction_mul x z)) b 
#pop-options
 
private let left_distributivity (#p: Type) (#dom: integral_domain p) (x y z: fraction dom) 
  : Lemma (fraction_eq (fraction_mul x (fraction_add y z)) (fraction_add (fraction_mul x y) (fraction_mul x z))) =
    reveal_opaque (`%is_symmetric) (is_symmetric #p); 
    reveal_opaque (`%is_transitive) (is_transitive #p);    
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive dom.multiplication.op); 
    Classical.forall_intro_3 dom.left_distributivity;
    Classical.forall_intro_3 dom.right_distributivity;
    let ( *) = dom.multiplication.op in
    let (+) = dom.addition.op in
    let mul = dom.multiplication.op in //because ( *) is both uglier than mul and slower to type
    let eq = dom.eq in   
    let mul_assoc_4 = assoc_lemma_4 mul in
    let mul_assoc_3 = assoc_lemma_3 mul in
    let mul_congruence = congruence_lemma_3 mul in
    let add_congruence = congruence_lemma_3 (+) in
    let (a,b,c,d,e,f) = (x.num,x.den,y.num,y.den,z.num,z.den) in  
    calc eq {
      ((a*c)*(b*f)) + ((b*d)*(a*e)); //numerator of xy+xz
      eq { 
         mul_assoc_4 a c b f;                                     // (ac)(bf)   =>   a (cbf)
         bring_any_operand_forth mul a c b f;                  // a(cbf)     =>   b(acf)
         add_congruence ((a*c)*(b*f)) (b*(a*(c*f))) ((b*d)*(a*e)) // acbf+bdae  =>   bacf+bdae
      }        
      (b*(a*(c*f))) + ((b*d)*(a*e));
      eq {
         mul_assoc_4 b d a e;                                     // (bd)(ae)   =>   b(d(ae))
         mul_assoc_3 d a e;                                       // d(ae)      =>   (da)e
         comm_lemma mul d a;                                   // da         =>   ad 
         mul_congruence (d*a) (a*d) e;                            // (da)e      =>   (ad)e
         mul_assoc_3 a d e;                               // (ad)e      =>   a(de)        
         mul_congruence ((d*a)*e) (a*(d*e)) b;                    // b(d(ae))   =>   b(a(de))
         add_congruence ((b*d)*(a*e)) (b*(a*(d*e))) (b*(a*(c*f))) // bacf+bdae  =>   b(acf)+b(ade)
      }
      (b*(a*(c*f))) + (b*(a*(d*e)));      
    };
    assert ((fraction_mul x (fraction_add y z)).den `eq` (b*(d*f))); 
    calc eq {
      (fraction_add (fraction_mul x y) (fraction_mul x z)).den;
      eq {}
      (b*d)*(b*f);
      eq {
        assoc_lemma_4 mul b d b f; 
        bring_any_operand_forth mul b d b f; 
        assoc_lemma_4 mul b b d f 
      }
      b*(b*(d*f));
    };
    fraction_equality_from_known_factor (fraction_mul x (fraction_add y z)) (fraction_add (fraction_mul x y) (fraction_mul x z)) b

let right_distributivity (#p: Type) (#dom: integral_domain p) (x y z: fraction dom) 
  : Lemma (fraction_eq (fraction_mul (fraction_add x y) z) (fraction_add (fraction_mul x z) (fraction_mul y z))) =
  reveal_opaque (`%is_reflexive) (is_reflexive #(fraction dom)); 
  reveal_opaque (`%is_symmetric) (is_symmetric #(fraction dom));  
  reveal_opaque (`%is_transitive) (is_transitive #(fraction dom));   
  let equivalence_wrt_add = congruence_lemma_3 (fraction_add #p #dom) in
  let (=) = fraction_eq #p #dom in
  let (+) = fraction_add #p #dom in
  let ( *) = fraction_mul #p #dom in
  let commutativity = comm_lemma ( *) in
  commutativity z x; 
  commutativity z y;   
  calc (=) {
    (x+y)*z;
    = {commutativity (x + y) z}
    z*(x + y);  
    = {left_distributivity z x y}
    z*x + z*y;
    = {equivalence_wrt_add (z*x) (x*z) (z*y)}
    x*z + z*y;
    = {equivalence_wrt_add (z*y) (y*z) (x*z)}
    x*z + y*z;
  } 
  
private let fraction_distributivity_lemma (#p: Type) (#dom: integral_domain p) 
  : Lemma (is_fully_distributive #(fraction dom) fraction_mul (fraction_add #p #dom)) =  
  reveal_opaque (`%is_fully_distributive) (is_fully_distributive #(fraction dom) #fraction_eq); 
  reveal_opaque (`%is_left_distributive) (is_left_distributive #(fraction dom) #fraction_eq); 
  reveal_opaque (`%is_right_distributive) (is_right_distributive #(fraction dom) #fraction_eq);   
  Classical.forall_intro_3 (left_distributivity #p #dom);
  Classical.forall_intro_3 (right_distributivity #p #dom) 

private let fraction_nonabsorbers_are_regular (#p:Type) (#d: integral_domain p)
  : Lemma (has_no_absorber_divisors #(fraction d) fraction_mul) =   
  reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors (fraction_mul #p #d));    
  let aux (x y: fraction d) : Lemma (requires is_absorber_of (fraction_mul x y) fraction_mul /\
                                              (~(is_absorber_of x fraction_mul)) /\
                                              (~(is_absorber_of y fraction_mul)))
                                    (ensures False) = 
    fraction_nonabsorber_is_unit y;
    let y' = fraction_inv y in
    absorber_lemma fraction_mul (fraction_mul x y) y';
    assert (is_absorber_of (fraction_mul (fraction_mul x y) y') fraction_mul);
    assoc_lemma_3 fraction_mul x y y';
    assert (is_neutral_of (fraction_mul y y') fraction_mul);
    neutral_lemma fraction_mul (fraction_mul y y') x;
    assert (fraction_eq (fraction_mul x (fraction_mul y y')) x);
    trans_lemma fraction_eq x (fraction_mul x (fraction_mul y y')) 
                              (fraction_mul (fraction_mul x y) y');
    absorber_equal_is_absorber fraction_mul (fraction_mul (fraction_mul x y) y') x
    in 
  let aux_2 (x y: fraction d) 
    : Lemma (requires is_absorber_of (fraction_mul x y) fraction_mul)
            (ensures is_absorber_of x fraction_mul \/ is_absorber_of y fraction_mul) = 
      Classical.move_requires_2 aux x y in 
  let aux_3 (x y: fraction d) 
    : Lemma (requires is_absorber_of x fraction_mul)
            (ensures is_absorber_of (fraction_mul x y) fraction_mul /\ 
                     is_absorber_of (fraction_mul y x) fraction_mul) = 
      absorber_lemma fraction_mul x y in
  Classical.forall_intro_2 (Classical.move_requires_2 aux_2);
  Classical.forall_intro_2 (Classical.move_requires_2 aux_3)

let fraction_eq_is_the_same #a (d: integral_domain a)
  : Lemma ((fraction_multiplicative_almost_group #a #d).eq ==
           (fraction_additive_group d).eq) = ()

let fraction_ring_distr #a (d: integral_domain a) : Lemma (is_fully_distributive
  #(fraction d)
  #(fraction_eq #a #d)
  ((fraction_multiplicative_almost_group #a #d).op <: (binary_op (fraction d)))
  (((fraction_additive_group d).op) <: (binary_op (fraction d)))) =
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive #(fraction d) #fraction_eq); 
  reveal_opaque (`%is_left_distributive) (is_left_distributive #(fraction d) #fraction_eq); 
  reveal_opaque (`%is_right_distributive) (is_right_distributive #(fraction d) #fraction_eq);   
  fraction_distributivity_lemma #a #d;
  let addition = fraction_additive_group d in
  let multiplication = fraction_multiplicative_almost_group #a #d in
  let eq = fraction_eq #a #d in
  ()

[@@"opaque_to_smt"]
let fraction_add_grp #a (d: integral_domain a) : commutative_group (fraction d) = 
  fraction_additive_group d 

[@@"opaque_to_smt"]
let fraction_mul_grp #a (d: integral_domain a) : commutative_monoid (fraction d) =
  fraction_multiplicative_almost_group #a #d

[@@"opaque_to_smt"]
let op_of #t (m: magma t) : op_with_congruence m.eq = m.op

let fraction_ring_op_distr #a (d: integral_domain a)
  : Lemma (
      let add = op_of (fraction_add_grp d) in
      let mul = op_of (fraction_mul_grp d) in
      reveal_opaque (`%fraction_add_grp) (fraction_add_grp d);
      reveal_opaque (`%fraction_mul_grp) (fraction_mul_grp d);
      is_fully_distributive #(fraction d) #(fraction_eq #a #d) (mul <: binary_op (fraction d)) (add <: binary_op (fraction d))
    ) = 
    reveal_opaque (`%fraction_add_grp) (fraction_add_grp d);    
    reveal_opaque (`%fraction_mul_grp) (fraction_mul_grp d);    
    reveal_opaque (`%op_of) (op_of #(fraction d));
    assert (op_of (fraction_add_grp d) == fraction_add #a #d);
    assert (op_of (fraction_mul_grp d) == fraction_mul #a #d);
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive #(fraction d) #fraction_eq); 
    reveal_opaque (`%is_left_distributive) (is_left_distributive #(fraction d) #fraction_eq); 
    reveal_opaque (`%is_right_distributive) (is_right_distributive #(fraction d) #fraction_eq);  
    fraction_distributivity_lemma #a #d;
    ()

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1"
let unit_subfunc #a (d: integral_domain a) (p: fraction d) : (u:fraction d{is_unit u (fraction_multiplicative_almost_group #a #d).op}) =
  let up = fraction_unit_part_f d p in
  let mg = fraction_multiplicative_almost_group #a #d in
  let mul = mg.op in
//  uncommenting the assertions below breaks every hell loose.

//  assert (fraction_eq #a #d == mg.eq);
//  assert (mul == fraction_mul #a #d);
//  assert (units_of (fraction_mul #a #d) == units_of (fraction_multiplicative_almost_group #a #d).op);
//  assert (is_unit up mul);
//  assert (is_unit #(fraction d) #mg.eq up (fraction_multiplicative_almost_group #a #d).op);
  up 
  
let fr_up_func #a (d: integral_domain a) (p: fraction d) 
  : units_of #(fraction d) 
             #(fraction_multiplicative_almost_group #a #d).eq 
             (fraction_multiplicative_almost_group #a #d).op = 
  unit_subfunc d p

let typed_fr_up_func #a (d: integral_domain a) 
  : ((fraction d) -> (units_of #(fraction d) 
                              #(fraction_multiplicative_almost_group #a #d).eq 
                              (fraction_multiplicative_almost_group #a #d).op)) =
  fr_up_func d


let normal_subfunc #a (d: integral_domain a) 
                      (up: a -> units_of (fraction_multiplicative_almost_group #a #d).op) 
                      (p: fraction d) 
  : (u: fraction d{is_neutral_of (fr_up_func d u) (fraction_multiplicative_almost_group #a #d).op}) = 
  fraction_normal_part_f d p  
 
let unit_normal_of_frac #a (d: integral_domain a)  
                      (p: fraction d) 
  : (u: fraction d{is_unit_normal (fraction_multiplicative_almost_group #a #d).op (fr_up_func d) u  }) = 
  fraction_normal_part_f d p  

let frac_euc_norm_fun #a (d: integral_domain a) (x: fraction d) 
  : Pure (option nat)
         (requires True)
         (ensures fun v -> v=None ==> is_absorber_of x (fraction_multiplicative_almost_group #a #d).op) =
    fraction_norm_f d x

let fr_eu #a (d: integral_domain a) : nat_function_defined_on_non_absorbers (fraction_multiplicative_almost_group #a #d).op = frac_euc_norm_fun d 
#pop-options




#push-options "--ifuel 0 --fuel 0 --z3rlimit 1"
#restart-solver 
let fraction_field (#a:Type) (d: integral_domain a) : field (fraction d) =  
  fraction_one_is_not_equal_to_fraction_zero #a #d;
  fraction_nonabsorbers_are_regular #a #d;  
  Classical.forall_intro (fraction_unit_cant_be_absorber #a #d);  
  Classical.forall_intro (fraction_nonabsorber_is_unit #a #d); 
  {
    addition = fraction_additive_group d;
    multiplication = fraction_multiplicative_almost_group #a #d;
    eq = fraction_eq #a #d;
    left_distributivity = (left_distributivity #a #d);
    right_distributivity = (right_distributivity #a #d);
    unit_part_of = fr_up_func d ;
    normal_part_of = unit_normal_of_frac d;
    euclidean_norm = fr_eu d
  }







let fraction_field2 (#a:Type) (d: integral_domain a) : field (fraction d) =   
  fraction_distributivity_lemma #a #d;
  fraction_one_is_not_equal_to_fraction_zero #a #d;
  fraction_nonabsorbers_are_regular #a #d;
  Classical.forall_intro (fraction_unit_cant_be_absorber #a #d);  
  Classical.forall_intro (fraction_nonabsorber_is_unit #a #d);
  let addition = fraction_additive_group d in
  let multiplication = fraction_multiplicative_almost_group #a #d in
  let eq = fraction_eq #a #d in
  let zero = fraction_absorber d in  
  assert (zero == addition.neutral);
  assert (addition.eq == multiplication.eq);
  assert (congruence_condition addition.op eq);
  assert (congruence_condition multiplication.op eq);
  assert (eq == addition.eq);
  assert (multiplication.op == fraction_mul #a #d);
  assert (is_fully_distributive multiplication.op addition.op);
  assert (is_absorber_of addition.neutral multiplication.op);    
  { 
    addition = addition;
    multiplication = multiplication;
    eq = eq;
    left_distributivity = (left_distributivity #a #d);
    right_distributivity = (right_distributivity #a #d);
    unit_part_of = fr_up_func d;
    normal_part_of = unit_normal_of_frac d;
    euclidean_norm = fr_eu d
  }
#pop-options

