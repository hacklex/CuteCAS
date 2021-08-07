module AlgebraTypes

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1 --query_stats"

type binary_op (a:Type) = a -> a -> a
type unary_op (a:Type) = a -> a
type predicate (a:Type) = a -> bool
type binary_relation (a: Type) = a -> a -> bool

[@@"opaque_to_smt"]
let is_reflexive  (#a:Type) (r: binary_relation a) = forall (x:a).     x `r` x
[@@"opaque_to_smt"]
let is_symmetric  (#a:Type) (r: binary_relation a) = forall (x y:a).   x `r` y == y `r` x
[@@"opaque_to_smt"]
let is_transitive (#a:Type) (r: binary_relation a) = forall (x y z:a). x `r` y /\ y `r` z ==> x `r` z 

/// We do this for future work with fractions over arbitrary domains.
/// Where there is no GCD computation, there's no reducing a/a to 1/1
/// (or 0/a to 0/1), and we'll use the custom equivalence relation,
/// (a/b)=(c/d) ==def== (ad=bc). The three properties shall be then proven explicitly.
type equivalence_relation (a: Type) = r:binary_relation a{is_reflexive r /\ is_symmetric r /\ is_transitive r}

[@@"opaque_to_smt"]
let equivalence_wrt_condition (#a: Type) (op: binary_op a) (eq: equivalence_relation a) = 
  (forall (x y z:a). (x `eq` y) ==> ((x `op` z) `eq` (y `op` z))  /\ (z `op` x) `eq` (z `op` y))
  
type equivalence_wrt (#a: Type) (op: binary_op a) = eq:equivalence_relation a{equivalence_wrt_condition op eq}

let equivalence_is_symmetric (#a:Type) (eq: equivalence_relation a) (x y:a)
  : Lemma (x `eq` y == y `eq` x) = reveal_opaque (`%is_symmetric) (is_symmetric #a)

//private let eq_rel (a:Type) (eq: equivalence_relation a) : (t:equivalence_relation a {t == eq}) = eq

let trans_lemma (#a:Type) (eq: equivalence_relation a) (x y z:a)
  : Lemma (requires ((x `eq` y) \/ (y `eq` x)) /\ ((y `eq` z) \/ (z `eq` y)))  (ensures x `eq` z && z `eq` x)   
  = reveal_opaque (`%is_transitive) (is_transitive #a);
    reveal_opaque (`%is_symmetric) (is_symmetric #a)

private let trans_lemma_4 (#a:Type) (eq: equivalence_relation a) (x:a)
                                                                 (y:a{eq x y \/ eq y x})
                                                                 (z:a{eq y z \/ eq z y})
                                                                 (w:a{eq z w \/ eq w z})
  : Lemma (x `eq` w /\ w `eq` x) = reveal_opaque (`%is_transitive) (is_transitive #a);
                                  reveal_opaque (`%is_symmetric) (is_symmetric #a)

let symm_lemma (#a:Type) (eq:equivalence_relation a) (x:a) (y:a) : Lemma (x `eq` y == y `eq` x) = reveal_opaque (`%is_symmetric) (is_symmetric #a) 

/// FStar does not automatically apply lemmas on equivalence being symmetric reflexive and transitive.
/// So, I at least make my lemmas such that I care about `eq` operand order as little as possible
let equivalence_wrt_operation_lemma (#a: Type) (#op: binary_op a) (eq: equivalence_wrt op) (e1 e2 z: a)
  : Lemma 
  (requires e1 `eq` e2 \/ e2 `eq` e1) 
  (ensures 
    (e1 `op` z) `eq` (e2 `op` z) /\    
    (e2 `op` z) `eq` (e1 `op` z) /\    
    (z `op` e1) `eq` (z `op` e2) /\
    (z `op` e2) `eq` (z `op` e1)) = reveal_opaque (`%equivalence_wrt_condition) (equivalence_wrt_condition #a);
                                    reveal_opaque (`%is_symmetric) (is_symmetric #a) 
    
let eq_wrt_emulated (#a:Type) (#op: binary_op a) (eq: equivalence_relation a{equivalence_wrt_condition op eq}) (e1 e2 z: a)
  : Lemma 
  (requires e1 `eq` e2 \/ e2 `eq` e1) 
  (ensures 
    (e1 `op` z) `eq` (e2 `op` z) /\    
    (e2 `op` z) `eq` (e1 `op` z) /\    
    (z `op` e1) `eq` (z `op` e2) /\
    (z `op` e2) `eq` (z `op` e1)) = equivalence_wrt_operation_lemma #a #op eq e1 e2 z

/// Here, we define basic axioms of algebraic structures in form of propositions
/// about operations and elements. 
///
/// The forall part has precisely the meaning we expect it to have :)
/// From here, one can deduce what an exists statement would look like...
[@@"opaque_to_smt"]
let is_associative (#a:Type) (op:binary_op a) (eq: equivalence_relation a) = forall (x y z:a). ((x `op` y) `op` z) `eq` (x `op` (y `op` z))
[@@"opaque_to_smt"]
let is_commutative (#a:Type) (op:binary_op a) (eq: equivalence_relation a) = forall (x y:a). (x `op` y) `eq` (y `op` x)


let associative_operation_lemma (#a:Type) (eq: equivalence_relation a) (op:binary_op a{is_associative op eq}) (x y z:a) 
  : Lemma (((x `op` y) `op` z) `eq` (x `op` (y `op` z)) && (x `op` (y `op` z)) `eq` ((x `op` y) `op` z))
  = reveal_opaque (`%is_associative) (is_associative #a);
    reveal_opaque (`%is_symmetric) (is_symmetric #a) 
  

let commutative_substitution_lemma (#a:Type) (#eq: equivalence_relation a) (op: binary_op a{is_commutative op eq}) 
  (x y z: a) : Lemma (x `eq` (y `op` z) == x `eq` (z `op` y)) = 
  reveal_opaque (`%is_commutative) (is_commutative #a);
  reveal_opaque (`%is_transitive) (is_transitive #a) 

let associative_lemma_for_substitution (#a:Type) (eq: equivalence_relation a)
  (op: binary_op a{is_associative op eq}) (x y z w: a)
  : Lemma ( ((x `op` y) `op` z) `eq` w == (x `op` (y `op` z)) `eq` w) = 
  reveal_opaque (`%is_associative) (is_associative #a);
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a) 
  
[@@"opaque_to_smt"]
let is_idempotent (#a:Type) (r: unary_op a) (eq: equivalence_relation a)  = forall (x:a). (r x) `eq` (r (r x))

/// Things quickly get funny if we consider non-associative structures (magmas etc).
/// Therefore we don't, not because we dislike fun, but because we strive for sanity.


[@@"opaque_to_smt"]
let is_left_id_of  (#a:Type) (u:a) (op:binary_op a) (eq: equivalence_relation a) = forall (x:a). (u `op` x) `eq` x // left identity
[@@"opaque_to_smt"]
let is_right_id_of (#a:Type) (u:a) (op:binary_op a) (eq: equivalence_relation a) = forall (x:a). (x `op` u) `eq` x // right identity
[@@"opaque_to_smt"]
let is_neutral_of  (#a:Type) (u:a) (op:binary_op a) (eq: equivalence_relation a) = is_left_id_of u op eq /\ is_right_id_of u op eq // neutral element

type neutral_element_of (#a: Type) (op: binary_op a) (eq: equivalence_relation a) = (x:a{is_neutral_of x op eq})

let neutral_lemma (#a:Type) (op: binary_op a) (eq: equivalence_relation a) (x: neutral_element_of op eq) (y:a)
  : Lemma ((x `op` y) `eq` y /\ (y `op` x) `eq` y) = 
  reveal_opaque (`%is_left_id_of) (is_left_id_of #a); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #a); 
  reveal_opaque (`%is_neutral_of) (is_neutral_of #a)
  
/// If you see something trivial, then it is either here to reduce the rlimit for some bigger lemma,
/// or a leftover from time where something didn't verify and I made more and more explicit lemmas,
/// or it should be deleted. I periodically cleanup this file and remove unused lemmas.
/// Nothing big gets removed anyway.

let neutral_is_unique (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) (u: neutral_element_of op eq) (v: neutral_element_of op eq) 
  : Lemma (eq u v) = 
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a);  
  reveal_opaque (`%is_left_id_of) (is_left_id_of #a); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #a);
  reveal_opaque (`%is_neutral_of) (is_neutral_of #a)
  

let neutral_equivalent_is_neutral (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) (x: neutral_element_of op eq) (y: a{y `eq` x}) : Lemma (is_neutral_of y op eq) =    
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  reveal_opaque (`%is_left_id_of) (is_left_id_of #a); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #a);
  reveal_opaque (`%is_neutral_of) (is_neutral_of #a);
  reveal_opaque (`%equivalence_wrt_condition) (equivalence_wrt_condition #a); 
  let aux (t:a) : Lemma (((t `op` y) `eq` t) /\ ((y `op` t) `eq` t)) = equivalence_wrt_operation_lemma eq x y t in
  FStar.Classical.forall_intro aux;
  assert (is_neutral_of y op eq);
  ()
  

/// The notion of absorbing element, or absorber, is the generalization of integer zero with respect to multiplication
/// That is, 0x = x0 = 0. Other exmaples are the empty set w.r.t. intersection, 1 w.r.t. GCD in naturals, etc.
[@@"opaque_to_smt"]
let is_absorber_of (#a:Type) (z:a) (op:binary_op a) (eq: equivalence_relation a) = forall (x:a). ((x `op` z) `eq` z) && ((z `op` x) `eq` z)

unfold type absorber_of (#a:Type) (op:binary_op a) (eq: equivalence_relation a) = z:a{is_absorber_of z op eq}
unfold type non_absorber_of (#a:Type) (op: binary_op a) (eq: equivalence_relation a) = z:a{~(is_absorber_of z op eq)}

let absorber_lemma (#a:Type) (op:binary_op a) (eq: equivalence_relation a) (z: a{is_absorber_of z op eq}) (x:a)
  : Lemma ((z `op` x) `eq` z /\ (x `op` z) `eq` z) = 
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a)

/// Proving that in any magma, there may not be 2 distinct absorbers, is left as an exercise to both Z3 and the reader.
/// And Z3 is doing fine on that account, just saying.
let absorber_is_unique (#a:Type) (op: binary_op a) (eq: equivalence_relation a) (z1 z2: a) 
  : Lemma (requires is_absorber_of z1 op eq /\ is_absorber_of z2 op eq) 
          (ensures eq z1 z2 /\ eq z2 z1) = 
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a)
  

let absorber_eq_is_abs (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) (z1: absorber_of op eq) (z2: a{z2 `eq` z1}) (t: a) 
  : Lemma (t `op` z2 `eq` z2 /\ z2 `op` t `eq` z2) =   
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a);
  equivalence_wrt_operation_lemma eq z1 z2 t 

let absorber_equal_is_absorber (#a:Type) (op:binary_op a) (eq: equivalence_wrt op) (z1: absorber_of op eq) (z2:a{z2 `eq` z1}) 
  : Lemma (is_absorber_of z2 op eq) = 
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a);
  FStar.Classical.forall_intro (absorber_eq_is_abs op eq z1 z2)

let absorber_equal_is_absorber_req (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) (z1 z2: a) 
  : Lemma (requires is_absorber_of z1 op eq /\ eq z1 z2) 
          (ensures is_absorber_of z2 op eq) = 
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a);           
  absorber_equal_is_absorber op eq z1 z2
  
let nonabsorber_equal_is_nonabsorber (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) (p: non_absorber_of op eq) (q:a{q `eq` p}) 
  : Lemma (~(is_absorber_of q op eq)) 
  = (Classical.move_requires (absorber_equal_is_absorber_req op eq q)) p


/// Since we are using custom equivalence relation, we specifically assure the existence of
/// the unit. We also write "forall" since, for example, for fractions, there'll also be neutral
/// elements of type a/a, b/b... for nonzero (a, b...), unless we operate in a euclidean domain
/// that offers the algorithm for GCD computation and thus the notion of reduced fractions.
///
/// For arbitrary domains, there is no hope of reduced fractions, so the notions for inverses and neutrals
/// stays in its most general form.
[@@"opaque_to_smt"]
let is_inverse_operation_for (#a: Type) (inv: unary_op a) (op: binary_op a) (eq: equivalence_relation a) 
  = (forall (x:a). is_neutral_of (op x (inv x)) op eq /\ is_neutral_of (op (inv x) x) op eq)

let inverse_operation_lemma (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) (inv: unary_op a{is_inverse_operation_for inv op eq}) (x: a) 
  : Lemma (is_neutral_of (x `op` (inv x)) op eq /\ is_neutral_of ((inv x) `op` x) op eq) = 
  reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #a)

/// The inverse operation type is also a refinement for arbitrary unary operation 
type inverse_op_for (#a: Type) (op: binary_op a) (eq: equivalence_relation a) 
  = (inv:unary_op a{is_inverse_operation_for inv op eq})

let inverses_produce_neutral (#a:Type) (eq: equivalence_relation a) (op: binary_op a{is_associative op eq /\ equivalence_wrt_condition op eq}) (inv: inverse_op_for op eq) (x y: a)
  : Lemma (requires inv x `eq` y)
          (ensures is_neutral_of (x `op` y) op eq) =
    equivalence_wrt_operation_lemma #a #op eq (inv x) y x;
    reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #a);
    neutral_equivalent_is_neutral op eq (x `op` inv x) (x `op` y)

let group_operation_lemma (#a:Type) (eq: equivalence_relation a) 
                             (op: binary_op a{is_associative op eq /\ equivalence_wrt_condition op eq}) 
                             (inv: inverse_op_for op eq) (x y z:a) 
  : Lemma (requires (x `op` z) `eq` (y `op` z)) (ensures (x `eq` y)) =    
  reveal_opaque (`%is_transitive) (is_transitive #a); // we're going to need the transitivity of ==
  let eq_wrt_lemma = equivalence_wrt_operation_lemma #a #op eq in
  let z'  = inv z in
  let op = op in
  let eq  = eq in
  let zz' = z `op` z' in
  let xz = x `op` z in                         // suppose zz'    = 1 (always possible in a group)
  let yz = y `op` z in                         // we have xz     = yz
  eq_wrt_lemma xz yz z';                       // then,   (xz)z' = (yz)z'
  associative_operation_lemma eq op x z z';    // or,     x(zz') = (yz)z'
  inverse_operation_lemma op eq inv z;         // as we know, zz'= 1
  neutral_lemma op eq zz' x;                   // zz'=1,  (zz')x = x
  trans_lemma eq (xz `op` z') (x `op` zz') x;  // transitivity, (xz)z' = x(zz') = x, (xz)z'=x
  trans_lemma eq x (xz `op` z') (yz `op` z');  // transitivity, x = (xz)z' = (yz)z'
  associative_operation_lemma eq op y z z';    // assoc again, (yz)z' = y(zz') 
  neutral_lemma op eq zz' y;                   // neutral again, y(zz')=y.
  ()                                           // the rest is left as an exercise for Z3

  
let producing_neutral_means_inverses (#a:Type) 
                                     (eq: equivalence_relation a) 
                                     (op: binary_op a{is_associative op eq /\ equivalence_wrt_condition op eq}) 
                                     (inv: inverse_op_for op eq) 
                                     (x y: a)
  : Lemma (requires is_neutral_of (x `op` y) op eq) 
          (ensures inv x `eq` y) = 
  reveal_opaque (`%is_neutral_of) (is_neutral_of #a); 
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  inverse_operation_lemma op eq inv y;
  inverse_operation_lemma op eq inv x;
  assert (is_neutral_of (inv y `op` y) op eq);
  // assert (is_neutral_of (x `op` y) op eq);
  neutral_is_unique op eq  (inv y `op` y) (x `op` y);
  group_operation_lemma eq op inv (inv y) x y;
  // assert (inv y `eq` x);
  equivalence_wrt_operation_lemma #a #op eq (inv y) x y;
  equivalence_wrt_operation_lemma #a #op eq (y `op` inv y) (y `op` x) (inv x);  
  // assert (((y `op` inv y) `op` inv x) `eq` ((y `op` x) `op` (inv x)));
  // assert (is_neutral_of (y `op` inv y) op eq);
  neutral_lemma op eq (y `op` inv y) (inv x);
  // assert ((inv x) `eq` ((y `op` x) `op` (inv x)));
  associative_operation_lemma eq op y x (inv x);
  // assert ((inv x) `eq` (y `op` (x `op` inv x)));
  neutral_lemma op eq (x `op` inv x) y;
  trans_lemma eq (inv x) (y `op` (x `op` inv x)) y;
  // assert (inv x `eq` y);
  // assert_spinoff (inv x `eq` y == true);
  () 

let equivalence_lemma_from_implications (#a:Type) (p) (q)
                                        (to_right : (x:a)->(y:a)->Lemma (requires p x y) (ensures q x y))
                                        (to_left  : (x:a)->(y:a)->Lemma (requires q x y) (ensures p x y))
                                        (x:a) (y:a)
                                        : Lemma (p x y <==> q x y) = 
                                        (Classical.move_requires_2 to_right) x y;
                                        (Classical.move_requires_2 to_left) x y
   
let inverse_lemma_def (#a:Type) (eq: equivalence_relation a) (op: binary_op a{is_associative op eq /\ equivalence_wrt_condition op eq}) (inv: inverse_op_for op eq) (x y: a)
  : Lemma (is_neutral_of (x `op` y) op eq <==> inv x `eq` y) = 
  (FStar.Classical.move_requires_2 (inverses_produce_neutral eq op inv)) x y;
  (FStar.Classical.move_requires_2 (producing_neutral_means_inverses eq op inv)) x y;
  assert (is_neutral_of (op x y) op eq ==> inv x `eq` y);   
  ()  

/// We shall generally keep in mind that distributivity laws must be considered separately
/// If in future we consider K[x] with multiplication f(x)*g(x) defined as composition f(g(x)),
/// we will do well to remember that only one of the two distributivities holds there.
[@@"opaque_to_smt"]
let is_left_distributive (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) (eq: equivalence_relation a) =
  forall (x y z:a). (x `op_mul` (y `op_add` z)) `eq` ((x `op_mul` y) `op_add` (x `op_mul` z))
[@@"opaque_to_smt"]
let is_right_distributive (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) (eq: equivalence_relation a) =
  forall (x y z:a). ((x `op_add` y) `op_mul` z) `eq` ((x `op_mul` z) `op_add` (y `op_mul` z))
[@@"opaque_to_smt"]
let is_fully_distributive (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) (eq: equivalence_relation a) =
  forall (x y z:a). ((x `op_mul` (y `op_add` z)) `eq` ((x `op_mul` y) `op_add` (x `op_mul` z))) /\ (((x `op_add` y) `op_mul` z) `eq` ((x `op_mul` z) `op_add` (y `op_mul` z)))

let fully_distributive_is_both_left_and_right  (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) (eq: equivalence_relation a) 
  : Lemma (is_fully_distributive op_mul op_add eq <==> is_left_distributive op_mul op_add eq /\ is_right_distributive op_mul op_add eq)  
  = reveal_opaque (`%is_left_distributive) (is_left_distributive #a);  
    reveal_opaque (`%is_right_distributive) (is_right_distributive #a);
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a)

let left_distributivity_lemma (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) (eq: equivalence_relation a) (x y z: a)
  : Lemma (requires is_left_distributive op_mul op_add eq) (ensures (x `op_mul` (y `op_add` z)) `eq` ((x `op_mul` y) `op_add` (x `op_mul` z))) 
  = reveal_opaque (`%is_left_distributive) (is_left_distributive #a)

let right_distributivity_lemma (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) (eq: equivalence_relation a) (x y z: a)
  : Lemma (requires is_right_distributive op_mul op_add eq) (ensures ((x `op_add` y) `op_mul` z) `eq` ((x `op_mul` z) `op_add` (y `op_mul` z))) 
  = reveal_opaque (`%is_right_distributive) (is_right_distributive #a) 

/// Domain defining property (the alternative form is the Cancellation Law, (ax=bx ==> (x=0 \/ a=b)
[@@"opaque_to_smt"]
let has_no_zero_divisors (#a:Type) (zero:a) (op_mul: binary_op a) (eq: equivalence_relation a) =
  forall (x y:a). ((x `op_mul` y) `eq` zero) ==> (x `eq` zero) \/ (y `eq` zero)
/// For future reference, we difine what it means for divisor to divide dividend
[@@"opaque_to_smt"]
let is_divisor_of (#a:Type) (op_mul: binary_op a) (eq: equivalence_relation a) (divisor: a) (dividend: a) = 
  exists (quotient: a). (quotient `op_mul` divisor) `eq` dividend


/// We provide the two lemmas that ensure divides, second one purely to
/// demonstrate how one uses exists_intro. Usually you're fine with '= ()'.
let inst_divides (#a:Type) (op_mul: binary_op a) (eq: equivalence_relation a) (y: a) (x: a) (z:a{(z `op_mul` y) `eq` x})
  : Lemma (is_divisor_of op_mul eq y x) = reveal_opaque (`%is_divisor_of) (is_divisor_of #a) 
  
/// explicitly stated version showcases FStar.Classical.exists_intro
let inst_divides_2 (#a:Type) (op_mul: binary_op a) (eq: equivalence_relation a) (y: a) (x: a) (z:a{(z `op_mul` y) `eq` x})
  : Lemma (is_divisor_of op_mul eq y x) = 
  reveal_opaque (`%is_divisor_of) (is_divisor_of #a);
  FStar.Classical.exists_intro (fun z -> (z `op_mul` y) `eq` x) z

/// This will soon be used as we'll represent elements in form of x=(unit_part)*(normal_part)
/// where (unit_part) is a ring unit, and (normal_part) is, roughly speaking, (unit_part⁻¹ * x),
/// so that normal part would represent absolute value, monic polynomial, etc.
/// If you're curious as to where did these (not so often used!) notions came from,
/// see the book "Algorithms for Computer Algebra" by Geddes, Czapor, Labahn.
/// You'll find quite a lot of interesting notions there.
///
/// we denote the unit u, because the word `unit` is reserved in F*
/// Invertible elements in a ring are called units, and here's their defining condition
[@@"opaque_to_smt"]
let is_unit (#a: Type) (x: a) (op:binary_op a) (eq: equivalence_relation a) 
  = exists (y:a). (is_neutral_of (x `op` y) op eq /\ is_neutral_of (y `op` x) op eq)
  
/// We call the two elements associated if they divide each other
let are_associated (#a: Type) (p: a) (q: a) (op_mul: binary_op a) (eq: equivalence_relation a) = (is_divisor_of op_mul eq p q) /\ (is_divisor_of op_mul eq q p) 

/// We also define in advance the notions of irreducibles and primes
/// We don't tell one from the other in Z, but in general, they are not the same thing.
[@@"opaque_to_smt"]
let is_irreducible (#a: Type) (x: a) (op_mul: binary_op a) (eq: equivalence_relation a) = 
  (~(is_unit x op_mul eq)) /\
  (exists (neutral: a). is_neutral_of neutral op_mul eq) /\  
  (forall (p q: a). ((q `op_mul` p) `eq` x) ==> ( (are_associated p x op_mul eq) /\ (is_unit q op_mul eq)) 
                                      \/ ((are_associated q x op_mul eq) /\ (is_unit p op_mul eq)))
[@@"opaque_to_smt"]                                     
let is_prime (#a: Type) (p: a) (one: a) (op_mul: binary_op a) (eq: equivalence_relation a) = 
  (~(is_unit p op_mul eq)) /\ (forall (m n: a). (is_divisor_of op_mul eq p (m `op_mul` n)) ==> ((is_divisor_of op_mul eq p m) \/ (is_divisor_of op_mul eq p n)))

[@@"opaque_to_smt"]  
let respects_equivalence (#a:Type) (f: unary_op a) (eq: equivalence_relation a) = forall (x y:a). (x `eq` y) ==> (f x) `eq` (f y)

noeq type magma (#a: Type) = 
{
  op: binary_op a;
  eq: equivalence_wrt op;
  inv: (t:unary_op a{ respects_equivalence t eq });
  neutral: a
}
 
type semigroup (#a:Type)             = g: magma #a{is_associative g.op g.eq}
type commutative_magma (#a:Type)     = g: magma #a{is_commutative g.op g.eq}
type commutative_semigroup (#a:Type) = g: semigroup #a{is_commutative g.op g.eq}
type monoid (#a:Type)                = g: semigroup #a{is_neutral_of g.neutral g.op g.eq}
type commutative_monoid (#a:Type)    = g: monoid #a{is_commutative g.op g.eq}
type group (#a:Type)                 = g: monoid #a{is_inverse_operation_for g.inv g.op g.eq}
type commutative_group (#a:Type)     = g: group #a{is_commutative g.op g.eq}

let magma_eq_wrt_condition (#a:Type) (m: magma #a) : Lemma(equivalence_wrt_condition m.op m.eq) = ()

let absorber_never_equals_non_absorber (#a: Type) (op: binary_op a) (eq: equivalence_wrt op) 
  (x: absorber_of op eq) (y: non_absorber_of op eq) : Lemma (~(x `eq` y)) = 
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  if (x `eq` y) then absorber_equal_is_absorber op eq x y

unfold let is_absorber_of_magma (#a:Type) (z: a) (m: magma #a) = is_absorber_of z m.op m.eq

/// When I try to keep the rlimit at minimum, lemmas like this one sometimes help
let neutral_inverse_is_neutral (#a:Type) (g: group #a) : Lemma (g.neutral `g.eq` (g.inv g.neutral)) =  
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  reveal_opaque (`%is_transitive) (is_transitive #a);
  neutral_lemma g.op g.eq g.neutral (g.inv g.neutral);
  inverse_operation_lemma g.op g.eq g.inv g.neutral;
  neutral_is_unique g.op g.eq g.neutral (g.neutral `g.op` g.inv g.neutral)

let group_op_lemma (#a:Type) (g: group #a) (x y z:a) 
  : Lemma (requires (x `g.op` z) `g.eq` (y `g.op` z)) (ensures (x `g.eq` y)) 
  = group_operation_lemma g.eq g.op g.inv x y z


#push-options "--ifuel 1 --fuel 0 --z3rlimit 16"
let group_element_equality_means_zero_difference (#a:Type) (g: group #a) (x y: a) 
  : Lemma (x `g.eq` y <==> (x `g.op` g.inv y) `g.eq` g.neutral) = 
  inverse_operation_lemma g.op g.eq g.inv y;                   // is_neutral (y + -y), x + -y
  neutral_is_unique g.op g.eq  (g.op y (g.inv y)) g.neutral;   // (y + (-y) = 0
  if (x `g.eq` y) then (
    equivalence_wrt_operation_lemma g.eq x y (g.inv y);
    assert ((x `g.op` g.inv y) `g.eq` (y `g.op` g.inv y));
    trans_lemma g.eq (x `g.op` g.inv y) (y `g.op` g.inv y) g.neutral
  ) else (
    if ((x `g.op` g.inv y) `g.eq` g.neutral) then ( 
      trans_lemma g.eq (x `g.op` g.inv y) g.neutral (y `g.op` g.inv y);
      group_op_lemma  g x y (g.inv y)
    ) 
  )

let absorber_for_invertible_operation_is_nonsense (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) (inv: inverse_op_for op eq)
   (y: non_absorber_of op eq) (z:a) : Lemma (requires is_absorber_of z op eq) (ensures False) =   
    reveal_opaque (`%is_absorber_of) (is_absorber_of #a);  
    absorber_never_equals_non_absorber op eq z y;
    let z' = inv z in
    let zz' = op z z' in
    absorber_lemma op eq z z';
    inverse_operation_lemma op eq inv z;                  // zz' is the neutral element
    let yzz' = op y zz' in                                // I write "the absorber" here to underline its uniqueness
    absorber_lemma op eq z z';                        (** 1. By definition of absorber, zz' should be equal to z.      *)
    absorber_equal_is_absorber op eq z zz';
    absorber_lemma op eq zz' y;
    absorber_equal_is_absorber op eq z zz';           (** 2. Any element equal to an absorber is the absorber,         *)
                                                      (**    therefore, zz' is also the absorber, since zz' = z.       *)
    (* assert (is_neutral_of zz' op eq); *)           (** 3. By definition of inverse, zz' is the neutral element.     *)
    (* assert (yzz' `eq` y);             *)           (** 4. By definition of neutral element (zz'), yzz' = y          *)
                                                      (**    This assertion somehow slowed* down the prover a lot!     *)
    (* assert (yzz' `eq` zz');           *)           (** 5. But as zz' is the absorber, yzz' = zz'!                   *)
    absorber_equal_is_absorber op eq zz' yzz';        (** 6. Being equal to the absorber zz', yzz' is the absorber     *)
    neutral_lemma op eq zz' y;                        (** 7. But, as an equal of y, yzz' can't be an absorber!         *) 
    nonabsorber_equal_is_nonabsorber op eq y yzz';    (**    So, we got the contradiction here!                        *) 
//  assert (~(is_absorber_of yzz' op eq)); 
//  assert (is_absorber_of yzz' op eq);               (**    Deleting the last two asserts gave* 10x proof slowdown!   *)
// * The slowdowns were noticed BEFORE the introduction of opaques. 
//   With opaques, most stuff here passes the verification with 0/0/1 resource settings
    ()    

let group_has_no_absorbers (#a:Type) (g: group #a) (z:a) (y:non_absorber_of g.op g.eq) 
  : Lemma (~(is_absorber_of z g.op g.eq)) = 
  (Classical.move_requires (absorber_for_invertible_operation_is_nonsense g.op g.eq g.inv y)) z
 
/// In our pursuit of sanity, we only consider ring-like structures that are at least rigs,
/// with addition forming a commutative group, and multiplication forming a semigroup that
/// is fully (left and right) distributive over addition
/// 
/// Notice how, just like inverse group operation, the euclidean_norm field holds little meaning
/// until we get to Euclidean Domains, but we shall keep the record field in the base type
/// because there is no inheritance in F*. Unfortunately so, to say the least.

let nat_function_defined_on_non_absorbers (#a:Type) (op: binary_op a) (eq: equivalence_relation a) 
  = f: (a -> (option nat)) { forall (x:a). (f x)=None ==> is_absorber_of x op eq }

let nat_function_value (#a:Type) (op: binary_op a) (eq: equivalence_relation a) (f: nat_function_defined_on_non_absorbers op eq) (x: non_absorber_of op eq) : nat 
  = allow_inversion (option nat); Some?.v (f x)

[@@"opaque_to_smt"]
let has_no_absorber_divisors (#a:Type) (op: binary_op a) (eq: equivalence_relation a) = forall (x y: a). is_absorber_of (op x y) op eq <==> (is_absorber_of x op eq) \/ (is_absorber_of y op eq)

let domain_multiplication_law (#a:Type) (eq: equivalence_relation a) (mul: binary_op a{has_no_absorber_divisors mul eq}) (x y: a)
  : Lemma (~(is_absorber_of x mul eq) /\ ~(is_absorber_of y mul eq) <==> ~ (is_absorber_of (mul x y) mul eq)) =   
    reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #a)
 
let domain_multiplication_law_inv (#a:Type) (eq: equivalence_relation a) (mul: binary_op a{has_no_absorber_divisors mul eq}) (x y: a)
  : Lemma ((is_absorber_of x mul eq) \/ (is_absorber_of y mul eq) <==> (is_absorber_of (mul x y) mul eq)) = 
    reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #a) 
  
let euclidean_norm_property (#a:Type) (eq: equivalence_relation a) 
                                      (mul: binary_op a{has_no_absorber_divisors mul eq}) 
                                      (x y: non_absorber_of mul eq) 
                                      (f: nat_function_defined_on_non_absorbers mul eq) = 
  domain_multiplication_law eq mul x y;
  nat_function_value mul eq f (mul x y) >= nat_function_value mul eq f x 

[@@"opaque_to_smt"]
let euclidean_norm_forall_property (#a:Type) (eq: equivalence_relation a) 
                                   (mul: binary_op a{has_no_absorber_divisors mul eq}) 
                                   (f: nat_function_defined_on_non_absorbers mul eq)
  = forall (x y: non_absorber_of mul eq). euclidean_norm_property eq mul x y f

type norm_function (#a:Type) (eq: equivalence_relation a) (mul: binary_op a{has_no_absorber_divisors mul eq})
  = f: nat_function_defined_on_non_absorbers mul eq{ forall (x y: non_absorber_of mul eq). euclidean_norm_property eq mul x y f }

let euclidean_norm_main_lemma (#a: Type) (eq: equivalence_relation a) (mul: binary_op a{has_no_absorber_divisors mul eq}) (f: norm_function eq mul) (x y: non_absorber_of mul eq)
  : Lemma (Some?.v (reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #a); f (mul x y)) >= Some?.v (f x)) =
  assert (euclidean_norm_property eq mul x y f)
  
private let test (a:Type) (eq:equivalence_relation a) (mul: binary_op a{has_no_absorber_divisors mul eq}) (f:norm_function eq mul) : Lemma ( 
  forall (x y: non_absorber_of mul eq). Some?.v (reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #a); f (mul x y)) >= Some?.v (f x) ) = 
  reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #a);
  FStar.Classical.forall_intro_2 (euclidean_norm_main_lemma eq mul f)

unfold let eq_of (p: magma) = p.eq

[@@"opaque_to_smt"]
let yields_units (#a: Type) (f: a->a) (mul: binary_op a) (eq: equivalence_relation a) = 
  forall (x:a). is_unit (f x) mul eq

let yields_units_lemma (#a: Type) (mul: binary_op a) (eq: equivalence_relation a) (f: (a->a){yields_units f mul eq}) (x:a)
  : Lemma (is_unit (f x) mul eq) = reveal_opaque (`%yields_units) (yields_units #a)

let unary_is_distributive_over (#a: Type) (f: a->a) (op: binary_op a) (eq: equivalence_relation a) (x y: a)
 = (f (x `op` y)) `eq` ((f x) `op` (f y))

[@@"opaque_to_smt"]
let unary_distributes_over (#a: Type) (f: a->a) (op: binary_op a) (eq: equivalence_relation a) = 
  forall (x y: a). unary_is_distributive_over f op eq x y

[@@"opaque_to_smt"]
let unary_over_nonzeros_distributes_over (#a: Type) (f: a->a) (op: binary_op a) (eq: equivalence_relation a) = 
  forall (x y: non_absorber_of op eq). unary_is_distributive_over f op eq x y

let un_distr_l (#a: Type) (op: binary_op a) (eq: equivalence_relation a) (f: (t:(a->a){ unary_over_nonzeros_distributes_over t op eq})) (x y: non_absorber_of op eq)  : Lemma (unary_is_distributive_over f op eq x y) = reveal_opaque (`%unary_over_nonzeros_distributes_over) (unary_over_nonzeros_distributes_over #a) 

type units_of (#a: Type) (mul: binary_op a) (eq: equivalence_relation a) = x:a{is_unit x mul eq}

let is_unit_part_function (#a: Type) (#mul: binary_op a) (#eq: equivalence_wrt mul) (f: a -> units_of mul eq) = 
  is_idempotent f eq /\
  yields_units f mul eq /\
  respects_equivalence f eq /\
  unary_over_nonzeros_distributes_over f mul eq

type unit_part_function (#a: Type) (mul: binary_op a) (eq: equivalence_wrt mul) = f:(a -> units_of mul eq){ is_unit_part_function f }

let un_op_distr_lemma (#a:Type) (mul: binary_op a) (eq: equivalence_wrt mul) (f: unit_part_function mul eq)
  : Lemma (unary_over_nonzeros_distributes_over f mul eq) = ()

let un_op_distr_lemma_p (#a:Type) (mul: binary_op a) (eq: equivalence_wrt mul) (f: unit_part_function mul eq) (x y: non_absorber_of mul eq)
  : Lemma (unary_is_distributive_over f mul eq x y) = reveal_opaque (`%unary_over_nonzeros_distributes_over) (unary_over_nonzeros_distributes_over #a)

let is_unit_normal (#a:Type) (mul: binary_op a) (eq: equivalence_wrt mul) (unit_part_func: a -> a) (x:a) = is_neutral_of (unit_part_func x) mul eq

[@@"opaque_to_smt"]
let yields_unit_normals (#a:Type) (mul: binary_op a) (eq: equivalence_wrt mul) (unit_part_func: a -> a) (f: a -> a) =
  forall (x:a). is_unit_normal mul eq unit_part_func (f x)

let yields_unit_normals_lemma (#a:Type) (mul: binary_op a) (eq: equivalence_wrt mul) (unit_part_func: a -> a) (f: (a -> a){yields_unit_normals mul eq unit_part_func f}) (x:a)
  : Lemma (is_unit_normal mul eq unit_part_func (f x)) = reveal_opaque (`%yields_unit_normals) (yields_unit_normals #a)

type unit_normal_of (#a: Type) (mul: binary_op a) (eq: equivalence_wrt mul) (unit_part_func: a -> a) = x:a { is_unit_normal mul eq unit_part_func x }

let is_normal_part_function (#a:Type) (#mul: binary_op a) (#eq: equivalence_wrt mul) (unit_part_func: a -> a) (f: a -> unit_normal_of mul eq unit_part_func) = 
  is_idempotent f eq /\
  respects_equivalence f eq /\
  yields_unit_normals mul eq unit_part_func f /\
  unary_distributes_over f mul eq


type normal_part_function (#a: Type) (#mul: binary_op a) (#eq: equivalence_wrt mul) (unit_part_func: a -> a)
  = f:(a -> (unit_normal_of mul eq unit_part_func)){ is_normal_part_function unit_part_func f }

let unit_part_func_of_product_is_product_of_unit_parts (#a: Type) (#mul: binary_op a) (#eq: equivalence_wrt mul)
  (unit_part_func: unit_part_function mul eq) (x y: non_absorber_of mul eq) 
  : Lemma((unit_part_func (x `mul` y)) `eq` ((unit_part_func x) `mul` (unit_part_func y))) = 
  un_op_distr_lemma_p mul eq unit_part_func x y;
  ()

let product_of_unit_normals_is_normal (#a: Type) (#mul: binary_op a) (#eq: equivalence_wrt mul)
  (unit_part_func: unit_part_function mul eq)
  (x y: unit_normal_of mul eq unit_part_func)
  : Lemma 
    (requires ~(is_absorber_of x mul eq) /\ ~(is_absorber_of y mul eq))
    (ensures is_unit_normal mul eq unit_part_func (x `mul` y)) =
  let up x = unit_part_func x in
  un_op_distr_lemma_p mul eq unit_part_func x y;                    // up (x*y) = up(x) * up(y) 
  yields_units_lemma mul eq unit_part_func (x `mul` y);             // up (x*y) is unit
  neutral_lemma mul eq (unit_part_func x) (unit_part_func y);       // unit part of unit normal is 1
  neutral_equivalent_is_neutral mul eq (up y) (up x `mul` up y);   
  neutral_equivalent_is_neutral mul eq (up x `mul` up y) (up (mul x y))


type test_unit_part_func (#a: Type) (mul: binary_op a) (eq: equivalence_wrt mul) = unit_part_function mul eq
 
noeq type ring (#a: Type) = {
  addition: commutative_group #a;
  multiplication: (t: monoid #a {is_fully_distributive t.op addition.op t.eq /\ is_absorber_of addition.neutral t.op t.eq });
  eq: (t:equivalence_relation a{ equivalence_wrt_condition addition.op t /\ equivalence_wrt_condition multiplication.op t /\ t===addition.eq /\ t===multiplication.eq });
  unit_part_of: a -> units_of multiplication.op eq;
  normal_part_of: a -> unit_normal_of multiplication.op eq unit_part_of;
  euclidean_norm: nat_function_defined_on_non_absorbers multiplication.op eq 
} 
 
unfold let neg_of (#a:Type) (r: ring #a) (p:a) : (t:a{ t `r.eq` (r.addition.neutral `r.addition.op` (r.addition.inv p) )}) 
  =  
  reveal_opaque (`%is_symmetric) (is_symmetric #a) ;
  inverse_operation_lemma r.addition.op r.eq r.addition.inv p;
  inverse_lemma_def r.eq r.addition.op r.addition.inv p (r.addition.inv p);
  neutral_lemma r.addition.op r.eq  r.addition.neutral (r.addition.inv p);
  r.addition.inv p

unfold let minus_of (#a:Type) (r: ring #a) (x:a) (y:a) : (t:a{ t `r.eq` (x `r.addition.op` (r.addition.inv y) )}) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #a);
  x `r.addition.op` (neg_of r y)

let double_inverse_is_id (#a:Type) (op: binary_op a) (eq: equivalence_wrt op{is_associative op eq}) (inv: inverse_op_for op eq) (x: a) 
  : Lemma (inv (inv x) `eq` x /\ x `eq` inv (inv x)) =    
  inverse_operation_lemma op eq inv x;
  inverse_operation_lemma op eq inv (inv x);   
  neutral_is_unique op eq (x `op` inv x) (inv (inv x) `op` inv x);
  group_operation_lemma eq op inv x (inv (inv x)) (inv x);
  symm_lemma eq (inv (inv x)) x

let minus_minus_x_is_x (#a:Type) (r: ring #a) (x: a) : Lemma (neg_of r (neg_of r x) `r.eq` x /\ x `r.eq` (neg_of r (neg_of r x)))
  = double_inverse_is_id r.addition.op r.eq r.addition.inv x  

let x_eq_y_means_inv_x_eq_inv_y (#a:Type) (op: binary_op a) (eq: equivalence_wrt op{is_associative op eq}) (inv: inverse_op_for op eq) (x y:a)
  : Lemma (x `eq` y <==> inv x `eq` inv y) = 
  if (x `eq` y) then (
    let x' = inv x in
    let y' = inv y in
    inverse_operation_lemma op eq inv y;
    equivalence_wrt_operation_lemma eq x y x';
    equivalence_wrt_operation_lemma eq x y y';
    neutral_equivalent_is_neutral op eq (op y y') (op x y');
    assert (is_neutral_of (op x y') op eq);
    producing_neutral_means_inverses eq op inv x y';
    assert (inv x `eq` inv y)    
  ) else (
    if (inv x `eq` inv y) then (
      let x' = inv x in
      let y' = inv y in
      let x'' = (inv (inv x)) in
      let y'' = (inv (inv y)) in
      double_inverse_is_id op eq inv x;
      double_inverse_is_id op eq inv y; 
      assert (inv x' `eq` x);
      assert (inv y' `eq` y);
      inverse_operation_lemma op eq inv y'; 
      equivalence_wrt_operation_lemma eq x' y' x'';
      equivalence_wrt_operation_lemma eq x' y' y'';
      neutral_equivalent_is_neutral op eq (op y' y'') (op x' y'');
      assert (is_neutral_of (op x' y'') op eq);
      producing_neutral_means_inverses eq op inv x' y'';
      trans_lemma_4 eq x x'' y'' y
    )
  )
 
let ring_additive_inv_x_is_x_times_minus_one (#a:Type) (r: ring #a) (x: a)
  : Lemma ((r.addition.inv x) `r.eq` (r.multiplication.op x (r.addition.inv r.multiplication.neutral)) /\
           (r.multiplication.op x (r.addition.inv r.multiplication.neutral)) `r.eq` (r.addition.inv x)) = 
    reveal_opaque (`%is_symmetric) (is_symmetric #a); 
    reveal_opaque (`%is_transitive) (is_transitive #a); 
    reveal_opaque (`%equivalence_wrt_condition) (equivalence_wrt_condition #a); 
    reveal_opaque (`%is_left_distributive) (is_left_distributive #a); 
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a); 
    reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #a); 
    let eq = r.eq in
    let mul = r.multiplication.op in
    let add = r.addition.op in
    let inv = r.addition.inv in 
    let zero = r.addition.neutral in
    let one = r.multiplication.neutral in
    let ix = inv x in  
    assert (is_neutral_of (one `add` (inv one)) add eq);
    neutral_is_unique r.addition.op r.eq zero (one `add` (inv one));
//    assert (zero `eq` (one `add` (inv one)));
    equivalence_wrt_operation_lemma #a #mul eq zero (one `add` (inv one)) x;
//    assert (mul x (one `add` (inv one)) `eq` (mul x zero));
//    assert (mul x zero `eq` zero);
//    assert ((mul x (one `add` (inv one))) `eq` ((mul x one) `add` (mul x (inv one)))); 
    symm_lemma eq ((mul x one) `add` (mul x (inv one))) (mul x (one `add` (inv one)));
    //this one speeds up the process if uncommented
//    left_distributivity_lemma mul add eq (mul x one)
    assert (is_left_distributive mul add eq);
    left_distributivity_lemma mul add eq x one (inv one);
    assert (((mul x one) `add` (mul x (inv one))) `eq` (mul x (one `add` (inv one))));    
    //this one requires spinoff!!! for some reason...
    inverse_operation_lemma add r.eq inv one;
    assert (is_neutral_of (one `add` inv one) add r.eq);
    neutral_is_unique add r.eq zero (one `add` inv one);
    assert (eq (one `add` inv one) zero);
    absorber_equal_is_absorber mul r.eq zero (one `add` inv one);
    absorber_lemma mul r.eq (one `add` inv one) x;
    assert_spinoff (mul x (one `add` (inv one)) `eq` zero);       
    trans_lemma r.eq ((mul x one) `add` (mul x (inv one))) (mul x (one `add` (inv one))) zero;
    assert (((mul x one) `add` (mul x (inv one))) `eq` zero);
    assert (is_neutral_of zero add eq);
    neutral_equivalent_is_neutral add eq zero ((mul x one) `add` (mul x (inv one)));
    assert (is_neutral_of ((mul x one) `add` (mul x (inv one))) add eq);
    producing_neutral_means_inverses eq add inv (mul x one) (mul x (inv one));
    assert (eq (inv (mul x one)) (mul x (inv one)));
    assert (is_neutral_of one mul eq);
    neutral_lemma mul eq one x;
    assert (mul x one `eq` x);    
    x_eq_y_means_inv_x_eq_inv_y add eq inv (mul x one) x;
    assert (inv (mul x one) `eq` (inv x));
    trans_lemma eq (inv x) (inv (mul x one)) (mul x (inv one))

let equal_elements_means_equal_inverses (#a:Type) (r: ring #a) (x y:a) 
  : Lemma ((r.eq x y == (r.addition.inv x `r.eq` r.addition.inv y)) /\ (r.eq x y == (r.addition.inv y `r.eq` r.addition.inv x))) =   
          reveal_opaque (`%is_symmetric) (is_symmetric #a); 
          reveal_opaque (`%is_reflexive) (is_reflexive #a);     
          x_eq_y_means_inv_x_eq_inv_y r.addition.op r.eq r.addition.inv x y 
 
let inv_switch_lemma (#a:Type) (r: ring #a) (x y:a) : Lemma (x `r.eq` (r.addition.inv y) <==> (r.addition.inv x) `r.eq` y) =   
  if (x `r.eq` r.addition.inv y) then (
    equal_elements_means_equal_inverses r x (r.addition.inv y);
    minus_minus_x_is_x r y;
    trans_lemma r.eq (r.addition.inv x) (r.addition.inv (r.addition.inv y)) y
  )
  else if (r.addition.inv x `r.eq` y) then (
    equal_elements_means_equal_inverses r (r.addition.inv x) y;
    minus_minus_x_is_x r x;    
    trans_lemma r.eq x (r.addition.inv (r.addition.inv x)) (r.addition.inv y)
  ) 

let ring_additive_inverse_is_unique (#a:Type) (r:ring #a) (x y: a) 
  : Lemma (requires x `r.eq` y \/ y `r.eq` x) 
          (ensures r.addition.inv x `r.eq` r.addition.inv y /\ r.addition.inv y `r.eq` r.addition.inv x) 
  = reveal_opaque (`%is_symmetric) (is_symmetric #a);   
    equal_elements_means_equal_inverses r x y


/// Make this fully symmetric with the previous lemma, if you want an exercise :)
let ring_additive_inv_x_is_minus_one_times_x (#a:Type) (r: ring #a) (x: a)
  : Lemma ((r.addition.inv x) `r.eq` (r.multiplication.op (r.addition.inv r.multiplication.neutral) x)) = 
    reveal_opaque (`%is_symmetric) (is_symmetric #a); 
    reveal_opaque (`%is_transitive) (is_transitive #a); 
    reveal_opaque (`%is_right_distributive) (is_right_distributive #a); 
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a); 
    reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #a); 
    let eq = r.eq in
    let mul = r.multiplication.op in
    let add = r.addition.op in
    let inv = r.addition.inv in 
    let zero = r.addition.neutral in
    let one = r.multiplication.neutral in
    let ix = inv x in  
    assert (is_neutral_of (inv one `add` one) add eq);
    neutral_is_unique r.addition.op r.eq zero (inv one `add` one);
    equivalence_wrt_operation_lemma #a #mul eq zero (inv one `add` one) x;
    absorber_equal_is_absorber mul eq zero (inv one `add` one);
//    assert (mul (inv one `add` one) x `eq` (mul (inv one) x `add` mul one x));
//    assert ( (mul (inv one) x `add` mul one x) `eq` (mul (inv one `add` one) x));
    right_distributivity_lemma mul add eq (inv one) one x;
//    assert (mul (inv one `add` one) x `eq` (mul (inv one) x `add` mul one x));
    symm_lemma eq (mul (inv one) x `add` mul one x) (mul (inv one `add` one) x);
    absorber_lemma mul eq (inv one `add` one) x;        
    trans_lemma eq (mul (inv one) x `add` mul one x) (mul (inv one `add` one) x) zero;
//  assert ((mul (inv one) x `add` mul one x) `eq` zero);
    neutral_equivalent_is_neutral add eq zero (mul (inv one) x `add` mul one x);
    producing_neutral_means_inverses eq add inv (mul (inv one) x) (mul one x);
//    assert (inv (mul (inv one) x) `eq` (mul one x));
    inv_switch_lemma r (mul (inv one) x) (mul one x);
//    assert (mul (inv one) x `eq` (inv (mul one x)));
    symm_lemma eq (inv (mul one x)) (mul (inv one) x);    
//    assert (mul one x `eq` x);
    neutral_lemma mul eq one x;
    ring_additive_inverse_is_unique r x (mul one x);
//    assert (inv x `eq` inv (mul one x));
//    assert (inv (mul one x) `eq` mul (inv one) x);
    trans_lemma eq (inv x) (inv (mul one x)) (mul (inv one) x);    
  ()
    

let ring_times_minus_one_is_commutative (#a:Type) (r: ring #a) (x:a) 
  : Lemma ( 
            (x `r.multiplication.op` r.addition.inv r.multiplication.neutral) `r.eq` (r.addition.inv r.multiplication.neutral `r.multiplication.op` x) &&
            (x `r.multiplication.op` r.addition.inv r.multiplication.neutral) `r.eq` (r.addition.inv x) &&
            (r.addition.inv x) `r.eq` (x `r.multiplication.op` r.addition.inv r.multiplication.neutral) &&
            (r.addition.inv x) `r.eq` (r.addition.inv r.multiplication.neutral `r.multiplication.op` x) &&
            (r.addition.inv r.multiplication.neutral `r.multiplication.op` x) `r.eq` (x `r.multiplication.op` r.addition.inv r.multiplication.neutral) &&
            (r.addition.inv r.multiplication.neutral `r.multiplication.op` x) `r.eq` (r.addition.inv x)
          ) = 
  reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  reveal_opaque (`%is_transitive) (is_transitive #a);  
  ring_additive_inv_x_is_minus_one_times_x r x;
  ring_additive_inv_x_is_x_times_minus_one r x

let ring_x_times_minus_y_is_minus_xy (#a:Type) (r:ring #a) (x y: a) : Lemma ((x `r.multiplication.op` r.addition.inv y) `r.eq` (r.addition.inv (x `r.multiplication.op` y))) =   
  ring_additive_inv_x_is_x_times_minus_one r y;
  let eq = r.eq in
  let mul = r.multiplication.op in
  let add = r.addition.op in
  let neg = r.addition.inv in 
  let zero = r.addition.neutral in
  let one = r.multiplication.neutral in
  ring_additive_inv_x_is_x_times_minus_one r y; // -y = (y * -1)
  equivalence_wrt_operation_lemma #a #mul eq (neg y) (y `mul` neg one) x; // x*(-y) = x*(y*(-1))
  associative_operation_lemma eq mul x y (neg one);                       // x*(y*(-1)) = (x*y)*(-1)
  ring_additive_inv_x_is_x_times_minus_one r (x `mul` y);                 // (xy)*(-1) = -(xy)
  trans_lemma eq (x `mul` neg y) (x `mul` (y `mul` neg one)) ((x `mul` y) `mul` neg one);
  trans_lemma eq (x `mul` neg y) ((x `mul` y) `mul` neg one) (neg (x `mul` y));  
  ()

let ring_x_times_minus_y_is_minus_x_times_y (#a:Type) (r:ring #a) (x y: a) : Lemma (
    (x `r.multiplication.op` r.addition.inv y) `r.eq` (r.addition.inv x `r.multiplication.op` y) &&
    (r.addition.inv x `r.multiplication.op` y) `r.eq` (x `r.multiplication.op` r.addition.inv y) 
  ) =   
  let eq = r.eq in
  let mul = r.multiplication.op in
  let add = r.addition.op in
  let neg = r.addition.inv in 
  let zero = r.addition.neutral in
  let one = r.multiplication.neutral in
  ring_additive_inv_x_is_minus_one_times_x r y;  
  associative_operation_lemma eq mul x (neg one) y;
  assert (neg y `eq` mul (neg one) y);
  equivalence_wrt_operation_lemma #a #mul eq (neg y) (mul (neg one) y) x;
  assert ((x `mul` neg y) `eq` (x `mul` (neg one `mul` y)));
  associative_operation_lemma eq mul x (neg one) y;
  assert ((x `mul` (neg one `mul` y)) `eq` ((x `mul` neg one) `mul` y));
  trans_lemma eq (x `mul` neg y) (x `mul` (neg one `mul` y)) ((x `mul` neg one) `mul` y);
  assert (eq (x `mul` neg y) ((x `mul` neg one) `mul` y));
  ring_additive_inv_x_is_x_times_minus_one r x;
  assert ((x `mul` neg one) `eq` neg x);
  equivalence_wrt_operation_lemma #a #mul eq (x `mul` neg one) (neg x) y;
  assert ( ((x `mul` neg one) `mul` y) `eq` (neg x `mul` y) );
  trans_lemma eq (x `mul` neg y) ((x `mul` neg one) `mul` y) (neg x `mul` y)

let ring_product_with_minus_lemma (#a:Type) (r:ring #a) (x y: a) 
  : Lemma (
           (x `r.multiplication.op` r.addition.inv y) `r.eq` (r.addition.inv x `r.multiplication.op` y) /\
           (x `r.multiplication.op` r.addition.inv y) `r.eq` (r.addition.inv (x `r.multiplication.op` y)) 
          ) = 
  ring_x_times_minus_y_is_minus_x_times_y r x y; 
  ring_x_times_minus_y_is_minus_xy r x y 

let neg_distr_lemma (#a:Type) (r: ring #a) (x y z: a) 
  : Lemma ((x `r.multiplication.op` (y `r.addition.op` r.addition.inv z)) `r.eq` ((r.multiplication.op x y) `r.addition.op` (r.addition.inv (r.multiplication.op x z)))) =  
  let eq = r.eq in
  let mul = r.multiplication.op in
  let add = r.addition.op in
  let neg = r.addition.inv in 
  let zero = r.addition.neutral in
  let one = r.multiplication.neutral in
  reveal_opaque (`%is_left_distributive) (is_left_distributive #a); 
  reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a); 
  left_distributivity_lemma mul add eq x y (neg z);
  ring_x_times_minus_y_is_minus_xy r x z;
  assert ((x `mul` neg z) `eq` neg (x `mul` z)); 
  equivalence_wrt_operation_lemma #a #add eq (x `mul` neg z) (neg (x `mul` z)) (x `mul` y);
  assert (((x `mul` y) `add` (x `mul` neg z)) `eq` ((x `mul` y) `add` (neg (x `mul` z))));
  trans_lemma eq (x `mul` (y `add` neg z)) ((x `mul` y) `add` (x `mul` neg z))  ((x `mul` y) `add` (neg (x `mul` z)));
  ()

let neut_add_lemma (#a: Type) (r: ring #a) : Lemma (is_neutral_of r.addition.neutral r.addition.op r.eq) = () 
let neut_lemma (#a: Type) (r: ring #a) : Lemma (is_neutral_of r.multiplication.neutral r.multiplication.op r.eq) = ()
let add_eq_of (#a:Type) (r: ring #a) : equivalence_wrt r.addition.op = r.eq

let mul_neutral_lemma (#a: Type) (r: ring #a) (x: a{is_neutral_of x r.multiplication.op r.eq})
  : Lemma (r.eq x r.multiplication.neutral) =
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  neutral_is_unique r.multiplication.op r.eq r.multiplication.neutral x

unfold let is_zero_of (#a: Type) (r: ring #a) (x: a) = is_absorber_of x r.multiplication.op r.eq

let two_zeros_are_equal (#a:Type) (r: ring #a) (x y: (t:a{r.eq t r.addition.neutral})) 
  : Lemma (x `r.eq` y) =  
  neutral_equivalent_is_neutral r.addition.op r.eq r.addition.neutral x; 
  neutral_equivalent_is_neutral r.addition.op r.eq r.addition.neutral y;
  neutral_is_unique r.addition.op r.eq x y

let eq_symmetry (#a:Type) (eq: equivalence_relation a) (x y: a) 
  : Lemma (requires (x `eq` y \/ y `eq` x)) (ensures (x `eq` y /\ y `eq` x)) = reveal_opaque (`%is_symmetric) (is_symmetric #a)
 
let zero_is_equal_to_add_neutral_p (#a:Type) (r: ring #a) (z: a)
  : Lemma (is_zero_of r z <==> r.eq z r.addition.neutral) = 
  if (r.eq z r.addition.neutral) 
  then absorber_equal_is_absorber r.multiplication.op r.eq r.addition.neutral z  
  else FStar.Classical.move_requires_2 (absorber_is_unique r.multiplication.op r.eq) z r.addition.neutral  
   
let zero_is_equal_to_add_neutral (#a:Type) (r: ring #a) : Lemma (forall (x:a). is_zero_of r x <==> r.eq x r.addition.neutral) 
  = FStar.Classical.forall_intro (zero_is_equal_to_add_neutral_p r)

let nonzero_is_not_equal_to_add_neutral (#a:Type) (r: ring #a) 
  : Lemma (forall (x:a). ~(is_zero_of r x) <==> ~(r.eq x r.addition.neutral)) = zero_is_equal_to_add_neutral r
 
let nonzero_is_not_equal_to_add_neutral_p (#a:Type) (r: ring #a) (z: a)
  : Lemma (~(is_absorber_of z r.multiplication.op r.eq) <==> ~(r.eq z r.addition.neutral)) = zero_is_equal_to_add_neutral r

type domain (#a: Type) = r:ring #a { has_no_absorber_divisors r.multiplication.op r.eq }

let domain_mul_absorber_lemma (#a:Type) (dom: domain #a) (x y:a) 
  : Lemma (is_absorber_of (dom.multiplication.op x y) dom.multiplication.op dom.eq <==> 
           is_absorber_of x dom.multiplication.op dom.eq \/ is_absorber_of y dom.multiplication.op dom.eq) = 
   domain_multiplication_law_inv dom.eq dom.multiplication.op x y

private let domain_lemma_1 (#a:Type) (dom: domain #a) (p q:a) 
  : Lemma (requires is_absorber_of p dom.multiplication.op dom.eq \/ is_absorber_of p dom.multiplication.op dom.eq)
          (ensures is_absorber_of (dom.multiplication.op p q) dom.multiplication.op dom.eq) = 
  reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #a) 
                                               
private let domain_lemma_2 (#a:Type) (dom: domain #a) (x y:a) 
  : Lemma (requires is_absorber_of (dom.multiplication.op x y) dom.multiplication.op dom.eq) 
          (ensures is_absorber_of x dom.multiplication.op dom.eq \/ is_absorber_of y dom.multiplication.op dom.eq) = 
  domain_mul_absorber_lemma dom x y
 
let domain_zero_product_means_zero_factor (#a:Type) (dom: domain #a) (p q: a) 
  : Lemma (requires (p `dom.multiplication.op` q) `dom.eq` dom.addition.neutral)
          (ensures (p `dom.eq` dom.addition.neutral \/ q `dom.eq` dom.addition.neutral)) =     
  neutral_equivalent_is_neutral dom.addition.op dom.eq dom.addition.neutral (p `dom.multiplication.op` q);
  absorber_equal_is_absorber dom.multiplication.op dom.eq dom.addition.neutral (p `dom.multiplication.op` q); 
  domain_multiplication_law_inv dom.eq dom.multiplication.op p q;
  zero_is_equal_to_add_neutral dom
 
let domain_characterizing_lemma (#a:Type) (dom: domain #a) (p q: a) 
  : Lemma ((p `dom.multiplication.op` q) `dom.eq` dom.addition.neutral <==>
           (p `dom.eq` dom.addition.neutral \/ q `dom.eq` dom.addition.neutral)) =   
  reveal_opaque (`%is_transitive) (is_transitive #a);     
  FStar.Classical.move_requires_2 (domain_zero_product_means_zero_factor dom) p q;
  if (dom.eq p dom.addition.neutral) then (
    absorber_equal_is_absorber dom.multiplication.op dom.eq dom.addition.neutral p;
    absorber_lemma dom.multiplication.op dom.eq p q;
    assert (p `dom.multiplication.op` q `dom.eq` dom.addition.neutral)
  ) else if (dom.eq q dom.addition.neutral) then (
    absorber_equal_is_absorber dom.multiplication.op dom.eq dom.addition.neutral q;
    absorber_lemma dom.multiplication.op dom.eq q p;
    assert (p `dom.multiplication.op` q `dom.eq` dom.addition.neutral)
  )  
  
private let domain_law_from_pq_eq_pr (#a:Type) (d: domain #a) (p q r: a)
  : Lemma (requires d.multiplication.op p q `d.eq` d.multiplication.op p r) 
          (ensures p `d.eq` d.addition.neutral \/ (q `d.eq` r)) =  
  reveal_opaque (`%is_transitive) (is_transitive #a);     
  reveal_opaque (`%is_symmetric) (is_symmetric #a);     
  let mul = d.multiplication.op in
  let eq = d.eq in
  let add = d.addition.op in
  let neg = d.addition.inv in
  let zero = d.addition.neutral in
  equal_elements_means_equal_inverses d (p `mul` q) (p `mul` r);
  inverses_produce_neutral eq add neg (p `mul` q) (neg (p `mul` r));
  assert (is_neutral_of ((p `mul` q) `add` (neg (p `mul` r))) add eq);
  neutral_is_unique add eq ((p `mul` q) `add` (neg (p `mul` r))) zero;
  
  ring_x_times_minus_y_is_minus_xy d p r;
  symm_lemma eq (mul p (neg r)) (neg (mul p r));
  equivalence_wrt_operation_lemma #a #add eq (neg (mul p r)) (mul p (neg r)) (mul p q);
  assert ((mul p q `add` neg (mul p r)) `eq` (mul p q `add` mul p (neg r)));
  fully_distributive_is_both_left_and_right mul add eq;
  left_distributivity_lemma mul add eq p q (neg r);
  assert (eq zero ((p `mul` q) `add` (neg (p `mul` r))));  
  trans_lemma_4 eq zero ((p `mul` q) `add` (neg (p `mul` r))) (mul p q `add` mul p (neg r)) (mul p (add q (neg r)));
  domain_characterizing_lemma d p (add q (neg r));
   if (p `d.eq` d.addition.neutral) then () else (
   if (d.addition.op q (d.addition.inv r) `d.eq` d.addition.neutral) then (
     group_element_equality_means_zero_difference d.addition q r;

     ()
   ) else ()
  )
 
  
type commutative_ring (#a: Type) = r:ring #a { is_commutative r.multiplication.op r.eq }

/// I'm not 100% sure, but somehow I think that PERHAPS unit/normal part functions
/// are safe to expect to be defined over any integral domain. 
/// 
/// The special case of euclidean domains, which allows for reduced fractions, will later be handled
/// differently, and all arithmetics will also account for the gcd/eea availability.
type integral_domain (#a: Type) = r:domain #a 
{ 
  is_commutative r.multiplication.op r.eq /\
  is_unit_part_function r.unit_part_of /\
  is_normal_part_function r.unit_part_of r.normal_part_of    
}

type euclidean_domain (#a:Type) = r:integral_domain #a 
{ 
  euclidean_norm_forall_property r.eq r.multiplication.op r.euclidean_norm
}
 
