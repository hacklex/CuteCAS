module AlgebraTypes
 
#push-options "--ifuel 0 --fuel 0 --z3rlimit 1"

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
 
let trans_lemma (#a:Type) (eq: equivalence_relation a) (x y z:a)
  : Lemma (requires ((x `eq` y) \/ (y `eq` x)) /\ 
                    ((y `eq` z) \/ (z `eq` y)))  
          (ensures x `eq` z && z `eq` x)   
  = reveal_opaque (`%is_transitive) (is_transitive #a);
    reveal_opaque (`%is_symmetric) (is_symmetric #a)

let trans_lemma_4 (#a:Type) (eq: equivalence_relation a) (x:a)
                                                         (y:a{eq x y \/ eq y x})
                                                         (z:a{eq y z \/ eq z y})
                                                         (w:a{eq z w \/ eq w z})
  : Lemma (x `eq` w /\ w `eq` x) = reveal_opaque (`%is_transitive) (is_transitive #a);
                                  reveal_opaque (`%is_symmetric) (is_symmetric #a)

let trans_lemma_5 (#a:Type) (eq: equivalence_relation a) (x:a)
                                                         (y:a{eq x y \/ eq y x})
                                                         (z:a{eq y z \/ eq z y})
                                                         (w:a{eq z w \/ eq w z})
                                                         (v:a{eq w v \/ eq v w})
  : Lemma (x `eq` v /\ v `eq` x) = reveal_opaque (`%is_transitive) (is_transitive #a);
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

/// Back in the times of old, when there were no opaques, some lemmas failed without this.
/// This artifact of the ancient times isn't supposed to be here. To be deleted asap.
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
  
let absorber_equal_is_absorber (#a:Type) (op:binary_op a) (eq: equivalence_wrt op) (z1 z2: a) 
  : Lemma (requires is_absorber_of z1 op eq /\ (eq z1 z2 \/ eq z2 z1)) 
          (ensures is_absorber_of z2 op eq) =             
  let absorber_eq_is_abs (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) (z1: absorber_of op eq) (z2: a{z2 `eq` z1}) (t: a) 
    : Lemma (t `op` z2 `eq` z2 /\ z2 `op` t `eq` z2) =   
    reveal_opaque (`%is_absorber_of) (is_absorber_of #a);
    reveal_opaque (`%is_transitive) (is_transitive #a); 
    reveal_opaque (`%is_symmetric) (is_symmetric #a); 
    equivalence_wrt_operation_lemma eq z1 z2 t in
  reveal_opaque (`%is_symmetric) (is_symmetric #a);
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a);
  FStar.Classical.forall_intro (absorber_eq_is_abs op eq z1 z2)
  
let absorber_lemma (#a:Type) (op:binary_op a) (eq: equivalence_wrt op) (z: a) (x:a)
  : Lemma (requires is_absorber_of z op eq) (ensures (z `op` x) `eq` z /\ (x `op` z) `eq` z /\ is_absorber_of (op x z) op eq /\ is_absorber_of (op z x) op eq) = 
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a);  
  absorber_equal_is_absorber op eq z (op x z);
  absorber_equal_is_absorber op eq z (op z x)

/// Proving that in any magma, there may not be 2 distinct absorbers, is left as an exercise
/// to both Z3 and the reader. And Z3 is doing fine on that count, just saying.
let absorber_is_unique (#a:Type) (op: binary_op a) (eq: equivalence_relation a) (z1 z2: a) 
  : Lemma (requires is_absorber_of z1 op eq /\ is_absorber_of z2 op eq) 
          (ensures eq z1 z2 /\ eq z2 z1) = 
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a) 

/// This automatically propagates equality between all known observers
let absorber_is_unique_smt_lemma (#a:Type) (op: binary_op a) (eq: equivalence_relation a) (z1 z2: a)
  : Lemma (requires is_absorber_of z1 op eq /\ is_absorber_of z2 op eq) 
          (ensures eq z1 z2 /\ eq z2 z1)  
          [SMTPat(is_absorber_of z1 op eq /\ is_absorber_of z2 op eq)]
          = absorber_is_unique op eq z1 z2
   
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
          (ensures is_neutral_of (x `op` y) op eq /\ is_neutral_of (y `op` x) op eq) =
    equivalence_wrt_operation_lemma #a #op eq (inv x) y x;
    reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #a);
    neutral_equivalent_is_neutral op eq (x `op` inv x) (x `op` y);
    neutral_equivalent_is_neutral op eq (inv x `op` x) (y `op` x)

private let group_operation_lemma_left (#a:Type) (eq: equivalence_relation a) 
                             (op: binary_op a{is_associative op eq /\ equivalence_wrt_condition op eq}) 
                             (inv: inverse_op_for op eq) (x y z:a) 
  : Lemma (requires (x `op` z) `eq` (y `op` z)) (ensures x `eq` y /\ y `eq` x) =    
  reveal_opaque (`%is_transitive) (is_transitive #a);
  reveal_opaque (`%is_associative) (is_associative #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a);
  let eq_wrt_lemma = equivalence_wrt_operation_lemma #a #op eq in
  let z'  = inv z in
  let op = op in
  let eq  = eq in
  let zz' = z `op` z' in
  let xz = x `op` z in                         // suppose zz'    = 1 (always possible in a group)
  let yz = y `op` z in                         // we have xz     = yz
  eq_wrt_lemma xz yz z';                       // then,   (xz)z' = (yz)z'
  // associativity lemmas are now redundant,
  // thanks to reveal_opaque 
  // associative_operation_lemma eq op x z z'; // or,     x(zz') = (yz)z'
  inverse_operation_lemma op eq inv z;         // as we know, zz'= 1
  neutral_lemma op eq zz' x;                   // zz'=1,  (zz')x = x
  trans_lemma eq (xz `op` z') (x `op` zz') x;  // transitivity, (xz)z' = x(zz') = x, (xz)z'=x
  trans_lemma eq x (xz `op` z') (yz `op` z');  // transitivity, x = (xz)z' = (yz)z'
  // associative_operation_lemma eq op y z z'; // assoc again, (yz)z' = y(zz') 
  neutral_lemma op eq zz' y;                   // neutral again, y(zz')=y.
  ()                                           // the rest is left as an exercise for Z3


private let group_operation_lemma_right (#a:Type) (eq: equivalence_relation a)
                                (op: binary_op a{is_associative op eq /\ equivalence_wrt_condition op eq})
                                (inv: inverse_op_for op eq) (x y z:a)
  : Lemma (requires (z `op` x) `eq` (z `op` y)) (ensures x `eq` y /\ y `eq` x) =
  reveal_opaque (`%is_transitive) (is_transitive #a); // we're going to need the transitivity of ==
  reveal_opaque (`%is_associative) (is_associative #a); // we're going to need the transitivity of ==
  reveal_opaque (`%is_symmetric) (is_symmetric #a);
  let eq_wrt_lemma = equivalence_wrt_operation_lemma #a #op eq in
  let z' = inv z in
  let zx = op z x in
  let zy = op z y in
  let z'z = op z' z in
  eq_wrt_lemma zx zy z';
  inverse_operation_lemma op eq inv z;
  neutral_lemma op eq z'z x;
  trans_lemma eq (z' `op` zx) (z'z `op` x) x;
  trans_lemma eq x (z' `op` zx) (z' `op` zy);
  neutral_lemma op eq z'z y
 // trans_lemma_4 eq x (z' `op` zy) (z'z `op` y) y

let group_operation_lemma (#a:Type) (eq: equivalence_relation a)
                                    (op: binary_op a{is_associative op eq /\ equivalence_wrt_condition op eq}) 
                                    (inv: inverse_op_for op eq) 
                                    (x y z: a)
  : Lemma (requires ((z `op` x) `eq` (z `op` y) \/ (x `op` z) `eq` (y `op` z))) 
          (ensures x `eq` y /\ y `eq` x) = 
  if ((z `op` x) `eq` (z `op` y)) 
  then group_operation_lemma_right eq op inv x y z
  else group_operation_lemma_left eq op inv x y z

  
let producing_neutral_means_inverses (#a:Type) 
                                     (eq: equivalence_relation a) 
                                     (op: binary_op a{is_associative op eq /\ equivalence_wrt_condition op eq}) 
                                     (inv: inverse_op_for op eq) 
                                     (x y: a)
  : Lemma (requires is_neutral_of (x `op` y) op eq) 
          (ensures inv x `eq` y /\ x `eq` inv y) = 
  reveal_opaque (`%equivalence_wrt_condition) (equivalence_wrt_condition #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  reveal_opaque (`%is_associative) (is_associative #a);
  inverse_operation_lemma op eq inv y;
  inverse_operation_lemma op eq inv x;
  neutral_is_unique op eq  (inv y `op` y) (x `op` y);
  group_operation_lemma eq op inv (inv y) x y;
  equivalence_wrt_operation_lemma #a #op eq (y `op` inv y) (y `op` x) (inv x);  
  neutral_lemma op eq (y `op` inv y) (inv x);  
  equivalence_wrt_operation_lemma #a #op eq ((y `op` x) `op` inv x) (y `op` (x `op` inv x)) (inv x);
  neutral_lemma op eq (x `op` inv x) y;
  // trans_lemma eq (inv x) (y `op` (x `op` inv x)) y;
  () 

let equivalence_lemma_from_implications (#a:Type) (p) (q)
                                        (to_right : (x:a)->(y:a)->Lemma (requires p x y) (ensures q x y))
                                        (to_left  : (x:a)->(y:a)->Lemma (requires q x y) (ensures p x y))
                                        (x:a) (y:a)
                                        : Lemma (p x y <==> q x y) = 
                                        (Classical.move_requires_2 to_right) x y;
                                        (Classical.move_requires_2 to_left) x y

let inverse_element_defining_lemma (#a:Type) (eq: equivalence_relation a) (op: binary_op a{is_associative op eq /\ equivalence_wrt_condition op eq}) (inv: inverse_op_for op eq) (x y: a)
  : Lemma (
           (is_neutral_of (x `op` y) op eq <==> inv x `eq` y) /\
           (is_neutral_of (x `op` y) op eq <==> inv y `eq` x) /\
           (is_neutral_of (y `op` x) op eq <==> inv x `eq` y) /\
           (is_neutral_of (y `op` x) op eq <==> inv y `eq` x)
          ) = 
  (FStar.Classical.move_requires_2 (inverses_produce_neutral eq op inv)) x y;
  (FStar.Classical.move_requires_2 (producing_neutral_means_inverses eq op inv)) x y;
  (FStar.Classical.move_requires_2 (inverses_produce_neutral eq op inv)) y x;
  (FStar.Classical.move_requires_2 (producing_neutral_means_inverses eq op inv)) y x
 
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

type units_of (#a: Type) (mul: binary_op a) (eq: equivalence_relation a) = x:a{is_unit x mul eq}

/// This one is only needed for the lemma below to turn 12 lines of equality into just 4.
unfold private let eq_twoway (#a:Type) (eq: equivalence_relation a) (x y: a) = (x `eq` y) && (y `eq` x)

unfold private let multi_equality_5 (#a: Type) (eq: equivalence_relation a) (e1 e2 e3 e4 e5: a) = 
  e1 `eq` e2 && e1 `eq` e3 && e1 `eq` e4 && e1 `eq` e5 &&
  e2 `eq` e1 && e2 `eq` e3 && e2 `eq` e4 && e2 `eq` e5 &&
  e3 `eq` e1 && e3 `eq` e2 && e3 `eq` e4 && e3 `eq` e5 &&
  e4 `eq` e1 && e4 `eq` e2 && e4 `eq` e3 && e4 `eq` e5 &&
  e5 `eq` e1 && e5 `eq` e2 && e5 `eq` e3 && e5 `eq` e4 
  
/// Regular associativity lemma, straightforward and with minimal possible requirements.
let assoc_lemma3 (#a:Type) (eq: equivalence_relation a) (op: binary_op a{is_associative op eq}) (x y z: a) 
  : Lemma (((x `op` y) `op` z) `eq` (x `op` (y `op` z)) /\ (x `op` (y `op` z)) `eq` ((x `op` y) `op` z)) 
  = reveal_opaque (`%is_associative) (is_associative #a);
    reveal_opaque (`%is_symmetric) (is_symmetric #a)

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
 
/// This one is used to assert commutativity, works with both add and mul.
/// Used when revealing is_commutative opaque wastes too much rlimit.
let comm_lemma (#a:Type) (eq: equivalence_relation a) (op: binary_op a{is_commutative op eq}) (x y: a)
  : Lemma ( (x `op` y) `eq` (y `op` x) /\ (y `op` x) `eq` (x `op` y)) = 
    reveal_opaque (`%is_commutative) (is_commutative #a)
     
let bring_any_operand_forth (#a:Type) 
                  (eq: equivalence_relation a) 
                  (op: binary_op a { is_associative op eq /\ is_commutative op eq /\ equivalence_wrt_condition op eq })
                  (x y z w: a) : Lemma (
                    multi_equality_5 eq (x `op` y `op` z `op` w)
                                        (x `op` (y `op` (z `op` w))) 
                                        (y `op` (x `op` (z `op` w))) 
                                        (z `op` (x `op` (y `op` w)))
                                        (w `op` (x `op` (y `op` z)))) =   
  let bring_any_operand_forth_aux (#a: Type) 
                                    (eq: equivalence_relation a) 
                                    (op: binary_op a { is_associative op eq /\ is_commutative op eq /\ equivalence_wrt_condition op eq })
                                    (x y z w: a) : Lemma ((eq (x `op` y `op` z `op` w) (x `op` (y `op` (z `op` w)))) /\ 
                                                          (eq (x `op` y `op` z `op` w) (y `op` (x `op` (z `op` w)))) /\
                                                          (eq (x `op` y `op` z `op` w) (z `op` (x `op` (y `op` w)))) /\
                                                          (eq (x `op` y `op` z `op` w) (w `op` (x `op` (y `op` z))))) =                    
        reveal_opaque (`%is_associative) (is_associative #a);
        reveal_opaque (`%is_commutative) (is_commutative #a);
        reveal_opaque (`%is_transitive) (is_transitive #a);
        reveal_opaque (`%is_symmetric) (is_symmetric #a);
        reveal_opaque (`%equivalence_wrt_condition) (equivalence_wrt_condition #a);
        assoc_lemma4 eq op x y z w;
        assert (multi_equality_5 eq (x `op` (y `op` (z `op` w)))
                                 (x `op` y `op` z `op` w)
                                 (y `op` x `op` z `op` w)
                                 (z `op` x `op` y `op` w)
                                 (w `op` x `op` y `op` z));
        //these two, despite being the obvious final steps, slow down the prover when uncommented :)
        //assoc_lemma4 eq op y x z w; 
        //assoc_lemma4 eq op z x y w; 
        assoc_lemma4 eq op w x y z in
  bring_any_operand_forth_aux eq op x y z w;
  reveal_opaque (`%is_transitive) (is_transitive #a);
  reveal_opaque (`%is_symmetric) (is_symmetric #a)

let unit_product_is_unit (#a:Type) (mul: binary_op a) (eq: equivalence_wrt mul{is_associative mul eq}) (x y: units_of mul eq)  
  : Lemma (is_unit (mul x y) mul eq) = 
    reveal_opaque (`%is_symmetric) (is_symmetric #a);
    reveal_opaque (`%is_transitive) (is_transitive #a);
    reveal_opaque (`%is_reflexive) (is_reflexive #a);
    reveal_opaque (`%is_associative) (is_associative #a);
    reveal_opaque (`%is_unit) (is_unit #a);
    let op = mul in
    // assert(exists (y:a). (is_neutral_of (x `op` y) op eq /\ is_neutral_of (y `op` x) op eq));
    let x' = IndefiniteDescription.indefinite_description_ghost (units_of mul eq) (fun x' -> (is_neutral_of (x `op` x') op eq /\ is_neutral_of (x' `op` x) op eq)) in
    let y' = IndefiniteDescription.indefinite_description_ghost (units_of mul eq) (fun y' -> (is_neutral_of (y `op` y') op eq /\ is_neutral_of (y' `op` y) op eq)) in
    let inv = op y' x' in
    let full = op (op y' x') (op x y) in    
    assert ((y' `op` x') `op` (x `op` y) `eq` full); 
    assoc_lemma4 eq op y' x' x y;
    // trans_lemma eq full ((y' `op` x') `op` (x `op` y)) (y' `op` ((x' `op` x) `op` y));
    neutral_lemma op eq (x' `op` x) y;
    equivalence_wrt_operation_lemma eq ((x' `op` x) `op` y) y y';
    // trans_lemma eq full (y' `op` ((x' `op` x) `op` y)) (y' `op` y);  
    assert (full `eq` (y' `op` y)); 
    // neutral_lemma op eq (y' `op` y) (y' `op` y);
    neutral_equivalent_is_neutral op eq (y' `op` y) full;
    neutral_lemma op eq full full;
    neutral_equivalent_is_neutral op eq full (op full full);
    assoc_lemma4 eq op x y y' x';
    neutral_lemma op eq (y `op` y') x;
    equivalence_wrt_operation_lemma eq (x `op` (y `op` y')) x x';
    // trans_lemma eq ((x `op` y) `op` (y' `op` x')) (x `op` (y `op` y') `op` x') (x `op` x');
    // neutral_lemma op eq (x `op` x') (x `op` x');
    neutral_equivalent_is_neutral op eq (x `op` x') ((x `op` y) `op` (y' `op` x'));
    assert (is_neutral_of (op full full) op eq);
    assert (is_neutral_of (op (op y' x') (op x y)) op eq);
    assert (is_neutral_of (op (op x y) (op y' x')) op eq);
    Classical.exists_intro (fun p -> is_neutral_of (op p (mul x y)) op eq /\ is_neutral_of (op (mul x y) p) op eq)  (op y' x') ;   
  ()

type unary_op_on_units_of (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) =
  f:unary_op(units_of op eq){
   respects_equivalence f (    
     reveal_opaque (`%is_reflexive) (is_reflexive #a); 
     reveal_opaque (`%is_reflexive) (is_reflexive #(units_of op eq)); 
     reveal_opaque (`%is_symmetric) (is_symmetric #a);   
     reveal_opaque (`%is_symmetric) (is_symmetric #(units_of op eq));   
     reveal_opaque (`%is_transitive) (is_transitive #a);
     reveal_opaque (`%is_transitive) (is_transitive #(units_of op eq));
     eq
   )
  }


let yields_inverses_for_units (#a:Type) (op: binary_op a) (eq: (t: equivalence_wrt op {is_associative op t})) (inv: unary_op_on_units_of op eq) = 
  forall (x: units_of op eq). is_neutral_of (op (inv x) x) op eq /\ is_neutral_of (op x (inv x)) op eq

type partial_inverse_op_for (#a:Type) (op: binary_op a) (eq: (t: equivalence_wrt op {is_associative op t})) = (f: unary_op_on_units_of op eq{yields_inverses_for_units op eq f})

let inverse_is_unique (#a:Type) (op: binary_op a) 
                                (eq: (t: equivalence_wrt op {is_associative op t})) 
                                (inv: partial_inverse_op_for op eq)
                                (x inv1 inv2: a) : Lemma
                                (requires is_neutral_of (inv1 `op` x) op eq 
                                        /\ is_neutral_of (x `op` inv1) op eq 
                                        /\ is_neutral_of (inv2 `op` x) op eq
                                        /\ is_neutral_of (x `op` inv2) op eq)
                                (ensures (eq inv1 inv2 /\ eq inv2 inv1)) = 
  reveal_opaque (`%is_associative) (is_associative #a);
  reveal_opaque (`%is_transitive) (is_transitive #a);
  let (x, y, z) = (inv1, inv2, x) in
  neutral_lemma op eq (x `op` z) y;
  neutral_lemma op eq (z `op` y) x;
  trans_lemma eq x ((x `op` z) `op` y) y
                            
let unit_inverse_is_unit (#a:Type) (op: binary_op a) 
                                   (eq: (t: equivalence_wrt op {is_associative op t}))
                                   (inv: partial_inverse_op_for op eq)
                                   (x: units_of op eq)
                                   : Lemma (is_unit (inv x) op eq) = reveal_opaque (`%is_unit) (is_unit #a)

let all_are_units (#a:Type) (op: binary_op a) (eq: equivalence_wrt op {is_associative op eq}) = 
  forall (x:a). is_unit x op eq

noeq type magma (#a: Type) =  
{
  op: binary_op a;
  eq: equivalence_wrt op;
  inv: unary_op_on_units_of op eq;
  neutral: a
}

let magma_inv_respects_eq (#a:Type) (m: magma #a) : Lemma (  
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  reveal_opaque (`%is_reflexive) (is_reflexive #(units_of m.op m.eq)); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  reveal_opaque (`%is_symmetric) (is_symmetric #(units_of m.op m.eq));   
  reveal_opaque (`%is_transitive) (is_transitive #a);
  reveal_opaque (`%is_transitive) (is_transitive #(units_of m.op m.eq)); 
  respects_equivalence #(units_of m.op m.eq) m.inv m.eq) = ()

type semigroup (#a:Type)             = g: magma #a{is_associative g.op g.eq /\ yields_inverses_for_units #a g.op g.eq g.inv}
type commutative_magma (#a:Type)     = g: magma #a{is_commutative g.op g.eq}
type commutative_semigroup (#a:Type) = g: semigroup #a{is_commutative g.op g.eq}
type monoid (#a:Type)                = g: semigroup #a{is_neutral_of g.neutral g.op g.eq}
type commutative_monoid (#a:Type)    = g: monoid #a{is_commutative g.op g.eq}
type group (#a:Type)                 = g: monoid #a{all_are_units g.op g.eq}
type commutative_group (#a:Type)     = g: group #a{is_commutative g.op g.eq}

let partial_inverse_lemma (#a:Type) (mul: binary_op a) (eq: equivalence_wrt mul{is_associative mul eq}) 
                          (f: unary_op_on_units_of mul eq{yields_inverses_for_units #a mul eq f}) 
                          (x: units_of mul eq) 
  : Lemma(is_neutral_of (mul x (f x)) mul eq /\ is_neutral_of (mul (f x) x) mul eq) = ()

let yields_inverses_for_units_lemma (a:Type) (sg: semigroup #a) : Lemma (yields_inverses_for_units #a sg.op sg.eq sg.inv) = ()

let group_elements_are_all_units (#a:Type) (g: group #a) : Lemma (forall (x:a). is_unit x g.op g.eq) = ()

let group_inv_is_complete (#a:Type) (g: group #a) 
  : Lemma (is_inverse_operation_for #a g.inv g.op g.eq) 
  [SMTPat((g.inv))]
  = reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #a)
 
let magma_associativity_smt_lemma (#a:Type) (g: magma #a{is_associative g.op g.eq}) (x y z:a) 
  : Lemma ((x `g.op` (y `g.op` z)) `g.eq` ((x `g.op` y) `g.op` z) /\ ((x `g.op` y) `g.op` z) `g.eq` (x `g.op` (y `g.op` z)))
   [SMTPatOr [[ SMTPat (x `g.op` (y `g.op` z)); SMTPat ((x `g.op` y) `g.op` z) ]]] =
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  reveal_opaque (`%is_associative) (is_associative #a)

let magma_commutativity_smt_lemma (#a:Type) (g: magma #a{is_commutative g.op g.eq}) (x y:a) 
  : Lemma ((x `g.op` y) `g.eq` (y `g.op` x) /\ (y `g.op` x) `g.eq` (x `g.op` y))
   [SMTPatOr [[ SMTPat (x `g.op` y); SMTPat (y `g.op` x) ]]] =
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  reveal_opaque (`%is_commutative) (is_commutative #a)

let magma_operation_respects_eq_smt_lemma (#a:Type) (g: magma #a) (x y z: a) : Lemma (requires x `g.eq` y)
                                                                         (ensures (z `g.op` x) `g.eq` (z `g.op` y) /\
                                                                                  (z `g.op` y) `g.eq` (z `g.op` x) /\
                                                                                  (x `g.op` z) `g.eq` (y `g.op` z) /\
                                                                                  (y `g.op` z) `g.eq` (x `g.op` z))
                                                                         [SMTPatOr [
                                                                           [SMTPat(g.op z x); SMTPat(g.eq x y)]; 
                                                                           [SMTPat(g.op x z); SMTPat(g.eq x y)]; 
                                                                           [SMTPat(g.op z y); SMTPat(g.eq x y)]; 
                                                                           [SMTPat(g.op y z); SMTPat(g.eq x y)]
                                                                         ]] = equivalence_wrt_operation_lemma g.eq x y z                                                        
                                                                                 
let monoid_neutral_smt_lemma (#a:Type) (g: monoid #a) (x: a) : Lemma (x `g.op` g.neutral `g.eq` x /\ g.neutral `g.op` x `g.eq` x)
                                                                     [SMTPatOr[
                                                                       [SMTPat(g.op x g.neutral)];
                                                                       [SMTPat(g.op g.neutral x)]
                                                                     ]] = neutral_lemma g.op g.eq g.neutral x
let monoid_neutral_smt_lemma_2 (#a:Type) (g:monoid #a) (x: a) (y:a) : Lemma (requires is_neutral_of y g.op g.eq)
                                                                            (ensures g.op x y `g.eq` x /\ g.op y x `g.eq` x)
                                                                            [SMTPatOr[
                                                                              [SMTPat(g.op x y)];
                                                                              [SMTPat(g.op y x)]
                                                                            ]] = neutral_lemma g.op g.eq y x
let magma_absorber_smt_lemma_2 (#a:Type) (m: magma #a) (x y:a) : Lemma (requires is_absorber_of x m.op m.eq) (ensures m.op x y `m.eq` x /\ m.op y x `m.eq` x)
                                                                            [SMTPatOr[
                                                                              [SMTPat(m.op x y)];
                                                                              [SMTPat(m.op y x)]
                                                                            ]] = absorber_lemma m.op m.eq x y

let group_inverse_smt_lemma (#a:Type) (g: group #a) (x: a) : Lemma (ensures g.op x (g.inv x) `g.eq` g.neutral /\
                                                                            g.op (g.inv x) x `g.eq` g.neutral /\
                                                                            is_neutral_of (g.op x (g.inv x)) g.op g.eq /\
                                                                            is_neutral_of (g.op (g.inv x) x) g.op g.eq) 
                                                                   [SMTPatOr[
                                                                     [SMTPat(g.op x (g.inv x))];
                                                                     [SMTPat(g.op (g.inv x) x)]
                                                                   ]] =   
  reveal_opaque (`%is_symmetric) (is_symmetric #a);  
  inverse_operation_lemma g.op g.eq g.inv x;
  neutral_is_unique g.op g.eq g.neutral (g.op x (g.inv x));
  neutral_is_unique g.op g.eq g.neutral (g.op (g.inv x) x)
                                                                            

let group_operation_cancellation_smt_lemma (#a:Type) (g: group #a) (e1 e2 x:a) 
  : Lemma (requires g.eq (g.op e1 x) (g.op e2 x) \/ g.eq (g.op x e1) (g.op x e2))
          (ensures g.eq e1 e2)
          [SMTPatOr[
            [SMTPat(g.eq (g.op e1 x) (g.op e2 x))];
            [SMTPat(g.eq (g.op x e1) (g.op x e2))]
          ]] =  
  group_operation_lemma g.eq g.op g.inv e1 e2 x
  
let absorber_never_equals_non_absorber (#a: Type) (op: binary_op a) (eq: equivalence_wrt op) 
  (x: absorber_of op eq) (y: non_absorber_of op eq) : Lemma (~(x `eq` y)) = 
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  if (x `eq` y) then absorber_equal_is_absorber op eq x y

let absorber_nonequal_is_nonabsorber (#a:Type) (op: binary_op a) (eq: equivalence_wrt op) (x: absorber_of op eq) (y: a)
  : Lemma (~(eq x y) \/ ~(eq y x)  ==> ~(is_absorber_of y op eq)) = 
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a);   
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  reveal_opaque (`%is_transitive) (is_transitive #a) //but why and how?!
  
unfold let is_absorber_of_magma (#a:Type) (z: a) (m: magma #a) = is_absorber_of z m.op m.eq

/// When I try to keep the rlimit at minimum, lemmas like this one sometimes help
let neutral_inverse_is_neutral (#a:Type) (g: group #a) : Lemma (g.neutral `g.eq` (g.inv g.neutral)) =  
  reveal_opaque (`%is_transitive) (is_transitive #a);
  // you should keep alive either the assertion, or the inverse_operation_lemma invocation.
  // disabling both will fail the lemma. Keeping both is redundant. SMTPat, I can't understand how you tick.
  // 
  // UPD 11.10.21: with FStar 2021.09.25 it only takes reveal_opaque. No assertion needed anymore.
  //
  assert (is_neutral_of (g.op (g.inv g.neutral) g.neutral) g.op g.eq)
  //inverse_operation_lemma g.op g.eq g.inv g.neutral 
  //group_operation_lemma g.eq g.op g.inv (g.inv g.neutral) g.neutral g.neutral

let group_op_lemma (#a:Type) (g: group #a) (x y z:a) 
  : Lemma (requires (x `g.op` z) `g.eq` (y `g.op` z) \/ (z `g.op` x) `g.eq` (z `g.op` y)) 
          (ensures (x `g.eq` y /\ y `g.eq` x)) 
  = () // group_operation_lemma g.eq g.op g.inv x y z 
       // SMTPat eliminated the need to call the lemma explicitly.

 
let group_element_equality_means_zero_difference (#a:Type) (g: group #a) (x y: a) 
  : Lemma (x `g.eq` y <==> (x `g.op` g.inv y) `g.eq` g.neutral) = 
  // SMTPat says "no need to be so verbose anymore. But I keep this because I know better.
  // inverse_operation_lemma g.op g.eq g.inv y;                   
  // neutral_is_unique g.op g.eq  (g.op y (g.inv y)) g.neutral;   
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
    //absorber_never_equals_non_absorber op eq z y;
    let z' = inv z in
    let zz' = op z z' in
    //absorber_lemma op eq z z';
    inverse_operation_lemma op eq inv z;                  // zz' is the neutral element
    let yzz' = op y zz' in                                // I write "the absorber" here to underline its uniqueness
    //absorber_lemma op eq z z';                        
                                                      (** 1. By definition of absorber, zz' should be equal to z.      *)
    //absorber_lemma op eq zz' y;
    absorber_equal_is_absorber op eq z zz';           (** 2. Any element equal to an absorber is the absorber,         *)
                                                      (**    therefore, zz' is also the absorber, since zz' = z.       *)
    (* assert (is_neutral_of zz' op eq); *)           (** 3. By definition of inverse, zz' is the neutral element.     *)
    (* assert (yzz' `eq` y);             *)           (** 4. By definition of neutral element (zz'), yzz' = y          *)
                                                      (**    This assertion somehow slowed* down the prover a lot!     *)
    (* assert (yzz' `eq` zz');           *)           (** 5. But as zz' is the absorber, yzz' = zz'!                   *)
    absorber_equal_is_absorber op eq zz' yzz';        (** 6. Being equal to the absorber zz', yzz' is the absorber     *)
    neutral_lemma op eq zz' y;                        (** 7. But, as an equal of y, yzz' can't be an absorber!         *) 
    nonabsorber_equal_is_nonabsorber op eq y yzz';    (**    So, we have a contradiction here!                         *) 
//  assert (~(is_absorber_of yzz' op eq)); 
//  assert (is_absorber_of yzz' op eq);               (**    Deleting the last two asserts gave* 10x proof slowdown!   *)
//  * The slowdowns were noticed BEFORE the introduction of opaques. 
//  With opaques, most stuff here passes the verification with 0/0/1 resource settings
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

let product_of_nonabsorbers_is_nonabsorber (#a:Type) (eq: equivalence_relation a) (mul: binary_op a{has_no_absorber_divisors mul eq}) (x y: non_absorber_of mul eq) 
  : Lemma (~(is_absorber_of (mul x y) mul eq) /\ ~(is_absorber_of (mul y x) mul eq)) =  
  reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #a) 
   
 
let euclidean_norm_main_lemma (#a: Type) (eq: equivalence_relation a) (mul: binary_op a{has_no_absorber_divisors mul eq}) (f: norm_function eq mul) (x y: non_absorber_of mul eq)
  : Lemma (Some?.v (
                      reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #a); 
                      allow_inversion (option nat);
                      f (mul x y)
                   ) >= Some?.v (f x)) =
  assert (euclidean_norm_property eq mul x y f)
  
private let test (a:Type) (eq:equivalence_relation a) (mul: binary_op a{has_no_absorber_divisors mul eq}) (f:norm_function eq mul) : Lemma ( 
  forall (x y: non_absorber_of mul eq). Some?.v (reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #a); allow_inversion (option nat); f (mul x y)) >= Some?.v (f x) ) = 
  reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #a);
  allow_inversion (option nat);
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

[@@"opaque_to_smt"]
let is_neutral_invariant (#a: Type) (mul: binary_op a) (eq: equivalence_wrt mul) (f: a -> a) = 
  forall (x:a). (is_neutral_of x mul eq ==> eq x (f x) /\ eq (f x) x)

let is_unit_part_function (#a: Type) (#mul: binary_op a) (#eq: equivalence_wrt mul) (f: a -> units_of mul eq) = 
  is_idempotent f eq /\
  is_neutral_invariant mul eq f /\
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

[@@"opaque_to_smt"]
let unit_and_normal_decomposition_property (#a:Type) (mul: binary_op a) (eq: equivalence_wrt mul) 
                                           (up: a->a) (np: a->a) = forall (x:a). (x `eq` mul (up x) (np x)) /\ (mul (up x) (np x) `eq` x)

[@@"opaque_to_smt"]
let is_normal_part_function (#a:Type) (#mul: binary_op a) (#eq: equivalence_wrt mul) (unit_part_func: a -> a) (f: a -> unit_normal_of mul eq unit_part_func) = 
  is_idempotent f eq /\
  is_neutral_invariant mul eq f /\
  respects_equivalence f eq /\
  yields_unit_normals mul eq unit_part_func f /\
  unary_distributes_over f mul eq /\
  unit_and_normal_decomposition_property mul eq unit_part_func f


type normal_part_function (#a: Type) (#mul: binary_op a) (#eq: equivalence_wrt mul) (unit_part_func: a -> a)
  = f:(a -> (unit_normal_of mul eq unit_part_func)){ is_normal_part_function unit_part_func f }
  
let unit_and_normal_decomposition_lemma (#a:Type) (mul: binary_op a) (eq: equivalence_wrt mul) (up: unit_part_function mul eq) (np: normal_part_function #a #mul #eq up) (x:a)
  : Lemma (x `eq` mul (up x) (np x) /\ mul (up x) (np x) `eq` x) = 
    reveal_opaque (`%is_normal_part_function) (is_normal_part_function #a #mul #eq);
    reveal_opaque (`%unit_and_normal_decomposition_property) (unit_and_normal_decomposition_property #a)
  

let unit_part_func_of_product_is_product_of_unit_parts (#a: Type) (#mul: binary_op a) (#eq: equivalence_wrt mul)
  (unit_part_func: unit_part_function mul eq) (x y: non_absorber_of mul eq) 
  : Lemma((unit_part_func (x `mul` y)) `eq` ((unit_part_func x) `mul` (unit_part_func y))) = 
  un_op_distr_lemma_p mul eq unit_part_func x y;
  ()

let product_of_unit_normals_is_normal (#a: Type) (#mul: binary_op a) (#eq: equivalence_wrt mul)
  (unit_part_func: unit_part_function mul eq)
  (x y: unit_normal_of mul eq unit_part_func)
  : Lemma (requires ~(is_absorber_of x mul eq) /\ ~(is_absorber_of y mul eq))
          (ensures is_unit_normal mul eq unit_part_func (x `mul` y)) =
  let up x = unit_part_func x in
  un_op_distr_lemma_p mul eq unit_part_func x y;                    // up (x*y) = up(x) * up(y) 
  yields_units_lemma mul eq unit_part_func (x `mul` y);             // up (x*y) is unit
  neutral_lemma mul eq (unit_part_func x) (unit_part_func y);       // unit part of unit normal is 1
  neutral_equivalent_is_neutral mul eq (up y) (up x `mul` up y);   
  neutral_equivalent_is_neutral mul eq (up x `mul` up y) (up (mul x y))

noeq type ring (#a: Type) = {
  addition: commutative_group #a;
  multiplication: (t: monoid #a {is_fully_distributive t.op addition.op t.eq});
  eq: (t:equivalence_relation a{ equivalence_wrt_condition addition.op t /\ equivalence_wrt_condition multiplication.op t /\ t==addition.eq /\ t==multiplication.eq });
  unit_part_of: a -> units_of multiplication.op eq;
  normal_part_of: a -> unit_normal_of multiplication.op eq unit_part_of;
  euclidean_norm: nat_function_defined_on_non_absorbers multiplication.op eq 
} 

let ring_distributivity_lemma (#a:Type) (r: ring #a) 
    : Lemma (is_right_distributive r.multiplication.op r.addition.op r.eq 
            /\ is_left_distributive r.multiplication.op r.addition.op r.eq) = 
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a);
    reveal_opaque (`%is_right_distributive) (is_right_distributive #a); 
    reveal_opaque (`%is_left_distributive) (is_left_distributive #a)
 
/// This one is made private because we only work with commutative multiplication here
unfold let mul_of (#a:Type) (r: ring #a) = r.multiplication.op

/// And this one is made private just for the sake of symmetry with mul_of
unfold let add_of (#a:Type) (r: ring #a) = r.addition.op

let ring_add_yields_inv_for_units (a:Type) (r: ring #a) : Lemma (yields_inverses_for_units r.addition.op r.eq r.addition.inv) = yields_inverses_for_units_lemma a r.addition

/// The general idea is (1) x = x*(1+0) = x*1+x*0 = x+x*0 = x+0;
///                     (2) (x+x*0 = x+0) ==> (x*0 = 0) QED.
let ring_addition_neutral_is_absorber (#a:Type) (r: ring #a) (x: a)
  : Lemma (x `r.multiplication.op` r.addition.neutral `r.eq` r.addition.neutral /\
           r.addition.neutral `r.multiplication.op` x `r.eq` r.addition.neutral /\
           r.addition.neutral `r.eq` (r.addition.neutral `r.multiplication.op` x) /\
           r.addition.neutral `r.eq` (x `r.multiplication.op` r.addition.neutral)) =  
  reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a); 
  let ( *) = r.multiplication.op in
  let (+) = r.addition.op in
  let zero = r.addition.neutral in
  let one = r.multiplication.neutral in
  let eq = r.eq in
  // neutral_lemma (+) eq zero one;
  neutral_equivalent_is_neutral ( *) eq one (zero+one);
  // neutral_lemma ( *) eq (zero+one) x;
  trans_lemma eq ((x*zero)+(x*one)) (x*(zero+one)) x;
  trans_lemma eq ((x*zero)+(x*one)) x (x*one);
  neutral_lemma (+) eq zero (x*one);
  trans_lemma eq ((x*zero)+(x*one)) (x*one) (zero+(x*one));
  // group_op_lemma r.addition (x*zero) zero (x*one);
  trans_lemma eq ((zero*x)+(one*x)) ((zero+one)*x) x;
  trans_lemma eq ((zero*x)+(one*x)) x (one*x);
  neutral_lemma (+) eq zero (one*x);
  trans_lemma eq ((zero*x)+(one*x)) (one*x) (zero+(one*x));
  // group_op_lemma r.addition (zero*x) zero (one*x);
  ()

let ring_addition_neutral_is_multiplication_absorber_smt_lemma (#a:Type) (r: ring #a)
  : Lemma (is_absorber_of r.addition.neutral r.multiplication.op r.eq) 
          [SMTPat(r.addition.neutral)] = 
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a);
  Classical.forall_intro (ring_addition_neutral_is_absorber r)
 

unfold let neg_of (#a:Type) (r: ring #a) (p:a) : (t:a{ t `r.eq` (r.addition.neutral `r.addition.op` (r.addition.inv p) )}) 
  =  //Without SMTPat, it took quite a lot of explicit steps:
//  reveal_opaque (`%is_symmetric) (is_symmetric #a) ;
//  inverse_operation_lemma r.addition.op r.eq r.addition.inv p;
//  inverse_element_defining_lemma r.eq r.addition.op r.addition.inv p (r.addition.inv p);
//  neutral_lemma r.addition.op r.eq  r.addition.neutral (r.addition.inv p);
  r.addition.inv p

unfold let minus_of (#a:Type) (r: ring #a) (x:a) (y:a) : (t:a{ t `r.eq` (x `r.addition.op` (r.addition.inv y) )}) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #a);
  x `r.addition.op` (neg_of r y)

let double_inverse_is_id (#a:Type) (op: binary_op a) (eq: equivalence_wrt op{is_associative op eq}) (inv: inverse_op_for op eq) (x: a) 
  : Lemma (inv (inv x) `eq` x /\ x `eq` inv (inv x)) =    
  inverse_operation_lemma op eq inv x;
  inverse_operation_lemma op eq inv (inv x);   
  neutral_is_unique op eq (x `op` inv x) (inv (inv x) `op` inv x);
  group_operation_lemma eq op inv x (inv (inv x)) (inv x)   //;
//  symm_lemma eq (inv (inv x)) x                           //At least, SMTPat cut this one off.

let minus_minus_x_is_x_smt_lemma (#a:Type) (r: ring #a) (x: a) 
  : Lemma (r.addition.inv (r.addition.inv x) `r.eq` x /\ x `r.eq` (r.addition.inv (r.addition.inv x)))
          [SMTPat(r.addition.inv (r.addition.inv x))]
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
    // assert (is_neutral_of (op x y') op eq);
    producing_neutral_means_inverses eq op inv x y'
    // assert (inv x `eq` inv y)    
  ) else (
    if (inv x `eq` inv y) then (
      let x' = inv x in
      let y' = inv y in
      let x'' = (inv (inv x)) in
      let y'' = (inv (inv y)) in
      double_inverse_is_id op eq inv x;
      double_inverse_is_id op eq inv y; 
      //assert (inv x' `eq` x);
      //assert (inv y' `eq` y);
      inverse_operation_lemma op eq inv y'; 
      //equivalence_wrt_operation_lemma eq x' y' x'';
      equivalence_wrt_operation_lemma eq x' y' y'';
      neutral_equivalent_is_neutral op eq (op y' y'') (op x' y'');
      //assert (is_neutral_of (op x' y'') op eq);
      producing_neutral_means_inverses eq op inv x' y'';
      trans_lemma_4 eq x x'' y'' y
    )
  )
  
let ring_additive_inv_x_is_x_times_minus_one (#a:Type) (r: ring #a) (x: a)
  : Lemma ((r.addition.inv x) `r.eq` (r.multiplication.op x (r.addition.inv r.multiplication.neutral)) /\
           (r.multiplication.op x (r.addition.inv r.multiplication.neutral)) `r.eq` (r.addition.inv x)) = 
    reveal_opaque (`%is_symmetric) (is_symmetric #a); 
    reveal_opaque (`%is_transitive) (is_transitive #a); 
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a); 
    let eq = r.eq in
    let mul = r.multiplication.op in
    let add = r.addition.op in
    let inv = r.addition.inv in 
    let zero = r.addition.neutral in
    let one = r.multiplication.neutral in
    //let ix = inv x in  
    //  ring_addition_neutral_is_multiplication_absorber_smt_lemma r;
    // assert (is_neutral_of (one `add` (inv one)) add eq);
     neutral_is_unique r.addition.op r.eq zero (one `add` (inv one));
    // assert (zero `eq` (one `add` (inv one)));
    // equivalence_wrt_operation_lemma #a #mul eq zero (one `add` (inv one)) x;
    // assert (mul x (one `add` (inv one)) `eq` (mul x zero));
    // assert (mul x zero `eq` zero);
    // assert ((mul x (one `add` (inv one))) `eq` ((mul x one) `add` (mul x (inv one)))); 
    // symm_lemma eq ((mul x one) `add` (mul x (inv one))) (mul x (one `add` (inv one)));
    // this one speeds up the process if uncommented
    // assert (is_left_distributive mul add eq);
    // left_distributivity_lemma mul add eq x one (inv one);
    // assert (((mul x one) `add` (mul x (inv one))) `eq` (mul x (one `add` (inv one))));    
    // this one requires spinoff!!! for some reason...
    // inverse_operation_lemma add r.eq inv one;
    // assert (is_neutral_of (one `add` inv one) add r.eq);
    // neutral_is_unique add r.eq zero (one `add` inv one);
    // assert (eq (one `add` inv one) zero);
    // absorber_equal_is_absorber mul r.eq zero (one `add` inv one);
    // absorber_lemma mul r.eq (one `add` inv one) x;
    // assert (mul x (one `add` (inv one)) `eq` zero);       
    // trans_lemma r.eq ((mul x one) `add` (mul x (inv one))) (mul x (one `add` (inv one))) zero;
    // assert (((mul x one) `add` (mul x (inv one))) `eq` zero);
    // assert (is_neutral_of zero add eq);
    neutral_equivalent_is_neutral add eq zero ((mul x one) `add` (mul x (inv one)));
    // assert (is_neutral_of ((mul x one) `add` (mul x (inv one))) add eq);
    producing_neutral_means_inverses eq add inv (mul x one) (mul x (inv one));
    // assert (eq (inv (mul x one)) (mul x (inv one)));
    // assert (is_neutral_of one mul eq);
    // neutral_lemma mul eq one x;
    // assert (mul x one `eq` x);    
    x_eq_y_means_inv_x_eq_inv_y add eq inv (mul x one) x;
    // assert (inv (mul x one) `eq` (inv x));
    trans_lemma eq (inv x) (inv (mul x one)) (mul x (inv one));
    () 

/// A quiz: why does this require is_reflexive, and the supposedly symmetric previous lemma doesn't? ;)
let ring_additive_inv_x_is_minus_one_times_x (#a:Type) (r: ring #a) (x: a)
  : Lemma ((r.addition.inv x) `r.eq` (r.multiplication.op (r.addition.inv r.multiplication.neutral) x) /\
           (r.multiplication.op (r.addition.inv r.multiplication.neutral) x) `r.eq` (r.addition.inv x)) = 
    reveal_opaque (`%is_symmetric) (is_symmetric #a); 
    reveal_opaque (`%is_transitive) (is_transitive #a); 
    reveal_opaque (`%is_reflexive) (is_reflexive #a);  
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a); 
    let eq = r.eq in
    let mul = r.multiplication.op in
    let add = r.addition.op in
    let inv = r.addition.inv in 
    let zero = r.addition.neutral in
    let one = r.multiplication.neutral in
    neutral_is_unique r.addition.op r.eq zero (one `add` (inv one));
    neutral_equivalent_is_neutral add eq zero ((mul one x) `add` (mul (inv one) x));
    producing_neutral_means_inverses eq add inv (mul one x) (mul (inv one) x);
    x_eq_y_means_inv_x_eq_inv_y add eq inv (mul one x) x;
    trans_lemma eq (inv x) (inv (mul one x)) (mul (inv one) x);
    () 


let equal_elements_means_equal_inverses (#a:Type) (r: ring #a) (x y:a) 
  : Lemma ((r.eq x y == (r.addition.inv x `r.eq` r.addition.inv y)) /\ 
           (r.eq x y == (r.addition.inv y `r.eq` r.addition.inv x))) =   
          reveal_opaque (`%is_symmetric) (is_symmetric #a); 
          reveal_opaque (`%is_reflexive) (is_reflexive #a);     
          x_eq_y_means_inv_x_eq_inv_y r.addition.op r.eq r.addition.inv x y 
 
let inv_switch_lemma (#a:Type) (r: ring #a) (x y:a) : Lemma (x `r.eq` (r.addition.inv y) <==> (r.addition.inv x) `r.eq` y) =   

  reveal_opaque (`%is_transitive) (is_transitive #a); 
  equal_elements_means_equal_inverses r x (r.addition.inv y)
  (* This is how the proof looked like without SMTPats
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
  *)

let ring_additive_inverse_is_unique (#a:Type) (r:ring #a) (x y: a) 
  : Lemma (requires x `r.eq` y \/ y `r.eq` x) 
          (ensures r.addition.inv x `r.eq` r.addition.inv y /\ r.addition.inv y `r.eq` r.addition.inv x) 
  = reveal_opaque (`%is_symmetric) (is_symmetric #a);   
    equal_elements_means_equal_inverses r x y


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
  reveal_opaque (`%is_associative) (is_associative #a);
  reveal_opaque (`%is_transitive) (is_transitive #a);   
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  ring_additive_inv_x_is_x_times_minus_one r y; // -y = (y * -1)
  equivalence_wrt_operation_lemma #a #mul eq (neg y) (y `mul` neg one) x; // x*(-y) = x*(y*(-1))
  //associative_operation_lemma eq mul x y (neg one);                       // x*(y*(-1)) = (x*y)*(-1)
  ring_additive_inv_x_is_x_times_minus_one r (x `mul` y);                 // (xy)*(-1) = -(xy)
 // trans_lemma eq (x `mul` neg y) (x `mul` (y `mul` neg one)) ((x `mul` y) `mul` neg one);
 // trans_lemma eq (x `mul` neg y) ((x `mul` y) `mul` neg one) (neg (x `mul` y));  
  ()

let ring_x_times_minus_y_is_minus_x_times_y (#a:Type) (r:ring #a) (x y: a) : Lemma (
    (x `r.multiplication.op` r.addition.inv y) `r.eq` (r.addition.inv x `r.multiplication.op` y) &&
    (r.addition.inv x `r.multiplication.op` y) `r.eq` (x `r.multiplication.op` r.addition.inv y) 
  ) =     
  reveal_opaque (`%is_transitive) (is_transitive #a);   
  let eq = r.eq in
  let mul = r.multiplication.op in
  let add = r.addition.op in
  let neg = r.addition.inv in 
  let zero = r.addition.neutral in
  let one = r.multiplication.neutral in
  ring_additive_inv_x_is_minus_one_times_x r y;  
  // associative_operation_lemma eq mul x (neg one) y;
  // assert (neg y `eq` mul (neg one) y);
  // equivalence_wrt_operation_lemma #a #mul eq (neg y) (mul (neg one) y) x;
  // assert ((x `mul` neg y) `eq` (x `mul` (neg one `mul` y)));
  // associative_operation_lemma eq mul x (neg one) y;
  // assert ((x `mul` (neg one `mul` y)) `eq` ((x `mul` neg one) `mul` y));
  // trans_lemma eq (x `mul` neg y) (x `mul` (neg one `mul` y)) ((x `mul` neg one) `mul` y);
  // assert (eq (x `mul` neg y) ((x `mul` neg one) `mul` y));
  ring_additive_inv_x_is_x_times_minus_one r x
  // assert ((x `mul` neg one) `eq` neg x);
  // equivalence_wrt_operation_lemma #a #mul eq (x `mul` neg one) (neg x) y;
  // assert ( ((x `mul` neg one) `mul` y) `eq` (neg x `mul` y) )
  // trans_lemma eq (x `mul` neg y) ((x `mul` neg one) `mul` y) (neg x `mul` y)

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
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a); 
  // left_distributivity_lemma mul add eq x y (neg z);
  ring_x_times_minus_y_is_minus_xy r x z;
  // assert ((x `mul` neg z) `eq` neg (x `mul` z)); 
  // equivalence_wrt_operation_lemma #a #add eq (x `mul` neg z) (neg (x `mul` z)) (x `mul` y);
  // assert (((x `mul` y) `add` (x `mul` neg z)) `eq` ((x `mul` y) `add` (neg (x `mul` z))));
  // trans_lemma eq (x `mul` (y `add` neg z)) ((x `mul` y) `add` (x `mul` neg z))  ((x `mul` y) `add` (neg (x `mul` z)));
  ()

(*
let neut_add_lemma (#a: Type) (r: ring #a) : Lemma (is_neutral_of r.addition.neutral r.addition.op r.eq) = () 
let neut_lemma (#a: Type) (r: ring #a) : Lemma (is_neutral_of r.multiplication.neutral r.multiplication.op r.eq) = ()
let add_eq_of (#a:Type) (r: ring #a) : equivalence_wrt r.addition.op = r.eq

let mul_neutral_lemma (#a: Type) (r: ring #a) (x: a{is_neutral_of x r.multiplication.op r.eq})
  : Lemma (r.eq x r.multiplication.neutral) =
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  neutral_is_unique r.multiplication.op r.eq r.multiplication.neutral x
*)

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
  //ring_addition_neutral_is_multiplication_absorber r;
  reveal_opaque (`%is_reflexive) (is_reflexive #a);   
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a); 
  if (r.eq z r.addition.neutral) 
  then absorber_equal_is_absorber r.multiplication.op r.eq r.addition.neutral z  
  else FStar.Classical.move_requires_2 (absorber_is_unique r.multiplication.op r.eq) z r.addition.neutral  
   
let zero_is_equal_to_add_neutral (#a:Type) (r: ring #a) : Lemma (forall (x:a). is_zero_of r x <==> r.eq x r.addition.neutral) 
  = FStar.Classical.forall_intro (zero_is_equal_to_add_neutral_p r)

let nonzero_is_not_equal_to_add_neutral (#a:Type) (r: ring #a) 
  : Lemma (forall (x:a). ~(is_zero_of r x) <==> ~(r.eq x r.addition.neutral)) = zero_is_equal_to_add_neutral r
 
let nonzero_is_not_equal_to_add_neutral_p (#a:Type) (r: ring #a) (z: a)
  : Lemma (~(is_absorber_of z r.multiplication.op r.eq) <==> ~(r.eq z r.addition.neutral)) = zero_is_equal_to_add_neutral r

type domain (#a: Type) = r:ring #a { has_no_absorber_divisors r.multiplication.op r.eq /\ ~(r.eq r.addition.neutral r.multiplication.neutral \/ r.eq r.multiplication.neutral r.addition.neutral ) }

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

let domain_deduce_zero_factor_from_zero_product_and_nonzero_factor (#a:Type) (d: domain #a) (x y: a)
  : Lemma (is_absorber_of (x `d.multiplication.op` y) d.multiplication.op d.eq 
       /\ ~(is_absorber_of y d.multiplication.op d.eq)
       ==> is_absorber_of x d.multiplication.op d.eq) 
  = reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #a) 

let domain_zero_product_means_zero_factor (#a:Type) (dom: domain #a) (p q: a) 
  : Lemma (requires (p `dom.multiplication.op` q) `dom.eq` dom.addition.neutral)
          (ensures (p `dom.eq` dom.addition.neutral \/ q `dom.eq` dom.addition.neutral)) =   
  neutral_equivalent_is_neutral dom.addition.op dom.eq dom.addition.neutral (p `dom.multiplication.op` q);
  absorber_equal_is_absorber dom.multiplication.op dom.eq dom.addition.neutral (p `dom.multiplication.op` q); 
  domain_multiplication_law_inv dom.eq dom.multiplication.op p q;
  zero_is_equal_to_add_neutral dom

let ring_zero_factor_means_zero_product (#a:Type) (r: ring #a) (p q:a)
  : Lemma (requires is_absorber_of p r.multiplication.op r.eq \/ is_absorber_of q r.multiplication.op r.eq)
          (ensures is_absorber_of (r.multiplication.op p q) r.multiplication.op r.eq) = 
          Classical.move_requires_2 (absorber_lemma r.multiplication.op r.eq) p q;
          Classical.move_requires_2 (absorber_lemma r.multiplication.op r.eq) q p

let domain_nonzero_product_means_nonzero_factors (#a:Type) (r: ring #a) (p q: a)
  : Lemma (requires ~(is_absorber_of (r.multiplication.op p q) r.multiplication.op r.eq))
          (ensures ~(is_absorber_of p r.multiplication.op r.eq) /\ ~(is_absorber_of q r.multiplication.op r.eq)) =
  Classical.move_requires_2 (ring_zero_factor_means_zero_product r) p q


          
let domain_characterizing_lemma (#a:Type) (dom: domain #a) (p q: a) 
  : Lemma ((p `dom.multiplication.op` q) `dom.eq` dom.addition.neutral <==>
           (p `dom.eq` dom.addition.neutral \/ q `dom.eq` dom.addition.neutral)) =   
  reveal_opaque (`%is_transitive) (is_transitive #a);              
  //ring_addition_neutral_is_multiplication_absorber dom;    
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
  
let domain_law_from_pq_eq_pr (#a:Type) (d: domain #a) (p q r: a)
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
  trans_lemma_4 eq zero 
                  ((p `mul` q) `add` (neg (p `mul` r))) 
                  ((p `mul` q) `add` (p `mul` (neg r))) 
                  ((p `mul` (q `add` neg r)));
  domain_characterizing_lemma d p (add q (neg r));
  if (not (p `d.eq` zero) && d.addition.op q (d.addition.inv r) `d.eq` zero) 
  then group_element_equality_means_zero_difference d.addition q r 
    
let domain_cancellation_law (#a:Type) (d: domain #a) (p q r: a)
  : Lemma (requires d.eq (d.multiplication.op p q) (d.multiplication.op p r) /\ ~(is_absorber_of p d.multiplication.op d.eq))
          (ensures d.eq q r) = 
          domain_law_from_pq_eq_pr d p q r;
          nonzero_is_not_equal_to_add_neutral_p d p 
 
let domain_unit_and_absorber_is_nonsense (#a:Type) (#d: domain #a) (x: a) 
  : Lemma (requires is_unit x d.multiplication.op d.eq /\ is_absorber_of x d.multiplication.op d.eq) (ensures False) =   
  let ( *) = d.multiplication.op in
  let eq = d.eq in
  reveal_opaque (`%is_unit) (is_unit #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  let x' = d.multiplication.inv x in 
  // With proper definition of inverse function, the call to indefinite_description_ghost is redundant.
  // Earlier, x' was initialized with indefinite_description_ghost (units_of ( *) eq) (fun x' -> 
  //                                    (is_neutral_of (x * x') ( *) eq /\ is_neutral_of (x' * x) ( *) eq)) 
  let xx' = x * x' in
  assert (is_neutral_of xx' ( *) eq);
  assert (is_neutral_of d.multiplication.neutral d.multiplication.op d.eq);
  neutral_is_unique ( *) eq d.multiplication.neutral xx'; 
  assert (eq xx' d.multiplication.neutral);
  absorber_lemma ( *) eq x x'; 
  assert (is_absorber_of xx' ( *) eq);
  absorber_is_unique ( *) eq d.addition.neutral xx';
  assert (eq xx' d.addition.neutral) 

let domain_unit_cant_be_absorber (#a:Type) (#d: domain #a) (x: units_of d.multiplication.op d.eq) : Lemma (~(is_absorber_of x d.multiplication.op d.eq)) = 
  Classical.move_requires (domain_unit_and_absorber_is_nonsense #a #d) x

let domain_absorber_cant_be_unit (#a:Type) (#d: domain #a) (x: absorber_of d.multiplication.op d.eq) : Lemma (~(is_unit x d.multiplication.op d.eq)) =
  Classical.move_requires (domain_unit_and_absorber_is_nonsense #a #d) x
  
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
 
private let normal_of_nonabs_cant_be_abs (#a:Type) (d: integral_domain #a) (x: non_absorber_of d.multiplication.op d.eq) : Lemma (requires is_absorber_of (d.normal_part_of x) d.multiplication.op d.eq) (ensures False) =
  unit_and_normal_decomposition_lemma d.multiplication.op d.eq d.unit_part_of d.normal_part_of x;
  reveal_opaque (`%is_reflexive) (is_reflexive #a);  
  reveal_opaque (`%is_symmetric) (is_symmetric #a);  
  reveal_opaque (`%is_transitive) (is_transitive #a);  
  absorber_lemma d.multiplication.op d.eq (d.normal_part_of x) (d.unit_part_of x);
  assert (x `d.eq` d.normal_part_of x);
  absorber_equal_is_absorber d.multiplication.op d.eq (d.normal_part_of x) x 

let normal_part_of_nonabsorber_is_nonabsorber (#a:Type) (#d: integral_domain #a) (x: non_absorber_of d.multiplication.op d.eq) 
  : Lemma (~(is_absorber_of (d.normal_part_of x) d.multiplication.op d.eq)) = Classical.move_requires (normal_of_nonabs_cant_be_abs d) x

type euclidean_domain (#a:Type) = r:integral_domain #a { euclidean_norm_forall_property r.eq r.multiplication.op r.euclidean_norm }

let ring_multiplicative_group_condition (#a:Type) (r: ring #a) = forall (x:a). (is_unit x r.multiplication.op r.eq <==> ~(is_absorber_of x r.multiplication.op r.eq))

/// Skewfields, aka division rings, are non-commutative counterparts for fields,
/// offering multiplicative inverses for each nonzero element, but not guaranteeing
/// ab⁻¹ to be equal to b⁻¹a.
/// Since these only appear in rather exotic situations (mind octonions),
/// I'll probably never have an instance of this type anyway.
type skewfield (#a:Type) = r:domain #a { ring_multiplicative_group_condition r }

/// Fields, on the other hands, are quite common.
/// We'll later have the notions for
///  - extensions for fields (algebraic and transcendental)
///  - differential fields (and extensions)
///  - fields of fractions for integral domains
/// 
/// We do not require the field to have unit_part and normal_part properly defined,
/// as for fields, all elements do have the multiplicative inverses, therefore their
/// "unit parts" are supposed to coincide with themselves, and we don't have a good notion
/// for irreducibles in fields anyway.
type field (#a:Type) = r:domain #a {
  is_commutative r.multiplication.op r.eq /\
  ring_multiplicative_group_condition r
}
#pop-options
