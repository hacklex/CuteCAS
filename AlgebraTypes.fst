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
let congruence_condition (#a: Type) (op: binary_op a) (eq: equivalence_relation a) = 
  forall (x y z:a). eq x y ==> (op x z `eq` op y z) && (op z x `eq` op z y)

[@@"opaque_to_smt"]
let unary_congruence_condition (#a: Type) (op: unary_op a) (eq: equivalence_relation a) = 
  forall (x y: a). eq x y ==> (op x `eq` op y) && (op y `eq` op x)

type op_with_congruence (#a:Type) (eq: equivalence_relation a) = op:binary_op a{congruence_condition op eq}

type unary_op_with_congruence #a (eq: equivalence_relation a) = op: unary_op a{unary_congruence_condition op eq}

let equivalence_is_symmetric (#a:Type) (eq: equivalence_relation a) (x y:a)
  : Lemma (x `eq` y = y `eq` x) = reveal_opaque (`%is_symmetric) (is_symmetric #a)
 
let trans_lemma (#a:Type) (eq: equivalence_relation a) (x y z:a)
  : Lemma (requires (eq x y \/ eq y x) /\ (eq y z \/ eq z y))  
          (ensures (x `eq` z) && (z `eq` x))   
  = reveal_opaque (`%is_transitive) (is_transitive eq);
    reveal_opaque (`%is_symmetric) (is_symmetric eq)

let trans_lemma_4 (#a:Type) (eq: equivalence_relation a) (x y z w:a)
  : Lemma (requires (eq x y \/ eq y x) /\ (eq y z \/ eq z y) /\ (eq z w \/ eq w z))
          (ensures x `eq` w && w `eq` x) = 
  reveal_opaque (`%is_transitive) (is_transitive eq);
  reveal_opaque (`%is_symmetric) (is_symmetric eq)

let trans_lemma_5 (#a:Type) (eq: equivalence_relation a) (x y z w v: a)                            
  : Lemma (requires (eq x y \/ eq y x) /\ (eq y z \/ eq z y) /\ (eq z w \/ eq w z) /\ (eq w v \/ eq v w))
          (ensures eq x v && eq v x) = 
  reveal_opaque (`%is_transitive) (is_transitive eq);
  reveal_opaque (`%is_symmetric) (is_symmetric eq)                                                        

let symm_lemma (#a:Type) (eq:equivalence_relation a) (x y:a) 
  : Lemma (eq x y == eq y x) = reveal_opaque (`%is_symmetric) (is_symmetric eq) 

/// FStar does not automatically apply lemmas on equivalence being symmetric reflexive and transitive.
/// So, I at least make my lemmas such that I care about `eq` operand order as little as possible
let congruence_lemma_3 (#a: Type) (#eq: equivalence_relation a) (op: op_with_congruence eq) (e1 e2 z: a)
  : Lemma 
  (requires e1 `eq` e2 \/ e2 `eq` e1) 
  (ensures 
    (e1 `op` z) `eq` (e2 `op` z) /\    
    (e2 `op` z) `eq` (e1 `op` z) /\    
    (z `op` e1) `eq` (z `op` e2) /\
    (z `op` e2) `eq` (z `op` e1)) = reveal_opaque (`%congruence_condition) (congruence_condition op);
                                    reveal_opaque (`%is_symmetric) (is_symmetric eq) 

let congruence_lemma_4 (#a:Type) 
                       (#eq: equivalence_relation a) 
                       (op: op_with_congruence eq)
                       (x y p q: a) 
  : Lemma (requires ((x `eq` p) \/ (p `eq` x)) /\ ((y `eq` q) \/ (q `eq` y)))
          (ensures (((x `op` y) `eq` (p `op` q)) /\ ((y `op` x) `eq` (q `op` p)))) =          
  reveal_opaque (`%congruence_condition) (congruence_condition op);
  reveal_opaque (`%is_transitive) (is_transitive eq);
  congruence_lemma_3 op x p y;
  congruence_lemma_3 op y q p
    
/// Here, we define basic axioms of algebraic structures in form of propositions
/// about operations and elements. 
[@@"opaque_to_smt"]
let is_associative (#a:Type) (#eq: equivalence_relation a) (op: op_with_congruence eq) 
  = forall (x y z:a). ((x `op` y) `op` z) `eq` (x `op` (y `op` z))

/// This one is only needed for the lemma below to turn 12 lines of equality into just 4.
unfold private let eq_twoway (#a:Type) (eq: equivalence_relation a) (x y: a) = (x `eq` y) && (y `eq` x)

unfold private let multi_equality_5 (#a: Type) (eq: equivalence_relation a) (e1 e2 e3 e4 e5: a) = 
  e1 `eq` e2 && e1 `eq` e3 && e1 `eq` e4 && e1 `eq` e5 &&
  e2 `eq` e1 && e2 `eq` e3 && e2 `eq` e4 && e2 `eq` e5 &&
  e3 `eq` e1 && e3 `eq` e2 && e3 `eq` e4 && e3 `eq` e5 &&
  e4 `eq` e1 && e4 `eq` e2 && e4 `eq` e3 && e4 `eq` e5 &&
  e5 `eq` e1 && e5 `eq` e2 && e5 `eq` e3 && e5 `eq` e4 
  
/// Regular associativity lemma, straightforward
/// and with minimal possible requirements.
let assoc_lemma_3 (#a:Type) (#eq: equivalence_relation a) 
                  (op: op_with_congruence eq{is_associative op}) 
                  (x y z: a) 
  : Lemma (((x `op` y) `op` z) `eq` (x `op` (y `op` z)) /\ 
           (x `op` (y `op` z)) `eq` ((x `op` y) `op` z)) 
  = reveal_opaque (`%is_associative) (is_associative op);
    reveal_opaque (`%is_symmetric) (is_symmetric eq)

/// Associativity for all possible parentheses configurations between 4 terms.
/// This one's a bit monstrous, but it comes in handy later. 
let assoc_lemma_4 (#a:Type) (#eq: equivalence_relation a) 
                  (op: op_with_congruence eq{is_associative op}) 
                  (x y z w: a) 
  : Lemma (multi_equality_5 eq 
     (((x `op` y) `op` z) `op` w)
     (x `op` (y `op` (z `op` w)))
     ((x `op` y) `op` (z `op` w))
     ((x `op` (y `op` z)) `op` w)
     (x `op` ((y `op` z) `op` w))) = 
  // revealing opaques eliminate the need for additional instructions to the prover.
  reveal_opaque (`%is_associative) (is_associative op);
  reveal_opaque (`%is_transitive) (is_transitive eq);
  reveal_opaque (`%is_symmetric) (is_symmetric eq);
  reveal_opaque (`%congruence_condition) (congruence_condition op) 
 
[@@"opaque_to_smt"]
let is_commutative (#a:Type) (#eq: equivalence_relation a) 
                   (op: op_with_congruence eq) 
  = forall (x y:a). ((x `op` y) `eq` (y `op` x)) /\ ((y `op` x) `eq` (x `op` y))

let bring_any_operand_forth (#a:Type) 
                  (#eq: equivalence_relation a) 
                  (op: op_with_congruence eq { is_associative op /\ is_commutative op })
                  (x y z w: a) 
  : Lemma (multi_equality_5 eq (x `op` y `op` z `op` w)
                               (x `op` (y `op` (z `op` w))) 
                               (y `op` (x `op` (z `op` w))) 
                               (z `op` (x `op` (y `op` w)))
                               (w `op` (x `op` (y `op` z)))) =   
  reveal_opaque (`%is_transitive) (is_transitive eq);
  reveal_opaque (`%is_symmetric) (is_symmetric eq);    
  reveal_opaque (`%is_associative) (is_associative op);
  reveal_opaque (`%is_commutative) (is_commutative op);
  reveal_opaque (`%congruence_condition) (congruence_condition op); 
  assoc_lemma_4 op x y z w;
  assert (multi_equality_5 eq (x `op` (y `op` (z `op` w)))
                              (x `op` y `op` z `op` w)
                              (y `op` x `op` z `op` w)
                              (z `op` x `op` y `op` w)
                              (w `op` x `op` y `op` z)); 
  assoc_lemma_4 op w x y z  
 
/// This one is used to assert commutativity, works with both add and mul.
/// Used when revealing is_commutative opaque wastes too much rlimit.
let comm_lemma (#a:Type) (#eq: equivalence_relation a) 
               (op: op_with_congruence eq{is_commutative op}) (x y: a)
  : Lemma ((op x y) `eq` (op y x) /\ (op y x) `eq` (op x y)) 
  = reveal_opaque (`%is_commutative) (is_commutative op)

[@@"opaque_to_smt"]
let is_idempotent (#a:Type) (#eq: equivalence_relation a) (r: unary_op_with_congruence eq) 
  = forall (x:a). (r x) `eq` (r (r x))

/// Things quickly get funny if we consider non-associative structures (magmas etc).
/// Therefore we don't, not because we dislike fun, but because we strive for sanity.

[@@"opaque_to_smt"]
let is_left_id_of  (#a:Type) (u:a) (#eq: equivalence_relation a) (op: op_with_congruence eq) = forall (x:a). (u `op` x) `eq` x // left identity

[@@"opaque_to_smt"]
let is_right_id_of (#a:Type) (u:a) (#eq: equivalence_relation a) (op: op_with_congruence eq) = forall (x:a). (x `op` u) `eq` x // right identity

[@@"opaque_to_smt"]
let is_neutral_of  (#a:Type) (u:a) (#eq: equivalence_relation a) (op: op_with_congruence eq) = is_left_id_of u op /\ is_right_id_of u op // neutral element

type neutral_element_of (#a: Type) (#eq: equivalence_relation a) (op: op_with_congruence eq) = (x:a{is_neutral_of x op})

let neutral_lemma (#a:Type) (#eq: equivalence_relation a) (op: op_with_congruence eq) (x: neutral_element_of op) (y:a)
  : Lemma ((x `op` y) `eq` y /\ (y `op` x) `eq` y) = 
  reveal_opaque (`%is_left_id_of) (is_left_id_of #a); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #a); 
  reveal_opaque (`%is_neutral_of) (is_neutral_of #a)
  
/// If you see something trivial, then it is either here to reduce the rlimit for some bigger lemma,
/// or a leftover from time where something didn't verify and I made more and more explicit lemmas,
/// or it should be deleted. I periodically cleanup this file and remove unused lemmas.
/// Nothing big gets removed anyway.
let neutral_is_unique (#a:Type) (#eq: equivalence_relation a) (op: op_with_congruence eq) (u: neutral_element_of op) (v: neutral_element_of op) 
  : Lemma (eq u v) = 
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a);  
  reveal_opaque (`%is_left_id_of) (is_left_id_of #a); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #a);
  reveal_opaque (`%is_neutral_of) (is_neutral_of #a)

let neutral_equivalent_is_neutral (#a:Type) (#eq: equivalence_relation a) 
                                  (op: op_with_congruence eq) 
                                  (x: neutral_element_of op) 
                                  (y: a{y `eq` x}) 
  : Lemma (is_neutral_of y op) =    
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  reveal_opaque (`%is_left_id_of) (is_left_id_of #a); 
  reveal_opaque (`%is_right_id_of) (is_right_id_of #a);
  reveal_opaque (`%is_neutral_of) (is_neutral_of #a);
  Classical.forall_intro (Classical.move_requires (congruence_lemma_3 op x y))
  
/// The notion of absorbing element, or absorber, is the generalization of integer zero with respect to multiplication
/// That is, 0x = x0 = 0. Other exmaples are the empty set w.r.t. intersection, 1 w.r.t. GCD in naturals, etc.
[@@"opaque_to_smt"]
let is_absorber_of (#a:Type) 
                   (z:a) 
                   (#eq: equivalence_relation a) 
                   (op: op_with_congruence eq) 
  = forall (x:a). ((x `op` z) `eq` z) && ((z `op` x) `eq` z)

unfold type absorber_of (#a:Type) (#eq: equivalence_relation a) (op: op_with_congruence eq)
  = z:a{is_absorber_of z op}
  
unfold type non_absorber_of (#a:Type) (#eq: equivalence_relation a) (op: op_with_congruence eq)
  = z:a{~(is_absorber_of z op)}
  
let absorber_equal_is_absorber (#a:Type) (#eq: equivalence_relation a) 
                               (op: op_with_congruence eq) (z1 z2: a) 
  : Lemma (requires is_absorber_of z1 op /\ (eq z1 z2 \/ eq z2 z1)) 
          (ensures is_absorber_of z2 op) =             
  let absorber_eq_is_abs (#a:Type)  (#eq: equivalence_relation a) (op: op_with_congruence eq) (z1: absorber_of op) (z2: a{z2 `eq` z1}) (t: a) 
    : Lemma (t `op` z2 `eq` z2 /\ z2 `op` t `eq` z2) =   
    reveal_opaque (`%is_absorber_of) (is_absorber_of #a);
    reveal_opaque (`%is_transitive) (is_transitive #a); 
    reveal_opaque (`%is_symmetric) (is_symmetric #a); 
    congruence_lemma_3 op z1 z2 t in
  reveal_opaque (`%is_symmetric) (is_symmetric #a);
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a);
  FStar.Classical.forall_intro (absorber_eq_is_abs op z1 z2)
  
let absorber_lemma (#a:Type) (#eq: equivalence_relation a) (op: op_with_congruence eq) (z: a) (x:a)
  : Lemma (requires is_absorber_of z op) 
          (ensures (z `op` x) `eq` z /\ (x `op` z) `eq` z /\ 
                   is_absorber_of (op x z) op /\ 
                   is_absorber_of (op z x) op) = 
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a);  
  absorber_equal_is_absorber op z (op x z);
  absorber_equal_is_absorber op z (op z x)

/// Proving that in any magma, there may not be 2 distinct absorbers, is left as an exercise
/// to both Z3 and the reader. And Z3 is doing fine on that count, just saying.
let absorber_is_unique (#a:Type) (#eq: equivalence_relation a) 
                       (op: op_with_congruence eq) (z1 z2: a) 
  : Lemma (requires is_absorber_of z1 op /\ is_absorber_of z2 op) 
          (ensures eq z1 z2 /\ eq z2 z1) = 
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a) 

/// This automatically propagates equality between all known observers
let absorber_is_unique_smt_lemma (#a:Type) (#eq: equivalence_relation a) 
                                 (op: op_with_congruence eq) (z1 z2: a)
  : Lemma (requires is_absorber_of z1 op /\ is_absorber_of z2 op) 
          (ensures eq z1 z2 /\ eq z2 z1)  
          [SMTPat(is_absorber_of z1 op /\ is_absorber_of z2 op)]
          = absorber_is_unique op z1 z2
   
let absorber_equal_is_absorber_req (#a:Type)
                                   (#eq: equivalence_relation a) 
                                   (op: op_with_congruence eq) (z1 z2: a) 
  : Lemma (requires is_absorber_of z1 op /\ eq z1 z2) 
          (ensures is_absorber_of z2 op) = 
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a);           
  absorber_equal_is_absorber op z1 z2
  
let nonabsorber_equal_is_nonabsorber (#a:Type) (#eq: equivalence_relation a)
                                     (op: op_with_congruence eq) 
                                     (p q: a) 
  : Lemma (requires (~(is_absorber_of p op)) /\ (q `eq` p \/ p `eq` q)) 
          (ensures ~(is_absorber_of q op)) = 
  reveal_opaque (`%is_symmetric) (is_symmetric #a);     
  Classical.move_requires (absorber_equal_is_absorber_req op q) p

/// Since we are using custom equivalence relation, we specifically assure the existence of
/// the unit. We also write "forall" since, for example, for fractions, there'll also be neutral
/// elements of type a/a, b/b... for nonzero (a, b...), unless we operate in a euclidean domain
/// that offers the algorithm for GCD computation and thus the notion of reduced fractions.
///
/// For arbitrary domains, there is no hope of reduced fractions, so the notions for inverses and neutrals
/// stays in its most general form.
[@@"opaque_to_smt"]
let is_inverse_operation_for (#a: Type) (#eq: equivalence_relation a) 
                             (inv: unary_op_with_congruence eq) 
                             (op: op_with_congruence eq)
  = (forall (x:a). is_neutral_of (op x (inv x)) op /\ is_neutral_of (op (inv x) x) op)

/// The inverse operation type is also a refinement for arbitrary unary operation 
type inverse_op_for (#a: Type) (#eq: equivalence_relation a) (op: op_with_congruence eq)
  = (inv:unary_op_with_congruence eq{is_inverse_operation_for inv op})

let inverse_operation_lemma (#a:Type) (#eq: equivalence_relation a) 
                            (#op: op_with_congruence eq) 
                            (inv: inverse_op_for op) 
                            (x: a) 
  : Lemma (is_neutral_of (x `op` inv x) op /\ is_neutral_of (inv x `op` x) op) =
  reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #a #eq)

let inverses_produce_neutral (#a:Type) (#eq: equivalence_relation a) 
                             (#op: op_with_congruence eq) 
                             (inv: inverse_op_for op) 
                             (x y: a)
  : Lemma (requires inv x `eq` y)
          (ensures is_neutral_of (op x y) op /\ 
                   is_neutral_of (op y x) op) =
    reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #a #eq);
    congruence_lemma_3 op (inv x) y x;
    neutral_equivalent_is_neutral op (x `op` inv x) (x `op` y);
    neutral_equivalent_is_neutral op (inv x `op` x) (y `op` x)

private let cancellation_lemma_left (#a:Type) (#eq: equivalence_relation a) 
                                    (#op: op_with_congruence eq{is_associative op})
                                    (inv: inverse_op_for op) 
                                    (x y z:a) 
  : Lemma (requires eq (op x z) (op y z)) (ensures eq x y /\ eq y x) =    
  reveal_opaque (`%is_transitive) (is_transitive #a);
  reveal_opaque (`%is_associative) (is_associative op); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  let z'  = inv z in
  let zz' = op z z' in                            // suppose zz'    = 1 (always possible in a group)
  let xz, yz = x `op` z, y `op` z in              // we have xz     = yz   
  congruence_lemma_3 op xz yz z';                 // then,   (xz)z' = (yz)z'  >(assoc)>   x(zz') = (yz)z'
  inverse_operation_lemma inv z;                  // as we defined, zz'= 1
  neutral_lemma op zz' x;                         // zz'=1,  (zz')x = x
  // trans_lemma eq (xz `op` z') (x `op` zz') x;  // transitivity, (xz)z' = x(zz') = x, (xz)z'=x
  // trans_lemma eq x (xz `op` z') (yz `op` z');  // transitivity, x = (xz)z' = (yz)z'
  // associative_operation_lemma eq op y z z';    // assoc again, (yz)z' = y(zz') 
  neutral_lemma op zz' y;                         // neutral again, y(zz')=y.
  ()                                              // the rest is left as an exercise for Z3


private let cancellation_lemma_right (#a:Type) (#eq: equivalence_relation a) 
                                     (#op: op_with_congruence eq{is_associative op})
                                     (inv: inverse_op_for op) 
                                     (x y z:a) 
  : Lemma (requires (op z x `eq` op z y) \/ (op z y `eq` op z x)) 
          (ensures eq x y /\ eq y x) =
  reveal_opaque (`%is_symmetric) (is_symmetric eq); 
  reveal_opaque (`%is_transitive) (is_transitive eq); // we're going to need the transitivity of ==
  reveal_opaque (`%is_associative) (is_associative op); // we're going to need the transitivity of ==
  inverse_operation_lemma inv z;      
  neutral_lemma op (op (inv z) z) x;
  neutral_lemma op (op (inv z) z) y;
  congruence_lemma_3 op (op z x) (op z y) (inv z) 

let cancellation_lemma (#a:Type) (#eq: equivalence_relation a)
                                 (#op: op_with_congruence eq{is_associative op}) 
                                 (inv: inverse_op_for op) 
                                 (x y z: a)
  : Lemma (requires (op z x `eq` op z y) \/ (op x z `eq` op y z))
          (ensures eq x y /\ eq y x) = 
  if ((z `op` x) `eq` (z `op` y)) 
  then cancellation_lemma_right inv x y z
  else cancellation_lemma_left inv x y z

let producing_neutral_means_inverses (#a:Type) 
                                     (#eq: equivalence_relation a) 
                                     (#op: op_with_congruence eq{is_associative op}) 
                                     (inv: inverse_op_for op) 
                                     (x y: a)
  : Lemma (requires is_neutral_of (op x y) op \/ is_neutral_of (op y x) op) 
          (ensures inv x `eq` y /\ x `eq` inv y) =   
  reveal_opaque (`%congruence_condition) (congruence_condition op); 
  reveal_opaque (`%is_symmetric) (is_symmetric eq); 
  reveal_opaque (`%is_transitive) (is_transitive eq); 
  reveal_opaque (`%is_associative) (is_associative op);
  let aux_xy () : Lemma (requires is_neutral_of (op x y) op) 
                        (ensures (eq (inv x) y /\ eq x (inv y))) =  
    inverse_operation_lemma inv y;
    inverse_operation_lemma inv x;
    neutral_is_unique op  (inv y `op` y) (x `op` y);
    cancellation_lemma inv (inv y) x y;
    congruence_lemma_3 op (y `op` inv y) (y `op` x) (inv x);  
    neutral_lemma op (y `op` inv y) (inv x);  
    congruence_lemma_3 op ((y `op` x) `op` inv x) (y `op` (x `op` inv x)) (inv x);
    neutral_lemma op   (x `op` inv x) y 
  in Classical.move_requires aux_xy ();    
  let aux_yx () : Lemma (requires is_neutral_of (op y x) op) 
                        (ensures (eq (inv x) y /\ eq x (inv y))) =  
    inverse_operation_lemma inv y;
    inverse_operation_lemma inv x;
    neutral_is_unique op (op y (inv y)) (y `op` x);
    cancellation_lemma inv x (inv y) y;
    congruence_lemma_3 op (y `op` inv y) (y `op` x) (inv x);  
    neutral_lemma op (y `op` inv y) (inv x);  
    neutral_lemma op (x `op` inv x) y 
  in Classical.move_requires aux_yx ()

/// This was written when F* was in a broken state, overwhelmed by facts
/// from definitions when they weren't opaque to SMT.
///
/// If you ever feel the need to invoke this directly, you're in trouble. 
let equivalence_lemma_from_implications (#a:Type) (p) (q)
                                        (to_right : (x:a)->(y:a)->Lemma (requires p x y) (ensures q x y))
                                        (to_left  : (x:a)->(y:a)->Lemma (requires q x y) (ensures p x y))
                                        (x:a) (y:a)
                                        : Lemma (p x y <==> q x y) = 
                                        Classical.move_requires_2 to_left x y;
                                        Classical.move_requires_2 to_right x y

/// Most general collection of facts about inverses
let inverse_element_defining_lemma (#a:Type) (#eq: equivalence_relation a) 
                                   (op: op_with_congruence eq{is_associative op}) 
                                   (inv: inverse_op_for op) (x y: a)
  : Lemma ((is_neutral_of (x `op` y) op <==> inv x `eq` y) /\
           (is_neutral_of (x `op` y) op <==> inv y `eq` x) /\
           (is_neutral_of (y `op` x) op <==> inv x `eq` y) /\
           (is_neutral_of (y `op` x) op <==> inv y `eq` x)) = 
  (FStar.Classical.move_requires_2 (inverses_produce_neutral inv)) x y;
  (FStar.Classical.move_requires_2 (producing_neutral_means_inverses inv)) x y;
  (FStar.Classical.move_requires_2 (inverses_produce_neutral inv)) y x;
  (FStar.Classical.move_requires_2 (producing_neutral_means_inverses inv)) y x
 
/// We shall generally keep in mind that distributivity laws must be considered separately
/// If in future we consider K[x] with multiplication f(x)*g(x) defined as composition f(g(x)),
/// we will do well to remember that only one of the two distributivities holds there.
[@@"opaque_to_smt"]
let is_left_distributive (#a:Type) (#eq: equivalence_relation a) 
                         (op_mul: op_with_congruence eq) 
                         (op_add: op_with_congruence eq) =
  forall (x y z:a). (x `op_mul` (y `op_add` z)) `eq` ((x `op_mul` y) `op_add` (x `op_mul` z))
  
[@@"opaque_to_smt"]
let is_right_distributive (#a:Type) (#eq: equivalence_relation a) 
                          (op_mul: op_with_congruence eq) 
                          (op_add: op_with_congruence eq) =
  forall (x y z:a). ((x `op_add` y) `op_mul` z) `eq` ((x `op_mul` z) `op_add` (y `op_mul` z))
  
[@@"opaque_to_smt"]
let is_fully_distributive (#a:Type) (#eq: equivalence_relation a) 
                          (op_mul: op_with_congruence eq) 
                          (op_add: op_with_congruence eq) =
  forall (x y z:a). ((x `op_mul` (y `op_add` z)) `eq` ((x `op_mul` y) `op_add` (x `op_mul` z))) /\ 
               (((x `op_add` y) `op_mul` z) `eq` ((x `op_mul` z) `op_add` (y `op_mul` z)))

let fully_distributive_is_both_left_and_right (#a:Type) (#eq: equivalence_relation a) 
                                              (op_mul: op_with_congruence eq) 
                                              (op_add: op_with_congruence eq) 
  : Lemma (is_fully_distributive op_mul op_add <==> is_left_distributive op_mul op_add /\ is_right_distributive op_mul op_add)  
  (* Notice how reveal_opaque      (`%is_left_distributive) (is_left_distributive op_mul)
     is effectively equivalent to  (`%is_left_distributive) (is_left_distributive op_mul op_add)

     From here, we will omit op_add in reveal_opaque invokes -- as well as any 
     additional parameters that are redundant.

     TECHNICALLY specifying them explicitly should speed up the verification process,
     but in practice, I expect the performance gains to be negligible. *)     
  = reveal_opaque (`%is_left_distributive) (is_left_distributive op_mul op_add);  
    reveal_opaque (`%is_right_distributive) (is_right_distributive op_mul);
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive op_mul)

let left_distributivity_lemma (#a:Type) (#eq: equivalence_relation a) 
                              (op_mul: op_with_congruence eq) 
                              (op_add: op_with_congruence eq) 
                              (x y z: a)
  : Lemma (requires is_left_distributive op_mul op_add \/ is_fully_distributive op_mul op_add) 
          (ensures (x `op_mul` (y `op_add` z)) `eq` ((x `op_mul` y) `op_add` (x `op_mul` z))) 
  = reveal_opaque (`%is_left_distributive) (is_left_distributive op_mul);
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive op_mul)

let right_distributivity_lemma (#a:Type) (#eq: equivalence_relation a) 
                               (op_mul: op_with_congruence eq) 
                               (op_add: op_with_congruence eq) 
                               (x y z: a)
  : Lemma (requires is_right_distributive op_mul op_add \/ is_fully_distributive op_mul op_add) 
          (ensures ((x `op_add` y) `op_mul` z) `eq` ((x `op_mul` z) `op_add` (y `op_mul` z))) 
  = reveal_opaque (`%is_right_distributive) (is_right_distributive op_mul);
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive op_mul) 

/// Domain defining property (the alternative form is the Cancellation Law, (ax=bx ==> (x=0 \/ a=b)
[@@"opaque_to_smt"]
let has_no_zero_divisors (#a:Type) (#eq: equivalence_relation a) (zero:a) (mul: op_with_congruence eq) =
  forall (x y:a). ((x `mul` y) `eq` zero) ==> (x `eq` zero) \/ (y `eq` zero)
  
/// For future reference, we difine what it means for divisor to divide dividend
[@@"opaque_to_smt"]
let is_divisor_of (#a:Type) (#eq: equivalence_relation a) (op: op_with_congruence eq) 
                  (divisor: a) (dividend: a) = 
  exists (quotient: a). (quotient `op` divisor) `eq` dividend

/// If we want to reason about divisors without revealing the opaque,
let inst_divides (#a:Type) (#eq: equivalence_relation a) 
                 (op: op_with_congruence eq) 
                 (y x: a) (z:a{(z `op` y) `eq` x})
  : Lemma (is_divisor_of op y x) = reveal_opaque (`%is_divisor_of) (is_divisor_of op) 
   
/// This will soon be used as we'll represent elements in form of x=(unit_part)*(normal_part)
/// where (unit_part) is a ring unit, and (normal_part) is, roughly speaking, (unit_part⁻¹ * x),
/// so that normal part would represent absolute value, monic polynomial, etc.
/// 
/// If you're curious as to where did these (not so often used!) notions came from, see
/// Keith O. Geddes, Stephen R. Czapor, George Labahn -- "Algorithms for Computer Algebra",
/// section 2.3 Divisibility and factorization in integral domains.
/// 
/// BTW you'll find quite a lot of interesting notions besides unit/normal there.
/// If you are still reading this, you'll probably find a lot of joy skimming through
/// that book. Seriously, check it out.
///
/// Invertible elements in a ring are called units, and here's their defining condition.
/// In perspective, it would be wise to define the multiplicative group of a ring,
/// but I currently just don't know whether constructively providing it is simple enough
/// to be included as a prerequisite to ring construction.
///
/// I call for help on this matter. Dear algebraists, your advise on architecture is needed here :)

[@@"opaque_to_smt"]
let is_unit (#a: Type) (x: a) (#eq: equivalence_relation a) (op:op_with_congruence eq) 
  = exists (y:a). (is_neutral_of (x `op` y) op /\ is_neutral_of (y `op` x) op)
 
/// We call the two elements associated if they divide each other
let are_associated (#a: Type) (p: a) (q: a) (#eq: equivalence_relation a) (mul:op_with_congruence eq) 
  = (is_divisor_of mul p q) /\ (is_divisor_of mul q p) 

/// We also define in advance the notions of irreducibles and primes
/// We don't tell one from the other in Z, but in general, they are not the same thing.
[@@"opaque_to_smt"]
let is_irreducible (#a: Type) (x: a) (#eq: equivalence_relation a) (mul: op_with_congruence eq) = 
  (~(is_unit x mul)) /\
  (exists (neutral: a). is_neutral_of neutral mul) /\  
  (forall (p q: a). ((q `mul` p) `eq` x) ==> ((are_associated p x mul) /\ (is_unit q mul)) 
                                        \/ ((are_associated q x mul) /\ (is_unit p mul)))
                                        
[@@"opaque_to_smt"]                                     
let is_prime (#a: Type) (p: a) (#eq: equivalence_relation a) (mul: op_with_congruence eq)  = 
  (~(is_unit p mul)) /\ (forall (m n: a). (is_divisor_of mul p (m `mul` n)) ==> ((is_divisor_of mul p m) \/ (is_divisor_of mul p n)))

type units_of (#a: Type) (#eq: equivalence_relation a) (mul: op_with_congruence eq) = x:a{is_unit x mul}

let unit_product_is_unit_new #a (#eq: equivalence_relation a) 
                             (mul: op_with_congruence eq{is_associative mul})
                             (x y: units_of mul)
  : Lemma (is_unit (mul x y) mul) = 
  reveal_opaque (`%is_unit) (is_unit #a);
  reveal_opaque (`%is_transitive) (is_transitive eq);
  let ( * ) = mul in
  let ( = ) = eq in
  eliminate exists (x' y':a). (is_neutral_of (x'*x) mul /\ is_neutral_of (x*x') mul  
                        /\ is_neutral_of (y'*y) mul /\ is_neutral_of (y*y') mul)
  returns is_unit (x*y) mul with _.
  begin
    calc (=) {
      (y'*x')*(x*y); = { assoc_lemma_3 mul y' x' (x*y) }
      y'*(x'*(x*y)); = { assoc_lemma_3 mul x' x y;
                         congruence_lemma_3 mul (x'*(x*y)) ((x'*x)*y) y' }
      y'*((x'*x)*y); = { neutral_lemma mul (x'*x) y;
                         congruence_lemma_3 mul ((x'*x)*y) y y' }
      y'*y;
    }; 
    neutral_equivalent_is_neutral mul (y'*y) ((y'*x')*(x*y)); // left inverse 
    calc (=) {
      (x*y)*(y'*x'); = { assoc_lemma_4 mul x y y' x' }
      x*((y*y')*x'); = { neutral_lemma mul (y*y') x';                         
                         congruence_lemma_3 mul ((y*y')*x') x' x }
      x*x';
    };  
    neutral_equivalent_is_neutral mul (x*x') ((x*y)*(y'*x')); // right inverse
    () // has both inverses ==> is unit.
  end
  

let unit_product_is_unit (#a:Type) (#eq: equivalence_relation a) (mul: op_with_congruence eq{is_associative mul}) (x y: units_of mul)
  : Lemma (is_unit (mul x y) mul) = 
    reveal_opaque (`%is_symmetric) (is_symmetric eq);
    reveal_opaque (`%is_transitive) (is_transitive eq);
    reveal_opaque (`%is_reflexive) (is_reflexive eq);
    reveal_opaque (`%is_associative) (is_associative mul);
    reveal_opaque (`%is_unit) (is_unit #a);
    let op = mul in 
    let x' = IndefiniteDescription.indefinite_description_ghost (units_of mul) 
             (fun x' -> (is_neutral_of (x `op` x') op /\ is_neutral_of (x' `op` x) op)) in
    let y' = IndefiniteDescription.indefinite_description_ghost (units_of mul) 
             (fun y' -> (is_neutral_of (y `op` y') op /\ is_neutral_of (y' `op` y) op)) in
    let inv = op y' x' in
    let full = op (op y' x') (op x y) in 
    assoc_lemma_4 op y' x' x y; 
    neutral_lemma op (x' `op` x) y;
    congruence_lemma_3 op ((x' `op` x) `op` y) y y';  
    neutral_equivalent_is_neutral op (y' `op` y) full;
    neutral_lemma op full full;
    assoc_lemma_4 op x y y' x';
    neutral_lemma op (y `op` y') x;
    congruence_lemma_3 op (x `op` (y `op` y')) x x'; 
    neutral_equivalent_is_neutral op (x `op` x') ((x `op` y) `op` (y' `op` x'));   
  ()

type unary_op_on_units_of (#a:Type) (#eq: equivalence_relation a) (mul: op_with_congruence eq) =
  unary_op_with_congruence #(units_of mul) (    
     reveal_opaque (`%is_reflexive) (is_reflexive #a); 
     reveal_opaque (`%is_reflexive) (is_reflexive #(units_of mul)); 
     reveal_opaque (`%is_symmetric) (is_symmetric #a);   
     reveal_opaque (`%is_symmetric) (is_symmetric #(units_of mul));   
     reveal_opaque (`%is_transitive) (is_transitive #a);
     reveal_opaque (`%is_transitive) (is_transitive #(units_of mul));
     eq)
 
let yields_inverses_for_units (#a:Type) (#eq: equivalence_relation a) 
                              (#op: op_with_congruence eq) 
                              (inv: unary_op_on_units_of op) = 
  forall (x: units_of op). is_neutral_of (op (inv x) x) op /\ 
                      is_neutral_of (op x (inv x)) op 

type partial_inverse_op_for (#a:Type) (#eq: equivalence_relation a) 
                            (op: op_with_congruence eq) 
  = (f: unary_op_on_units_of op {yields_inverses_for_units f})

let inverse_is_unique (#a:Type) (#eq: equivalence_relation a) 
                      (#op: op_with_congruence eq{is_associative op}) 
                      (inv: partial_inverse_op_for op)
                      (x inv1 inv2: a)
  : Lemma (requires is_neutral_of (inv1 `op` x) op 
                  /\ is_neutral_of (x `op` inv1) op 
                  /\ is_neutral_of (inv2 `op` x) op
                  /\ is_neutral_of (x `op` inv2) op)
          (ensures (eq inv1 inv2 /\ eq inv2 inv1)) = 
  reveal_opaque (`%is_associative) (is_associative op);
  reveal_opaque (`%is_transitive) (is_transitive eq);
  let (x, y, z) = (inv1, inv2, x) in
  neutral_lemma op (x `op` z) y;
  neutral_lemma op (z `op` y) x;
  trans_lemma eq x ((x `op` z) `op` y) y
                            
let unit_inverse_is_unit (#a:Type) (#eq: equivalence_relation a) 
                         (#op: op_with_congruence eq{is_associative op}) 
                         (inv: partial_inverse_op_for op)
                         (x: units_of op)
  : Lemma (is_unit (inv x) op) = reveal_opaque (`%is_unit) (is_unit #a)

let all_are_units (#a:Type) (#eq: equivalence_relation a) 
                  (op: op_with_congruence eq{is_associative op}) = forall (x:a). is_unit x op

noeq type magma (a: Type) =  
{
  eq: equivalence_relation a;
  op: op_with_congruence eq;
  inv: unary_op_on_units_of op;
  neutral: a
}

let magma_inv_respects_eq (#a:Type) (m: magma a) : Lemma (  
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  reveal_opaque (`%is_reflexive) (is_reflexive #(units_of m.op)); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  reveal_opaque (`%is_symmetric) (is_symmetric #(units_of m.op));   
  reveal_opaque (`%is_transitive) (is_transitive #a);
  reveal_opaque (`%is_transitive) (is_transitive #(units_of m.op)); 
  unary_congruence_condition #(units_of m.op) m.inv m.eq) = ()

type semigroup (a:Type)             = g: magma a{is_associative g.op /\ yields_inverses_for_units g.inv}
type commutative_magma (a:Type)     = g: magma a{is_commutative g.op}
type commutative_semigroup (a:Type) = g: semigroup a{is_commutative g.op}
type monoid (a:Type)                = g: semigroup a{is_neutral_of g.neutral g.op}
type commutative_monoid (a:Type)    = g: monoid a{is_commutative g.op}
type group (a:Type)                 = g: (m:monoid a{all_are_units m.op}){is_inverse_operation_for #a ( 
  reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #a); 
  reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #(units_of g.op));
//  reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #a #g.eq);  
g.inv) g.op}
type commutative_group (a:Type)     = g: group a{is_commutative g.op}

let partial_inverse_lemma (#a:Type) (#eq: equivalence_relation a) 
                          (mul: op_with_congruence eq{is_associative mul}) 
                          (f: unary_op_on_units_of mul {yields_inverses_for_units f}) 
                          (x: units_of mul) 
  : Lemma(is_neutral_of (mul x (f x)) mul /\ is_neutral_of (mul (f x) x) mul) = ()

let yields_inverses_for_units_lemma (a:Type) (sg: semigroup a) 
  : Lemma (yields_inverses_for_units sg.inv) = ()

let group_elements_are_all_units (#a:Type) (g: group a) 
  : Lemma (forall (x:a). is_unit x g.op) = ()

let group_inv_is_complete_l (#a:Type) (g: group a) (x:a)
  : Lemma (is_neutral_of (x `g.op` g.inv x) g.op /\
           is_neutral_of (g.inv x `g.op` x) g.op) = ()

let group_inv_congruence_condition (#a:Type) (g: group a) : Lemma (unary_congruence_condition (
  reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #a); 
  reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #(units_of g.op)); 
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  reveal_opaque (`%is_reflexive) (is_reflexive #(units_of g.op)); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  reveal_opaque (`%is_symmetric) (is_symmetric #(units_of g.op));   
  reveal_opaque (`%is_transitive) (is_transitive #a);
  reveal_opaque (`%is_transitive) (is_transitive #(units_of g.op));
g.inv) g.eq) = ()

let group_inv_op (#a:Type) (g: group a) : inverse_op_for g.op =
  group_inv_congruence_condition g;
  (reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #a); 
  reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #(units_of g.op));
  reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #a #g.eq); 
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  reveal_opaque (`%is_reflexive) (is_reflexive #(units_of g.op)); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  reveal_opaque (`%is_symmetric) (is_symmetric #(units_of g.op));   
  reveal_opaque (`%is_transitive) (is_transitive #a);
  reveal_opaque (`%is_transitive) (is_transitive #(units_of g.op)); 
  g.inv)
                                                        
let group_inverse_lemma (#a:Type) (g: group a) 
  : Lemma (is_inverse_operation_for #a #g.eq
  (
  group_inv_congruence_condition g;
  group_inv_op g) g.op) = 
  reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #a #g.eq);  
  ()
  
let group_inv_is_complete (#a:Type) (g: group a) 
  : Lemma (is_inverse_operation_for #a (
    reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #a); 
    reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #(units_of g.op)); 
    g.inv) g.op) 
  [SMTPat((g.inv))]
  = reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #a #g.eq)
 
let magma_associativity_smt_lemma (#a:Type) (g: magma a{is_associative g.op}) (x y z:a) 
  : Lemma ((x `g.op` (y `g.op` z)) `g.eq` ((x `g.op` y) `g.op` z) /\ 
          ((x `g.op` y) `g.op` z) `g.eq` (x `g.op` (y `g.op` z)))
   [SMTPatOr [[ SMTPat (x `g.op` (y `g.op` z)); SMTPat ((x `g.op` y) `g.op` z) ]]] =
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  reveal_opaque (`%is_associative) (is_associative g.op)

let magma_commutativity_smt_lemma (#a:Type) (g: magma a{is_commutative g.op}) (x y:a) 
  : Lemma ((x `g.op` y) `g.eq` (y `g.op` x) /\ (y `g.op` x) `g.eq` (x `g.op` y))
   [SMTPatOr [[ SMTPat (x `g.op` y); SMTPat (y `g.op` x) ]]] =
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  reveal_opaque (`%is_commutative) (is_commutative g.op)

let magma_operation_respects_eq_smt_lemma (#a:Type) (g: magma a) (x y z: a) 
  : Lemma (requires x `g.eq` y)
          (ensures (z `g.op` x) `g.eq` (z `g.op` y) /\
                   (z `g.op` y) `g.eq` (z `g.op` x) /\
                   (x `g.op` z) `g.eq` (y `g.op` z) /\
                   (y `g.op` z) `g.eq` (x `g.op` z))
          [SMTPatOr [
                    [SMTPat(g.op z x); SMTPat(g.eq x y)]; 
                    [SMTPat(g.op x z); SMTPat(g.eq x y)]; 
                    [SMTPat(g.op z y); SMTPat(g.eq x y)]; 
                    [SMTPat(g.op y z); SMTPat(g.eq x y)]
          ]] = congruence_lemma_3 g.op x y z                                                        


let monoid_neutral_smt_lemma (#a:Type) (g: monoid a) (x: a) 
  : Lemma (x `g.op` g.neutral `g.eq` x /\ g.neutral `g.op` x `g.eq` x)
    [SMTPatOr[ [SMTPat(g.op x g.neutral)]; [SMTPat(g.op g.neutral x)] ]] 
  = neutral_lemma g.op g.neutral x
    
let monoid_neutral_smt_lemma_2 (#a:Type) (g:monoid a) (x: a) (y:a) 
  : Lemma (requires is_neutral_of y g.op)
          (ensures g.op x y `g.eq` x /\ g.op y x `g.eq` x)
    [SMTPatOr[
      [SMTPat(g.op x y)];
      [SMTPat(g.op y x)]
    ]] = neutral_lemma g.op y x
    
let magma_absorber_smt_lemma_2 (#a:Type) (m: magma a) (x y:a) 
  : Lemma (requires is_absorber_of x m.op) 
          (ensures m.op x y `m.eq` x /\ m.op y x `m.eq` x)
    [SMTPatOr[
      [SMTPat(m.op x y)];
      [SMTPat(m.op y x)]
    ]] = absorber_lemma m.op x y

let group_inverse_smt_lemma (#a:Type) (g: group a) (x: a) 
  : Lemma (ensures g.op x (g.inv x) `g.eq` g.neutral /\
                   g.op (g.inv x) x `g.eq` g.neutral /\
                   is_neutral_of (g.op x (g.inv x)) g.op /\
                   is_neutral_of (g.op (g.inv x) x) g.op) 
    [SMTPatOr[
      [SMTPat(g.op x (g.inv x))];
      [SMTPat(g.op (g.inv x) x)]
    ]] =   
  reveal_opaque (`%is_symmetric) (is_symmetric #a);  
  group_elements_are_all_units g;
  neutral_is_unique g.op g.neutral (g.op x (g.inv x));
  neutral_is_unique g.op g.neutral (g.op (g.inv x) x)
                                                                            

let group_operation_cancellation_smt_lemma (#a:Type) (g: group a) (e1 e2 x:a) 
  : Lemma (requires g.eq (g.op e1 x) (g.op e2 x) \/ g.eq (g.op x e1) (g.op x e2))
          (ensures g.eq e1 e2)
          [SMTPatOr[
            [SMTPat(g.eq (g.op e1 x) (g.op e2 x))];
            [SMTPat(g.eq (g.op x e1) (g.op x e2))]
          ]] =   
  group_inv_is_complete g;
  reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #a); 
  reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #(units_of g.op)); 
  cancellation_lemma #a #g.eq #g.op g.inv e1 e2 x
  
let absorber_never_equals_non_absorber (#a: Type) (#eq: equivalence_relation a) (op: op_with_congruence eq) 
  (x: absorber_of op) (y: non_absorber_of op) : Lemma (~(x `eq` y)) = 
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  if (x `eq` y) then absorber_equal_is_absorber op x y

let absorber_nonequal_is_nonabsorber (#a:Type) 
                                     (#eq: equivalence_relation a) 
                                     (op: op_with_congruence eq) 
                                     (x: absorber_of op) (y: a)
  : Lemma (~(eq x y) \/ ~(eq y x)  ==> ~(is_absorber_of y op)) = 
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a);   
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  reveal_opaque (`%is_transitive) (is_transitive #a) //but why and how?!
  
unfold let is_absorber_of_magma (#a:Type) (z: a) (m: magma a) = is_absorber_of z m.op 

/// When I try to keep the rlimit at minimum, lemmas like this one sometimes help
let neutral_inverse_is_neutral (#a:Type) (g: group a) : Lemma (g.neutral `g.eq` (g.inv g.neutral)) =  
  reveal_opaque (`%is_transitive) (is_transitive #a);
  // you should keep alive either the assertion, or the inverse_operation_lemma invocation.
  // disabling both will fail the lemma. Keeping both is redundant. SMTPat, I can't understand how you tick.
  // 
  // UPD 11.10.21: with FStar 2021.09.25 it only takes reveal_opaque. No assertion needed anymore.
  //
  assert (is_neutral_of (g.op (g.inv g.neutral) g.neutral) g.op)
  //inverse_operation_lemma g.op g.eq g.inv g.neutral 
  //group_operation_lemma g.eq g.op g.inv (g.inv g.neutral) g.neutral g.neutral

let group_op_lemma (#a:Type) (g: group a) (x y z:a) 
  : Lemma (requires (x `g.op` z) `g.eq` (y `g.op` z) \/ (z `g.op` x) `g.eq` (z `g.op` y)) 
          (ensures (x `g.eq` y /\ y `g.eq` x)) 
  = () // group_operation_lemma g.eq g.op g.inv x y z 
       // SMTPat eliminated the need to call the lemma explicitly.

 
let group_element_equality_means_zero_difference (#a:Type) (g: group a) (x y: a) 
  : Lemma (x `g.eq` y <==> (x `g.op` g.inv y) `g.eq` g.neutral) = 
  // SMTPat says "no need to be so verbose anymore. But I keep this because I know better.
  // inverse_operation_lemma g.op g.eq g.inv y;                   
  // neutral_is_unique g.op g.eq  (g.op y (g.inv y)) g.neutral;   
  if (x `g.eq` y) then begin
    congruence_lemma_3 g.op x y (g.inv y);
    //assert ((x `g.op` g.inv y) `g.eq` (y `g.op` g.inv y));
    trans_lemma g.eq (x `g.op` g.inv y) (y `g.op` g.inv y) g.neutral
  end else begin
    if ((x `g.op` g.inv y) `g.eq` g.neutral) then begin 
      trans_lemma g.eq (x `g.op` g.inv y) g.neutral (y `g.op` g.inv y);
      group_op_lemma  g x y (g.inv y)
    end
  end

let absorber_for_invertible_operation_is_nonsense (#a:Type) (#eq: equivalence_relation a) (#op: op_with_congruence eq)  (inv: inverse_op_for op)
   (y: non_absorber_of op) (z:a) : Lemma (requires is_absorber_of z op) (ensures False) =   
    reveal_opaque (`%is_absorber_of) (is_absorber_of #a);  
    //absorber_never_equals_non_absorber op eq z y;
    let z' = inv z in
    let zz' = op z z' in
    //absorber_lemma op eq z z';
    inverse_operation_lemma inv z;                 // zz' is the neutral element
    let yzz' = op y zz' in                         // I write "the absorber" here to underline its uniqueness
    //absorber_lemma op eq z z';                        
                                                   (** 1. By definition of absorber, zz' should be equal to z.      *)
    //absorber_lemma op eq zz' y;
    absorber_equal_is_absorber op z zz';           (** 2. Any element equal to an absorber is the absorber,         *)
                                                   (**    therefore, zz' is also the absorber, since zz' = z.       *)
    (* assert (is_neutral_of zz' op eq); *)        (** 3. By definition of inverse, zz' is the neutral element.     *)
    (* assert (yzz' `eq` y);             *)        (** 4. By definition of neutral element (zz'), yzz' = y          *)
                                                   (**    This assertion somehow slowed* down the prover a lot!     *)
    (* assert (yzz' `eq` zz');           *)        (** 5. But as zz' is the absorber, yzz' = zz'!                   *)
    absorber_equal_is_absorber op zz' yzz';        (** 6. Being equal to the absorber zz', yzz' is the absorber     *)
    neutral_lemma op zz' y;                        (** 7. But, as an equal of y, yzz' can't be an absorber!         *) 
    nonabsorber_equal_is_nonabsorber op y yzz';    (**    So, we have a contradiction here!                         *) 
//  assert (~(is_absorber_of yzz' op eq)); 
//  assert (is_absorber_of yzz' op eq);               (**    Deleting the last two asserts gave* 10x proof slowdown!   *)
//  * The slowdowns were noticed BEFORE the introduction of opaques. 
//  With opaques, most stuff here passes the verification with 0/0/1 resource settings
    ()    

let group_has_no_absorbers (#a:Type) (g: group a) (z:a) (y:non_absorber_of g.op) 
  : Lemma (~(is_absorber_of z g.op)) = 
  reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #a); 
  reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #(units_of g.op));
  reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #a #g.eq);  
  let ginv : inverse_op_for g.op = g.inv in  
  let nonsense_lemma (z:a) : Lemma (requires is_absorber_of z g.op) (ensures False) = 
    absorber_for_invertible_operation_is_nonsense ginv y z in
  Classical.move_requires nonsense_lemma z

/// In our pursuit of sanity, we only consider ring-like structures that are at least rigs,
/// with addition forming a commutative group, and multiplication forming a semigroup that
/// is fully (left and right) distributive over addition
/// 
/// Notice how, just like inverse group operation, the euclidean_norm field holds little meaning
/// until we get to Euclidean Domains, but we shall keep the record field in the base type
/// because there is no inheritance in F*. Unfortunately so, to say the least.

let nat_function_defined_on_non_absorbers (#a:Type) (#eq: equivalence_relation a) (op: op_with_congruence eq) 
  = f: (a -> (option nat)) { forall (x:a). (f x)=None ==> is_absorber_of x op }

let nat_function_value (#a:Type) (#eq: equivalence_relation a) (op: op_with_congruence eq) 
                       (f: nat_function_defined_on_non_absorbers op) (x: non_absorber_of op) : nat 
  = allow_inversion (option nat); Some?.v (f x)

[@@"opaque_to_smt"]
let has_no_absorber_divisors (#a:Type) (#eq: equivalence_relation a) (op: op_with_congruence eq)  
  = forall (x y: a). is_absorber_of (op x y) op <==> (is_absorber_of x op) \/ (is_absorber_of y op)

let domain_multiplication_law (#a:Type) (#eq: equivalence_relation a) (mul: op_with_congruence eq{has_no_absorber_divisors mul}) (x y: a)
  : Lemma (~(is_absorber_of x mul) /\ ~(is_absorber_of y mul) <==> ~ (is_absorber_of (mul x y) mul)) =   
    reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors mul)
 
let domain_multiplication_law_inv (#a:Type) (#eq: equivalence_relation a) (mul: op_with_congruence eq{has_no_absorber_divisors mul}) (x y: a)
  : Lemma ((is_absorber_of x mul) \/ (is_absorber_of y mul) <==> (is_absorber_of (mul x y) mul)) = 
    reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors mul) 
  
let euclidean_norm_property (#a:Type) (#eq: equivalence_relation a) 
                                      (op: op_with_congruence eq{has_no_absorber_divisors op}) 
                                      (x y: non_absorber_of op) 
                                      (f: nat_function_defined_on_non_absorbers op) = 
  domain_multiplication_law op x y;
  nat_function_value op f (op x y) >= nat_function_value op f x 

[@@"opaque_to_smt"]
let euclidean_norm_forall_property (#a:Type) (#eq: equivalence_relation a) 
                                   (op: op_with_congruence eq{has_no_absorber_divisors op}) 
                                   (f: nat_function_defined_on_non_absorbers op)
  = forall (x y: non_absorber_of op). euclidean_norm_property op x y f

type norm_function (#a:Type) (#eq: equivalence_relation a) (op: op_with_congruence eq{has_no_absorber_divisors op})
  = f: nat_function_defined_on_non_absorbers op{ forall (x y: non_absorber_of op). euclidean_norm_property op x y f }

let product_of_nonabsorbers_is_nonabsorber (#a:Type) (#eq: equivalence_relation a) 
                                           (op: op_with_congruence eq{has_no_absorber_divisors op}) 
                                           (x y: non_absorber_of op) 
  : Lemma (~(is_absorber_of (op x y) op) /\ ~(is_absorber_of (op y x) op)) =  
  reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors op) 
  
let euclidean_norm_main_lemma (#a: Type) (#eq: equivalence_relation a) 
                              (op: op_with_congruence eq{has_no_absorber_divisors op}) 
                              (f: norm_function op) 
                              (x y: non_absorber_of op)
  : Lemma (Some?.v (reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors op); 
                    allow_inversion (option nat);
                    f (op x y)) >= Some?.v (f x)) =
  assert (euclidean_norm_property op x y f)
   
unfold let eq_of #a (p: magma a) = p.eq

[@@"opaque_to_smt"]
let yields_units (#a: Type) (f: a->a) (#eq: equivalence_relation a) (op: op_with_congruence eq) 
 = forall (x:a). is_unit (f x) op 

let yields_units_lemma (#a: Type) (#eq: equivalence_relation a) (op: op_with_congruence eq) (f: (a->a){yields_units f op}) (x:a)
  : Lemma (is_unit (f x) op) = reveal_opaque (`%yields_units) (yields_units #a)

let unary_distributivity_condition (#a: Type) (#eq: equivalence_relation a) 
                                   (f: a->a) (op: op_with_congruence eq) (x y: a)
 = f (x `op` y) `eq` (f x `op` f y)

[@@"opaque_to_smt"]
let unary_distributes_over (#a: Type) (f: a->a) (#eq: equivalence_relation a) (op: op_with_congruence eq) = 
  forall (x y: a). unary_distributivity_condition f op x y

[@@"opaque_to_smt"]
let unary_over_nonzeros_distributes_over (#a: Type) 
                                         (#eq: equivalence_relation a) 
                                         (f: a->a) (op: op_with_congruence eq) = 
  forall (x y: non_absorber_of op). unary_distributivity_condition f op x y
 
[@@"opaque_to_smt"]
let is_neutral_invariant (#a: Type) (#eq: equivalence_relation a) 
                         (op: op_with_congruence eq) (f: a -> a) = 
  forall (x:a). (is_neutral_of x op ==> eq x (f x) /\ eq (f x) x)

let is_unit_part_function (#a: Type) (#eq: equivalence_relation a) (#op: op_with_congruence eq) (f: a -> units_of op) = 
  unary_congruence_condition f eq /\
  is_idempotent #a #eq f /\
  is_neutral_invariant op f /\
  yields_units f op  /\
  unary_over_nonzeros_distributes_over f op

type unit_part_function (#a: Type) (#eq: equivalence_relation a) 
                        (op: op_with_congruence eq) 
  = f:(a -> units_of op){ is_unit_part_function f }

let un_op_distr_lemma (#a:Type) (#eq: equivalence_relation a) 
                      (mul: op_with_congruence eq)  (f: unit_part_function mul)
  : Lemma (unary_over_nonzeros_distributes_over f mul) = ()

let un_op_distr_lemma_p (#a:Type) (#eq: equivalence_relation a) (mul: op_with_congruence eq)  (f: unit_part_function mul) (x y: non_absorber_of mul)
  : Lemma (unary_distributivity_condition f mul x y) = reveal_opaque (`%unary_over_nonzeros_distributes_over) (unary_over_nonzeros_distributes_over #a #eq)

let is_unit_normal (#a:Type) (#eq: equivalence_relation a) (mul: op_with_congruence eq) (unit_part_func: a -> a) (x:a) = is_neutral_of (unit_part_func x) mul

[@@"opaque_to_smt"]
let yields_unit_normals (#a:Type) (#eq: equivalence_relation a) (mul: op_with_congruence eq) (unit_part_func: a -> a) (f: a -> a) =
  forall (x:a). is_unit_normal mul unit_part_func (f x)

let yields_unit_normals_lemma (#a:Type) (#eq: equivalence_relation a) 
                              (mul: op_with_congruence eq) (unit_part_func: a -> a) 
                              (f: (a -> a){yields_unit_normals mul unit_part_func f}) (x:a)
  : Lemma (is_unit_normal mul unit_part_func (f x)) = reveal_opaque (`%yields_unit_normals) (yields_unit_normals mul)

type unit_normal_of (#a: Type) (#eq: equivalence_relation a) (mul: op_with_congruence eq) (unit_part_func: a -> a) 
  = x:a { is_unit_normal mul unit_part_func x }

[@@"opaque_to_smt"]
let unit_and_normal_decomposition_property (#a:Type) (#eq: equivalence_relation a) 
                                           (mul: op_with_congruence eq)
                                           (up: a->a) (np: a->a) 
  = forall (x:a). (eq x (up x `mul` np x)) /\ (eq (up x `mul` np x) x)

[@@"opaque_to_smt"]
let is_normal_part_function (#a:Type) (#eq: equivalence_relation a) 
                            (#mul: op_with_congruence eq) 
                            (unit_part_func: a -> a) 
                            (f: a -> unit_normal_of mul unit_part_func) = 
  is_neutral_invariant mul f /\
  unary_congruence_condition f eq /\
  is_idempotent #a #eq f /\ 
  yields_unit_normals mul unit_part_func f /\
  unary_distributes_over f mul /\
  unit_and_normal_decomposition_property mul unit_part_func f


type normal_part_function (#a: Type) (#eq: equivalence_relation a) 
                          (mul: op_with_congruence eq) 
                          (unit_part_func: a -> a) 
  = f:(a -> (unit_normal_of mul unit_part_func)){ is_normal_part_function unit_part_func f }
  
let unit_and_normal_decomposition_lemma (#a:Type) (#eq: equivalence_relation a) 
                                        (#mul: op_with_congruence eq)
                                        (up: unit_part_function mul)
                                        (np: normal_part_function mul up) (x:a)
  : Lemma (x `eq` mul (up x) (np x) /\ mul (up x) (np x) `eq` x) = 
    reveal_opaque (`%is_normal_part_function) (is_normal_part_function #a #eq #mul);
    reveal_opaque (`%unit_and_normal_decomposition_property) (unit_and_normal_decomposition_property mul)
  
let unit_part_func_of_product_is_product_of_unit_parts (#a: Type) (#eq: equivalence_relation a) 
                                                       (#mul: op_with_congruence eq)
                                                       (up: unit_part_function mul) 
                                                       (x y: non_absorber_of mul) 
  : Lemma((up (x `mul` y)) `eq` ((up x) `mul` (up y))) = un_op_distr_lemma_p mul up x y 

let product_of_unit_normals_is_normal (#a: Type) (#eq: equivalence_relation a) 
                                      (#mul: op_with_congruence eq)
                                      (up: unit_part_function mul)
                                      (x y: unit_normal_of mul up)
  : Lemma (requires ~(is_absorber_of x mul) /\ ~(is_absorber_of y mul))
          (ensures is_unit_normal mul up (x `mul` y)) = 
  un_op_distr_lemma_p mul up x y;                    // up (x*y) = up(x) * up(y) 
  yields_units_lemma mul up (x `mul` y);             // up (x*y) is unit
  neutral_lemma mul (up x) (up y);       // unit part of unit normal is 1
  neutral_equivalent_is_neutral mul (up y) (up x `mul` up y);   
  neutral_equivalent_is_neutral mul (up x `mul` up y) (up (mul x y))

noeq type ring (a: Type) = {
  addition: commutative_group a;
  multiplication: (z:monoid a{z.eq == addition.eq});
  eq: (t:equivalence_relation a { 
         congruence_condition addition.op t /\ 
         congruence_condition multiplication.op t /\ 
         t==addition.eq /\ t==multiplication.eq /\
         is_fully_distributive multiplication.op addition.op /\
         is_absorber_of addition.neutral multiplication.op
       });
  unit_part_of: a -> units_of multiplication.op;
  normal_part_of: a -> unit_normal_of multiplication.op unit_part_of;
  euclidean_norm: nat_function_defined_on_non_absorbers multiplication.op 
} 

let ring_distributivity_lemma (#a:Type) (r: ring a) 
    : Lemma (is_right_distributive r.multiplication.op r.addition.op  
            /\ is_left_distributive r.multiplication.op r.addition.op) =             
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a #r.eq);
    reveal_opaque (`%is_right_distributive) (is_right_distributive #a #r.eq); 
    reveal_opaque (`%is_left_distributive) (is_left_distributive #a #r.eq)
 
/// This one is made private because we only work with commutative multiplication here
unfold let mul_of (#a:Type) (r: ring a) = r.multiplication.op

/// And this one is made private just for the sake of symmetry with mul_of
unfold let add_of (#a:Type) (r: ring a) = r.addition.op

let ring_add_yields_inv_for_units (a:Type) (r: ring a) 
  : Lemma (yields_inverses_for_units r.addition.inv) 
  = yields_inverses_for_units_lemma a r.addition

/// The general idea is (1) x = x*(1+0) = x*1+x*0 = x+x*0 = x+0;
///                     (2) (x+x*0 = x+0) ==> (x*0 = 0) QED.
let ring_addition_neutral_is_absorber (#a:Type) (r: ring a) (x: a)
  : Lemma (x `r.multiplication.op` r.addition.neutral `r.eq` r.addition.neutral /\
           r.addition.neutral `r.multiplication.op` x `r.eq` r.addition.neutral /\
           r.addition.neutral `r.eq` (r.addition.neutral `r.multiplication.op` x) /\
           r.addition.neutral `r.eq` (x `r.multiplication.op` r.addition.neutral)) =  
  reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a #r.eq); 
  let ( *) = r.multiplication.op in
  let (+) = r.addition.op in
  let eq = r.eq in 
  let zero, one = r.addition.neutral, r.multiplication.neutral in
  neutral_equivalent_is_neutral ( *) one (zero+one); 
  trans_lemma eq ((x*zero)+(x*one)) (x*(zero+one)) x;
  trans_lemma eq ((x*zero)+(x*one)) x (x*one);
  neutral_lemma (+) zero (x*one);
  trans_lemma eq ((x*zero)+(x*one)) (x*one) (zero+(x*one)); 
  trans_lemma eq ((zero*x)+(one*x)) ((zero+one)*x) x;
  trans_lemma eq ((zero*x)+(one*x)) x (one*x);
  neutral_lemma (+) zero (one*x);
  trans_lemma eq ((zero*x)+(one*x)) (one*x) (zero+(one*x)) 

let ring_addition_neutral_is_multiplication_absorber_smt_lemma (#a:Type) (r: ring a)
  : Lemma (is_absorber_of r.addition.neutral r.multiplication.op) 
          [SMTPat(r.addition.neutral)] = 
  reveal_opaque (`%is_absorber_of) (is_absorber_of #a);
  Classical.forall_intro (ring_addition_neutral_is_absorber r)
 

let neg_of (#a:Type) (r: ring a) = group_inv_op r.addition
(*
  : Pure (inverse_op_for r.addition.op)
         (requires True)
         (ensures fun neg -> (neg == group_inv_op r.addition) /\
                          (is_inverse_operation_for neg r.addition.op) /\
                          (forall (x:a). (r.addition.op x (neg x) `r.eq` r.addition.neutral /\
                                    r.addition.op (neg x) x `r.eq` r.addition.neutral /\
                                    is_neutral_of (r.addition.op x (neg x)) r.addition.op /\
                                    is_neutral_of (r.addition.op (neg x) x) r.addition.op))) =
  group_inv_congruence_condition r.addition;
  reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #a); 
  reveal_opaque (`%unary_congruence_condition) (unary_congruence_condition #(units_of r.addition.op));
  reveal_opaque (`%is_inverse_operation_for) (is_inverse_operation_for #a #r.eq); 
  reveal_opaque (`%is_reflexive) (is_reflexive #a); 
  reveal_opaque (`%is_reflexive) (is_reflexive #(units_of r.addition.op)); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a);   
  reveal_opaque (`%is_symmetric) (is_symmetric #(units_of r.addition.op));   
  reveal_opaque (`%is_transitive) (is_transitive #a);
  reveal_opaque (`%is_transitive) (is_transitive #(units_of r.addition.op));
  group_inv_op r.addition  *)

unfold let minus_of (#a:Type) (r: ring a) (x:a) (y:a) 
  : (t:a{ t `r.eq` (x `r.addition.op` (r.addition.inv y) )}) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #a);
  x `r.addition.op` (neg_of r y)

let double_inverse_is_id (#a:Type) (#eq: equivalence_relation a) 
                         (#op: op_with_congruence eq)  
                         (inv: inverse_op_for op{is_associative op}) (x: a) 
  : Lemma (inv (inv x) `eq` x /\ x `eq` inv (inv x)) =    
  inverse_operation_lemma inv x;
  inverse_operation_lemma inv (inv x);   
  neutral_is_unique op (x `op` inv x) (inv (inv x) `op` inv x);
  cancellation_lemma inv x (inv (inv x)) (inv x)

let minus_minus_x_is_x_smt_lemma (#a:Type) (r: ring a) (x: a) 
  : Lemma (r.addition.inv (r.addition.inv x) `r.eq` x /\ x `r.eq` (r.addition.inv (r.addition.inv x)))
          [SMTPat(r.addition.inv (r.addition.inv x))] =
  let inv = group_inv_op r.addition in
  double_inverse_is_id inv x  

let x_eq_y_means_inv_x_eq_inv_y (#a:Type) (#eq: equivalence_relation a) 
                                (#op: op_with_congruence eq)  
                                (inv: inverse_op_for op{is_associative op}) 
                                (x y:a)
  : Lemma (x `eq` y <==> inv x `eq` inv y) = 
  // let-instruction also serves as brackets for the if-branch
  // Should we ever want to limit the symbol visibility, 
  // we'd use parentheses: (let temp = smth in my_lemma smth);
  if (x `eq` y) then 
    let x', y' = inv x, inv y in
    inverse_operation_lemma inv y;
    congruence_lemma_3 op x y x';
    congruence_lemma_3 op x y y';
    neutral_equivalent_is_neutral op (op y y') (op x y');
    producing_neutral_means_inverses inv x y'
  else if (inv x `eq` inv y) then 
    let x', y' = inv x, inv y in
    let x'', y'' = inv x', inv y' in
    double_inverse_is_id inv x;
    double_inverse_is_id inv y;
    inverse_operation_lemma inv y'; 
    congruence_lemma_3 op x' y' y'';
    neutral_equivalent_is_neutral op (op y' y'') (op x' y'');
    producing_neutral_means_inverses inv x' y'';
    trans_lemma_4 eq x x'' y'' y
 
let ring_additive_inv_x_is_x_times_minus_one (#a:Type) (r: ring a) (x: a)
  : Lemma ((r.addition.inv x) `r.eq` (r.multiplication.op x (r.addition.inv r.multiplication.neutral)) /\
           (r.multiplication.op x (r.addition.inv r.multiplication.neutral)) `r.eq` (r.addition.inv x)) = 
    reveal_opaque (`%is_symmetric) (is_symmetric #a); 
    reveal_opaque (`%is_transitive) (is_transitive #a); 
    reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a #r.eq); 
    let eq = r.eq in
    let mul = r.multiplication.op in
    let add = r.addition.op in
    let inv = group_inv_op r.addition in 
    let zero = r.addition.neutral in
    let one = r.multiplication.neutral in
    group_inv_is_complete r.addition;
    neutral_is_unique r.addition.op zero (one `add` (inv one));
    neutral_equivalent_is_neutral add zero ((mul x one) `add` (mul x (inv one)));
    producing_neutral_means_inverses inv (mul x one) (mul x (inv one));
    x_eq_y_means_inv_x_eq_inv_y inv (mul x one) x

let ring_additive_inv_x_is_minus_one_times_x (#a:Type) (r: ring a) (x: a)
  : Lemma ((r.addition.inv x) `r.eq` (r.multiplication.op (r.addition.inv r.multiplication.neutral) x) /\
           (r.multiplication.op (r.addition.inv r.multiplication.neutral) x) `r.eq` (r.addition.inv x)) = 
    let eq = r.eq in
    let mul = r.multiplication.op in
    let add = r.addition.op in
    let inv = neg_of r  in 
    let zero = r.addition.neutral in
    let one = r.multiplication.neutral in
    reveal_opaque (`%is_transitive) (is_transitive eq); 
    group_inv_is_complete r.addition;  
    group_inv_congruence_condition r.addition; 
    neutral_is_unique r.addition.op zero (one `add` (inv one));
    right_distributivity_lemma mul add one (inv one) x;
    absorber_equal_is_absorber mul zero (add one (inv one));
    absorber_lemma mul (add one (inv one)) x;
    absorber_equal_is_absorber mul zero (add one (inv one) `mul` x);    
    trans_lemma eq ((mul one x) `add` (mul (inv one) x))
                   (add one (inv one) `mul` x)  
                   zero;
    neutral_equivalent_is_neutral add zero (mul one x `add` mul (inv one) x);
    producing_neutral_means_inverses inv (mul one x) (mul (inv one) x);
    x_eq_y_means_inv_x_eq_inv_y inv (mul one x) x;
    trans_lemma eq (inv x) (inv (mul one x)) (mul (inv one) x)

let equal_elements_means_equal_inverses (#a:Type) (r: ring a) (x y:a) 
  : Lemma ((r.eq x y == (r.addition.inv x `r.eq` r.addition.inv y)) /\ 
           (r.eq x y == (r.addition.inv y `r.eq` r.addition.inv x))) =   
          reveal_opaque (`%is_symmetric) (is_symmetric #a); 
          reveal_opaque (`%is_reflexive) (is_reflexive #a);     
          x_eq_y_means_inv_x_eq_inv_y (neg_of r) x y 
 
let inv_switch_lemma (#a:Type) (r: ring a) (x y:a) 
  : Lemma (x `r.eq` r.addition.inv y <==> r.addition.inv x `r.eq` y) =
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  equal_elements_means_equal_inverses r x (r.addition.inv y)
  
let ring_additive_inverse_is_unique (#a:Type) (r:ring a) (x y: a) 
  : Lemma (requires x `r.eq` y \/ y `r.eq` x) 
          (ensures r.addition.inv x `r.eq` r.addition.inv y /\ 
                   r.addition.inv y `r.eq` r.addition.inv x) 
  = reveal_opaque (`%is_symmetric) (is_symmetric #a);   
    equal_elements_means_equal_inverses r x y

let ring_times_minus_one_is_commutative (#a:Type) (r: ring a) (x:a) 
  : Lemma ((x `r.multiplication.op` r.addition.inv r.multiplication.neutral) `r.eq` (r.addition.inv r.multiplication.neutral `r.multiplication.op` x) &&
           (x `r.multiplication.op` r.addition.inv r.multiplication.neutral) `r.eq` (r.addition.inv x) &&
           (r.addition.inv x) `r.eq` (x `r.multiplication.op` r.addition.inv r.multiplication.neutral) &&
           (r.addition.inv x) `r.eq` (r.addition.inv r.multiplication.neutral `r.multiplication.op` x) &&
           (r.addition.inv r.multiplication.neutral `r.multiplication.op` x) `r.eq` (x `r.multiplication.op` r.addition.inv r.multiplication.neutral) &&
           (r.addition.inv r.multiplication.neutral `r.multiplication.op` x) `r.eq` (r.addition.inv x)) = 
  reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  reveal_opaque (`%is_transitive) (is_transitive #a);  
  ring_additive_inv_x_is_minus_one_times_x r x;
  ring_additive_inv_x_is_x_times_minus_one r x

let ring_x_times_minus_y_is_minus_xy (#a:Type) (r:ring a) (x y: a) : Lemma ((x `r.multiplication.op` r.addition.inv y) `r.eq` (r.addition.inv (x `r.multiplication.op` y))) =   
  ring_additive_inv_x_is_x_times_minus_one r y;
  let eq = r.eq in
  let mul = r.multiplication.op in
  let add = r.addition.op in
  let neg = r.addition.inv in 
  let zero = r.addition.neutral in
  let one = r.multiplication.neutral in
  reveal_opaque (`%is_associative) (is_associative mul);
  reveal_opaque (`%is_transitive) (is_transitive eq);   
  reveal_opaque (`%is_symmetric) (is_symmetric eq);   
  ring_additive_inv_x_is_x_times_minus_one r y;            // -y = (y * -1)
  congruence_lemma_3 mul (neg y) (y `mul` neg one) x;      // x*(-y) = x*(y*(-1))
  //associativity is handled automatically here            // x*(y*(-1)) = (x*y)*(-1)
  ring_additive_inv_x_is_x_times_minus_one r (x `mul` y)  // (xy)*(-1) = -(xy)

let ring_x_times_minus_y_is_minus_x_times_y (#a:Type) (r:ring a) (x y: a) : Lemma (
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

let ring_product_with_minus_lemma (#a:Type) (r:ring a) (x y: a) 
  : Lemma ((x `r.multiplication.op` r.addition.inv y) `r.eq` (r.addition.inv x `r.multiplication.op` y) /\
           (x `r.multiplication.op` r.addition.inv y) `r.eq` (r.addition.inv (x `r.multiplication.op` y))) = 
  ring_x_times_minus_y_is_minus_x_times_y r x y; 
  ring_x_times_minus_y_is_minus_xy r x y 

let neg_distr_lemma (#a:Type) (r: ring a) (x y z: a) 
  : Lemma ((x `r.multiplication.op` (y `r.addition.op` r.addition.inv z)) `r.eq` 
          ((r.multiplication.op x y) `r.addition.op` (r.addition.inv (r.multiplication.op x z)))) =  
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  reveal_opaque (`%is_fully_distributive) (is_fully_distributive #a #r.eq);  
  ring_x_times_minus_y_is_minus_xy r x z 

let two_zeros_are_equal (#a:Type) (r: ring a) (x y: (t:a{r.eq t r.addition.neutral})) 
  : Lemma (x `r.eq` y) =  
  neutral_equivalent_is_neutral r.addition.op r.addition.neutral x; 
  neutral_equivalent_is_neutral r.addition.op r.addition.neutral y;
  neutral_is_unique r.addition.op x y

let eq_symmetry (#a:Type) (eq: equivalence_relation a) (x y: a) 
  : Lemma (requires (x `eq` y \/ y `eq` x)) (ensures (x `eq` y /\ y `eq` x)) = reveal_opaque (`%is_symmetric) (is_symmetric #a)

let is_zero_of #a (r: ring a) p = is_absorber_of p (mul_of r)

/// This illustrates how move_requires helps proving predicate equivalence.
/// The lemma itself can be proven way simpler. We leave it as an exercise
/// to the reader :)
let zero_is_equal_to_add_neutral_p (#a:Type) (r: ring a) (z: a)
  : Lemma (is_absorber_of z r.multiplication.op <==> r.eq z r.addition.neutral) =  
  let mul = mul_of r in
  let zero = r.addition.neutral in
  let aux_1 () : Lemma (requires is_absorber_of z r.multiplication.op) 
                       (ensures r.eq z r.addition.neutral) = 
    absorber_is_unique mul z zero in
  let aux_2 () : Lemma (requires r.eq z r.addition.neutral) 
                       (ensures is_absorber_of z r.multiplication.op) = 
    absorber_equal_is_absorber mul zero z in
  let aux_3 () : Lemma (r.eq z zero <==> is_absorber_of z mul) = 
    Classical.move_requires aux_1();
    Classical.move_requires aux_2() in aux_3()
   
let zero_is_equal_to_add_neutral (#a:Type) (r: ring a) : Lemma (forall (x:a). is_zero_of r x <==> r.eq x r.addition.neutral) 
  = FStar.Classical.forall_intro (zero_is_equal_to_add_neutral_p r)

let nonzero_is_not_equal_to_add_neutral (#a:Type) (r: ring a) 
  : Lemma (forall (x:a). ~(is_zero_of r x) <==> ~(r.eq x r.addition.neutral)) = zero_is_equal_to_add_neutral r
 
let nonzero_is_not_equal_to_add_neutral_p (#a:Type) (r: ring a) (z: a)
  : Lemma (~(is_absorber_of z r.multiplication.op) <==> ~(r.eq z r.addition.neutral)) = zero_is_equal_to_add_neutral r

type domain (a: Type) = r:ring a { 
  has_no_absorber_divisors r.multiplication.op /\ 
  ~(r.eq r.addition.neutral r.multiplication.neutral) }

let domain_mul_absorber_lemma (#a:Type) (dom: domain a) (x y:a) 
  : Lemma (is_absorber_of (dom.multiplication.op x y) dom.multiplication.op <==> 
           is_absorber_of x dom.multiplication.op \/ is_absorber_of y dom.multiplication.op) = 
   domain_multiplication_law_inv dom.multiplication.op x y

private let domain_lemma_1 (#a:Type) (dom: domain a) (p q:a) 
  : Lemma (requires is_absorber_of p dom.multiplication.op \/ is_absorber_of p dom.multiplication.op)
          (ensures is_absorber_of (dom.multiplication.op p q) dom.multiplication.op) = 
  reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors dom.multiplication.op) 
                                               
private let domain_lemma_2 (#a:Type) (dom: domain a) (x y:a) 
  : Lemma (requires is_absorber_of (dom.multiplication.op x y) dom.multiplication.op) 
          (ensures is_absorber_of x dom.multiplication.op \/ is_absorber_of y dom.multiplication.op) = 
  domain_mul_absorber_lemma dom x y

let domain_deduce_zero_factor_from_zero_product_and_nonzero_factor (#a:Type) (d: domain a) (x y: a)
  : Lemma (is_absorber_of (x `d.multiplication.op` y) d.multiplication.op 
       /\ ~(is_absorber_of y d.multiplication.op)
       ==> is_absorber_of x d.multiplication.op) 
  = reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors d.multiplication.op) 

let domain_zero_product_means_zero_factor (#a:Type) (dom: domain a) (p q: a) 
  : Lemma (requires (p `dom.multiplication.op` q) `dom.eq` dom.addition.neutral)
          (ensures (p `dom.eq` dom.addition.neutral \/ q `dom.eq` dom.addition.neutral)) =   
  neutral_equivalent_is_neutral dom.addition.op dom.addition.neutral (p `dom.multiplication.op` q);
  absorber_equal_is_absorber dom.multiplication.op dom.addition.neutral (p `dom.multiplication.op` q); 
  domain_multiplication_law_inv dom.multiplication.op p q;
  zero_is_equal_to_add_neutral dom

let ring_zero_factor_means_zero_product (#a:Type) (r: ring a) (p q:a)
  : Lemma (requires is_absorber_of p r.multiplication.op \/ is_absorber_of q r.multiplication.op)
          (ensures is_absorber_of (r.multiplication.op p q) r.multiplication.op) = 
          Classical.move_requires_2 (absorber_lemma r.multiplication.op) p q;
          Classical.move_requires_2 (absorber_lemma r.multiplication.op) q p

let domain_nonzero_product_means_nonzero_factors (#a:Type) (r: ring a) (p q: a)
  : Lemma (requires ~(is_absorber_of (r.multiplication.op p q) r.multiplication.op))
          (ensures ~(is_absorber_of p r.multiplication.op) /\ ~(is_absorber_of q r.multiplication.op)) =
  Classical.move_requires_2 (ring_zero_factor_means_zero_product r) p q
          
let domain_characterizing_lemma (#a:Type) (dom: domain a) (p q: a) 
  : Lemma ((p `dom.multiplication.op` q) `dom.eq` dom.addition.neutral <==>
           (p `dom.eq` dom.addition.neutral \/ q `dom.eq` dom.addition.neutral)) =   
  reveal_opaque (`%is_transitive) (is_transitive #a);              
  FStar.Classical.move_requires_2 (domain_zero_product_means_zero_factor dom) p q;
  if (dom.eq p dom.addition.neutral) then (
    absorber_equal_is_absorber dom.multiplication.op dom.addition.neutral p;
    absorber_lemma dom.multiplication.op p q
  ) else if (dom.eq q dom.addition.neutral) then (
    absorber_equal_is_absorber dom.multiplication.op dom.addition.neutral q;
    absorber_lemma dom.multiplication.op q p
  ) 

#restart-solver
let domain_law_from_pq_eq_pr (#a:Type) (d: domain a) (p q r: a)
  : Lemma (requires d.multiplication.op p q `d.eq` d.multiplication.op p r) 
          (ensures p `d.eq` d.addition.neutral \/ (q `d.eq` r)) =  
  reveal_opaque (`%is_transitive) (is_transitive #a);     
  reveal_opaque (`%is_symmetric) (is_symmetric #a);      
  let mul = d.multiplication.op in
  let eq = d.eq in
  let add = d.addition.op in
  let neg = neg_of d in
  let zero = d.addition.neutral in 
  equal_elements_means_equal_inverses d (p `mul` q) (p `mul` r);
  inverses_produce_neutral neg (p `mul` q) (neg (p `mul` r));
  assert (is_neutral_of ((p `mul` q) `add` (neg (p `mul` r))) add);
  neutral_is_unique add ((p `mul` q) `add` (neg (p `mul` r))) zero;  
  ring_x_times_minus_y_is_minus_xy d p r;
  symm_lemma eq (mul p (neg r)) (neg (mul p r));
  congruence_lemma_3 add (neg (mul p r)) (mul p (neg r)) (mul p q);
  assert ((mul p q `add` neg (mul p r)) `eq` (mul p q `add` mul p (neg r)));
  fully_distributive_is_both_left_and_right mul add  ;
  left_distributivity_lemma mul add   p q (neg r);
  assert (eq zero ((p `mul` q) `add` (neg (p `mul` r))));  
  trans_lemma_4 eq zero 
                  ((p `mul` q) `add` (neg (p `mul` r))) 
                  ((p `mul` q) `add` (p `mul` (neg r))) 
                  ((p `mul` (q `add` neg r)));
  domain_characterizing_lemma d p (add q (neg r));
  if (not (p `d.eq` zero) && d.addition.op q (d.addition.inv r) `d.eq` zero) 
  then group_element_equality_means_zero_difference d.addition q r 
    
let domain_cancellation_law (#a:Type) (d: domain a) (p q r: a)
  : Lemma (requires d.multiplication.op p q `d.eq` d.multiplication.op p r /\
                    ~(is_absorber_of p d.multiplication.op))
          (ensures d.eq q r) = 
          domain_law_from_pq_eq_pr d p q r;
          nonzero_is_not_equal_to_add_neutral_p d p 
 
let domain_unit_and_absorber_is_nonsense (#a:Type) (#d: domain a) (x: a) 
  : Lemma (requires is_unit x d.multiplication.op /\ 
                    is_absorber_of x d.multiplication.op) (ensures False) =   
  let ( *) = d.multiplication.op in
  let eq = d.eq in
  reveal_opaque (`%is_unit) (is_unit #a); 
  reveal_opaque (`%is_symmetric) (is_symmetric #a); 
  reveal_opaque (`%is_transitive) (is_transitive #a); 
  let x' = d.multiplication.inv x in 
  (* With proper definition of inverse function, the call to 
     indefinite_description_ghost is redundant.
     Earlier, x' was initialized with 
       indefinite_description_ghost (units_of ( * ) eq) (fun x' -> 
         (is_neutral_of (x * x') ( * ) eq /\ 
          is_neutral_of (x' * x) ( * ) eq)) *)
  let xx' = x * x' in
  neutral_is_unique ( *) d.multiplication.neutral xx'; 
  absorber_lemma ( *) x x'; 
  absorber_is_unique ( *) d.addition.neutral xx'

let domain_unit_cant_be_absorber (#a:Type) (#d: domain a) 
                                 (x: units_of d.multiplication.op) 
  : Lemma (~(is_absorber_of x d.multiplication.op)) 
  = Classical.move_requires (domain_unit_and_absorber_is_nonsense #a #d) x

let domain_absorber_cant_be_unit (#a:Type) (#d: domain a) (x: absorber_of d.multiplication.op) 
  : Lemma (~(is_unit x d.multiplication.op)) =
  Classical.move_requires (domain_unit_and_absorber_is_nonsense #a #d) x
  
type commutative_ring (a: Type) = r:ring a { is_commutative r.multiplication.op }

/// I'm not 100% sure, but somehow I think that PERHAPS unit/normal part functions
/// are safe to expect to be defined over any integral domain. 
/// 
/// The special case of euclidean domains, which allows for reduced fractions, will later be handled
/// differently, and all arithmetics will also account for the gcd/eea availability.
type integral_domain (a: Type) = r:domain a 
{ 
  is_commutative r.multiplication.op /\
  is_unit_part_function r.unit_part_of /\
  is_normal_part_function r.unit_part_of r.normal_part_of    
}
 
private let normal_of_nonabs_cant_be_abs (#a:Type) (d: integral_domain a) 
                                         (x: non_absorber_of d.multiplication.op) 
  : Lemma (requires is_absorber_of (d.normal_part_of x) d.multiplication.op) (ensures False) =
  reveal_opaque (`%is_transitive) (is_transitive #a);  
  unit_and_normal_decomposition_lemma d.unit_part_of d.normal_part_of x;
  absorber_lemma d.multiplication.op (d.normal_part_of x) (d.unit_part_of x);
  absorber_equal_is_absorber d.multiplication.op (d.normal_part_of x) x 

let normal_part_of_nonabsorber_is_nonabsorber (#a:Type) (#d: integral_domain a) 
                                              (x: non_absorber_of d.multiplication.op) 
  : Lemma (~(is_absorber_of (d.normal_part_of x) d.multiplication.op)) 
  = Classical.move_requires (normal_of_nonabs_cant_be_abs d) x

type euclidean_domain (a:Type) = 
  r:integral_domain a { euclidean_norm_forall_property r.multiplication.op r.euclidean_norm }

let ring_multiplicative_group_condition (#a:Type) (r: ring a) 
  = forall (x:a). (is_unit x r.multiplication.op <==> ~(is_absorber_of x r.multiplication.op))

/// Skewfields, aka division rings, are non-commutative counterparts for fields,
/// offering multiplicative inverses for each nonzero element, but not guaranteeing
/// ab⁻¹ to be equal to b⁻¹a.
/// Since these only appear in rather exotic situations (mind octonions),
/// I'll probably never have an instance of this type anyway.
type skewfield (a:Type) = r:domain a { ring_multiplicative_group_condition r }

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
type field (a:Type) = r:domain a {
  is_commutative r.multiplication.op /\
  ring_multiplicative_group_condition r
}
#pop-options
