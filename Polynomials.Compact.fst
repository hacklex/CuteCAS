module Polynomials.Compact
 
open AlgebraTypes
  
open FStar.Seq.Extras
open FStar.Seq
open FStar.Seq.Base
open FStar.Seq.Properties

open Polynomials.Definition
open Polynomials.Equivalence


#push-options "--ifuel 0 --fuel 2 --z3rlimit 10 --query_stats"
 
let is_compact_poly #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) : bool = length p=0 || not(is_zero r (last p))

type poly_over_ring #coefficient_type (coefficient_ring: commutative_ring #coefficient_type) = 
  p: noncompact_poly_over_ring coefficient_ring { is_compact_poly p }
  
#push-options "--ifuel 0 --fuel 2 --z3rlimit 10 --query_stats"
let rec poly_compact #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) : Tot(z:poly_over_ring r{
    noncompact_poly_eq p z /\ // is logically equal to the input
    length z <= length p /\ // can't be longer than the input
    (length p>0 && is_zero r (last p) ==> length z < length p) /\ // trailing zero will be cut
    (starts_with p z) /\ 
    (ncpoly_eq p empty ==> z `equal` empty) /\
    (is_compact_poly p ==> p == z) // does not affect already compact polys
  }) (decreases length p) =    
  let zero = r.addition.neutral in
  if length p = 0 then p else
  if (last p `r.eq` zero) then ( // thankfully, F* automatically deduces p == liat p $+ last p    
    poly_eq_poly_cat_nil (liat p) (last p); // liat p ~=~ (liat p $+ last p) 
    // eq_of_snoc (liat p) (last p) zero; // redundant: (liat p $+ last p) ~=~ (liat p $+ zero)
    symm_lemma r.eq zero (last p);
    trans_lemma ncpoly_eq (poly_compact (liat p)) (liat p) p;    
    if (poly_compact (liat p) `ncpoly_eq` empty) then (
      poly_eq_empty_means_all_zeros (poly_compact (liat p)); // This call is redundant :)    
      poly_compact (liat p)
    ) else (
      trans_inequality ncpoly_eq p (liat p) empty; 
      poly_compact (liat p)
    )
  ) else (
    ncpoly_eq_is_reflexive_lemma p;
    symm_lemma r.eq r.addition.neutral (last p);
    // Everything beyond this line is redundant
    assert (length p > 0);  
    (Classical.move_requires (poly_eq_empty_means_all_zeros #c #r))(p);
    assert (~(last p `r.eq` zero));
    assert (exists (i: nat{i<length p}). ~(index p i `r.eq` zero));    
    assert (~(ncpoly_eq p empty)); 
    p
  )
#pop-options


let poly_compact_eliminates_cat_zero #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) (z: c{is_zero r z}) 
  : Lemma (ensures poly_compact p == poly_compact (p $+ z)) (decreases length p) = ()
  // This entire body is redundant since introducing result type refinement to poly_compact definition
  (*
  if length p = 0 then ()  
  else (
    if (not(is_zero r (last p))) then lemma_eq_elim (liat (p $+ z)) p
    else (    
      assert (is_zero r (last p));
      assert (poly_compact p == poly_compact #c #r (liat p));
      assert (poly_compact (p $+ z) `equal` poly_compact (liat (p $+ z)));
      assert (liat (p $+ z) `equal` p);
      lemma_eq_elim (liat (p $+ z)) p
    )
  ) *)

type poly_over_field #c (f: field #c) = poly_over_ring f

let poly_cons_is_again_poly #c (#r: commutative_ring #c) (h: c) (p: poly_over_ring r) 
  : Lemma (requires length p > 0 \/ ~(r.eq h r.addition.neutral)) 
          (ensures is_compact_poly (cons h p)) = symm_lemma r.eq r.addition.neutral h
            
let poly_compact_is_not_longer_than_input #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) 
  : Lemma (ensures length (poly_compact p) <= length p) 
          (decreases length p) = ()

let poly_compact_does_nothing_on_poly #c (#r: commutative_ring #c) (p: poly_over_ring r) 
  : Lemma (ensures poly_compact p == p /\ equal (poly_compact p) p)
          (decreases length p) = ()

let poly_compact_is_idempotent #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) 
  : Lemma ((poly_compact p) == (poly_compact (poly_compact p))) = ()
      
let poly_eq_its_compact #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) 
  : Lemma (ensures noncompact_poly_eq p (poly_compact p)) = ()
   
let transitivity x y z : Lemma (requires x==y /\ y==z) (ensures x==z) = ()
let transitivity_4 x y z w : Lemma (requires x==y /\ y==z /\ z==w) (ensures x==w) = ()

#push-options "--ifuel 0 --fuel 1 --z3rlimit 10 --query_stats"
let rec poly_compact_of_nonzero_cons_lemma #c (#r: commutative_ring #c) (h: c{not(is_zero r h)}) (t: noncompact_poly_over_ring r)
  : Lemma (ensures poly_compact (h +$ t) == h +$ poly_compact t) (decreases length t) =
    let pc = poly_compact #c #r in  
    if (length t=0) then () else (
      if (not (is_zero r (last t))) then () else (
        poly_liat_decomposition t;
        poly_compact_eliminates_cat_zero (liat t) (last t);
        // assert (pc (liat t) == (pc t)); //trivial anyway
        // this only splits the proof in two smaller parts thus reducing resource usage
        assert_spinoff (pc (h +$ t) == pc (liat (h +$ t))); 
        lemma_cons_liat h t;
        // assert ((liat (cons h t)) == (cons h (liat t)));
        poly_compact_of_nonzero_cons_lemma h (liat t);
        
        // everything beyond this call is redundant.
        
        // assert (pc (h $$ (liat t)) == h $$ (pc (liat t))); 
        // assert_spinoff (t == snoc (liat t) (last t));
        // poly_compact_eliminates_cat_zero (liat t) (last t);
        // assert_spinoff (pc (liat t) == pc t);
        // assert_spinoff (poly_compact (cons h t) == poly_compact (cons h (liat t))); 
        // assert_spinoff (h $$ pc t == h $$ (pc (liat t)));
        // assert_spinoff (h $$ (pc (liat t)) == pc (h $$ (liat t))); 
        // assert (pc (h $$ (liat t)) == pc (h $$ t));        
        transitivity_4 (h +$ pc t) 
                       (h +$ (pc (liat t))) 
                       (pc (h +$ (liat t))) 
                       (pc (h +$ t));        
        ()
      )
    )

let rec poly_compact_of_zero_cons_nonzero_lemma (#c)
                                                (#r: commutative_ring #c) 
                                                (h:c{is_zero r h}) 
                                                (t: noncompact_poly_over_ring r{length (poly_compact t)>0})
  : Lemma (ensures poly_compact (h +$ t) == h +$ poly_compact t) (decreases length t) = 
    // The proof is absolutely identical to the above lemma. 
    // Only this time it's the tail of nonzero length, not the head
    let pc = poly_compact #c #r in
    if length t=0 || not(is_zero r (last t)) then () else (
        poly_liat_decomposition t;
        poly_compact_eliminates_cat_zero (liat t) (last t);
        assert_spinoff (pc (h +$ t) == pc (liat (h +$ t))); 
        lemma_cons_liat h t;
        poly_compact_of_zero_cons_nonzero_lemma h (liat t);         
      ()
    )
    
#pop-options 

let poly_compact_of_nonzero_eq_head_cat_compact_of_tail #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r{length p>0 /\ ~(is_zero r (head p))})
  : Lemma (ensures poly_compact p == head p +$ poly_compact (tail p)) = 
    poly_compact_of_nonzero_cons_lemma (head p) (tail p)
    
let poly_compact_of_nonzero_cons_strict #c (#r: commutative_ring #c) (head: c{not(is_zero r head)}) (tail: noncompact_poly_over_ring r) 
  : Lemma (ensures (poly_compact (head +$ tail) == head +$ (poly_compact tail))) 
  = poly_compact_of_nonzero_cons_lemma head tail
    
let poly_compact_of_equals_lemma #c (#r: commutative_ring #c) (p1 p2: noncompact_poly_over_ring r)
  : Lemma (requires p1 `ncpoly_eq` p2) (ensures poly_compact p1 `ncpoly_eq` poly_compact p2) 
  = trans_lemma_4 ncpoly_eq (poly_compact p1) p1 p2 (poly_compact p2)

let poly_compact_of_nonzero_cons #c (#r: commutative_ring #c) (head: c{not(is_zero r head)}) (tail: noncompact_poly_over_ring r) 
  : Lemma (ensures (poly_compact (head +$ tail) `ncpoly_eq` (head +$ poly_compact tail))) 
  = reveal_opaque (`%is_reflexive) (is_reflexive #c);
    assert (ncpoly_eq tail (poly_compact tail));
    eq_of_cons head head tail (poly_compact tail);
    trans_lemma ncpoly_eq (poly_compact (head +$ tail)) (head +$ tail) (head +$ poly_compact tail)

//let poly_compact_of_zero_cat_poly #c (#r: commutative_ring #c) (h: c{is_zero r h}) (t: noncompact_poly_over_ring r)
//  : Lemma (poly_compact #c #r (cons h t)

let poly_compact_of_cat_lemma #c (#r: commutative_ring #c) (h: c) (t: noncompact_poly_over_ring r) 
  : Lemma (ensures poly_compact (cons h t) == poly_compact (cons h (poly_compact t))) 
          (decreases length t) = 
          if (is_zero r h) && length (poly_compact t) = 0 then (
            poly_eq_empty_means_all_zeros2 t;
            poly_of_zeros_equals_empty (h +$ t)
          )
          else if not(is_zero r h) then poly_compact_of_nonzero_cons_strict h t
          else poly_compact_of_zero_cons_nonzero_lemma h t
   
 
let eq_ignores_compact #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r) 
  : Lemma (requires noncompact_poly_eq p q) 
          (ensures noncompact_poly_eq (poly_compact p) q) = 
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r) 


let poly_tail_is_poly #c (#r: commutative_ring #c) (p: poly_over_ring r{length p > 0}) 
  : Lemma (is_compact_poly (tail p) ) = ()
 
let poly_compact_of_zeros_is_nil #c (#r: commutative_ring #c) (p:noncompact_poly_over_ring r{noncompact_poly_eq p empty})
  : Lemma (ensures poly_compact p == empty) = ()

let poly_eq_nil_means_compact_is_nil #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r{noncompact_poly_eq p empty}) 
  : Lemma (poly_compact p == empty) = ()
