module Polynomials.Equivalence

open AlgebraTypes
open FStar.Seq.Base
open FStar.Seq.Properties
open Polynomials.Definition

#push-options "--ifuel 0 --fuel 2 --z3rlimit 10 --query_stats"

/// This looks less ugly than reveal_opaque.
/// Also, this adds just one fact, thus reducing resource usage.
let equals_self #c (r: commutative_ring #c) (x:c) : Lemma (x `r.eq` x) = reveal_opaque (`%is_reflexive) (is_reflexive #c)

/// Same as above :)
let identical_means_equal #c (r: commutative_ring #c) (x y: c)
  : Lemma (x == y ==> x `r.eq` y /\ y `r.eq` x) = reveal_opaque (`%is_reflexive) (is_reflexive #c)

let zero_equals_self #c (r: commutative_ring #c) : Lemma (r.eq r.addition.neutral r.addition.neutral)  = equals_self r r.addition.neutral

/// Similar to transitivity lemma, but deduces inequality instead.
let trans_inequality #c (eq: equivalence_relation c) (x:c) (y:c{x `eq` y \/ y `eq` x}) (z:c{~(z `eq` x /\ z `eq` y /\ x `eq` z /\ y `eq` z)})
  : Lemma ((not(x `eq` z)) /\ (not (z `eq` x)) /\ (not (y `eq` z)) /\ (not (z `eq` y))) 
  = reveal_opaque (`%is_transitive) (is_transitive #c);
    reveal_opaque (`%is_symmetric) (is_symmetric #c)

/// Equality of noncompact polys
let rec noncompact_poly_eq #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r) 
  : Pure bool (requires True) (ensures fun b -> b /\ q==empty /\ length p > 0 ==> is_zero r (last p) ) (decreases (length p + length q)) =  
  if length p > 0 then equals_self r (head p);
  if length p = 0 && length q = 0 then true 
  else if length p>0 && length q>0 then r.eq (head p) (head q) && noncompact_poly_eq (tail p) (tail q)
  else if length p = 0 then is_zero r (head q) && noncompact_poly_eq p (tail q)
  else is_zero r (head p) && noncompact_poly_eq (tail p) q       

let nth_of_cons #c (#r: commutative_ring #c) (h: c) (t: noncompact_poly_over_ring r) : Lemma (forall (i: nat{i<length t}). nth t i == nth (h +$ t) (i+1)) = ()


/// for any poly x, it is true that (x = x)
let rec ncpoly_eq_is_reflexive_lemma #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) 
  : Lemma (ensures noncompact_poly_eq p p) (decreases length p) = 
  if length p > 0 then (
    equals_self r (head p);
    ncpoly_eq_is_reflexive_lemma (tail p)
  )

/// for any two polys p, q, (p = q) <==> (q = p)
let rec ncpoly_eq_is_symmetric_lemma #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r) 
  : Lemma (ensures noncompact_poly_eq p q == noncompact_poly_eq q p) (decreases length p + length q) = 
  if length p>0 && length q>0 then symm_lemma r.eq (head p) (head q); 
  if length q>0 || length p>0 then ncpoly_eq_is_symmetric_lemma (tail p) (tail q)


/// for any three polys p, q, w,  (p = q  &&  q = w) ==> (p = w)
#push-options "--ifuel 0 --fuel 1 --z3rlimit 4"
let rec ncpoly_eq_is_transitive_lemma #c (#r: commutative_ring #c) (p q w: noncompact_poly_over_ring r) 
  : Lemma (ensures noncompact_poly_eq p q /\ noncompact_poly_eq q w ==> noncompact_poly_eq p w) (decreases length p + length q + length w) = 
  reveal_opaque (`%is_symmetric) (is_symmetric #c);  
  reveal_opaque (`%is_transitive) (is_transitive #c);
  // this may be written in a very short form. 
  // But The proof will take more time and might fail occasionally.
  // if length p>0 || length q>0 || length w>0 then ncpoly_eq_is_transitive_lemma (tail p) (tail q) (tail w)  
  if length p=0 && length q=0 && length w=0 then () 
  else if length p=0 && length q=0 && length w>0 then ncpoly_eq_is_transitive_lemma p q (tail w)
  else if length p=0 && length q>0 && length w=0 then ncpoly_eq_is_transitive_lemma p (tail q) w
  else if length p>0 && length q=0 && length w=0 then ncpoly_eq_is_transitive_lemma (tail p) q w
  else if length p=0 && length q>0 && length w>0 then ncpoly_eq_is_transitive_lemma p (tail q) (tail w)
  else if length p>0 && length q=0 && length w>0 then ncpoly_eq_is_transitive_lemma (tail p) q (tail w)
  else if length p>0 && length q>0 && length w=0 then ncpoly_eq_is_transitive_lemma (tail p) (tail q) w
  else if length p>0 && length q>0 && length w>0 then ncpoly_eq_is_transitive_lemma (tail p) (tail q) (tail w)
#pop-options


/// for cases when a_i == b_i, not just r.eq
let rec seq_equal_means_poly_equal #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r)
  : Lemma (requires equal p q) (ensures noncompact_poly_eq p q) (decreases length q) = 
  if length p>0 && length q>0 then (equals_self r (head p); seq_equal_means_poly_equal (tail p) (tail q))

/// polys consisting of zeros are all equal to empty polynomial
let rec poly_of_zeros_equals_empty #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r{for_all (fun coef -> is_zero r coef) p}) 
  : Lemma (ensures noncompact_poly_eq p empty) (decreases length p) = if length p > 0 then poly_of_zeros_equals_empty (tail p)

/// Polys equal to empty are either empty or only contain zeros.
let rec poly_eq_empty_means_all_zeros #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r)
  : Lemma (requires noncompact_poly_eq p empty) (ensures length p=0 \/ (length p>0 /\ noncompact_poly_eq (tail p) empty /\ is_zero r (head p))) (decreases length p) = 
  if length p > 0 then poly_eq_empty_means_all_zeros (tail p) 



/// rewrote the condition of the above lemma a bit
let rec poly_eq_empty_means_all_zeros2 #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r)
  : Lemma (requires noncompact_poly_eq p empty) (ensures length p=0 \/ (forall (i:nat{i < length p}). is_zero r (index p i))) (decreases length p) = 
  if length p > 0 then (
    assert (is_zero r (last p));
    assert (is_zero r (index p (length p - 1)));
    poly_eq_empty_means_all_zeros2 (tail p);
    assert (forall (i:nat{i<length (tail p) - 1}). is_zero r (index (tail p) i));
    assert (equal (slice p 1 (length p)) (tail p)); 
    assert (forall (i:nat{i>0 && i<length p}). (index p i) == (index (tail p) (i-1)));
    assert (forall (i:nat{i>0 && i<length p}). is_zero r (index p i));
    assert (is_zero r (index p 0));
    assert (forall (i:nat{i<length p}). is_zero r (index p i));    
    ()
  )

/// strongly typed poly equality as equivalence relation
let ncpoly_eq #c (#r: commutative_ring #c) : equivalence_relation (noncompact_poly_over_ring r) = 
  reveal_opaque (`%is_symmetric) (is_symmetric #(noncompact_poly_over_ring r));    
  reveal_opaque (`%is_transitive) (is_transitive #(noncompact_poly_over_ring r));
  reveal_opaque (`%is_reflexive) (is_reflexive #(noncompact_poly_over_ring r)); 
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  noncompact_poly_eq #c #r

/// h1 = h2 && p = q ==> (cons h1 p) = (cons h2 q)
let eq_of_cons #c (#r: commutative_ring #c) (h1 h2: c) (p q: noncompact_poly_over_ring r) 
  : Lemma (requires p `noncompact_poly_eq` q /\ ((h1 `r.eq` h2) \/ (h1 == h2))) 
          (ensures (h1 +$ p) `noncompact_poly_eq` (h2 +$ q)) 
          (decreases length p + length q) =  
    identical_means_equal r h1 h2;
    //everything beyond this line is redundant :)
    //lemma_eq_elim (tail (h1 +$ p)) p;
    //assert (tail (h1 +$ p) == p);
    //assert (equal (tail (h1 +$ p)) p);
    //assert (equal (tail (h2 +$ q)) q);
    seq_equal_means_poly_equal (tail (h1 +$ p)) p;
    seq_equal_means_poly_equal (tail (h2 +$ q)) q;
    trans_lemma_4 ncpoly_eq (tail (h1 +$ p)) 
                            p 
                            q 
                            (tail (h2 +$ q)) //4-transitivity of eq a=b=c=d ==> a=d 

let rec poly_eq_from_nth_eq #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r) 
  : Lemma (requires (forall (i: nat{i<max (length p) (length q)}). nth p i `r.eq` nth q i))
          (ensures noncompact_poly_eq p q)
          (decreases length p + length q)= 
    if length p = 0 then (
      assert (forall (i: nat{i<length q}). nth p i == r.addition.neutral);
      // assert (forall (i: nat{i<max (length p) (length q)}). nth q i `r.eq` r.addition.neutral);
      assert (for_all (fun coef -> is_zero r coef) q);
      lemma_eq_elim p empty;
      poly_of_zeros_equals_empty q; 
      ncpoly_eq_is_symmetric_lemma p q;
      ()
    ) else if length q = 0 then (       
      assert (forall (i: nat{i<max (length p) (length q)}). nth p i `r.eq` r.addition.neutral);
      assert (max (length p) (length q) == length p);
      assert (forall (i: nat{i<length p}). nth p i `r.eq` r.addition.neutral);
      reveal_opaque (`%is_symmetric) (is_symmetric #c);  
      assert (for_all (fun coef -> is_zero r coef) p); 
      lemma_eq_elim q empty;
      poly_of_zeros_equals_empty p; 
      ncpoly_eq_is_symmetric_lemma p q;
      ()
    ) else (
      assert (forall (i: nat{i<max (length p) (length q)}). nth p i `r.eq` nth q i);
      reveal_opaque (`%is_symmetric) (is_symmetric #c);  
      reveal_opaque (`%is_reflexive) (is_reflexive #c);  
      reveal_opaque (`%is_transitive) (is_transitive #c);  
      assert (forall (i: nat{i<max  (length p) (length q)}). nth p i `r.eq` nth q i);
      nth_of_cons (head p) (tail p);
      assert (forall (i: nat{i>0 && i<max  (length p) (length q)}). nth (tail p) (i-1) `r.eq` nth q i);
      assert (forall (i: nat{i>0 && i<max  (length p) (length q)}). nth q i `r.eq` nth (tail q) (i-1));
      assert (forall (i: nat{i>0 && i<max  (length p) (length q)}). nth (tail q) (i-1) `r.eq` nth (tail q) (i-1));            
      poly_eq_from_nth_eq (tail p) (tail q);      
      assert (r.eq (head p) (nth p 0));
      assert (head p `r.eq` head q);
      eq_of_cons (head p) (head q) (tail p) (tail q);
      ()
    )
   
let rec nth_eq_from_poly_eq_forall #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r)
  : Lemma (requires noncompact_poly_eq p q) (ensures (forall (i: nat{i<max (length p) (length q)}). nth p i `r.eq` nth q i)) (decreases length p + length q) = 
  if length p = 0 then (
    lemma_eq_elim p empty;
    ncpoly_eq_is_symmetric_lemma p q;
    poly_eq_empty_means_all_zeros2 q;
    ()
  ) else if length q = 0 then (
    lemma_eq_elim q empty;
    poly_eq_empty_means_all_zeros2 p;
    reveal_opaque (`%is_symmetric) (is_symmetric #c);  
    ()
  ) else (  
    nth_eq_from_poly_eq_forall (tail p) (tail q);
    //a little hint to the prover:
    assert (forall (i: nat{i>0 && i<max (length p) (length q)}). nth (tail p) (i-1) `r.eq` nth (tail q) (i-1))    
  )

let nth_eq_from_poly_eq #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r) (i:nat)
  : Lemma (requires noncompact_poly_eq p q) (ensures nth p i `r.eq` nth q i) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #c);
  nth_eq_from_poly_eq_forall p q 
 
let poly_eq_trim_lemma #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r)
  : Lemma (requires ncpoly_eq p q /\
                    length p > length q)
          (ensures ncpoly_eq (slice p 0 (length q)) q) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #c);
  nth_eq_from_poly_eq_forall p q;
  poly_eq_from_nth_eq p (slice p 0 (length q));        
  trans_lemma ncpoly_eq (slice p 0 (length q)) p q

/// This allows to omit parentheses in (x +$ y $+ z) 
let cat_assoc_lemma #c (#r: commutative_ring #c) (x:c) (y: noncompact_poly_over_ring r) (z: c)
  : Lemma ((x +$ y) $+ z == x +$ (y $+ z) /\ x +$ (y $+ z) == (x +$ y) $+ z) 
    [SMTPatOr [ 
      [SMTPat(x +$ (y $+ z))]; 
      [SMTPat((x +$ y) $+ z)] 
    ]] = 
  lemma_eq_elim ((x +$ y) $+ z) (x +$ (y $+ z))

/// This has a stronger condition than eq_of_cons: it requires the liats to be seq-equal!
let rec eq_of_snoc #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) (x y: c) 
  : Lemma (requires x `r.eq` y)
          (ensures (p $+ x) `noncompact_poly_eq` (p $+ y))
          (decreases length p) =                   
    if (length p > 0) then (
      eq_of_snoc (tail p) x y;
      eq_of_cons (head p) (head p) (tail p $+ x) (tail p $+ y); 
      // assert (equal (head p +$ tail p $+ x) (p $+ x));
      // assert (equal (head p +$ tail p $+ y) (p $+ y)); 
      // trans_lemma_4 ncpoly_eq (p $+ x) (head p +$ tail p $+ x) (head p +$ tail p $+ y) (p $+ y);
      ()
    )

/// Approaching poly compact routines, we particularly need a lemma about trailing zeros.
let rec poly_eq_poly_cat_nil #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) (zero: c)
  : Lemma (requires r.eq zero r.addition.neutral) (ensures noncompact_poly_eq p (p $+ zero)) (decreases length p) = 
    if (length p = 0) then symm_lemma r.eq r.addition.neutral zero // minimally required fact instead of revealing opaque
    else (        
      poly_eq_poly_cat_nil (tail p) zero; // tail p ~=~ tail p $+ zero
      eq_of_cons (head p) (head p) (tail p) ((tail p) $+ zero); // head p +$ tail p ~=~ head p +$ tail p $+ zero
      seq_equal_means_poly_equal (head p +$ tail p) p;
      seq_equal_means_poly_equal (head p +$ tail p $+ zero) (p $+ zero);
      // transitivity call is redundant, but helps reading the proof
      trans_lemma_4 ncpoly_eq p //Adjusted tabs for best readability
              (head p +$ tail p) 
              (head p +$ tail p $+ zero) 
                             (p $+ zero)          
    )

/// synonym to eq_of_snoc
let poly_cat_tail_eq_lemma #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) (t1 t2: c)
  : Lemma (requires r.eq t1 t2)
          (ensures noncompact_poly_eq (p $+ t1) (p $+ t2))
          (decreases length p) = eq_of_snoc p t1 t2 

/// (0) = empty
let nul_poly_lemma #c (#r: commutative_ring #c) 
  : Lemma (noncompact_poly_eq #c #r (empty) (create 1 r.addition.neutral)) 
  = zero_equals_self r

/// synonym to eq_of_cons
let poly_equality_from_cons #c (#r: commutative_ring #c) (h1 h2: c) (t1 t2: noncompact_poly_over_ring r)
  : Lemma (requires (r.eq h1 h2) /\ (noncompact_poly_eq t1 t2))
          (ensures noncompact_poly_eq (h1 +$ t1) (h2 +$ t2))
          (decreases length t1 + length t2) = eq_of_cons h1 h2 t1 t2 
          
/// wonder if this duplicate is safe to remove... 
let poly_of_zero_eq_z #c (#r: commutative_ring #c) : Lemma (noncompact_poly_eq #c #r (create 1 r.addition.neutral) (empty))
  = zero_equals_self r

let poly_cat_eq_lemma #c (#r: commutative_ring #c) (h:c) (t1 t2: noncompact_poly_over_ring r)
  : Lemma (requires noncompact_poly_eq t1 t2)
          (ensures noncompact_poly_eq (h +$ t1) (h +$ t2)) 
          (decreases length t1 + length t2) = 
    equals_self r h;
    //eq_of_cons h h t1 t2; // redundant since including the refinements to +$
    ()
    
let poly_cons_eq_lemma #c (#r: commutative_ring #c) (h1 h2: c) (t1 t2: noncompact_poly_over_ring r)
  : Lemma (requires noncompact_poly_eq t1 t2 /\ r.eq h1 h2)
          (ensures noncompact_poly_eq (h1 +$ t1) (h2 +$ t2)) 
          (decreases length t1 + length t2) = () // eq_of_cons h1 h2 t1 t2 //redundant too

let poly_eq_of_cat #c (#r: commutative_ring #c) (h1 h2: c) (t1 t2: noncompact_poly_over_ring r) 
  : Lemma (requires noncompact_poly_eq t1 t2 /\ r.eq h1 h2) 
          (ensures noncompact_poly_eq (h1 +$ t1) (h2 +$ t2)) = () // eq_of_cons h1 h2 t1 t2
           
let lemma_cons_liat #c (#r : commutative_ring #c) (h: c) (p: noncompact_poly_over_ring r{length p>0}) 
  : Lemma (h +$ liat p == liat (h +$ p)) 
  = lemma_eq_elim (h +$ liat p) (liat (h +$ p))
  
let poly_liat_decomposition #c (#r : commutative_ring #c) (p: noncompact_poly_over_ring r {length p > 0}) 
  : Lemma (p == liat p $+ last p) = ()

let noncompact_poly_eq_means_first_coef_eq #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) (q: noncompact_poly_over_ring r) 
  : Lemma (requires noncompact_poly_eq p q /\ (length p > 0) /\ (length q > 0)) 
          (ensures r.eq (head p) (head q))=()
 
let poly_eq_nil_means_nil_eq_tail #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) 
  : Lemma (requires noncompact_poly_eq p empty /\ length p > 0) (ensures noncompact_poly_eq (tail p) empty) = ()

let rec poly_eq_is_reflexive_lemma #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) 
  : Lemma (ensures noncompact_poly_eq p p) (decreases length p) =  
  if is_empty p then () else (
    equals_self r (head p);
    poly_eq_is_reflexive_lemma (tail p)
  )

let rec contains_no_nonzeros #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) 
  : Tot (bool) (decreases length p) 
  = if is_empty p then true else (is_zero r (head p)) && contains_no_nonzeros (tail p)

let rec contains_no_nonzeros_statement #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r)
  : Lemma (requires contains_no_nonzeros p) (ensures for_all (fun x -> (is_zero r x)) p) (decreases length p) = 
  if is_empty p then () else contains_no_nonzeros_statement (tail p) 

let rec contains_no_nonzeros_statement_backwards #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r)
  : Lemma (requires  for_all (fun x -> (is_zero r x)) p) 
          (ensures contains_no_nonzeros p) 
          (decreases length p) = 
  if is_empty p then () else contains_no_nonzeros_statement_backwards (tail p) 

let rec poly_eq_nil_means_elements_eq_zero #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r{noncompact_poly_eq p empty})
  : Lemma (requires length p > 0) (ensures contains_no_nonzeros p) (decreases length p) = if length p > 1 then poly_eq_nil_means_elements_eq_zero (tail p)

let rec poly_elements_eq_zero_means_poly_eq_nil #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r)
  : Lemma (requires contains_no_nonzeros p) (ensures noncompact_poly_eq p empty) (decreases length p)
= if length p > 0 then poly_elements_eq_zero_means_poly_eq_nil (tail p)

let poly_eq_nil_means_first_eq_zero #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r{noncompact_poly_eq p empty})
  : Lemma (requires length p > 0) (ensures (is_zero r (head p))) = 
  poly_eq_nil_means_elements_eq_zero p

let poly_eq_nil_last_is_zero #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r{noncompact_poly_eq p empty /\ length p > 0}) 
  : Lemma (ensures is_zero r (last p)) = ()
