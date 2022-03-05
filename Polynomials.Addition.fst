module Polynomials.Addition

open FStar.Seq
open FStar.Seq.Base
open FStar.Seq.Properties

open AlgebraTypes

open Polynomials.Definition
open Polynomials.Equivalence
open Polynomials.Compact

let max (x y: nat) : (t:nat{ t >= x /\ t >= y /\ (if x>y then t=x else t=y) }) = if x>y then x else y

let nth_of_cons #c (#r: commutative_ring #c) (h: c) (t: noncompact_poly_over_ring r) : Lemma (forall (i: nat{i<length t}). nth t i == nth (h +$ t) (i+1)) = ()

let rec noncompact_poly_add #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r) 
  : Tot (z:noncompact_poly_over_ring r {
           ((length p=length q /\ length z=length p) ==> (forall (i:nat{i<length p}). index z i == r.addition.op (index p i) (index q i))) /\
           (forall (i: nat{i < max (length p) (length q) }). nth z i `r.eq` r.addition.op (nth p i) (nth q i)) /\
           length z = (max (length p) (length q))
         }) 
        (decreases length p + length q) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #c); 
  if is_empty p && is_empty q then empty
  else if is_nonempty p && is_empty q then p
  else if is_empty p && is_nonempty q then q
  else (  
    let tail_add = noncompact_poly_add (tail p) (tail q) in
    let sum = (r.addition.op (head p) (head q)) +$ tail_add in
    //assert (nth sum 0 `r.eq` r.addition.op (nth p 0) (nth q 0));    
    //assert (forall (i: nat{i>0 && i<max (length p) (length q)}). nth sum i == nth tail_add (i-1));
    assert (forall (i: nat{i>0 && i<max (length p) (length q)}). nth sum i `r.eq` r.addition.op (nth (tail p) (i-1)) (nth (tail q) (i-1)));
    //assert (forall (i: nat{i>0 && i<max (length p) (length q)}). nth sum i `r.eq` r.addition.op (nth p i) (nth q i));
    //assert (forall (i: nat{ i<max (length p) (length q)}). nth sum i `r.eq` r.addition.op (nth p i) (nth q i));
    (r.addition.op (head p) (head q)) +$ (noncompact_poly_add (tail p) (tail q))
  )

let nth_of_sum #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r) (n: nat) : Lemma (nth (noncompact_poly_add p q) n `r.eq` r.addition.op (nth p n) (nth q n)) 
  = 
  if (n>=max (length p) (length q)) then (
    assert (n >= length (noncompact_poly_add p q));
    assert (nth (noncompact_poly_add p q) n == r.addition.neutral)
  ) 
  

let rec noncompact_poly_add_is_commutative #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r) 
  : Lemma (ensures (noncompact_poly_add p q) `noncompact_poly_eq` (noncompact_poly_add q p)) (decreases length p + length q) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #c); 
  if is_nonempty p && is_nonempty q then comm_lemma r.eq r.addition.op (head p) (head q);
  if is_empty p && is_empty q then () else noncompact_poly_add_is_commutative (tail p) (tail q) 
 
#push-options "--ifuel 0 --fuel 1 --z3rlimit 5"
let rec noncompact_poly_add_is_associative #c (#r: commutative_ring #c) (p q w: noncompact_poly_over_ring r) 
  : Lemma (ensures (noncompact_poly_add p (noncompact_poly_add q w)) `ncpoly_eq` (noncompact_poly_add (noncompact_poly_add p q) w))
          (decreases %[length p;length q;length w]) =  
  if is_nonempty p then  equals_self r (head p);
  if is_nonempty q then  equals_self r (head q);
  if is_nonempty w then  equals_self r (head w);
  if (is_nonempty p && is_nonempty q && is_nonempty w) then assoc_lemma3 r.eq r.addition.op (head p) (head q) (head w);
  if (is_empty p && is_empty q && is_empty w) then () else 
  noncompact_poly_add_is_associative (tail p) (tail q) (tail w) 
  (*
    if (is_empty p && is_empty q && is_empty w) then () else 
    if (is_empty p && is_empty q && is_nonempty w) then noncompact_poly_add_is_associative p q (tail w) else 
    if (is_empty p && is_empty w && is_nonempty q) then noncompact_poly_add_is_associative p (tail q) w else 
    if (is_empty w && is_empty q && is_nonempty p) then noncompact_poly_add_is_associative (tail p) q w else 
    if (is_empty p && is_nonempty q && is_nonempty w) then noncompact_poly_add_is_associative p (tail q) (tail w) else 
    if (is_nonempty p && is_empty q && is_nonempty w) then noncompact_poly_add_is_associative (tail p) q (tail w) else
    if (is_nonempty p && is_nonempty q && is_empty w) then noncompact_poly_add_is_associative (tail p) (tail q) w else
    if (is_nonempty p && is_nonempty q && is_nonempty w) then noncompact_poly_add_is_associative (tail p) (tail q) (tail w) 
  *)
#pop-options
     
let poly_add #c (#r: commutative_ring #c) (p q: poly_over_ring r) 
  : (z: poly_over_ring r{z `ncpoly_eq` (noncompact_poly_add p q)}) = 
  symm_lemma ncpoly_eq (poly_compact (noncompact_poly_add p q)) (noncompact_poly_add p q);
  poly_compact (noncompact_poly_add #c #r p q)

let rec poly_nil_is_zero #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r)
  : Lemma (ensures noncompact_poly_add p empty `noncompact_poly_eq` p) (decreases length p) = 
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);    
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  if is_nonempty p then poly_nil_is_zero #c #r (tail p)
 
#push-options "--ifuel 0 --fuel 1 --z3rlimit 10"
let rec poly_add_respects_poly_eq #c (#r: commutative_ring #c) 
                                     (x y: noncompact_poly_over_ring r) 
                                     (z: noncompact_poly_over_ring r{noncompact_poly_eq y z})
  : Lemma (ensures noncompact_poly_eq (noncompact_poly_add x y) (noncompact_poly_add x z) /\
                   noncompact_poly_eq (noncompact_poly_add y x) (noncompact_poly_add z x)) (decreases length x + length y + length z) =
  let (| (+),           eq,   zero               |) = 
      (| r.addition.op, r.eq, r.addition.neutral |) in 
  reveal_opaque (`%is_symmetric) (is_symmetric #c);                     // a `eq` b <==> b `eq` a
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);          // p `poly_eq` p for any polynomial p
  if (is_empty x && is_empty y && is_empty z) then () else
  if (is_empty x && is_empty y && is_nonempty z) then poly_add_respects_poly_eq x y (tail z) else
  if (is_empty x && is_nonempty y && is_empty z) then poly_add_respects_poly_eq x (tail y) z else
  if (is_nonempty x && is_empty y && is_empty z) then poly_add_respects_poly_eq (tail x) y z else
  if (is_nonempty x && is_nonempty y && is_empty z) then (
    neutral_equivalent_is_neutral (+) eq zero (head y);
    neutral_lemma (+) eq (head y) (head x);
    poly_add_respects_poly_eq (tail x) (tail y) z
  )
  else if (is_nonempty x && is_empty y && is_nonempty z) then (
    neutral_equivalent_is_neutral (+) eq zero (head z);
    neutral_lemma (+) eq (head z) (head x);
    poly_add_respects_poly_eq (tail x) y (tail z)     
  )
  else if (is_nonempty x && is_nonempty y && is_nonempty z) then (
    equivalence_wrt_operation_lemma #c #(+) eq (head y) (head z) (head x); 
    poly_add_respects_poly_eq (tail x) (tail y) (tail z);
    ()
  )
   
let rec noncompact_poly_negate #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) 
  : Tot(q: noncompact_poly_over_ring r{ contains_no_nonzeros (noncompact_poly_add q p) }) (decreases length p) = 
  if is_empty p then empty else (
    let neg = r.addition.inv (head p) in
    reveal_opaque (`%is_neutral_of) (is_neutral_of #c);
    reveal_opaque (`%is_left_id_of) (is_left_id_of #c);
    reveal_opaque (`%is_right_id_of) (is_right_id_of #c);
    inverse_operation_lemma r.addition.op r.eq r.addition.inv neg;  
    neutral_is_unique r.addition.op r.eq (r.addition.op neg (head p)) r.addition.neutral; 
    r.addition.inv (head p)) +$ (noncompact_poly_negate (tail p)
  ) 

let poly_add_is_commutative #c (#r: commutative_ring #c) (p q: poly_over_ring r) : Lemma (poly_add p q `ncpoly_eq` poly_add q p) =  
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);    
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  noncompact_poly_add_is_commutative #c #r p q 

let poly_add_is_associative #c (#r: commutative_ring #c) (p q w: poly_over_ring r) : Lemma (poly_add p (poly_add q w) `ncpoly_eq` poly_add (poly_add p q) w) = 
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);    
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  noncompact_poly_add_is_associative #c #r p q w;
  Classical.forall_intro_3 (poly_add_respects_poly_eq #c #r);  
  calc (noncompact_poly_eq) {
    poly_compact (noncompact_poly_add p (poly_compact (noncompact_poly_add q w)));
    noncompact_poly_eq {}
    noncompact_poly_add p (poly_compact (noncompact_poly_add q w));
    noncompact_poly_eq {}
    noncompact_poly_add p (noncompact_poly_add q w);
    noncompact_poly_eq {}
    noncompact_poly_add (noncompact_poly_add p q) w;
    noncompact_poly_eq {}
    noncompact_poly_add (poly_compact (noncompact_poly_add p q)) w;
    noncompact_poly_eq {}
    poly_compact (noncompact_poly_add (poly_compact (noncompact_poly_add p q)) w);    
   } 
 
let field_poly_add_is_assoc #c (#f: field #c) (p q r: poly_over_field f) 
  : Lemma (poly_add p (poly_add q r) `ncpoly_eq` poly_add (poly_add p q) r) 
  = poly_add_is_associative #c #f p q r

let rec poly_times_const #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) (a: c) 
  : Tot (noncompact_poly_over_ring r) (decreases length p) = 
  if is_nonempty p then (head p `mul_of r` a) +$ (poly_times_const (tail p) a) else empty
 
let poly_add_identity #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) : Lemma (noncompact_poly_add p empty `ncpoly_eq` p) = 
  trans_lemma ncpoly_eq (noncompact_poly_add p empty) (poly_add (poly_compact p) empty) p 
 
let compact_poly_add_respects_poly_eq #c (#r: commutative_ring #c) (x y z: poly_over_ring r)
  : Lemma (requires ncpoly_eq y z) (ensures ncpoly_eq (poly_add x y) (poly_add x z) /\
                                            ncpoly_eq (poly_add y x) (poly_add z x) 
                                              ) =  
  poly_add_respects_poly_eq x y z; 
  trans_lemma_4 ncpoly_eq (poly_add x y) (noncompact_poly_add x y) (noncompact_poly_add x z) (poly_add x z);
  trans_lemma_4 ncpoly_eq (poly_add y x) (noncompact_poly_add y x) (noncompact_poly_add z x) (poly_add z x) 
  
let poly_add_congruence_lemma #c (#r: commutative_ring #c) (x y z w: noncompact_poly_over_ring r)
  : Lemma (requires ncpoly_eq x z /\ ncpoly_eq y w) 
          (ensures ncpoly_eq (noncompact_poly_add x y) (noncompact_poly_add z w)) =
  let (+) = noncompact_poly_add #c #r in 
  let (=) = ncpoly_eq #c #r in
  poly_add_respects_poly_eq x y w; 
  poly_add_respects_poly_eq w x z; 
  trans_lemma (=) (x+y) (x+w) (z+w)
