module Polynomials

open AlgebraTypes

open FStar.List

let rec last_gtot #a (l: list a{length l > 0}) = 
  match l with 
  | Cons head [] -> head
  | Cons head tail -> last_gtot tail

type noncompact_poly_over_ring #c (r: ring #c) = list c

let is_poly #c (#r: ring #c) (p: noncompact_poly_over_ring r) = 
  (length p>0 /\ ~(last_gtot p `r.eq` r.addition.neutral)) \/ length p=0
  
type poly_over_ring #coefficient_type (coefficient_ring: ring #coefficient_type) = 
  p: noncompact_poly_over_ring coefficient_ring { is_poly p }

let poly_cons_is_again_poly #c (#r: ring #c) (h: c) (p: poly_over_ring r) 
  : Lemma (requires length p > 0 \/ ~(r.eq h r.addition.neutral)) 
          (ensures is_poly #c #r (Cons h p)) = ()
  
let rec poly_compact #c (#r: ring #c) (p: noncompact_poly_over_ring r) : poly_over_ring r  = 
  match p with
  | Nil -> Nil
  | Cons h t -> match (poly_compact #c #r t) with
               | Nil -> if h `r.eq` r.addition.neutral then Nil else [h]
               | lst -> [h] @ lst
 
let rec poly_compact_does_nothing_on_poly #c (#r: ring #c) (p: poly_over_ring r) 
  : Lemma (poly_compact p == p) =  
  match p with
  | Nil -> ()
  | h::t -> poly_compact_does_nothing_on_poly #c #r t 

let poly_compact_is_idempotent #c (#r: ring #c) (p: noncompact_poly_over_ring r) 
  : Lemma ((poly_compact p) == (poly_compact (poly_compact p))) = 
  poly_compact_does_nothing_on_poly (poly_compact p)
  
let rec noncompact_poly_eq #c (#r: ring #c) (p q: noncompact_poly_over_ring r) = 
  match (p,q) with
  | Nil, Nil -> true
  | Nil, _ -> false
  | _, Nil -> false
  | a::at, b::bt -> if r.eq a b then noncompact_poly_eq #c #r at bt else false

let rec noncompact_poly_add #c (#r: ring #c) (p q: noncompact_poly_over_ring r) : noncompact_poly_over_ring r  = 
  match (p, q) with
  | (ph::pt, qh::qt) -> (Cons (r.addition.op ph qh) (noncompact_poly_add #c #r pt qt))
  | (Nil, qx) -> qx
  | (px, Nil) -> px
  | (Nil, Nil) -> Nil

let rec noncompact_poly_add_is_commutative #c (#r: ring #c) (p q: noncompact_poly_over_ring r) 
  : Lemma ((noncompact_poly_add p q) `noncompact_poly_eq` (noncompact_poly_add q p)) = 
  reveal_opaque (`%is_commutative) (is_commutative #c);
  reveal_opaque (`%is_reflexive) (is_reflexive #c); 
  match (p,q) with 
  | Nil, Nil -> ()
  | (Nil, qx::qt) -> (noncompact_poly_add_is_commutative #c #r [] qt); () 
  | (px::pt, Nil) -> (noncompact_poly_add_is_commutative #c #r pt []); ()  
  | (px::pt, qx::qt) -> noncompact_poly_add_is_commutative #c #r pt qt
 
let rec noncompact_poly_add_is_associative #c (#r: ring #c) (p q w: noncompact_poly_over_ring r) 
  : Lemma ((noncompact_poly_add p (noncompact_poly_add q w)) `noncompact_poly_eq` (noncompact_poly_add (noncompact_poly_add p q) w)) = 
  reveal_opaque (`%is_associative) (is_associative #c);
  reveal_opaque (`%is_reflexive) (is_reflexive #c); 
  match (p,q,w) with 
  | Nil, Nil, Nil -> ()
  | (Nil, Nil, wx::wt) -> noncompact_poly_add_is_associative #c #r [] [] wt  
  | (Nil, qx::qt, Nil) -> noncompact_poly_add_is_associative #c #r [] qt []
  | (px::pt, Nil, Nil) -> noncompact_poly_add_is_associative #c #r pt [] []
  | (Nil, qx::qt, wx::wt) -> noncompact_poly_add_is_associative #c #r [] qt wt
  | (px::pt, qx::qt, Nil) -> noncompact_poly_add_is_associative #c #r pt qt []
  | (px::pt, Nil, wx::wt) -> noncompact_poly_add_is_associative #c #r pt [] wt
  | (px::pt, qx::qt, wx::wt) -> noncompact_poly_add_is_associative #c #r pt qt wt
  
let poly_tail_is_poly #c (#r: ring #c) (p: poly_over_ring r{length p > 0}) 
  : Lemma (is_poly #c #r (Cons?.tl p) ) = ()

let rec poly_eq_internal #c (#r: ring #c) (p q: poly_over_ring r) : bool = 
  match (p, q) with
  | Nil, Nil -> true
  | Nil, b::bt -> false
  | a::at, Nil -> false
  | a::at, b::bt -> if (r.eq a b) then poly_eq_internal #c #r at bt else false

let rec poly_noncompact_eq_implies_eq #c (#r: ring #c) (p q: noncompact_poly_over_ring r) 
  : Lemma (requires  p `noncompact_poly_eq` q) 
          (ensures (poly_compact p) `poly_eq_internal` (poly_compact q)) = 
  match (p, q) with
  | ph::pt, qh::qt -> if ph `r.eq` r.addition.neutral then trans_lemma r.eq qh ph r.addition.neutral;
                   if qh `r.eq` r.addition.neutral then trans_lemma r.eq ph qh r.addition.neutral;
                   poly_noncompact_eq_implies_eq #c #r pt qt
  | _ -> ()
           (***** Don't panic. It's okay. Here's what happens under the hood:   *)       
            (*     assert (r.eq ph qh);
                   if ph `r.eq` r.addition.neutral then (
                     trans_lemma r.eq qh ph r.addition.neutral;
                     assert (r.eq qh r.addition.neutral);
                     poly_noncompact_eq_implies_eq #c #r pt qt;  
                     ()
                   ) else if qh `r.eq` r.addition.neutral then (
                     trans_lemma r.eq ph qh r.addition.neutral;
                     assert (r.eq ph r.addition.neutral);
                     poly_noncompact_eq_implies_eq #c #r pt qt;  
                     ()
                   ) else (                   
                     poly_noncompact_eq_implies_eq #c #r pt qt;
                     assert (poly_eq_internal #c #r (poly_compact pt) (poly_compact qt));
                     assert (r.eq ph qh); 
                     ()
                   )
           *)

let rec poly_eq_is_reflexive_lemma #c (#r: ring #c) (p: poly_over_ring r) : Lemma (poly_eq_internal p p) = 
  match p with 
  | Nil -> assert (poly_eq_internal p p)
  | a::at -> reveal_opaque (`%is_reflexive) (is_reflexive #c); 
           poly_eq_is_reflexive_lemma #c #r at
 
let rec poly_eq_is_symmetric_lemma #c (#r: ring #c) (p q: poly_over_ring r) : Lemma (poly_eq_internal p q == poly_eq_internal q p) = 
  match (p,q) with
  | a::at, b::bt -> reveal_opaque (`%is_symmetric) (is_symmetric #c); 
                 poly_eq_is_symmetric_lemma #c #r at bt
  | _ -> ()

let rec poly_eq_is_transitive_lemma #c (#r: ring #c) (p q w: poly_over_ring r) : Lemma (poly_eq_internal p q /\ poly_eq_internal q w ==> poly_eq_internal p w) = 
  match (p,q,w) with
  | a::at,b::bt,d::dt -> reveal_opaque (`%is_transitive) (is_transitive #c); 
                   poly_eq_is_transitive_lemma #c #r at bt dt
  | _ -> ()
  
let poly_eq #c (#r: ring #c) : equivalence_relation (poly_over_ring r) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #(poly_over_ring r));
  reveal_opaque (`%is_transitive) (is_transitive #(poly_over_ring r));
  reveal_opaque (`%is_symmetric) (is_symmetric #(poly_over_ring r));
  Classical.forall_intro (poly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (poly_eq_is_symmetric_lemma #c #r);
  Classical.forall_intro_3 (poly_eq_is_transitive_lemma #c #r);  
  poly_eq_internal #c #r
  
let poly_add #c (#r: ring #c) (p q: poly_over_ring r) : poly_over_ring r = 
  poly_compact (noncompact_poly_add #c #r p q)
 
let poly_add_is_commutative #c (#r: ring #c) (p q: poly_over_ring r) : Lemma (poly_add p q `poly_eq` poly_add q p) = 
  noncompact_poly_add_is_commutative #c #r p q;
  poly_noncompact_eq_implies_eq #c #r (noncompact_poly_add #c #r p q) (noncompact_poly_add #c #r q p);  
() 

let poly_add_is_associative #c (#r: ring #c) (p q w: poly_over_ring r) : Lemma (poly_add p (poly_add q w) `poly_eq` poly_add (poly_add p q) w) = 
  noncompact_poly_add_is_associative #c #r p q w;
  poly_noncompact_eq_implies_eq #c #r (noncompact_poly_add #c #r p (noncompact_poly_add q w)) (noncompact_poly_add #c #r (noncompact_poly_add p q) w);
  assert (poly_compact (noncompact_poly_add p (noncompact_poly_add q w)) `poly_eq` poly_compact (noncompact_poly_add (noncompact_poly_add p q) w));
  
  admit();
  assert (poly_add p (q `noncompact_poly_add` w) `poly_eq` poly_add (p `noncompact_poly_add` q) w); 
  poly_noncompact_eq_implies_eq #c #r (noncompact_poly_add #c #r p (poly_add q w)) (noncompact_poly_add #c #r (poly_add p q) w);  
()
 
