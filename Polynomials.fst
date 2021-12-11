module Polynomials

open AlgebraTypes

open FStar.List

let rec last_gtot #a (l: list a{length l > 0}) = 
  match l with 
  | Cons head [] -> head
  | Cons head tail -> last_gtot tail

type noncompact_poly_over_ring #c (r: ring #c) = list c

let rec noncompact_poly_eq #c (#r: ring #c) (p q: noncompact_poly_over_ring r) : bool = 
  match (p,q) with
  | Nil, Nil -> true
  | Nil, (x::tail) -> (if (r.eq r.addition.neutral x) then (noncompact_poly_eq #c #r Nil tail) else false)
  | (x::tail), Nil -> (if (r.eq r.addition.neutral x) then (noncompact_poly_eq #c #r tail Nil) else false)
  | a::at, b::bt -> if r.eq a b then noncompact_poly_eq #c #r at bt else false
  
let is_poly #c (#r: ring #c) (p: noncompact_poly_over_ring r) = 
  (length p>0 /\ ~(last_gtot p `r.eq` r.addition.neutral)) \/ length p=0

let rec ncpoly_eq_is_reflexive_lemma #c (#r: ring #c) (p: noncompact_poly_over_ring r) 
  : Lemma (noncompact_poly_eq p p) = 
  match p with 
  | Nil -> assert (noncompact_poly_eq p p)
  | a::at -> reveal_opaque (`%is_reflexive) (is_reflexive #c); 
           ncpoly_eq_is_reflexive_lemma #c #r at
           
let rec ncpoly_eq_is_symmetric_lemma #c (#r: ring #c) (p q: noncompact_poly_over_ring r) 
  : Lemma (noncompact_poly_eq p q == noncompact_poly_eq q p) = 
  match (p,q) with
  | Nil, Nil -> ()
  | a::at, Nil -> ncpoly_eq_is_symmetric_lemma #c #r at Nil
  | Nil, a::at -> ncpoly_eq_is_symmetric_lemma #c #r Nil at
  | a::at, b::bt -> reveal_opaque (`%is_symmetric) (is_symmetric #c);  
                 ncpoly_eq_is_symmetric_lemma #c #r at bt

let rec ncpoly_eq_is_transitive_lemma #c (#r: ring #c) (p q w: noncompact_poly_over_ring r) 
  : Lemma (noncompact_poly_eq p q /\ noncompact_poly_eq q w ==> noncompact_poly_eq p w) = 
  reveal_opaque (`%is_symmetric) (is_symmetric #c);    
  reveal_opaque (`%is_transitive) (is_transitive #c);
  match (p, q, w) with 
  | a::at, b::bt, Nil -> ncpoly_eq_is_transitive_lemma #c #r at bt Nil 
  | Nil, a::at, b::bt -> ncpoly_eq_is_transitive_lemma #c #r Nil at bt 
  | a::at, Nil, b::bt -> ncpoly_eq_is_transitive_lemma #c #r at Nil bt 
  | a::at,b::bt, d::dt -> ncpoly_eq_is_transitive_lemma #c #r at bt dt
  | _ -> ()
  

type poly_over_ring #coefficient_type (coefficient_ring: ring #coefficient_type) = 
  p: noncompact_poly_over_ring coefficient_ring { is_poly p }

type poly_over_field #c (f: field #c) = poly_over_ring f

let poly_cons_is_again_poly #c (#r: ring #c) (h: c) (p: poly_over_ring r) 
  : Lemma (requires length p > 0 \/ ~(r.eq h r.addition.neutral)) 
          (ensures is_poly #c #r (Cons h p)) = ()

let nul_poly_lemma #c (#r: ring #c) : Lemma (noncompact_poly_eq #c #r Nil [r.addition.neutral]) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #c)

let rec except_last #a (l: list a{length l > 0}) 
  : Pure (z: list a{length l = 0 \/ length z = ((length l) - 1)})
         (requires True)
         (ensures fun (z: list a) -> (l == (z @ [last_gtot l])))
   = 
  match l with
  | Nil -> Nil
  | [x] -> []
  | h::t -> (h::(except_last #a t))

let rec poly_cat_eq_lemma #c (#r: ring #c) h t1 t2 
  : Lemma (requires noncompact_poly_eq #c #r t1 t2)
          (ensures noncompact_poly_eq #c #r (h::t1) (h::t2)) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #c) 

let rec poly_cat_tail_eq_lemma #c (#r: ring #c) (p: noncompact_poly_over_ring r) (t1 t2: c)
  : Lemma (requires r.eq t1 t2)
          (ensures noncompact_poly_eq #c #r (p @ [t1]) (p @ [t2])) = 
  match p with 
  | Nil -> ()
  | h::ht ->  reveal_opaque (`%is_reflexive) (is_reflexive #c); poly_cat_tail_eq_lemma #c #r ht t1 t2


let rec poly_eq_poly_cat_nil #c (#r: ring #c) (p: noncompact_poly_over_ring r) : Lemma (noncompact_poly_eq #c #r p (p @ [r.addition.neutral])) = 
  match p with
  | Nil -> nul_poly_lemma #c #r
  | h::th -> poly_eq_poly_cat_nil #c #r th;
           nul_poly_lemma #c #r;
           poly_cat_eq_lemma #c #r h th (th @ [r.addition.neutral])
           
  

let rec poly_compact #c (#r: ring #c) (p: noncompact_poly_over_ring r) : Tot(z:poly_over_ring r{noncompact_poly_eq #c #r p z /\ length z <= length p}) (decreases length p) =  
  reveal_opaque (`%is_symmetric) (is_symmetric #c);  
  reveal_opaque (`%is_reflexive) (is_reflexive #c);  
  reveal_opaque (`%is_transitive) (is_transitive #c); 
  if length p = 0 then [] else
  if (last_gtot p `r.eq` r.addition.neutral) then ( 
    poly_eq_poly_cat_nil #c #r (except_last p);
    Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
    Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);    
    Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
    assert ((except_last p) @ [last_gtot p] == p); 
    assert (noncompact_poly_eq #c #r (except_last p) (except_last p @ [r.addition.neutral]));
    assert ([last_gtot p] `noncompact_poly_eq #c #r` [r.addition.neutral]);
    poly_cat_tail_eq_lemma #c #r (except_last p) (last_gtot p) r.addition.neutral;
    assert (noncompact_poly_eq #c #r (except_last p) p);
    poly_compact #c #r (except_last p)  
    
  ) else (
    ncpoly_eq_is_reflexive_lemma p;
    p
  )
  

let rec poly_compact_is_not_longer_than_input #c (#r: ring #c) (p: noncompact_poly_over_ring r) 
  : Lemma (length (poly_compact p) <= length p) = 
  match p with
  | Nil -> ()
  | ph::pt -> poly_compact_is_not_longer_than_input #c #r pt

let rec poly_compact_does_nothing_on_poly #c (#r: ring #c) (p: poly_over_ring r) 
  : Lemma (poly_compact p == p) =  
  match p with
  | Nil -> ()
  | h::t -> poly_compact_does_nothing_on_poly #c #r t 

let poly_compact_is_idempotent #c (#r: ring #c) (p: noncompact_poly_over_ring r) 
  : Lemma ((poly_compact p) == (poly_compact (poly_compact p))) = 
  poly_compact_does_nothing_on_poly (poly_compact p)
  

let poly_eq_of_cat #c (#r: ring #c) (h1 h2: c) (t1 t2: noncompact_poly_over_ring r) 
  : Lemma (requires noncompact_poly_eq t1 t2 /\ r.eq h1 h2) 
          (ensures noncompact_poly_eq #c #r (h1::t1) (h2::t2)) = () 
           
let rec poly_eq_its_compact #c (#r: ring #c) (p: noncompact_poly_over_ring r) 
  : Lemma (noncompact_poly_eq p (poly_compact p)) = ()
                                          

let first #a (l: list a{length l > 0}) : a = match l with | h::t -> h
let tail_of #a (l: list a{length l > 0}) : list a = match l with | h::t -> t
  
let rec poly_compact_of_cat_lemma #c (#r: ring #c) (h: c) (t: noncompact_poly_over_ring r) 
  : Lemma (ensures poly_compact #c #r (h::t) == poly_compact (h::(poly_compact t))) 
          (decreases length t)
          =          
  if length t = 0 then () 
  else if last_gtot t `r.eq` r.addition.neutral 
       then poly_compact_of_cat_lemma #c #r h (except_last t)
  
let noncompact_poly_eq_means_first_coef_eq #c (#r: ring #c) (p: noncompact_poly_over_ring r) (q: noncompact_poly_over_ring r) 
  : Lemma (requires noncompact_poly_eq p q /\ (length p > 0) /\ (length q > 0)) 
          (ensures r.eq (first p) (first q) )=()

let poly_eq_nil_means_nil_eq_tail #c (#r: ring #c) (p: noncompact_poly_over_ring r) 
  : Lemma (requires noncompact_poly_eq p Nil /\ length p > 0) (ensures noncompact_poly_eq #c #r (tail_of p) Nil) = ()

let rec poly_eq_is_reflexive_lemma #c (#r: ring #c) (p: noncompact_poly_over_ring r) : Lemma (noncompact_poly_eq p p) =  
  match p with 
  | Nil -> ()
  | a::at -> reveal_opaque (`%is_reflexive) (is_reflexive #c); 
           poly_eq_is_reflexive_lemma #c #r at

let eq_ignores_compact #c (#r: ring #c) (p q: noncompact_poly_over_ring r) 
  : Lemma (requires noncompact_poly_eq p q) 
          (ensures noncompact_poly_eq (poly_compact p) q) = 
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r) 

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
 
let poly_eq #c (#r: ring #c) : equivalence_relation (poly_over_ring r) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #(poly_over_ring r));
  reveal_opaque (`%is_transitive) (is_transitive #(poly_over_ring r));
  reveal_opaque (`%is_symmetric) (is_symmetric #(poly_over_ring r));
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);    
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  noncompact_poly_eq #c #r
  
let poly_add #c (#r: ring #c) (p q: poly_over_ring r) : poly_over_ring r = 
  poly_compact (noncompact_poly_add #c #r p q)

let rec poly_nil_is_zero #c (#r: ring #c) (p: noncompact_poly_over_ring r) : Lemma (noncompact_poly_add #c #r p Nil `noncompact_poly_eq` p) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #(poly_over_ring r));
  reveal_opaque (`%is_transitive) (is_transitive #(poly_over_ring r));
  reveal_opaque (`%is_symmetric) (is_symmetric #(poly_over_ring r));
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);    
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  match p with
  | Nil -> ()
  | ph::pt -> poly_nil_is_zero #c #r pt

let rec contains_no_nonzeros #c (#r: ring #c) (p: noncompact_poly_over_ring r) : bool = 
  match p with 
  | Nil -> true
  | t::th -> r.eq t r.addition.neutral && contains_no_nonzeros #c #r th


let rec poly_eq_nil_means_elements_eq_zero #c (#r: ring #c) (p: noncompact_poly_over_ring r{noncompact_poly_eq p Nil})
: Lemma (requires length p > 0) (ensures contains_no_nonzeros p)
= reveal_opaque (`%is_symmetric) (is_symmetric #c);  
  reveal_opaque (`%is_reflexive) (is_reflexive #c);  
  reveal_opaque (`%is_transitive) (is_transitive #c); 
  reveal_opaque (`%is_reflexive) (is_reflexive #(poly_over_ring r));
  reveal_opaque (`%is_transitive) (is_transitive #(poly_over_ring r));
  reveal_opaque (`%is_symmetric) (is_symmetric #(poly_over_ring r));
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);    
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  match p with 
  | Nil -> ()
  | t::th -> 
           assert (r.eq t r.addition.neutral);
           if (length th > 0) then poly_eq_nil_means_elements_eq_zero #c #r th


let rec poly_elements_eq_zero_means_poly_eq_nil #c (#r: ring #c) (p: noncompact_poly_over_ring r)
: Lemma (requires contains_no_nonzeros p) (ensures noncompact_poly_eq p Nil)
= reveal_opaque (`%is_symmetric) (is_symmetric #c);  
  reveal_opaque (`%is_reflexive) (is_reflexive #c);  
  reveal_opaque (`%is_transitive) (is_transitive #c); 
  reveal_opaque (`%is_reflexive) (is_reflexive #(poly_over_ring r));
  reveal_opaque (`%is_transitive) (is_transitive #(poly_over_ring r));
  reveal_opaque (`%is_symmetric) (is_symmetric #(poly_over_ring r));
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);    
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  match p with 
  | Nil -> ()
  | t::th -> 
           assert (r.eq t r.addition.neutral);
           if (length th > 0) then poly_elements_eq_zero_means_poly_eq_nil #c #r th

let poly_eq_nil_means_first_eq_zero #c (#r: ring #c) (p: noncompact_poly_over_ring r{noncompact_poly_eq p Nil})
: Lemma (requires length p > 0) (ensures first p `r.eq` r.addition.neutral) = 
  poly_eq_nil_means_elements_eq_zero p

let rec poly_eq_nil_last_is_zero #c (#r: ring #c) (p: noncompact_poly_over_ring r{noncompact_poly_eq p Nil /\ length p > 0}) : Lemma (r.eq (last_gtot p) r.addition.neutral) 
  = 
  match p with
  | ph::pt -> match pt with 
            | Nil -> poly_eq_nil_means_first_eq_zero p
            | zh::zt -> poly_eq_nil_last_is_zero #c #r pt

let rec poly_compact_of_zeros_is_nil #c (#r: ring #c) (p:noncompact_poly_over_ring r{noncompact_poly_eq p Nil})
: Lemma (ensures poly_compact p == Nil) 
        (decreases length p) = 
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);    
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  if (length p = 0) then () else (
    poly_eq_nil_last_is_zero p;
    assert ((last_gtot p `r.eq` r.addition.neutral));
    assert (poly_compact p == poly_compact (except_last p));
    poly_compact_of_zeros_is_nil #c #r (except_last p);
    ()
  )

let poly_eq_nil_means_compact_is_nil #c (#r: ring #c) (p: noncompact_poly_over_ring r{noncompact_poly_eq p Nil}) 
  : Lemma (poly_compact p == Nil) = 
  match p with 
  | Nil -> () 
  | ph::pt -> poly_compact_of_zeros_is_nil p

let rec poly_add_respects_poly_eq #c (#r: ring #c) 
                                     (x y: noncompact_poly_over_ring r) 
                                     (z: noncompact_poly_over_ring r{noncompact_poly_eq y z})
  : Lemma (ensures noncompact_poly_eq (noncompact_poly_add x y) (noncompact_poly_add x z) /\
                   noncompact_poly_eq (noncompact_poly_add y x) (noncompact_poly_add z x)) =
  let (| (+),           eq,   zero               |) = 
      (| r.addition.op, r.eq, r.addition.neutral |) in
  reveal_opaque (`%is_symmetric) (is_symmetric #c);                     // a `eq` b <==> b `eq` a
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);          // p `poly_eq` p for any polynomial p
  match (x,y,z) with
  | t::tt, s::ss, Nil -> neutral_equivalent_is_neutral (+) eq zero s;      // ring zero is necessarily  unique
                      neutral_lemma (+) eq s t;                         // 0+a = a+0 = a
                      poly_add_respects_poly_eq #c #r tt ss Nil         // recursive call
  | t::tt, Nil, s::ss -> neutral_equivalent_is_neutral (+) eq zero s;
                      neutral_lemma r.addition.op eq s t;
                      poly_add_respects_poly_eq #c #r tt Nil ss
  | t::tt, s::ss, u::uu ->equivalence_wrt_operation_lemma #c  #(+) eq s u t;
                      poly_add_respects_poly_eq #c #r tt ss uu
  | _ -> ()
(*
  | Nil, Nil, Nil -> ()
  | t::tt, Nil, Nil -> () // less than 2 nonzero objects case is proven automatically
  | Nil, t::tt, Nil -> () 
  | Nil, Nil, t::tt -> () 
*)

let nc_poly_eq #c (#r: ring #c) : equivalence_relation (noncompact_poly_over_ring r) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #(noncompact_poly_over_ring r));
  reveal_opaque (`%is_transitive) (is_transitive #(noncompact_poly_over_ring r));
  reveal_opaque (`%is_symmetric) (is_symmetric #(noncompact_poly_over_ring r));
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);    
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  noncompact_poly_eq #c #r
    
let rec noncompact_poly_negate #c (#r: ring #c) (p: noncompact_poly_over_ring r) : (q: noncompact_poly_over_ring r{ contains_no_nonzeros (noncompact_poly_add q p) }) = 
  match p with
  | ph::pt -> (r.addition.inv ph) :: (noncompact_poly_negate #c #r pt)
  | Nil -> Nil

let poly_add_is_commutative #c (#r: ring #c) (p q: poly_over_ring r) : Lemma (poly_add p q `poly_eq` poly_add q p) =  
  reveal_opaque (`%is_reflexive) (is_reflexive #(poly_over_ring r));
  reveal_opaque (`%is_transitive) (is_transitive #(poly_over_ring r));
  reveal_opaque (`%is_symmetric) (is_symmetric #(poly_over_ring r));
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);    
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  noncompact_poly_add_is_commutative #c #r p q 

let poly_add_is_associative #c (#r: ring #c) (p q w: poly_over_ring r) : Lemma (poly_add p (poly_add q w) `poly_eq` poly_add (poly_add p q) w) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #(poly_over_ring r));
  reveal_opaque (`%is_transitive) (is_transitive #(poly_over_ring r));
  reveal_opaque (`%is_symmetric) (is_symmetric #(poly_over_ring r));
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
    
  } ; 
  //assert (poly_add p (q `noncompact_poly_add` w) `poly_eq` poly_add (p `noncompact_poly_add` q) w); 
()
 
let field_poly_add_is_assoc #c (#f: field #c) (p q r: poly_over_field f) : Lemma (poly_add p (poly_add q r) `poly_eq` poly_add (poly_add p q) r) = 
  poly_add_is_associative #c #f p q r
