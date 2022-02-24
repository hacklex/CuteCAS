module Polynomials.Multiplication
 
open AlgebraTypes
  
open FStar.Seq.Extras
open FStar.Seq
open FStar.Seq.Base
open FStar.Seq.Properties

open Polynomials.Definition
open Polynomials.Equivalence
open Polynomials.Compact
open Polynomials.Addition

let stream_of_zeros #c (#r: commutative_ring #c) (n: pos) : (f:noncompact_poly_over_ring r{noncompact_poly_eq f empty}) = 
  let result = create n r.addition.neutral in
  zero_equals_self r;
  assert (for_all (fun x -> x `r.eq` r.addition.neutral) result);
  poly_of_zeros_equals_empty #c #r result;
  result  

#push-options "--ifuel 0 --fuel 3 --z3rlimit 48 --query_stats"
let monomial #c (r: commutative_ring #c) (a:c) (degree: nat) 
  : Tot(z:noncompact_poly_over_ring r{
                                       is_nonempty z /\ (last z == a) /\ 
                                       noncompact_poly_eq (liat z) empty /\
                                       r.eq (last z) a
                                     }) 
  (decreases degree) = 
  equals_self r a;
  if degree=0 then create 1 a
  else (stream_of_zeros #c #r (degree)) $+ a 

let nth_of_monomial #c (r: commutative_ring #c) (a:c) (deg: nat)
  : Lemma (forall (i: nat). (nth (monomial r a deg) i == (if (i=deg) then a else r.addition.neutral))) = ()

let monomial_length_is_deg #c (r: commutative_ring #c) (a:c) (deg: nat) : Lemma (length (monomial r a deg) = (1+deg)) = ()

let monomial_leading_coefficient_is_a #c (r: commutative_ring #c) (a:c) (deg: nat)
  : Lemma (nth (monomial r a deg) deg == a) = ()
  
let monomial_other_coefficients_are_zeros #c (r: commutative_ring #c) (a:c) (deg: nat) (i: nat{i<>deg})
  : Lemma (nth (monomial r a i) deg == r.addition.neutral) = ()

let monomials_equality_lemma #c (r: commutative_ring #c) (a:c) (b:c{r.eq a b}) (degree: nat)
  : Lemma (ensures ncpoly_eq (monomial r a degree) (monomial r b degree)) (decreases degree) 
  = if degree > 0 then eq_of_snoc (stream_of_zeros #c #r degree) a b  

let get_int_range (n: nat) : (f:seq (t:nat{t<n}){length f = n /\ (forall (k:nat{k<n}). index f k = k) })
  = let rec aux (k:nat{k<=n}) : Tot (z:seq (t:nat{t<n}){length z=k /\ (forall (id:nat{id<k}). index z id == id ) }) 
                                 (decreases k) 
                           = if k=0 then empty
                             else Seq.Properties.snoc (aux (k-1)) (k-1)
                           in
    aux (n)
  
let get_indices #a (s: seq a) : seq (i:nat{i<length s}) = 
  get_int_range (length s)

open MatrixIndexTransform

let index_for #a (p: seq a) = t:nat{t<length p}

let poly_unit #c (#r: commutative_ring #c) : noncompact_poly_over_ring r = empty 
let poly_add_op #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r) 
  : Tot(noncompact_poly_over_ring r) = noncompact_poly_add p q 
let poly_equiv #c (#r: commutative_ring #c) = 
  Algebra.CommMonoid.Equiv.EQ (fun (x y : noncompact_poly_over_ring r) -> ncpoly_eq #c #r x y) 
  ncpoly_eq_is_reflexive_lemma ncpoly_eq_is_symmetric_lemma ncpoly_eq_is_transitive_lemma   
let poly_identity_lemma #c (#r: commutative_ring #c) (x:noncompact_poly_over_ring r) 
  : Lemma ((poly_equiv #c #r).eq (poly_add_op #c #r (poly_unit #c #r) x) x) = poly_add_identity #c #r x   
let commutativity #c (#r: commutative_ring #c) (x y: noncompact_poly_over_ring r)
  : Lemma ((poly_equiv #c #r).eq (poly_add_op #c #r  x y) (poly_add_op #c #r  y x)) = noncompact_poly_add_is_commutative x y  
let associativity #c (#r: commutative_ring #c) (x y z: noncompact_poly_over_ring r)
  : Lemma ((poly_equiv #c #r).eq (poly_add_op #c #r  (poly_add_op #c #r  x y) z) (poly_add_op #c #r  x (poly_add_op #c #r  y z))) 
  = noncompact_poly_add_is_associative x y z;
    symm_lemma ncpoly_eq (x `poly_add_op #c #r` poly_add_op #c #r y z) (poly_add_op #c #r x y `poly_add_op #c #r` z) 

let  ( *) = op_Multiply 
// definitely not Latin or smth
 
#pop-options

let int_range_len_lemma (n: nat) : Lemma (length (get_int_range n) = n) = ()

#push-options "--ifuel 2 --fuel 2 --z3rlimit 15 --query_stats"

unfold let index_matrix #a (m n: pos) (s: seq a{length s=m*n})  (i: under m) (j: under n) : a =
  flattened_index_is_under_flattened_size m n i j;
  index s (i*n + j)

let map_seq_index_forall #a #b (f:a->b) (s: seq a) 
  : Lemma (forall (i:nat{i<length s}). (map_seq_len f s; index (map_seq f s) i == f (index s i))) 
  = map_seq_len f s; 
    Classical.forall_intro (map_seq_index f s)
     
let poly_product_monomial #c (#r: commutative_ring #c) 
                          (p q: (t:noncompact_poly_over_ring r{is_nonempty t})) 
                          (i: under (length p)) (j: under (length q))
  : (z:noncompact_poly_over_ring r {z == (monomial r 
                                                   (r.multiplication.op (index p i) 
                                                                        (index q j)
                                                   ) 
                                                   (i+j)
                                         )
                                   }
    ) =  
   let ai = (index p i) in
   let bj = (index q j) in
   monomial r (r.multiplication.op ai bj) (i+j)
 
let poly_product_monomial_ij #c (#r: commutative_ring #c) 
                          (p q: (t:noncompact_poly_over_ring r{is_nonempty t})) 
                          (ij: under (length p * length q)) 
  : (z:noncompact_poly_over_ring r {z == (monomial r 
                                                   (r.multiplication.op (index p (get_i (length p) (length q) ij)) 
                                                                        (index q (get_j (length p) (length q) ij))
                                                   ) 
                                                   ((get_i (length p) (length q) ij)+(get_j (length p) (length q) ij))
                                         )
                                   }
    ) = poly_product_monomial p q (get_i (length p) (length q) ij) (get_j (length p) (length q) ij)

let poly_product_monomial_matrix #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r)
  : Pure (z:seq (noncompact_poly_over_ring r){length z = length p * length q}) 
         (requires is_nonempty p /\ is_nonempty q)
         (ensures fun x -> ( (forall (i: index_for p) (j: index_for q). index x (get_ij (length p) (length q) i j)  == poly_product_monomial p q i j ) /\ 
                           (forall (ij: under (length p * length q)). (index x ij) == (poly_product_monomial_ij p q ij)) ) )  = 
  let mn = length p * length q in
  let m = length p in
  let n = length q in
  let flat_indices : seq (t:nat{t<mn}) = get_int_range (mn) in 
  map_seq_len (poly_product_monomial_ij p q) flat_indices;
  let result = map_seq (poly_product_monomial_ij p q) flat_indices in
  let aux (i: index_for p) (j: index_for q) 
    : Lemma (index (map_seq (poly_product_monomial_ij p q) flat_indices) (get_ij (length p) (length q) i j) == poly_product_monomial p q i j) 
    = 
      consistency_of_i_j m n i j;
      consistency_of_ij m n (get_ij m n i j);
      assert (poly_product_monomial_ij p q (get_ij m n i j) == poly_product_monomial p q i j);
      map_seq_index (poly_product_monomial_ij p q) flat_indices (get_ij m n i j);    
    () in
  let aux1 (ij: under (length p * length q)) : Lemma (index (map_seq (poly_product_monomial_ij p q) flat_indices) ij == poly_product_monomial_ij p q ij) 
    = map_seq_index (poly_product_monomial_ij p q) flat_indices ij;
    () in 
  Classical.forall_intro aux1;
  Classical.forall_intro_2 aux;
  result
  
let poly_product_monomial_matrix_transpose_lemma #c (#r: commutative_ring #c) (p q: (t:noncompact_poly_over_ring r{is_nonempty t}))
  : Lemma (forall (i: index_for p) (j: index_for q). (poly_product_monomial p q i j `ncpoly_eq` poly_product_monomial q p j i)) = 
  let aux (i: index_for p) (j: index_for q) : Lemma (poly_product_monomial p q i j `ncpoly_eq` poly_product_monomial q p j i) = 
    monomials_equality_lemma r (r.multiplication.op (index p i) (index q j)) (r.multiplication.op (index q j) (index p i)) (i+j);
  () in Classical.forall_intro_2 aux 

let poly_product_coefficient_is_commutative #c (#r: commutative_ring #c) (p q: (t:noncompact_poly_over_ring r{is_nonempty t})) 
                                                                         (ij: under (length p * length q))
  : Lemma (poly_product_monomial_ij p q ij `ncpoly_eq` poly_product_monomial_ij q p (transpose_ji (length p) (length q) ij)) 
  = 
  dual_indices (length p) (length q) ij;
  poly_product_monomial_matrix_transpose_lemma p q;
  ()

let transpose_inequality_lemma (m n: pos) (ij: under (m*n)) (kl: under (n*m)) 
  : Lemma (requires kl <> ij) (ensures transpose_ji m n ij <> transpose_ji m n kl) = 
  dual_indices m n ij;
  dual_indices m n kl

#push-options "--ifuel 0 --fuel 1 --z3rlimit 10 --query_stats"
let poly_product_monomial_matrix_transposed_eq_lemma #c (#r: commutative_ring #c) (p q: (t:noncompact_poly_over_ring r{is_nonempty t})) (ij: under (length p * length q)) : Lemma (ncpoly_eq (index (poly_product_monomial_matrix p q) ij) (index  (poly_product_monomial_matrix q p) (transpose_ji (length p) (length q) ij))) = 
  let i = get_i (length p) (length q) ij in 
  let j = get_j (length p) (length q) ij in 
  dual_indices (length p) (length q) ij;
  monomials_equality_lemma r (r.multiplication.op (index p i) (index q j)) (r.multiplication.op (index q j) (index p i)) (i+j);
  ()

let poly_product_monomial_matrix_permutation_lemma #c (#r: commutative_ring #c) (p q: (t: noncompact_poly_over_ring r{is_nonempty t}))
  : Lemma (is_permutation' poly_equiv (poly_product_monomial_matrix p q) (poly_product_monomial_matrix q p) (transpose_ji (length p) (length q))) 
  = 
  Classical.forall_intro (poly_product_monomial_matrix_transposed_eq_lemma p q); 
  Classical.forall_intro_2 (Classical.move_requires_2 (transpose_inequality_lemma (length p) (length q)));
  reveal_is_permutation' poly_equiv (poly_product_monomial_matrix p q) 
                                    (poly_product_monomial_matrix q p)
                                    (transpose_ji (length p) (length q))

private let poly_add_commutative_monoid #c (r: commutative_ring #c) 
  = Algebra.CommMonoid.Equiv.CM #(noncompact_poly_over_ring r) 
                                #(poly_equiv) 
                                poly_unit 
                                poly_add_op 
                                poly_identity_lemma 
                                associativity 
                                commutativity 
                                poly_add_congruence_lemma 

let poly_mul #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r) 
  : noncompact_poly_over_ring r 
  = if (is_empty p || is_empty q) then empty
    else Seq.Permutation.foldm_snoc (poly_add_commutative_monoid #c r) 
                                    (poly_product_monomial_matrix p q)

let rec poly_sum_batch #c (#r: commutative_ring #c) (p: seq (noncompact_poly_over_ring r)) (q: seq (noncompact_poly_over_ring r))
  : Pure (s: seq (noncompact_poly_over_ring r){length s = length p})
         (requires length q = length p)
         (ensures fun s -> forall (x:index_for s). index s x == noncompact_poly_add (index p x) (index q x))
         (decreases length p) =         
    if length p = 0 then empty
    else Seq.Properties.cons (noncompact_poly_add (Seq.Properties.head p) (Seq.Properties.head q)) 
                             (poly_sum_batch (Seq.Properties.tail p) (Seq.Properties.tail q))
          
 
let rec big_sum #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq) 
                 (n0: int) (nk: int{nk >= n0}) (expr: (t:int{t>=n0 /\ t<=nk}) -> c) 
                 : Pure (c) 
                 (requires True)  
                 (ensures (fun (x:c) -> ( (nk=n0) ==> (x == expr nk )))) 
                 (decreases nk-n0) = 
  if nk = n0 then expr nk
  else (big_sum cm n0 (nk-1) expr) `cm.mult` expr nk

let rec big_sum_equality #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq) (n0: int) (nk: int{nk>=n0}) (expr1: int->c) (expr2: int->c)
  : Lemma (requires (forall (i: int{i>=n0 && i<=nk}). expr1 i == expr2 i))
          (ensures big_sum cm n0 nk expr1 == big_sum cm n0 nk expr2)
          (decreases nk-n0) = 
  if nk>n0 then big_sum_equality cm n0 (nk-1) expr1 expr2 
  

let big_sum_snoc #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq) 
                 (n0: nat) (nk: nat{nk > n0}) (expr: (t:nat{t>=n0 /\ t<=nk}) -> c) 
                 : Lemma (big_sum cm n0 nk expr == big_sum cm n0 (nk-1) expr `cm.mult` (expr nk)) = ()

unfold let foldm_snoc #c #eq = FStar.Seq.Permutation.foldm_snoc #c #eq

#push-options "--ifuel 0 --fuel 1 --z3rlimit 3 --query_stats"
let rec big_sum_equals_foldm #c #eq 
                             (cm: Algebra.CommMonoid.Equiv.cm c eq) 
                             (n0:int) 
                             (nk:int{nk>=n0}) 
                             (expr: (t:int{t>=n0 && t<=nk})->c)
  : Lemma (ensures big_sum cm n0 nk expr `eq.eq` foldm_snoc cm (init (nk+1-n0) (fun (i: under (nk+1-n0)) -> expr (n0+i))))
          (decreases nk-n0) = 
  if (nk=n0) then (
   let ts = init (nk+1-n0) (fun (i: under (nk+1-n0)) -> expr (n0+i)) in
   lemma_eq_elim (create 1 (expr nk)) ts; 
   Seq.Permutation.foldm_snoc_singleton cm (expr nk);   
   eq.symmetry (foldm_snoc cm ts) (expr nk);
   eq.reflexivity (expr nk); 
   eq.transitivity (big_sum cm n0 nk expr) (expr nk) (foldm_snoc cm ts); 
   ()
  )
  else (
    let lhs = big_sum cm n0 nk expr in
    let rhs = foldm_snoc cm (init (nk+1-n0) (fun (i: under (nk+1-n0)) -> expr (n0+i))) in
    let fullseq = init (nk+1-n0) (fun (i: under (nk+1-n0)) -> expr (n0+i)) in    
    let subseq = init (nk-n0) (fun (i: under (nk-n0)) -> expr (n0+i)) in
    let subsum = big_sum cm n0 (nk-1) expr in
    let fullfold = foldm_snoc cm fullseq in
    let subfold = foldm_snoc cm subseq in
    let last = expr nk in
    let op = cm.mult in
    big_sum_equals_foldm cm n0 (nk-1) expr;    
    lemma_eq_elim (init ((nk-1)+1-n0) (fun (i: under ((nk-1)+1-n0)) -> expr (n0+i))) subseq;
    // yes! [(nk-1)+1-n0 == nk-n0] is not enough!
    // assert (subsum `eq.eq` foldm_snoc cm subseq); -- comes from recursion
    // assert (lhs == subsum `cm.mult` (expr nk)); -- by the definition of big_sum
    lemma_eq_elim (fst (un_snoc fullseq)) subseq; // subseq is literally (liat fullseq)
    // what we already have: rhs == (expr nk) + (foldm_snoc cm subseq)
    // what we want: rhs `eq.eq` (foldm_snoc cm subseq) + (expr nk)
    cm.commutativity last subfold;
    eq.reflexivity last; 
    // subsum * last `eq` subfold * last -- from congruence
    cm.congruence subsum last subfold last;
    eq.symmetry rhs (subfold `op` last);
    eq.transitivity lhs (subfold `op` last) rhs;
    ()
  )

let bounds_lemma (n0:int) (nk: int{nk>=n0}) (i:nat{i<(nk+1-n0)}) : Lemma (n0+i >= n0 /\ n0+i <= nk) = ()

let fold_decomposition_aux #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq)
                           (n0: int) 
                           (nk: int{nk=n0}) 
                           (expr1 expr2: (t:int{t>=n0 /\ t<=nk}) -> c)
  : Lemma (foldm_snoc cm (init (nk+1-n0) (fun i -> expr1 (n0+i) `cm.mult` expr2 (n0+i))) `eq.eq`
           cm.mult (foldm_snoc cm (init (nk+1-n0) (fun i -> expr1 (n0+i)))) 
                   (foldm_snoc cm (init (nk+1-n0) (fun i -> expr2 (n0+i))))) =  
    lemma_eq_elim (init (nk+1-n0) (fun i -> expr1 (n0+i) `cm.mult` expr2 (n0+i))) 
                  (create 1 (expr1 n0 `cm.mult` expr2 n0));
    Seq.Permutation.foldm_snoc_singleton cm (expr1 n0 `cm.mult` expr2 n0);
    let ts = (init (nk+1-n0) (fun i -> expr1 (n0+i) `cm.mult` expr2 (n0+i))) in
    let lhs = foldm_snoc cm ts in
    let ts1 = (init (nk+1-n0) (fun i -> expr1 (n0+i))) in
    let ts2 = (init (nk+1-n0) (fun i -> expr2 (n0+i))) in
    let rhs = cm.mult (foldm_snoc cm ts1) (foldm_snoc cm ts2) in
    eq.symmetry (foldm_snoc cm ts) (expr1 n0 `cm.mult` expr2 n0);
    eq.reflexivity ((fun (i:nat{i<(nk+1-n0)}) -> bounds_lemma n0 nk i;  expr1 (n0+i) `cm.mult` expr2 (n0+i)) (nk-n0)); 
    assert (foldm_snoc cm ts `eq.eq`  ((fun i -> bounds_lemma n0 nk i; 
                                              expr1 (n0+i) `cm.mult` expr2 (n0+i)) 
                                      (nk-n0))); //lambda call.
    assert ( ((fun i -> bounds_lemma n0 nk i; expr1 (n0+i) `cm.mult` expr2 (n0+i)) (nk-n0)) ==
      cm.mult (expr1 (n0)) (expr2 (n0)));
    assert (lhs `eq.eq` cm.mult (expr1 nk) (expr2 nk));  
    assert (equal ts1 (create 1 (expr1 nk)));
    Seq.Permutation.foldm_snoc_singleton cm (expr1 nk);    
    assert (eq.eq (foldm_snoc cm ts1) (expr1 nk));
    Seq.Permutation.foldm_snoc_singleton cm (expr2 nk);    
    assert (eq.eq (foldm_snoc cm ts2) (expr2 nk));
    cm.congruence (foldm_snoc cm ts1) (foldm_snoc cm ts2) (expr1 nk) (expr2 nk);
    assert (rhs `eq.eq` (cm.mult (expr1 nk) (expr2 nk)));
    eq.symmetry rhs (cm.mult (expr1 nk) (expr2 nk));
    eq.transitivity lhs (cm.mult (expr1 nk) (expr2 nk)) rhs 

let aux_shuffle_lemma #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq) (s1 s2 l1 l2: c)
  : Lemma (((s1 `cm.mult` s2) `cm.mult` (l1 `cm.mult` l2)) `eq.eq`  
           ((s1 `cm.mult` l1) `cm.mult` (s2 `cm.mult` l2))) =  
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 (Classical.move_requires_2 eq.symmetry);
  Classical.forall_intro_2 (Classical.move_requires_2 cm.commutativity);
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity); 
  let (+) = cm.mult in
  let (=) = eq.eq in
  let assoc = cm.associativity in
  let s12 = s1 + s2 in
  let lhs = (s1+s2)+(l1+l2) in
  assoc s12 l1 l2 ;
  assert (lhs = (s12 + l1) + l2);
  assoc s1 s2 l1;
  assert (((s1+s2)+l1) = (s1+(s2+l1)));
  cm.congruence (s1+s2) l1 (s2+s1) l1;
  assert (((s1+s2)+l1) = ((s2+s1)+l1));
  cm.congruence ((s1+s2)+l1) l2 ((s2+s1)+l1) l2;
  assert (lhs = (((s2+s1)+l1)+l2));
  assoc s2 s1 l1;
  cm.congruence ((s2+s1)+l1) l2 (s2+(s1+l1)) l2;
  assert (lhs = ((s2+(s1+l1))+l2));
  cm.congruence (s2+(s1+l1)) l2 ((s1+l1)+s2) l2;
  
  assert (lhs = (((s1+l1)+s2)+l2));
  assoc (s1+l1) s2 l2;
  assert (lhs = ((s1+l1)+(s2+l2)));  
  ()

#push-options "--ifuel 0 --fuel 1 --z3rlimit 5 --query_stats"
 
#push-options "--ifuel 0 --fuel 1 --z3rlimit 2 --z3refresh --query_stats"
let rec fold_decomposition_clean #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq)
                           (n0: int) 
                           (nk: int{nk>=n0}) 
                           (expr1 expr2: int -> c)
  : Lemma (ensures foldm_snoc cm (init (nk+1-n0) (fun i -> expr1 (n0+i) `cm.mult` expr2 (n0+i)))
          `eq.eq` (foldm_snoc cm (init (nk+1-n0) (fun i -> expr1 (n0+i))) 
         `cm.mult` foldm_snoc cm (init (nk+1-n0) (fun i -> expr2 (n0+i)))))
          (decreases nk-n0) = 
  if (nk=n0) then fold_decomposition_aux cm n0 nk expr1 expr2  else (  
    Classical.forall_intro_2 (Classical.move_requires_2 cm.commutativity);
    Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity); 
    let op = cm.mult in
    let fold s = foldm_snoc #c #eq cm s in
    let left_func : (i:nat{i<(nk+1-n0)}) -> c = fun i -> expr1 (n0+i) `op` expr2 (n0+i) in
    let fullseq = init (nk+1-n0) left_func in
    let lhs = fold fullseq in
    let right_func1 : (i:nat{i<(nk+1-n0)}) -> c = fun i -> expr1 (n0+i) in
    let right_func2 : (i:nat{i<(nk+1-n0)}) -> c = fun i -> expr2 (n0+i) in
    let fullseq_r1 = init (nk+1-n0) right_func1 in
    let fullseq_r2 = init (nk+1-n0) right_func2 in
    let rhs = (fold fullseq_r1) `op` (fold fullseq_r2) in
    fold_decomposition_clean cm n0 (nk-1) expr1 expr2;
    let subseq = init (nk-n0) left_func in
    let subfold = fold subseq in
    let last = left_func (nk-n0) in
    lemma_eq_elim (fst (un_snoc fullseq)) subseq;    
    let subseq_r1 = init (nk-n0) right_func1 in
    let subseq_r2 = init (nk-n0) right_func2 in  
    lemma_eq_elim subseq (init ((nk-1)+1-n0) (fun i -> expr1 (n0+i) `op` expr2 (n0+i)));       
    let subfold_r1 = foldm_snoc cm subseq_r1 in
    let subfold_r2 = foldm_snoc cm subseq_r2 in 
    lemma_eq_elim subseq_r1 (init ((nk-1)+1-n0) (fun i -> expr1 (n0+i)));
    lemma_eq_elim subseq_r2 (init ((nk-1)+1-n0) (fun i -> expr2 (n0+i))); 
    cm.congruence (foldm_snoc cm (init ((nk-1)+1-n0) (fun i -> expr1 (n0+i)))) 
                  (foldm_snoc cm (init ((nk-1)+1-n0) (fun i -> expr2 (n0+i))))
                  subfold_r1 subfold_r2; 
    let last_r1 = right_func1 (nk-n0) in
    let last_r2 = right_func2 (nk-n0) in
    lemma_eq_elim (fst (un_snoc fullseq_r1)) subseq_r1; // subseq is literally (liat fullseq)
    lemma_eq_elim (fst (un_snoc fullseq_r2)) subseq_r2;
    cm.congruence subfold last (subfold_r1 `op` subfold_r2) last;
    aux_shuffle_lemma cm subfold_r1 subfold_r2 last_r1 last_r2;    
    cm.congruence (subfold_r1 `op` last_r1) (subfold_r2 `op` last_r2) (foldm_snoc cm fullseq_r1) (foldm_snoc cm fullseq_r2) 
) 

type comm_monoid c eq = Algebra.CommMonoid.Equiv.cm c eq 

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1 --query_stats"
let big_sum_decomposition #c #eq 
                              (cm: Algebra.CommMonoid.Equiv.cm c eq) 
                              (n0: int) 
                              (nk: int{nk>=n0}) 
                              (expr1 expr2: (t:int{t>=n0 && t<=nk}) -> c)
  : Lemma (big_sum cm n0 nk (fun (i:int{i>=n0 && i<=nk}) -> expr1 i `cm.mult` expr2 i) 
   `eq.eq` (cm.mult (big_sum cm n0 nk expr1) (big_sum cm n0 nk expr2))) =  
    Classical.forall_intro_2 (Classical.move_requires_2 eq.symmetry);
    Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
    let op = cm.mult in
    let make_seq (expr: (t:int{t>=n0 /\ t<=nk}) -> c) = init (nk+1-n0) (fun (i:under (nk+1-n0)) -> expr (n0+i)) in 
    let sum_expr : ((t:int{t>=n0 /\ t<=nk}) -> c) = fun (i:int{i>=n0 && i<=nk}) -> expr1 i `op` expr2 i in
    big_sum_equals_foldm cm n0 nk sum_expr; 
    fold_decomposition_clean cm n0 nk expr1 expr2; 
    big_sum_equals_foldm cm n0 nk expr1;
    big_sum_equals_foldm cm n0 nk expr2;
    cm.congruence (foldm_snoc cm (make_seq expr1)) (foldm_snoc cm (make_seq expr2))
                  (big_sum cm n0 nk expr1) (big_sum cm n0 nk expr2) 


let matrix_seq #c #eq (cm: comm_monoid c eq) (m n: pos) (generator: (under m) -> (under n) -> c)
  : Pure (z:seq c{length z = m `op_Multiply` n}) 
         (requires True)
         (ensures fun x -> ( (forall (i: under m) (j: under n). index x (get_ij m n i j) == generator i j) /\ 
                           (forall (ij: under (m `op_Multiply` n)). (index x ij) == ( generator (get_i m n ij) (get_j m n ij)))))  = 
  let ( *) = op_Multiply in                           
  let mn = m * n in
  let generator_ij ij = generator (get_i m n ij) (get_j m n ij) in
  let flat_indices : seq (t:nat{t<mn}) = get_int_range (mn) in 
  map_seq_len generator_ij flat_indices;
  let result = map_seq generator_ij flat_indices in
  let aux (i: under m) (j: under n) 
    : Lemma (index (map_seq generator_ij flat_indices) (get_ij m n i j) == generator i j) 
    = 
      consistency_of_i_j m n i j;
      consistency_of_ij m n (get_ij m n i j);
      assert (generator_ij (get_ij m n i j) == generator i j);
      map_seq_index generator_ij flat_indices (get_ij m n i j);    
    () in
  let aux1 (ij: under mn) : Lemma (index (map_seq generator_ij flat_indices) ij == generator_ij ij) 
    = map_seq_index generator_ij flat_indices ij;
    () in 
  Classical.forall_intro aux1;
  Classical.forall_intro_2 aux;
  result

#push-options "--ifuel 1 --fuel 0 --z3rlimit 10 --query_stats"

let matrix_snoc #c #eq (cm: comm_monoid c eq) (m n: pos) (generator: (under m) -> (under n) -> c)
  : Lemma (matrix_seq cm m n generator `equal` append (slice (matrix_seq cm m n generator) 0 ((m-1)*n))
                                                      (slice (matrix_seq cm m n generator) ((m-1)*n) (m*n))) = ()

let matrix_sum_snoc #c #eq (cm: comm_monoid c eq) (m n: pos) (generator: (under m) -> (under n) -> c)
  : Lemma (foldm_snoc cm (matrix_seq cm m n generator) `eq.eq` (cm.mult
           (foldm_snoc cm (slice (matrix_seq cm m n generator) 0 ((m-1)*n)))
           (foldm_snoc cm (slice (matrix_seq cm m n generator) ((m-1)*n) (m*n))))) = 
           Seq.Permutation.foldm_snoc_append cm (slice (matrix_seq cm m n generator) 0 ((m-1)*n))
                                                (slice (matrix_seq cm m n generator) ((m-1)*n) (m*n));
           lemma_eq_elim (matrix_seq cm m n generator) (append (slice (matrix_seq cm m n generator) 0 ((m-1)*n))
                                                (slice (matrix_seq cm m n generator) ((m-1)*n) (m*n))) 

let matrix_last_line_equals_big_sum #c #eq (cm: comm_monoid c eq) (m n: pos) (generator: (under m) -> (under n) -> c) 
  : Lemma (foldm_snoc cm (slice (matrix_seq cm m n generator) ((m-1)*n) (m*n)) `eq.eq` big_sum cm 0 (n-1) (fun (j: under n) -> generator (m-1) j)) = 
  big_sum_equals_foldm cm 0 (n-1) (fun j -> generator (m-1) j);
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 (Classical.move_requires_2 eq.symmetry);
  Classical.forall_intro_2 (Classical.move_requires_2 cm.commutativity);
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity); 
  
  assert (big_sum cm 0 (n-1) (fun j -> generator (m-1) j) `eq.eq`  
          foldm_snoc cm (init ((n-1)+1-0) (fun j -> generator (m-1) (j+0))) 
          );
  admit();
          
  assert (slice (matrix_seq cm m n generator) ((m-1)*n) (m*n) `equal` init n (fun (j: under n) -> generator (m-1) j));
  lemma_eq_elim (slice (matrix_seq cm m n generator) ((m-1)*n) (m*n)) (init n (fun (j: under n) -> generator (m-1) j));
  assert (foldm_snoc cm (slice (matrix_seq cm m n generator) ((m-1)*n) (m*n)) ==
          foldm_snoc cm (init n (fun (j: under n) -> generator (m-1) j)));

 
          ()
           
let rec matrix_seq_fold_equals_big_sum #c #eq (cm: comm_monoid c eq) (m n: pos)  (generator: int -> int -> c) 
  : Lemma (ensures foldm_snoc cm (matrix_seq cm m n generator) `eq.eq` 
           big_sum cm 0 (m-1) (fun (i:under m) -> big_sum cm 0 (n-1) (fun (j:under n) -> generator i j))) (decreases %[m;n])= 
  let lhs = foldm_snoc cm (matrix_seq cm m n generator) in
  let rhs = big_sum cm 0 (m-1) (fun (i:under m) -> big_sum cm 0 (n-1) (fun (j:under n) -> generator i j)) in
  let matrix = matrix_seq cm m n generator in
  let line_lemma (i: under m) 
    : Lemma (big_sum cm 0 (n-1) (fun (j:under n) -> generator i j) `eq.eq` 
             foldm_snoc cm (slice matrix (i*n) (i*n+n))) = 
    assert (slice matrix (i*n) (i*n+n) `equal` (init n (fun (j:under n) -> generator i j)));
    let gen_fun (j: under n) = generator i j in
    let lhs_bigsum = big_sum cm 0 (n-1) gen_fun in
    let sliced = slice matrix (i*n) (i*n + n) in
    lemma_eq_elim (init ((n-1) + 1 - 0) gen_fun) (init n gen_fun);
    big_sum_equals_foldm cm 0 (n-1) gen_fun;
    assert (eq.eq (big_sum cm 0 (n-1) gen_fun) (foldm_snoc cm (init n (fun j -> gen_fun (0+j) )  )));
    admit();
    lemma_eq_elim sliced (init n (fun (j:under n) -> generator i j));
    Classical.forall_intro eq.reflexivity;     
    assert (foldm_snoc cm sliced == foldm_snoc cm (init n (fun (j:under n) -> generator i j)));
    eq.transitivity (big_sum cm 0 (n-1) gen_fun)
                    (foldm_snoc cm (init n (fun (j:under n) -> generator i j)))
                    (foldm_snoc cm sliced);
    assert (eq.eq (big_sum cm 0 (n-1) gen_fun) (foldm_snoc cm sliced)); 
    () in
  if (m=1) then (
    assert (matrix `equal` slice matrix 0 n);
    line_lemma 0;
    assert (foldm_snoc cm (matrix_seq cm m n generator) == foldm_snoc cm (slice matrix 0 n));
    assert (m-1 = 0); 
    let general_func i = big_sum cm 0 (m-1) (fun j -> generator i j) in
      
    assert (big_sum cm 0 (m-1) general_func == big_sum cm 0 (m-1) (fun j -> generator 0 j));
    big_sum_equality cm 0 (m-1) general_func (fun j -> generator 0 j);
    admit();
    assert (rhs == big_sum cm 0 (m-1) general_func);
//    assert (rhs == big_sum cm 0 (m-1) outer_func); 
    ()
  ) else ( 
    admit();
    ()
  )


let double_sum_flatten #c #eq (cm: comm_monoid c eq)
                              (m0: int) (mk: int{mk>=m0})
                              (n0: int) (nk: int{nk>=n0})
                              (expr: int -> int -> c)
  : Lemma (ensures big_sum cm m0 mk (fun m -> big_sum cm n0 nk (fun n -> expr m n)) `eq.eq`
                   foldm_snoc cm (init ((mk+1-m0) `op_Multiply` (nk+1-n0)) (fun ij -> expr (ij / (nk+1-n0)) (ij % (nk+1-n0))))) 
          (decreases %[(mk-m0); (nk-n0)]) = 
  let lhs = big_sum cm m0 mk (fun m -> big_sum cm n0 nk (fun n -> expr m n)) in
  let p = (mk+1-m0) in
  let q = (nk+1-n0) in
  if (mk=m0) then (
    assert (mk == m0);
    assert (p=1);
    assert (lhs == big_sum cm n0 nk (fun n -> expr mk n));
    admit();
    ()
  ) else admit()

let double_fold_swap #c #eq (cm: comm_monoid c eq)
                            (m0: int) (mk: int{mk>=m0})
                            (n0: int) (nk: int{nk>=n0})
                            (expr: int -> int -> c)
  : Lemma (ensures big_sum cm m0 mk (fun m -> big_sum cm n0 nk (fun n -> expr m n)) `eq.eq`
                   big_sum cm n0 nk (fun n -> big_sum cm m0 mk (fun m -> expr m n))) = admit()

let rec fold_decomposition #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq)
                           (n0: int) 
                           (nk: int{nk>=n0}) 
                           (expr1 expr2: (t:int{t>=n0 /\ t<=nk}) -> c)
  : Lemma (ensures foldm_snoc cm (init (nk+1-n0) (fun (i:nat{i<(nk+1-n0)}) -> expr1 (n0+i) `cm.mult` expr2 (n0+i))) `eq.eq`
           cm.mult (foldm_snoc cm (init (nk+1-n0) (fun (i:nat{i<(nk+1-n0)}) -> expr1 (n0+i)))) 
                   (foldm_snoc cm (init (nk+1-n0) (fun (i:nat{i<(nk+1-n0)}) -> expr2 (n0+i)))))
          (decreases nk-n0) = 
  if (nk=n0) then fold_decomposition_aux cm n0 nk expr1 expr2  else (  
    Classical.forall_intro eq.reflexivity;
    Classical.forall_intro_2 (Classical.move_requires_2 eq.symmetry);
    Classical.forall_intro_2 (Classical.move_requires_2 cm.commutativity);
    Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity); 
    let op = cm.mult in
    let fold s = foldm_snoc #c #eq cm s in
    let left_func : (i:nat{i<(nk+1-n0)}) -> c = fun (i:nat{i<(nk+1-n0)}) -> expr1 (n0+i) `op` expr2 (n0+i) in
    let fullseq = init (nk+1-n0) left_func in
    let lhs = fold fullseq in
    let right_func1 : (i:nat{i<(nk+1-n0)}) -> c = fun (i:nat{i<(nk+1-n0)}) -> expr1 (n0+i) in
    let right_func2 : (i:nat{i<(nk+1-n0)}) -> c = fun (i:nat{i<(nk+1-n0)}) -> expr2 (n0+i) in
    let fullseq_r1 = init (nk+1-n0) right_func1 in
    let fullseq_r2 = init (nk+1-n0) right_func2 in
    let rhs = (fold fullseq_r1) `op` (fold fullseq_r2) in
    fold_decomposition cm n0 (nk-1) expr1 expr2;
    //assert (foldm_snoc cm (init ((nk-1)+1-n0) (fun i -> expr1 (n0+i) `cm.mult` expr2 (n0+i))) `eq.eq`
    //       cm.mult (foldm_snoc cm (init ((nk-1)+1-n0) (fun i -> expr1 (n0+i)))) 
    //               (foldm_snoc cm (init ((nk-1)+1-n0) (fun i -> expr2 (n0+i))))); 
    let subseq = init (nk-n0) left_func in
    //lemma_eq_elim (init ((nk-1)+1-n0) left_func) subseq;
    let subfold = foldm_snoc cm subseq in
    let last = left_func (nk-n0) in
    lemma_eq_elim (fst (un_snoc fullseq)) subseq; // subseq is literally (liat fullseq) 
    //cm.commutativity last subfold;
    //eq.reflexivity (foldm_snoc cm fullseq);  
    //assert (foldm_snoc cm fullseq == cm.mult last subfold);
    //assert (foldm_snoc cm fullseq `eq.eq` cm.mult subfold last);
    //assert (lhs `eq.eq` cm.mult subfold last); 
    //assert (rhs == foldm_snoc cm fullseq_r1 `cm.mult` foldm_snoc cm fullseq_r2);
    let subseq_r1 = init (nk-n0) right_func1 in
    let subseq_r2 = init (nk-n0) right_func2 in
    lemma_eq_elim (init ((nk-1)+1-n0) right_func1) subseq_r1;
    lemma_eq_elim (init ((nk-1)+1-n0) right_func2) subseq_r2; 
    lemma_eq_elim subseq (init ((nk-1)+1-n0) (fun i -> expr1 (n0+i) `cm.mult` expr2 (n0+i)));
    //assert (subseq `equal` (init ((nk-1)+1-n0) (fun i -> expr1 (n0+i) `cm.mult` expr2 (n0+i))));
    //assert (foldm_snoc cm (init ((nk-1)+1-n0) (fun i -> expr1 (n0+i) `cm.mult` expr2 (n0+i))) `eq.eq`
    //       cm.mult (foldm_snoc cm (init ((nk-1)+1-n0) (fun i -> expr1 (n0+i)))) 
    //               (foldm_snoc cm (init ((nk-1)+1-n0) (fun i -> expr2 (n0+i))))); 
    //assert (foldm_snoc cm subseq `eq.eq` cm.mult (foldm_snoc cm (init ((nk-1)+1-n0) (fun i -> expr1 (n0+i)))) 
    //               (foldm_snoc cm (init ((nk-1)+1-n0) (fun i -> expr2 (n0+i)))));  
    let subfold_r1 = foldm_snoc cm subseq_r1 in
    let subfold_r2 = foldm_snoc cm subseq_r2 in
    lemma_eq_elim subseq_r1 (init ((nk-1)+1-n0) (fun i -> expr1 (n0+i)));
    lemma_eq_elim subseq_r2 (init ((nk-1)+1-n0) (fun i -> expr2 (n0+i)));
    //eq.reflexivity subfold_r1;
    //eq.reflexivity subfold_r2; 
    cm.congruence  (foldm_snoc cm (init ((nk-1)+1-n0) (fun i -> expr1 (n0+i)))) 
                   (foldm_snoc cm (init ((nk-1)+1-n0) (fun i -> expr2 (n0+i))))
                   subfold_r1
                   subfold_r2;
    let last_r1 = right_func1 (nk-n0) in
    let last_r2 = right_func2 (nk-n0) in
    //assert (subfold `eq.eq` cm.mult subfold_r1 subfold_r2);  
    lemma_eq_elim (fst (un_snoc fullseq_r1)) subseq_r1; // subseq is literally (liat fullseq)
    lemma_eq_elim (fst (un_snoc fullseq_r2)) subseq_r2; // subseq is literally (liat fullseq) 
    //assert (last == last_r1 `cm.mult` last_r2);
    //eq.reflexivity last;
    //assert (lhs `eq.eq` (subfold `cm.mult` last));
    //assert (lhs `eq.eq` (subfold `cm.mult` (last_r1 `cm.mult` last_r2)));
    cm.congruence subfold last (subfold_r1 `cm.mult` subfold_r2) last;
    //assert ((subfold `cm.mult` last) `eq.eq` ((subfold_r1 `cm.mult` subfold_r2) `cm.mult` last));
    //eq.transitivity lhs (subfold `cm.mult` last) ((subfold_r1 `cm.mult` subfold_r2) `cm.mult` last);
    //assert (lhs `eq.eq` ((subfold_r1 `cm.mult` subfold_r2) `cm.mult` (last_r1 `cm.mult` last_r2)));
    aux_shuffle_lemma cm subfold_r1 subfold_r2 last_r1 last_r2;
    //eq.transitivity lhs  
    //                ((subfold_r1 `cm.mult` subfold_r2) `cm.mult` (last_r1 `cm.mult` last_r2))
    //                ((subfold_r1 `cm.mult` last_r1) `cm.mult` (subfold_r2 `cm.mult` last_r2));
    //assert (foldm_snoc cm fullseq_r1 == cm.mult last_r1 subfold_r1);
    //cm.commutativity last_r1 subfold_r1;
    //cm.commutativity last_r2 subfold_r2;
    //eq.reflexivity (foldm_snoc cm fullseq_r1);  
    //eq.reflexivity (foldm_snoc cm fullseq_r2);  
    //eq.symmetry (cm.mult last_r1 subfold_r1) (cm.mult subfold_r1 last_r1);
    //eq.symmetry (cm.mult last_r2 subfold_r2) (cm.mult subfold_r2 last_r2);
    //assert (cm.mult subfold_r1 last_r1 `eq.eq` foldm_snoc cm fullseq_r1 ); 
    //assert (cm.mult subfold_r2 last_r2 `eq.eq` foldm_snoc cm fullseq_r2 ); 
    //assert (cm.mult last_r1 subfold_r1 == foldm_snoc cm fullseq_r1);
    
    cm.congruence (subfold_r1 `cm.mult` last_r1)
                  (subfold_r2 `cm.mult` last_r2)
                  (foldm_snoc cm fullseq_r1)
                  (foldm_snoc cm fullseq_r2);
    //eq.transitivity lhs
    //                ((subfold_r1 `cm.mult` last_r1) `cm.mult` (subfold_r2 `cm.mult` last_r2))
    //                ((foldm_snoc cm fullseq_r1) `cm.mult`  (foldm_snoc cm fullseq_r2));
 
    ()
) 



let rec big_sum_exchange #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq) (m0: nat) (mk: nat{mk>=m0}) (n0: nat) (nk: nat{nk>=n0}) (expr: nat -> nat -> c) 
  : Lemma (
      big_sum cm m0 mk (fun (m:nat) -> big_sum cm n0 nk (fun (n:nat) -> expr m n)) `eq.eq` 
      big_sum cm n0 nk (fun (n:nat) -> big_sum cm m0 mk (fun (m:nat) -> expr m n))           
   ) = admit()


//let poly_mul_nth_value #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r) (deg: nat{deg < length p * length q})
//  : Lemma (nth (poly_mul p q) deg == 

let poly_mul_is_commutative #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r) 
  : Lemma (ensures poly_mul p q `noncompact_poly_eq` poly_mul q p) =  
    let cm = poly_add_commutative_monoid r in
    if is_empty p || is_empty q then () else (
      poly_product_monomial_matrix_permutation_lemma p q;
      foldm_snoc_perm cm (poly_product_monomial_matrix p q) 
                         (poly_product_monomial_matrix q p) 
                         (transpose_ji (length p) (length q)) 
    )

let poly_mul_is_associative #c (#r: commutative_ring #c) (p q w: noncompact_poly_over_ring r)
  : Lemma (ensures poly_mul p (poly_mul q w) `ncpoly_eq` poly_mul (poly_mul p q) w) = admit()

let poly_mul_left_distributivity #c (#r: commutative_ring #c) (p q w: noncompact_poly_over_ring r)
  : Lemma (poly_mul p (noncompact_poly_add q w) `ncpoly_eq` noncompact_poly_add (poly_mul p q) (poly_mul p w)) = 
  if is_empty p || is_empty q || is_empty w then admit() else (
  let lhs = poly_product_monomial_matrix p (noncompact_poly_add q w) in
  let cm = poly_add_commutative_monoid r in
  let rhs = noncompact_poly_add
    (Seq.Permutation.foldm_snoc cm (poly_product_monomial_matrix p q))
    (Seq.Permutation.foldm_snoc cm (poly_product_monomial_matrix p w)) in
  Seq.Permutation.
  
  admit();
  ()
  )
  
let poly_mul_right_distributivity #c (#r: commutative_ring #c) (p q w: noncompact_poly_over_ring r)
  : Lemma (poly_mul (noncompact_poly_add p q) w `ncpoly_eq` noncompact_poly_add (poly_mul p w) (poly_mul q w)) = admit()

let poly_mul_commutative_monoid #c (#r: commutative_ring #c) : commutative_monoid #(noncompact_poly_over_ring r) = {
  eq = ncpoly_eq;
  op = poly_mul;
  

}
