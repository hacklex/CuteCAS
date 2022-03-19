module Polynomials.Multiplication

module CE=FStar.Algebra.CommMonoid.Equiv
module CF=FStar.Algebra.CommMonoid.Fold
module CFN=FStar.Algebra.CommMonoid.Fold.Nested

open AlgebraTypes
   
open FStar.Seq
open FStar.Mul
open FStar.Seq.Base
open FStar.Matrix
open FStar.Seq.Properties
open FStar.Seq.Permutation
open FStar.IntegerIntervals

open Polynomials.Definition
open Polynomials.Equivalence
open Polynomials.Compact
open Polynomials.Addition
open Polynomials.Monomial
  
let poly_unit #c (#r: commutative_ring c) : noncompact_poly_over_ring r = empty 
let poly_add_op #c (#r: commutative_ring c) (p q: noncompact_poly_over_ring r) 
  : Tot(noncompact_poly_over_ring r) = noncompact_poly_add p q 
let poly_equiv #c (#r: commutative_ring c) = 
  Algebra.CommMonoid.Equiv.EQ (fun (x y : noncompact_poly_over_ring r) -> ncpoly_eq #c #r x y) 
  ncpoly_eq_is_reflexive_lemma ncpoly_eq_is_symmetric_lemma ncpoly_eq_is_transitive_lemma   
let poly_identity_lemma #c (#r: commutative_ring c) (x:noncompact_poly_over_ring r) 
  : Lemma ((poly_equiv #c #r).eq (poly_add_op #c #r (poly_unit #c #r) x) x) = poly_add_identity #c #r x   
let commutativity #c (#r: commutative_ring c) (x y: noncompact_poly_over_ring r)
  : Lemma ((poly_equiv #c #r).eq (poly_add_op #c #r  x y) (poly_add_op #c #r  y x)) = noncompact_poly_add_is_commutative x y  
let associativity #c (#r: commutative_ring c) (x y z: noncompact_poly_over_ring r)
  : Lemma ((poly_equiv #c #r).eq (poly_add_op #c #r  (poly_add_op #c #r  x y) z) (poly_add_op #c #r  x (poly_add_op #c #r  y z))) 
  = noncompact_poly_add_is_associative x y z;
    symm_lemma ncpoly_eq (x `poly_add_op #c #r` poly_add_op #c #r y z) (poly_add_op #c #r x y `poly_add_op #c #r` z) 
 
private let poly_add_commutative_monoid #c (r: commutative_ring c) 
  = Algebra.CommMonoid.Equiv.CM #(noncompact_poly_over_ring r) 
                                #(poly_equiv) 
                                poly_unit 
                                poly_add_op 
                                poly_identity_lemma 
                                associativity 
                                commutativity 
                                poly_add_congruence_lemma 

let poly_mul_monomial_matrix_gen_aux #c (#r: commutative_ring c) 
                                 (x y: noncompact_poly_over_ring r) 
                                 (i: under (length x)) (j: under (length y))  
  = monomial r ((index x i) `r.multiplication.op` (index y j)) (i+j)

let poly_mul_monomial_matrix_gen #c (#r: commutative_ring c) (x: noncompact_poly_over_ring r{length x > 0})
                                               (y: noncompact_poly_over_ring r{length y > 0})
  : matrix_generator (noncompact_poly_over_ring r) (length x) (length y) = 
  poly_mul_monomial_matrix_gen_aux x y

let poly_mul_gen_transpose_lemma #c (#r: commutative_ring c) 
                                 (x y: noncompact_poly_over_ring r) 
                                 (i: under (length x)) (j: under (length y)) 
  : Lemma (poly_mul_monomial_matrix_gen x y i j `noncompact_poly_eq` poly_mul_monomial_matrix_gen y x j i) 
  = monomial_equality_lemma r ((index x i) `r.multiplication.op` (index y j))
                              ((index y j) `r.multiplication.op` (index x i)) (i+j)

let matrix_seq #c #m #r (generator: matrix_generator c m r) = 
  seq_of_matrix (Matrix.init generator)

let poly_mul #c (#r: commutative_ring c) (x y: noncompact_poly_over_ring r) : noncompact_poly_over_ring r = 
  if (is_empty x) then x
  else if (is_empty y) then y else 
  let mul = r.multiplication.op in
  let cm = poly_add_commutative_monoid r in
  let coef_mx = matrix_seq (poly_mul_monomial_matrix_gen x y) in
  foldm_snoc cm coef_mx
  
  
let rec poly_sum_equality #c (#r: commutative_ring c) 
                          (s1: seq (noncompact_poly_over_ring r)) 
                          (s2: seq (noncompact_poly_over_ring r){length s2=length s1})
  : Lemma (requires (forall (i:under (length s1)). noncompact_poly_eq (index s1 i) (index s2 i)))
          (ensures foldm_snoc (poly_add_commutative_monoid r) s1 `noncompact_poly_eq`
                   foldm_snoc (poly_add_commutative_monoid r) s2) 
          (decreases length s1) = if length s1 > 0 then 
  let cm = (poly_add_commutative_monoid r) in 
  let (liat_1, last_1), (liat_2, last_2) = un_snoc s1, un_snoc s2 in    
  poly_sum_equality liat_1 liat_2;
  poly_add_congruence_lemma last_1 (foldm_snoc cm liat_1)
                            (last_2) (foldm_snoc cm liat_2) 

let rec sum_of_zero_polys #c (#r: commutative_ring c)
                          (s: seq (noncompact_poly_over_ring r))
  : Lemma (requires forall (i:(under (length s))). (index s i) `ncpoly_eq` empty)
          (ensures foldm_snoc (poly_add_commutative_monoid r) s `ncpoly_eq` empty)
          (decreases length s) =
  if length s > 0 then
  let cm, (subseq, last) = poly_add_commutative_monoid r, un_snoc s in
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  sum_of_zero_polys subseq;
  poly_add_congruence_lemma last (foldm_snoc cm subseq) empty empty

let sum_of_zero_polys_from_lemma #c (#r: commutative_ring c)
                                 (s: seq (noncompact_poly_over_ring r))
                                 (lemma: (i:under (length s)) -> Lemma (index s i `ncpoly_eq` empty))
  : Lemma (foldm_snoc (poly_add_commutative_monoid r) s `ncpoly_eq` empty)
  = Classical.forall_intro lemma;
  sum_of_zero_polys s

let poly_mul_transposed_monomial_aux #c (#r: commutative_ring c) 
                                     (x y: noncompact_poly_over_ring r) 
                                     (ji: under ((length y) * (length x)))
  : Lemma (noncompact_poly_eq
          (index (matrix_seq (poly_mul_monomial_matrix_gen y x)) ji)
          (index (matrix_seq (transposed_matrix_gen (poly_mul_monomial_matrix_gen x y))) ji)) = 
  let m, n = length x, length y in
  let i = get_i m n (transpose_ji n m ji) in
  let j = get_j m n (transpose_ji n m ji) in
  let mul = r.multiplication.op in
  let coef_yx = matrix_seq (poly_mul_monomial_matrix_gen y x) in
  let trans_xy = matrix_seq (transposed_matrix_gen (poly_mul_monomial_matrix_gen x y)) in 
  dual_indices n m ji;
  monomial_equality_lemma r (index x i `mul` index y j) (index y j `mul` index x i) (i+j);
  symm_lemma noncompact_poly_eq (index coef_yx ji) (index trans_xy ji)
   
let poly_mul_is_commutative #c (#r: commutative_ring c) 
                            (x y: noncompact_poly_over_ring r) 
  : Lemma (noncompact_poly_eq (poly_mul x y) (poly_mul y x)) =  
  if is_nonempty x && is_nonempty y then 
  let m, n = length x, length y in
  let mul = r.multiplication.op in
  let cm = poly_add_commutative_monoid r in
  let coef_xy = matrix_seq (poly_mul_monomial_matrix_gen x y) in
  let coef_yx = matrix_seq (poly_mul_monomial_matrix_gen y x) in
  let trans_xy = matrix_seq (transposed_matrix_gen (poly_mul_monomial_matrix_gen x y)) in
  let aux (ji: under (n*m)) : Lemma ((index coef_yx ji) `ncpoly_eq` (index trans_xy ji)) = 
    dual_indices n m ji;
    let i = get_i m n (transpose_ji n m ji) in
    let j = get_j m n (transpose_ji n m ji) in
    monomial_equality_lemma r (index x i `mul` index y j) (index y j `mul` index x i) (i+j);
    symm_lemma noncompact_poly_eq (index coef_yx ji) (index trans_xy ji) in
  matrix_fold_equals_fold_of_transpose cm (poly_mul_monomial_matrix_gen x y); 
  Classical.forall_intro aux;
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma  #c #r);
  poly_sum_equality coef_yx trans_xy;
  trans_lemma noncompact_poly_eq (foldm_snoc cm coef_xy) 
                                 (foldm_snoc cm trans_xy) 
                                 (foldm_snoc cm coef_yx)
  
 
let sum_of_monomials_of_same_degree_zeros_lemma #c (r: commutative_ring c) (x y: c) (deg:nat)
  : Lemma (forall (i: nat{i<deg}). nth (noncompact_poly_add (monomial r x deg) (monomial r y deg)) i 
                     `r.eq` r.addition.neutral) = ()
   
let sum_of_monomials_lc #c (r: commutative_ring c)
                           (x y:c) (deg: nat)
  : Lemma (nth (noncompact_poly_add (monomial r x deg) (monomial r y deg)) deg == 
           nth (monomial r (r.addition.op x y) deg) deg) = ()
 
let sum_of_monomials_nth_lemma #c (#r: commutative_ring c) (x y:c) (deg:nat) (i:nat{i<=deg}) 
  : Lemma (nth (noncompact_poly_add (monomial r x deg) (monomial r y deg)) i `r.eq`
           nth (monomial r (r.addition.op x y) deg) i) = 
  sum_of_monomials_of_same_degree_zeros_lemma r x y deg;
  let aux (i: under deg) : Lemma (nth (noncompact_poly_add (monomial r x deg) (monomial r y deg)) i `r.eq`
           nth (monomial r (r.addition.op x y) deg) i) = () in
  let aux2 (i: nat{i=deg}) : Lemma (nth (noncompact_poly_add (monomial r x deg) (monomial r y deg)) i `r.eq`
          nth (monomial r (r.addition.op x y) deg) i) = () in  
  let aux3 (i: nat{i<=deg}) : Lemma (nth (noncompact_poly_add (monomial r x deg) (monomial r y deg)) i `r.eq`
          nth (monomial r (r.addition.op x y) deg) i) =
          if i<deg then aux i else aux2 i in       
  Classical.forall_intro aux3
 
let sum_of_monomials_is_monomial_of_sum #c (#r: commutative_ring c)
                             (x y:c) (deg: nat)
  : Lemma (noncompact_poly_add (monomial r x deg) (monomial r y deg) `ncpoly_eq`
           monomial r (r.addition.op x y) deg) = 
  Classical.forall_intro (sum_of_monomials_nth_lemma #c #r x y deg);    
  monomial_length_is_deg r (r.addition.op x y) deg;
  assert (length (monomial r x deg) = length (monomial r y deg));
  poly_eq_from_nth_eq (noncompact_poly_add (monomial r x deg) (monomial r y deg)) 
                      (monomial r (r.addition.op x y) deg)
  //assert (length (monomial r x deg) == length (monomial r y deg));
  //assert (length (monomial r (r.addition.op x y) deg) = length (monomial r y deg));
  //assert (max (length (monomial r x deg)) (length (monomial r y deg)) == length (monomial r x deg));

let foldm_snoc_of_empty #c #eq (cm: CE.cm c eq) (s: seq c {length s=0})
  : Lemma (foldm_snoc cm s == cm.unit) 
  = assert_norm (foldr_snoc cm.mult s cm.unit == cm.unit)

let foldm_snoc_splitting_lemma #c #eq (cm: CE.cm c eq) 
                               (s1: seq c) 
                               (s2: seq c {length s1==length s2})
                               (s3: seq c {length s1==length s3})                                                     
  : Lemma (requires forall (i: under (length s1)). index s3 i == cm.mult (index s1 i) (index s2 i))
          (ensures eq.eq (foldm_snoc cm s1 `cm.mult` foldm_snoc cm s2)
                         (foldm_snoc cm s3)) =    
    let n = (length s1) in
    let init = FStar.Seq.Base.init in
    if (n=0) then (
      //assert_norm (foldm_snoc cm s1 == cm.unit);
      //assert_norm (foldm_snoc cm s2 == cm.unit);
      //assert_norm (foldm_snoc cm s3 == cm.unit);
      cm.identity cm.unit;
      eq.reflexivity cm.unit 
    )
    else (
    let expr1 = fun (i: in_between 0 (n-1)) -> index s1 i in
    let expr2 = fun (i: in_between 0 (n-1)) -> index s2 i in
    foldm_snoc_split cm 0 (n-1) expr1 expr2;
    let sum_func_init_expr = init_func_from_expr (func_sum cm expr1 expr2) 0 (n-1) in
    let e1_init_expr = init_func_from_expr expr1 0 (n-1) in
    let e2_init_expr = init_func_from_expr expr2 0 (n-1) in    
    assert ((foldm_snoc cm (init n sum_func_init_expr))
            `eq.eq` 
            (foldm_snoc cm (init n e1_init_expr) `cm.mult` foldm_snoc cm (init n e2_init_expr)));
    lemma_eq_elim s1 (init n e1_init_expr);
    lemma_eq_elim s2 (init n e2_init_expr);
    assert (forall (i: in_between 0 (n-1)). sum_func_init_expr i == expr1 i `cm.mult` expr2 i);
    assert (forall (i: in_between 0 (n-1)). sum_func_init_expr i == (index s1 i) `cm.mult` (index s2 i));
    assert (forall (i: in_between 0 (n-1)). (index (init n sum_func_init_expr) i) == index s1 i `cm.mult` index s2 i);
    assert (foldm_snoc cm s1 == foldm_snoc cm (init n e1_init_expr));
    Classical.forall_intro_2 (Classical.move_requires_2 eq.symmetry);
    Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
    assert ((foldm_snoc cm s1 `cm.mult` foldm_snoc cm s2) `eq.eq`
            (foldm_snoc cm (init n e1_init_expr) `cm.mult` foldm_snoc cm (init n e2_init_expr)));
    lemma_eq_elim s3 (init n sum_func_init_expr);
    ()
    )

private type leveled_poly #c (#r: commutative_ring c) (x y: noncompact_poly_over_ring r)
  = (t:noncompact_poly_over_ring r{length t=(max (length x) (length y))})

private let aux_append_lemma #c (#r: commutative_ring c) (p q w: noncompact_poly_over_ring r) 
  : Lemma (requires equal q w) (ensures p $$ q == p $$ w) = 
    lemma_eq_elim (p $$ q) (p $$ w)
    
#push-options "--ifuel 0 --fuel 0 --z3rlimit 5"
#restart-solver
let rec poly_cat_zeros_eq_lemma #c (#r: commutative_ring c) (x: noncompact_poly_over_ring r) (n: nat)
  : Lemma (ensures (x $$ (create n r.addition.neutral)) `ncpoly_eq` x) (decreases n) = 
  poly_eq_is_reflexive_lemma x;   
  let zero = r.addition.neutral in
  if (n=0) then lemma_eq_elim x (x $$ create 0 zero) else
  let subseq : noncompact_poly_over_ring r = create (n-1) zero in
  poly_cat_zeros_eq_lemma x (n-1);
  aux_append_lemma x (subseq $+ zero) (create n zero);
  lemma_eq_elim (x $$ create n zero) (x $$ subseq $+ zero);
  reveal_opaque (`%is_reflexive) (is_reflexive #c);
  poly_eq_poly_cat_nil (x $$ subseq) zero;  
  assert  (ncpoly_eq (x $$ subseq) (x $$ subseq $+ zero));
  trans_lemma ncpoly_eq x (x $$ subseq) (x $$ create n zero)
#pop-options

(* makes a pair of non-compact polys of equal length by adding higher-degree 
   zero coefficients when needed *)
let level_polys #c (#r: commutative_ring c) 
                (x: noncompact_poly_over_ring r) 
                (y: noncompact_poly_over_ring r)  
  : Pure (tuple2 (leveled_poly x y) (leveled_poly x y)) 
    (requires True)
    (ensures fun (p,q) -> (noncompact_poly_eq p x) /\ 
                       (noncompact_poly_eq q y) /\ 
                       (length p = length q)) =     
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r); 
  let zero = r.addition.neutral in
  if (length x=length y) then (x,y) else
  if (length x>length y) then (
    poly_cat_zeros_eq_lemma y (length x - length y);
    (x, y $$ create (length x - length y) zero)   
  ) else (
    poly_cat_zeros_eq_lemma x (length y - length x);
    (x $$ create (length y - length x) zero, y)
  )  
 
let absorber_lemma_eq #a (#eq: equivalence_relation a) (op:op_with_congruence eq) (z: absorber_of op) (x:a)
  : Lemma ((z `op` x) `eq` z /\ 
           (x `op` z) `eq` z /\ 
           z `eq` (z `op` x) /\ 
           z `eq` (x `op` z) /\ 
           is_absorber_of (x `op` z) op /\
           is_absorber_of (z `op` x) op) = 
  absorber_lemma op z x;
  absorber_equal_is_absorber op z (z `op` x);
  absorber_equal_is_absorber op z (x `op` z);
  symm_lemma eq z (z `op` x);
  symm_lemma eq z (x `op` z)  

let poly_mul_congruence_aux #c (#r: commutative_ring c) 
                            (x y z: noncompact_poly_over_ring r)
  : Lemma (requires ncpoly_eq x y /\
                    is_empty x /\ is_nonempty y /\ is_nonempty z)
          (ensures (poly_mul x z `ncpoly_eq` poly_mul y z)) = 
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);    
  let m, n = length y, length z in
  let mul = r.multiplication.op in
  let eq, zero = r.eq, r.addition.neutral in
  let mgen = poly_mul_monomial_matrix_gen y z in
  let mat_yz = matrix_seq (poly_mul_monomial_matrix_gen y z) in
  let aux (ij: under (m*n)) : Lemma (index mat_yz ij `ncpoly_eq` empty) =     
    let (i, j) = (get_i m n ij, get_j m n ij) in
    let (yi, zj) = (index y i, index z j) in
    nth_eq_from_poly_eq y x i; 
    absorber_equal_is_absorber mul zero yi;
    congruence_lemma_3 mul yi zero zj;
    absorber_lemma mul zero zj;    
    trans_lemma eq (mul yi zj) (mul zero zj) zero;
    monomial_equality_lemma r (mul yi zj) zero (i+j);
    monomial_zero_lemma r (mul yi zj) (i+j);
  () in
  Classical.forall_intro aux;
  sum_of_zero_polys mat_yz;
  lemma_eq_elim x empty 

let poly_eq_means_tail_of_zeros #c (#r: commutative_ring c) 
                                (x y: noncompact_poly_over_ring r)
  : Lemma (requires ncpoly_eq x y /\ (length x > length y))
          (ensures (forall (i:int{i>=length y /\ i< length x}). 
                      r.eq (index x i) r.addition.neutral)) = 
  reveal_opaque (`%is_reflexive) (is_reflexive #c); 
  nth_eq_from_poly_eq_forall x y;
  assert (forall (i: int{i>=length y /\ i < length x}). nth x i `r.eq` r.addition.neutral) 

let rec foldm_snoc_equality #c #eq (cm: CE.cm c eq)
                        (s1: seq c) (s2: seq c{length s2=length s1})
  : Lemma (requires (forall (i: under (length s1)). index s1 i `eq.eq` index s2 i))
          (ensures foldm_snoc cm s1 `eq.eq` foldm_snoc cm s2) 
          (decreases length s1) = 
  if length s1=0 then eq.reflexivity cm.unit else 
  let s1_liat, s1_last = un_snoc s1 in 
  let s2_liat, s2_last = un_snoc s2 in 
  foldm_snoc_equality cm s1_liat s2_liat; 
  cm.congruence s1_last (foldm_snoc cm s1_liat) s2_last (foldm_snoc cm s2_liat) 
  

let foldm_snoc_equality_from_lemma #c #eq (cm: CE.cm c eq)
                                   (s1:seq c) (s2: seq c{length s2 = length s1}) 
                                   (proof : (i:under (length s1))
                                          -> Lemma (index s1 i `eq.eq` index s2 i))
  : Lemma (ensures foldm_snoc cm s1 `eq.eq` foldm_snoc cm s2) = 
  FStar.Classical.forall_intro proof;
  foldm_snoc_equality cm s1 s2

let comm_monoid_transitivity_4 #t (eq:CE.equiv t) (a b c d:t) 
  : Lemma (requires eq.eq a b /\ eq.eq b c /\ eq.eq c d)
          (ensures eq.eq a d) 
  = eq.transitivity a b c; eq.transitivity a c d
 
let rec foldm_snoc_cut_tail #c #eq (cm: CE.cm c eq) (s: seq c{length s > 0}) (n: nat{n<length s})
  : Lemma (requires (forall (i:int{i>=n && i<length s}). index s i `eq.eq` cm.unit))
          (ensures foldm_snoc cm s `eq.eq` foldm_snoc cm (slice s 0 n))
          (decreases (length s)-n) = 
  let liat = (slice s 0 ((length s)-1)) in
  let last = FStar.Seq.Properties.last s in
  let subsum = foldm_snoc cm liat in
  let lhs = foldm_snoc cm s in
  let rhs = foldm_snoc cm (slice s 0 n) in
  if n < (length s)-1 then foldm_snoc_cut_tail cm liat n;
  cm.identity subsum;
  eq.reflexivity subsum; 
  cm.congruence last subsum cm.unit subsum;
  comm_monoid_transitivity_4 eq lhs (cm.unit `cm.mult` subsum) subsum rhs     
 
let poly_mul_congruence_equilen_aux #c (#r: commutative_ring c) 
                                 (x y z: noncompact_poly_over_ring r)
  : Lemma (requires ncpoly_eq x y /\ length y > 0 /\ length x = length y /\ length z > 0) 
          (ensures poly_mul x z `ncpoly_eq` poly_mul y z) =
  let cm = poly_add_commutative_monoid r in
  let m_xz = matrix_seq (poly_mul_monomial_matrix_gen x z) in
  let m_yz = matrix_seq (poly_mul_monomial_matrix_gen y z) in
  let m, n = length x, length z in
  let eq = r.eq in 
  let zero = r.addition.neutral in 
  let mul, add = r.multiplication.op, r.addition.op in
  let aux (ij: under (m*n)) : Lemma (index m_xz ij `ncpoly_eq` index m_yz ij) = 
    let i = get_i m n ij in
    let j = get_j m n ij in
    nth_eq_from_poly_eq x y i;  
    congruence_lemma_3 r.multiplication.op (nth x i) (nth y i) (nth z j);
    monomial_equality_lemma r (nth x i `mul` nth z j) (nth y i `mul` nth z j) (i+j) in
  foldm_snoc_equality_from_lemma cm m_xz m_yz aux

#push-options "--ifuel 0 --fuel 0 --z3rlimit 5" 
let poly_mul_congruence_main_aux #c (#r: commutative_ring c) 
                                 (x y z: noncompact_poly_over_ring r)
  : Lemma (requires ncpoly_eq x y /\ length y > 0 /\ length x > length y /\ length z > 0) 
          (ensures poly_mul x z `ncpoly_eq` poly_mul y z) = 
  let eq = r.eq in 
  let add = r.addition.op in
  let mul = r.multiplication.op in
  let zero = r.addition.neutral in 
  let cm = poly_add_commutative_monoid r in
  let m_xz = matrix_seq (poly_mul_monomial_matrix_gen x z) in
  let m_yz = matrix_seq (poly_mul_monomial_matrix_gen y z) in
  let m_big, m_sml, n = length x, length y, length z in
  Math.Lemmas.multiplication_order_lemma m_big m_sml n;
  let aux (ij: under (m_sml*n)) : Lemma (index m_xz ij `ncpoly_eq` index m_yz ij) = 
    let i = get_i m_sml n ij in
    let j = get_j m_sml n ij in
    nth_eq_from_poly_eq x y i; 
    congruence_lemma_3 r.multiplication.op (nth x i) (nth y i) (nth z j);
    monomial_equality_lemma r (nth x i `mul` nth z j) (nth y i `mul` nth z j) (i+j); 
  () in Classical.forall_intro aux;
  let aux_tail (ij: int{ij>=(m_sml*n) && ij<(m_big*n)}) 
    : Lemma (index m_xz ij `ncpoly_eq` empty) = 
    let i = get_i m_big n ij in
    let j = get_j m_big n ij in 
    Math.Lemmas.division_definition_lemma_2 ij n m_sml; 
    nth_eq_from_poly_eq x y i; 
    absorber_equal_is_absorber mul zero (nth x i);
    absorber_lemma mul (nth x i) (nth z j);
    absorber_is_unique mul zero (mul (nth x i) (nth z j));
    monomial_zero_lemma r (mul (nth x i) (nth z j)) (i+j); 
  () in Classical.forall_intro aux_tail;
  foldm_snoc_cut_tail cm m_xz (m_sml*n);
  foldm_snoc_equality cm (slice m_xz 0 (m_sml*n)) m_yz;
  trans_lemma ncpoly_eq (poly_mul x z) (foldm_snoc cm (slice m_xz 0 (m_sml*n))) (poly_mul y z)
#pop-options 

let poly_mul_congruence_lemma_left #c (#r: commutative_ring c) 
                                      (x y z: noncompact_poly_over_ring r)
  : Lemma (requires (noncompact_poly_eq x y) \/ 
                    (noncompact_poly_eq y x) \/ 
                    (x == y))
          (ensures (poly_mul x z `ncpoly_eq` poly_mul y z) /\
                   (poly_mul z x `ncpoly_eq` poly_mul z y)) = 
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  if length z=0 && length x=0 then lemma_eq_elim x z;
  if length z=0 && length y=0 then lemma_eq_elim y z;
  if ((length x=0 && length y=0) || length z=0) then ()
  else if (length x=0) then poly_mul_congruence_aux x y z
  else if (length y=0) then poly_mul_congruence_aux y x z
  else if (length z=0) then ncpoly_eq_is_reflexive_lemma z
  else if length x > length y then poly_mul_congruence_main_aux x y z
  else if length x = length y then poly_mul_congruence_equilen_aux x y z
  else poly_mul_congruence_main_aux y x z;
  poly_mul_is_commutative x z;
  poly_mul_is_commutative y z

let poly_mul_congruence_lemma #c (#r: commutative_ring c) 
                              (x y z w: noncompact_poly_over_ring r)
  : Lemma (requires ((ncpoly_eq x z \/ ncpoly_eq z x \/ (z == x)) /\ 
                     (ncpoly_eq y w \/ ncpoly_eq w y \/ (w == y)))) 
          (ensures ncpoly_eq (poly_mul x y) (poly_mul z w) /\
                   ncpoly_eq (poly_mul y x) (poly_mul w z)) = 
  poly_mul_congruence_lemma_left y w z;   
  poly_mul_congruence_lemma_left x z y;
  poly_mul_is_commutative z y;
  poly_mul_is_commutative w z; 
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r)
  
let poly_mul_congruence_lemma_right #c (#r: commutative_ring c) 
                              (x y z: noncompact_poly_over_ring r)
  : Lemma (requires ncpoly_eq y z \/ ncpoly_eq z y \/ z == y)
          (ensures poly_mul x y `ncpoly_eq` poly_mul x z) = 
  ncpoly_eq_is_reflexive_lemma x;
  poly_mul_congruence_lemma x y x z

#push-options "--fuel 1 --z3rlimit 15"
let poly_mul_left_distributivity #c (#r: commutative_ring c) (x y z: noncompact_poly_over_ring r) 
  : Lemma (poly_mul x (noncompact_poly_add y z) `ncpoly_eq` noncompact_poly_add (poly_mul x y) (poly_mul x z)) = 
  if (length x = 0) then begin 
    lemma_eq_elim x empty; 
    ncpoly_eq_is_reflexive_lemma x;
    poly_add_identity x
  end 
  else if (length y=0 && length z=0) then ncpoly_eq_is_reflexive_lemma (poly_mul x (noncompact_poly_add y z))
  else  
  let init = FStar.Seq.Base.init in
  let lhs = poly_mul x (noncompact_poly_add y z) in
  let rhs = (noncompact_poly_add (poly_mul x y) (poly_mul x z)) in 
  let mul = r.multiplication.op in
  let cm = poly_add_commutative_monoid r in
  let add = r.addition.op in
  let m, n = length x, max (length y) (length z) in 
  let yb, zb = level_polys y z in
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  poly_mul_congruence_lemma x y x yb;
  poly_mul_congruence_lemma x z x zb;
  poly_add_congruence_lemma (poly_mul x y) (poly_mul x z) (poly_mul x yb) (poly_mul x zb);
  let xybm = matrix_seq (poly_mul_monomial_matrix_gen x yb) in
  let xzbm = matrix_seq (poly_mul_monomial_matrix_gen x zb) in
  let lhsm = matrix_seq (poly_mul_monomial_matrix_gen x (noncompact_poly_add y z)) in
  let aux (ij: under (m*n)) : Lemma (index lhsm ij `ncpoly_eq` 
                                    noncompact_poly_add (index xybm ij) (index xzbm ij)) = 
  let i, j = (get_i m n ij, get_j m n ij) in
    let xi, yj, zj, sumj = (nth x i, nth yb j, nth zb j, nth (noncompact_poly_add yb zb) j) in
    poly_add_congruence_lemma y z yb zb;
    nth_eq_from_poly_eq (noncompact_poly_add y z) (noncompact_poly_add yb zb) j;
    left_distributivity_lemma mul add xi yj zj;
    monomial_equality_lemma r (xi `mul` (nth (noncompact_poly_add y z) j)) (xi `mul` sumj) (i+j);
    monomial_equality_lemma r (xi `mul` sumj) ((xi `mul` yj) `add` (xi `mul` zj)) (i+j);
    sum_of_monomials_is_monomial_of_sum #c #r (xi `mul` yj) (xi `mul` zj) (i+j);
  () in
  let sum_m = init (m*n) (fun (ij:under (m*n)) -> noncompact_poly_add (index xybm ij) (index xzbm ij)) in 
  foldm_snoc_equality_from_lemma (poly_add_commutative_monoid r) lhsm sum_m aux;
  foldm_snoc_splitting_lemma (poly_add_commutative_monoid r) xybm xzbm sum_m;
  assert (lhs == foldm_snoc cm lhsm);
  assert (lhs `ncpoly_eq` foldm_snoc cm sum_m);
  assert (foldm_snoc cm sum_m `ncpoly_eq` noncompact_poly_add (foldm_snoc cm xybm) (foldm_snoc cm xzbm));
  assert (rhs `ncpoly_eq` noncompact_poly_add (foldm_snoc cm xybm) (foldm_snoc cm xzbm));
  trans_lemma_4 ncpoly_eq lhs
                          (foldm_snoc cm sum_m)
                          (noncompact_poly_add (foldm_snoc cm xybm) (foldm_snoc cm xzbm))
                          rhs;
  ()
#pop-options

let poly_mul_right_distributivity #c (#r: commutative_ring c) (x y z: noncompact_poly_over_ring r)
  : Lemma (poly_mul (noncompact_poly_add x y) z `noncompact_poly_eq` noncompact_poly_add (poly_mul x z) (poly_mul y z)) = 
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  Classical.forall_intro_2 (poly_mul_is_commutative #c #r); 
  poly_mul_left_distributivity z x y;
  poly_add_congruence_lemma (poly_mul z x) (poly_mul z y) (poly_mul x z) (poly_mul y z)

let rec poly_mul_fold_of_polys_lemma #c (#r: commutative_ring c) (p: noncompact_poly_over_ring r) (s: seq (noncompact_poly_over_ring r))
  : Lemma (ensures ncpoly_eq (poly_mul p (foldm_snoc (poly_add_commutative_monoid r) s))
                             (foldm_snoc (poly_add_commutative_monoid r) (FStar.Seq.Base.init (length s) (fun i -> poly_mul p (index s i))))) 
          (decreases length s) =
  if length s = 0 then () else
  let init = FStar.Seq.Base.init in
  let liat, last = un_snoc s in 
  let cm = poly_add_commutative_monoid r in
  let lhs = poly_mul p (foldm_snoc cm s) in
  let rhseq_fun (n:nat{n<=length s}) (i: under n) = poly_mul p (index s i) in  
  let rhs = foldm_snoc cm (init (length s) (rhseq_fun (length s))) in
  let rhseq = init (length s) (rhseq_fun (length s)) in
  let rh_subseq, rh_last = un_snoc rhseq in 
  lemma_eq_elim (init (length s) (fun (i: under (length s)) -> poly_mul p (index s i)))
                (init (length s) (fun i -> poly_mul p (index s i)));
  poly_mul_fold_of_polys_lemma p liat;
  poly_mul_left_distributivity p last (foldm_snoc cm liat); 
  lemma_eq_elim (init (length liat) (rhseq_fun (length liat)))
                (init (length liat) (fun i -> poly_mul p (index liat i)));
  lemma_eq_elim rh_subseq (init (length liat) (rhseq_fun (length liat)));
  ncpoly_eq_is_reflexive_lemma (poly_mul p last);
  poly_add_congruence_lemma (poly_mul p last) (poly_mul p (foldm_snoc cm liat)) 
                            (poly_mul p last) (foldm_snoc cm rh_subseq);
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r)

let poly_mul_fold_seq_lemma_aux #c (#r: commutative_ring c) (p: noncompact_poly_over_ring r) 
                            (s: seq (noncompact_poly_over_ring r))
                            (result: seq (noncompact_poly_over_ring r){length result=length s})
  : Lemma (requires forall (i: under (length s)). index result i `ncpoly_eq` poly_mul p (index s i))
          (ensures ncpoly_eq (poly_mul p (foldm_snoc (poly_add_commutative_monoid r) s))
                             (foldm_snoc (poly_add_commutative_monoid r) result)) =  
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  let cm = poly_add_commutative_monoid r in
  let func = fun i -> poly_mul p (index s i) in
  let init = FStar.Seq.Base.init in
  poly_mul_fold_of_polys_lemma p s;
  foldm_snoc_equality cm (init (length s) func) result

let poly_mul_fold_seq_lemma #c (#r: commutative_ring c) (p: noncompact_poly_over_ring r) 
                            (s: seq (noncompact_poly_over_ring r))
                            (result: seq (noncompact_poly_over_ring r){length result=length s})
  : Lemma (requires (forall (i: under (length s)). index result i `ncpoly_eq` poly_mul p (index s i)) \/
                    (forall (i: under (length s)). index result i `ncpoly_eq` poly_mul (index s i) p))
          (ensures ncpoly_eq (poly_mul (foldm_snoc (poly_add_commutative_monoid r) s) p)
                             (foldm_snoc (poly_add_commutative_monoid r) result) /\
                   ncpoly_eq (poly_mul p (foldm_snoc (poly_add_commutative_monoid r) s))
                             (foldm_snoc (poly_add_commutative_monoid r) result)) =  
    Classical.move_requires (poly_mul_fold_seq_lemma_aux p s) result;
    Classical.forall_intro_2 (poly_mul_is_commutative #c #r);
    Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r)
  
let nth_as_monomial #c (#r: commutative_ring c) (p: noncompact_poly_over_ring r) (n: nat{n<length p})
  : t:noncompact_poly_over_ring r{t==monomial r (nth p n) n} = monomial r (nth p n) n

let poly_equals_lc_monomial_plus_liat #c (#r: commutative_ring c) (p: noncompact_poly_over_ring r)
  : Lemma (requires length p>0) 
          (ensures p `ncpoly_eq` (liat p `noncompact_poly_add` monomial r (last p) (length p-1))) = 
  let rhs = noncompact_poly_add (liat p) (monomial r (last p) (length p-1)) in
  let aux (i: under (length p)) : Lemma (nth p i `r.eq` nth rhs i) = 
    neutral_lemma r.addition.op r.addition.neutral (nth (liat p) i);
    neutral_lemma r.addition.op r.addition.neutral (last p);
    reveal_opaque (`%is_transitive) (is_transitive #c);
    nth_of_sum p rhs i in Classical.forall_intro aux;
  poly_eq_from_nth_eq p rhs 

private let init_aux_lemma #c (#r:commutative_ring c) (p: noncompact_poly_over_ring r{length p > 0})
  : squash (FStar.Seq.Base.init (length p-1) (nth_as_monomial p) == 
            FStar.Seq.Base.init (length (liat p)) (nth_as_monomial (liat p))) = 
  lemma_eq_elim (FStar.Seq.Base.init (length p-1) (nth_as_monomial p)) 
                (FStar.Seq.Base.init (length (liat p)) (nth_as_monomial (liat p)))
 
#push-options "--fuel 1 --z3rlimit 15 --ifuel 0"
#restart-solver
let rec poly_equals_sum_of_monomials #c (#r: commutative_ring c) (p: noncompact_poly_over_ring r)
  : Lemma (ensures p `ncpoly_eq` foldm_snoc (poly_add_commutative_monoid r) 
                                 (FStar.Seq.Base.init (length p) (nth_as_monomial p)))
          (decreases length p) = 
  if (length p=0) then () else 
  let cm = poly_add_commutative_monoid r in
  let n = length p in
  let mono_gen = nth_as_monomial p in
  let mono_seq = FStar.Seq.Base.init n mono_gen in  
  let recursive_known = (FStar.Seq.Base.init (length (liat p)) (nth_as_monomial (liat p))) in
  let subseq, last_mono = un_snoc mono_seq in 
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  poly_equals_lc_monomial_plus_liat p;
  poly_equals_sum_of_monomials (liat p);
  lemma_eq_elim subseq recursive_known; 
  ncpoly_eq_is_reflexive_lemma last_mono;
  poly_add_congruence_lemma (liat p) last_mono (foldm_snoc cm subseq) last_mono; 
  cm.commutativity (foldm_snoc cm subseq) last_mono 
#pop-options

private let last_ij_lemma (m n: pos) (ij: under (m*n)) 
  : Lemma (requires get_i m n ij == (m-1) /\ get_j m n ij == (n-1)) 
          (ensures ij = ((m*n)-1)) = () 
          
private let ij_is_last_lemma (m n: pos) (ij: under (m*n)) 
  : Lemma (requires ij = ((m*n)-1)) 
          (ensures get_i m n ij = (m-1) /\ get_j m n ij = (n-1)) = () 
          
private let aux_ij_index (m n: nat)  (ij: under ((m+1)*(n+1) - 1)) 
  : Lemma (get_i (m+1) (n+1) ij < m 
         \/ get_j (m+1) (n+1) ij < n) 
  = Classical.move_requires (last_ij_lemma (m+1) (n+1)) ij 

private let length_of_un_snoc #a (s: seq a) 
  : Lemma (requires length s > 0) 
          (ensures length (fst (un_snoc s)) == length s - 1) = ()

#push-options "--ifuel 0 --fuel 1 --z3rlimit 30"
#restart-solver
let monomial_product_is_monomial #c (r: commutative_ring c)
                                (a: c) (m: nat) (b: c) (n: nat)
  : Lemma (poly_mul (monomial r a m) (monomial r b n) `ncpoly_eq` monomial r (r.multiplication.op a b) (m+n)) = 
  let cm = poly_add_commutative_monoid r in
  let p = monomial r a m in
  let q = monomial r b n in
  let mxgen = poly_mul_monomial_matrix_gen p q in
  let mxseq = matrix_seq mxgen in
  let zero = r.addition.neutral in
  let mul = r.multiplication.op in
  let i_of (ij: under ((m+1)*(n+1))) = get_i (m+1) (n+1) ij in
  let j_of (ij: under ((m+1)*(n+1))) = get_j (m+1) (n+1) ij in
  let zero_of_mx (ij: under ((m+1)*(n+1))) 
    : Lemma (requires ij < ((m+1)*(n+1)-1)) 
            (ensures index mxseq ij `ncpoly_eq` empty) = 
        aux_ij_index m n ij; 
        let i = i_of ij in
        let j = j_of ij in 
        Classical.forall_intro_2 (absorber_lemma_eq mul);      
        monomial_zero_lemma r (mul (index p i) (index q j)) (i+j)
    in 
  let test_monomial = monomial r (mul a b) (m+n) in 
  Math.Lemmas.multiplication_order_lemma (m+1) 1 (n+1);
  assert ((m+1)*(n+1) >= 1);
  assert ((m+1)*(n+1)-1 >= 0);
  let last_id : under ((m+1)*(n+1)) = ((m+1)*(n+1) - 1) in
  ij_is_last_lemma (m+1) (n+1) last_id;
  assert (i_of last_id == m);
  assert (index mxseq last_id == test_monomial);
  assert (poly_mul p q == foldm_snoc cm mxseq);
  let liat, last_mono = un_snoc mxseq in 
  lemma_eq_elim liat (slice mxseq 0 last_id);
  length_of_un_snoc mxseq;
  let liat_ij_is_empty (ij: under (length liat)) 
    : Lemma (index liat ij `ncpoly_eq` empty) = zero_of_mx ij 
    in    
  sum_of_zero_polys_from_lemma liat liat_ij_is_empty;  
  ncpoly_eq_is_reflexive_lemma (noncompact_poly_add last_mono (foldm_snoc cm liat));  
  assert_spinoff (foldm_snoc cm liat `ncpoly_eq` empty);  
  assert_spinoff (poly_add_zero_lemma last_mono (foldm_snoc cm liat);
                  last_mono `ncpoly_eq` 
                  noncompact_poly_add last_mono (foldm_snoc cm liat));
  trans_lemma ncpoly_eq (poly_mul p q)
                        (noncompact_poly_add last_mono (foldm_snoc cm liat))
                        last_mono
#pop-options
 
private let matrix_3d_indices_lemma (m n h: pos) (ijk: under (m*n*h)) 
  : Lemma (
  get_i m (n*h) ijk = get_i m n (get_i (m*n) h ijk) /\
  get_j m n (get_i (m*n) h ijk) = get_i n h (get_j m (n*h) ijk) /\
  get_j n h (get_j m (n*h) ijk) = get_j (m*n) h ijk
) = Math.Lemmas.modulo_division_lemma ijk h n;
    Math.Lemmas.division_multiplication_lemma ijk h n 

let monomial_mul_is_associative #c (r: commutative_ring c) 
                                (a: c) (m: nat) (b: c) (n: nat) (d: c) (k: nat)
  : Lemma (poly_mul (monomial r a m) (poly_mul (monomial r b n) (monomial r d k)) `ncpoly_eq`
           poly_mul (poly_mul (monomial r a m) (monomial r b n)) (monomial r d k)) = 
  let lhs = poly_mul (monomial r a m) (poly_mul (monomial r b n) (monomial r d k)) in
  let rhs = poly_mul (poly_mul (monomial r a m) (monomial r b n)) (monomial r d k) in
  let mul = r.multiplication.op in
  monomial_product_is_monomial r b n d k;  
  monomial_product_is_monomial r a m b n;   
  monomial_product_is_monomial r (a `mul` b) (m+n) d k;
  monomial_product_is_monomial r a m (b `mul` d) (n+k);  
  poly_mul_congruence_lemma (poly_mul (monomial r a m) (monomial r b n)) (monomial r d k)
                            (monomial r (a `mul` b) (m+n)) (monomial r d k);
  poly_mul_congruence_lemma (monomial r a m) (poly_mul (monomial r b n) (monomial r d k))
                            (monomial r a m) (monomial r (b `mul` d) (n+k));
  FStar.Math.Lemmas.addition_is_associative m n k;
  assoc_lemma_3 mul a b d;
  monomial_equality_lemma r (a `mul` (b `mul` d)) (a `mul` b `mul` d) (m+n+k);
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  trans_lemma_5 ncpoly_eq lhs (poly_mul (monomial r a m) (monomial r (b `mul` d) (n+k))) 
                              (monomial r (a `mul` (b `mul` d)) (m+n+k))
                              (monomial r ((a `mul` b) `mul` d) (m+n+k)) rhs
 
#push-options "--ifuel 0 --fuel 0 --z3refresh --z3rlimit 20"
let poly_mul_is_associative #c (#r: commutative_ring c) (p q w: noncompact_poly_over_ring r)
  : Lemma (requires length p>0 /\ length q>0 /\ length w > 0)
          (ensures poly_mul p (poly_mul q w) `ncpoly_eq` poly_mul (poly_mul p q) w) = 
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  let cm = poly_add_commutative_monoid r in
  let gen_qw = poly_mul_monomial_matrix_gen q w in
  let mx_qw = matrix_seq gen_qw in  
  let gen_pq = poly_mul_monomial_matrix_gen p q in
  let mx_pq = matrix_seq gen_pq in
  let lhs = poly_mul p (poly_mul q w) in
  let rhs = poly_mul (poly_mul p q) w in
  let mul = r.multiplication.op in
  let m = length p in 
  let n = length q in
  let h = length w in  
  let init = FStar.Seq.Base.init in
  let p_monos = init m (nth_as_monomial p) in

  let qw_p_seq = init m (fun i -> poly_mul (foldm_snoc cm mx_qw) (nth_as_monomial p i)) in   
  let p_qw_seq = init m (fun i -> poly_mul (nth_as_monomial p i) (foldm_snoc cm mx_qw)) in
  let p_qw_seq_eq_qw_p_seq (i: under m) : Lemma (index qw_p_seq i `ncpoly_eq` index p_qw_seq i) = 
    poly_mul_is_commutative (foldm_snoc cm mx_qw) (nth_as_monomial p i) in
  Classical.forall_intro p_qw_seq_eq_qw_p_seq;  
  foldm_snoc_equality cm qw_p_seq p_qw_seq; 

  let w_monos = init h (nth_as_monomial w) in
  let pq_w_seq = init (m*n) (fun ij -> poly_mul (index mx_pq ij) (foldm_snoc cm w_monos)) in
  
  poly_equals_sum_of_monomials w;
  poly_mul_congruence_lemma (foldm_snoc cm mx_pq) w (foldm_snoc cm mx_pq) (foldm_snoc cm w_monos);
  poly_mul_fold_seq_lemma (foldm_snoc cm w_monos) mx_pq pq_w_seq;
   
  // get_i m n ij == ij/n
  // get_j m n ij == ij%n 
  let mx_3d_gen : matrix_generator (noncompact_poly_over_ring r) m (n*h) = 
    fun i jk -> poly_mul (nth_as_monomial p i) (index mx_qw jk) in
  let mx_3d_dgen : matrix_generator (noncompact_poly_over_ring r) (m*n) h =
    fun ij k -> poly_mul (index mx_pq ij) (nth_as_monomial w k) in

  let mx_3d_fold_seq = init m (fun i -> foldm_snoc cm (init (n*h) (mx_3d_gen i))) in
  let mx_3d_fold_dseq = init (m*n) (fun ij -> foldm_snoc cm (init h (mx_3d_dgen ij))) in

  let mx_3d_2 = matrix_seq mx_3d_dgen in
  let mx_3d = matrix_seq mx_3d_gen in
 
  Math.Lemmas.paren_mul_right m n h;
  
  let mx_equals (ijk: under (m*(n*h))) : Lemma (index mx_3d ijk `ncpoly_eq` index mx_3d_2 ijk) = 
    matrix_3d_indices_lemma m n h ijk;
    let i = get_i m (n*h) ijk in
    let j = get_j m n (get_i (m*n) h ijk) in
    let k = get_j (m*n) h ijk in 
    monomial_product_is_monomial r (nth p i) i (nth q j) j;
    monomial_product_is_monomial r (nth q j) j (nth w k) k; 
    poly_mul_congruence_lemma (monomial r (nth p i `mul` nth q j) (i+j)) (monomial r (nth w k) k)
                              (poly_mul (monomial r (nth p i) i) (monomial r (nth q j) j)) (monomial r (nth w k) k);
    poly_mul_congruence_lemma (nth_as_monomial p i) (monomial r (nth q j `mul` nth w k) (j+k))
                              (nth_as_monomial p i) (poly_mul (nth_as_monomial q j) (nth_as_monomial w k)); 
    monomial_mul_is_associative r (nth p i) i (nth q j) j (nth w k) k; 
  () in
  Classical.forall_intro mx_equals;
  foldm_snoc_equality cm mx_3d mx_3d_2;

  matrix_fold_equals_fold_of_seq_folds cm mx_3d_dgen;
  matrix_fold_equals_fold_of_seq_folds cm mx_3d_gen;

  let p_qw_aux (i: under m) : Lemma (index p_qw_seq i `ncpoly_eq` index mx_3d_fold_seq i) = 
    poly_mul_fold_seq_lemma (nth_as_monomial p i) mx_qw (init (n*h) (mx_3d_gen i)); 
  () in  
  let pq_w_aux (ij: under (m*n)) : Lemma (index pq_w_seq ij `ncpoly_eq` index mx_3d_fold_dseq ij) =  
    poly_mul_fold_seq_lemma (index mx_pq ij) w_monos (init h (mx_3d_dgen ij));
  () in
  Classical.forall_intro pq_w_aux;
  Classical.forall_intro p_qw_aux;
  foldm_snoc_equality cm p_qw_seq mx_3d_fold_seq;
  foldm_snoc_equality cm pq_w_seq mx_3d_fold_dseq;
  trans_lemma ncpoly_eq (foldm_snoc cm p_qw_seq) (foldm_snoc cm mx_3d_fold_seq) (foldm_snoc cm mx_3d);
  let index_3d (ijk: under (m*(n*h))) : Lemma (index mx_3d ijk == poly_mul (monomial r (nth p (get_i m (n*h) ijk)) (get_i m (n*h) ijk))
                                                                           (monomial r (mul (nth q (get_i n h (get_j m (n*h) ijk)))
                                                                                            (nth w (get_j n h (get_j m (n*h) ijk))))
                                                                                       (get_i n h (get_j m (n*h) ijk) + get_j n h (get_j m (n*h) ijk))
                                                                           )
                                              ) = () in  
  poly_equals_sum_of_monomials p;
  poly_mul_is_commutative p (foldm_snoc cm mx_qw);  
  poly_mul_congruence_lemma_left p (foldm_snoc cm p_monos) (foldm_snoc cm mx_qw);
  poly_mul_fold_seq_lemma (foldm_snoc cm mx_qw) p_monos qw_p_seq;
  poly_mul_is_commutative (foldm_snoc cm mx_qw) (foldm_snoc cm p_monos) 
(* 
   Previously this was stated explicitly, but it seems that 
   F* solves this automatically just fine:
  
  trans_lemma_4 ncpoly_eq (poly_mul p (poly_mul q w))
                          (poly_mul (foldm_snoc cm mx_qw) (foldm_snoc cm p_monos))
                          (foldm_snoc cm qw_p_seq)
                          (foldm_snoc cm p_qw_seq); 
  trans_lemma_5 ncpoly_eq lhs (foldm_snoc cm p_qw_seq)
                              (foldm_snoc cm mx_3d)
                              (foldm_snoc cm mx_3d_2)
                              (foldm_snoc cm pq_w_seq);                              
  trans_lemma ncpoly_eq lhs (foldm_snoc cm pq_w_seq) rhs
*)

let poly_mul_unit #c (r: commutative_ring c) : (noncompact_poly_over_ring r) = create 1 r.multiplication.neutral

let poly_mul_identity_aux #c (#r: commutative_ring c) (x: noncompact_poly_over_ring r)
  : Lemma (poly_mul x (poly_mul_unit r) `ncpoly_eq` x) = 
  if length x = 0 then ncpoly_eq_is_reflexive_lemma x else 
  let init = FStar.Seq.Base.init in
  let one = poly_mul_unit r in
  let cm = poly_add_commutative_monoid r in
  let m,n = length x, length one in
  let mx = matrix_seq (poly_mul_monomial_matrix_gen x one) in
  poly_equals_sum_of_monomials x; 
  let monos = init (length x) (nth_as_monomial x) in
  Classical.forall_intro (neutral_lemma r.multiplication.op r.multiplication.neutral);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  let aux (i: under m) : Lemma (index monos i `ncpoly_eq` index mx i) = (
    assert (index monos i == monomial r (nth x i) i);
    let j = get_j 1 (length x) i in 
    monomial_equality_lemma r (r.multiplication.op (nth x i) r.multiplication.neutral) (nth x i) i
  ) in foldm_snoc_equality_from_lemma cm monos mx aux;
  poly_mul_congruence_lemma_left x (foldm_snoc cm monos) one; 
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r) 
 
let poly_mul_identity #c (#r: commutative_ring c) (x: noncompact_poly_over_ring r)
  : Lemma (poly_mul (poly_mul_unit r) x `ncpoly_eq` x) = 
  poly_mul_identity_aux x;
  poly_mul_is_commutative x (poly_mul_unit r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r) 

let poly_mul_associativity #c (#r: commutative_ring c) (x y z: noncompact_poly_over_ring r)
  : Lemma (poly_mul (poly_mul x y) z  `ncpoly_eq` poly_mul x (poly_mul y z)) =
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  if length x = 0 then (ncpoly_eq_is_reflexive_lemma x)
  else if length y = 0 then (ncpoly_eq_is_reflexive_lemma y)
  else if length z = 0 then poly_mul_is_commutative (poly_mul x y) z 
  else poly_mul_is_associative x y z
   
let poly_mul_commutative_monoid #c (r: commutative_ring c) 
  = Algebra.CommMonoid.Equiv.CM #(noncompact_poly_over_ring r) 
                                #(poly_equiv) 
                                (poly_mul_unit r)
                                poly_mul 
                                poly_mul_identity  
                                poly_mul_associativity
                                poly_mul_is_commutative 
                                poly_mul_congruence_lemma
  
