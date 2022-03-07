module Polynomials.Multiplication

module CE=FStar.Algebra.CommMonoid.Equiv
module CF=FStar.Algebra.CommMonoid.Fold
module CFN=FStar.Algebra.CommMonoid.Fold.Nested

open AlgebraTypes
   
open FStar.Seq
open FStar.Mul
open FStar.Seq.Base
open FStar.Seq.Matrix
open FStar.Seq.Properties
open FStar.Seq.Permutation
open FStar.IntegerIntervals

open Polynomials.Definition
open Polynomials.Equivalence
open Polynomials.Compact
open Polynomials.Addition
 
let stream_of_zeros #c (#r: commutative_ring #c) (n: pos) 
  : (f:noncompact_poly_over_ring r{noncompact_poly_eq f empty}) = 
  let result = create n r.addition.neutral in
  zero_equals_self r; 
  poly_of_zeros_equals_empty #c #r result;
  result  
 
let monomial #c (r: commutative_ring #c) (a:c) (degree: nat) 
  : Tot(z:noncompact_poly_over_ring r{
                                       is_nonempty z /\ (last z == a) /\ 
                                       noncompact_poly_eq (liat z) empty /\
                                       r.eq (last z) a
                                     }) (decreases degree) = 
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

let monomial_zero_lemma #c (r: commutative_ring #c) (a:c{r.eq a r.addition.neutral}) (degree: nat)
  : Lemma (monomial r a degree `ncpoly_eq` empty) = poly_eq_from_nth_eq (monomial r a degree) empty

let poly_add_nth_lemma #c (#r:commutative_ring #c) (x y: noncompact_poly_over_ring r) (n: nat)
  : Lemma (ensures nth (noncompact_poly_add x y) n `r.eq` (r.addition.op (nth x n) (nth y n))) = () 


let index_for #a (p: seq a) = under (length p)

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
 
private let poly_add_commutative_monoid #c (r: commutative_ring #c) 
  = Algebra.CommMonoid.Equiv.CM #(noncompact_poly_over_ring r) 
                                #(poly_equiv) 
                                poly_unit 
                                poly_add_op 
                                poly_identity_lemma 
                                associativity 
                                commutativity 
                                poly_add_congruence_lemma 

let poly_mul_monomial_matrix_gen #c (#r: commutative_ring #c) 
                                 (x y: noncompact_poly_over_ring r) 
                                 (i: under (length x)) (j: under (length y))  
  = monomial r ((index x i) `r.multiplication.op` (index y j)) (i+j)

let poly_mul_mgen #c (#r: commutative_ring #c) (x: noncompact_poly_over_ring r{length x > 0})
                                               (y: noncompact_poly_over_ring r{length y > 0})
  : matrix_generator (noncompact_poly_over_ring r) (length x) (length y) = 
  poly_mul_monomial_matrix_gen x y

let poly_mul_gen_transpose_lemma #c (#r: commutative_ring #c) 
                                 (x y: noncompact_poly_over_ring r) 
                                 (i: under (length x)) (j: under (length y)) 
  : Lemma (poly_mul_monomial_matrix_gen x y i j `noncompact_poly_eq` poly_mul_monomial_matrix_gen y x j i) 
  = monomials_equality_lemma r ((index x i) `r.multiplication.op` (index y j))
                               ((index y j) `r.multiplication.op` (index x i)) (i+j)
                             
let poly_mul #c (#r: commutative_ring #c) (x y: noncompact_poly_over_ring r) : noncompact_poly_over_ring r = 
  if (is_empty x) then x
  else if (is_empty y) then y else
  (
    let mul = r.multiplication.op in
    let cm = poly_add_commutative_monoid r in
    let coef_mx = matrix_seq (poly_mul_monomial_matrix_gen x y) in
    foldm_snoc cm coef_mx
  ) 
  
let rec poly_sum_equality #c (#r: commutative_ring #c) 
                          (s1: seq (noncompact_poly_over_ring r)) 
                          (s2: seq (noncompact_poly_over_ring r){length s2=length s1})
  : Lemma (requires (forall (i:under (length s1)). noncompact_poly_eq (index s1 i) (index s2 i)))
          (ensures foldm_snoc (poly_add_commutative_monoid r) s1 `noncompact_poly_eq`
                   foldm_snoc (poly_add_commutative_monoid r) s2) 
          (decreases length s1)
  = if length s1 > 0 then ( 
      let cm = (poly_add_commutative_monoid r) in 
      let last = FStar.Seq.Properties.last in
      assert (last s1 `noncompact_poly_eq` last s2);
      assert (foldm_snoc cm s1 == (last s1 `cm.mult` foldm_snoc cm (slice s1 0 ((length s1)-1))));
      poly_sum_equality (slice s1 0 ((length s1)-1)) (slice s2 0 ((length s2)-1));
      poly_add_congruence_lemma (last s1) (foldm_snoc cm (slice s1 0 ((length s1)-1)))
                                (last s2) (foldm_snoc cm (slice s2 0 ((length s2)-1)));       
      ()
    ) 

let rec sum_of_zero_polys #c (#r: commutative_ring #c)
                          (s: seq (noncompact_poly_over_ring r))
  : Lemma (requires forall (i:(under (length s))). (index s i) `ncpoly_eq` empty)
          (ensures foldm_snoc (poly_add_commutative_monoid r) s `ncpoly_eq` empty)
          (decreases length s) =
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  if (length s=0) then ()
  else (
    let cm = poly_add_commutative_monoid r in
    let subseq = (slice s 0 ((length s)-1)) in
    let last = FStar.Seq.Properties.last s in
    sum_of_zero_polys subseq;
    poly_add_congruence_lemma last (foldm_snoc cm subseq) empty empty
  )

private let commutativity_lemma #c (#r: commutative_ring #c) x y
  : Lemma (((x `r.multiplication.op` y) `r.eq` (y `r.multiplication.op` x)) /\
           ((y `r.multiplication.op` x) `r.eq` (x `r.multiplication.op` y))) = 
           reveal_opaque (`%is_commutative) (is_commutative #c)
 
let poly_mul_transposed_monomial_aux #c (#r: commutative_ring #c) 
                                     (x y: noncompact_poly_over_ring r) 
                                     (ji: under ((length y) * (length x)))
  : Lemma (noncompact_poly_eq
          (index (matrix_seq (poly_mul_monomial_matrix_gen y x)) ji)
          (index (matrix_seq (transposed_matrix_gen (poly_mul_monomial_matrix_gen x y))) ji)) = 
  let m = length x in
  let n = length y in
  let i = get_i m n (transpose_ji n m ji) in
  let j = get_j m n (transpose_ji n m ji) in
  let mul = r.multiplication.op in
  let coef_yx = matrix_seq (poly_mul_monomial_matrix_gen y x) in
  let trans_xy = matrix_seq (transposed_matrix_gen (poly_mul_monomial_matrix_gen x y)) in 
  dual_indices n m ji;
  monomials_equality_lemma r (index x i `mul` index y j) (index y j `mul` index x i) (i+j);
  symm_lemma noncompact_poly_eq (index coef_yx ji) (index trans_xy ji)
   
let poly_mul_is_commutative #c (#r: commutative_ring #c) 
                            (x y: noncompact_poly_over_ring r) 
  : Lemma (noncompact_poly_eq (poly_mul x y) (poly_mul y x)) =  
  if is_nonempty x && is_nonempty y then begin
    let m = length x in
    let n = length y in
    let mul = r.multiplication.op in
    let cm = poly_add_commutative_monoid r in
    let coef_xy = matrix_seq (poly_mul_monomial_matrix_gen x y) in
    let coef_yx = matrix_seq (poly_mul_monomial_matrix_gen y x) in
    let trans_xy = matrix_seq (transposed_matrix_gen (poly_mul_monomial_matrix_gen x y)) in
    let aux (ji: under (n*m)) 
      : Lemma ((index (matrix_seq (poly_mul_monomial_matrix_gen y x)) ji) `noncompact_poly_eq`
               (index (matrix_seq (transposed_matrix_gen (poly_mul_monomial_matrix_gen x y))) ji)) = 
      dual_indices n m ji;
      let i = get_i m n (transpose_ji n m ji) in
      let j = get_j m n (transpose_ji n m ji) in
      monomials_equality_lemma r (index x i `mul` index y j) (index y j `mul` index x i) (i+j);
      symm_lemma noncompact_poly_eq (index coef_yx ji) (index trans_xy ji) in
    matrix_fold_equals_fold_of_transpose cm (poly_mul_monomial_matrix_gen x y); 
    Classical.forall_intro aux;
    poly_sum_equality coef_yx trans_xy;
    trans_lemma noncompact_poly_eq (foldm_snoc cm coef_xy) 
                                   (foldm_snoc cm trans_xy) 
                                   (foldm_snoc cm coef_yx)
  end

#push-options "--z3rlimit 11 --fuel 0 --ifuel 0"
let sum_of_monomials_of_same_degree_zeros_lemma #c (r: commutative_ring #c) (x y: c) (deg:nat)
  : Lemma (forall (i: nat{i<deg}). nth (noncompact_poly_add (monomial r x deg) (monomial r y deg)) i `r.eq` r.addition.neutral) = 
  let sum_monomial = monomial r (r.addition.op x y) deg in
  let monomials_sum = (noncompact_poly_add (monomial r x deg) (monomial r y deg)) in
  nth_of_sum (monomial r x deg) (monomial r y deg) deg;
  let zeros (i: under deg) : Lemma (nth monomials_sum i `r.eq` r.addition.neutral) = 
      nth_of_monomial r x deg;
      nth_of_monomial r y deg;
      neutral_lemma r.addition.op r.eq r.addition.neutral r.addition.neutral
  in
  Classical.forall_intro zeros 
#pop-options

let weird_lemma (n: nat) (p: nat->prop) : Lemma (requires (forall (i:under n). p i) /\ (p n)) (ensures (forall (i: under (n+1)). p i)) = ()

#push-options "--z3rlimit 2 --fuel 0 --ifuel 0"
let sum_of_monomials_lc #c (r: commutative_ring #c)
                           (x y:c) (deg: nat)
  : Lemma (nth (noncompact_poly_add (monomial r x deg) (monomial r y deg)) deg `r.eq` 
           nth (monomial r (r.addition.op x y) deg) deg) = 
  let sum_monomial = monomial r (r.addition.op x y) deg in
  let monomials_sum = (noncompact_poly_add (monomial r x deg) (monomial r y deg)) in 
  assert (nth sum_monomial deg == nth monomials_sum deg);   
  assert (nth monomials_sum deg `r.eq` nth sum_monomial deg)
 
let sum_of_monomials_nth_lemma #c (#r: commutative_ring #c) (x y:c) (deg:nat) (i:nat{i<=deg}) 
  : Lemma (nth (noncompact_poly_add (monomial r x deg) (monomial r y deg)) i `r.eq`
           nth (monomial r (r.addition.op x y) deg) i) = 
  assert (i <= deg);
  if (i<deg) then (sum_of_monomials_of_same_degree_zeros_lemma r x y deg)  
  else sum_of_monomials_lc r x y deg 

let sum_of_monomials_is_monomial_of_sum #c (#r: commutative_ring #c)
                             (x y:c) (deg: nat)
  : Lemma (noncompact_poly_add (monomial r x deg) (monomial r y deg) `noncompact_poly_eq`
           monomial r (r.addition.op x y) deg) = 

  Classical.forall_intro (sum_of_monomials_nth_lemma #c #r x y deg);
  Polynomials.Equivalence.poly_eq_from_nth_eq (noncompact_poly_add (monomial r x deg) (monomial r y deg))
                                              (monomial r (r.addition.op x y) deg)

let foldm_snoc_of_empty #c #eq (cm: CE.cm c eq) (s: seq c {length s=0})
  : Lemma (foldm_snoc cm s == cm.unit) = 
  assert_norm (foldr_snoc cm.mult s cm.unit == cm.unit)

let foldm_snoc_splitting_lemma #c #eq (cm: CE.cm c eq) 
                               (s1: seq c) 
                               (s2: seq c {length s1==length s2})
                               (s3: seq c {length s1==length s3})                                                     
  : Lemma (requires forall (i: under (length s1)). index s3 i == cm.mult (index s1 i) (index s2 i))
          (ensures eq.eq (foldm_snoc cm s1 `cm.mult` foldm_snoc cm s2)
                         (foldm_snoc cm s3)) =    
    let n = (length s1) in
    if (n=0) then (
      assert_norm (foldm_snoc cm s1 == cm.unit);
      assert_norm (foldm_snoc cm s2 == cm.unit);
      assert_norm (foldm_snoc cm s3 == cm.unit);
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

private type leveled_poly #c (#r: commutative_ring #c) (x y: noncompact_poly_over_ring r)
  = (t:noncompact_poly_over_ring r{length t=(max (length x) (length y))})

let rec poly_cat_zeros_eq_lemma #c (#r: commutative_ring #c) (x: noncompact_poly_over_ring r) (n: nat)
  : Lemma (ensures (x $$ (create n r.addition.neutral)) `noncompact_poly_eq` x) (decreases n) = 
  if (n=0) then (
    lemma_eq_elim x (x $$ (create 0 r.addition.neutral));
    poly_eq_is_reflexive_lemma x    
  ) 
  else (
    let zero = r.addition.neutral in
    poly_cat_zeros_eq_lemma x (n-1);
    lemma_eq_elim (x $$ (create n zero)) 
                  ((x $$ (create (n-1) zero)) $+ zero);
    reveal_opaque (`%is_reflexive) (is_reflexive #c);
    poly_eq_poly_cat_nil (x $$ (create (n-1) zero)) zero;
    trans_lemma (ncpoly_eq) x (x $$ (create (n-1) zero)) (x $$ (create n zero))
  )

let level_polys #c (#r: commutative_ring #c) 
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

let poly_mul_congruence_aux #c (#r: commutative_ring #c) 
                            (x y z: noncompact_poly_over_ring r)
  : Lemma (requires ncpoly_eq x y /\
                    is_empty x /\ is_nonempty y /\ is_nonempty z)
          (ensures (poly_mul x z `ncpoly_eq` poly_mul y z)) = 
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);    
  let m=length y in
  let n=length z in
  let eq=r.eq in
  let mul=r.multiplication.op in
  let zero=r.addition.neutral in
  let mgen=poly_mul_mgen y z in
  let mat_yz=matrix_seq (poly_mul_mgen y z) in
  let aux (ij: under (m*n)) : Lemma (index mat_yz ij `ncpoly_eq` empty) =     
    nth_eq_from_poly_eq y x (get_i m n ij); 
    let (i, j) = (get_i m n ij, get_j m n ij) in
    let (yi, zj) = (index y (get_i m n ij), index z (get_j m n ij)) in
    absorber_equal_is_absorber mul eq zero yi; 
    absorber_lemma mul eq yi zj;
    absorber_is_unique mul eq zero (mul yi zj);
    monomials_equality_lemma r (mul yi zj) zero (i+j);
    monomial_zero_lemma r (mul yi zj) (i+j);
  () in
  Classical.forall_intro aux;
  sum_of_zero_polys mat_yz;
  lemma_eq_elim x empty;
  ()

let poly_eq_means_tail_of_zeros #c (#r: commutative_ring #c) 
                                (x y: noncompact_poly_over_ring r)
  : Lemma (requires ncpoly_eq x y /\ (length x > length y))
          (ensures (forall (i:int{i>=length y /\ i< length x}). r.eq (index x i) r.addition.neutral))
  = nth_eq_from_poly_eq_forall x y;
    reveal_opaque (`%is_reflexive) (is_reflexive #c); 
    assert (forall (i: int{i>=length y /\ i < length x}). nth x i `r.eq` r.addition.neutral) 


#push-options "--ifuel 1 --fuel 1"
let rec foldm_snoc_equality #c #eq (cm: CE.cm c eq)
                        (s1: seq c) (s2: seq c{length s2=length s1})
  : Lemma (requires (forall (i: under (length s1)). index s1 i `eq.eq` index s2 i))
          (ensures foldm_snoc cm s1 `eq.eq` foldm_snoc cm s2) 
          (decreases length s1) = 
  if length s1=0 then eq.reflexivity cm.unit 
  else (
    let s1_liat, s1_last = un_snoc s1 in 
    let s2_liat, s2_last = un_snoc s2 in 
    foldm_snoc_equality cm s1_liat s2_liat; 
    cm.congruence s1_last (foldm_snoc cm s1_liat) s2_last (foldm_snoc cm s2_liat) 
  )
#pop-options

let comm_monoid_transitivity_4 #t (eq:CE.equiv t) (a b c d:t) 
  : Lemma (requires eq.eq a b /\ eq.eq b c /\ eq.eq c d)
          (ensures eq.eq a d) 
  = eq.transitivity a b c; eq.transitivity a c d

#push-options "--ifuel 0 --fuel 1 --z3rlimit 5"
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
#pop-options  

let poly_mul_congruence_equilen_aux #c (#r: commutative_ring #c) 
                                 (x y z: noncompact_poly_over_ring r)
  : Lemma (requires ncpoly_eq x y /\ length y > 0 /\ length x = length y /\ length z > 0) 
          (ensures poly_mul x z `ncpoly_eq` poly_mul y z) =
  let cm = poly_add_commutative_monoid r in
  let m_xz = matrix_seq (poly_mul_mgen x z) in
  let m_yz = matrix_seq (poly_mul_mgen y z) in
  let m = length x in
  let n = length z in
  let mul = r.multiplication.op in
  let eq = r.eq in 
  let add = r.addition.op in
  let zero = r.addition.neutral in 
  let aux (ij: under (m*n)) : Lemma (index m_xz ij `ncpoly_eq` index m_yz ij) = 
    let i = get_i m n ij in
    let j = get_j m n ij in
    nth_eq_from_poly_eq x y i;  
    equivalence_wrt_operation_lemma #c #mul eq (nth x i) (nth y i) (nth z j);
    monomials_equality_lemma r (nth x i `mul` nth z j) (nth y i `mul` nth z j) (i+j); 
  () in
  Classical.forall_intro aux;
  foldm_snoc_equality cm m_xz m_yz 

#push-options "--ifuel 0 --fuel 1 --z3rlimit 10" 
let poly_mul_congruence_main_aux #c (#r: commutative_ring #c) 
                                 (x y z: noncompact_poly_over_ring r)
  : Lemma (requires ncpoly_eq x y /\ length y > 0 /\ length x > length y /\ length z > 0) 
          (ensures poly_mul x z `ncpoly_eq` poly_mul y z) = 
  let cm = poly_add_commutative_monoid r in
  let m_xz = matrix_seq (poly_mul_mgen x z) in
  let m_yz = matrix_seq (poly_mul_mgen y z) in
  let m_big = length x in
  let m_sml = length y in
  let n = length z in
  let mul = r.multiplication.op in
  let eq = r.eq in 
  let add = r.addition.op in
  let zero = r.addition.neutral in 
  let ind_aux (n: pos) (m1: pos) (m2: pos) (ij1: under(m1*n)) (ij2: under(m2*n))
    : Lemma (requires ij1=ij2) (ensures get_i m1 n ij1 = get_i m2 n ij2) = () in 
  assert (m_big*n > m_sml*n); //can't delete this assertion
  let aux (ij: under (m_sml*n)) : Lemma (index m_xz ij `ncpoly_eq` index m_yz ij) = 
    let i = get_i m_sml n ij in
    let j = get_j m_sml n ij in
    nth_eq_from_poly_eq x y i; 
    equivalence_wrt_operation_lemma #c #mul eq (nth x i) (nth y i) (nth z j);
    monomials_equality_lemma r (nth x i `mul` nth z j) (nth y i `mul` nth z j) (i+j); 
  () in
  let aux_tail (ij: int{ij>=(m_sml*n) && ij<(m_big*n)}) : Lemma (index m_xz ij `ncpoly_eq` empty) = 
    let i = get_i m_big n ij in
    let j = get_j m_big n ij in 
    Math.Lemmas.division_definition_lemma_2 ij n m_sml; 
    nth_eq_from_poly_eq x y i; 
    absorber_equal_is_absorber mul eq zero (nth x i);
    absorber_lemma mul eq (nth x i) (nth z j);
    absorber_is_unique mul eq zero (mul (nth x i) (nth z j));
    monomial_zero_lemma r (mul (nth x i) (nth z j)) (i+j); 
  () in 
  Classical.forall_intro aux;
  Classical.forall_intro aux_tail;
  foldm_snoc_cut_tail cm m_xz (m_sml*n);
  foldm_snoc_equality cm (slice m_xz 0 (m_sml*n)) m_yz;
  trans_lemma ncpoly_eq (poly_mul x z) (foldm_snoc cm (slice m_xz 0 (m_sml*n))) (poly_mul y z)

let poly_mul_congruence_lemma_left #c (#r: commutative_ring #c) 
                              (x y z: noncompact_poly_over_ring r)
  : Lemma (requires noncompact_poly_eq x y)
          (ensures poly_mul x z `noncompact_poly_eq` poly_mul y z) = 
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  if length z=0 && length x=0 then lemma_eq_elim x z;
  if length z=0 && length y=0 then lemma_eq_elim y z;
  if ((length x=0 && length y=0) || length z=0) then ()
  else if (length x=0) then poly_mul_congruence_aux x y z
  else if (length y=0) then poly_mul_congruence_aux y x z
  else if (length z=0) then ncpoly_eq_is_reflexive_lemma z
  else if length x > length y then poly_mul_congruence_main_aux x y z
  else if length x = length y then poly_mul_congruence_equilen_aux x y z
  else poly_mul_congruence_main_aux y x z 

let poly_mul_congruence_lemma #c (#r: commutative_ring #c) (x y z w: noncompact_poly_over_ring r)
  : Lemma (requires ncpoly_eq x z /\ ncpoly_eq y w) (ensures ncpoly_eq (poly_mul x y) (poly_mul z w)) = 
  poly_mul_congruence_lemma_left y w z;  
  poly_mul_congruence_lemma_left x z y;
  poly_mul_is_commutative z y;
  poly_mul_is_commutative w z;
  // all that's left is three transitivity steps.
  // In fact, F* can prove the entire lemma automatically if we just 
  // call forall_intros on the above two lemmas, but we keep the 
  // essential part of the proof as explicit as possible.
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r)

let left_distributivity #c (r:commutative_ring #c) (x y z: c)
  : Lemma (r.multiplication.op x (r.addition.op y z) `r.eq` r.addition.op (r.multiplication.op x y) (r.multiplication.op x z)) = 
  reveal_opaque (`%is_fully_distributive) (is_fully_distributive #c);
  reveal_opaque (`%is_left_distributive) (is_fully_distributive #c)

#push-options "--ifuel 0 --fuel 0 --z3rlimit 5"
let poly_mul_left_distributivity #c (#r: commutative_ring #c) (x y z: noncompact_poly_over_ring r) 
  : Lemma (poly_mul x (noncompact_poly_add y z) `noncompact_poly_eq` noncompact_poly_add (poly_mul x y) (poly_mul x z)) = 
  let lhs = poly_mul x (noncompact_poly_add y z) in
  let rhs = (noncompact_poly_add (poly_mul x y) (poly_mul x z)) in 
  let (mul, add) = r.multiplication.op, r.addition.op in
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  if (length x = 0) then begin 
    lemma_eq_elim x empty; 
    ncpoly_eq_is_reflexive_lemma x;
    poly_add_identity x
  end 
  else if (length y=0 && length z=0) then ncpoly_eq_is_reflexive_lemma lhs 
  else begin
    let (m, n) = (length x, max (length y) (length z)) in 
    let (yb, zb) = level_polys y z in
    poly_mul_congruence_lemma x y x yb;
    poly_mul_congruence_lemma x z x zb;
    poly_add_congruence_lemma (poly_mul x y) (poly_mul x z) (poly_mul x yb) (poly_mul x zb);
    let xybm = matrix_seq (poly_mul_monomial_matrix_gen x yb) in
    let xzbm = matrix_seq (poly_mul_monomial_matrix_gen x zb) in
    let lhsm = matrix_seq (poly_mul_monomial_matrix_gen x (noncompact_poly_add y z)) in
    let aux (ij: under (m*n)) : Lemma (index lhsm ij `ncpoly_eq` noncompact_poly_add (index xybm ij) (index xzbm ij)) = 
      let (i,j) = (get_i m n ij, get_j m n ij) in
      let (xi, yj, zj, sumj) = (nth x i, nth yb j, nth zb j, nth (noncompact_poly_add yb zb) j) in
      poly_add_congruence_lemma y z yb zb;
      nth_eq_from_poly_eq (noncompact_poly_add y z) (noncompact_poly_add yb zb) j;
      left_distributivity r xi yj zj;
      monomials_equality_lemma r (xi `mul` (nth (noncompact_poly_add y z) j)) (xi `mul` sumj) (i+j);
      monomials_equality_lemma r (xi `mul` sumj) ((xi `mul` yj) `add` (xi `mul` zj)) (i+j);
      sum_of_monomials_is_monomial_of_sum #c #r (xi `mul` yj) (xi `mul` zj) (i+j);
    () in Classical.forall_intro aux;
    let sum_m = init (m*n) (fun (ij:under (m*n)) -> noncompact_poly_add (index xybm ij) (index xzbm ij)) in   
    foldm_snoc_equality (poly_add_commutative_monoid r) lhsm sum_m;
    foldm_snoc_splitting_lemma (poly_add_commutative_monoid r) xybm xzbm sum_m    
  end
#pop-options

let poly_mul_right_distributivity #c (#r: commutative_ring #c) (x y z: noncompact_poly_over_ring r)
  : Lemma (poly_mul (noncompact_poly_add x y) z `noncompact_poly_eq` noncompact_poly_add (poly_mul x z) (poly_mul y z)) = 
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  Classical.forall_intro_2 (poly_mul_is_commutative #c #r); 
  poly_mul_left_distributivity z x y;
  poly_add_congruence_lemma (poly_mul z x) (poly_mul z y) (poly_mul x z) (poly_mul y z)

let seq_equality_from_members #c (s1 s2: seq c) : Lemma (requires length s1=length s2 /\ (forall (i: under (length s1)). index s1 i == index s2 i))
                                                        (ensures s1 == s2) = lemma_eq_elim s1 s2
 
#push-options "--ifuel 0 --fuel 1 --z3rlimit 15"
let rec poly_mul_fold_of_polys_lemma #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) (s: seq (noncompact_poly_over_ring r))
  : Lemma (ensures ncpoly_eq (poly_mul p (foldm_snoc (poly_add_commutative_monoid r) s))
                             (foldm_snoc (poly_add_commutative_monoid r) (init (length s) (fun i -> poly_mul p (index s i))))) 
          (decreases length s) =
  if length s = 0 then ()
  else begin
    lemma_eq_elim (init (length s) (fun (i: under (length s)) -> poly_mul p (index s i)))
                  (init (length s) (fun i -> poly_mul p (index s i)));

    let (liat, last) = un_snoc s in
    let cm = poly_add_commutative_monoid r in
    let lhs = poly_mul p (foldm_snoc cm s) in
    let rhseq_fun (n:nat{n<=length s}) (i: under n) = poly_mul p (index s i) in  
    let rhs = foldm_snoc cm (init (length s) (rhseq_fun (length s))) in
    let rhseq = init (length s) (rhseq_fun (length s)) in
    poly_mul_fold_of_polys_lemma p liat;
    poly_mul_left_distributivity p last (foldm_snoc cm liat);    
    assert (lhs `ncpoly_eq` ((poly_mul p last) `noncompact_poly_add`
                            (poly_mul p (foldm_snoc cm liat))));
    assert (forall (i: under (length liat)). index s i == index liat i);
    lemma_eq_elim (init (length liat) (fun (i:under(length liat))-> poly_mul p (index liat i)))
                  (init (length liat) (fun i-> poly_mul p (index s i)));
    lemma_eq_elim (init (length liat) (rhseq_fun (length liat)))
                  (init (length liat) (fun i-> poly_mul p (index liat i)));
    assert (poly_mul p (foldm_snoc cm liat) `ncpoly_eq` foldm_snoc cm (init (length liat) (rhseq_fun (length liat)))); 
    
    assert (poly_mul p (foldm_snoc cm liat) `ncpoly_eq` foldm_snoc cm (init (length liat) (rhseq_fun (length liat)))); 
    lemma_eq_elim (Seq.Properties.snoc (init (length liat) (rhseq_fun (length liat))) (poly_mul p last)) rhseq;
    lemma_eq_elim (init (length liat) (rhseq_fun (length liat)))
                  (init (length liat) (fun (i: under (length liat))-> poly_mul p (index liat i)));
    let (rh_subseq, rh_last) = un_snoc rhseq in 
    assert (poly_mul p (foldm_snoc cm liat) `ncpoly_eq` foldm_snoc cm (init (length liat) (rhseq_fun (length liat))));
    lemma_eq_elim rh_subseq (init (length liat) (rhseq_fun (length liat)));
    assert (poly_mul p (foldm_snoc cm liat) `ncpoly_eq` foldm_snoc cm rh_subseq);
    assert (foldm_snoc cm rhseq == (poly_mul p last `noncompact_poly_add` (foldm_snoc cm rh_subseq)));
    ncpoly_eq_is_reflexive_lemma (poly_mul p last);
    poly_add_congruence_lemma (poly_mul p last) (poly_mul p (foldm_snoc cm liat)) (poly_mul p last) (foldm_snoc cm rh_subseq);
    trans_lemma ncpoly_eq lhs
                          ((poly_mul p last) `noncompact_poly_add` (poly_mul p (foldm_snoc cm liat)))
                          ((poly_mul p last) `noncompact_poly_add` (foldm_snoc cm rh_subseq)); 
    ()
  end

let poly_mul_fold_seq_lemma #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) 
                            (s: seq (noncompact_poly_over_ring r))
                            (result: seq (noncompact_poly_over_ring r){length result=length s})
  : Lemma (requires forall (i: under (length s)). index result i `ncpoly_eq` poly_mul p (index s i))
          (ensures ncpoly_eq (poly_mul p (foldm_snoc (poly_add_commutative_monoid r) s))
                             (foldm_snoc (poly_add_commutative_monoid r) result))  
  = Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
    Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
    Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
    poly_mul_fold_of_polys_lemma p s;
    let cm = poly_add_commutative_monoid r in
    let func = fun i -> poly_mul p (index s i) in
    assert (ncpoly_eq (poly_mul p (foldm_snoc cm s)) (foldm_snoc cm (init (length s) func)));  
    foldm_snoc_equality cm (init (length s) func) result;
    trans_lemma ncpoly_eq (poly_mul p (foldm_snoc cm s))
                          (foldm_snoc cm (init (length s) func))
                          (foldm_snoc cm result) 
#pop-options

let nth_as_monomial #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) (n: nat{n<length p})
  : t:noncompact_poly_over_ring r{t==monomial r (nth p n) n} = monomial r (nth p n) n

let rec poly_equals_lc_monomial_plus_liat #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r{length p > 0})
  : Lemma (ensures p `ncpoly_eq` ((liat p) `noncompact_poly_add` monomial r (last p) (length p-1))) (decreases length p) = 
  if (length p = 1) then () else
  (
    reveal_opaque (`%is_reflexive) (is_reflexive #c);
    reveal_opaque (`%is_symmetric) (is_symmetric #c);
    reveal_opaque (`%is_transitive) (is_transitive #c);
    poly_equals_lc_monomial_plus_liat (liat p);
    nth_of_sum (liat p) (monomial r (last p) (length p - 1)) (length p - 1) ;
    assert (nth (liat p) (length p - 1) == r.addition.neutral);
    neutral_lemma r.addition.op r.eq r.addition.neutral (nth p (length p - 1));
    assert (nth (noncompact_poly_add (liat p) (monomial r (last p) (length p - 1))) (length p - 1) `r.eq` nth p (length p - 1));
    poly_eq_from_nth_eq p (liat p `noncompact_poly_add` monomial r (last p) (length p - 1));
    ()
  )

private let init_aux_lemma #c (#r:commutative_ring #c) (p: noncompact_poly_over_ring r{length p > 0})
  : squash (init (length p-1) (nth_as_monomial p) == init (length (liat p)) (nth_as_monomial (liat p))) = 
  lemma_eq_elim (init (length p-1) (nth_as_monomial p)) (init (length (liat p)) (nth_as_monomial (liat p)))

#push-options "--ifuel 0 --fuel 1 --z3rlimit 25"
let rec poly_equals_sum_of_monomials #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r)
  : Lemma (ensures p `ncpoly_eq` foldm_snoc (poly_add_commutative_monoid r) (init (length p) (nth_as_monomial p)))
          (decreases length p) = 
  let cm = poly_add_commutative_monoid r in
  let mono_gen = nth_as_monomial p in
  let n = length p in
  let mono_seq = init n mono_gen in  
  if (length p=0) then () else ( 
    poly_equals_lc_monomial_plus_liat p;
    poly_equals_sum_of_monomials (liat p);
    let recursive_known = (init (length (liat p)) (nth_as_monomial (liat p))) in
    let subseq = (init (length p - 1) (nth_as_monomial p)) in
    let last_mono = monomial r (last p) (length p - 1) in
    let (subseq, last_mono) = un_snoc mono_seq in
    lemma_eq_elim subseq recursive_known;
    init_aux_lemma p; //yes, we double-prove it. Speeds up the verification dramatically.
    assert (subseq == recursive_known);
    assert (liat p `ncpoly_eq` foldm_snoc cm recursive_known);
    assert (liat p `ncpoly_eq` (foldm_snoc cm subseq));
    ncpoly_eq_is_reflexive_lemma last_mono;
    poly_add_congruence_lemma (liat p) last_mono
                              (foldm_snoc cm subseq) last_mono;                              
    assert (foldm_snoc cm (init (length p) (nth_as_monomial p)) == last_mono `noncompact_poly_add` foldm_snoc cm subseq); 
    trans_lemma ncpoly_eq p (liat p `noncompact_poly_add` last_mono)
                           ((foldm_snoc cm subseq) `noncompact_poly_add` last_mono);
    assert (p `ncpoly_eq` ((foldm_snoc cm subseq) `noncompact_poly_add` last_mono));
    cm.commutativity (foldm_snoc cm subseq) last_mono;
    assert (foldm_snoc cm mono_seq == last_mono `noncompact_poly_add` (foldm_snoc cm subseq));
    trans_lemma ncpoly_eq p ((foldm_snoc cm subseq) `noncompact_poly_add` last_mono)
                            (foldm_snoc cm mono_seq); 
    ()
  )
#pop-options

let last_ij_lemma (m n: pos) (ij: under (m*n)) 
  : Lemma (requires get_i m n ij == (m-1) /\ get_j m n ij == (n-1)) 
          (ensures ij = ((m*n)-1)) = () 
          
let ij_is_last_lemma (m n: pos) (ij: under (m*n)) 
  : Lemma (requires ij = ((m*n)-1)) 
          (ensures get_i m n ij = (m-1) /\ get_j m n ij = (n-1)) = () 
          
let aux_ij_index (m n: nat)  (ij: under ((m+1)*(n+1) - 1)) : Lemma (get_i (m+1) (n+1) ij < (m) \/ get_j (m+1) (n+1) ij < (n)) 
  = Classical.move_requires (last_ij_lemma (m+1) (n+1)) ij

let absorber_lemma_eq #a (op:binary_op a) (eq: equivalence_wrt op) (z: absorber_of op eq) (x:a)
  : Lemma ((z `op` x) `eq` z /\ (x `op` z) `eq` z /\ z `eq` (z `op` x) /\ z `eq` (x `op` z)) = 
  absorber_lemma op eq z x;
  absorber_equal_is_absorber op eq z (z `op` x);
  absorber_equal_is_absorber op eq z (x `op` z);
  symm_lemma eq z (z `op` x);
  symm_lemma eq z (x `op` z) 

let length_of_un_snoc #a (s: seq a) : Lemma (requires length s > 0)
  (ensures length (fst (un_snoc s)) == length s - 1) = ()

#push-options "--ifuel 0 --fuel 1 --z3rlimit 30"
let monomial_product_is_monomial #c (r: commutative_ring #c)
                                (a: c) (m: nat) (b: c) (n: nat)
  : Lemma (poly_mul (monomial r a m) (monomial r b n) `ncpoly_eq` monomial r (r.multiplication.op a b) (m+n)) = 
  let cm = poly_add_commutative_monoid r in
  let p = monomial r a m in
  let q = monomial r b n in
  let mxgen = poly_mul_mgen p q in
  let mxseq = matrix_seq mxgen in
  let zero = r.addition.neutral in
  let mul = r.multiplication.op in
  let i_of (ij: under ((m+1)*(n+1))) = get_i (m+1) (n+1) ij in
  let j_of (ij: under ((m+1)*(n+1))) = get_j (m+1) (n+1) ij in
  let zero_of_p (i: under m) : Lemma (index p i == r.addition.neutral) = () in
  let zero_of_q (j: under n) : Lemma (index q j == r.addition.neutral) = () in
  let zero_of_mx (ij: under ((m+1)*(n+1))) : Lemma (requires ij < ((m+1)*(n+1)-1)) (ensures index mxseq ij `ncpoly_eq` empty) = 
    aux_ij_index m n ij;
    let i = i_of ij in
    let j = j_of ij in
    if (i < m) then (zero_of_p i; absorber_lemma_eq mul r.eq (index p i) (index q j); monomial_zero_lemma r (mul (index p i) (index q j)) (i+j))
    else (zero_of_q j; absorber_lemma_eq mul r.eq (index q j) (index p i); monomial_zero_lemma r (mul (index p i) (index q j)) (i+j)) in
  let test_monomial = monomial r (mul a b) (m+n) in
//  assert ((m+1)*(n+1)-1 < (m+1)*(n+1));
//  assert ((m+1) >= 1);
//  assert ((n+1) >= 1);
  Math.Lemmas.multiplication_order_lemma (m+1) 1 (n+1);
  assert ((m+1)*(n+1) >= 1);
  assert ((m+1)*(n+1)-1 >= 0);
  let last_id : under ((m+1)*(n+1)) = ((m+1)*(n+1) - 1) in
  ij_is_last_lemma (m+1) (n+1) last_id;
  assert (i_of last_id == m);
  assert (index mxseq last_id == test_monomial);
  assert (poly_mul p q == foldm_snoc cm mxseq);
  let liat, last_mono = un_snoc mxseq in
//  assert (last_mono == test_monomial);
//  assert (foldm_snoc cm mxseq == noncompact_poly_add last_mono (foldm_snoc cm liat));
//  assert (noncompact_poly_add last_mono (foldm_snoc cm liat) == noncompact_poly_add test_monomial (foldm_snoc cm liat));
  lemma_eq_elim liat (slice mxseq 0 last_id);
  length_of_un_snoc mxseq;
  let wtf (ij: under (length liat)) : Lemma (index liat ij `ncpoly_eq` empty) = zero_of_mx ij in
  Classical.forall_intro wtf;
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  sum_of_zero_polys liat;
  assert (poly_mul p q == noncompact_poly_add last_mono (foldm_snoc cm liat));
  poly_add_zero_lemma last_mono (foldm_snoc cm liat);
  trans_lemma ncpoly_eq (poly_mul p q)
                        (noncompact_poly_add last_mono (foldm_snoc cm liat))
                        last_mono;
()
#pop-options

let monomial_mul_is_associative #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r)
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
  ncpoly_eq_is_reflexive_lemma (monomial r a m);
  ncpoly_eq_is_reflexive_lemma (monomial r d k);
  poly_mul_congruence_lemma (poly_mul (monomial r a m) (monomial r b n)) (monomial r d k)
                            (monomial r (a `mul` b) (m+n)) (monomial r d k);
  poly_mul_congruence_lemma (monomial r a m) (poly_mul (monomial r b n) (monomial r d k))
                            (monomial r a m) (monomial r (b `mul` d) (n+k));
  FStar.Math.Lemmas.addition_is_associative m n k;
  assoc_lemma3 r.eq mul a b d;
  monomials_equality_lemma r (a `mul` (b `mul` d)) (a `mul` b `mul` d) (m+n+k);
  trans_lemma ncpoly_eq rhs (poly_mul (monomial r (a `mul` b) (m+n)) (monomial r d k)) (monomial r ((a `mul` b) `mul` d) (m+n+k));
  trans_lemma_5 ncpoly_eq lhs (poly_mul (monomial r a m) (monomial r (b `mul` d) (n+k))) 
                              (monomial r (a `mul` (b `mul` d)) (m+n+k))
                              (monomial r ((a `mul` b) `mul` d) (m+n+k)) rhs

let mgen #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r{length p > 0})
                                      (q: noncompact_poly_over_ring r{length q > 0})
  : matrix_generator (noncompact_poly_over_ring r) (length p) (length q) = poly_mul_mgen p q

#push-options "--ifuel 0 --fuel 0 --z3rlimit 20"
let poly_mul_is_associative #c (#r: commutative_ring #c) (p q w: noncompact_poly_over_ring r)
  : Lemma (requires length p>0 /\ length q>0 /\ length w > 0)
          (ensures poly_mul p (poly_mul q w) `ncpoly_eq` poly_mul (poly_mul p q) w) = 
  Classical.forall_intro (ncpoly_eq_is_reflexive_lemma #c #r);
  Classical.forall_intro_2 (ncpoly_eq_is_symmetric_lemma #c #r);
  Classical.forall_intro_3 (ncpoly_eq_is_transitive_lemma #c #r);
  let cm = poly_add_commutative_monoid r in
  let gen_qw = poly_mul_mgen q w in
  let mx_qw = matrix_seq gen_qw in  
  let m = length p in 
  let n = length q in
  let k = length w in 
  assert (poly_mul q w == foldm_snoc cm mx_qw);
  poly_equals_sum_of_monomials p;
  let p_monos = init m (nth_as_monomial p) in
  let p_qw_seq = init m (fun i -> poly_mul (foldm_snoc cm mx_qw) (nth_as_monomial p i)) in
  poly_mul_is_commutative (foldm_snoc cm p_monos) (foldm_snoc cm mx_qw);
  poly_mul_fold_seq_lemma (foldm_snoc cm mx_qw) p_monos p_qw_seq;
  poly_mul_is_commutative (foldm_snoc cm mx_qw) (foldm_snoc cm p_monos);
  trans_lemma ncpoly_eq (poly_mul p (poly_mul q w))
                        ((foldm_snoc cm mx_qw) `poly_mul` (foldm_snoc cm p_monos))
                        ((foldm_snoc cm p_monos) `poly_mul` (foldm_snoc cm mx_qw));
  let aux (i: under m) : Lemma (index p_qw_seq i `ncpoly_eq` 
    foldm_snoc cm (init (length mx_qw) (fun jk -> poly_mul (nth_as_monomial p i) (index mx_qw jk)))) = 
      //poly_mul_fold_seq_lemma (nth_as_monomial p i) 
      assert (index p_qw_seq i == foldm_snoc cm mx_qw `poly_mul` nth_as_monomial p i);
      let res = init (n*k) (fun jk -> poly_mul (nth_as_monomial p i) (index mx_qw jk)) in 
      poly_mul_fold_seq_lemma (nth_as_monomial p i) mx_qw res;
      admit();
    () in
  admit();
(*  matrix_fold_equals_fold_of_seq_folds cm gen_qw;
  let seq_qw = (init n (fun j -> foldm_snoc cm (init k (gen_qw j)))) in
  assert (foldm_snoc cm mx_qw `ncpoly_eq` 
          foldm_snoc cm seq_qw);
  poly_mul_congruence_lemma p (poly_mul q w) p (foldm_snoc cm seq_qw); 
  assert (poly_mul p (poly_mul q w) `ncpoly_eq` poly_mul p (foldm_snoc cm seq_qw));
  let qw_fold : noncompact_poly_over_ring r = foldm_snoc cm seq_qw in
  if(length qw_fold = 0) then admit() else 
  begin
    assert (length qw_fold > 0);
    let p_qw_gen = mgen p qw_fold in
    poly_mul_fold_of_polys_lemma p seq_qw;
    assert (length seq_qw == n);
    lemma_eq_elim (init (length seq_qw) (fun j -> poly_mul p (index seq_qw j)       ))
                  (init (length seq_qw) (fun j -> poly_mul p (foldm_snoc cm (init k (gen_qw j)))       ));
    
    assert (ncpoly_eq (poly_mul p (foldm_snoc cm seq_qw))
           (foldm_snoc cm (init (length seq_qw) (fun j -> poly_mul p (index seq_qw j)       ))));
    admit();  
    ()
  end; *)
  //assert (lhs `ncpoly_eq` rhs);
()

 
