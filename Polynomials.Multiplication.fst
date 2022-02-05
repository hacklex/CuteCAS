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
    else Seq.Properties.cons (noncompact_poly_add (Seq.Properties.head p) (Seq.Properties.head q)) (poly_sum_batch (Seq.Properties.tail p) (Seq.Properties.tail q))
          

let fold_of_sum #c (#r: commutative_ring #c) (p: seq (noncompact_poly_over_ring r)) (q: (seq (noncompact_poly_over_ring r)){length q = length p})
  : Lemma (FStar.Seq.Permutation.foldm_snoc (poly_add_commutative_monoid r) (poly_sum_batch p q) 
          `noncompact_poly_eq` 
          noncompact_poly_add (Seq.Permutation.foldm_snoc (poly_add_commutative_monoid r) p)
                              (Seq.Permutation.foldm_snoc (poly_add_commutative_monoid r) q)) = admit()


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
  : Lemma (poly_mul p (noncompact_poly_add q w) `ncpoly_eq` noncompact_poly_add (poly_mul p q) (poly_mul p w)) = admit()
  
let poly_mul_right_distributivity #c (#r: commutative_ring #c) (p q w: noncompact_poly_over_ring r)
  : Lemma (poly_mul (noncompact_poly_add p q) w `ncpoly_eq` noncompact_poly_add (poly_mul p w) (poly_mul q w)) = admit()

let poly_mul_commutative_monoid #c (#r: commutative_ring #c) : commutative_monoid #(noncompact_poly_over_ring r) = {
  eq = ncpoly_eq;
  op = poly_mul;
  

}
