module FStar.Seq.BigSum

open FStar.Algebra.CommMonoid.Equiv
open FStar.Algebra.CommMonoid.Fold
open FStar.Seq.Base
open FStar.Seq.Permutation
open FStar.Seq.Properties 
open FStar.IntegerIntervals
open MatrixIndexTransform


/// This module introduces the notion of big_sum over arbitrary commutative monoid
/// without involving sequences (seq), and proves several useful properties of such
/// sums.
///
/// Also we establish the equality of folding over sequences to big_sums of the
/// corresponding range.


#push-options "--ifuel 0 --fuel 1 --z3rlimit 1 --query_stats"

type comm_monoid c eq = Algebra.CommMonoid.Equiv.cm c eq 

open FStar.Mul

/// This lemma, especially when used with forall_intro, helps the prover verify
/// the index ranges of sequences that correspond to arbitrary big_sums
private let bounds_lemma (n0:int) (nk: not_less_than n0) (i: counter_for (ifrom_ito n0 nk))
  : Lemma (n0+i >= n0 /\ n0+i <= nk) = ()

/// Big sum (sigma notation in mathematics) folding of an arbitrary function expr
/// defined over a finite range of integers.
///
/// Notice how one should very strictly control the domains of lambdas,
/// otherwise the proofs easily fail.
let rec big_sum #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq) 
                 (n0: int) (nk: not_less_than n0) (expr: (ifrom_ito n0 nk) -> c) 
                 = FStar.Algebra.CommMonoid.Fold.fold cm n0 nk expr 

/// This lemma establishes the definitional equality of the big_sum given said equality
/// for all the arguments from the allowed range
let rec big_sum_equality #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq) 
                         (n0: int) (nk: int{nk>=n0}) (expr1 expr2: (ifrom_ito n0 nk)->c)
  : Lemma (requires (forall (i: ifrom_ito n0 nk). expr1 i == expr2 i))
          (ensures big_sum cm n0 nk expr1 == big_sum cm n0 nk expr2)
          (decreases nk-n0) = 
  if nk>n0 then big_sum_equality cm n0 (nk-1) expr1 expr2 

/// This lemma decomposes the big_sum into the sum of the first (k-1) elements
/// plus the remaining last one.
/// Obviously requires the argument range that is at least 2 elements long.
let big_sum_snoc #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq) 
                 (n0: int) (nk: int{nk > n0}) (expr: (ifrom_ito n0 nk) -> c) 
                 : Lemma (big_sum cm n0 nk expr == big_sum cm n0 (nk-1) expr `cm.mult` (expr nk)) = ()
 
  
 

/// This function returns a range of integers from 0 to (n-1) with index value available to the prover.
/// This can probably be simplified with just init n (fun x -> x)...
private let get_int_range (n: pos) : (f:seq (t:nat{t<n}){length f = n /\ (forall (k:nat{k<n}). index f k = k) }) = init n (fun x -> x)

/// This function constructs a flattened matrix (seq) given generator function
/// Notice how the domains of both indices are strictly controlled.
let matrix_seq #c (m n: pos) (generator: (under m) -> (under n) -> c)
  : Pure (z:seq c{length z = m `op_Multiply` n}) 
         (requires True)
         (ensures fun x -> ( (forall (i: under m) (j: under n). index x (get_ij m n i j) == generator i j) /\ 
                          (forall (ij: under (m*n)). (index x ij) == ( generator (get_i m n ij) (get_j m n ij))))) =  
  let mn = m * n in
  let generator_ij ij = generator (get_i m n ij) (get_j m n ij) in
  let flat_indices : seq (t:nat{t<mn}) = get_int_range (mn) in 
  map_seq_len generator_ij flat_indices;
  let result = map_seq generator_ij flat_indices in
  let aux (i: under m) (j: under n) 
    : Lemma (index (map_seq generator_ij flat_indices) (get_ij m n i j) == generator i j) 
    = consistency_of_i_j m n i j;
      consistency_of_ij m n (get_ij m n i j);
      assert (generator_ij (get_ij m n i j) == generator i j);
      map_seq_index generator_ij flat_indices (get_ij m n i j) in
  let aux1 (ij: under mn) 
    : Lemma (index (map_seq generator_ij flat_indices) ij == generator_ij ij) 
    = map_seq_index generator_ij flat_indices ij in 
  Classical.forall_intro aux1;
  Classical.forall_intro_2 aux;
  result

/// This auxiliary lemma establishes the decomposition of the matrix into the concatenation
/// of first (m-1) rows and the last row. 
let matrix_snoc #c #eq (cm: comm_monoid c eq) (m n: pos) (generator: (under m) -> (under n) -> c)
  : Lemma (matrix_seq m n generator == append (slice (matrix_seq m n generator) 0 ((m-1)*n))
                                                      (slice (matrix_seq m n generator) ((m-1)*n) (m*n))) 
  = lemma_eq_elim (matrix_seq m n generator) 
                  (append (slice (matrix_seq m n generator) 0 ((m-1)*n))
                          (slice (matrix_seq m n generator) ((m-1)*n) (m*n)))

#push-options "--ifuel 0 --fuel 0 --z3rlimit 4 --query_stats"

/// This auxiliary lemma establishes the equality of the fold of the entire matrix
/// to the sum of folds of (the submatrix of first (m-1) rows) and (the last row).
private let matrix_sum_snoc #c #eq (cm: comm_monoid c eq) (m: not_less_than 2) (n: pos) (generator: (under m) -> (under n) -> c)
  : Lemma (foldm_snoc cm (matrix_seq m n generator) `eq.eq` 
    cm.mult (foldm_snoc cm (matrix_seq (m-1) n generator))
            (foldm_snoc cm (slice (matrix_seq m n generator) ((m-1)*n) (m*n))))
  = 
    lemma_eq_elim (matrix_seq m n generator) (append (matrix_seq (m-1) n generator)
                                                        (slice (matrix_seq m n generator) ((m-1)*n) (m*n)));    
    Seq.Permutation.foldm_snoc_append cm (matrix_seq (m-1) n generator)
                                         (slice (matrix_seq m n generator) ((m-1)*n) (m*n)) 

/// This auxiliary lemma shows that the fold of the last line of a matrix
/// is equal to the corresponding big_sum 
private let matrix_last_line_equals_big_sum #c #eq (cm: comm_monoid c eq) (m n: pos) (generator: (under m) -> (under n) -> c) 
  : Lemma (foldm_snoc cm (slice (matrix_seq m n generator) ((m-1)*n) (m*n)) `eq.eq` 
           big_sum cm 0 (n-1) (generator (m-1))) =  

  assert (equal (slice (matrix_seq m n generator) ((m-1)*n) (m*n))
                (init n (generator (m-1))));
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 (Classical.move_requires_2 cm.commutativity);
  Classical.forall_intro_2 (Classical.move_requires_2 eq.symmetry);
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity); 
  let expr = generator (m-1) in
  fold_equals_seq_foldm cm 0 (n-1) expr;
  lemma_eq_elim (init (interval_size (ifrom_ito 0 (n-1))) (fun i -> expr (0+i))) (init n (generator (m-1)))

/// This lemma establishes that the fold of a matrix is equal to
/// the double big_sum over the matrix generator
let rec matrix_sum_equals_big_sum #c #eq (cm: comm_monoid c eq) (m n: pos) 
                                         (gen_m: not_less_than m) (gen_n: not_less_than n) 
                                         (generator: (under gen_m)->(under gen_n)->c)
  : Lemma (ensures foldm_snoc cm (matrix_seq m n generator) `eq.eq` 
           big_sum cm 0 (m-1) (fun (i: under m) -> big_sum cm 0 (n-1) (generator i)))
          (decreases m)
  = if m=1 then matrix_last_line_equals_big_sum cm m n generator
    else (     
      Classical.forall_intro eq.reflexivity;
      Classical.forall_intro_2 (Classical.move_requires_2 cm.commutativity);
      Classical.forall_intro_2 (Classical.move_requires_2 eq.symmetry);
      Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);  
      matrix_sum_equals_big_sum cm (m-1) n gen_m gen_n generator;       
      let outer_func : ((under m)->c) = fun (i:under m) -> big_sum cm 0 (n-1) (generator i) in
      big_sum_equality cm 0 (m-2) (fun (i: under (m-1)) -> big_sum cm 0 (n-1) (generator i)) outer_func;
      big_sum_snoc cm 0 (m-1) outer_func;  
      matrix_sum_snoc cm m n generator;
      matrix_last_line_equals_big_sum cm m n generator;               
      cm.congruence (foldm_snoc cm (matrix_seq (m-1) n generator))
                    (foldm_snoc cm (slice (matrix_seq m n generator) ((m-1)*n) (m*n)))
                    (big_sum cm 0 (m-2) outer_func)
                    (big_sum cm 0 (n-1) (generator (m-1)));
      ()
    )
#pop-options

/// This function provides the transposed matrix generator, with indices swapped
/// Notice how the forall property of the result function is happily proved automatically by z3 :)
let inv_gen #c (#m:pos) (#n:pos) (generator: (under m)->(under n)->c) 
  : (f:((under n)->(under m)->c){ forall (j: under n)(i: under m). f j i == generator i j }) 
  = fun j i -> generator i j

/// Auxiliary lemmas needed for the double big_sum swapping equality proof
private let matrix_transposed_eq_lemma #c #eq (cm: comm_monoid c eq) (m n: pos) (generator: (under m)->(under n)->c) (ij: under (m*n)) 
  : Lemma (eq.eq (index (matrix_seq m n generator) ij) 
                 (index (matrix_seq n m (inv_gen generator)) (transpose_ji m n ij))) = Classical.forall_intro eq.reflexivity 

private let transpose_inequality_lemma (m n: pos) (ij: under (m*n)) (kl: under (n*m)) 
  : Lemma (requires kl <> ij) (ensures transpose_ji m n ij <> transpose_ji m n kl) = 
  dual_indices m n ij;
  dual_indices m n kl

/// This lemma shows that the transposed matrix is a permutation of the original one
let matrix_permutation_lemma #c #eq (cm: comm_monoid c eq) (m n: pos) (generator: (under m)->(under n)->c)
  : Lemma (is_permutation' eq (matrix_seq m n generator) (matrix_seq n m (inv_gen generator)) (transpose_ji m n)) 
  = 
  Classical.forall_intro (matrix_transposed_eq_lemma cm m n generator); 
  Classical.forall_intro_2 (Classical.move_requires_2 (transpose_inequality_lemma m n));
  reveal_is_permutation' eq (matrix_seq m n generator)
                            (matrix_seq n m (inv_gen generator))
                            (transpose_ji m n) 
                            
/// This lemma allows swapping the two big_sums applied to the same generator
let matrix_big_sum_transpose #c #eq (cm: comm_monoid c eq) (m n: pos) (generator: (under m) -> (under n) -> c)
  : Lemma (big_sum cm 0 (m-1) (fun (i:under m) -> big_sum cm 0 (n-1) (generator i))
          `eq.eq` big_sum cm 0 (n-1) (fun (j: under n) -> big_sum cm 0 (m-1) (inv_gen generator j))) =  
  Classical.forall_intro_2 (Classical.move_requires_2 eq.symmetry);
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity); 
  let matrix_mn = matrix_seq m n generator in
  let matrix_nm = matrix_seq n m (fun j i -> generator i j) in
  matrix_permutation_lemma cm m n generator;
  foldm_snoc_perm cm (matrix_seq m n generator)
                     (matrix_seq n m (inv_gen generator))
                     (transpose_ji m n);
  matrix_sum_equals_big_sum cm m n m n generator;
  matrix_sum_equals_big_sum cm n m n m (inv_gen generator);      
  () 
