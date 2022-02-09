module FStar.Seq.BigSum

open FStar.Algebra.CommMonoid.Equiv
open FStar.Seq.Base
open FStar.Seq.Permutation
open FStar.Seq.Properties
open FStar.Seq.Extras

open MatrixIndexTransform


/// This module introduces the notion of big_sum over arbitrary commutative monoid
/// without involving sequences (seq), and proves several useful properties of such
/// sums.
///
/// Also we establish the equality of folding over sequences to big_sums of the
/// corresponding range.


#push-options "--ifuel 0 --fuel 1 --z3rlimit 1 --query_stats"

type comm_monoid c eq = Algebra.CommMonoid.Equiv.cm c eq 

let ( *) = op_Multiply 

/// These are way better readable than the inline formulas 
unfold type not_less_than (x: int) = (t: int{t>=x})
unfold type inbetween (x: int) (y: not_less_than x) = (t: int{t>=x && t<=y})
unfold type counter_of_range (x: int) (y: not_less_than x) = (t: nat{t<(y+1-x)})
unfold let range_count (x: int) (y: not_less_than x) : pos = (y+1)-x

/// This lemma, especially when used with forall_intro, helps the prover verify
/// the index ranges of sequences that correspond to arbitrary big_sums
private let bounds_lemma (n0:int) (nk: not_less_than n0) (i: counter_of_range n0 nk) 
  : Lemma (n0+i >= n0 /\ n0+i <= nk) = ()

/// Big sum (sigma notation in mathematics) folding of an arbitrary function expr
/// defined over a finite range of integers.
///
/// Notice how one should very strictly control the domains of lambdas,
/// otherwise the proofs easily fail.
let rec big_sum #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq) 
                 (n0: int) (nk: not_less_than n0) (expr: (inbetween n0 nk) -> c) 
                 : Pure c 
                   (requires True)  
                   (ensures (fun (x:c) -> ((nk = n0) ==> (x == expr nk)))) 
                   (decreases nk-n0) = 
  if nk = n0 then expr nk
  else (big_sum cm n0 (nk-1) expr) `cm.mult` expr nk

/// This lemma establishes the definitional equality of the big_sum given said equality
/// for all the arguments from the allowed range
let rec big_sum_equality #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq) 
                         (n0: int) (nk: int{nk>=n0}) (expr1 expr2: (inbetween n0 nk)->c)
  : Lemma (requires (forall (i: inbetween n0 nk). expr1 i == expr2 i))
          (ensures big_sum cm n0 nk expr1 == big_sum cm n0 nk expr2)
          (decreases nk-n0) = 
  if nk>n0 then big_sum_equality cm n0 (nk-1) expr1 expr2 

/// This lemma decomposes the big_sum into the sum of the first (k-1) elements
/// plus the remaining last one.
/// Obviously requires the argument range that is at least 2 elements long.
let big_sum_snoc #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq) 
                 (n0: int) (nk: int{nk > n0}) (expr: (inbetween n0 nk) -> c) 
                 : Lemma (big_sum cm n0 nk expr == big_sum cm n0 (nk-1) expr `cm.mult` (expr nk)) = ()

/// This lemma establishes the equality of big_sum to its foldm_snoc counterpart.
/// The equality is considered with respect to the commutative monoid used for folding.
#push-options "--ifuel 0 --fuel 1 --z3rlimit 2 --z3refresh --query_stats"
let rec big_sum_equals_foldm #c #eq 
                             (cm: Algebra.CommMonoid.Equiv.cm c eq) 
                             (n0: int) 
                             (nk: not_less_than n0) 
                             (expr: (inbetween n0 nk) -> c)
  : Lemma (ensures big_sum cm n0 nk expr `eq.eq` 
                   foldm_snoc cm (init (range_count n0 nk) (fun (i: counter_of_range n0 nk) -> expr (n0+i))))
          (decreases nk-n0) = 
  if (nk=n0) then (
   let ts = init (range_count n0 nk) (fun (i: counter_of_range n0 nk) -> expr (n0+i)) in
   lemma_eq_elim (create 1 (expr nk)) ts; 
   Seq.Permutation.foldm_snoc_singleton cm (expr nk);   
   eq.symmetry (foldm_snoc cm ts) (expr nk);
   eq.reflexivity (expr nk); 
   eq.transitivity (big_sum cm n0 nk expr) (expr nk) (foldm_snoc cm ts)
  )
  else (
    let lhs = big_sum cm n0 nk expr in
    let rhs = foldm_snoc cm (init (range_count n0 nk) (fun (i: counter_of_range n0 nk) -> expr (n0+i))) in
    let fullseq = init (range_count n0 nk) (fun (i: counter_of_range n0 nk) -> expr (n0+i)) in    
    let subseq = init (range_count n0 (nk-1)) (fun (i: counter_of_range n0 (nk-1)) -> expr (n0+i)) in
    let subsum = big_sum cm n0 (nk-1) expr in
    let fullfold = foldm_snoc cm fullseq in
    let subfold = foldm_snoc cm subseq in
    let last = expr nk in
    let op = cm.mult in
    big_sum_equals_foldm cm n0 (nk-1) expr;    
    lemma_eq_elim (init (range_count n0 (nk-1)) (fun (i: counter_of_range n0 (nk-1)) -> expr (n0+i))) subseq;
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
    eq.transitivity lhs (subfold `op` last) rhs
  )
#pop-options

/// This is the auxiliary lemma for the fold_decomposition lemma below, handling the
/// induction base case. It is extracted to a separate lemma to minimimze resource usage.
private let fold_decomposition_aux #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq)
                           (n0: int) 
                           (nk: int{nk=n0}) 
                           (expr1 expr2: (inbetween n0 nk) -> c)
  : Lemma (foldm_snoc cm (init (range_count n0 nk) (fun (i:counter_of_range n0 nk) -> expr1 (n0+i) `cm.mult` expr2 (n0+i))) `eq.eq`
           cm.mult (foldm_snoc cm (init (nk+1-n0) (fun (i:counter_of_range n0 nk) -> expr1 (n0+i)))) 
                   (foldm_snoc cm (init (nk+1-n0) (fun (i:counter_of_range n0 nk) -> expr2 (n0+i))))) =   
    Classical.forall_intro_2 (Classical.move_requires_2 eq.symmetry); 
    Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity); 
    let sum_of_funcs (i: counter_of_range n0 nk) = expr1 (n0+i) `cm.mult` expr2 (n0+i) in
    lemma_eq_elim (init (range_count n0 nk) sum_of_funcs) (create 1 (expr1 n0 `cm.mult` expr2 n0));
    foldm_snoc_singleton cm (expr1 n0 `cm.mult` expr2 n0);
    let ts = (init (range_count n0 nk) sum_of_funcs) in
    let ts1 = (init (nk+1-n0) (fun i -> expr1 (n0+i))) in
    let ts2 = (init (nk+1-n0) (fun i -> expr2 (n0+i))) in 
    assert (foldm_snoc cm ts `eq.eq`  ((fun i -> bounds_lemma n0 nk i; 
                                              expr1 (n0+i) `cm.mult` expr2 (n0+i)) 
                                      (nk-n0))); // lemma will fail without this assert.
    Seq.Permutation.foldm_snoc_singleton cm (expr1 nk);  
    Seq.Permutation.foldm_snoc_singleton cm (expr2 nk); 
    cm.congruence (foldm_snoc cm ts1) (foldm_snoc cm ts2) (expr1 nk) (expr2 nk)

/// This is the initial version of the auxiliary lemma, with all assertions left intact.
/// It is no longer needed, but in case one wants to understand why and how exactly does
/// the final lemma version work, this version might provide some insight.
private let fold_decomposition_aux_backup #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq)
                           (n0: int) 
                           (nk: int{nk=n0}) 
                           (expr1 expr2: (inbetween n0 nk) -> c)
  : Lemma (foldm_snoc cm (init (range_count n0 nk) (fun (i:counter_of_range n0 nk) -> expr1 (n0+i) `cm.mult` expr2 (n0+i))) `eq.eq`
           cm.mult (foldm_snoc cm (init (nk+1-n0) (fun (i:counter_of_range n0 nk) -> expr1 (n0+i)))) 
                   (foldm_snoc cm (init (nk+1-n0) (fun (i:counter_of_range n0 nk) -> expr2 (n0+i))))) = 
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

/// This is another auxiliary basic algebra manipulations lemma.
/// I removed the assertions and comments since there is nothing really
/// interesting going on.
private let aux_shuffle_lemma #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq) (s1 s2 l1 l2: c)
  : Lemma (((s1 `cm.mult` s2) `cm.mult` (l1 `cm.mult` l2)) `eq.eq`  
           ((s1 `cm.mult` l1) `cm.mult` (s2 `cm.mult` l2))) =  
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 (Classical.move_requires_2 cm.commutativity);
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity); 
  Classical.forall_intro_3 (Classical.move_requires_3 cm.associativity); 
  let (+) = cm.mult in 
  cm.congruence (s1+s2) l1 (s2+s1) l1;
  cm.congruence ((s1+s2)+l1) l2 ((s2+s1)+l1) l2; 
  cm.congruence ((s2+s1)+l1) l2 (s2+(s1+l1)) l2;
  cm.congruence (s2+(s1+l1)) l2 ((s1+l1)+s2) l2 

/// This constructs a sequence initialization function from an expression used with big_sum,
/// i.e. offsets the argument by n0 and handles the function domain 
unfold let init_func_from_expr #c (#n0: int) (#nk: not_less_than n0) (expr: (inbetween n0 nk) -> c) (a: inbetween n0 nk) (b: inbetween a nk) : ((counter_of_range a b) -> c)
  = fun (i: counter_of_range a b) -> expr (n0+i)

/// This constructs a pointwise sum function from two functions sharing the same domain,
/// with respect to given commutative monoid.
unfold let func_sum #a #c #eq (cm: comm_monoid c eq) (f g: a->c) : (t:(a->c){ forall (x:a). t x == f x `cm.mult` g x}) 
  = fun (x:a) -> cm.mult (f x) (g x)

/// This lemma proves the equality of big_sum of sums to sum of big_sums,
/// i.e. big_sum [i] (f(i)+g(i)) `eq.eq` big_sum[i]f(i) + big_sum[i]g(i).
///
/// The proof gets very verbose, and it takes quite some control over function domains
/// in order for prover to be happy about it. I'll be happy to replace this
/// proof with a more efficient and/or shorter one :)
#push-options "--ifuel 0 --fuel 1 --z3rlimit 10 --z3refresh --query_stats"
let rec fold_decomposition #c #eq (cm: Algebra.CommMonoid.Equiv.cm c eq)
                           (n0: int) 
                           (nk: not_less_than n0) 
                           (expr1 expr2: (inbetween n0 nk) -> c)
  : Lemma (ensures foldm_snoc cm (init (nk+1-n0) (init_func_from_expr (func_sum cm expr1 expr2) n0 nk)) `eq.eq`
           cm.mult (foldm_snoc cm (init (nk+1-n0) (init_func_from_expr expr1 n0 nk))) 
                   (foldm_snoc cm (init (nk+1-n0) (init_func_from_expr expr2 n0 nk)))) (decreases nk-n0) = 
  if (nk=n0) then fold_decomposition_aux cm n0 nk expr1 expr2  else (  
    Classical.forall_intro (bounds_lemma n0 nk); 
    Classical.forall_intro_2 (Classical.move_requires_2 cm.commutativity);
    Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity); 
    let lfunc_up_to (nf: inbetween n0 nk) = init_func_from_expr (func_sum cm expr1 expr2) n0 nf in
    let full_count = range_count n0 nk in
    let sub_count = range_count n0 (nk-1) in 
    let fullseq = init full_count (lfunc_up_to nk) in 
    let rfunc_1_up_to (nf: inbetween n0 nk) = init_func_from_expr expr1 n0 nf in
    let rfunc_2_up_to (nf: inbetween n0 nk) = init_func_from_expr expr2 n0 nf in 
    let fullseq_r1 = init full_count (rfunc_1_up_to nk) in
    let fullseq_r2 = init full_count (rfunc_2_up_to nk) in
    fold_decomposition cm n0 (nk-1) expr1 expr2;
    let subseq = init sub_count (lfunc_up_to nk) in
    let subfold = foldm_snoc cm subseq in
    let last = lfunc_up_to nk sub_count in
    lemma_eq_elim (fst (un_snoc fullseq)) subseq; // subseq is literally (liat fullseq)   
    let fullfold = foldm_snoc cm fullseq in 
    let subseq_r1 = init sub_count (rfunc_1_up_to nk) in
    let subseq_r2 = init sub_count (rfunc_2_up_to nk) in
    lemma_eq_elim (fst (un_snoc fullseq_r1)) subseq_r1; // subseq is literally (liat fullseq)
    lemma_eq_elim (fst (un_snoc fullseq_r2)) subseq_r2; // subseq is literally (liat fullseq)      
    lemma_eq_elim (init sub_count (lfunc_up_to nk)) subseq; 
    lemma_eq_elim (init sub_count (lfunc_up_to (nk-1))) subseq;  
    lemma_eq_elim subseq_r1 (init sub_count (rfunc_1_up_to (nk-1)));
    lemma_eq_elim subseq_r2 (init sub_count (rfunc_2_up_to (nk-1)));
    let fullfold_r1 = foldm_snoc cm fullseq_r1 in
    let fullfold_r2 = foldm_snoc cm fullseq_r2 in
    let subfold_r1 = foldm_snoc cm subseq_r1 in
    let subfold_r2 = foldm_snoc cm subseq_r2 in      
    cm.congruence  (foldm_snoc cm (init sub_count (rfunc_1_up_to (nk-1)))) 
                   (foldm_snoc cm (init sub_count (rfunc_2_up_to (nk-1))))
                   subfold_r1 subfold_r2; 
    let last_r1 = rfunc_1_up_to nk sub_count in
    let last_r2 = rfunc_2_up_to nk sub_count in   
    cm.congruence subfold last (subfold_r1 `cm.mult` subfold_r2) last;
    aux_shuffle_lemma cm subfold_r1 subfold_r2 (rfunc_1_up_to nk sub_count) (rfunc_2_up_to nk sub_count);     
    cm.congruence (subfold_r1 `cm.mult` (rfunc_1_up_to nk sub_count)) (subfold_r2 `cm.mult` (rfunc_2_up_to nk sub_count))
                  (foldm_snoc cm fullseq_r1) (foldm_snoc cm fullseq_r2)
) 
#pop-options

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
  big_sum_equals_foldm cm 0 (n-1) expr;
  lemma_eq_elim (init (range_count 0 (n-1)) (fun i -> expr (0+i))) (init n (generator (m-1)))

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
