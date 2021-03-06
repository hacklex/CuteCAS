(*
   Copyright 2008-2022 Microsoft Research
   
   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at
   
       http://www.apache.org/licenses/LICENSE-2.0
       
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: A. Rozanov
*)

(*
   In this module we provide basic definitions to work with matrices via
   seqs, and define transpose transform together with theorems that assert
   matrix fold equality of original and transposed matrices.
*)


module FStar.Seq.Matrix

module CE = FStar.Algebra.CommMonoid.Equiv
module CF = FStar.Algebra.CommMonoid.Fold

open FStar.IntegerIntervals
open FStar.Math.Lemmas
open FStar.Seq.Properties
open FStar.Seq.Permutation
open FStar.Seq.Base
open FStar.Mul

let flattened_index_is_under_flattened_size (m n: pos) (i: under m) (j: under n) 
  : Lemma ((((i*n)+j)) < m*n) = assert (i*n <= (m-1)*n)
  
(* Returns the flattened index from 2D indices pair 
   and the two array dimensions. *) 
let get_ij (m n: pos) (i:under m) (j: under n) : under (m*n) 
  = flattened_index_is_under_flattened_size m n i j; i*n + j 

(* The following two functions return the matrix indices from the 
   flattened index and the two dimensions *)
let get_i (m n: pos) (ij: under (m*n)) : under m = ij / n
let get_j (m n: pos) (ij: under (m*n)) : under n = ij % n

(* A proof that getting a 2D index back from the flattened 
   index works correctly *)
let consistency_of_i_j (m n: pos) (i: under m) (j: under n) 
  : Lemma (get_i m n (get_ij m n i j) = i /\ get_j m n (get_ij m n i j) = j) = 
  flattened_index_is_under_flattened_size m n i j; //speeds up the proof
  lemma_mod_plus j i n;
  lemma_div_plus j i n 
  
(* A proof that getting the flattened index from 2D 
   indices works correctly *)
let consistency_of_ij (m n: pos) (ij: under (m*n)) 
  : Lemma (get_ij m n (get_i m n ij) (get_j m n ij) == ij) = ()

(* The transposition transform for the flattened index *)
let transpose_ji (m n: pos) (ij: under (m*n)) : under (n*m) =  
  flattened_index_is_under_flattened_size n m (get_j m n ij) (get_i m n ij);
  (get_j m n ij)*m + (get_i m n ij)

(* Auxiliary arithmetic lemma *)
let lemma_indices_transpose (m: pos) (i: under m) (j: nat) 
  : Lemma (((j*m+i)%m=i) && ((j*m+i)/m=j)) = lemma_mod_plus i j m
 
(* A proof of trasnspotition transform bijectivity *)
let ji_is_transpose_of_ij (m n: pos) (ij: under (m*n)) 
  : Lemma (transpose_ji n m (transpose_ji m n ij) = ij) = 
  lemma_indices_transpose m (get_i m n ij) (get_j m n ij)
   
(* A proof that 2D indices are swapped with the transpotition transform *)
let dual_indices (m n: pos) (ij: under (m*n)) : Lemma (
     (get_j n m (transpose_ji m n ij) = get_i m n ij) /\
     (get_i n m (transpose_ji m n ij) = get_j m n ij)) 
  = consistency_of_ij m n ij;
    lemma_indices_transpose m (get_i m n ij) (get_j m n ij)  

type matrix_generator c (m n: pos) = under m -> under n -> c
 
type matrix c m n = z:seq c { length z = m*n }

type matrix_of #c (#m #n: pos) (gen: matrix_generator c m n) = z:matrix c m n {
  (forall (i: under m) (j: under n). index z (get_ij m n i j) == gen i j) /\ 
  (forall (ij: under (m*n)). (index z ij) == (gen (get_i m n ij) (get_j m n ij)))  
}

(* A flattened matrix (seq) constructed from generator function
   Notice how the domains of both indices are strictly controlled. *)
let matrix_seq #c (#m #n: pos) (generator: matrix_generator c m n)
  : matrix_of generator =  
  let mn = m * n in
  let generator_ij ij = generator (get_i m n ij) (get_j m n ij) in
  let flat_indices = indices_seq mn in  
  let result = map_seq generator_ij flat_indices in
  map_seq_len generator_ij flat_indices;
  assert (length result == length flat_indices);
  let aux (i: under m) (j: under n) 
    : Lemma (index (map_seq generator_ij flat_indices) (get_ij m n i j) == generator i j) 
    = consistency_of_i_j m n i j;
      consistency_of_ij m n (get_ij m n i j);
      assert (generator_ij (get_ij m n i j) == generator i j);
      map_seq_index generator_ij flat_indices (get_ij m n i j) in
  let aux1 (ij: under mn) 
    : Lemma (index (map_seq generator_ij flat_indices) ij == generator_ij ij) 
    = map_seq_index generator_ij flat_indices ij in 
  FStar.Classical.forall_intro aux1;
  FStar.Classical.forall_intro_2 aux;
  result
  
(* This auxiliary lemma establishes the decomposition of the seq-matrix 
   into the concatenation of its first (m-1) rows and its last row (thus snoc)  *)
let matrix_append_snoc_lemma #c #eq (#m #n: pos) (generator: matrix_generator c m n)
  : Lemma (matrix_seq generator == (slice (matrix_seq generator) 0 ((m-1)*n))
                                   `append`
                                   (slice (matrix_seq generator) ((m-1)*n) (m*n))) 
  = lemma_eq_elim (matrix_seq generator) 
                  (append (slice (matrix_seq generator) 0 ((m-1)*n))
                          (slice (matrix_seq generator) ((m-1)*n) (m*n)))

(* This auxiliary lemma establishes the equality of the fold of the entire matrix
   to the op of folds of (the submatrix of the first (m-1) rows) and (the last row). *) 
#push-options "--ifuel 0 --fuel 0 --z3rlimit 5"
let matrix_fold_snoc_lemma #c #eq 
                           (#m: not_less_than 2) 
                           (#n: pos) 
                           (cm: CE.cm c eq) 
                           (generator: matrix_generator c m n)
  : Lemma (foldm_snoc cm (matrix_seq generator) `eq.eq` 
    cm.mult (foldm_snoc cm (matrix_seq #c #(m-1) #n generator))
            (foldm_snoc cm (slice (matrix_seq #c #m #n generator) ((m-1)*n) (m*n))))
  = lemma_eq_elim (matrix_seq generator)
                  ((matrix_seq #c #(m-1) #n generator) `append` 
                  (slice (matrix_seq generator) ((m-1)*n) (m*n)));    
    foldm_snoc_append cm (matrix_seq #c #(m-1) #n generator) 
                         (slice (matrix_seq generator) ((m-1)*n) (m*n)) 

#push-options "--ifuel 0 --fuel 1 --z3rlimit 1"
let foldm_snoc_last #c #eq (cm: CE.cm c eq) (s: seq c{length s > 0})
  : Lemma (foldm_snoc cm s == cm.mult (snd (un_snoc s)) (foldm_snoc cm (fst (un_snoc s)))) 
  = ()
#pop-options 

let rec matrix_fold_equals_fold_of_seq_folds #c #eq 
                                         (#m #n: pos)
                                         (cm: CE.cm c eq)
                                         (generator: matrix_generator c m n)
  : Lemma (ensures foldm_snoc cm (matrix_seq generator) `eq.eq`
                   foldm_snoc cm (init m (fun i -> foldm_snoc cm (init n (generator i))))) 
          (decreases m) =
  let lhs_seq = matrix_seq generator in
  let rhs_seq = init m (fun i -> foldm_snoc cm (init n (generator i))) in
  let lhs = foldm_snoc cm (matrix_seq generator) in
  let rhs = foldm_snoc cm rhs_seq in
  if m=1 then (
    foldm_snoc_singleton cm (foldm_snoc cm (init n (generator 0)));
    lemma_eq_elim (create 1 (foldm_snoc cm (init n (generator 0))))
                  (init m (fun i -> foldm_snoc cm (init n (generator i))));
    eq.reflexivity (foldm_snoc cm (create 1 (foldm_snoc cm (init n (generator 0)))));
    lemma_eq_elim (matrix_seq generator) (init n (generator 0));
    eq.symmetry rhs lhs
  ) 
  else (
    Classical.forall_intro_2 (Classical.move_requires_2 eq.symmetry);
    matrix_fold_snoc_lemma cm generator;
    let matrix = matrix_seq generator in
    let subgen = (fun (i:under (m-1)) (j:under n) -> generator i j) in 
    let submatrix = slice (matrix_seq generator) 0 ((m-1)*n) in
    let last_row = slice (matrix_seq #c #m #n generator) ((m-1)*n) (m*n) in
    Math.Lemmas.multiplication_order_lemma (m) (m-1) n;
    lemma_len_slice (matrix_seq generator) ((m-1)*n) (m*n); 
    lemma_eq_elim (matrix_seq subgen) submatrix;
    matrix_fold_equals_fold_of_seq_folds cm subgen;
    lemma_eq_elim last_row (init n (generator (m-1))); 
    lemma_eq_elim (matrix_seq generator) 
                  ((matrix_seq subgen) `append` (init n (generator (m-1))));
    let rec_seq = init (m-1) (fun i -> foldm_snoc cm (init n (subgen i))) in
    let rec_subseq = init (m-1) (fun i -> foldm_snoc cm (init n (generator i))) in
    let aux_eq (i: under (m-1)) : Lemma (index rec_seq i == index rec_subseq i) = 
      lemma_eq_elim (init n (subgen i)) (init n (generator i));
    () in 
    Classical.forall_intro aux_eq;
    foldm_snoc_append cm (matrix_seq subgen) last_row;
    lemma_eq_elim rhs_seq (snoc rec_subseq (foldm_snoc cm (init n (generator (m-1)))));
    let liat_rhs_seq, last_rhs_seq = un_snoc rhs_seq in
    lemma_eq_elim liat_rhs_seq rec_seq;
    foldm_snoc_last cm rhs_seq;
    lemma_eq_elim rec_subseq liat_rhs_seq; 
    eq.reflexivity (foldm_snoc cm last_row);
    cm.congruence (foldm_snoc cm (matrix_seq subgen)) (foldm_snoc cm last_row)
                  (foldm_snoc cm liat_rhs_seq) (last_rhs_seq);
    eq.transitivity lhs 
                    (foldm_snoc cm (matrix_seq subgen) `cm.mult` foldm_snoc cm last_row)
                    (foldm_snoc cm liat_rhs_seq `cm.mult` last_rhs_seq); 
    cm.commutativity (foldm_snoc cm liat_rhs_seq) last_rhs_seq;
    eq.transitivity lhs (foldm_snoc cm liat_rhs_seq `cm.mult` last_rhs_seq) rhs 
  )
#pop-options 

(* This auxiliary lemma shows that the fold of the last line of a matrix
   is equal to the corresponding fold of the generator function *)
 
(* This lemma establishes that the fold of a matrix is equal to
   nested Algebra.CommMonoid.Fold.fold over the matrix generator *)
#push-options "--ifuel 0 --fuel 0 --z3rlimit 50 --z3refresh"
let matrix_fold_equals_func_double_fold #c #eq 
                                       (#m #n: pos)
                                       (cm: CE.cm c eq)
                                       (generator: matrix_generator c m n)
  : Lemma (foldm_snoc cm (matrix_seq generator) `eq.eq` 
           CF.fold cm 0 (m-1) (fun (i:under m) -> CF.fold cm 0 (n-1) (generator i)))
  = let matrix_last_line_equals_gen_fold #c #eq 
                                         (#m #n: pos)  
                                         (cm: CE.cm c eq) 
                                         (generator: matrix_generator c m n) 
      : Lemma (foldm_snoc cm (slice (matrix_seq generator) ((m-1)*n) (m*n)) 
              `eq.eq` CF.fold cm 0 (n-1) (generator (m-1)))
      = lemma_eq_elim (slice (matrix_seq generator) ((m-1)*n) (m*n)) 
                      (init n (generator (m-1))); 
        let g : ifrom_ito 0 (n-1) -> c = generator (m-1) in 
        CF.fold_equals_seq_foldm cm 0 (n-1) g;
        let gen = CF.init_func_from_expr g 0 (n-1) in
        eq.reflexivity (foldm_snoc cm (init (closed_interval_size 0 (n-1)) gen));  
        lemma_eq_elim (slice (matrix_seq generator) ((m-1)*n) (m*n))    
                      (init (closed_interval_size 0 (n-1)) gen); 
        eq.symmetry (CF.fold cm 0 (n-1) (generator (m-1)))
                    (foldm_snoc cm (init (closed_interval_size 0 (n-1)) gen)); 
        eq.transitivity (foldm_snoc cm (slice (matrix_seq generator) ((m-1)*n) (m*n)))
                        (foldm_snoc cm (init (closed_interval_size 0 (n-1)) gen))
                        (CF.fold cm 0 (n-1) (generator (m-1))) in
    let rec matrix_fold_aux #c #eq //inner lemma needed for precise generator domain control
                               (#gen_m #gen_n: pos) //full generator domain
                               (cm: CE.cm c eq) 
                               (m: ifrom_ito 1 gen_m) (n: ifrom_ito 1 gen_n) //subdomain
                               (generator: matrix_generator c gen_m gen_n)
    : Lemma (ensures foldm_snoc cm (matrix_seq #c #m #n generator) `eq.eq` 
                     CF.fold cm 0 (m-1) (fun (i: under m) -> CF.fold cm 0 (n-1) (generator i)))
            (decreases m) = 
      if m = 1 then begin
        matrix_last_line_equals_gen_fold #c #eq #m #n cm generator; 
        CF.fold_singleton_lemma cm 0 (fun (i:under m) -> CF.fold cm 0 (n-1) (generator i))
      end else begin     
        Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);  
        matrix_fold_aux cm (m-1) n generator;    
        let outer_func (i: under m) = CF.fold cm 0 (n-1) (generator i) in
        let outer_func_on_subdomain (i: under (m-1)) = CF.fold cm 0 (n-1) (generator i) in
        CF.fold_equality cm 0 (m-2) outer_func_on_subdomain outer_func;
        CF.fold_snoc_decomposition cm 0 (m-1) outer_func;  
        matrix_fold_snoc_lemma #c #eq #m #n cm generator;
        matrix_last_line_equals_gen_fold #c #eq #m #n cm generator;
        cm.congruence (foldm_snoc cm (matrix_seq #c #(m-1) #n generator))
                      (foldm_snoc cm (slice (matrix_seq #c #m #n generator) ((m-1)*n) (m*n)))
                      (CF.fold cm 0 (m-2) outer_func)
                      (CF.fold cm 0 (n-1) (generator (m-1))) 
      end in matrix_fold_aux cm m n generator
#pop-options 

(* This function provides the transposed matrix generator, with indices swapped
   Notice how the forall property of the result function is happily proved 
   automatically by z3 :) *)
let transposed_matrix_gen #c (#m:pos) (#n:pos) (generator: matrix_generator c m n) 
  : (f: matrix_generator c n m { forall i j. f j i == generator i j }) 
  = fun j i -> generator i j


(* This lemma shows that the transposed matrix is 
   a permutation of the original one *)
let matrix_transpose_is_permutation #c (#m #n: pos) 
                             (generator: matrix_generator c m n)
  : Lemma (is_permutation (matrix_seq generator) 
                          (matrix_seq (transposed_matrix_gen generator)) 
                          (transpose_ji m n)) = 
  let matrix_transposed_eq_lemma #c (#m #n: pos) 
                                        (gen: matrix_generator c m n) 
                                        (ij: under (m*n)) 
    : Lemma (index (matrix_seq gen) ij ==
             index (matrix_seq (transposed_matrix_gen gen)) (transpose_ji m n ij)) 
    = () in 
  let transpose_inequality_lemma (m n: pos) (ij: under (m*n)) (kl: under (n*m)) 
    : Lemma (requires kl <> ij) (ensures transpose_ji m n ij <> transpose_ji m n kl) = 
      dual_indices m n ij;
      dual_indices m n kl in
  Classical.forall_intro (matrix_transposed_eq_lemma generator); 
  Classical.forall_intro_2 (Classical.move_requires_2 
                           (transpose_inequality_lemma m n));
  reveal_is_permutation (matrix_seq generator)
                        (matrix_seq (transposed_matrix_gen generator))
                        (transpose_ji m n) 

(* Fold over matrix equals fold over transposed matrix *)
let matrix_fold_equals_fold_of_transpose #c #eq 
                                         (#m #n: pos) 
                                         (cm: CE.cm c eq) 
                                         (gen: matrix_generator c m n)
  : Lemma (foldm_snoc cm (matrix_seq gen) `eq.eq`
           foldm_snoc cm (matrix_seq (transposed_matrix_gen gen))) = 
  let matrix_mn = matrix_seq gen in
  let matrix_nm = matrix_seq (transposed_matrix_gen gen) in
  matrix_transpose_is_permutation gen;
  foldm_snoc_perm cm (matrix_seq gen)
                     (matrix_seq (transposed_matrix_gen gen))
                     (transpose_ji m n)
