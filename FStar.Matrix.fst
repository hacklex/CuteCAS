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


module FStar.Matrix

module CE = FStar.Algebra.CommMonoid.Equiv
module CF = FStar.Algebra.CommMonoid.Fold
module SP = FStar.Seq.Permutation
module SB = FStar.Seq.Base
module SProp = FStar.Seq.Properties
module ML = FStar.Math.Lemmas

open FStar.IntegerIntervals   
open FStar.Mul

type matrix c m n = z:SB.seq c { SB.length z = m*n }
 
let seq_of_matrix #c #m #n mx = mx

let ijth #c #m #n mx i j = SB.index mx (get_ij m n i j)

let ijth_lemma #c #m #n mx i j 
 : Lemma (ijth mx i j == SB.index (seq_of_matrix mx) (get_ij m n i j)) = ()

let matrix_of_seq #c m n s = s

let foldm #c #eq #m #n cm mx = SP.foldm_snoc cm mx
 
let matrix_fold_equals_fold_of_seq #c #eq #m #n cm mx
  : Lemma (ensures foldm cm mx `eq.eq` SP.foldm_snoc cm (seq_of_matrix mx)) [SMTPat(foldm cm mx)]
  = eq.reflexivity (foldm cm mx)

let matrix_fold_internal #c #eq #m #n (cm:CE.cm c eq) (mx: matrix c m n)
  : Lemma (ensures foldm cm mx == SP.foldm_snoc cm mx) = ()
     
(* A flattened matrix (seq) constructed from generator function
   Notice how the domains of both indices are strictly controlled. *)
let init #c (#m #n: pos) (generator: matrix_generator c m n)
  : matrix_of generator =  
  let mn = m * n in
  let generator_ij ij = generator (get_i m n ij) (get_j m n ij) in
  let flat_indices = indices_seq mn in  
  let result = SProp.map_seq generator_ij flat_indices in
  SProp.map_seq_len generator_ij flat_indices;
  assert (SB.length result == SB.length flat_indices);
  let aux (i: under m) (j: under n) 
    : Lemma (SB.index (SProp.map_seq generator_ij flat_indices) (get_ij m n i j) == generator i j) 
    = consistency_of_i_j m n i j;
      consistency_of_ij m n (get_ij m n i j);
      assert (generator_ij (get_ij m n i j) == generator i j);
      SProp.map_seq_index generator_ij flat_indices (get_ij m n i j) in
  let aux1 (ij: under mn) 
    : Lemma (SB.index (SProp.map_seq generator_ij flat_indices) ij == generator_ij ij) 
    = SProp.map_seq_index generator_ij flat_indices ij in 
  FStar.Classical.forall_intro aux1;
  FStar.Classical.forall_intro_2 aux;
  result
  
private let matrix_seq #c #m #n (gen: matrix_generator c m n) : (t:SB.seq c{ (SB.length t = (m*n)) /\
  (forall (i: under m) (j: under n). SB.index t (get_ij m n i j) == gen i j) /\ 
  (forall(ij: under (m*n)). SB.index t ij == gen (get_i m n ij) (get_j m n ij))
}) = init gen

(* This auxiliary lemma establishes the decomposition of the seq-matrix 
   into the concatenation of its first (m-1) rows and its last row (thus snoc)  *)
let matrix_append_snoc_lemma #c (#m #n: pos) (generator: matrix_generator c m n)
  : Lemma (matrix_seq generator == (SB.slice (matrix_seq generator) 0 ((m-1)*n))
                                   `SB.append`
                                   (SB.slice (matrix_seq generator) ((m-1)*n) (m*n))) 
  = SB.lemma_eq_elim (matrix_seq generator) 
                  (SB.append (SB.slice (matrix_seq generator) 0 ((m-1)*n))
                          (SB.slice (matrix_seq generator) ((m-1)*n) (m*n)))

let matrix_seq_decomposition_lemma  #c (#m:greater_than 1) (#n: pos) (generator: matrix_generator c m n)
  : Lemma ((matrix_seq generator) == 
          SB.append (matrix_seq #c #(m-1) #n generator)
                    (SB.slice (matrix_seq generator) ((m-1)*n) (m*n)))
  = SB.lemma_eq_elim (matrix_seq generator)
                  ((matrix_seq #c #(m-1) #n generator) `SB.append` 
                  (SB.slice (matrix_seq generator) ((m-1)*n) (m*n))) 

(* This auxiliary lemma establishes the equality of the fold of the entire matrix
   to the op of folds of (the submatrix of the first (m-1) rows) and (the last row). *) 
let matrix_fold_snoc_lemma #c #eq 
                           (#m: not_less_than 2) 
                           (#n: pos) 
                           (cm: CE.cm c eq) 
                           (generator: matrix_generator c m n)
  : Lemma (assert ((m-1)*n < m*n);
            SP.foldm_snoc cm (matrix_seq generator) `eq.eq` 
    cm.mult (SP.foldm_snoc cm (matrix_seq #c #(m-1) #n generator))
            (SP.foldm_snoc cm (SB.slice (matrix_seq #c #m #n generator) ((m-1)*n) (m*n))))
  = SB.lemma_eq_elim (matrix_seq generator)
                  ((matrix_seq #c #(m-1) #n generator) `SB.append` 
                  (SB.slice (matrix_seq generator) ((m-1)*n) (m*n)));    
    SP.foldm_snoc_append cm (matrix_seq #c #(m-1) #n generator) 
                         (SB.slice (matrix_seq generator) ((m-1)*n) (m*n)) 

let foldm_snoc_last #c #eq (cm: CE.cm c eq) (s: SB.seq c{SB.length s > 0})
  : Lemma (SP.foldm_snoc cm s == cm.mult (snd (SProp.un_snoc s)) 
                                         (SP.foldm_snoc cm (fst (SProp.un_snoc s)))) 
  = ()


let matrix_submatrix_lemma #c (#m: not_less_than 2) (#n: pos)  
                           (generator: matrix_generator c m n)
  : Lemma ((matrix_seq generator) == (matrix_seq (fun (i:under(m-1)) (j:under n) -> generator i j) `SB.append` SB.init n (generator (m-1))))
  = SB.lemma_eq_elim (matrix_seq (fun (i:under (m-1)) (j:under n) -> generator i j)) (matrix_seq #c #(m-1) #n generator);
    SB.lemma_eq_elim (SB.slice (matrix_seq generator) ((m-1)*n) (m*n)) (SB.init n (generator (m-1)));
    matrix_seq_decomposition_lemma generator

(* This one could be probably written more efficiently -- 
   but this implementation also works. *)
#push-options "--ifuel 0 --fuel 0 --z3rlimit 25"
#restart-solver
let rec matrix_fold_equals_fold_of_seq_folds #c #eq #m #n cm generator : Lemma 
  (ensures foldm cm (init generator) `eq.eq`
           SP.foldm_snoc cm (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i)))) /\ 
           SP.foldm_snoc cm (seq_of_matrix (init generator)) `eq.eq`
           SP.foldm_snoc cm (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i))))) 
  (decreases m) =
  let lhs_seq = matrix_seq generator in
  let rhs_seq = SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i))) in
  let lhs = SP.foldm_snoc cm (matrix_seq generator) in
  let rhs = SP.foldm_snoc cm rhs_seq in
  if m=1 then begin
    SP.foldm_snoc_singleton cm (SP.foldm_snoc cm (SB.init n (generator 0)));
    SB.lemma_eq_elim (SB.create 1 (SP.foldm_snoc cm (SB.init n (generator 0))))
                  (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i))));
    SB.lemma_eq_elim (matrix_seq generator) (SB.init n (generator 0));
    eq.symmetry rhs lhs 
  end else 
  let matrix = matrix_seq generator in 
  let subgen = (fun (i:under (m-1)) (j:under n) -> generator i j) in 
  let submatrix = SB.slice (matrix_seq generator) 0 ((m-1)*n) in
  let last_row = SB.slice (matrix_seq #c #m #n generator) ((m-1)*n) (m*n) in
  Classical.forall_intro_2 (Classical.move_requires_2 eq.symmetry);
  matrix_fold_snoc_lemma cm generator;
  Math.Lemmas.multiplication_order_lemma (m) (m-1) n;
  assert ((m-1)*n < m*n);
  SB.lemma_len_slice (matrix_seq generator) ((m-1)*n) (m*n); 
  SB.lemma_eq_elim (matrix_seq subgen) submatrix;
  matrix_fold_equals_fold_of_seq_folds cm subgen;    
  SB.lemma_eq_elim last_row (SB.init n (generator (m-1))); 
  matrix_submatrix_lemma generator;
  let rec_seq = SB.init (m-1) (fun i -> SP.foldm_snoc cm (SB.init n (subgen i))) in
  let rec_subseq = SB.init (m-1) (fun i -> SP.foldm_snoc cm (SB.init n (generator i))) in
  let aux_eq (i: under (m-1)) : Lemma (SB.index rec_seq i == SB.index rec_subseq i) = 
    SB.lemma_eq_elim (SB.init n (subgen i)) (SB.init n (generator i));
  () in 
  Classical.forall_intro aux_eq;
  matrix_append_snoc_lemma generator;
  SP.foldm_snoc_append cm (matrix_seq subgen) last_row;
  SB.lemma_eq_elim rhs_seq (SProp.snoc rec_subseq (SP.foldm_snoc cm (SB.init n (generator (m-1)))));
  let liat_rhs_seq, last_rhs_seq = SProp.un_snoc rhs_seq in
  SB.lemma_eq_elim liat_rhs_seq rec_seq;
  foldm_snoc_last cm rhs_seq;
  SB.lemma_eq_elim rec_subseq liat_rhs_seq; 
  eq.reflexivity (SP.foldm_snoc cm last_row);
  cm.congruence (SP.foldm_snoc cm (matrix_seq subgen)) (SP.foldm_snoc cm last_row)
                (SP.foldm_snoc cm liat_rhs_seq) (last_rhs_seq);
  eq.transitivity lhs 
                  (SP.foldm_snoc cm (matrix_seq subgen) `cm.mult` SP.foldm_snoc cm last_row)
                  (SP.foldm_snoc cm liat_rhs_seq `cm.mult` last_rhs_seq); 
  cm.commutativity (SP.foldm_snoc cm liat_rhs_seq) last_rhs_seq;
  eq.transitivity lhs (SP.foldm_snoc cm liat_rhs_seq `cm.mult` last_rhs_seq) rhs;
  matrix_fold_equals_fold_of_seq cm (init generator);
  assert (SP.foldm_snoc cm (matrix_seq generator) `eq.eq` rhs);
  assert (lhs == SP.foldm_snoc cm (matrix_seq generator));
  assert (lhs `eq.eq` rhs);
  assert_spinoff (foldm cm (init generator) == lhs);
  assert (SP.foldm_snoc cm (init generator) `eq.eq` rhs);
  () 
#pop-options 

(* This auxiliary lemma shows that the fold of the last line of a matrix
   is equal to the corresponding fold of the generator function *) 
let matrix_last_line_equals_gen_fold #c #eq 
                                        (#m #n: pos)  
                                        (cm: CE.cm c eq) 
                                        (generator: matrix_generator c m n) 
    : Lemma (SP.foldm_snoc cm (SB.slice (matrix_seq generator) ((m-1)*n) (m*n)) 
            `eq.eq` CF.fold cm 0 (n-1) (generator (m-1)))
    = 

      let slice = SB.slice #c in
      let foldm_snoc = SP.foldm_snoc #c #eq in
      assert (matrix_seq generator == seq_of_matrix (init generator));
      let init = SB.init #c in
      let lemma_eq_elim = SB.lemma_eq_elim #c in 
      lemma_eq_elim (slice (matrix_seq generator) ((m-1)*n) (m*n)) 
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
                      (CF.fold cm 0 (n-1) (generator (m-1))) 
 

#push-options "--ifuel 0 --fuel 0 --z3rlimit 4"
let rec matrix_fold_aux #c #eq // lemma needed for precise generator domain control
                           (#gen_m #gen_n: pos) // full generator domain
                           (cm: CE.cm c eq) 
                           (m: ifrom_ito 1 gen_m) (n: ifrom_ito 1 gen_n) //subdomain
                           (generator: matrix_generator c gen_m gen_n)
  : Lemma (ensures SP.foldm_snoc cm (matrix_seq #c #m #n generator) `eq.eq` 
                   CF.fold cm 0 (m-1) (fun (i: under m) -> CF.fold cm 0 (n-1) (generator i)))
          (decreases m) = 
  Classical.forall_intro_2 (ijth_lemma (init generator));
  let slice = SB.slice #c in
  let foldm_snoc = SP.foldm_snoc #c #eq in
  let lemma_eq_elim = SB.lemma_eq_elim #c in
  if m = 1 then begin
    matrix_fold_equals_fold_of_seq cm (init generator);
    matrix_last_line_equals_gen_fold #c #eq #m #n cm generator;  
    CF.fold_singleton_lemma cm 0 (fun (i:under m) -> CF.fold cm 0 (n-1) (generator i));
    assert (CF.fold cm 0 (m-1) (fun (i: under m) -> CF.fold cm 0 (n-1) (generator i)) 
            == CF.fold cm 0 (n-1) (generator 0));
    ()
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
  end  
#pop-options

(* This lemma establishes that the fold of a matrix is equal to
   nested Algebra.CommMonoid.Fold.fold over the matrix generator *)
let matrix_fold_equals_func_double_fold #c #eq #m #n cm generator
  : Lemma (foldm cm (init generator) `eq.eq` 
           CF.fold cm 0 (m-1) (fun (i:under m) -> CF.fold cm 0 (n-1) (generator i)))
  = let slice = SB.slice #c in
    let foldm_snoc = SP.foldm_snoc #c #eq in
    let init = SB.init #c in
    let lemma_eq_elim = SB.lemma_eq_elim #c in 
    matrix_fold_aux cm m n generator

let rec eq_of_seq #c (eq:CE.equiv c) (s1 s2: SB.seq c) 
  : Tot prop (decreases SB.length s1) = 
  (SB.length s1 = SB.length s2 /\
   (SB.length s1 = 0 \/ (
    let s1s, s1l = SProp.un_snoc s1 in
     let s2s, s2l = SProp.un_snoc s2 in
      eq.eq s1l s2l /\ eq_of_seq eq s1s s2s)))

let rec eq_of_seq_element_equality #c (eq: CE.equiv c) (s1 s2: SB.seq c)
  : Lemma (requires eq_of_seq eq s1 s2) 
          (ensures SB.length s1 = SB.length s2 /\ (forall (i: under (SB.length s1)). (SB.index s1 i `eq.eq` SB.index s2 i))) 
          (decreases SB.length s1)
  = 
  if (SB.length s1 > 0) then 
  let s1liat, s1last = SProp.un_snoc s1 in
  let s2liat, s2last = SProp.un_snoc s2 in
  eq_of_seq_element_equality eq s1liat s2liat

let rec eq_of_seq_from_element_equality #c (eq: CE.equiv c) (s1 s2: SB.seq c)
  : Lemma (requires (SB.length s1 = SB.length s2) /\ (forall (i: under (SB.length s1)). (SB.index s1 i `eq.eq` SB.index s2 i)))
          (ensures eq_of_seq eq s1 s2)
          (decreases SB.length s1) = 
  if SB.length s1 = 0 then () else 
  let s1liat, s1last = SProp.un_snoc s1 in
  let s2liat, s2last = SProp.un_snoc s2 in  
  eq_of_seq_from_element_equality eq s1liat s2liat

let eq_of_seq_condition #c (eq: CE.equiv c) (s1 s2: SB.seq c)
  : Lemma ((SB.length s1==SB.length s2) /\ (forall (i: under (SB.length s1)). (SB.index s1 i `eq.eq` SB.index s2 i)) <==>
            eq_of_seq eq s1 s2) = 
  Classical.move_requires_2 (eq_of_seq_element_equality eq) s1 s2;
  Classical.move_requires_2 (eq_of_seq_from_element_equality eq) s1 s2

let rec eq_of_seq_reflexivity #c (eq: CE.equiv c) (s: SB.seq c)
  : Lemma (ensures eq_of_seq eq s s) (decreases SB.length s) = 
  if SB.length s > 0 then 
  let liat, last = SProp.un_snoc s in
  eq_of_seq_reflexivity eq liat;
  eq.reflexivity last

let rec eq_of_seq_symmetry #c (eq: CE.equiv c) (s1 s2: SB.seq c)
  : Lemma (requires eq_of_seq eq s1 s2) (ensures eq_of_seq eq s2 s1) (decreases SB.length s1) =  
  if SB.length s1 > 0 then 
  let lia1, las1 = SProp.un_snoc s1 in
  let lia2, las2 = SProp.un_snoc s2 in
  eq_of_seq_symmetry eq lia1 lia2;
  eq.symmetry las1 las2

let rec eq_of_seq_transitivity #c (eq: CE.equiv c) (s1 s2 s3: SB.seq c)
  : Lemma (requires eq_of_seq eq s1 s2 /\ eq_of_seq eq s2 s3) (ensures eq_of_seq eq s1 s3) (decreases SB.length s1) =  
  if SB.length s1 > 0 then 
  let lia1, las1 = SProp.un_snoc s1 in
  let lia2, las2 = SProp.un_snoc s2 in
  let lia3, las3 = SProp.un_snoc s3 in
  eq_of_seq_transitivity eq lia1 lia2 lia3;
  eq.transitivity las1 las2 las3

let seq_equiv #c (eq:CE.equiv c) : (CE.equiv (SB.seq c)) = 
  CE.EQ (eq_of_seq eq) (eq_of_seq_reflexivity eq)
                       (eq_of_seq_symmetry eq)
                       (eq_of_seq_transitivity eq)

let matrix_add_generator #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb: matrix c m n) 
  : matrix_generator c m n = fun i j -> add.mult (ijth ma i j) (ijth mb i j)

let matrix_add #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb: matrix c m n) 
  : matrix_of (matrix_add_generator add ma mb)
  = init (matrix_add_generator add ma mb)

let matrix_add_ijth #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb: matrix c m n) (i: under m) (j: under n)
  : Lemma (ijth (matrix_add add ma mb) i j == add.mult (ijth ma i j) (ijth mb i j)) = ()

let matrix_eq_fun #c (#m #n: pos) (eq: CE.equiv c) (ma mb: matrix c m n) =   
  eq_of_seq eq (seq_of_matrix ma) (seq_of_matrix mb)

let matrix_equiv #c (eq: CE.equiv c) (m n: pos) : CE.equiv (matrix c m n) = 
  CE.EQ (matrix_eq_fun eq)
        (fun m -> eq_of_seq_reflexivity eq (seq_of_matrix m))
        (fun ma mb -> eq_of_seq_symmetry eq (seq_of_matrix ma) (seq_of_matrix mb))
        (fun ma mb mc -> eq_of_seq_transitivity eq (seq_of_matrix ma) (seq_of_matrix mb) (seq_of_matrix mc))

let matrix_equiv_ijth #c (#m #n: pos) (eq: CE.equiv c) (ma mb: matrix c m n) (i: under m) (j: under n)
  : Lemma (requires (matrix_equiv eq m n).eq ma mb) (ensures ijth ma i j `eq.eq` ijth mb i j) = 
  eq_of_seq_element_equality eq (seq_of_matrix ma) (seq_of_matrix mb)

#push-options "--fuel 1 --z3rlimit 2"
let matrix_equiv_from_element_eq #c (#m #n: pos) (eq: CE.equiv c) (ma mb: matrix c m n)
  : Lemma (requires (forall (i: under m) (j: under n). ijth ma i j `eq.eq` ijth mb i j))
          (ensures matrix_eq_fun eq ma mb) = 
  assert (SB.length (seq_of_matrix ma) = SB.length (seq_of_matrix mb));
  let s1 = seq_of_matrix ma in
  let s2 = seq_of_matrix mb in
  assert (forall (ij: under (m*n)). SB.index s1 ij == ijth ma (get_i m n ij) (get_j m n ij));
  assert (forall (ij: under (m*n)). SB.index s2 ij == ijth mb (get_i m n ij) (get_j m n ij));
  assert (forall (ij: under (m*n)). SB.index s1 ij `eq.eq` SB.index s2 ij);  
  eq_of_seq_from_element_equality eq (seq_of_matrix ma) (seq_of_matrix mb)
#pop-options

let matrix_equiv_from_proof #c (#m #n: pos) (eq: CE.equiv c) (ma mb: matrix c m n)
  (proof: (i:under m) -> (j:under n) -> Lemma (eq.eq (ijth ma i j) (ijth mb i j)))
  : Lemma (matrix_eq_fun eq ma mb)
  = Classical.forall_intro_2 proof; 
    matrix_equiv_from_element_eq eq ma mb 

let matrix_add_is_associative #c #eq #m #n (add: CE.cm c eq) (ma mb mc: matrix c m n)
  : Lemma (matrix_add add (matrix_add add ma mb) mc `(matrix_equiv eq m n).eq` 
           matrix_add add ma (matrix_add add mb mc)) =  
  matrix_equiv_from_proof eq 
    (matrix_add add (matrix_add add ma mb) mc)
    (matrix_add add ma (matrix_add add mb mc))  
    (fun i j -> add.associativity (ijth ma i j) (ijth mb i j) (ijth mc i j))
 
let matrix_add_is_commutative #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb: matrix c m n)
  : Lemma (matrix_add add ma mb `(matrix_equiv eq m n).eq` matrix_add add mb ma) = 
  matrix_equiv_from_proof eq (matrix_add add ma mb) (matrix_add add mb ma)
    (fun i j -> add.commutativity (ijth ma i j) (ijth mb i j)) 

let matrix_add_congruence #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb mc md: matrix c m n)
  : Lemma (requires matrix_eq_fun eq ma mc /\ matrix_eq_fun eq mb md)
          (ensures matrix_add add ma mb `matrix_eq_fun eq` matrix_add add mc md) =
  matrix_equiv_from_proof eq (matrix_add add ma mb) (matrix_add add mc md)
                          (fun i j -> matrix_equiv_ijth eq ma mc i j;
                                   matrix_equiv_ijth eq mb md i j; 
                                   add.congruence (ijth ma i j) (ijth mb i j) 
                                                  (ijth mc i j) (ijth md i j)) 
 
let matrix_add_zero #c #eq (add: CE.cm c eq) (m n: pos) 
  : (z: matrix c m n { forall (i: under m) (j: under n). ijth z i j == add.unit }) 
  = matrix_of_seq m n (SB.create (m*n) add.unit)

let matrix_add_identity #c #eq (add: CE.cm c eq) (#m #n: pos) (mx: matrix c m n)
  : Lemma (matrix_add add (matrix_add_zero add m n) mx `matrix_eq_fun eq` mx) =
  matrix_equiv_from_proof eq (matrix_add add (matrix_add_zero add m n) mx) mx
                          (fun i j -> add.identity (ijth mx i j))
  
let matrix_add_comm_monoid #c #eq (add: CE.cm c eq) (m n: pos)
  : CE.cm (matrix c m n) (matrix_equiv eq m n) 
  = CE.CM (matrix_add_zero add m n)
          (matrix_add add)
          (matrix_add_identity add)
          (matrix_add_is_associative add)
          (matrix_add_is_commutative add)
          (matrix_add_congruence add)

let col #c #m #n (mx: matrix c m n) (j: under n) = SB.init m (fun (i: under m) -> ijth mx i j) 

let row #c #m #n (mx: matrix c m n) (i: under m) = SB.init n (fun (j: under n) -> ijth mx i j) 

let seq_op_const #c #eq (cm: CE.cm c eq) (s: SB.seq c) (const: c) 
  = SB.init (SB.length s) (fun (i: under (SB.length s)) -> cm.mult (SB.index s i) const)
  
let const_op_seq #c #eq (cm: CE.cm c eq) (const: c) (s: SB.seq c)                       
  = SB.init (SB.length s) (fun (i: under (SB.length s)) -> cm.mult const (SB.index s i))

let seq_of_products #c #eq (mul: CE.cm c eq) (s: SB.seq c) (t: SB.seq c {SB.length t == SB.length s})
  = SB.init (SB.length s) (fun (i: under (SB.length s)) -> SB.index s i `mul.mult` SB.index t i)

let seq_of_products_lemma #c #eq (mul: CE.cm c eq) (s: SB.seq c) (t: SB.seq c {SB.length t == SB.length s})
  (r: SB.seq c{SB.equal r (SB.init (SB.length s) (fun (i: under (SB.length s)) -> SB.index s i `mul.mult` SB.index t i))})
  : Lemma (seq_of_products mul s t == r) = ()

let dot #c #eq (add mul: CE.cm c eq) (s: SB.seq c) (t: SB.seq c{SB.length t == SB.length s}) 
  = SP.foldm_snoc add (seq_of_products mul s t) 

let dot_lemma #c #eq (add mul: CE.cm c eq) (s: SB.seq c) (t: SB.seq c{SB.length t == SB.length s}) 
  : Lemma (dot add mul s t == SP.foldm_snoc add (seq_of_products mul s t)) = ()

let matrix_mul_gen #c #eq #m #n #p (add mul: CE.cm c eq) 
                   (mx: matrix c m n) (my: matrix c n p) 
                   (i: under m) (k: under p)
  = dot add mul (row mx i) (col my k)

let matrix_mul #c #eq #m #n #p (add mul: CE.cm c eq) (mx: matrix c m n) (my: matrix c n p) 
  = init (matrix_mul_gen add mul mx my)

let matrix_row_col_lemma #c #m #n (mx: matrix c m n) (i: under m) (j: under n) 
  : Lemma (ijth mx i j == SB.index (row mx i) j /\ ijth mx i j == SB.index (col mx j) i) = ()

let is_left_distributive #c #eq (mul add: CE.cm c eq) = 
  forall (x y z: c). mul.mult x (add.mult y z) `eq.eq` add.mult (mul.mult x y) (mul.mult x z)

let is_right_distributive #c #eq (mul add: CE.cm c eq) = 
  forall (x y z: c). mul.mult (add.mult x y) z `eq.eq` add.mult (mul.mult x z) (mul.mult y z)

let is_fully_distributive #c #eq (mul add: CE.cm c eq) = is_left_distributive mul add /\ is_right_distributive mul add

let is_absorber #c #eq (z:c) (op: CE.cm c eq) = 
  forall (x:c). op.mult z x `eq.eq` z /\ op.mult x z `eq.eq` z

let seq_last_index #c (s: SB.seq c{SB.length s > 0}) : Lemma (SProp.last s == SB.index s (SB.length s - 1)) = ()

let seq_fold_decomposition #c #eq (cm: CE.cm c eq) (s: SB.seq c{SB.length s > 0}) 
  : Lemma (SP.foldm_snoc cm s == cm.mult (SProp.last s) (SP.foldm_snoc cm (fst (SProp.un_snoc s)))) = ()
  
let rec foldm_snoc_distributivity_left #c #eq (mul add: CE.cm c eq) (a: c) (s: SB.seq c)
  : Lemma (requires is_fully_distributive mul add /\ is_absorber add.unit mul) 
          (ensures mul.mult a (SP.foldm_snoc add s) `eq.eq`
                   SP.foldm_snoc add (const_op_seq mul a s))
          (decreases SB.length s) = 
  if SB.length s > 0 then 
  let ((+), ( * ), (=)) = add.mult, mul.mult, eq.eq in
  let sum s = SP.foldm_snoc add s in
  let liat, last = SProp.un_snoc s in 
  let rhs_liat, rhs_last = SProp.un_snoc (const_op_seq mul a s) in
  foldm_snoc_distributivity_left mul add a liat; 
  SB.lemma_eq_elim rhs_liat (const_op_seq mul a liat);
  eq.reflexivity rhs_last;
  add.congruence rhs_last (a*sum liat) rhs_last (sum rhs_liat);
  eq.transitivity (a*sum s) (rhs_last + a*sum liat) (rhs_last + sum rhs_liat) 

let rec foldm_snoc_distributivity_right #c #eq (mul add: CE.cm c eq) (s: SB.seq c) (a: c)
  : Lemma (requires is_fully_distributive mul add /\ is_absorber add.unit mul) 
          (ensures mul.mult (SP.foldm_snoc add s) a `eq.eq`
                   SP.foldm_snoc add (seq_op_const mul s a))
          (decreases SB.length s) = 
  if SB.length s > 0 then 
  let ((+), ( * ), (=)) = add.mult, mul.mult, eq.eq in
  let sum s = SP.foldm_snoc add s in
  let liat, last = SProp.un_snoc s in
  let rhs_liat, rhs_last = SProp.un_snoc (seq_op_const mul s a) in
  foldm_snoc_distributivity_right mul add liat a; 
  SB.lemma_eq_elim rhs_liat (seq_op_const mul liat a);
  eq.reflexivity rhs_last;
  add.congruence rhs_last (sum liat*a) rhs_last (sum rhs_liat);
  eq.transitivity (sum s*a) (rhs_last + sum liat*a) (rhs_last + sum rhs_liat) 

let foldm_snoc_distributivity_right_eq #c #eq (mul add: CE.cm c eq) (s: SB.seq c) (a: c) (r: SB.seq c)
  : Lemma (requires is_fully_distributive mul add /\ is_absorber add.unit mul /\
                    SB.equal r (seq_op_const mul s a)) 
          (ensures mul.mult (SP.foldm_snoc add s) a `eq.eq`
                   SP.foldm_snoc add r)
  = foldm_snoc_distributivity_right mul add s a

let foldm_snoc_distributivity_left_eq #c #eq (mul add: CE.cm c eq) (a: c) (s: SB.seq c) (r: SB.seq c{SB.equal r (const_op_seq mul a s)})
  : Lemma (requires is_fully_distributive mul add /\ is_absorber add.unit mul) 
          (ensures (mul.mult a(SP.foldm_snoc add s)) `eq.eq`
                   SP.foldm_snoc add r)
  = foldm_snoc_distributivity_left mul add a s 
 
let matrix_mul_ijth #c #eq #m #n #k (add: CE.cm c eq) 
                    (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                    (mx: matrix c m n) (my: matrix c n k) (i: under m) (h: under k)
  : Lemma (ijth (matrix_mul add mul mx my) i h == dot add mul (row mx i) (col my h)) = ()

let matrix_mul_ijth_as_sum #c #eq #m #n #p (add: CE.cm c eq) 
                    (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                    (mx: matrix c m n) (my: matrix c n p) (i: under m) (k: under p)
  : Lemma (ijth (matrix_mul add mul mx my) i k == 
           SP.foldm_snoc add (SB.init n (fun (j: under n) -> mul.mult (ijth mx i j) (ijth my j k)))) =
  let r = SB.init n (fun (j: under n) -> mul.mult (ijth mx i j) (ijth my j k)) in
  assert (ijth (matrix_mul add mul mx my) i k == 
          SP.foldm_snoc add (seq_of_products mul (row mx i) (col my k)));
  seq_of_products_lemma mul (row mx i) (col my k) r

let matrix_mul_ijth_eq_sum_of_seq #c #eq #m #n #p (add: CE.cm c eq) 
                                  (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                                  (mx: matrix c m n) (my: matrix c n p) (i: under m) (k: under p)
                                  (r: SB.seq c{r `SB.equal` seq_of_products mul (row mx i) (col my k)})
  : Lemma (ijth (matrix_mul add mul mx my) i k == SP.foldm_snoc add r) = ()

let rec foldm_snoc_of_equal_inits #c #eq (#m: pos) (cm: CE.cm c eq) (f: (under m) -> c) (g: (under m) -> c)
  : Lemma (requires  (forall (i: under m). f i `eq.eq` g i))
          (ensures SP.foldm_snoc cm (SB.init m f) `eq.eq` SP.foldm_snoc cm (SB.init m g)) = 
  if m=0 then () else 
  if m=1 then begin
    SP.foldm_snoc_singleton cm (f 0);
    SP.foldm_snoc_singleton cm (g 0);
    eq.transitivity (SP.foldm_snoc cm (SB.init m f)) (f 0) (g 0);
    eq.symmetry (SP.foldm_snoc cm (SB.init m g)) (g 0);
    eq.transitivity (SP.foldm_snoc cm (SB.init m f)) (g 0) (SP.foldm_snoc cm (SB.init m g))
  end else
  let fliat, flast = SProp.un_snoc (SB.init m f) in
  let gliat, glast = SProp.un_snoc (SB.init m g) in  
  foldm_snoc_of_equal_inits cm (fun (i: under (m-1)) -> f i) (fun (i: under (m-1)) -> g i);
  SB.lemma_eq_elim (SB.init (m-1) (fun (i: under (m-1)) -> f i)) fliat;
  SB.lemma_eq_elim (SB.init (m-1) (fun (i: under (m-1)) -> g i)) gliat;
  cm.congruence flast (SP.foldm_snoc cm fliat)
                glast (SP.foldm_snoc cm gliat)

let double_foldm_snoc_transpose_lemma #c #eq (#m #n: pos) (cm: CE.cm c eq) (f: under m -> under n -> c)
  : Lemma (SP.foldm_snoc cm (SB.init m (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j)))) `eq.eq`
           SP.foldm_snoc cm (SB.init n (fun (j: under n) -> SP.foldm_snoc cm (SB.init m (fun (i: under m) -> f i j))))) = 
  Classical.forall_intro_2 (Classical.move_requires_2 eq.symmetry);
  let gen : matrix_generator c m n = f in  
  let mx = init gen in 
  let mx_seq = matrix_seq gen in
  matrix_fold_equals_fold_of_seq_folds cm gen; 
  let aux (i: under m) : Lemma (SB.init n (gen i) == SB.init n (fun (j: under n) -> f i j))
    = SB.lemma_eq_elim (SB.init n (gen i))(SB.init n (fun (j: under n) -> f i j)) 
    in Classical.forall_intro aux;  
  SB.lemma_eq_elim (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (gen i))))
                   (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j))));      
  SB.lemma_eq_elim (SB.init m (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j))))
                   (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j))));                   
  matrix_transpose_is_permutation gen;
  matrix_fold_equals_fold_of_transpose cm gen;
  let trans_gen = transposed_matrix_gen gen in
  let mx_trans = init trans_gen in
  let mx_trans_seq = matrix_seq trans_gen in
  matrix_fold_equals_fold_of_seq_folds cm trans_gen;
  assert (foldm cm mx_trans `eq.eq` 
          SP.foldm_snoc cm (SB.init n (fun j -> SP.foldm_snoc cm (SB.init m (trans_gen j)))));
  let aux_tr_lemma (j: under n) 
    : Lemma ((SB.init m (trans_gen j)) == (SB.init m (fun (i: under m) -> f i j))) 
    = SB.lemma_eq_elim (SB.init m (trans_gen j)) (SB.init m (fun (i: under m) -> f i j)) 
    in Classical.forall_intro aux_tr_lemma;
  SB.lemma_eq_elim (SB.init n (fun j -> SP.foldm_snoc cm (SB.init m (trans_gen j))))
                   (SB.init n (fun (j:under n) -> SP.foldm_snoc cm (SB.init m (fun (i: under m) -> f i j))));
  assert (foldm cm mx_trans `eq.eq` 
          SP.foldm_snoc cm (SB.init n (fun (j:under n) -> SP.foldm_snoc cm (SB.init m (fun (i: under m) -> f i j)))));
  eq.transitivity (SP.foldm_snoc cm (SB.init m (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j)))))
                  (foldm cm mx)
                  (foldm cm mx_trans);
  eq.transitivity (SP.foldm_snoc cm (SB.init m (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j)))))
                  (foldm cm mx_trans)
                  (SP.foldm_snoc cm (SB.init n (fun (j:under n) -> SP.foldm_snoc cm (SB.init m (fun (i: under m) -> f i j)))))

let matrix_mul_ijth_eq_sum_of_seq_for_init #c #eq #m #n #p (add: CE.cm c eq) 
  (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
  (mx: matrix c m n) (my: matrix c n p) (i: under m) (k: under p)
  (f: (under n)->c { SB.init n f `SB.equal` seq_of_products mul (row mx i) (col my k)})
  : Lemma (ijth (matrix_mul add mul mx my) i k == SP.foldm_snoc add (SB.init n f)) = ()

let double_foldm_snoc_of_equal_generators #c #eq (#m #n: pos) (cm: CE.cm c eq) (f g: under m -> under n -> c)
  : Lemma (requires (forall (i: under m) (j: under n). f i j `eq.eq` g i j))
          (ensures SP.foldm_snoc cm (SB.init m (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j))))
          `eq.eq`  SP.foldm_snoc cm (SB.init m (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> g i j))))) = 
  let aux (i: under m) : Lemma (SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j)) `eq.eq`
                                SP.foldm_snoc cm (SB.init n (fun (j: under n) -> g i j))) 
    = foldm_snoc_of_equal_inits cm (fun (j:under n) -> f i j) (fun (j:under n) -> g i j) in
  Classical.forall_intro aux;
  foldm_snoc_of_equal_inits cm (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j)))
                               (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> g i j)))

#push-options "--z3rlimit 10 --ifuel 0 --fuel 0"  
let matrix_mul_is_associative #c #eq #m #n #p #q (add: CE.cm c eq) 
                    (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                    (mx: matrix c m n) (my: matrix c n p) (mz: matrix c p q)
  : Lemma (matrix_eq_fun eq ((matrix_mul add mul mx my) `matrix_mul add mul` mz)
                            (matrix_mul add mul mx (matrix_mul add mul my mz))) =  
  let rhs = mx `matrix_mul add mul` (my `matrix_mul add mul` mz) in
  let lhs = (mx `matrix_mul add mul` my) `matrix_mul add mul` mz in
  let mxy = matrix_mul add mul mx my in
  let myz = matrix_mul add mul my mz in
  let ((+), ( * ), (=)) = add.mult, mul.mult, eq.eq in 
  let aux (i: under m) (l: under q) : Lemma (ijth lhs i l = ijth rhs i l) =
    let sum_j (f: under n -> c) = SP.foldm_snoc add (SB.init n f) in
    let sum_k (f: under p -> c) = SP.foldm_snoc add (SB.init p f) in 
    let xy_products_init (k: under p) (j: under n) = ijth mx i j * ijth my j k in
    let xy_cell_as_sum (k: under p) = sum_j (xy_products_init k) in    
    let xy_cell_lemma (k: under p) : Lemma (ijth mxy i k == xy_cell_as_sum k) = 
        matrix_mul_ijth_eq_sum_of_seq_for_init add mul mx my i k (xy_products_init k)
        in Classical.forall_intro xy_cell_lemma;  
    let xy_z_products_init (k: under p) = xy_cell_as_sum k * ijth mz k l in
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul mxy mz i l xy_z_products_init;
    let full_init_kj (k: under p) (j: under n) = (ijth mx i j * ijth my j k) * ijth mz k l in
    let full_init_jk (j: under n) (k: under p) = (ijth mx i j * ijth my j k) * ijth mz k l in 
    let full_init_rh (j: under n) (k: under p) = ijth mx i j * (ijth my j k * ijth mz k l) in
    let sum_jk (f: (under n -> under p -> c)) = sum_j (fun (j: under n) -> sum_k (fun (k: under p) -> f j k)) in
    let sum_kj (f: (under p -> under n -> c)) = sum_k (fun (k: under p) -> sum_j (fun (j: under n) -> f k j)) in
    let xy_z_distr (k: under p) : Lemma (((xy_cell_as_sum k) * (ijth mz k l)) = sum_j (full_init_kj k))
      = foldm_snoc_distributivity_right_eq mul add (SB.init n (xy_products_init k)) (ijth mz k l) 
                                                   (SB.init n (full_init_kj k)) 
      in Classical.forall_intro xy_z_distr;
    foldm_snoc_of_equal_inits add xy_z_products_init 
                                  (fun (k:under p) -> sum_j (full_init_kj k));  
    double_foldm_snoc_transpose_lemma add full_init_kj;
    eq.transitivity (ijth lhs i l) (sum_kj full_init_kj)
                                   (sum_jk full_init_jk);
    let aux_rh (j: under n) (k: under p) : Lemma (full_init_jk j k = full_init_rh j k)
      = mul.associativity (ijth mx i j) (ijth my j k) (ijth mz k l)
      in Classical.forall_intro_2 aux_rh;
    double_foldm_snoc_of_equal_generators add full_init_jk full_init_rh;
    eq.transitivity (ijth lhs i l) (sum_jk full_init_jk) (sum_jk full_init_rh); 
    
    // now expand the right hand side, fully dual to the first part of the lemma.
    let yz_products_init (j: under n) (k: under p) = ijth my j k * ijth mz k l in
    let yz_cell_as_sum (j: under n) = sum_k (yz_products_init j) in
    let x_yz_products_init (j: under n) = ijth mx i j * yz_cell_as_sum j in 
    let yz_cell_lemma (j: under n) : Lemma (ijth myz j l == sum_k (yz_products_init j)) = 
        matrix_mul_ijth_eq_sum_of_seq_for_init add mul my mz j l (yz_products_init j);
      () in Classical.forall_intro yz_cell_lemma; 
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul mx myz i l x_yz_products_init; 
    let x_yz_distr (j: under n) : Lemma (ijth mx i j * yz_cell_as_sum j = sum_k (full_init_rh j))  
      = foldm_snoc_distributivity_left_eq mul add (ijth mx i j) (SB.init p (yz_products_init j))   
                                                                (SB.init p (full_init_rh j)) 
      in Classical.forall_intro x_yz_distr;
    foldm_snoc_of_equal_inits add x_yz_products_init                                  
                                  (fun (j:under n) -> sum_k (full_init_rh j));  
    eq.symmetry (ijth rhs i l) (sum_jk full_init_rh);
    eq.transitivity (ijth lhs i l) (sum_jk full_init_rh) (ijth rhs i l);   
  () in Classical.forall_intro_2 aux;
  matrix_equiv_from_element_eq eq lhs rhs
     
let matrix_mul_unit #c #eq m (add: CE.cm c eq) 
                              (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
  : matrix c m m = init (fun i j -> if i=j then mul.unit else add.unit)
 
let absorber_lemma #c #eq (x:c) (z:c) (add: CE.cm c eq) 
                   (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul})
  : Lemma (requires eq.eq z add.unit) 
          (ensures mul.mult z x `eq.eq` add.unit) = 
  eq.reflexivity x; mul.congruence z x add.unit x;
  eq.transitivity (mul.mult z x) (mul.mult add.unit x) add.unit

let matrix_mul_unit_row_lemma #c #eq m (add mul: CE.cm c eq) (i: under m)
  : Lemma (requires is_fully_distributive mul add /\ is_absorber add.unit mul)
          (ensures (row (matrix_mul_unit m add mul) i 
                    == (SB.create i add.unit) `SB.append` 
                       ((SB.create 1 mul.unit) `SB.append` (SB.create (m-i-1) add.unit))) /\
                    row (matrix_mul_unit m add mul) i == 
                       ((SB.create i add.unit) `SB.append` (SB.create 1 mul.unit)) `SB.append`
                       (SB.create (m-i-1) add.unit)) =  
  SB.lemma_eq_elim ((SB.create i add.unit `SB.append` SB.create 1 mul.unit) 
                   `SB.append` (SB.create (m-i-1) add.unit))
                   (row (matrix_mul_unit m add mul) i); 
  SB.lemma_eq_elim ((SB.create i add.unit) `SB.append` 
                   (SB.create 1 mul.unit `SB.append` SB.create (m-i-1) add.unit))
                   (row (matrix_mul_unit m add mul) i)
                   
let matrix_mul_unit_col_lemma #c #eq m (add mul: CE.cm c eq) (i: under m)
  : Lemma (requires is_fully_distributive mul add /\ is_absorber add.unit mul)
          (ensures (col (matrix_mul_unit m add mul) i 
                    == (SB.create i add.unit) `SB.append` 
                       ((SB.create 1 mul.unit) `SB.append` (SB.create (m-i-1) add.unit))) /\
                    col (matrix_mul_unit m add mul) i == 
                       ((SB.create i add.unit) `SB.append` (SB.create 1 mul.unit)) `SB.append`
                       (SB.create (m-i-1) add.unit)) =  
  SB.lemma_eq_elim ((SB.create i add.unit `SB.append` SB.create 1 mul.unit) 
                   `SB.append` (SB.create (m-i-1) add.unit))
                   (col (matrix_mul_unit m add mul) i); 
  SB.lemma_eq_elim ((SB.create i add.unit) `SB.append` 
                   (SB.create 1 mul.unit `SB.append` SB.create (m-i-1) add.unit))
                   (col (matrix_mul_unit m add mul) i)

#restart-solver
let seq_of_products_zeroes_lemma #c #eq #m (mul: CE.cm c eq) (z: c{is_absorber z mul})
                                 (s: SB.seq c{SB.length s == m})
  : Lemma (ensures (eq_of_seq eq (seq_of_products mul (SB.create m z) s) (SB.create m z))) 
  = eq_of_seq_from_element_equality eq (seq_of_products mul (SB.create m z) s) (SB.create m z) 

let rec foldm_snoc_zero_lemma #c #eq (add: CE.cm c eq) (zeroes: SB.seq c)
  : Lemma (requires (forall (i: under (SB.length zeroes)). SB.index zeroes i `eq.eq` add.unit))
          (ensures eq.eq (SP.foldm_snoc add zeroes) add.unit) 
          (decreases SB.length zeroes) =
  if (SB.length zeroes < 1) then begin
    assert_norm (SP.foldm_snoc add zeroes == add.unit);
    eq.reflexivity add.unit    
  end else
  let liat, last = SProp.un_snoc zeroes in
  foldm_snoc_zero_lemma add liat;
  add.congruence last (SP.foldm_snoc add liat) add.unit add.unit;
  add.identity add.unit;
  foldm_snoc_last add zeroes;
  eq.transitivity (SP.foldm_snoc add zeroes)                                
                  (add.mult add.unit add.unit)
                  add.unit
   

(* right identity will soon get a fully similar proof *)
#push-options "--z3rlimit 20 --fuel 1 --ifuel 0"
#restart-solver
let matrix_mul_right_identity #c #eq #m (add: CE.cm c eq) 
                              (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                              (mx: matrix c m m)
  : Lemma (matrix_mul add mul mx (matrix_mul_unit m add mul) `matrix_eq_fun eq` mx) =   
  let unit = matrix_mul_unit m add mul in
  let mxu = matrix_mul add mul mx unit in
  let ( * ) = mul.mult in
  let ( $=$ ) = eq.eq in
  let aux (i j: under m) : Lemma (ijth mxu i j $=$ ijth mx i j) = 
    let gen = fun (k: under m) -> ijth mx i k * ijth unit k j in
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul mx unit i j gen;
    let seq = SB.init m gen in       
    let rec seq_sum_is_item (k:under (m+1)) 
      : Lemma (ensures SP.foldm_snoc add (SB.init k gen) `eq.eq`
                       (if k>j then ijth mx i j else add.unit))
              (decreases k) = 
      if k=0 then eq.reflexivity add.unit
      else if k<(j+1) then begin
        let full = SB.init k gen in
        let liat,last = SProp.un_snoc full in
        seq_sum_is_item (k-1);
        SB.lemma_eq_elim (liat) ((SB.init (k-1) gen));
        eq.reflexivity (SP.foldm_snoc add liat);
        mul.congruence last (SP.foldm_snoc add liat) add.unit (SP.foldm_snoc add liat);
        eq.transitivity (last * SP.foldm_snoc add liat)
                        (add.unit * SP.foldm_snoc add liat)
                        (add.unit);
        add.congruence last (SP.foldm_snoc add liat) add.unit add.unit;
        add.identity add.unit;
        eq.transitivity (SP.foldm_snoc add full)
                        (add.mult add.unit add.unit)
                        add.unit 
      end else if k=(j+1) then begin
        let full = SB.init k gen in
        let liat,last = SProp.un_snoc full in
        seq_sum_is_item j;
        SB.lemma_eq_elim (liat) ((SB.init (k-1) gen));
        mul.identity (ijth mx i j);
        eq.reflexivity last; 
        add.congruence last (SP.foldm_snoc add liat) last add.unit;
        add.identity last;
        add.commutativity last add.unit;
        mul.commutativity (ijth mx i j) mul.unit;
        eq.transitivity (add.mult last add.unit) (add.mult add.unit last) last;
        eq.transitivity (SP.foldm_snoc add full) (add.mult last add.unit) last;                         
        eq.transitivity last (mul.unit * ijth mx i j) (ijth mx i j);
        eq.transitivity (SP.foldm_snoc add full) last (ijth mx i j)
      end else begin
        let full = SB.init k gen in
        seq_sum_is_item (k-1);
        let liat,last = SProp.un_snoc full in
        let subgen (i: under (k)) = gen i in
        SB.lemma_eq_elim liat (SB.init (k-1) gen); 
        add.identity add.unit;
        mul.commutativity (ijth mx i (k-1)) add.unit;
        eq.transitivity last (add.unit * ijth mx i (k-1)) add.unit;
        eq.reflexivity (SP.foldm_snoc add (SB.init (k-1) gen));
        add.congruence last (SP.foldm_snoc add (SB.init (k-1) gen)) 
                   add.unit (SP.foldm_snoc add (SB.init (k-1) gen));
        add.identity (SP.foldm_snoc add (SB.init (k-1) gen));
        eq.transitivity (SP.foldm_snoc add full)
                        (add.mult add.unit (SP.foldm_snoc add (SB.init (k-1) gen)))
                        (SP.foldm_snoc add (SB.init (k-1) gen));
        eq.transitivity (SP.foldm_snoc add full)
                        (SP.foldm_snoc add (SB.init (k-1) gen))
                        (ijth mx i j) 
      end in seq_sum_is_item m
    in Classical.forall_intro_2 aux;
  matrix_equiv_from_element_eq eq mxu mx 
  
let matrix_mul_left_identity #c #eq #m (add: CE.cm c eq) 
                              (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                              (mx: matrix c m m)
  : Lemma (matrix_mul add mul (matrix_mul_unit m add mul) mx `matrix_eq_fun eq` mx) =   
  let unit = matrix_mul_unit m add mul in
  let mxu = matrix_mul add mul unit mx in
  let ( * ) = mul.mult in
  let ( $=$ ) = eq.eq in
  let aux (i j: under m) : Lemma (ijth mxu i j $=$ ijth mx i j) = 
    let gen (k: under m) = ijth unit i k * ijth mx k j in
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul unit mx i j gen;
    let seq = SB.init m gen in       
    let rec seq_sum_is_item (k:under (m+1)) 
      : Lemma (ensures SP.foldm_snoc add (SB.init k gen) `eq.eq`
                       (if k>i then ijth mx i j else add.unit))
              (decreases k) = 
      if k=0 then (eq.reflexivity add.unit)
      else if k<(i+1) then begin
        let full = SB.init k gen in
        let liat,last = SProp.un_snoc full in        
        seq_sum_is_item (k-1);
        SB.lemma_eq_elim (liat) ((SB.init (k-1) gen));
        eq.reflexivity (SP.foldm_snoc add liat);
        mul.congruence last (SP.foldm_snoc add liat) add.unit (SP.foldm_snoc add liat);
        eq.transitivity (last * SP.foldm_snoc add liat)
                        (add.unit * SP.foldm_snoc add liat)
                        (add.unit);
        add.congruence last (SP.foldm_snoc add liat) add.unit add.unit;
        add.identity add.unit;
        eq.transitivity (SP.foldm_snoc add full)
                        (add.mult add.unit add.unit)
                        add.unit 
      end else if k=(i+1) then begin 
        let full = SB.init k gen in
        let liat,last = SProp.un_snoc full in
        seq_sum_is_item i;
        SB.lemma_eq_elim (liat) ((SB.init (k-1) gen));
        mul.identity (ijth mx i j);
        eq.reflexivity last; 
        add.congruence last (SP.foldm_snoc add liat) last add.unit;
        add.identity last;
        add.commutativity last add.unit;
        mul.commutativity (ijth mx i j) mul.unit;
        eq.transitivity (add.mult last add.unit) (add.mult add.unit last) last;
        eq.transitivity (SP.foldm_snoc add full) (add.mult last add.unit) last;                         
        eq.transitivity last (mul.unit * ijth mx i j) (ijth mx i j); 
        eq.transitivity (SP.foldm_snoc add full) last (ijth mx i j)
      end else begin
        let full = SB.init k gen in
        seq_sum_is_item (k-1);
        let liat,last = SProp.un_snoc full in
        SB.lemma_eq_elim liat (SB.init (k-1) gen); 
        add.identity add.unit;
        mul.commutativity (ijth mx i (k-1)) add.unit;
        eq.reflexivity (SP.foldm_snoc add (SB.init (k-1) gen));
        add.congruence last (SP.foldm_snoc add (SB.init (k-1) gen)) 
                   add.unit (SP.foldm_snoc add (SB.init (k-1) gen));
        add.identity (SP.foldm_snoc add (SB.init (k-1) gen));
        eq.transitivity (SP.foldm_snoc add full)
                        (add.mult add.unit (SP.foldm_snoc add (SB.init (k-1) gen)))
                        (SP.foldm_snoc add (SB.init (k-1) gen));
        eq.transitivity (SP.foldm_snoc add full)
                        (SP.foldm_snoc add (SB.init (k-1) gen))
                        (ijth mx i j) 
      end in seq_sum_is_item m
    in Classical.forall_intro_2 aux;
  matrix_equiv_from_element_eq eq mxu mx
#pop-options    
 
let matrix_mul_identity #c #eq #m (add: CE.cm c eq) 
                              (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                              (mx: matrix c m m)
  : Lemma (matrix_mul add mul mx (matrix_mul_unit m add mul) `matrix_eq_fun eq` mx /\
           matrix_mul add mul (matrix_mul_unit m add mul) mx `matrix_eq_fun eq` mx) =
  matrix_mul_left_identity add mul mx;
  matrix_mul_right_identity add mul mx

let eq_of_seq_unsnoc #c (eq:CE.equiv c) (m:pos) (s1 s2: (z:SB.seq c{SB.length z==m}))
  : Lemma (requires eq_of_seq eq s1 s2)
          (ensures eq.eq (snd (SProp.un_snoc s1)) (snd (SProp.un_snoc s2)) /\
                   eq_of_seq eq (fst (SProp.un_snoc s1)) (fst (SProp.un_snoc s2))) =
  eq_of_seq_element_equality eq s1 s2;
  eq_of_seq_from_element_equality eq (fst (SProp.un_snoc s1)) (fst (SProp.un_snoc s2))

let rec foldm_snoc_equality #c #eq (add: CE.cm c eq) (s t: SB.seq c)
  : Lemma (requires SB.length s == SB.length t /\ eq_of_seq eq s t)
          (ensures SP.foldm_snoc add s `eq.eq` SP.foldm_snoc add t)
          (decreases SB.length s) = 
  if SB.length s = 0 then (
    assert_norm (SP.foldm_snoc add s == add.unit);
    assert_norm (SP.foldm_snoc add t == add.unit);
    eq.reflexivity add.unit
  ) 
  else (
    let sliat, slast = SProp.un_snoc s in
    let tliat, tlast = SProp.un_snoc t in
    eq_of_seq_unsnoc eq (SB.length s) s t;
    foldm_snoc_equality add sliat tliat;
    foldm_snoc_last add s;
    foldm_snoc_last add t; 
    add.congruence slast (SP.foldm_snoc add sliat)
                   tlast (SP.foldm_snoc add tliat) 
  )

let dot_of_equal_sequences #c #eq (m:pos)
                                  (add: CE.cm c eq) 
                                  (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                                  (p q r s: (z:SB.seq c{SB.length z == m}))
  : Lemma (requires eq_of_seq eq p r /\ eq_of_seq eq q s) 
          (ensures eq.eq (dot add mul p q) (dot add mul r s)) = 
  eq_of_seq_element_equality eq p r;
  eq_of_seq_element_equality eq q s;
  let aux (i: (under (SB.length p))) : Lemma (SB.index (seq_of_products mul p q) i `eq.eq`
                                              SB.index (seq_of_products mul r s) i)
    = mul.congruence (SB.index p i) (SB.index q i) (SB.index r i) (SB.index s i);
    ()
    in Classical.forall_intro aux;  
  eq_of_seq_from_element_equality eq (seq_of_products mul p q) (seq_of_products mul r s);
  foldm_snoc_equality add  (seq_of_products mul p q) (seq_of_products mul r s)  

let matrix_mul_congruence #c #eq #m #n #p (add: CE.cm c eq) 
                    (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                    (mx: matrix c m n) (my: matrix c n p) 
                    (mz: matrix c m n) (mw: matrix c n p)
  : Lemma (requires matrix_eq_fun eq mx mz /\ matrix_eq_fun eq my mw)
          (ensures matrix_eq_fun eq (matrix_mul add mul mx my) (matrix_mul add mul mz mw)) =  
  let aux (i: under m) (k: under p) : squash (ijth (matrix_mul add mul mx my) i k 
                                      `eq.eq` ijth (matrix_mul add mul mz mw) i k) = 
    let init_xy (j: under n) = mul.mult (ijth mx i j) (ijth my j k) in
    let init_zw (j: under n) = mul.mult (ijth mz i j) (ijth mw j k) in
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul mx my i k init_xy;
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul mz mw i k init_zw; 
    let sp_xy = SB.init n init_xy in
    let sp_zw = SB.init n init_zw in
    let all_eq (j: under n) : Lemma (init_xy j `eq.eq` init_zw j)   
      = matrix_equiv_ijth eq mx mz i j;
        matrix_equiv_ijth eq my mw j k;
        mul.congruence (ijth mx i j) (ijth my j k) (ijth mz i j) (ijth mw j k) 
    in Classical.forall_intro all_eq;      
    eq_of_seq_from_element_equality eq sp_xy sp_zw;
    foldm_snoc_equality add sp_xy sp_zw
  in matrix_equiv_from_proof eq (matrix_mul add mul mx my) (matrix_mul add mul mz mw) aux
