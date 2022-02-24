(*
   Copyright 2008-2018 Microsoft Research
   
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

module FStar.Seq.Matrix

open FStar.Algebra.CommMonoid.Equiv
open FStar.Math.Lemmas
open FStar.Seq.Properties
open FStar.Seq.Permutation
open FStar.Seq.Base

(* Here we provide tools to treat a seq of length m*n as a 2D matrix
   We also prove lemmas about folding such seqs, as well as lemmas
   about treating such seqs as folds of functions over int ranges *)
 
(* We refine multiplication a bit to make proofs smoothier *)
let ( *) (x y: int) : (t:int{(x>0 /\ y>0) ==> t>0}) = op_Multiply x y

// A shortcut for bounded positive integers.
type under (k: pos) = x:nat{x<k}
type not_less_than (x: int) = (t: int{t>=x})
type inbetween (x: int) (y: not_less_than x) = (t: int{t>=x && t<=y})
type counter_of_range (x: int) (y: not_less_than x) = (t: nat{t<(y+1-x)})

let range_count (x: int) (y: not_less_than x) : pos = (y+1)-x

(* 
   This lemma, especially when used with forall_intro, helps the prover verify
   the index ranges of sequences that correspond to arbitrary big_sums
*)
let bounds_lemma (n0:int) (nk: not_less_than n0) (i: counter_of_range n0 nk) 
  : Lemma (n0+i >= n0 /\ n0+i <= nk) = ()
  
(* 
   This is a simple arithmetic fact, but the prover needs a slight
   nudge in the right direction. By having it in a separate lemma, 
   we stabilize the proofs of bigger lemmas using it.
*)
let flattened_index_is_under_flattened_size (m n: pos) (i: under m) (j: under n) 
  : Lemma ((((i*n)+j)) < m*n) = assert (i*n <= (m-1)*n)
  
(* 
   Returns the flattened index from 2D indices pair 
   and the two array dimensions.
*)
let get_ij (m n: pos) (i:under m) (j: under n) : under (m*n) 
  = flattened_index_is_under_flattened_size m n i j; i*n + j
  
(* 
   The following two functions return the matrix indices from the 
   flattened index and the two dimensions
*)
let get_i (m n: pos) (ij: under (m*n)) : under m = ij / n
let get_j (m n: pos) (ij: under (m*n)) : under n = ij % n


// A proof that getting a 2D index back from the flattened index works correctly
let consistency_of_i_j (m n: pos) (i: under m) (j: under n) 
  : Lemma (get_i m n (get_ij m n i j) = i /\ get_j m n (get_ij m n i j) = j) = 
  flattened_index_is_under_flattened_size m n i j;
  lemma_div_plus j i n;
  lemma_mod_plus j i n
  
// A proof that getting the flattened index from 2D indices works correctly
let consistency_of_ij (m n: pos) (ij: under (m*n)) 
  : Lemma (get_ij m n (get_i m n ij) (get_j m n ij) == ij) = ()

// The transposition transform for the flattened index
let transpose_ji (m n: pos) (ij: under (m*n)) : under (n*m) =  
  flattened_index_is_under_flattened_size n m (get_j m n ij) (get_i m n ij);
  (get_j m n ij)*m + (get_i m n ij)

// Auxiliary arithmetic lemma
let lemma_indices_transpose (m: pos) (i: under m) (j: nat) 
  : Lemma (((j*m+i)%m=i) && ((j*m+i)/m=j)) = lemma_mod_plus i j m
 
// A proof of trasnspotition transform bijectivity
let ji_is_transpose_of_ij (m n: pos) (ij: under (m*n)) 
  : Lemma (transpose_ji n m (transpose_ji m n ij) = ij) = 
  let i = get_i m n ij in
  let j = get_j m n ij in
  let ji = j*m + i in
  flattened_index_is_under_flattened_size m n i j;
  flattened_index_is_under_flattened_size n m j i;
  flattened_index_is_under_flattened_size n m (get_j m n ij) (get_i m n ij);
  let gji = transpose_ji n m ji in
  calc (=) {
    transpose_ji n m (transpose_ji m n ij); ={}
    transpose_ji n m ji; ={}
    (ji % m)*n + (ji / m); ={}
    ((j*m + i) %m)*n + ((j*m + i)/m); ={ lemma_indices_transpose m i j }
    i*n + j;
  }

// A proof that 2D indices are swapped with the transpotition transform  
let dual_indices (m n: pos) (ij: under (m*n)) : Lemma (
     (get_j n m (transpose_ji m n ij) = get_i m n ij) /\
     (get_i n m (transpose_ji m n ij) = get_j m n ij)) 
  = consistency_of_ij m n ij;
    lemma_indices_transpose m (get_i m n ij) (get_j m n ij)  

type comm_monoid c eq = Algebra.CommMonoid.Equiv.cm c eq 

