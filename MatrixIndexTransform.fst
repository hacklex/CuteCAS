module MatrixIndexTransform

open FStar.Math.Lemmas

/// This module describes the transform that would return the index of an element
/// in a flattened M*N matrix after its transposition.
///
/// For example, suppose we are interested in an element [1,3] of a matrix A of size 3*5.
/// For the original matrix A, the flattened index is 1*5+3 = 8.
/// For the transposed matrix A^T, sized 5*3, the flattened index is 3*3+1 = 10.

/// We refine multiplication a bit to make proofs smoothier
unfold let ( *) (x y: int) : (t:int{(x>0 /\ y>0) ==> t>0}) = op_Multiply x y

/// A shortcut for bounded positive integers.
type under (k: pos) = x:nat{x<k}

/// This is a simple arithmetic fact, but the prover needs a slight nudge in the right direction.
/// By having it in a separate lemma, we stabilize the proofs of bigger lemmas using it.
let flattened_index_is_under_flattened_size (m n: pos) (i: under m) (j: under n) 
  : Lemma ((((i*n)+j)) < m*n) = assert (i*n <= (m-1)*n)

/// Returns the flattened index from 2D indices pair and the two array dimensions.
let get_ij (m n: pos) (i:under m) (j: under n) : under (m*n) = flattened_index_is_under_flattened_size m n i j; i*n + j

/// Returns the first matrix index from the flattened index and the two dimensions
let get_i (m n: pos) (ij: under (m*n)) : under m = ij / n
/// Returns the second matrix index from the flattened index and the two dimensions
let get_j (m n: pos) (ij: under (m*n)) : under n = ij % n

/// A proof that getting a 2D index back from the flattened index works correctly
let consistency_of_i_j (m n: pos) (i: under m) (j: under n) : Lemma (
  get_i m n (get_ij m n i j) = i /\ get_j m n (get_ij m n i j) = j) = 
  flattened_index_is_under_flattened_size m n i j;
  lemma_div_plus j i n;
  lemma_mod_plus j i n

/// A proof that getting the flattened index from 2D indices works correctly
let consistency_of_ij (m n: pos) (ij: under (m*n)) : Lemma (get_ij m n (get_i m n ij) (get_j m n ij) == ij) = ()

/// The transposition transform for the flattened index
let transpose_ji (m n: pos) (ij: under (m*n)) : under (n*m) 
  =  
  flattened_index_is_under_flattened_size n m (get_j m n ij) (get_i m n ij);
  (get_j m n ij)*m + (get_i m n ij)
 
/// Auxiliary arithmetic lemmas
let lemma_jm_plus_i_mod_m (m: pos) (i: under m) (j: nat) : Lemma ((j*m+i)%m = i) = lemma_mod_plus i j m
let lemma_jm_plus_i_div_m (m: pos) (i: under m) (j: nat) : Lemma ((j*m+i)/m = j) = lemma_mod_plus i j m

/// A proof of trasnspotition transform bijectivity
let ji_is_transpose_of_ij (m n: pos) (ij: under (m*n)) : Lemma (transpose_ji n m (transpose_ji m n ij) = ij) = 
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
    ((j*m + i) %m)*n + ((j*m + i)/m);  ={ lemma_jm_plus_i_div_m m i j; lemma_jm_plus_i_mod_m m i j }
    i*n + j;
  }

/// A proof that 2D indices are swapped with the transpotition transform 
#push-options "--z3cliopt 'smt.arith.nl=false'"
let dual_indices (m n: pos) (ij: under (m*n)) : Lemma (
     (get_j n m (transpose_ji m n ij) = get_i m n ij) /\
     (get_i n m (transpose_ji m n ij) = get_j m n ij)
 ) = 
    let i = get_i m n ij in
    let j = get_j m n ij in
    let ji = transpose_ji m n ij in
    consistency_of_ij m n ij;
    assert (i*n+j == ij); 
    calc (=) {
      get_j n m (transpose_ji m n ij); 
      == {} 
      ji % m;
      = {}
      (j*m+i)%m;
      = { lemma_jm_plus_i_mod_m m i j }
      i;      
    }; 
    consistency_of_ij n m ji;
    calc (=) {
      get_i n m (transpose_ji m n ij); 
      = {}
      get_i n m ji;
      = {}      
      ((get_j m n ij)*m + (get_i m n ij)) / m;
      = { lemma_jm_plus_i_div_m m i j  }    
      j;
    }  
#pop-options

