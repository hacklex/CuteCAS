module Core.Matrix

(*
  Square matrices over a generic coefficient type, represented as
  functions `i: fin n -> j: fin n -> t`.
  
  Public interface is in Core.Matrix.fsti. This file provides:
  - Private equality infrastructure (matrix bool equality)
  - Proofs for all val declarations in the .fsti
*)

module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Combinators
open Core.Algebra.Notation
open Core.Algebra.Helpers
open Core.FinSum
open Core.Permutation
open Core.Vector

(* ----------------------------------------------------------------- *)
(*  Private: matrix equality infrastructure                          *)
(* ----------------------------------------------------------------- *)

private let matrix_row_eq (#t: Type) {| equatable t |} #n (a b: square_matrix t n) (i: fin n) 
  : bool = vector_eq (row a i) (row b i)
 
private let matrix_col_eq (#t: Type) {| equatable t |} #n (a b: square_matrix t n) (j: fin n)
  : bool = vector_eq (col a j) (col b j)

private let matrix_eq_prop_rowwise (#t: Type) {| equatable t |} #n (a b: square_matrix t n)
  : prop = forall (i: fin n). matrix_row_eq a b i

private let matrix_eq_prop_colwise (#t: Type) {| equatable t |} #n (a b: square_matrix t n)
  : prop = forall (j: fin n). matrix_col_eq a b j
   
private let matrix_eq_pointwise_iff_eq_rowwise (#t: Type) {| equatable t |} #n (a b: square_matrix t n)
  : Lemma (ensures matrix_eq a b <==> matrix_eq_prop_rowwise a b)
          = Classical.forall_intro (fun i -> vector_eq_iff_prop (row a i) (row b i))

private let matrix_eq_colwise_to_eq_pointwise (#t: Type) {| eq: equatable t |} #n (a b: square_matrix t n) 
  : Lemma (requires matrix_eq_prop_colwise a b) (ensures matrix_eq a b)
    = let aux (i j: fin n) : Lemma (a i j = b i j) =
        vector_eq_iff_prop (col a j) (col b j);
         assert (col a j i == a i j)
      in Classical.forall_intro_2 aux

private let matrix_eq_pointwise_to_colwise (#t: Type) {| eq: equatable t |} #n (a b: square_matrix t n) 
  : Lemma (requires matrix_eq a b) (ensures matrix_eq_prop_colwise a b)
    = let aux (j: fin n) : Lemma (matrix_col_eq a b j) =
       vector_eq_iff_prop (col a j) (col b j)
      in Classical.forall_intro aux

private let matrix_eq_colwise_iff_eq_pointwise (#t: Type) {| eq: equatable t |} #n (a b: square_matrix t n) 
  : Lemma (matrix_eq_prop_colwise a b <==> matrix_eq a b) = 
  Classical.move_requires_2 matrix_eq_colwise_to_eq_pointwise a b; 
  Classical.move_requires_2 matrix_eq_pointwise_to_colwise a b

private let rec matrix_rows_eq_from (#t: Type) {| equatable t |} #n (a b: square_matrix t n) (i: fin n)
  : Tot bool (decreases (n - i)) = 
  if i = (n-1) then matrix_row_eq a b i else matrix_row_eq a b i && matrix_rows_eq_from a b (succ i)

private let rec matrix_cols_eq_from (#t: Type) {| equatable t |} #n (a b: square_matrix t n) (j: fin n)
  : Tot bool (decreases (n - j)) = 
  if j = (n-1) then matrix_col_eq a b j else matrix_col_eq a b j && matrix_cols_eq_from a b (succ j)
 
private let matrix_eq_by_rows (#t: Type) {| equatable t |} #n (a b: square_matrix t n)
  : bool = matrix_rows_eq_from a b 0

private let matrix_eq_by_cols (#t: Type) {| equatable t |} #n (a b: square_matrix t n)
  : bool = matrix_cols_eq_from a b 0

private let matrix_eq_by_rows_to_prop (#t: Type) {| equatable t |} #n (a b: square_matrix t n)
  : Lemma (requires matrix_eq_by_rows a b) (ensures matrix_eq_prop_rowwise a b) (decreases n) = 
  let rec aux (#t: Type) {| equatable t |} #n (a b: square_matrix t n) (from: fin n)
    : Lemma (requires matrix_rows_eq_from a b from) 
            (ensures forall (i: fin n{i >= from}). matrix_row_eq a b i) 
            (decreases (n - from))= 
    if from < n-1 then begin
      assert (matrix_row_eq a b from);
      aux a b (succ from)
    end else () in
  aux a b 0
 
private let matrix_eq_by_cols_to_prop (#t: Type) {| equatable t |} #n (a b: square_matrix t n)
  : Lemma (requires matrix_eq_by_cols a b) (ensures matrix_eq_prop_colwise a b) (decreases n) =
  let rec aux (#t: Type) {| equatable t |} #n (a b: square_matrix t n) (from: fin n)
    : Lemma (requires matrix_cols_eq_from a b from) 
            (ensures forall (j: fin n{j >= from}). matrix_col_eq a b j) 
            (decreases (n - from))= 
    if from < n-1 then begin
      assert (matrix_col_eq a b from);
      aux a b (succ from)
    end else () in
  aux a b 0

private let matrix_eq_prop_rowwise_to_eq_by_rows (#t: Type) {| equatable t |} #n (a b: square_matrix t n)
  : Lemma (requires matrix_eq_prop_rowwise a b) (ensures matrix_eq_by_rows a b) (decreases n) = 
  let rec aux (#t: Type) {| equatable t |} #n (a b: square_matrix t n) (from: fin n)
    : Lemma (requires forall (i: fin n{i >= from}). matrix_row_eq a b i) 
            (ensures matrix_rows_eq_from a b from) 
            (decreases (n - from))= 
  if from < n-1 then begin
    assert (matrix_row_eq a b from);
    aux a b (succ from)
  end else () in
aux a b 0

private let matrix_eq_prop_colwise_to_eq_by_cols (#t: Type) {| equatable t |} #n (a b: square_matrix t n)
  : Lemma (requires matrix_eq_prop_colwise a b) (ensures matrix_eq_by_cols a b) (decreases n) = 
  let rec aux (#t: Type) {| equatable t |} #n (a b: square_matrix t n) (from: fin n)
    : Lemma (requires forall (j: fin n{j >= from}). matrix_col_eq a b j) 
            (ensures matrix_cols_eq_from a b from) 
            (decreases (n - from))= 
  if from < n-1 then begin
    assert (matrix_col_eq a b from);
    aux a b (succ from)
  end else () in
aux a b 0

private let matrix_eq_by_rows_iff_by_cols #t {| equatable t |} #n (a b: square_matrix t n)
  : Lemma ((matrix_eq_by_rows a b <==> matrix_eq_by_cols a b) /\ (matrix_eq_by_rows a b <==> matrix_eq a b)) = 
  Classical.move_requires_2 matrix_eq_by_rows_to_prop a b; 
  Classical.move_requires_2 matrix_eq_prop_rowwise_to_eq_by_rows a b;
  Classical.move_requires_2 matrix_eq_by_cols_to_prop a b; 
  Classical.move_requires_2 matrix_eq_prop_colwise_to_eq_by_cols a b;
  matrix_eq_pointwise_iff_eq_rowwise a b;
  matrix_eq_colwise_iff_eq_pointwise a b

(* ----------------------------------------------------------------- *)
(*  Propositional equality lemmas                                    *)
(* ----------------------------------------------------------------- *)

let matrix_eq_refl (#t: Type) {| equatable t |} #n (a: square_matrix t n) : Lemma (matrix_eq a a)
  = Classical.forall_intro (reflexivity #t)

let matrix_eq_sym (#t: Type) {| equatable t |} #n
                  (a b: square_matrix t n)
  : Lemma (matrix_eq a b <==> matrix_eq b a)
  = let aux (i j: fin n) : Lemma ((a i j = b i j) <==> (b i j = a i j)) = symmetry (a i j) (b i j) 
    in Classical.forall_intro_2 aux

let matrix_eq_trans (#t: Type) {| equatable t |} #n
                    (a b c: square_matrix t n)
  : Lemma (requires matrix_eq a b /\ matrix_eq b c) (ensures matrix_eq a c)
  = let aux (i j: fin n) : Lemma (a i j = c i j) = transitivity (a i j) (b i j) (c i j)   
    in Classical.forall_intro_2 aux

(* ----------------------------------------------------------------- *)
(*  Transpose lemmas                                                 *)
(* ----------------------------------------------------------------- *)

let transpose_involutive (#t: Type) {| equatable t |} #n
                         (a: square_matrix t n)
  : Lemma (matrix_eq (transpose (transpose a)) a)
  = matrix_eq_refl a

let transpose_transpose_reveal (#t: Type) {| equatable t |} #n
                         (a: square_matrix t n) (r c: fin n)
  : Lemma (transpose (transpose a) r c == a r c) = ()

(* ----------------------------------------------------------------- *)
(*  Identity matrix lemmas                                           *)
(* ----------------------------------------------------------------- *)

let id_matrix_diag (#t: Type) {| r: ring t |} #n (i: fin n) : Lemma (id_matrix #t #r #n i i == one) = ()

let id_matrix_off (#t: Type) {| r: ring t |} #n (i j: fin n)
  : Lemma (requires ~(i == j)) (ensures id_matrix #t i j == zero) = ()

(* ----------------------------------------------------------------- *)
(*  Addition lemma                                                   *)
(* ----------------------------------------------------------------- *)

let matrix_add_eq_at (#t: Type) {| add_comm_group t |} #n (a b: square_matrix t n) (i j: fin n)
  : Lemma (matrix_add a b i j == a i j + b i j) = ()

(* ----------------------------------------------------------------- *)
(*  Multiplication lemmas                                            *)
(* ----------------------------------------------------------------- *)

let matrix_mul_unfold #t {| r: ring t |} #n (a b: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a b i j == vector_dot (row a i) (col b j)) = ()

let matrix_mul_to_fin_sum (#t: Type) {| r: ring t |} #n (a b: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a b i j == fin_sum (pointwise_mul (row a i) (col b j)))
  = assert_norm (matrix_mul a b i j == fin_sum (pointwise_mul (row a i) (col b j)))

(* ----------------------------------------------------------------- *)
(*  Boolean matrix equality                                          *)
(* ----------------------------------------------------------------- *)

let matrix_eq_bool (#t: Type) {| equatable t |} #n
                   (a b: square_matrix t n) : bool
  = matrix_eq_by_rows a b 
   
let matrix_eq_bool_iff_pointwise
  (#t: Type) {| equatable t |} #n (a b: square_matrix t n)
  : Lemma (matrix_eq_bool a b <==> matrix_eq a b)
  = matrix_eq_by_rows_iff_by_cols a b 

let matrix_eq_bool_reflexivity
  (#t: Type) {| equatable t |} #n (a: square_matrix t n)
  : Lemma (matrix_eq_bool a a)
  = matrix_eq_refl a;
    matrix_eq_bool_iff_pointwise a a

let matrix_eq_bool_symmetry
  (#t: Type) {| equatable t |} #n (a b: square_matrix t n)
  : Lemma (matrix_eq_bool a b <==> matrix_eq_bool b a)
  = matrix_eq_bool_iff_pointwise a b;
    matrix_eq_bool_iff_pointwise b a;
    matrix_eq_sym a b

let matrix_eq_bool_transitivity
  (#t: Type) {| equatable t |} #n (a b c: square_matrix t n)
  : Lemma (requires matrix_eq_bool a b /\ matrix_eq_bool b c)
          (ensures matrix_eq_bool a c)
  = matrix_eq_bool_iff_pointwise a b;
    matrix_eq_bool_iff_pointwise b c;
    matrix_eq_bool_iff_pointwise a c;
    matrix_eq_trans a b c

(* ----------------------------------------------------------------- *)
(*  Additive structure: matrix_add_comm_group instance               *)
(* ----------------------------------------------------------------- *)

let matrix_neg (#t: Type) {| add_comm_group t |} (#n: pos)
               (a: square_matrix t n) : square_matrix t n
  = fun i j -> neg (a i j)

let matrix_add_congruence
  (#t: Type) {| add_comm_group t |} #n
  (a b c d: square_matrix t n)
  : Lemma (requires matrix_eq_bool a c /\ matrix_eq_bool b d)
          (ensures matrix_eq_bool (matrix_add a b) (matrix_add c d))
  = matrix_eq_bool_iff_pointwise a c;
    matrix_eq_bool_iff_pointwise b d;
    let pf (i j: fin n) : Lemma (matrix_add a b i j = matrix_add c d i j)
      = add_congruence (a i j) (b i j) (c i j) (d i j)
    in Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_add a b) (matrix_add c d)

let matrix_add_associativity
  (#t: Type) {| add_comm_group t |} #n
  (a b c: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_add (matrix_add a b) c)
                          (matrix_add a (matrix_add b c)))
  = Classical.forall_intro_3 #t add_associativity;
    matrix_eq_bool_iff_pointwise (matrix_add (matrix_add a b) c)
                                 (matrix_add a (matrix_add b c))

let matrix_add_commutativity
  (#t: Type) {| add_comm_group t |} #n (a b: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_add a b) (matrix_add b a))
  = Classical.forall_intro_2 #t add_commutativity;
    matrix_eq_bool_iff_pointwise (matrix_add a b) (matrix_add b a)

let matrix_add_zero
  (#t: Type) {| add_comm_group t |} #n (a: square_matrix t n)
  : Lemma ((matrix_eq_bool (matrix_add a zero_matrix) a) /\
           (matrix_eq_bool (matrix_add zero_matrix a) a))
  = Classical.forall_intro #t add_zero;
    matrix_eq_bool_iff_pointwise (matrix_add a zero_matrix) a;
    matrix_eq_bool_iff_pointwise (matrix_add zero_matrix a) a

let matrix_neg_congruence
  (#t: Type) {| add_comm_group t |} #n
  (a b: square_matrix t n)
  : Lemma (requires matrix_eq_bool a b)
          (ensures matrix_eq_bool (matrix_neg a) (matrix_neg b))
  = matrix_eq_bool_iff_pointwise a b;
    let pf (i j: fin n) : Lemma (matrix_neg a i j = matrix_neg b i j)
      = neg_congruence (a i j) (b i j)
    in Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_neg a) (matrix_neg b)

let matrix_add_negation
  (#t: Type) {| g: add_comm_group t |} #n (a: square_matrix t n)
  : Lemma ((matrix_eq_bool (matrix_add (matrix_neg a) a) (zero_matrix)) /\
           (matrix_eq_bool (matrix_add a (matrix_neg a)) (zero_matrix)))
  = Classical.forall_intro #t add_negation;
    matrix_eq_bool_iff_pointwise (matrix_add (matrix_neg a) a) (zero_matrix);
    matrix_eq_bool_iff_pointwise (matrix_add a (matrix_neg a)) (zero_matrix)
