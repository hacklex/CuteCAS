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
  if i = (n-1) then matrix_row_eq a b i else matrix_row_eq a b i && matrix_rows_eq_from a b (i ++ 1)

private let rec matrix_cols_eq_from (#t: Type) {| equatable t |} #n (a b: square_matrix t n) (j: fin n)
  : Tot bool (decreases (n - j)) = 
  if j = (n-1) then matrix_col_eq a b j else matrix_col_eq a b j && matrix_cols_eq_from a b (j ++ 1)
 
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
      aux a b (from ++ 1)
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
      aux a b (from ++ 1)
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
    aux a b (from ++ 1)
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
    aux a b (from ++ 1)
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
  = fun i j -> (- (a i j))

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

(* ===== merged from Core.Matrix.Ring - matrix ring instance + mul laws (matrix_mul_* private) ===== *)

(* ----------------------------------------------------------------- *)
(*  Congruence of matrix_mul                                         *)
(* ----------------------------------------------------------------- *)

let matrix_mul_pointwise_congruence
  (#t: Type) {| r: ring t |} (#n: pos)
  (a b c d: square_matrix t n) (i j: fin n)
  : Lemma (requires matrix_eq a c /\ matrix_eq b d)
          (ensures matrix_mul a b i j = matrix_mul c d i j)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    matrix_mul_to_fin_sum a b i j;
    matrix_mul_to_fin_sum c d i j;
    let pf (k: fin n) : Lemma (pointwise_mul (row a i) (col b j) k 
                              = pointwise_mul (row c i) (col d j) k)
      = mul_congruence (a i k) (b k j) (c i k) (d k j)
    in
    fin_sum_congruence (pointwise_mul (row a i) (col b j))
                       (pointwise_mul (row c i) (col d j)) pf

let matrix_mul_congruence
  (#t: Type) {| r: ring t |} (#n: pos)
  (a b c d: square_matrix t n)
  : Lemma (requires matrix_eq_bool a c /\ matrix_eq_bool b d)
          (ensures matrix_eq_bool (matrix_mul a b) (matrix_mul c d))
  = matrix_eq_bool_iff_pointwise a c;
    matrix_eq_bool_iff_pointwise b d;
    let pf (i j: fin n) : Lemma (matrix_mul a b i j = matrix_mul c d i j)
      = matrix_mul_pointwise_congruence a b c d i j
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul a b) (matrix_mul c d)

(* ----------------------------------------------------------------- *)
(*  Left/right identities                                            *)
(* ----------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let matrix_mul_left_identity_pointwise
  (#t: Type) {| r: ring t |} (#n: pos)
  (a: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul id_matrix a i j = a i j)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    matrix_mul_to_fin_sum id_matrix a i j;
    fin_sum_congruence (pointwise_mul (row id_matrix i) (col a j))
                       (pointwise_mul (fin_kronecker_delta i) (col a j)) (fun _ -> ());
    fin_sum_kronecker i (col a j)

let matrix_mul_right_identity_pointwise
  (#t: Type) {| r: ring t |} (#n: pos)
  (a: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a id_matrix i j = a i j)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    matrix_mul_to_fin_sum a id_matrix i j;
    let pf (k: fin n) : Lemma (pointwise_mul (row a i) (col id_matrix j) k
                              = pointwise_mul (fin_kronecker_delta j) (row a i) k)
      = if k = j then (x_mul_one (a i k); one_mul_x (a i k))
        else (x_mul_zero (a i k); zero_mul_x (a i k))
    in
    fin_sum_congruence (pointwise_mul (row a i) (col id_matrix j))
                       (pointwise_mul (fin_kronecker_delta j) (row a i)) pf;
    fin_sum_kronecker j (row a i)
#pop-options

let matrix_mul_left_identity
  (#t: Type) {| r: ring t |} (#n: pos) (a: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul id_matrix a) a)
  = let id_mat = id_matrix in
    let pf (i j: fin n) : Lemma (matrix_mul id_mat a i j = a i j)
      = matrix_mul_left_identity_pointwise a i j
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul id_mat a) a

let matrix_mul_right_identity
  (#t: Type) {| r: ring t |} (#n: pos) (a: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul a id_matrix) a)
  = let id_mat = id_matrix in
    let pf (i j: fin n) : Lemma (matrix_mul a id_mat i j = a i j)
      = matrix_mul_right_identity_pointwise a i j
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul a id_mat) a

(* ----------------------------------------------------------------- *)
(*  Associativity                                                    *)
(* ----------------------------------------------------------------- *)

(* Clean proof using only combinators, no lambdas. 
   Goal: (AB)C_{ij} = A(BC)_{ij}
   
   Strategy (all sums are fin_sum):
     LHS == Σₗ (AB)ᵢₗ·cₗⱼ
         == Σₗ (Σₖ aᵢₖ·bₖₗ)·cₗⱼ           (expand AB)
         == Σₗ Σₖ (aᵢₖ·bₖₗ)·cₗⱼ            (fin_sum_mul_right)
         == Σₗ Σₖ aᵢₖ·(bₖₗ·cₗⱼ)            (ring associativity)
         == Σₖ Σₗ aᵢₖ·(bₖₗ·cₗⱼ)            (fin_sum_swap)
         == Σₖ aᵢₖ·(Σₗ bₖₗ·cₗⱼ)            (fin_sum_mul_left)
         == Σₖ aᵢₖ·(BC)ₖⱼ                   (fold BC)
         == RHS
*)

let matrix_mul_assoc_clean
  (#t: Type) {| r: ring t |} (#n: pos)
  (a b c: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul (matrix_mul a b) c i j
        = matrix_mul a (matrix_mul b c) i j)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let ab = matrix_mul a b in
    let bc = matrix_mul b c in
    let ri  = row a i in    (* ri k  = a i k *)
    let cj  = col c j in    (* cj l  = c l j *)

    (* The key curried double-sum: double_lk l k = aᵢₖ·(bₖₗ·cₗⱼ) *)
    let double_lk (l: fin n) (k: fin n) : t = ri k * (b k l * cj l) in
    let rhs_summand (k: fin n) : t = ri k * bc k j in

    (* ——— LHS unfolding ———
       matrix_mul ab c i j 
       == fin_sum (pointwise_mul (row ab i) cj)         [matrix_mul_to_fin_sum]
       Each summand: (row ab i) l * cj l 
                   = ab i l * cj l
                   = fin_sum (pointwise_mul ri (col b l)) * cj l   [step1]
                   = fin_sum (double_lk l)                         [step2]
                   = fin_sum_curry double_lk l *)
    let lhs_to_double (l: fin n) : Lemma (pointwise_mul (row ab i) cj l = fin_sum_curry double_lk l) = 
        matrix_mul_to_fin_sum a b i l;
        fin_sum_mul_right (pointwise_mul (row a i) (col b l)) (col c j l);
        Classical.forall_intro_3 #t mul_associativity;
        fin_sum_congruence
          (pointwise_mul (pointwise_mul (row a i) (col b l)) (const (col c j l)))
          (double_lk l) (fun _ -> ())
    in
    matrix_mul_to_fin_sum (matrix_mul a b) c i j;
    fin_sum_congruence (pointwise_mul (row (matrix_mul a b) i) (col c j)) 
                       (fin_sum_curry double_lk) lhs_to_double;
    (* Now: matrix_mul ab c i j = fin_sum (fin_sum_curry double_lk) *)
    (* ——— Sum swap ———
       fin_sum (fin_sum_curry double_lk) = fin_sum (fin_sum_curry (swap_args double_lk)) *)
    fin_sum_swap double_lk;
    (* ——— RHS folding ———
       fin_sum_curry (swap_args double_lk) k
       = fin_sum (swap_args double_lk k)
       = Σₗ double_lk l k
       = Σₗ aᵢₖ·(bₖₗ·cₗⱼ)
       = aᵢₖ · Σₗ bₖₗ·cₗⱼ                  [fin_sum_mul_left]
       = aᵢₖ · (BC)ₖⱼ                       [fold BC]
       = rhs_summand k *)
    let double_to_rhs (k: fin n) : Lemma
      (fin_sum_curry (swap_args double_lk) k = rhs_summand k)
      = fin_sum_congruence (swap_args double_lk k)
          (pointwise_mul (const (row a i k)) (pointwise_mul (row b k) (col c j))) (fun _ -> ());
        fin_sum_mul_left (row a i k) (pointwise_mul (row b k) (col c j));
        matrix_mul_to_fin_sum b c k j;
        mul_congruence (row a i k) (fin_sum (pointwise_mul (row b k) (col c j)))
                         (row a i k) (matrix_mul b c k j)
    in
    fin_sum_congruence (fin_sum_curry (swap_args double_lk)) rhs_summand double_to_rhs;
    (* Now: fin_sum (fin_sum_curry (swap_args double_lk)) = fin_sum rhs_summand *)

    (* RHS: matrix_mul a (matrix_mul b c) i j = fin_sum rhs_summand *)
    matrix_mul_to_fin_sum a (matrix_mul b c) i j;
    fin_sum_congruence (pointwise_mul (row a i) (col (matrix_mul b c) j)) rhs_summand (fun _ -> ())    

let matrix_mul_associativity
  (#t: Type) {| r: ring t |} (#n: pos) (a b c: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul (matrix_mul a b) c)
                          (matrix_mul a (matrix_mul b c)))
  = Classical.forall_intro_2 (matrix_mul_assoc_clean a b c);
    matrix_eq_bool_iff_pointwise (matrix_mul (matrix_mul a b) c)
                                 (matrix_mul a (matrix_mul b c))

(* ----------------------------------------------------------------- *)
(*  Left distributivity:  a * (b + c) = a*b + a*c                    *)
(* ----------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let matrix_left_distributivity_pointwise
  (#t: Type) {| r: ring t |} (#n: pos)
  (a b c: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a (matrix_add b c) i j
        = matrix_add (matrix_mul a b) (matrix_mul a c) i j)
  = elim_equatable_laws t ();
    matrix_mul_to_fin_sum a (matrix_add b c) i j;
    matrix_mul_to_fin_sum a b i j;
    matrix_mul_to_fin_sum a c i j;
    let pf (k: fin n) : Lemma (pointwise_mul (row a i) (col (matrix_add b c) j) k 
                              = pointwise_mul (row a i) (col b j) k + pointwise_mul (row a i) (col c j) k)
      = left_distributivity (a i k) (b k j) (c k j) in
    fin_sum_add_ext (pointwise_mul (row a i) (col b j))
                    (pointwise_mul (row a i) (col c j))
                    (pointwise_mul (row a i) (col (matrix_add b c) j)) pf;
    add_congruence (fin_sum (pointwise_mul (row a i) (col b j)))
                   (fin_sum (pointwise_mul (row a i) (col c j)))
                   (matrix_mul a b i j) (matrix_mul a c i j)
#pop-options

let matrix_left_distributivity
  (#t: Type) {| r: ring t |} (#n: pos) (a b c: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul a (matrix_add b c))
                          (matrix_add (matrix_mul a b) (matrix_mul a c)))
  = let pf (i j: fin n) : Lemma (matrix_mul a (matrix_add b c) i j
                              = matrix_add (matrix_mul a b) (matrix_mul a c) i j)
      = matrix_left_distributivity_pointwise a b c i j
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul a (matrix_add b c))
                                 (matrix_add (matrix_mul a b) (matrix_mul a c))

(* ----------------------------------------------------------------- *)
(*  Right distributivity:  (b + c) * a = b*a + c*a                   *)
(*  Note arg order matches `r.right_distributivity x y z`:           *)
(*    (y+z)*x = y*x + z*x  — first arg is the RIGHT factor.          *)
(* ----------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let matrix_right_distributivity_pointwise
  (#t: Type) {| r: ring t |} (#n: pos)
  (a b c: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul (matrix_add a b) c i j = matrix_add (matrix_mul a c) (matrix_mul b c) i j) = 
    elim_equatable_laws t ();
    matrix_mul_to_fin_sum (matrix_add a b) c i j;
    matrix_mul_to_fin_sum a c i j;
    matrix_mul_to_fin_sum b c i j;
    let pf (k: fin n) : Lemma (pointwise_mul (row (matrix_add a b) i) (col c j) k
                              = pointwise_mul (row a i) (col c j) k + pointwise_mul (row b i) (col c j) k)
      = right_distributivity (c k j) (a i k) (b i k)
    in
    fin_sum_add_ext (pointwise_mul (row a i) (col c j))
                    (pointwise_mul (row b i) (col c j))
                    (pointwise_mul (row (matrix_add a b) i) (col c j)) pf;
    add_congruence (fin_sum (pointwise_mul (row a i) (col c j)))
                   (fin_sum (pointwise_mul (row b i) (col c j)))
                   (matrix_mul a c i j) (matrix_mul b c i j)
#pop-options

let matrix_right_distributivity
  (#t: Type) {| r: ring t |} (#n: pos) (a b c: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul (matrix_add b c) a)
                          (matrix_add (matrix_mul b a) (matrix_mul c a)))
  = Classical.forall_intro_2 (matrix_right_distributivity_pointwise b c a);
    matrix_eq_bool_iff_pointwise (matrix_mul (matrix_add b c) a)
                                 (matrix_add (matrix_mul b a) (matrix_mul c a))

(* ----------------------------------------------------------------- *)
(*  Zero absorption (derived: needed for the ring instance closure)  *)
(* ----------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let matrix_left_absorption_pointwise
  (#t: Type) {| r: ring t |} (#n: pos)
  (a: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul zero_matrix a i j = zero)
  = matrix_mul_to_fin_sum zero_matrix a i j;
    Classical.forall_intro #t (zero_mul_x);
    fin_sum_zero_ext (pointwise_mul (row zero_matrix i) (col a j)) (fun _ -> ())
#pop-options

let matrix_left_absorption
  (#t: Type) {| r: ring t |} (#n: pos) (a: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul zero_matrix a) zero_matrix)
  = Classical.forall_intro_2 (matrix_left_absorption_pointwise a);    
    matrix_eq_bool_iff_pointwise (matrix_mul zero_matrix a) zero_matrix

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let matrix_right_absorption_pointwise
  (#t: Type) {| r: ring t |} (#n: pos)
  (a: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a zero_matrix i j = zero) = 
    matrix_mul_to_fin_sum a zero_matrix i j;
    Classical.forall_intro #t (x_mul_zero);
    fin_sum_zero_ext (pointwise_mul (row a i) (col zero_matrix j)) (fun _ -> ())
#pop-options

let matrix_right_absorption
  (#t: Type) {| r: ring t |} (#n: pos) (a: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul a zero_matrix) zero_matrix)
  = Classical.forall_intro_2 (matrix_right_absorption_pointwise a);   
    matrix_eq_bool_iff_pointwise (matrix_mul a zero_matrix) zero_matrix

(* ----------------------------------------------------------------- *)
(*  ring (square_matrix t n) instance                                *)
(* ----------------------------------------------------------------- *)

(* merged left∧right multiplicative identity (implements the fsti val; used by matrix_ring). *)
let matrix_mul_identity #t {| r: ring t |} (#n: pos) (a: square_matrix t n)
  : Lemma ((matrix_mul a id_matrix `matrix_eq_bool` a) /\ (matrix_mul id_matrix a `matrix_eq_bool` a)) =
  matrix_mul_left_identity a;
  matrix_mul_right_identity a

(* matrix_ring instance now lives (transparently) in Core.Matrix.fsti. *)
