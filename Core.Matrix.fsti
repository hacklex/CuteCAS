module Core.Matrix

(*
  Public interface for square matrices over a generic coefficient type.

  Matrices are functions `fin n -> fin n -> t` with `n: pos`.
  Equality is propositional pointwise (`forall i j. a i j = b i j`)
  with a decidable bool form for the `equatable` instance.
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
(*  Core types                                                       *)
(* ----------------------------------------------------------------- *)

let square_matrix (t: Type) (n: pos) = fin n -> fin n -> t

let row (#t: Type) (#n: pos) (a: square_matrix t n) (row_num: fin n) : vector t n = a row_num

let col (#t: Type) (#n: pos) (a: square_matrix t n) (col_num: fin n) : vector t n = swap_args a col_num

(* ----------------------------------------------------------------- *)
(*  Propositional matrix equality                                    *)
(* ----------------------------------------------------------------- *)

let matrix_eq (#t: Type) {| equatable t |} #n (a b: square_matrix t n) : prop
  = forall (i j: fin n). a i j = b i j

val matrix_eq_refl (#t: Type) {| equatable t |} #n (a: square_matrix t n)
  : Lemma (matrix_eq a a)

val matrix_eq_sym (#t: Type) {| equatable t |} #n (a b: square_matrix t n)
  : Lemma (matrix_eq a b <==> matrix_eq b a)

val matrix_eq_trans (#t: Type) {| equatable t |} #n (a b c: square_matrix t n)
  : Lemma (requires matrix_eq a b /\ matrix_eq b c) (ensures matrix_eq a c)

(* ----------------------------------------------------------------- *)
(*  Transpose                                                        *)
(* ----------------------------------------------------------------- *)

let transpose (#t: Type) #n (a: square_matrix t n) : square_matrix t n = swap_args a

val transpose_involutive (#t: Type) {| equatable t |} #n (a: square_matrix t n)
  : Lemma (matrix_eq (transpose (transpose a)) a)

val transpose_transpose_reveal (#t: Type) {| equatable t |} #n (a: square_matrix t n) (r c: fin n)
  : Lemma (transpose (transpose a) r c == a r c)

(* ----------------------------------------------------------------- *)
(*  Zero / identity matrices                                         *)
(* ----------------------------------------------------------------- *)

let zero_matrix (#t: Type) {| add_comm_group t |} #n (r c: fin n) = zero #t

let id_matrix (#t: Type) {| r: ring t |} #n (i j: fin n) : t = if i = j then one else zero

val id_matrix_diag (#t: Type) {| r: ring t |} #n (i: fin n)
  : Lemma (id_matrix #t #r #n i i == one)

val id_matrix_off (#t: Type) {| r: ring t |} #n (i j: fin n)
  : Lemma (requires ~(i == j)) (ensures id_matrix #t i j == zero)

(* ----------------------------------------------------------------- *)
(*  Row/column permutation; row swap                                 *)
(* ----------------------------------------------------------------- *)

let permute_rows (#t: Type) #n (a: square_matrix t n) (p: permutation n) (i j: fin n) : t = a (p.fwd i) j

let permute_cols (#t: Type) #n (a: square_matrix t n) (p: permutation n) (i j: fin n) : t = a i (p.fwd j)

let swap_rows (#t: Type) #n (a: square_matrix t n) (i1 i2: fin n) : square_matrix t n = permute_rows a (transposition n i1 i2)

(* ----------------------------------------------------------------- *)
(*  Matrix addition                                                  *)
(* ----------------------------------------------------------------- *)

let matrix_add (#t: Type) {| add_comm_group t |} #n (a b: square_matrix t n) i j : t = a i j + b i j

val matrix_add_eq_at (#t: Type) {| add_comm_group t |} #n (a b: square_matrix t n) (i j: fin n)
  : Lemma (matrix_add a b i j == a i j + b i j)

(* ----------------------------------------------------------------- *)
(*  Matrix multiplication                                            *)
(* ----------------------------------------------------------------- *)

let matrix_mul (#t: Type) {| r: ring t |} #n (a b: square_matrix t n) (i j: fin n) : t
  = vector_dot (row a i) (col b j)

val matrix_mul_unfold (#t: Type) {| r: ring t |} #n (a b: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a b i j == vector_dot (row a i) (col b j))

val matrix_mul_to_fin_sum (#t: Type) {| r: ring t |} #n (a b: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a b i j == fin_sum (pointwise_mul (row a i) (col b j)))

(* ----------------------------------------------------------------- *)
(*  Boolean matrix equality (equatable instance)                     *)
(* ----------------------------------------------------------------- *)

val matrix_eq_bool (#t: Type) {| equatable t |} #n (a b: square_matrix t n) : bool

val matrix_eq_bool_iff_pointwise (#t: Type) {| equatable t |} #n (a b: square_matrix t n)
  : Lemma (matrix_eq_bool a b <==> matrix_eq a b)

val matrix_eq_bool_reflexivity (#t: Type) {| equatable t |} #n (a: square_matrix t n)
  : Lemma (matrix_eq_bool a a)

val matrix_eq_bool_symmetry (#t: Type) {| equatable t |} #n (a b: square_matrix t n)
  : Lemma (matrix_eq_bool a b <==> matrix_eq_bool b a)

val matrix_eq_bool_transitivity (#t: Type) {| equatable t |} #n (a b c: square_matrix t n)
  : Lemma (requires matrix_eq_bool a b /\ matrix_eq_bool b c)
          (ensures matrix_eq_bool a c)

instance matrix_equatable (t: Type) {| eq: equatable t |} (n: pos)
  : equatable (square_matrix t n)
  = {
    eq           = matrix_eq_bool #t #eq #n;
    reflexivity  = (fun a -> matrix_eq_bool_reflexivity #t #eq #n a);
    symmetry     = (fun a b -> matrix_eq_bool_symmetry #t #eq #n a b);
    transitivity = (fun a b c -> matrix_eq_bool_transitivity #t #eq #n a b c);
  }

(* ----------------------------------------------------------------- *)
(*  Additive structure                                               *)
(* ----------------------------------------------------------------- *)

val matrix_neg (#t: Type) {| add_comm_group t |} (#n: pos) (a: square_matrix t n) : square_matrix t n

val matrix_add_congruence (#t: Type) {| add_comm_group t |} #n
  (a b c d: square_matrix t n)
  : Lemma (requires matrix_eq_bool a c /\ matrix_eq_bool b d)
          (ensures matrix_eq_bool (matrix_add a b) (matrix_add c d))

val matrix_add_associativity (#t: Type) {| add_comm_group t |} #n
  (a b c: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_add (matrix_add a b) c)
                          (matrix_add a (matrix_add b c)))

val matrix_add_commutativity (#t: Type) {| add_comm_group t |} #n
  (a b: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_add a b) (matrix_add b a))

val matrix_add_zero (#t: Type) {| add_comm_group t |} #n
  (a: square_matrix t n)
  : Lemma ((matrix_eq_bool (matrix_add a zero_matrix) a) /\
           (matrix_eq_bool (matrix_add zero_matrix a) a))

val matrix_neg_congruence (#t: Type) {| add_comm_group t |} #n
  (a b: square_matrix t n)
  : Lemma (requires matrix_eq_bool a b)
          (ensures matrix_eq_bool (matrix_neg a) (matrix_neg b))

val matrix_add_negation (#t: Type) {| g: add_comm_group t |} #n
  (a: square_matrix t n)
  : Lemma ((matrix_eq_bool (matrix_add (matrix_neg a) a) (zero_matrix)) /\
           (matrix_eq_bool (matrix_add a (matrix_neg a)) (zero_matrix)))

instance matrix_add_comm_group (t: Type) {| g: add_comm_group t |} (n: pos)
  : add_comm_group (square_matrix t n)
  = {
    acg_eq            = matrix_equatable t #(g.acg_eq) n;
    zero              = zero_matrix #t #g #n;
    add               = matrix_add #t #g #n;
    add_congruence    = (fun a b c d -> matrix_add_congruence #t #g #n a b c d);
    add_commutativity = (fun a b -> matrix_add_commutativity #t #g #n a b);
    add_associativity = (fun a b c -> matrix_add_associativity #t #g #n a b c);
    add_zero          = (fun a -> matrix_add_zero #t #g #n a);
    neg               = matrix_neg #t #g #n;
    neg_congruence    = (fun a b -> matrix_neg_congruence #t #g #n a b);
    add_negation      = (fun a -> matrix_add_negation #t #g #n a);
  }
