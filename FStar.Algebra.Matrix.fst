module FStar.Algebra.Matrix

(*
  Square matrices over an arbitrary type, represented as functions
  `i:fin n -> j:fin n -> t`. This is the simplest faithful representation for
  algebraic-proof use; matrix algebra over typeclass-rich coefficient types
  is built up from here.

  Designed for use in determinant and resultant constructions.

  Author: A. Rozanov (CuteCAS).
*)

module TC = FStar.Tactics.Typeclasses

open FStar.Algebra.Classes.Equatable
open FStar.Algebra.Classes.Grouplikes
open FStar.Algebra.Classes.Ringlikes
open FStar.Algebra.FinSum
open FStar.Algebra.Permutation

(* The natural-number-bounded index type, shared with `Permutation`. *)

(* A square matrix of size n is just a function from index pairs. *)
let square_matrix (t: Type) (n: nat) = fin n -> fin n -> t

(* Pointwise equality of matrices, expressed as a boolean check on every
   index pair via the carrier's `equatable`. We expose two forms:
   - `matrix_eq_at`: equality at a specific index (for proof bookkeeping).
   - `matrix_eq`: forall-quantified extensional equality (for stating
                   lemmas, not for runtime).
*)

let matrix_eq (#t: Type) {| equatable t |} (#n: nat)
              (a b: square_matrix t n) : prop
  = forall (i j: fin n). a i j = b i j

let matrix_eq_refl (#t: Type) {| equatable t |} (#n: nat)
                   (a: square_matrix t n)
  : Lemma (matrix_eq a a)
  = Classical.forall_intro (reflexivity #t)

let matrix_eq_sym (#t: Type) {| equatable t |} (#n: nat)
                  (a b: square_matrix t n)
  : Lemma (matrix_eq a b <==> matrix_eq b a)
  = let aux (i j: fin n) : Lemma ((a i j = b i j) <==> (b i j = a i j))
      = symmetry (a i j) (b i j)
    in
    Classical.forall_intro_2 aux

let matrix_eq_trans (#t: Type) {| equatable t |} (#n: nat)
                    (a b c: square_matrix t n)
  : Lemma (requires matrix_eq a b /\ matrix_eq b c)
          (ensures matrix_eq a c)
  = let aux (i j: fin n) : Lemma (a i j = c i j)
      = transitivity (a i j) (b i j) (c i j)
    in
    Classical.forall_intro_2 aux

(* Transpose. *)
let transpose (#t: Type) (#n: nat) (a: square_matrix t n) : square_matrix t n
  = fun i j -> a j i

let transpose_involutive (#t: Type) {| equatable t |} (#n: nat)
                         (a: square_matrix t n)
  : Lemma (matrix_eq (transpose (transpose a)) a)
  = matrix_eq_refl a

(* Identity matrix. Only meaningful in the presence of `zero` and `one`,
   which together come from a `semiring` (or any structure providing both). *)
let id_matrix (#t: Type) {| h0: has_zero t |} {| h1: has_one t |}
              (n: nat) : square_matrix t n
  = fun i j -> if i = j then one else zero

(* The zero matrix. *)
let zero_matrix (#t: Type) {| has_zero t |} (n: nat) : square_matrix t n
  = fun _ _ -> zero

(* ----------------------------------------------------------------- *)
(*  Row/column permutation; row swap                                 *)
(* ----------------------------------------------------------------- *)

let permute_rows (#t: Type) (#n: nat) (a: square_matrix t n)
                 (p: permutation n) : square_matrix t n
  = fun i j -> a (p.fwd i) j

let permute_cols (#t: Type) (#n: nat) (a: square_matrix t n)
                 (p: permutation n) : square_matrix t n
  = fun i j -> a i (p.fwd j)

let swap_rows (#t: Type) (#n: nat) (a: square_matrix t n)
              (i1 i2: fin n) : square_matrix t n
  = permute_rows a (transposition n i1 i2)

(* ----------------------------------------------------------------- *)
(*  Matrix addition (componentwise, over has_add)                    *)
(* ----------------------------------------------------------------- *)

let matrix_add (#t: Type) {| has_add t |} (#n: nat)
               (a b: square_matrix t n) : square_matrix t n
  = fun i j -> a i j + b i j

let matrix_add_eq_at (#t: Type) {| has_add t |} (#n: nat)
                     (a b: square_matrix t n) (i j: fin n)
  : Lemma (matrix_add a b i j == a i j + b i j) = ()

(* ----------------------------------------------------------------- *)
(*  Matrix multiplication: (A*B) i j = sum_k A i k * B k j           *)
(*                                                                   *)
(*  Requires `semiring` (or stronger) so that `+`/`*`/`zero`/`one`   *)
(*  are coherently in scope.                                         *)
(* ----------------------------------------------------------------- *)

let matrix_mul (#t: Type) {| r: semiring t |} (#n: nat)
               (a b: square_matrix t n) : square_matrix t n
  = fun i j -> sum_range (fun (k: nat) -> if k < n then a i k * b k j else zero) 0 n

let matrix_mul_eq_at (#t: Type) {| r: semiring t |} (#n: nat)
                    (a b: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a b i j ==
           sum_range (fun (k: nat) -> if k < n then a i k * b k j else zero) 0 n) = ()

(* ----------------------------------------------------------------- *)
(*  Boolean matrix equality                                          *)
(*                                                                   *)
(*  We want a decidable equality to instantiate `equatable`.  Build  *)
(*  it as a recursive `all` over the index pairs.                    *)
(* ----------------------------------------------------------------- *)

let rec matrix_eq_row_from
  (#t: Type) {| equatable t |} (#n: nat)
  (a b: square_matrix t n) (i: fin n) (j: nat{j <= n})
  : Tot bool (decreases (Prims.op_Subtraction n j))
  = if j >= n then true
    else (a i (j <: fin n) = b i j) && matrix_eq_row_from a b i (Prims.op_Addition j 1)

let rec matrix_eq_from
  (#t: Type) {| equatable t |} (#n: nat)
  (a b: square_matrix t n) (i: nat{i <= n})
  : Tot bool (decreases (Prims.op_Subtraction n i))
  = if i >= n then true
    else matrix_eq_row_from a b (i <: fin n) 0 && matrix_eq_from a b (Prims.op_Addition i 1)

let matrix_eq_bool (#t: Type) {| equatable t |} (#n: nat)
                   (a b: square_matrix t n) : bool
  = matrix_eq_from a b 0

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec matrix_eq_row_from_complete
  (#t: Type) {| equatable t |} (#n: nat)
  (a b: square_matrix t n) (i: fin n) (j: nat{j <= n})
  : Lemma (ensures matrix_eq_row_from a b i j
                <==> (forall (k: nat). j <= k /\ k < n ==> a i (k <: fin n) = b i k))
          (decreases (Prims.op_Subtraction n j))
  = if j >= n then ()
    else matrix_eq_row_from_complete a b i (Prims.op_Addition j 1)
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec matrix_eq_from_complete
  (#t: Type) {| equatable t |} (#n: nat)
  (a b: square_matrix t n) (i: nat{i <= n})
  : Lemma (ensures matrix_eq_from a b i
                <==> (forall (k: nat) (j: nat).
                       i <= k /\ k < n /\ j < n ==> a (k <: fin n) (j <: fin n) = b k j))
          (decreases (Prims.op_Subtraction n i))
  = if i >= n then ()
    else begin
      matrix_eq_from_complete a b (Prims.op_Addition i 1);
      matrix_eq_row_from_complete a b (i <: fin n) 0
    end
#pop-options

let matrix_eq_bool_iff_pointwise
  (#t: Type) {| equatable t |} (#n: nat)
  (a b: square_matrix t n)
  : Lemma (matrix_eq_bool a b <==> matrix_eq a b)
  = matrix_eq_from_complete a b 0

(* equatable instance *)
let matrix_eq_bool_reflexivity
  (#t: Type) {| equatable t |} (#n: nat) (a: square_matrix t n)
  : Lemma (matrix_eq_bool a a)
  = matrix_eq_refl a;
    matrix_eq_bool_iff_pointwise a a

let matrix_eq_bool_symmetry
  (#t: Type) {| equatable t |} (#n: nat) (a b: square_matrix t n)
  : Lemma (matrix_eq_bool a b <==> matrix_eq_bool b a)
  = matrix_eq_bool_iff_pointwise a b;
    matrix_eq_bool_iff_pointwise b a;
    matrix_eq_sym a b

let matrix_eq_bool_transitivity
  (#t: Type) {| equatable t |} (#n: nat) (a b c: square_matrix t n)
  : Lemma (requires matrix_eq_bool a b /\ matrix_eq_bool b c)
          (ensures matrix_eq_bool a c)
  = matrix_eq_bool_iff_pointwise a b;
    matrix_eq_bool_iff_pointwise b c;
    matrix_eq_bool_iff_pointwise a c;
    matrix_eq_trans a b c

instance matrix_equatable (t: Type) {| equatable t |} (n: nat)
  : equatable (square_matrix t n)
  = {
    op_Equals = matrix_eq_bool;
    reflexivity = matrix_eq_bool_reflexivity;
    symmetry = matrix_eq_bool_symmetry;
    transitivity = (fun a b c ->
      matrix_eq_bool_iff_pointwise a b;
      matrix_eq_bool_iff_pointwise b c;
      matrix_eq_bool_iff_pointwise a c;
      Classical.move_requires_3 matrix_eq_trans a b c);
  }

(* ----------------------------------------------------------------- *)
(*  Additive structure                                               *)
(* ----------------------------------------------------------------- *)

let matrix_add_congruence
  (#t: Type) {| h: has_add t |} (#n: nat)
  (a b c d: square_matrix t n)
  : Lemma (requires matrix_eq_bool a c /\ matrix_eq_bool b d)
          (ensures matrix_eq_bool (matrix_add a b) (matrix_add c d))
  = matrix_eq_bool_iff_pointwise a c;
    matrix_eq_bool_iff_pointwise b d;
    let pf (i j: fin n) : Lemma (matrix_add a b i j = matrix_add c d i j)
      = add_congruence (a i j) (b i j) (c i j) (d i j)
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_add a b) (matrix_add c d)

instance matrix_has_zero (t: Type) {| h: has_zero t |} (n: nat)
  : has_zero (square_matrix t n)
  = {
    eq = matrix_equatable t #h.eq n;
    zero = zero_matrix n;
  }

instance matrix_has_add (t: Type) {| h: has_add t |} (n: nat)
  : has_add (square_matrix t n)
  = {
    ( + ) = matrix_add;
    eq = matrix_equatable t #h.eq n;
    congruence = matrix_add_congruence #t #h #n;
  }

let matrix_add_associativity
  (#t: Type) {| sg: add_semigroup t |} (#n: nat)
  (a b c: square_matrix t n)
  : Lemma (matrix_add (matrix_add a b) c = matrix_add a (matrix_add b c))
  = let pf (i j: fin n) : Lemma (matrix_add (matrix_add a b) c i j
                              = matrix_add a (matrix_add b c) i j)
      = add_associativity (a i j) (b i j) (c i j)
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_add (matrix_add a b) c)
                                 (matrix_add a (matrix_add b c))

instance matrix_add_semigroup (t: Type) {| sg: add_semigroup t |} (n: nat)
  : add_semigroup (square_matrix t n)
  = {
    has_add = matrix_has_add t #sg.has_add n;
    associativity = matrix_add_associativity #t #sg #n;
  }

let matrix_left_add_identity
  (#t: Type) {| m: add_monoid t |} (#n: nat) (a: square_matrix t n)
  : Lemma (matrix_add (zero_matrix n) a = a)
  = let pf (i j: fin n) : Lemma (matrix_add (zero_matrix n) a i j = a i j)
      = left_add_identity (a i j)
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_add (zero_matrix n) a) a

let matrix_right_add_identity
  (#t: Type) {| m: add_monoid t |} (#n: nat) (a: square_matrix t n)
  : Lemma (matrix_add a (zero_matrix n) = a)
  = let pf (i j: fin n) : Lemma (matrix_add a (zero_matrix n) i j = a i j)
      = right_add_identity (a i j)
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_add a (zero_matrix n)) a

instance matrix_add_monoid (t: Type) {| m: add_monoid t |} (n: nat)
  : add_monoid (square_matrix t n)
  = {
    has_zero = matrix_has_zero t #m.has_zero n;
    add_semigroup = matrix_add_semigroup t #m.add_semigroup n;
    left_add_identity = matrix_left_add_identity #t #m #n;
    right_add_identity = matrix_right_add_identity #t #m #n;
  }

let matrix_add_commutativity
  (#t: Type) {| cm: add_comm_magma t |} (#n: nat) (a b: square_matrix t n)
  : Lemma (matrix_add a b = matrix_add b a)
  = let pf (i j: fin n) : Lemma (matrix_add a b i j = matrix_add b a i j)
      = add_commutativity (a i j) (b i j)
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_add a b) (matrix_add b a)

instance matrix_add_comm_magma (t: Type) {| cm: add_comm_magma t |} (n: nat)
  : add_comm_magma (square_matrix t n)
  = {
    has_add = matrix_has_add t #cm.has_add n;
    add_commutativity = matrix_add_commutativity #t #cm #n;
  }

instance matrix_add_comm_semigroup
  (t: Type) {| csg: add_comm_semigroup t |} (n: nat)
  : add_comm_semigroup (square_matrix t n)
  = {
    add_semigroup = matrix_add_semigroup t #csg.add_semigroup n;
    add_comm_magma = matrix_add_comm_magma t #csg.add_comm_magma n;
  }

instance matrix_add_comm_monoid
  (t: Type) {| cm: add_comm_monoid t |} (n: nat)
  : add_comm_monoid (square_matrix t n)
  = {
    add_monoid = matrix_add_monoid t #cm.add_monoid n;
    add_comm_semigroup = matrix_add_comm_semigroup t #cm.add_comm_semigroup n;
  }

(* ----------------------------------------------------------------- *)
(*  Negation / subtraction                                           *)
(* ----------------------------------------------------------------- *)

let matrix_neg (#t: Type) {| h: has_neg t |} (#n: nat)
               (a: square_matrix t n) : square_matrix t n
  = fun i j -> -(a i j)

let matrix_sub (#t: Type) {| h: has_sub t |} (#n: nat)
               (a b: square_matrix t n) : square_matrix t n
  = fun i j -> (a i j) - (b i j)

instance matrix_has_neg (t: Type) {| h: has_neg t |} (n: nat)
  : has_neg (square_matrix t n)
  = { op_Minus = matrix_neg; }

instance matrix_has_sub (t: Type) {| h: has_sub t |} (n: nat)
  : has_sub (square_matrix t n)
  = { op_Subtraction = matrix_sub; }

let matrix_subtraction_definition
  (#t: Type) {| g: add_group t |} (#n: nat) (a b: square_matrix t n)
  : Lemma ((matrix_sub a b) = (matrix_add a (matrix_neg b)))
  = let pf (i j: fin n)
      : Lemma ((matrix_sub a b) i j = (matrix_add a (matrix_neg b)) i j)
      = subtraction_definition (a i j) (b i j)
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_sub a b) (matrix_add a (matrix_neg b))

let matrix_negation
  (#t: Type) {| g: add_group t |} (#n: nat) (a: square_matrix t n)
  : Lemma ((matrix_add a (matrix_neg a)) = zero_matrix n
        /\ (matrix_add (matrix_neg a) a) = zero_matrix n)
  = let pf1 (i j: fin n)
      : Lemma ((matrix_add a (matrix_neg a)) i j = zero_matrix n i j
            /\ (matrix_add (matrix_neg a) a) i j = zero_matrix n i j)
      = negation (a i j)
    in
    Classical.forall_intro_2 pf1;
    matrix_eq_bool_iff_pointwise (matrix_add a (matrix_neg a)) (zero_matrix n);
    matrix_eq_bool_iff_pointwise (matrix_add (matrix_neg a) a) (zero_matrix n)

instance matrix_add_group (t: Type) {| g: add_group t |} (n: nat)
  : add_group (square_matrix t n)
  = {
    add_monoid = matrix_add_monoid t #g.add_monoid n;
    has_neg = matrix_has_neg t #g.has_neg n;
    has_sub = matrix_has_sub t #g.has_sub n;
    subtraction_definition = matrix_subtraction_definition #t #g #n;
    negation = matrix_negation #t #g #n;
  }

instance matrix_add_comm_group (t: Type) {| g: add_comm_group t |} (n: nat)
  : add_comm_group (square_matrix t n)
  = {
    add_group = matrix_add_group t #g.add_group n;
    add_comm_monoid = matrix_add_comm_monoid t #g.add_comm_monoid n;
  }
