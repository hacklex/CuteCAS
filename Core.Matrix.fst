module Core.Matrix

(*
  Square matrices over a generic coefficient type, represented as
  functions `i: fin n -> j: fin n -> t`.

  Ported from FStar.CAS.Matrix into the diamond-free `core/` tower.

  Differences from the old version:
  - Old tower had fine-grained atomic data classes (has_zero, has_add,
    has_neg, has_mul, has_one) and a separate `add_comm_monoid`. The new
    tower has bundle classes only: `add_comm_group t`, `ring t`,
    `commutative_ring t`. So:
      * Old `{| equatable t |} {| has_add t |}`        → `{| add_comm_group t |}`
      * Old `{| equatable t |} {| has_zero t |} {| has_one t |}` → `{| ring t |}`
      * Old `{| m: add_comm_monoid t |}`               → `{| acg: add_comm_group t |}`
      * Old `{| r: semiring t |}`                      → `{| r: ring t |}`
  - The matrix subtraction operator is dropped; in the new tower
    `add_comm_group` has no `sub` field — subtraction is `add x (neg y)`.
*)

module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Helpers
open Core.FinSum
open Core.Permutation

(* A square matrix of size n is a function from index pairs to t. *)
let square_matrix (t: Type) (n: nat) = fin n -> fin n -> t

(* ----------------------------------------------------------------- *)
(*  Pointwise equality                                               *)
(* ----------------------------------------------------------------- *)

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

(* ----------------------------------------------------------------- *)
(*  Transpose                                                        *)
(* ----------------------------------------------------------------- *)

let transpose (#t: Type) (#n: nat) (a: square_matrix t n) : square_matrix t n
  = fun i j -> a j i

let transpose_involutive (#t: Type) {| equatable t |} (#n: nat)
                         (a: square_matrix t n)
  : Lemma (matrix_eq (transpose (transpose a)) a)
  = matrix_eq_refl a

(* ----------------------------------------------------------------- *)
(*  Zero / identity matrices                                         *)
(* ----------------------------------------------------------------- *)

let zero_matrix (#t: Type) {| add_comm_group t |} (n: nat)
  : square_matrix t n
  = fun _ _ -> zero

let id_matrix (#t: Type) {| r: ring t |} (n: nat) : square_matrix t n
  = fun i j -> if i = j then r.one else r.r_add.zero

let id_matrix_diag (#t: Type) {| r: ring t |} (n: nat) (i: fin n)
  : Lemma (id_matrix #t #r n i i == r.one)
  = ()

let id_matrix_off (#t: Type) {| r: ring t |} (n: nat) (i j: fin n)
  : Lemma (requires ~(i == j))
          (ensures  id_matrix #t #r n i j == r.r_add.zero)
  = ()

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
(*  Matrix addition                                                  *)
(* ----------------------------------------------------------------- *)

let matrix_add (#t: Type) {| add_comm_group t |} (#n: nat)
               (a b: square_matrix t n) : square_matrix t n
  = fun i j -> a i j + b i j

let matrix_add_eq_at (#t: Type) {| add_comm_group t |} (#n: nat)
                     (a b: square_matrix t n) (i j: fin n)
  : Lemma (matrix_add a b i j == a i j + b i j) = ()

(* ----------------------------------------------------------------- *)
(*  Matrix multiplication                                            *)
(* ----------------------------------------------------------------- *)

let matrix_mul (#t: Type) {| r: ring t |} (#n: nat)
               (a b: square_matrix t n) : square_matrix t n
  = fun i j -> fin_sum #t #(acg_of_r t #r) #n (fun (k: fin n) -> a i k * b k j)

let matrix_mul_eq_at (#t: Type) {| r: ring t |} (#n: nat)
                    (a b: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a b i j ==
           fin_sum #t #(acg_of_r t #r) #n (fun (k: fin n) -> a i k * b k j)) = ()

(* ----------------------------------------------------------------- *)
(*  Boolean matrix equality (for the `equatable` instance)           *)
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
    eq = matrix_eq_bool;
    reflexivity = matrix_eq_bool_reflexivity;
    symmetry = matrix_eq_bool_symmetry;
    transitivity = (fun a b c ->
      matrix_eq_bool_iff_pointwise a b;
      matrix_eq_bool_iff_pointwise b c;
      matrix_eq_bool_iff_pointwise a c;
      Classical.move_requires_3 matrix_eq_trans a b c);
  }

(* ----------------------------------------------------------------- *)
(*  Additive structure: matrix_add_comm_group instance               *)
(* ----------------------------------------------------------------- *)

let matrix_neg (#t: Type) {| add_comm_group t |} (#n: nat)
               (a: square_matrix t n) : square_matrix t n
  = fun i j -> neg (a i j)

let matrix_add_congruence
  (#t: Type) {| g: add_comm_group t |} (#n: nat)
  (a b c d: square_matrix t n)
  : Lemma (requires matrix_eq_bool a c /\ matrix_eq_bool b d)
          (ensures matrix_eq_bool (matrix_add a b) (matrix_add c d))
  = matrix_eq_bool_iff_pointwise a c;
    matrix_eq_bool_iff_pointwise b d;
    let pf (i j: fin n) : Lemma (matrix_add a b i j = matrix_add c d i j)
      = g.add_congruence (a i j) (b i j) (c i j) (d i j)
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_add a b) (matrix_add c d)

let matrix_add_associativity
  (#t: Type) {| g: add_comm_group t |} (#n: nat)
  (a b c: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_add (matrix_add a b) c)
                          (matrix_add a (matrix_add b c)))
  = let pf (i j: fin n) : Lemma (matrix_add (matrix_add a b) c i j
                              = matrix_add a (matrix_add b c) i j)
      = g.add_associativity (a i j) (b i j) (c i j)
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_add (matrix_add a b) c)
                                 (matrix_add a (matrix_add b c))

let matrix_add_commutativity
  (#t: Type) {| g: add_comm_group t |} (#n: nat) (a b: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_add a b) (matrix_add b a))
  = let pf (i j: fin n) : Lemma (matrix_add a b i j = matrix_add b a i j)
      = g.add_commutativity (a i j) (b i j)
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_add a b) (matrix_add b a)

let matrix_add_zero
  (#t: Type) {| g: add_comm_group t |} (#n: nat) (a: square_matrix t n)
  : Lemma ((matrix_eq_bool (matrix_add a (zero_matrix n)) a) /\
           (matrix_eq_bool (matrix_add (zero_matrix n) a) a))
  = let pf1 (i j: fin n) : Lemma (matrix_add a (zero_matrix n) i j = a i j)
      = x_plus_zero (a i j)
    in
    let pf2 (i j: fin n) : Lemma (matrix_add (zero_matrix n) a i j = a i j)
      = zero_plus_x (a i j)
    in
    Classical.forall_intro_2 pf1;
    Classical.forall_intro_2 pf2;
    matrix_eq_bool_iff_pointwise (matrix_add a (zero_matrix n)) a;
    matrix_eq_bool_iff_pointwise (matrix_add (zero_matrix n) a) a

let matrix_neg_congruence
  (#t: Type) {| g: add_comm_group t |} (#n: nat)
  (a b: square_matrix t n)
  : Lemma (requires matrix_eq_bool a b)
          (ensures matrix_eq_bool (matrix_neg a) (matrix_neg b))
  = matrix_eq_bool_iff_pointwise a b;
    let pf (i j: fin n) : Lemma (matrix_neg a i j = matrix_neg b i j)
      = g.neg_congruence (a i j) (b i j)
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_neg a) (matrix_neg b)

let matrix_add_negation
  (#t: Type) {| g: add_comm_group t |} (#n: nat) (a: square_matrix t n)
  : Lemma ((matrix_eq_bool (matrix_add (matrix_neg a) a) (zero_matrix n)) /\
           (matrix_eq_bool (matrix_add a (matrix_neg a)) (zero_matrix n)))
  = let pf1 (i j: fin n)
      : Lemma (matrix_add (matrix_neg a) a i j = zero_matrix #t #g n i j)
      = neg_x_plus_x (a i j)
    in
    let pf2 (i j: fin n)
      : Lemma (matrix_add a (matrix_neg a) i j = zero_matrix #t #g n i j)
      = x_plus_neg_x (a i j)
    in
    Classical.forall_intro_2 pf1;
    Classical.forall_intro_2 pf2;
    matrix_eq_bool_iff_pointwise (matrix_add (matrix_neg a) a) (zero_matrix n);
    matrix_eq_bool_iff_pointwise (matrix_add a (matrix_neg a)) (zero_matrix n)

instance matrix_add_comm_group (t: Type) {| g: add_comm_group t |} (n: nat)
  : add_comm_group (square_matrix t n)
  = {
    acg_eq            = matrix_equatable t #g.acg_eq n;
    zero              = zero_matrix #t #g n;
    add               = (fun a b -> matrix_add #t #g #n a b);
    add_congruence    = (fun a b c d -> matrix_add_congruence #t #g #n a b c d);
    add_commutativity = (fun a b   -> matrix_add_commutativity #t #g #n a b);
    add_associativity = (fun a b c -> matrix_add_associativity #t #g #n a b c);
    add_zero          = (fun a     -> matrix_add_zero #t #g #n a);
    neg               = (fun a     -> matrix_neg #t #g #n a);
    neg_congruence    = (fun a b   -> matrix_neg_congruence #t #g #n a b);
    add_negation      = (fun a     -> matrix_add_negation #t #g #n a);
  }
