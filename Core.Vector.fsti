module Core.Vector

(*
  Vectors over a generic coefficient type: fin n -> t.

  Provides:
    - vector type
    - propositional pointwise equality
    - decidable bool equality + equivalence lemma
    - dot product via pointwise_mul (no lambdas)
*)

open Core.Algebra
open Core.Algebra.Combinators
open Core.Algebra.Notation
open Core.FinSum
open Core.Permutation

(* ----------------------------------------------------------------- *)
(*  Core type                                                        *)
(* ----------------------------------------------------------------- *)

let vector (t: Type) (n: pos) = fin n -> t

(* ----------------------------------------------------------------- *)
(*  Propositional vector equality                                    *)
(* ----------------------------------------------------------------- *)

let vector_eq_prop (#t: Type) {| equatable t |} #n (a b: vector t n) : prop
  = forall (i: fin n). a i = b i

(* ----------------------------------------------------------------- *)
(*  Boolean vector equality                                          *)
(* ----------------------------------------------------------------- *)

val vector_eq (#t: Type) {| equatable t |} #n (a b: vector t n) : bool

val vector_eq_iff_prop (#t: Type) {| equatable t |} #n (a b: vector t n)
  : Lemma (vector_eq a b <==> vector_eq_prop a b)

val vector_eq_reflexivity (#t: Type) {| equatable t |} #n (a: vector t n)
  : Lemma (vector_eq a a)

val vector_eq_symmetry (#t: Type) {| equatable t |} #n (a b: vector t n)
  : Lemma (vector_eq a b <==> vector_eq b a)

val vector_eq_transitivity (#t: Type) {| equatable t |} #n (a b c: vector t n)
  : Lemma (requires vector_eq a b /\ vector_eq b c)
          (ensures vector_eq a c)

(* ----------------------------------------------------------------- *)
(*  Dot product                                                      *)
(* ----------------------------------------------------------------- *)

let vector_dot (#t: Type) {| r: ring t |} #n (a b: vector t n) : t
  = fin_sum (pointwise_mul a b)

val vector_dot_reveal (#t: Type) {| r: ring t |} #n (a b: vector t n)
  : Lemma (vector_dot a b == fin_sum (pointwise_mul a b))

(* ----------------------------------------------------------------- *)
(*  Pointwise additive structure                                     *)
(* ----------------------------------------------------------------- *)

let vector_zero (#t: Type) {| add_comm_group t |} #n (i: fin n) : t = zero

let vector_add (#t: Type) {| add_comm_group t |} #n (a b: vector t n) : vector t n = pointwise_add a b

let vector_neg (#t: Type) {| add_comm_group t |} #n (a: vector t n) : vector t n = pointwise_neg a

val vector_add_congruence (#t: Type) {| add_comm_group t |} #n (a b c d: vector t n)
  : Lemma (requires vector_eq a c /\ vector_eq b d)
          (ensures vector_eq (vector_add a b) (vector_add c d))

val vector_add_commutativity (#t: Type) {| add_comm_group t |} #n (a b: vector t n)
  : Lemma (vector_eq (vector_add a b) (vector_add b a))

val vector_add_associativity (#t: Type) {| add_comm_group t |} #n (a b c: vector t n)
  : Lemma (vector_eq (vector_add (vector_add a b) c)
                          (vector_add a (vector_add b c)))

val vector_add_zero (#t: Type) {| add_comm_group t |} #n (a: vector t n)
  : Lemma ((vector_eq (vector_add a vector_zero) a) /\
           (vector_eq (vector_add vector_zero a) a))

val vector_neg_congruence (#t: Type) {| add_comm_group t |} #n (a b: vector t n)
  : Lemma (requires vector_eq a b)
          (ensures vector_eq (vector_neg a) (vector_neg b))

val vector_add_negation (#t: Type) {| add_comm_group t |} #n (a: vector t n)
  : Lemma ((vector_eq (vector_add (vector_neg a) a) vector_zero) /\
           (vector_eq (vector_add a (vector_neg a)) vector_zero))

private let vector_equatable (t: Type) {| eq: equatable t |} n
  : equatable (vector t n)
  = {
    eq           = vector_eq #t #eq #n;
    reflexivity  = vector_eq_reflexivity #t #eq #n;
    symmetry     = vector_eq_symmetry #t #eq #n;
    transitivity = vector_eq_transitivity #t #eq #n;
  }

instance vector_add_comm_group (t: Type) {| g: add_comm_group t |} (n: pos)
  : add_comm_group (vector t n)
  = {
    acg_eq            = vector_equatable t #(g.acg_eq) n;
    zero              = vector_zero #t #g #n;
    add               = vector_add #t #g #n;
    add_congruence    = vector_add_congruence #t #g #n;
    add_commutativity = vector_add_commutativity #t #g #n;
    add_associativity = vector_add_associativity #t #g #n;
    add_zero          = vector_add_zero #t #g #n;
    neg               = vector_neg #t #g #n;
    neg_congruence    = vector_neg_congruence #t #g #n;
    add_negation      = vector_add_negation #t #g #n;
  }
