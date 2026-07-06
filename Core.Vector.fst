module Core.Vector

open Core.Algebra
open Core.Algebra.Combinators
open Core.Algebra.Notation
open Core.FinSum
open Core.Permutation

(* ----------------------------------------------------------------- *)
(*  Private: vector equality infrastructure                          *)
(* ----------------------------------------------------------------- *)

private let vec_eq_prop_ranged #t {| equatable t |} #n (v1 v2: vector t n) (from to: fin n) : prop
  = forall (i: nat{i >= from && i <= to}). v1 i = v2 i

private let rec vec_eq_downfrom (#t: Type) {| eq: equatable t |} (#n: pos) (v1 v2: vector t n) (i: fin n) : bool
  = if i = 0 then v1 i = v2 i else (v1 i = v2 i) && vec_eq_downfrom v1 v2 (i-1)

private let rec vec_eq_downfrom_when_prop #t {| equatable t |} #n (v1 v2: vector t n) (i: fin n)
  : Lemma (ensures vec_eq_prop_ranged v1 v2 0 i ==> vec_eq_downfrom v1 v2 i)
          (decreases i) = if i > 0 then vec_eq_downfrom_when_prop v1 v2 (i-1)

private let rec vec_eq_prop_when_downfrom #t {| equatable t |} #n (v1 v2: vector t n) (i: fin n)
  : Lemma (ensures vec_eq_downfrom v1 v2 i ==> vec_eq_prop_ranged v1 v2 0 i)
          (decreases i) = if i > 0 then vec_eq_prop_when_downfrom v1 v2 (i-1)

private let vec_eq_downfrom_iff_prop #t {| equatable t |} #n (v1 v2: vector t n) (i: fin n)
  : Lemma (vec_eq_downfrom v1 v2 i <==> vec_eq_prop_ranged v1 v2 0 i)
  = vec_eq_downfrom_when_prop v1 v2 i; vec_eq_prop_when_downfrom v1 v2 i

private let rec vec_eq_from (#t: Type) {| eq: equatable t |} #n (v1 v2: vector t n) (i: fin n)
  : Tot bool (decreases n-i)
  = if i = (n-1) then v1 i = v2 i else (v1 i = v2 i) && vec_eq_from v1 v2 (i ++ 1)

private let rec vec_eq_from_when_prop #t {| equatable t |} #n (v1 v2: vector t n) (i: fin n)
  : Lemma (ensures vec_eq_prop_ranged v1 v2 i (n-1) ==> vec_eq_from v1 v2 i)
          (decreases n-i) = if i < n-1 then vec_eq_from_when_prop v1 v2 (i ++ 1)

private let rec vec_eq_prop_when_from #t {| equatable t |} #n (v1 v2: vector t n) (i: fin n)
  : Lemma (ensures vec_eq_from v1 v2 i ==> vec_eq_prop_ranged v1 v2 i (n-1))
          (decreases n-i) = if i < n-1 then vec_eq_prop_when_from v1 v2 (i ++ 1)

private let vec_eq_from_iff_prop #t {| equatable t |} #n (v1 v2: vector t n) (i: fin n)
  : Lemma (vec_eq_from v1 v2 i <==> vec_eq_prop_ranged v1 v2 i (n-1))
  = vec_eq_from_when_prop v1 v2 i; vec_eq_prop_when_from v1 v2 i

private let vec_eq_up (#t: Type) {| eq: equatable t |} #n (v1 v2: vector t n)
  : bool = vec_eq_from v1 v2 0

private let vec_eq_up_iff_prop #t {| equatable t |} #n (v1 v2: vector t n)
  : Lemma (vec_eq_up v1 v2 <==> vec_eq_prop_ranged v1 v2 0 (n-1))
  = vec_eq_from_iff_prop v1 v2 0

(* ----------------------------------------------------------------- *)
(*  Public: vector_eq and its properties                        *)
(* ----------------------------------------------------------------- *)

let vector_eq (#t: Type) {| equatable t |} #n (a b: vector t n) : bool
  = vec_eq_up a b

let vector_eq_iff_prop (#t: Type) {| equatable t |} #n (a b: vector t n)
  : Lemma (vector_eq a b <==> vector_eq_prop a b)
  = vec_eq_up_iff_prop a b

let vector_eq_reflexivity (#t: Type) {| equatable t |} #n (a: vector t n)
  : Lemma (vector_eq a a)
  = Classical.forall_intro #t reflexivity;
    vector_eq_iff_prop a a

let vector_eq_symmetry (#t: Type) {| equatable t |} #n (a b: vector t n)
  : Lemma (vector_eq a b <==> vector_eq b a)
  = Classical.forall_intro_2 #t symmetry;
    vector_eq_iff_prop a b;
    vector_eq_iff_prop b a

let vector_eq_transitivity (#t: Type) {| equatable t |} #n (a b c: vector t n)
  : Lemma (requires vector_eq a b /\ vector_eq b c)
          (ensures vector_eq a c)
  = vector_eq_iff_prop a b;
    vector_eq_iff_prop b c;
    vector_eq_iff_prop a c;
    Classical.forall_intro_3 (Classical.move_requires_3 #t transitivity)

(* ----------------------------------------------------------------- *)
(*  Dot product reveal                                               *)
(* ----------------------------------------------------------------- *)

let vector_dot_reveal (#t: Type) {| r: ring t |} #n (a b: vector t n)
  : Lemma (vector_dot a b == fin_sum (pointwise_mul a b)) = ()

(* ----------------------------------------------------------------- *)
(*  Pointwise additive structure proofs                              *)
(* ----------------------------------------------------------------- *)

let vector_add_congruence (#t: Type) {| add_comm_group t |} #n
  (a b c d: vector t n)
  : Lemma (requires vector_eq a c /\ vector_eq b d)
          (ensures vector_eq (vector_add a b) (vector_add c d))
  = vector_eq_iff_prop a c;
    vector_eq_iff_prop b d;
    let pf (i: fin n) : Lemma (vector_add a b i = vector_add c d i)
      = add_congruence (a i) (b i) (c i) (d i)
    in Classical.forall_intro pf;
    vector_eq_iff_prop (vector_add a b) (vector_add c d)

let vector_add_commutativity (#t: Type) {| add_comm_group t |} #n
  (a b: vector t n)
  : Lemma (vector_eq (vector_add a b) (vector_add b a))
  = Classical.forall_intro_2 #t add_commutativity;
    vector_eq_iff_prop (vector_add a b) (vector_add b a)

let vector_add_associativity (#t: Type) {| add_comm_group t |} #n
  (a b c: vector t n)
  : Lemma (vector_eq (vector_add (vector_add a b) c)
                          (vector_add a (vector_add b c)))
  = Classical.forall_intro_3 #t add_associativity;
    vector_eq_iff_prop (vector_add (vector_add a b) c) 
                       (vector_add a (vector_add b c))

let vector_add_zero (#t: Type) {| add_comm_group t |} #n
  (a: vector t n)
  : Lemma ((vector_eq (vector_add a vector_zero) a) /\
           (vector_eq (vector_add vector_zero a) a))
  = Classical.forall_intro #t add_zero;
    vector_eq_iff_prop (vector_add a vector_zero) a;
    vector_eq_iff_prop (vector_add vector_zero a) a

let vector_neg_congruence (#t: Type) {| add_comm_group t |} #n
  (a b: vector t n)
  : Lemma (requires vector_eq a b)
          (ensures vector_eq (vector_neg a) (vector_neg b))
  = vector_eq_iff_prop a b;
    let pf (i: fin n) : Lemma (vector_neg a i = vector_neg b i)
      = neg_congruence (a i) (b i)
    in Classical.forall_intro pf;
    vector_eq_iff_prop (vector_neg a) (vector_neg b)

let vector_add_negation (#t: Type) {| add_comm_group t |} #n
  (a: vector t n)
  : Lemma ((vector_eq (vector_add (vector_neg a) a) vector_zero) /\
           (vector_eq (vector_add a (vector_neg a)) vector_zero))
  = Classical.forall_intro #t add_negation;
    vector_eq_iff_prop (vector_add (vector_neg a) a) (vector_zero);
    vector_eq_iff_prop (vector_add a (vector_neg a)) (vector_zero)
