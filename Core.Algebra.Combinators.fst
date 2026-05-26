module Core.Algebra.Combinators

(*
   Named pointwise combinators for the algebra tower.

   Motivation: F* unification stumbles on inline anonymous lambdas
   inside lemma postconditions. Instead of writing
       Lemma (sum_list (map (fun x -> neg (f x)) xs) = neg (sum_list (map f xs)))
   we factor the pointwise operation as a named top-level function
       Lemma (sum_list (map (pointwise_neg f) xs) = neg (sum_list (map f xs)))
   which has a stable syntactic form and survives unification across
   helper invocations.

   Design rules:
   - All definitions are plain `let` (NOT `unfold`). The stable named
     form must NOT reduce during unification. To inspect the body,
     callers invoke the corresponding `_unfold` lemma explicitly,
     or `norm [delta_only [`%pointwise_neg; ...]]`.
   - No `forall` in any clause. These combinators are pure functions;
     reasoning about them happens through unfold lemmas, not requires.
   - No SMTPat on the unfold lemmas — explicit invocation only.
   - This module is opt-in: it has no implicit instance machinery, so
     opening it brings only the names into scope.

   Author: A. Rozanov (CuteCAS).
*)

open Core.Algebra
open Core.Algebra.Notation
open Core.Permutation

(* ---------------------------------------------------------------- *)
(*  Polymorphic constant                                            *)
(* ---------------------------------------------------------------- *)

let const (#a #t: Type) (v: t) (_: a) : t = v

let const_unfold (#a #t: Type) (v: t) (x: a)
  : Lemma (const v x == v)
  = ()

(* ---------------------------------------------------------------- *)
(*  Pointwise additive operations                                   *)
(* ---------------------------------------------------------------- *)

let pointwise_neg
  (#a #t: Type) {| acg: add_comm_group t |} (f: a -> t) (x: a) : t
  = neg (f x)

let pointwise_neg_unfold
  (#a #t: Type) {| acg: add_comm_group t |} (f: a -> t) (x: a)
  : Lemma (pointwise_neg f x == neg (f x))
  = ()

let pointwise_add
  (#a #t: Type) {| acg: add_comm_group t |} (f g: a -> t) (x: a) : t
  = f x + g x

let pointwise_add_unfold
  (#a #t: Type) {| acg: add_comm_group t |} (f g: a -> t) (x: a)
  : Lemma (pointwise_add f g x == f x + g x)
  = ()

(* ---------------------------------------------------------------- *)
(*  Pointwise multiplicative operation                              *)
(* ---------------------------------------------------------------- *)

let pointwise_mul
  (#a #t: Type) {| r: ring t |} (f g: a -> t) (x: a) : t
  = f x * g x

let pointwise_mul_unfold
  (#a #t: Type) {| r: ring t |} (f g: a -> t) (x: a)
  : Lemma (pointwise_mul f g x == f x * g x)
  = ()

(* ---------------------------------------------------------------- *)
(*  Argument-swap (curried function transposition)                  *)
(* ---------------------------------------------------------------- *)

let swap_args (#a #b #c: Type) (f: a -> b -> c) (y: b) (x: a) : c
  = f x y

let swap_args_unfold (#a #b #c: Type) (f: a -> b -> c) (y: b) (x: a)
  : Lemma (swap_args f y x == f x y)
  = ()

(* ---------------------------------------------------------------- *)
(*  Function composition                                             *)
(*                                                                  *)
(*  fcomp f g x = f (g x). Named `fcomp` (not `compose`) to avoid    *)
(*  collision with Core.Permutation.compose (permutation product).   *)
(*  Used to express patterns like                                    *)
(*    L.map (fun sp -> f (inject_at i j sp)) xs                      *)
(*  as the stable named form  L.map (fcomp f (inject_at i j)) xs.    *)
(* ---------------------------------------------------------------- *)

let fcomp (#a #b #c: Type) (f: b -> c) (g: a -> b) (x: a) : c
  = f (g x)

let fcomp_unfold (#a #b #c: Type) (f: b -> c) (g: a -> b) (x: a)
  : Lemma (fcomp f g x == f (g x))
  = ()

(* ---------------------------------------------------------------- *)
(*  flip: swap the first two arguments of a curried function.       *)
(*                                                                  *)
(*  Stable named form of  fun y x -> f x y.  Enables patterns like  *)
(*    flip compose q        instead of  fun s -> compose s q        *)
(*    flip List.append ys   instead of  fun xs -> append xs ys      *)
(*  to keep public lemma posts lambda-free.                         *)
(* ---------------------------------------------------------------- *)

let flip (#a #b #c: Type) (f: a -> b -> c) (y: b) (x: a) : c
  = f x y

let flip_unfold (#a #b #c: Type) (f: a -> b -> c) (y: b) (x: a)
  : Lemma (flip f y x == f x y)
  = ()

(* ---------------------------------------------------------------- *)
(*  restrict_fn : fin_map (k+1) m -> fin_map k m                        *)
(*                                                                  *)
(*  Restricts a function on fin (k+1) to fin k by composing with the *)
(*  natural inclusion fin k <: fin (k+1). Stable named form of       *)
(*    fun (i: fin k) -> f (i <: fin (k+1)).                          *)
(* ---------------------------------------------------------------- *)

let restrict_fn (#k #m: nat) (f: fin (Prims.op_Addition k 1) -> fin m) (i: fin k)
  : fin m
  = f (i <: fin (Prims.op_Addition k 1))

let restrict_fn_unfold (#k #m: nat)
  (f: fin (Prims.op_Addition k 1) -> fin m) (i: fin k)
  : Lemma (restrict_fn f i == f (i <: fin (Prims.op_Addition k 1)))
  = ()

(* ---------------------------------------------------------------- *)
(*  apply_along : (fin n -> fin n -> t) -> (fin n -> fin n)         *)
(*              -> (fin n -> t)                                     *)
(*                                                                  *)
(*  Diagonal of a square matrix `a` indexed along a choice function *)
(*  `phi`. apply_along a phi i = a i (phi i).                       *)
(*                                                                  *)
(*  Named replacement for inline lambdas of the form                *)
(*    fun (i: fin n) -> a i (phi i)                                 *)
(*  in determinant / Cauchy-Binet expansions.                       *)
(* ---------------------------------------------------------------- *)

unfold let apply_along (#t: Type) (#n: nat)
                (a: fin n -> fin n -> t) (phi: fin n -> fin n) (i: fin n)
                : t
  = a i (phi i)

let apply_along_unfold (#t: Type) (#n: nat)
                       (a: fin n -> fin n -> t) (phi: fin n -> fin n) (i: fin n)
  : Lemma (apply_along a phi i == a i (phi i))
  = ()

(* ---------------------------------------------------------------- *)
(*  Kronecker delta (over a ring)                                   *)
(*                                                                  *)
(*  kronecker_delta i j = if i = j then one else zero.              *)
(*                                                                  *)
(*  Composes with pointwise_mul to express the delta-masking idiom: *)
(*    pointwise_mul (kronecker_delta i0) g                          *)
(*  is the function k |-> if i0 = k then g k else zero.             *)
(* ---------------------------------------------------------------- *)

let kronecker_delta
  (#t: Type) {| r: ring t |} (i j: nat) : t
  = if i = j then one else zero

let kronecker_delta_eq
  (#t: Type) {| r: ring t |} (i j: nat)
  : Lemma (requires i = j) (ensures kronecker_delta #t i j == one)
  = ()

let kronecker_delta_neq
  (#t: Type) {| r: ring t |} (i j: nat)
  : Lemma (requires i <> j) (ensures kronecker_delta #t i j == zero)
  = ()

let fin_kronecker_delta
  (#t: Type) {| r: ring t |} (#n: nat) (i j: fin n) : t
  = kronecker_delta #t (i <: nat) (j <: nat)

let fin_kronecker_delta_unfold
  (#t: Type) {| r: ring t |} (#n: nat) (i j: fin n)
  : Lemma (fin_kronecker_delta i j == kronecker_delta #t (i <: nat) (j <: nat))
  = ()

(* ---------------------------------------------------------------- *)
(*  fin_lift : (fin n -> t) -> (nat -> t), padded with zero         *)
(*                                                                  *)
(*  Used to define fin_sum on top of sum_range. Stable named form   *)
(*  of  fun k -> if k < n then f (k <: fin n) else zero.            *)
(* ---------------------------------------------------------------- *)

let fin_lift
  (#t: Type) {| acg: add_comm_group t |} (#n: nat) (f: fin n -> t) (k: nat) : t
  = if k < n then f (k <: fin n) else zero

let fin_lift_in_range
  (#t: Type) {| acg: add_comm_group t |} (#n: nat) (f: fin n -> t) (k: nat)
  : Lemma (requires k < n)
          (ensures fin_lift f k == f (k <: fin n))
  = ()

let fin_lift_out_of_range
  (#t: Type) {| acg: add_comm_group t |} (#n: nat) (f: fin n -> t) (k: nat)
  : Lemma (requires k >= n)
          (ensures fin_lift f k == zero)
  = ()

(* ---------------------------------------------------------------- *)
(*  Notes                                                            *)
(*                                                                  *)
(*  sum_range_on and fin_sum_curry — partial applications of        *)
(*  sum_range and fin_sum to a curried first argument — are defined *)
(*  in Core.FinSum to avoid a circular dependency: this module is   *)
(*  opened by FinSum, not the other way around.                     *)
(* ---------------------------------------------------------------- *)
