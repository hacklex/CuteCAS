module Core.Algebra.Notation

(*
   Opt-in infix operator notation for the algebra tower.

   Opening this module makes `( + )`, `( * )`, unary `( ~- )`, and
   binary `( -- )` refer to the typeclass-overloaded operators of
   `Core.Algebra`. Binary `( - )` is deliberately NOT overloaded:
   it stays bound to Prims integer subtraction so that nat-arithmetic
   in refinement types and decreases clauses (`n - 1`, `m - k`, etc.)
   continues to work.

   Files that need plain integer arithmetic in refinement types,
   decreases clauses, list indexing, etc. should open ONLY
   `Core.Algebra`, never `Core.Algebra.Notation`, so F* picks the
   Prims operators.

   The intended usage pattern is:
     - Public `.fsti` interfaces and definitions: open Core.Algebra
     - Proof bodies / lemma definitions: locally `open Core.Algebra.Notation`

   `Core.Algebra.Int` is opened here so that `add_comm_group int` /
   `ring int` instances are in scope — this lets Notation-open files
   freely write things like `let x: int = -5 in ...` without TC
   resolution failing on the now-overloaded unary `( ~- )`.
*)

open Core.Algebra
open Core.Algebra.Int

unfold let succ (x:nat) : nat = x + 1

unfold let ( = ) (#t:Type) {| e: equatable t |} (x y:t) : bool = e.eq x y

unfold let ( <> ) (#t:Type) {| e: equatable t |} (x y:t) : bool = not (e.eq x y)

unfold let ( + ) (#t:Type) {| _: equatable t |} {| acg: add_comm_group t |} (x y:t) : t =
  acg.add x y

unfold let ( * ) (#t:Type) {| _: equatable t |} {| r: ring t |} (x y:t) : t =
  r.mul x y

unfold let op_Minus (#t:Type) {| g: add_comm_group t |} (x:t) : t =
  g.neg x

unfold let ( -- ) (#t:Type) {| g: add_comm_group t |} (x y:t) : t =
  g.add x (g.neg y)

