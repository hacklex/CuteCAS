module Core.Algebra.NotationTest

(*
   Smoke test for the new Notation operators:
     - unary ( ~- ) as TC neg
     - binary ( -- ) as TC subtract
     - int literals like -5 resolve through int_acg
     - nat arithmetic ( n - 1 ) still uses Prims
*)

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Helpers

(* Generic-t use: works under any add_comm_group. *)
let neg_id (#t:Type) {| g: add_comm_group t |} (x:t)
  : Lemma (-x = g.neg x)
  = reflexivity (-x)

let sub_def (#t:Type) {| g: add_comm_group t |} (x y:t)
  : Lemma (x -- y = g.add x (g.neg y))
  = reflexivity (x -- y)

(* int literals: -5 resolves via int_acg. *)
let int_neg_lit (_: unit) : Lemma (let x: int = -5 in x == -5)
  = ()

(* nat arithmetic: still Prims. *)
let nat_minus_still_prims (n: nat{n > 0}) (k: nat{k <= n})
  : Lemma (n - k <= n)
  = let r:nat = n-k in ()

(* Mixed: nat refinement + TC operator on int. *)
let mixed (n: nat) (x: int)
  : Lemma (let r = x -- 1 in r = x -- 1 /\ n - 0 == n)
  = reflexivity (x -- 1)

(* fin n indices stay clean. *)
let fin_arith (n: nat{n > 0}) (i: nat{i < n - 1})
  : Lemma (i + 1 < n)
  = ()
