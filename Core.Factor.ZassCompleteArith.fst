module Core.Factor.ZassCompleteArith

(* ================================================================ *)
(*  Arithmetic side-conditions feeding the Kronecker hypotheses of   *)
(*  the Zassenhaus completeness proof.                               *)
(*                                                                   *)
(*    choose_k_spec        : the fuel-bounded k-search `choose_k`     *)
(*                           actually REACHES a k with pᵏ > target    *)
(*                           (fuel = target+1 suffices, since pᵏ ≥ k  *)
(*                           grows past any target within that many   *)
(*                           steps).                                  *)
(*                                                                   *)
(*    node_list_wf         : the integer node pool `node_list b`      *)
(*                           (= 1,2,…,deg b+1) is pairwise DISTINCT   *)
(*                           — the property the Kronecker bound       *)
(*                           `kbound_rhs` needs of its evaluation     *)
(*                           nodes.                                   *)
(*                                                                   *)
(*    node_nonvanishing_exist : the SEPARATE Kronecker recombination  *)
(*                           hypothesis (a distinct node list, long   *)
(*                           enough — length > deg g — on which bigF  *)
(*                           NEVER vanishes) is NOT a property of      *)
(*                           `node_list` (bigF can vanish at some of  *)
(*                           its nodes, e.g. b = x-1 vanishes at the   *)
(*                           node 1).  It is instead the finite-roots  *)
(*                           existence lemma `recombination_nodes_    *)
(*                           exist`, re-exposed here for completeness. *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                        *)
(* ================================================================ *)

module L    = FStar.List.Tot
module HR   = Core.Modular.ResidueRing.Hensel.Reduce
module Z    = Core.Factor.Zassenhaus
module RCmp = Core.Modular.RecombinationComplete

open Core.Algebra
open Core.Algebra.Int
open Core.Polynomial
open Core.Polynomial.Roots
open Core.Polynomial.Monic
open Core.Polynomial.Eval

(* ================================================================ *)
(*  §1 — choose_k reaches a power exceeding `target`.                 *)
(* ================================================================ *)

(* One step of `ppow` strictly increases the value by at least 1:     *)
(* pᵏ⁺¹ = p·pᵏ ≥ 2·pᵏ = pᵏ + pᵏ ≥ pᵏ + 1  (p ≥ 2, pᵏ ≥ 1).           *)
let ppow_step_grows (p:int{p > 1}) (k:nat)
  : Lemma (HR.ppow p (k + 1) >= HR.ppow p k + 1)
  = HR.ppow_succ p k

(* Invariant-carrying engine: as long as pᵏ + fuel exceeds target,    *)
(* `choose_k` terminates on some k' with pᵏ' > target.  Each recursive *)
(* step trades one unit of fuel for at least +1 of pᵏ, so the sum      *)
(* pᵏ + fuel never decreases and the fuel=0 branch is unreachable      *)
(* under the invariant.                                                *)
let rec choose_k_spec_aux (p:int{p > 1}) (target:nat) (k:pos) (fuel:nat)
  : Lemma (requires HR.ppow p k + fuel > target)
          (ensures  HR.ppow p (Z.choose_k p target k fuel) > target)
          (decreases fuel)
  = if HR.ppow p k > target then ()
    else if fuel = 0 then ()                         (* vacuous: invariant *)
    else begin
      ppow_step_grows p k;
      choose_k_spec_aux p target (k + 1) (fuel - 1)
    end

(* Instantiated at the call-site parameters k = 1, fuel = target+1:    *)
(* p¹ + (target+1) = p + target + 1 > target, so the invariant holds.  *)
let choose_k_spec (p:int{p > 1}) (target:nat)
  : Lemma (HR.ppow p (Z.choose_k p target 1 (target + 1)) > target)
  = choose_k_spec_aux p target 1 (target + 1)

(* ================================================================ *)
(*  §2 — the integer node pool is pairwise distinct.                  *)
(* ================================================================ *)

(* Every element of the consecutive-integer list `iota a cnt` is ≥ a.  *)
let rec iota_lower_bound (a:int) (cnt:nat) (d:int)
  : Lemma (requires L.memP d (Z.iota a cnt))
          (ensures  d >= a)
          (decreases cnt)
  = if cnt = 0 then ()
    else if d = a then ()
    else iota_lower_bound (a + 1) (cnt - 1) d

(* `iota a cnt = a, a+1, …, a+cnt-1` is pairwise distinct: the head a  *)
(* is strictly below every tail element (all ≥ a+1).                   *)
let rec iota_all_distinct (a:int) (cnt:nat)
  : Lemma (ensures all_distinct #int (Z.iota a cnt))
          (decreases cnt)
  = if cnt = 0 then ()
    else begin
      iota_all_distinct (a + 1) (cnt - 1);
      introduce forall (d:int). L.memP d (Z.iota (a + 1) (cnt - 1)) ==> not (a = d)
      with introduce _ ==> _
        with hmem. iota_lower_bound (a + 1) (cnt - 1) d
    end

(* `node_list b = iota 1 (deg b + 1)` — distinct Kronecker nodes.      *)
let node_list_wf (b: polynomial int)
  : Lemma (all_distinct #int (Z.node_list b))
  = let m : nat = if deg b >= 0 then Prims.op_Addition (deg b) 1 else 1 in
    iota_all_distinct 1 m

(* ================================================================ *)
(*  §3 — non-vanishing node list (the OTHER Kronecker hypothesis).    *)
(*                                                                   *)
(*  This is NOT about `node_list` (bigF may vanish at its nodes);     *)
(*  it is the finite-roots existence lemma, re-exposed so the whole   *)
(*  Kronecker precondition bundle lives in one place.                 *)
(* ================================================================ *)

let node_nonvanishing_exist (bigF g: polynomial int)
  : Lemma (requires monic g /\ deg bigF >= 0)
          (ensures  exists (int_cs: list int).
             deg g < L.length int_cs /\
             all_distinct #int int_cs /\
             (forall (j:nat). j < L.length int_cs ==>
                poly_eval bigF (L.index int_cs j) <> 0))
  = RCmp.recombination_nodes_exist bigF g
