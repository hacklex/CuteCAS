module Core.Polynomial.LagrangeInterp

(* ================================================================ *)
(*  Lagrange interpolant (existence half of interpolation, §D).     *)
(*                                                                   *)
(*  For distinct nodes  cs = [c_0; ...; c_{n-1}]  and a polynomial g *)
(*  define                                                           *)
(*    interpolant = sum_{j<n} g(c_j) . basis_j                       *)
(*  where basis_j is the Lagrange basis polynomial.                  *)
(*                                                                   *)
(*  PRIORITY 1: interpolant(c_k) = g(c_k) for every node c_k.       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Roots
open Core.Polynomial.Lagrange
open Core.Polynomial.DerivPower   (* for pacg *)

open Core.FinSum

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* The commutative_ring a `field t` induces on the coefficients. *)
unfold
let crf (t:Type) {| f: field t |} : commutative_ring t = cr_of_id t #(id_of_f t)

(* ---------------------------------------------------------------- *)
(*  The interpolant summand, as a NAMED total `nat -> polynomial t`. *)
(*  The `j < length cs` guard keeps it total and exposes the         *)
(*  refinement needed by `lagrange_basis` / `L.index`.               *)
(* ---------------------------------------------------------------- *)

let interp_term (#t:Type) {| f: field t |} (g: polynomial t) (cs: list t)
                {| sq: squash (all_distinct cs) |} (j: nat)
  : polynomial t
  = if j < L.length cs
    then poly_scale (poly_eval g (L.index cs j)) (lagrange_basis cs j #sq)
    else poly_zero #t

(* ---------------------------------------------------------------- *)
(*  The interpolant.                                                 *)
(* ---------------------------------------------------------------- *)

let lagrange_interpolant (#t:Type) {| f: field t |} (g: polynomial t) (cs: list t)
                         {| sq: squash (all_distinct cs) |}
  : polynomial t
  = sum_range (interp_term g cs #sq) 0 (L.length cs)

(* ================================================================ *)
(*  PRIORITY 1 — evaluation at a node.                               *)
(* ================================================================ *)

(* ---------------------------------------------------------------- *)
(*  Eval-over-finite-sum homomorphism.                               *)
(*    poly_eval (sum_range_poly F m) ck                              *)
(*       = sum_range_t (fun j -> poly_eval (F j) ck) m               *)
(*  Eval at a fixed point ck is an add_comm_group hom                *)
(*  polynomial t -> t; this is its action on a finite sum.           *)
(* ---------------------------------------------------------------- *)

(* the t-level summand obtained by evaluating each polynomial summand *)
let eval_at_term (#t:Type) {| f: field t |} (cc: t) (ff: nat -> polynomial t) (j: nat)
  : t
  = poly_eval (ff j) cc

let rec eval_over_sum (#t:Type) {| f: field t |} (cc: t) (ff: nat -> polynomial t) (m: nat)
  : Lemma (ensures
      poly_eval (sum_range ff 0 m) cc
        = sum_range (eval_at_term cc ff) 0 m)
    (decreases m)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if m = 0 then begin
      (* both sums empty *)
      sum_range_empty ff 0 0;
      (* poly_eval poly_zero cc = zero *)
      eval_zero cc;
      eval_congruence (sum_range ff 0 0)
                      (poly_zero #t) cc;
      sum_range_empty (eval_at_term cc ff) 0 0
    end else begin
      (* unfold both sums on the right end *)
      let mp = m - 1 in
      sum_range_unfold_right ff 0 m;
      (* sum_range ff 0 m == sum_range ff 0 mp + ff mp   (in polynomial acg = poly_add) *)
      eval_congruence
        (sum_range ff 0 m)
        (sum_range ff 0 mp + ff mp) cc;
      (* eval_add splits the poly_add *)
      eval_add (sum_range ff 0 mp) (ff mp) cc;
      (* IH on mp *)
      eval_over_sum cc ff mp;
      (* combine: poly_eval (sum ff 0 mp) cc = sum_t (eval_at) 0 mp *)
      add_congruence
        (poly_eval (sum_range ff 0 mp) cc)
        (poly_eval (ff mp) cc)
        (sum_range (eval_at_term cc ff) 0 mp)
        (eval_at_term cc ff mp);
      (* t-level sum unfolds the same way *)
      sum_range_unfold_right (eval_at_term cc ff) 0 m
    end

(* ---------------------------------------------------------------- *)
(*  The Kronecker-collapse target: the t-level function whose value  *)
(*  the sum picks out, written in the `pointwise_mul (kronecker_     *)
(*  delta k) node_value` form that `sum_range_kronecker_in_range`    *)
(*  consumes.                                                        *)
(* ---------------------------------------------------------------- *)

(* node_value g cs j = g(c_j)  (guarded total function) *)
let node_value (#t:Type) {| f: field t |} (g: polynomial t) (cs: list t) (j: nat)
  : t
  = if j < L.length cs then poly_eval g (L.index cs j) else (zero <: t)

(* For every j in range, the evaluated interpolant summand equals
   the Kronecker-masked node value:
     poly_eval (interp_term g cs j) ck
       = kronecker_delta k j * node_value g cs k
   (note: at j=k the factor is one and the value is g(c_k); off it is zero). *)
let interp_term_eval_is_kronecker
  (#t:Type) {| f: field t |} (g: polynomial t) (cs: list t) (k: nat)
  {| sq: squash (all_distinct cs) |}
  (j: nat{j < L.length cs})
  : Lemma (requires k < L.length cs)
          (ensures eval_at_term (L.index cs k) (interp_term g cs #sq) j
                   = pointwise_mul (kronecker_delta k)
                                   (node_value g cs) j)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let ck = L.index cs k in
    let aj = poly_eval g (L.index cs j) in
    (* eval_at_term ... j = poly_eval (interp_term g cs j) ck *)
    (* interp_term g cs j = poly_scale aj (lagrange_basis cs j) *)
    (* poly_eval (poly_scale aj basis_j) ck = aj * poly_eval basis_j ck *)
    eval_scale aj (lagrange_basis cs j #sq) ck;
    (* poly_eval basis_j ck = lagrange_delta_value j k *)
    lagrange_basis_delta cs j k #sq;
    (* aj * poly_eval basis_j ck = aj * lagrange_delta_value j k *)
    mul_congruence aj (poly_eval (lagrange_basis cs j #sq) ck)
                   aj (lagrange_delta_value #t #f j k);
    (* Now show  aj * lagrange_delta_value j k = kronecker_delta k j * node_value g cs k *)
    pointwise_mul_unfold (kronecker_delta k) (node_value g cs) j;
    (* RHS = kronecker_delta k j * node_value g cs j *)
    if j = k then begin
      (* lagrange_delta_value j k = one ;  kronecker_delta k j = one ;
         aj = poly_eval g (index cs k) = node_value g cs k *)
      (* aj * one = aj *)
      H.x_mul_one aj;
      (* node_value g cs k = poly_eval g (index cs k) = aj  (since j=k) *)
      (* kronecker_delta k j * node_value g cs k = one * node_value = node_value *)
      H.one_mul_x (node_value g cs j)
    end else begin
      (* lagrange_delta_value j k = zero ; kronecker_delta k j = zero *)
      (* aj * zero = zero *)
      H.x_mul_zero aj;
      (* zero * node_value = zero *)
      H.zero_mul_x (node_value g cs j)
    end

(* ---------------------------------------------------------------- *)
(*  PRIORITY 1 lemma — interpolant agrees with g at every node.      *)
(* ---------------------------------------------------------------- *)

let lagrange_interpolant_eval_node
  (#t:Type) {| f: field t |} (g: polynomial t) (cs: list t) (k: nat)
  {| sq: squash (all_distinct cs) |}
  : Lemma (requires k < L.length cs)
          (ensures poly_eval (lagrange_interpolant g cs #sq) (L.index cs k)
                   = poly_eval g (L.index cs k))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let n  = L.length cs in
    let ck = L.index cs k in
    (* 1. eval-over-sum hom on the interpolant. *)
    eval_over_sum ck (interp_term g cs #sq) n;
    (* poly_eval interpolant ck = sum_t (eval_at_term ck interp_term) 0 n *)
    (* 2. rewrite the t-level summand to the Kronecker-masked node value. *)
    let lhs : nat -> t = eval_at_term ck (interp_term g cs #sq) in
    let rhs : nat -> t = pointwise_mul (kronecker_delta k)
                                       (node_value g cs) in
    let step (j: nat{0 <= j /\ j < n}) : Lemma (lhs j = rhs j)
      = interp_term_eval_is_kronecker g cs k j
    in
    sum_range_congruence lhs rhs 0 n step;
    (* 3. Kronecker collapse: sum_t rhs 0 n = node_value g cs k. *)
    sum_range_kronecker_in_range k (node_value g cs) 0 n
