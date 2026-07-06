module Core.Polynomial.LagrangeInterpId

(* ================================================================ *)
(*  Lagrange interpolation IDENTITY (uniqueness half, §D).          *)
(*                                                                   *)
(*  For distinct nodes cs and a polynomial g with deg g < #nodes,    *)
(*  the Lagrange interpolant of g equals g:                          *)
(*    g  =  sum_{j<n} g(c_j) . basis_j.                              *)
(*                                                                   *)
(*  Strategy: the interpolant agrees with g at every node            *)
(*  (lagrange_interpolant_eval_node) and has degree < #nodes         *)
(*  (degree-of-sum_range bound); poly_interpolation_unique then      *)
(*  forces poly_eq g interpolant.                                    *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module FS = Core.FinSum
module DV = Core.Polynomial.Div
module SD = Core.Polynomial.SplitDivisor
module LR = Core.Risch.LRT
module UN = Core.Polynomial.Unique

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Roots
open Core.Polynomial.Lagrange
open Core.Polynomial.LagrangeInterp
open Core.Polynomial.RootBound
open Core.Polynomial.DerivPower

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* The commutative_ring on coefficients induced by the field. *)
unfold
let crf (t:Type) {| f: field t |} : commutative_ring t = cr_of_id t #(id_of_f t)

(* ================================================================ *)
(*  Step 1 — memP <-> index bridge for the agreement hypothesis.    *)
(* ================================================================ *)

(* Every member of cs equals some index; convert the index-form        *)
(* node-agreement lemma into the memP-form needed by uniqueness.       *)
let interp_agrees_at_member
  (#t:Type) {| f: field t |} (g: polynomial t) (cs: list t)
  {| sq: squash (all_distinct cs) |}
  (c: t)
  : Lemma (requires L.memP c cs)
          (ensures poly_eval g c
                   = poly_eval (lagrange_interpolant g cs #sq) c)
  = H.elim_equatable_laws t ();
    (* memP c cs  ==>  c == index cs k for some k < length cs *)
    let k = L.index_of cs c in
    (* index_of returns k with index cs k == c *)
    lagrange_interpolant_eval_node g cs k #sq
    (* poly_eval interpolant (index cs k) = poly_eval g (index cs k) *)

(* ================================================================ *)
(*  Step 2 — degree of a single Lagrange basis polynomial.          *)
(*    deg (lagrange_basis cs j) = Some (n-1),  hence  < n.          *)
(* ================================================================ *)

let lagrange_basis_deg_lt
  (#t:Type) {| f: field t |} (cs: list t)
  (j: nat{j < L.length cs})
  {| sq: squash (all_distinct cs) |}
  : Lemma (ensures deg (lagrange_basis cs j #sq) < L.length cs)
  = lagrange_denom_nonzero cs j;
    let d    = lagrange_denom cs j in
    let invd = inv d in
    let numer = lagrange_numer cs j in
    (* numer = poly_prod_linears (delete_index cs j) ; deg = length (delete_index cs j) = n-1 *)
    SD.poly_prod_linears_deg (delete_index cs j);
    delete_index_length cs j;
    (* deg numer = Some (n-1), so deg numer < n. *)
    (* lagrange_basis = poly_scale invd numer ; deg(scale) <= deg numer < n *)
    LR.poly_scale_deg_le invd numer (L.length cs)

(* ================================================================ *)
(*  Step 3 — degree of the interpolant.                             *)
(*    Each summand interp_term g cs j has deg < n (or None);        *)
(*    a degree-of-sum_range induction lifts the bound to the sum.   *)
(* ================================================================ *)

(* Per-summand degree bound, for ALL j (including the out-of-range      *)
(* j where interp_term = poly_zero, deg None).                          *)
let interp_term_deg_lt
  (#t:Type) {| f: field t |} (g: polynomial t) (cs: list t)
  {| sq: squash (all_distinct cs) |}
  (j: nat)
  : Lemma (ensures deg (interp_term g cs j) < L.length cs)
  = if j < L.length cs then begin
      (* interp_term = poly_scale (g cj) (lagrange_basis cs j) *)
      lagrange_basis_deg_lt cs j #sq;
      LR.poly_scale_deg_le (poly_eval g (L.index cs j))
                           (lagrange_basis cs j #sq) (L.length cs)
    end else
      (* interp_term = poly_zero = [] ; deg None (definitional) *)
      ()

(* Generic degree-of-sum_range bound: if every summand of ff over     *)
(* [0,m) has deg < bnd (None or < bnd), so does the partial sum.       *)
let rec sum_range_deg_lt
  (#t:Type) {| f: field t |} (ff: nat -> polynomial t) (m: nat) (bnd: nat)
  : Lemma (requires (forall (j:nat). j < m ==> deg (ff j) < bnd))
          (ensures (let s = FS.sum_range ff 0 m in
                    deg s < bnd))
          (decreases m)
  = if m = 0 then
      (* empty sum = poly_zero, deg None *)
      FS.sum_range_empty #(polynomial t) #(pacg (crf t)) ff 0 0
    else begin
      let mp = m - 1 in
      let acg = pacg (crf t) in
      let s   = FS.sum_range ff 0 m in
      let sp  = FS.sum_range #(polynomial t) #acg ff 0 mp in
      (* sum 0 m  ~  sum 0 mp + ff mp   (the + is acg.add = poly_add) *)
      FS.sum_range_unfold_right ff 0 m;
      (* the group element  sp + ff mp  is poly_add sp (ff mp) *)
      assert (s = (sp + ff mp));
      sum_range_deg_lt #t #f ff mp bnd;
      (* poly_add bound: both deg < bnd ==> deg (poly_add sp (ff mp)) < bnd *)
      DV.poly_add_degree_bound #t #(crf t) sp (ff mp) bnd;
      (* transport the degree bound across poly_eq *)
      UN.degree_well_defined s (poly_add sp (ff mp))
    end

(* The interpolant has degree < #nodes (or None). *)
let lagrange_interpolant_deg_lt
  (#t:Type) {| f: field t |} (g: polynomial t) (cs: list t)
  {| sq: squash (all_distinct cs) |}
  : Lemma (ensures deg (lagrange_interpolant g cs #sq) < L.length cs)
  = let aux (j:nat) : Lemma (j < L.length cs ==>
        deg (interp_term g cs j) < L.length cs) =
      FStar.Classical.move_requires (interp_term_deg_lt g cs #sq) j
    in
    FStar.Classical.forall_intro aux;
    sum_range_deg_lt (interp_term g cs #sq) (L.length cs) (L.length cs)

(* ================================================================ *)
(*  Step 4 — assemble: the interpolation identity.                  *)
(* ================================================================ *)

let lagrange_interpolation
  (#t:Type) {| f: field t |} (g: polynomial t) (cs: list t)
  {| sq: squash (all_distinct cs) |}
  : Lemma (requires deg g < L.length cs)
          (ensures g = (lagrange_interpolant g cs #sq))
  = let interp = lagrange_interpolant g cs in
    (* (a) agreement at every node. *)
    let agree (c:t) : Lemma (requires L.memP c cs)
                            (ensures poly_eval g c = poly_eval interp c) =
      interp_agrees_at_member g cs #sq c
    in
    all_nodes_agree_intro g interp cs agree;
    (* (b) deg interp < #nodes. *)
    lagrange_interpolant_deg_lt g cs #sq;
    (* (c) uniqueness forces equality. *)
    poly_interpolation_unique g interp cs
