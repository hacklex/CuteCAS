module Core.Polynomial.RootBound

(*
   A nonzero polynomial of degree d over a field has AT MOST d distinct roots.

   This is the prerequisite for Lagrange-interpolation uniqueness and is broadly
   reusable.  The proof is the classic induction on the list of roots, peeling a
   linear factor (x - r) at each step via the factor theorem, and re-using the
   distinct-roots / division infrastructure already in Core.Polynomial.Roots.
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module UN = Core.Polynomial.Unique
module DV = Core.Polynomial.Div

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Roots

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* `nonzero_iff_some_deg` (is_nonzero p <==> deg p >= 0) now lives publicly in
   Core.Polynomial.Unique (UN.nonzero_iff_some_deg). *)

(* ---------------------------------------------------------------- *)
(*  Opaque spec predicates (Q1): every listed root vanishes on p,   *)
(*  and p,q agree at every listed node.                             *)
(* ---------------------------------------------------------------- *)

[@@"opaque_to_smt"]
let all_roots_vanish (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  : prop = forall (r:t). L.memP r roots ==> poly_eval p r = zero

let all_roots_vanish_elim (#t:Type) {| f: field t |} (p: polynomial t)
  (roots: list t{all_roots_vanish p roots})
  : Lemma (forall (r:t). L.memP r roots ==> poly_eval p r = zero)
  = reveal_opaque (`%all_roots_vanish) (all_roots_vanish p roots)

let all_roots_vanish_proof (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  = (r:t) -> Lemma (requires L.memP r roots) (ensures poly_eval p r = zero)

let all_roots_vanish_intro (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (proof: all_roots_vanish_proof p roots)
  : Lemma (all_roots_vanish p roots)
  = reveal_opaque (`%all_roots_vanish) (all_roots_vanish p roots);
    let aux (r:t) : Lemma (L.memP r roots ==> poly_eval p r = zero)
      = Classical.move_requires proof r
    in
    Classical.forall_intro aux

[@@"opaque_to_smt"]
let all_nodes_agree (#t:Type) {| f: field t |} (p q: polynomial t) (nodes: list t)
  : prop = forall (c:t). L.memP c nodes ==> poly_eval p c = poly_eval q c

let all_nodes_agree_elim (#t:Type) {| f: field t |} (p q: polynomial t)
  (nodes: list t{all_nodes_agree p q nodes})
  : Lemma (forall (c:t). L.memP c nodes ==> poly_eval p c = poly_eval q c)
  = reveal_opaque (`%all_nodes_agree) (all_nodes_agree p q nodes)

let all_nodes_agree_proof (#t:Type) {| f: field t |} (p q: polynomial t) (nodes: list t)
  = (c:t) -> Lemma (requires L.memP c nodes) (ensures poly_eval p c = poly_eval q c)

let all_nodes_agree_intro (#t:Type) {| f: field t |} (p q: polynomial t) (nodes: list t)
  (proof: all_nodes_agree_proof p q nodes)
  : Lemma (all_nodes_agree p q nodes)
  = reveal_opaque (`%all_nodes_agree) (all_nodes_agree p q nodes);
    let aux (c:t) : Lemma (L.memP c nodes ==> poly_eval p c = poly_eval q c)
      = Classical.move_requires proof c
    in
    Classical.forall_intro aux

(* ================================================================ *)
(*  MAIN LEMMA.                                                      *)
(*    nonzero p, distinct roots all vanishing on p                  *)
(*      ==>  Some? (poly_deg p)  /\  #roots <= deg p.               *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let rec poly_roots_le_degree (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  : Lemma (requires is_nonzero p /\ all_distinct roots /\ all_roots_vanish p roots)
          (ensures deg p >= 0 /\ L.length roots <= deg p)
          (decreases roots)
  = H.elim_equatable_laws t ();
    all_roots_vanish_elim p roots;
    UN.nonzero_iff_some_deg p;                              (* deg p >= 0 *)
    match roots with
    | [] -> ()                                            (* 0 <= deg p *)
    | r :: rest ->
        (* r is a root of p ==> (x - r) | p ==> p ~ (x-r)*q. *)
        let _ : squash (L.memP r roots) = () in
        assert (poly_eval p r = zero);
        factor_forward p r;                               (* divides (x-r) p *)
        let la = poly_linear r in
        eliminate exists (q: polynomial t). (p = (la * q))
        returns deg p >= 0 /\ L.length roots <= deg p
        with _hq.
        begin
          (* q is nonzero, and deg p = 1 + deg q. *)
          mul_linear_nonzero_quotient r p q;              (* deg q >= 0 *)
          UN.nonzero_iff_some_deg q;                       (* is_nonzero q *)
          poly_linear_deg r;                               (* deg la = 1 *)
          deg_mul la q;                    (* deg(la*q) = 1 + deg q *)
          UN.degree_well_defined p (la * q);               (* deg p = deg(la*q) *)
          assert (deg p == (1 ++ deg q));
          (* every element of rest is a root of q. *)
          assert ((forall (d:t). L.memP d rest ==> not (r = d)) /\ all_distinct rest);
          let surv (c:t) : Lemma (requires L.memP c rest)
                                 (ensures poly_eval q c = zero) =
            assert (L.memP c roots);                       (* c in rest ==> c in roots *)
            assert (poly_eval p c = zero);
            assert (not (r = c));                          (* from all_distinct head *)
            H.elim_equatable_laws t ();
            assert (not (c = r));
            root_survives_division r c p q
          in
          all_roots_vanish_intro q rest surv;
          (* IH on q: length rest <= deg q. *)
          poly_roots_le_degree q rest;
          (* length roots = 1 + length rest <= 1 + deg q = deg p. *)
          assert (L.length roots == (1 ++ L.length rest))
        end
#pop-options

(* ================================================================ *)
(*  COROLLARY (the form interpolation uniqueness uses).             *)
(*    distinct roots all vanishing, more roots than the degree      *)
(*      ==>  p is the zero polynomial (poly_eq).                    *)
(* ================================================================ *)

let poly_zero_of_roots_gt_degree (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  : Lemma (requires all_distinct roots /\ all_roots_vanish p roots /\
                    deg p < L.length roots)
          (ensures p = poly_zero)
  = (* contrapositive of the main lemma. *)
    UN.nonzero_iff_some_deg p;
    if is_nonzero p then begin
      (* p nonzero ==> deg p >= 0 ==> the second disjunct holds,
         deg p < length roots; but the main lemma forces length roots <= deg p. *)
      poly_roots_le_degree p roots;
      assert False
    end
    (* not (is_nonzero p) is, by definition, poly_eq p poly_zero. *)

(* ================================================================ *)
(*  POLYNOMIAL INTERPOLATION UNIQUENESS.                            *)
(*    two polynomials of degree < #nodes that agree at all          *)
(*    (distinct) nodes are equal.                                   *)
(* ================================================================ *)

(* (p -- q) vanishes at any node where p and q agree. *)
private let interp_diff_vanishes (#t:Type) {| f: field t |} (p q: polynomial t) (c: t)
  : Lemma (requires poly_eval p c = poly_eval q c)
          (ensures  poly_eval (p -- q) c = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    eval_add p (- q) c;                 (* eval (p--q) c = eval p c + eval (neg q) c *)
    eval_neg q c;                              (* eval (neg q) c = neg (eval q c) *)
    add_congruence (poly_eval p c) (poly_eval (- q) c)
                   (poly_eval p c) (- (poly_eval q c));
    (* eval q c = eval p c, so neg (eval q c) = neg (eval p c). *)
    neg_congruence (poly_eval q c) (poly_eval p c);
    add_congruence (poly_eval p c) (- (poly_eval q c))
                   (poly_eval p c) (- (poly_eval p c));
    H.x_plus_neg_x (poly_eval p c)             (* p(c) + neg p(c) = zero *)

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let poly_interpolation_unique (#t:Type) {| f: field t |} (p q: polynomial t) (nodes: list t)
  : Lemma (requires all_distinct nodes /\
                    deg p < L.length nodes /\
                    deg q < L.length nodes /\
                    all_nodes_agree p q nodes)
          (ensures p = q)
  = all_nodes_agree_elim p q nodes;
    let r = p -- q in
    (* (1) r vanishes at every node. *)
    let vanish (c:t) : Lemma (requires L.memP c nodes)
                             (ensures poly_eval r c = zero) =
      interp_diff_vanishes p q c
    in
    all_roots_vanish_intro r nodes vanish;
    (* (2) deg r < #nodes (or None). *)
    DV.poly_sub_degree_bound p q (L.length nodes);
    (* (3) r ~ poly_zero. *)
    poly_zero_of_roots_gt_degree r nodes;
    (* (4) sub-zero bridge: r = (p -- q) ~ 0  ==>  p ~ q. *)
    UN.sub_zero_implies_eq p q
#pop-options
