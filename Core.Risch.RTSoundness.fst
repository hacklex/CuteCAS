module Core.Risch.RTSoundness

(*
   Rothstein-Trager soundness (tier 2, relative to a given splitting field).

   Goal: the rational-function identity
       d/dx [ Σ_c c · log(v_c) ] = Σ_c c · (v_c' / v_c) = p / q
   where the c are the roots of R(z) = res_x(p - z·q', q) and
   v_c = gcd(p - c·q', q).  Built bottom-up.

   Phase 1 (this file, fraction-free core):
     - poly_deriv_linear     : d/dx (x - a) = 1
     - prod_linears_skip      : ∏_{i≠a}(x - b_i)   (the exact quotient v/(x-a))
     - deriv_prod_linears     : d/dx ∏(x-b_i) = Σ_a ∏_{i≠a}(x-b_i)
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module LRT = Core.Risch.LRT
module LR  = Core.Risch.LRT
module SP  = Core.Polynomial.Roots
module RES = Core.Matrix.Resultant
module RC  = Core.Matrix.Resultant
module GC  = Core.Polynomial.GCD
module SD  = Core.Polynomial.SplitDivisor

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Subst
open Core.Polynomial.Derivative
open Core.Polynomial.Roots
open Core.Polynomial.Roots
open Core.Polynomial.Roots
open Core.Fractions
open Core.Algebra.Divisibility

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  T1.  d/dx (x - a) = 1   (as poly_eq to poly_one).                *)
(* ================================================================ *)

let poly_deriv_linear (#t:Type) {| f: field t |} (a: t)
  : Lemma ((poly_deriv (poly_linear #t #f a)) = (poly_one #t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let _ : squash (not (one #t = zero)) = f.f_one_ne_zero in
    let lin = poly_linear #t #f a in
    poly_linear_deg #t #f a;                       (* deg lin = 1 *)
    let aux (j:nat) : Lemma (coeff (poly_deriv lin) j = coeff (poly_one #t) j) =
      poly_deriv_coeff lin j;                       (* coeff(deriv lin) j = nat_scale (j+1) (coeff lin (j+1)) *)
      if j = 0 then begin
        (* coeff (deriv lin) 0 = nat_scale 1 (coeff lin 1); coeff lin 1 = one = coeff poly_one 0 *)
        nat_scale_one (coeff lin 1);
        (* nat_scale 1 (coeff lin 1) = coeff lin 1, and coeff lin 1 == one == coeff poly_one 0 (defeq) *)
        transitivity (coeff (poly_deriv lin) j)
                     (nat_scale 1 (coeff lin 1))
                     (coeff (poly_one #t) j)
      end else begin
        (* coeff lin (j+1) = zero (deg lin = 1 < j+1) ; nat_scale (j+1) zero = zero = coeff poly_one j *)
        coeff_above_degree lin (j ++ 1);
        nat_scale_zero_element #t (j ++ 1);
        coeff_above_degree (poly_one #t) j;
        nat_scale_congruence (j ++ 1) (coeff lin (j ++ 1)) zero;
        transitivity (coeff (poly_deriv lin) j)
                     (nat_scale (j ++ 1) (coeff lin (j ++ 1)))
                     zero;

        transitivity (coeff (poly_deriv lin) j) zero (coeff (poly_one #t) j)
      end
    in
    poly_eq_by_coeff (poly_deriv lin) (poly_one #t) aux

(* ================================================================ *)
(*  T2.  Leibniz cons-step for ∏ of linear factors.                 *)
(* ================================================================ *)

let deriv_prod_linears_step (#t:Type) {| f: field t |} (a: t) (rest: list t)
  : Lemma ((poly_deriv (poly_prod_linears #t #f (a :: rest)))
                   = ((poly_prod_linears rest)
                     + ((poly_linear a) * (poly_deriv (poly_prod_linears rest)))))
  = H.elim_equatable_laws (polynomial t) ();
    let lin = poly_linear a in
    let w   = poly_prod_linears rest in
    let dw  = poly_deriv w in
    (* poly_prod_linears (a::rest) == lin * w (definitional) *)
    (* (1) Leibniz: D(lin·w) ~ D(lin)·w + lin·D(w) *)
    poly_deriv_mul lin w;
    (* (2) left summand: D(lin)·w ~ poly_one·w ~ w *)
    poly_deriv_linear a;                       (* D(lin) ~ poly_one *)
    reflexivity w;
    mul_congruence (poly_deriv lin) w (poly_one #t) w;  (* D(lin)·w ~ poly_one·w *)
    mul_one w;                                   (* poly_one·w ~ w *)
    transitivity ((poly_deriv lin) * w) ((poly_one #t) * w) w;
    (* (3) add-congruence on the left summand *)
    reflexivity (lin * dw);
    add_congruence ((poly_deriv lin) * w) (lin * dw)
                   w                       (lin * dw);
    (* (4) chain (1) and (3) *)
    transitivity (poly_deriv (lin * w))
                 (((poly_deriv lin) * w) + (lin * dw))
                 (w + (lin * dw))

(* ================================================================ *)
(*  Simple residue: if q ~ (x - b)·w then q'(b) = w(b).             *)
(* ================================================================ *)

let simple_residue (#t:Type) {| f: field t |} (b: t) (w q: polynomial t)
  : Lemma (requires (q = ((poly_linear b) * w)))
          (ensures poly_eval (poly_deriv q) b = poly_eval w b)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let lin = poly_linear b in
    let dlin = poly_deriv lin in
    let dw  = poly_deriv w in
    let lw  = lin * w in
    let leib = (dlin * w) + (lin * dw) in
    let wb  = poly_eval w b in
    let dwb = poly_eval dw b in
    let dlinb = poly_eval dlin b in
    let linb  = poly_eval lin b in
    (* (1) eval (deriv q) b = eval (deriv lw) b *)
    poly_deriv_congruence q lw;                              (* poly_eq (deriv q) (deriv lw) *)
    eval_congruence (poly_deriv q) (poly_deriv lw) b;
    (* (2) deriv lw ~ D(lin)·w + lin·D(w), so eval (deriv lw) b = eval leib b *)
    poly_deriv_mul lin w;
    eval_congruence (poly_deriv lw) leib b;
    transitivity (poly_eval (poly_deriv q) b)
                 (poly_eval (poly_deriv lw) b)
                 (poly_eval leib b);
    (* (3) eval leib b = eval (dlin·w) b + eval (lin·dw) b *)
    eval_add (dlin * w) (lin * dw) b;
    eval_mul dlin w b;                                       (* = dlinb * wb *)
    eval_mul lin dw b;                                       (* = linb * dwb *)
    (* (4) dlinb = one : eval (deriv lin) b = one *)
    poly_deriv_linear b;                               (* poly_eq dlin poly_one *)
    eval_congruence dlin (poly_one #t) b;                    (* dlinb = eval poly_one b *)
    eval_one b;                                           (* eval poly_one b = one *)
    transitivity dlinb (poly_eval (poly_one #t) b) one;
    (* (5) linb = zero *)
    eval_linear_root b;                                      (* linb = zero *)
    (* (6) dlinb * wb = one * wb = wb *)
    mul_congruence dlinb wb one wb;
    H.one_mul_x wb;                                          (* one * wb = wb *)
    transitivity (dlinb * wb) (one * wb) wb;
    (* (7) linb * dwb = zero * dwb = zero *)
    mul_congruence linb dwb zero dwb;
    H.zero_mul_x dwb;                                        (* zero * dwb = zero *)
    transitivity (linb * dwb) (zero * dwb) zero;
    (* (8) eval leib b = eval(dlin·w)b + eval(lin·dw)b = dlinb*wb + linb*dwb *)
    add_congruence (poly_eval (dlin * w) b) (poly_eval (lin * dw) b)
                   (dlinb * wb) (linb * dwb);
    transitivity (poly_eval leib b)
                 (poly_eval (dlin * w) b + poly_eval (lin * dw) b)
                 (dlinb * wb + linb * dwb);
    (* = wb + zero = wb *)
    add_congruence (dlinb * wb) (linb * dwb) wb zero;
    transitivity (poly_eval leib b) (dlinb * wb + linb * dwb) (wb + zero);
    H.x_plus_zero wb;                                        (* wb + zero = wb *)
    transitivity (poly_eval leib b) (wb + zero) wb;
    (* (9) chain: eval (deriv q) b = eval leib b = wb *)
    transitivity (poly_eval (poly_deriv q) b) (poly_eval leib b) wb

(* ================================================================ *)
(*  Interpolation uniqueness:  a polynomial whose degree is below    *)
(*  the number of distinct points at which it vanishes is zero.      *)
(* ================================================================ *)

let rec low_degree_many_roots_zero (#t:Type) {| f: field t |} (r: polynomial t) (roots: list t)
  : Lemma (requires all_distinct roots /\
                    (forall (b:t). L.memP b roots ==> poly_eval r b = zero) /\
                    deg r < L.length roots)
          (ensures (r = (poly_zero #t)))
          (decreases roots)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();

    match roots with
    | [] ->
        (* length roots = 0, so the precondition forces deg r < 0. *)
        assert (deg r < 0);
        Core.Polynomial.Unique.degree_none_poly_eq_zero #t r
    | b :: rest ->
        (* b is a root: (x-b) | r, so r ~ (x-b)*r'. *)
        let _ : squash (L.memP b roots) = () in
        assert (poly_eval r b = zero);
        factor_forward r b;                         (* divides (x-b) r *)
        let la = poly_linear b in
        eliminate exists (q: polynomial t). r = (la * q)
        returns r = (poly_zero #t)
        with _hq.
        begin
          (* all_distinct (b::rest) gives the head distinctness and all_distinct rest. *)
          assert ((forall (d:t). L.memP d rest ==> not (b = d)) /\ all_distinct rest);
          (* (1) remaining roots survive in q. *)
          let rest_roots (c:t) : Lemma (requires L.memP c rest)
                                       (ensures poly_eval q c = zero) =
            assert (L.memP c roots);                       (* c in rest ==> c in roots *)
            assert (poly_eval r c = zero);
            assert (not (b = c));                          (* from all_distinct head *)
            H.elim_equatable_laws t ();

            assert (not (c = b));
            root_survives_division b c r q
          in
          let rest_roots_all (c:t) : Lemma (L.memP c rest ==> poly_eval q c = zero) =
            Classical.move_requires rest_roots c
          in
          Classical.forall_intro rest_roots_all;
          (* (2) degree drop:  deg q >= 0 ==> deg q < length rest. *)
          poly_linear_deg b;                          (* deg la = 1 *)
          if deg q >= 0 then begin
            deg_mul la q;                  (* deg(la*q) = 1 + deg q *)
            Core.Polynomial.Unique.degree_well_defined r (la * q);   (* deg r == deg (la*q) *)
            assert (deg r >= 0);
            assert (deg r == 1 ++ deg q);
            assert (deg r < L.length roots);
            assert (L.length roots == (L.length rest) ++ 1);
            assert (deg q < L.length rest)
          end;
          (* (3) IH on q. *)
          low_degree_many_roots_zero q rest;          (* poly_eq q poly_zero *)
          (* (4) r ~ la*q ~ la*0 ~ 0. *)

          mul_congruence la q la (poly_zero #t);        (* la*q ~ la*0 *)
          transitivity
                       r (la * q) (la * (poly_zero #t));
          H.x_mul_zero la;      (* la*0 ~ 0 *)
          transitivity
                       r (la * (poly_zero #t)) (poly_zero #t)
        end

(* ================================================================ *)
(*  Peel an occurring root b to the front of the product.           *)
(* ================================================================ *)

let rec prod_linears_peel (#t:Type) {| f: field t |} (b: t) (roots: list t)
  : Pure (list t)
         (requires L.memP b roots)
         (ensures fun rest ->
            L.length rest == L.length roots - 1 /\
            (poly_prod_linears roots)
                    = ((poly_linear b) * (poly_prod_linears rest)))
         (decreases roots)
  = H.elim_equatable_laws (polynomial t) ();
    match roots with
    | a :: tl ->
        let la = poly_linear a in
        let lb = poly_linear b in
        if a = b then begin
          (* poly_prod_linears (a::tl) == la * (poly_prod_linears tl). *)
          let ptl = poly_prod_linears tl in
          (* poly_eq la lb : [neg a; one] vs [neg b; one] *)
          neg_congruence a b;                              (* neg a = neg b *)
          assert (la == [(- a); one ]);
          assert (lb == [(- b); one ]);

          assert ((([(- a); one ] <: polynomial t) = ([(- b); one ] <: polynomial t)) ==
                  (((- a) = (- b)) && ((one #t = one #t) && true)))
            by (FStar.Tactics.norm [delta_only [`%poly_eq]; iota; zeta; primops]; FStar.Tactics.trefl ());
          assert (la = lb);
          reflexivity ptl;
          mul_congruence la ptl lb ptl;              (* la*ptl ~ lb*ptl *)
          tl
        end
        else begin
          (* derive L.memP b tl from L.memP b (a::tl) and a<>b. *)
          eliminate (b == a) \/ (L.memP b tl)
          returns L.memP b tl
          with _h_eq.
            (H.leibniz_to_eq b a; symmetry b a)            (* b==a ==> a=b, contradiction *)
          and _h_tl. ();
          let rest' = prod_linears_peel b tl in
          let prest' = poly_prod_linears #t #f rest' in
          let ptl = poly_prod_linears tl in
          (* IH: poly_eq ptl (lb * prest') *)
          (* Goal: poly_eq (la * ptl) (lb * (la * prest')) *)
          (* step 1: la*ptl ~ la*(lb*prest') *)
          reflexivity la;
          mul_congruence la ptl la (lb * prest');
          (* step 2: la*(lb*prest') ~ (la*lb)*prest'  (assoc, reversed) *)
          mul_associativity la lb prest';
          symmetry ((la * lb) * prest') (la * (lb * prest'));
          transitivity (la * ptl)
                       (la * (lb * prest'))
                       ((la * lb) * prest');
          (* step 3: (la*lb)*prest' ~ (lb*la)*prest'  (comm + congruence) *)
          mul_commutativity la lb;
          reflexivity prest';
          mul_congruence (la * lb) prest' (lb * la) prest';
          transitivity (la * ptl)
                       ((la * lb) * prest')
                       ((lb * la) * prest');
          (* step 4: (lb*la)*prest' ~ lb*(la*prest')  (assoc) *)
          mul_associativity lb la prest';
          transitivity (la * ptl)
                       ((lb * la) * prest')
                       (lb * (la * prest'));
          a :: rest'
        end

(* ================================================================ *)
(*  Derivative of the split product, evaluated at one of its roots:  *)
(*    q'(b) = (the cofactor product) evaluated at b = prod_{i!=b}(b - b_i).  *)
(*  Immediate from prod_linears_peel (q ~ (x-b)*cofactor) + simple_residue. *)
(* ================================================================ *)

let deriv_prod_at_root (#t:Type) {| f: field t |} (b: t) (roots: list t)
  : Lemma (requires L.memP b roots)
          (ensures poly_eval (poly_deriv (poly_prod_linears roots)) b
                 = poly_eval (poly_prod_linears (prod_linears_peel b roots)) b)
  = let rest = prod_linears_peel b roots in
    simple_residue b (poly_prod_linears rest) (poly_prod_linears roots)

(* ================================================================ *)
(*  A cofactor vanishes at every OTHER root.                         *)
(*    cof = ∏_{i≠b}(x - b_i) ~ (poly_prod_linears (peel b roots)).   *)
(*  At a distinct root c (c in roots, c<>b):  the whole product       *)
(*  vanishes at c (prod_linears_vanishes), the product factors as     *)
(*  (x-b)*cof, and (x-b)(c) = neg b + c <> 0, so by the domain law    *)
(*  cof(c) = 0.  Discharged directly by root_survives_division with   *)
(*  p := ∏ roots,  q := cof.                                          *)
(* ================================================================ *)

let cofactor_eval_off (#t:Type) {| f: field t |} (b c: t) (roots: list t)
  : Lemma (requires L.memP b roots /\ L.memP c roots /\ not (b = c))
          (ensures poly_eval (poly_prod_linears (prod_linears_peel b roots)) c
                 = zero)
  = H.elim_equatable_laws t ();
    let rest = prod_linears_peel b roots in
    let cof  = poly_prod_linears rest in
    let p    = poly_prod_linears roots in
    (* p ~ (x-b)*cof, from prod_linears_peel's ensures. *)
    assert (p = ((poly_linear b) * cof));
    (* p(c) = 0 since c is a root of the whole product. *)
    prod_linears_vanishes roots c;
    assert (poly_eval p c = zero);
    (* c <> b from not (b = c) by symmetry. *)

    assert (not (c = b));
    (* domain-law argument packaged in root_survives_division. *)
    root_survives_division b c p cof

(* ================================================================ *)
(*  Every factor surviving the peel is distinct from the peeled root. *)
(*    a in (prod_linears_peel b roots)  /\ all_distinct roots         *)
(*      ==>  a <> b.                                                  *)
(*  Mirrors prod_linears_peel's own recursion.                       *)
(* ================================================================ *)

let rec peel_excludes (#t:Type) {| f: field t |} (b a: t) (roots: list t)
  : Lemma (requires L.memP b roots /\ all_distinct roots /\
                    L.memP a (prod_linears_peel b roots))
          (ensures  not (a = b))
          (decreases roots)
  = H.elim_equatable_laws t ();
    match roots with
    | h :: tl ->
        (* all_distinct (h::tl) = (forall d. memP d tl ==> not (h=d)) /\ all_distinct tl *)
        assert ((forall (d:t). L.memP d tl ==> not (h = d)) /\ all_distinct tl);
        if h = b then begin
          (* peel b (h::tl) == tl, so a in tl; distinctness gives not (h = a). *)
          assert (L.memP a tl);
          assert (not (h = a));               (* from the head-distinctness of h::tl *)

          (* h = b (boolean true); if a = b then a = h, contradiction. *)
          if a = b then begin

            transitivity a b h                 (* a = b /\ b = h ==> a = h, contradiction *)
          end
        end
        else begin
          (* peel b (h::tl) == h :: (peel b tl); a in (h :: peel b tl). *)
          (* derive L.memP b tl, as in prod_linears_peel's else-branch. *)
          eliminate (b == h) \/ (L.memP b tl)
          returns L.memP b tl
          with _h_eq.
            (H.leibniz_to_eq b h; symmetry b h)
          and _h_tl. ();
          let rest' = prod_linears_peel b tl in
          (* a == h \/ a in rest'. *)
          eliminate (a == h) \/ (L.memP a rest')
          returns not (a = b)
          with _h_ah.
            (* a == h, and the branch condition is not (h = b). *)
            (H.leibniz_to_eq a h;              (* a = h *)
             if a = b then begin

               transitivity h a b              (* h = a /\ a = b ==> h = b, contradiction *)
             end)
          and _h_ar.
            peel_excludes b a tl
        end

(* ================================================================ *)
(*  ∏_{a in rest}(neg a + b) is nonzero when every a <> b (field).   *)
(*    Induction:  base one <> 0 (f_one_ne_zero); cons via the domain *)
(*    law on nonzero factors (sub_nonzero_of_distinct + domain law). *)
(* ================================================================ *)

let rec eval_prod_sub_nonzero (#t:Type) {| f: field t |} (b: t) (rest: list t)
  : Lemma (requires (forall (a:t). L.memP a rest ==> not (a = b)))
          (ensures  not (eval_prod_sub rest b = zero))
          (decreases rest)
  = H.elim_equatable_laws t ();
    match rest with
    | [] ->
        (* eval_prod_sub [] b == one; one <> zero. *)
        let _ : squash (not (one #t = zero)) = f.f_one_ne_zero in
        ()
    | a :: tl ->
        (* eval_prod_sub (a::tl) b == (neg a + b) * eval_prod_sub tl b. *)
        assert (not (a = b));                      (* a in (a::tl) *)

        sub_nonzero_of_distinct a b;          (* not (neg a + b = zero) *)
        eval_prod_sub_nonzero b tl;           (* IH: tail product nonzero *)
        domain_nonzero_mul_nonzero ((- a) + b) (eval_prod_sub tl b)

(* ================================================================ *)
(*  Main:  q'(b) <> 0 for q = ∏_{a in roots}(x - a), roots distinct.  *)
(*    (residue denominator nonzero.)                                  *)
(*  q'(b) = eval (∏ (peel b roots)) b      (deriv_prod_at_root)       *)
(*        = eval_prod_sub (peel b roots) b (eval_poly_prod_linears)   *)
(*        <> 0                             (every peel factor <> b).  *)
(* ================================================================ *)

let split_deriv_nonzero (#t:Type) {| f: field t |} (b: t) (roots: list t)
  : Lemma (requires L.memP b roots /\ all_distinct roots)
          (ensures  not (poly_eval (poly_deriv (poly_prod_linears roots)) b
                         = zero))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let rest = prod_linears_peel b roots in
    (* q'(b) = eval (∏ rest) b. *)
    deriv_prod_at_root b roots;
    (* eval (∏ rest) b = eval_prod_sub rest b. *)
    eval_poly_prod_linears rest b;
    transitivity (poly_eval (poly_deriv (poly_prod_linears roots)) b)
                 (poly_eval (poly_prod_linears rest) b)
                 (eval_prod_sub rest b);
    (* every factor of rest excludes b. *)
    let peel_off (a:t) : Lemma (L.memP a rest ==> not (a = b)) =
      Classical.move_requires (peel_excludes b a) roots
    in
    Classical.forall_intro peel_off;
    (* product nonzero. *)
    eval_prod_sub_nonzero b rest


(* ================================================================ *)
(*  Residue scalar  r_b = p(b) * inv(q'(b))  with q = prod roots.    *)
(*  inv carries a nonzero precondition; split_deriv_nonzero          *)
(*  discharges it from  memP b roots /\ all_distinct roots.          *)
(* ================================================================ *)

let residue (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (b: t)
  : Pure t (requires L.memP b roots /\ all_distinct roots)
           (ensures fun _ -> True)
  = split_deriv_nonzero b roots;
    poly_eval p b * inv (poly_eval (poly_deriv (poly_prod_linears roots)) b)

(* ================================================================ *)
(*  Residue partial-fraction numerator over a sublist `sub`:         *)
(*    Sum_{b in sub}  r_b * (cofactor product of b).                 *)
(* ================================================================ *)

let rec residue_sum (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (sub: list t)
  : Pure (polynomial t)
         (requires (forall (b:t). L.memP b sub ==> L.memP b roots) /\ all_distinct roots)
         (ensures fun _ -> True)
         (decreases sub)
  = match sub with
    | [] -> poly_zero #t
    | b :: tl ->
        (poly_scale (residue p roots b)
                             (poly_prod_linears (prod_linears_peel b roots)))
                 + (residue_sum p roots tl)

(* ================================================================ *)
(*  Off-root vanishing:  the residue sum over `sub` is zero at any    *)
(*  root c that differs from every element of `sub`.                  *)
(* ================================================================ *)

let rec eval_residue_sum_vanishes (#t:Type) {| f: field t |} (p: polynomial t) (roots sub: list t) (c: t)
  : Lemma (requires (forall (b:t). L.memP b sub ==> L.memP b roots) /\ all_distinct roots /\
                    L.memP c roots /\
                    (forall (b:t). L.memP b sub ==> not (b = c)))
          (ensures poly_eval (residue_sum p roots sub) c = zero)
          (decreases sub)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match sub with
    | [] -> eval_zero c
    | b :: tl ->
        let rb  = residue p roots b in
        let cof = poly_prod_linears (prod_linears_peel b roots) in
        let term = poly_scale rb cof in
        let rest = residue_sum p roots tl in
        eval_add term rest c;
        eval_mul (rb @ poly_zero) cof c;
        let _ : squash (poly_eval (rb @ poly_zero) c = rb) =
          if rb = zero then begin
            eval_zero c;

            transitivity (poly_eval (rb @ poly_zero) c) zero rb
          end else
            eval_singleton rb c in
        mul_congruence (poly_eval (rb @ poly_zero) c) (poly_eval cof c) rb (poly_eval cof c);
        transitivity (poly_eval term c)
                     (poly_eval (rb @ poly_zero) c * poly_eval cof c)
                     (rb * poly_eval cof c);
        cofactor_eval_off b c roots;
        mul_congruence rb (poly_eval cof c) rb zero;
        H.x_mul_zero rb;
        transitivity (rb * poly_eval cof c) (rb * zero) zero;
        transitivity (poly_eval term c) (rb * poly_eval cof c) zero;
        eval_residue_sum_vanishes p roots tl c;
        add_congruence (poly_eval term c) (poly_eval rest c) zero zero;
        H.x_plus_zero #t zero;
        transitivity (poly_eval (residue_sum p roots sub) c)
                     (poly_eval term c + poly_eval rest c)
                     (zero + zero);
        transitivity (poly_eval (residue_sum p roots sub) c)
                     (zero + zero)
                     zero

(* ================================================================ *)
(*  At-root value:  on a distinct sublist `sub` containing c, the     *)
(*  residue sum reproduces  p(c).                                     *)
(* ================================================================ *)

let rec eval_residue_sum_at_root (#t:Type) {| f: field t |} (p: polynomial t) (roots sub: list t) (c: t)
  : Lemma (requires (forall (b:t). L.memP b sub ==> L.memP b roots) /\ all_distinct roots /\
                    all_distinct sub /\ L.memP c sub)
          (ensures poly_eval (residue_sum p roots sub) c = poly_eval p c)
          (decreases sub)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match sub with
    | b :: tl ->
        assert ((forall (d:t). L.memP d tl ==> not (b = d)) /\ all_distinct tl);
        let rb  = residue p roots b in
        let cof = poly_prod_linears (prod_linears_peel b roots) in
        let term = poly_scale rb cof in
        let rest = residue_sum p roots tl in
        eval_add term rest c;
        eval_mul (rb @ poly_zero) cof c;
        let _ : squash (poly_eval (rb @ poly_zero) c = rb) =
          if rb = zero then begin
            eval_zero c;

            transitivity (poly_eval (rb @ poly_zero) c) zero rb
          end else
            eval_singleton rb c in
        mul_congruence (poly_eval (rb @ poly_zero) c) (poly_eval cof c) rb (poly_eval cof c);
        transitivity (poly_eval term c)
                     (poly_eval (rb @ poly_zero) c * poly_eval cof c)
                     (rb * poly_eval cof c);
        if b = c then begin
          (* point congruence (b = c): Core.Polynomial.Eval.eval_point_congruence. *)
          (* tl excludes c (head distinctness, b = c), so eval rest c = 0 *)
          let off (d:t) : Lemma (L.memP d tl ==> not (d = c)) =
            let inner () : Lemma (requires L.memP d tl) (ensures not (d = c)) =
              symmetry b d in
            Classical.move_requires inner () in
          Classical.forall_intro off;
          eval_residue_sum_vanishes p roots tl c;
          (* q'(b) = eval cof b ; with point congruence, eval cof c = eval cof b *)
          deriv_prod_at_root b roots;
          eval_point_congruence cof b c;
          let qd : t = poly_eval (poly_deriv (poly_prod_linears roots)) b in

          transitivity (poly_eval cof c) (poly_eval cof b) qd;
          split_deriv_nonzero b roots;
          let pc : t = poly_eval p b in
          let iq : t = inv qd in
          (* rb == pc * iq  (residue definition, qd is the same denominator) *)
          mul_congruence rb (poly_eval cof c) (pc * iq) qd;
          transitivity (poly_eval term c) (rb * poly_eval cof c) ((pc * iq) * qd);
          mul_associativity pc iq qd;
          inversion_lemma qd;
          mul_congruence pc (iq * qd) pc one;
          H.x_mul_one pc;
          transitivity (pc * (iq * qd)) (pc * one) pc;
          transitivity ((pc * iq) * qd) (pc * (iq * qd)) pc;
          transitivity (poly_eval term c) ((pc * iq) * qd) pc;
          (* eval (term + rest) c = pc + zero = pc = eval p b ; bridge to eval p c *)
          add_congruence (poly_eval term c) (poly_eval rest c) pc zero;
          H.x_plus_zero pc;
          transitivity (poly_eval (residue_sum p roots sub) c)
                       (poly_eval term c + poly_eval rest c)
                       (pc + zero);
          transitivity (poly_eval (residue_sum p roots sub) c)
                       (pc + zero)
                       pc;
          eval_point_congruence p b c;
          transitivity (poly_eval (residue_sum p roots sub) c) pc (poly_eval p c)
        end else begin
          cofactor_eval_off b c roots;
          mul_congruence rb (poly_eval cof c) rb zero;
          H.x_mul_zero rb;
          transitivity (rb * poly_eval cof c) (rb * zero) zero;
          transitivity (poly_eval term c) (rb * poly_eval cof c) zero;
          eliminate (c == b) \/ (L.memP c tl)
          returns L.memP c tl
          with _h_eq. (H.leibniz_to_eq c b; symmetry c b)
          and _h_tl. ();
          eval_residue_sum_at_root p roots tl c;
          add_congruence (poly_eval term c) (poly_eval rest c) zero (poly_eval p c);
          H.zero_plus_x (poly_eval p c);
          transitivity (poly_eval (residue_sum p roots sub) c)
                       (poly_eval term c + poly_eval rest c)
                       (zero + poly_eval p c);
          transitivity (poly_eval (residue_sum p roots sub) c)
                       (zero + poly_eval p c)
                       (poly_eval p c)
        end

(* ================================================================ *)
(*  STEP 1 support.  Degree of a product of linear factors and a     *)
(*  scaled polynomial; degree bound on the residue partial-fraction  *)
(*  numerator.                                                       *)
(* ================================================================ *)

(* deg poly_one = 0 (over a field, one <> zero). *)
let poly_one_deg (#t:Type) {| f: field t |} ()
  : Lemma (deg (poly_one #t) == 0)
  = H.elim_equatable_laws t ();
    let _ : squash (not (one #t = zero)) = f.f_one_ne_zero in
    poly_lc_reveal (poly_one #t)

(* deg (poly_prod_linears roots) = length roots. *)
let rec poly_prod_linears_deg (#t:Type) {| f: field t |} (roots: list t)
  : Lemma (ensures deg (poly_prod_linears roots) == L.length roots)
          (decreases roots)
  = match roots with
    | []        -> poly_one_deg #t #f ()
    | a :: rest ->
        let la = poly_linear a in
        let pr = poly_prod_linears rest in
        poly_linear_deg a;                 (* deg la = 1 *)
        poly_prod_linears_deg rest;        (* IH: deg pr = length rest *)
        deg_mul la pr            (* deg (la*pr) = 1 + length rest *)

(* high coeffs of a scaled poly vanish (mirror of LRTResultant). *)
let coeff_zero_above_k_of_scale_loc (#t:Type) {| f: field t |} (c: t) (qq: polynomial t) (k:nat) (i:nat)
  : Lemma (requires i >= k /\ deg qq < k)
          (ensures coeff (poly_scale c qq) i = zero)
  = H.elim_equatable_laws t ();
    coeff_above_degree qq i;                       (* coeff qq i = zero *)
    poly_mul_singleton_coeff c qq i;               (* coeff (poly_scale c qq) i = c * coeff qq i *)
    H.x_mul_zero c;                                (* c * zero = zero *)

    mul_congruence c (coeff qq i) c zero;
    transitivity (coeff (poly_scale c qq) i) (c * coeff qq i) (c * zero);
    transitivity (coeff (poly_scale c qq) i) (c * zero) zero

(* deg (poly_scale c qq) < k when deg qq < k (mirror of LRTResultant). *)
let poly_scale_deg_le_loc (#t:Type) {| f: field t |} (c: t) (qq: polynomial t) (k:nat)
  : Lemma (requires deg qq < k)
          (ensures deg (poly_scale c qq) < k)
  = if deg (poly_scale c qq) < 0 then ()
    else begin
      let d = deg (poly_scale c qq) in
      if d < k then ()
      else begin
        coeff_zero_above_k_of_scale_loc c qq k d;
        leading_coeff_nonzero (poly_scale c qq)
      end
    end

(* degree bound on the residue partial-fraction numerator over `sub`. *)
let rec residue_sum_degree_bound (#t:Type) {| f: field t |} (p: polynomial t) (roots sub: list t)
  : Lemma (requires (forall (b:t). L.memP b sub ==> L.memP b roots) /\ all_distinct roots)
          (ensures deg (residue_sum p roots sub) < L.length roots)
          (decreases sub)
  = match sub with
    | []      -> ()                                (* residue_sum = poly_zero, deg = -1 *)
    | b :: tl ->
        let rb   = residue p roots b in
        let peel = prod_linears_peel b roots in
        let cof  = poly_prod_linears peel in
        let term = poly_scale rb cof in
        let rest = residue_sum p roots tl in
        (* deg cof = length roots - 1 < length roots. *)
        poly_prod_linears_deg #t #f peel;
        (* term: deg < length roots. *)
        poly_scale_deg_le_loc rb cof (L.length roots);
        (* rest: deg < length roots by IH. *)
        residue_sum_degree_bound p roots tl;
        (* poly_add bound. *)
        poly_add_degree_bound term rest (L.length roots)

(* ================================================================ *)
(*  Group cancellation:  x + (neg y) = zero  ==>  x = y.             *)
(* ================================================================ *)

let lemma_sub_zero_imp_eq (#u:Type) {| g: add_comm_group u |} (x y: u)
  : Lemma (requires (x + (- y)) = zero) (ensures x = y)
  = H.elim_equatable_laws u ();
    H.trans_for_calc u ();
    (* m = (x + neg y) + y *)
    add_associativity x (- y) y;                 (* m = x + (neg y + y) *)
    H.neg_x_plus_x y;                              (* neg y + y = zero *)
    add_congruence x ((- y) + y) x zero;    (* x+(neg y+y) = x+zero *)
    H.x_plus_zero x;                               (* x+zero = x *)
    transitivity ((x + (- y)) + y) (x + ((- y) + y)) (x + zero);
    transitivity ((x + (- y)) + y) (x + zero) x;     (* m = x *)
    add_congruence (x + (- y)) y zero y;    (* m = zero+y *)
    H.zero_plus_x y;                               (* zero+y = y *)
    transitivity ((x + (- y)) + y) (zero + y) y;     (* m = y *)

    transitivity x ((x + (- y)) + y) y             (* x = y *)

(* ================================================================ *)
(*  STEP 2 — CAPSTONE.  Interpolation identity:                      *)
(*    p  ~  Sum_{b in roots} r_b * prod_{i<>b}(x - beta_i)           *)
(*  whenever deg p < #roots and the roots are distinct.              *)
(* ================================================================ *)

let interpolation_identity (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  : Lemma (requires all_distinct roots /\
                    deg p < L.length roots)
          (ensures (p = (residue_sum p roots roots)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();


    let pp = residue_sum p roots roots in
    let d  : polynomial t = (p -- pp) in
    (* (1) d vanishes at every root c. *)
    let vanish (c:t) : Lemma (requires L.memP c roots)
                            (ensures poly_eval d c = zero) =
      eval_residue_sum_at_root p roots roots c;   (* poly_eval pp c = poly_eval p c *)
      eval_add p (- pp) c;                              (* eval d c = eval p c + eval (neg pp) c *)
      eval_neg pp c;                                    (* eval (neg pp) c = neg (eval pp c) *)

      add_congruence (poly_eval p c) (poly_eval (- pp) c)
                     (poly_eval p c) (- (poly_eval pp c));
      transitivity (poly_eval d c)
                   (poly_eval p c + poly_eval (- pp) c)
                   (poly_eval p c + (- (poly_eval pp c)));
      (* eval pp c = eval p c, so neg (eval pp c) = neg (eval p c). *)
      neg_congruence (poly_eval pp c) (poly_eval p c);
      add_congruence (poly_eval p c) (- (poly_eval pp c))
                     (poly_eval p c) (- (poly_eval p c));
      transitivity (poly_eval d c)
                   (poly_eval p c + (- (poly_eval pp c)))
                   (poly_eval p c + (- (poly_eval p c)));
      H.x_plus_neg_x (poly_eval p c);                  (* p(c) + neg p(c) = zero *)
      transitivity (poly_eval d c)
                   (poly_eval p c + (- (poly_eval p c)))
                   zero
    in
    Classical.forall_intro (Classical.move_requires vanish);
    (* (2) degree bound on d. *)
    residue_sum_degree_bound p roots roots;       (* deg pp < #roots *)
    poly_sub_degree_bound p pp (L.length roots);
    (* (3) interpolation uniqueness: d ~ poly_zero. *)
    low_degree_many_roots_zero d roots;
    (* (4) d = poly_add p (poly_neg pp) ~ 0  ==>  p ~ pp. *)
    lemma_sub_zero_imp_eq p pp

(* ================================================================ *)
(*  FRACTION-LEVEL WRAP.  The polynomial interpolation identity       *)
(*    p ~ residue_sum p roots roots   (interpolation_identity)        *)
(*  lifts to an equality of rational functions over the common        *)
(*  denominator q = prod roots:  p/q = P/q  as elements of            *)
(*    fraction (polynomial_id #t).                       *)
(* ================================================================ *)

(* The product of linear factors is a nonzero denominator whenever     *)
(* roots is nonempty:  deg = length roots >= 1, so it is              *)
(* not poly_eq to poly_zero (whose degree is -1).                     *)
let prod_linears_nonzero (#t:Type) {| f: field t |} (roots: list t)
  : Lemma (requires Cons? roots)
          (ensures  is_nonzero (poly_prod_linears roots))
  = let q = poly_prod_linears roots in
    poly_prod_linears_deg roots;                 (* deg q == length roots *)
    (* if q were poly_eq poly_zero, degree_well_defined forces deg q == deg poly_zero == -1. *)
    let aux () : Lemma (requires (q = (poly_zero #t))) (ensures False) =
      Core.Polynomial.Unique.degree_well_defined q (poly_zero #t);
      assert (deg (poly_zero #t) == -1)
    in
    Classical.move_requires aux ()

(* The same-denominator fraction wrap.  With q = prod roots (nonzero), the     *)
(* fractions p/q and P/q (P = residue_sum p roots roots) are equal as elements *)
(* of fraction over the polynomial integral domain.  By fraction_eq_reveal the *)
(* equality reduces to the cross-product  p * q = q * P  in poly_mul/poly_eq;  *)
(* interpolation_identity gives poly_eq p P, and a comm+congruence chain gives *)
(* poly_eq (poly_mul p q) (poly_mul q P).                                      *)
let pf_same_denom (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  : Lemma (requires Cons? roots /\ all_distinct roots /\
                    deg p < L.length roots)
          (ensures (let id_p = polynomial_id #t in
                    is_nonzero (poly_prod_linears roots) /\
                    (let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
                     (Fraction p q)
                       = (Fraction #(polynomial t) #id_p (residue_sum #t #f p roots roots) q))))
  = let id_p = polynomial_id #t in
    prod_linears_nonzero roots;
    let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
    let pp = residue_sum p roots roots in
    let xf : fraction id_p = Fraction p q in
    let yf : fraction id_p = Fraction pp q in
    (* poly_eq p pp from the interpolation identity. *)
    interpolation_identity p roots;              (* poly_eq p pp *)
    (* poly_eq (p*q) (q*pp):  p*q ~ q*p ~ q*pp. *)
    H.elim_equatable_laws (polynomial t) ();
    mul_commutativity p q;                     (* p*q ~ q*p *)
    reflexivity q;
    mul_congruence q p q pp;                   (* q*p ~ q*pp *)
    transitivity (p * q) (q * p) (q * pp);
    (* fraction_eq_reveal:  (xf = yf) <==> (num xf * den yf = den xf * num yf) *)
    (*   num xf = p, den yf = q, den xf = q, num yf = pp.                       *)
    fraction_eq_reveal xf yf


(* ================================================================ *)
(*  poly_linear b is a nonzero polynomial (deg = 1).                *)
(* ================================================================ *)
let poly_linear_nonzero (#t:Type) {| f: field t |} (b: t)
  : Lemma (ensures is_nonzero (poly_linear b))
  = let lb = poly_linear b in
    poly_linear_deg b;                           (* deg lb == 1 *)
    let aux () : Lemma (requires (lb = (poly_zero #t))) (ensures False) =
      Core.Polynomial.Unique.degree_well_defined #t lb (poly_zero #t);
      assert (deg (poly_zero #t) == -1)
    in
    Classical.move_requires aux ()

(* ================================================================ *)
(*  One residue term over the common denominator q = prod roots      *)
(*  equals the simple fraction  residue_b / (x - beta_b).            *)
(*  By fraction_eq_reveal this reduces to the cross product           *)
(*    (residue_b * cof) * (x-b)  ~  q * [residue_b]                  *)
(*  with q ~ (x-b) * cof from prod_linears_peel; closed by a         *)
(*  comm/assoc/congruence chain in poly_mul/poly_eq.                 *)
(* ================================================================ *)
let residue_term_as_simple (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (b: t)
  : Lemma (requires L.memP b roots /\ all_distinct roots)
          (ensures (let id_p = polynomial_id #t in
                    is_nonzero (poly_prod_linears roots) /\
                    is_nonzero (poly_linear b) /\
                    (let q  : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
                     let lb : (ll:polynomial t{is_nonzero ll}) = poly_linear b in
                     let cof = poly_prod_linears (prod_linears_peel b roots) in
                     let rb : t = residue p roots b in
                     (Fraction (poly_scale rb cof) q)
                       = (Fraction #(polynomial t) #id_p (rb @ poly_zero) lb))))
  = let id_p = polynomial_id #t in
    (* nonzero denominators. *)
    prod_linears_nonzero roots;
    poly_linear_nonzero b;
    let q  : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
    let lb : (ll:polynomial t{is_nonzero ll}) = poly_linear b in
    let peel = prod_linears_peel b roots in      (* poly_eq roots-prod  (lb * cof) *)
    let cof = poly_prod_linears peel in
    let rb  = residue p roots b in
    let r1  = rb @ poly_zero in                        (* the singleton [rb] *)
    (* poly_scale rb cof == r1 * cof, definitionally. *)
    assert (poly_scale rb cof == r1 * cof);
    H.elim_equatable_laws (polynomial t) ();
    (* Cross-product goal (poly_eq):                                   *)
    (*   (r1 * cof) * lb  ~  q * r1                                    *)
    (* via the chain  (r1*cof)*lb ~ r1*(cof*lb) ~ r1*(lb*cof)          *)
    (*               ~ (lb*cof)*r1 ~ q*r1.                             *)
    (* step 1: (r1*cof)*lb ~ r1*(cof*lb)  (assoc). *)
    mul_associativity r1 cof lb;
    (* step 2: cof*lb ~ lb*cof,  congr with refl r1. *)
    mul_commutativity cof lb;
    reflexivity r1;
    mul_congruence r1 (cof * lb) r1 (lb * cof);
    transitivity ((r1 * cof) * lb)
                 (r1 * (cof * lb))
                 (r1 * (lb * cof));
    (* step 3: r1*(lb*cof) ~ (lb*cof)*r1  (comm). *)
    mul_commutativity r1 (lb * cof);
    transitivity ((r1 * cof) * lb)
                 (r1 * (lb * cof))
                 ((lb * cof) * r1);
    (* step 4: (lb*cof)*r1 ~ q*r1,  from q ~ lb*cof (peel, already in *)
    (* scope via cof's definition) reversed. *)
    symmetry q (lb * cof);
    reflexivity r1;
    mul_congruence (lb * cof) r1 q r1;
    transitivity ((r1 * cof) * lb)
                 ((lb * cof) * r1)
                 (q * r1);
    (* hence poly_eq (poly_mul (poly_scale rb cof) lb) (poly_mul q r1). *)
    (* fraction_eq_reveal: (xf = yf) <==> num xf * den yf = den xf * num yf *)
    (*   num xf = poly_scale rb cof,  den yf = lb,  den xf = q,  num yf = r1. *)
    let xf : fraction id_p = Fraction (poly_scale rb cof) q in
    let yf : fraction id_p = Fraction r1 lb in
    fraction_eq_reveal xf yf

(* ================================================================ *)
(*  FRACTION ASSEMBLY.  Build  p/q = Sum_b residue_b/(x - beta_b)    *)
(*  as an identity of `fraction id_p`, using the NAMED constructors  *)
(*  fraction_add / fraction_zero (reasoned about through the two     *)
(*  reveals fraction_add_reveal / fraction_eq_reveal).               *)
(* ================================================================ *)

(* Pure cross-product identity behind left-congruence.  Stated with the   *)
(* hypothesis as an explicit `squash` binder so canon_ring_subst_auto can  *)
(* find and substitute it.                                                 *)
let frac_add_cong_cross (#t:Type) {| d: integral_domain t |}
                        (n1 d1 n2 d2 yn yd: t)
                        (h: squash ((n1 * d2) = (d1 * n2)))
  : Lemma (((n1 * yd + d1 * yn) * (d2 * yd))
             = ((d1 * yd) * (n2 * yd + d2 * yn)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    (* expand both sides into  key-term + common-term (pure ring) *)
    assert (((n1 * yd + d1 * yn) * (d2 * yd))
              = (n1 * d2) * (yd * yd) + (d1 * d2) * (yn * yd))
      by Core.Tactics.CanonRing.canon_ring ();
    assert (((d1 * yd) * (n2 * yd + d2 * yn))
              = (d1 * n2) * (yd * yd) + (d1 * d2) * (yn * yd))
      by Core.Tactics.CanonRing.canon_ring ();
    (* the two key-terms agree because  n1*d2 = d1*n2  (hypothesis h) *)

    mul_congruence (n1 * d2) (yd * yd) (d1 * n2) (yd * yd);

    add_congruence ((n1 * d2) * (yd * yd)) ((d1 * d2) * (yn * yd))
                   ((d1 * n2) * (yd * yd)) ((d1 * d2) * (yn * yd));
    transitivity ((n1 * yd + d1 * yn) * (d2 * yd))
                 ((n1 * d2) * (yd * yd) + (d1 * d2) * (yn * yd))
                 ((d1 * n2) * (yd * yd) + (d1 * d2) * (yn * yd));
    symmetry ((d1 * yd) * (n2 * yd + d2 * yn))
             ((d1 * n2) * (yd * yd) + (d1 * d2) * (yn * yd));
    transitivity ((n1 * yd + d1 * yn) * (d2 * yd))
                 ((d1 * n2) * (yd * yd) + (d1 * d2) * (yn * yd))
                 ((d1 * yd) * (n2 * yd + d2 * yn))

(* Left-congruence of fraction_add under fraction `=`.               *)
let frac_add_cong (#t:Type) {| d: integral_domain t |} (x1 x2 y: fraction d)
  : Lemma (requires x1 = x2)
          (ensures  fraction_add x1 y = fraction_add x2 y)
  = let s1 = fraction_add x1 y in
    let s2 = fraction_add x2 y in
    fraction_add_reveal x1 y;                          (* num/den s1 *)
    fraction_add_reveal x2 y;                          (* num/den s2 *)
    fraction_eq_reveal s1 s2;                          (* goal <==> cross product *)
    fraction_eq_reveal x1 x2;                          (* x1.num*x2.den = x1.den*x2.num *)
    frac_add_cong_cross x1.num x1.den x2.num x2.den y.num y.den ()

(* Pure cross-product identity behind commutativity of fraction_add. *)
let frac_add_comm_cross (#t:Type) {| d: integral_domain t |}
                        (a b c e: t)
  : Lemma (((a * e + b * c) * (e * b))
             = ((b * e) * (c * b + e * a)))
  = assert (((a * e + b * c) * (e * b))
              = ((b * e) * (c * b + e * a)))
      by Core.Tactics.CanonRing.canon_ring ()

(* Commutativity of fraction_add (the library's version is private).  *)
let frac_add_comm (#t:Type) {| d: integral_domain t |} (x y: fraction d)
  : Lemma (fraction_add x y = fraction_add y x)
  = let s1 = fraction_add x y in
    let s2 = fraction_add y x in
    fraction_add_reveal x y;                           (* num s1 = x.num*y.den + x.den*y.num, den = x.den*y.den *)
    fraction_add_reveal y x;                           (* num s2 = y.num*x.den + y.den*x.num, den = y.den*x.den *)
    fraction_eq_reveal s1 s2;                          (* goal <==> cross product *)
    frac_add_comm_cross x.num x.den y.num y.den

let frac_add_cong_r (#t:Type) {| d: integral_domain t |} (x y1 y2: fraction d)
  : Lemma (requires y1 = y2)
          (ensures  fraction_add x y1 = fraction_add x y2)
  = H.elim_equatable_laws (fraction d) ();
    H.trans_for_calc (fraction d) ();
    frac_add_comm x y1;                                (* x+y1 = y1+x *)
    frac_add_cong y1 y2 x;                             (* y1+x = y2+x *)
    frac_add_comm y2 x;                                (* y2+x = x+y2 *)
    transitivity (fraction_add x y1) (fraction_add y1 x) (fraction_add y2 x);
    transitivity (fraction_add x y1) (fraction_add y2 x) (fraction_add x y2)

(* Pure cross-product identity behind same-denominator splitting.     *)
let frac_split_cross (#t:Type) {| d: integral_domain t |} (a b q: t)
  : Lemma (((a + b) * (q * q)) = (q * (a * q + q * b)))
  = assert (((a + b) * (q * q)) = (q * (a * q + q * b)))
      by Core.Tactics.CanonRing.canon_ring ()

(* Combine two same-denominator fractions:  (a+b)/q = a/q (+) b/q.    *)
let frac_split_same_denom (#t:Type) {| f: field t |}
                          (a b: polynomial t)
                          (q: polynomial t{is_nonzero q})
  : Lemma (let id_p = polynomial_id #t in
           (Fraction (a + b) q)
             = (fraction_add #(polynomial t) #id_p
                  (Fraction a q)
                  (Fraction b q)))
  = let id_p = polynomial_id #t in
    let xa : fraction id_p = Fraction a q in
    let xb : fraction id_p = Fraction b q in
    let lhs : fraction id_p = Fraction (a + b) q in
    let rhs : fraction id_p = fraction_add xa xb in
    fraction_add_reveal xa xb;   (* num rhs = a*q + q*b, den rhs = q*q *)
    fraction_eq_reveal lhs rhs;  (* goal <==> cross product *)
    frac_split_cross a b q

(* ================================================================ *)
(*  The simple fraction  residue_b / (x - beta_b)  for one root b.    *)
(* ================================================================ *)
let simple_term (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (b: t)
  : Pure (fraction (polynomial_id #t))
         (requires L.memP b roots /\ all_distinct roots)
         (ensures fun _ -> True)
  = poly_linear_nonzero b;
    Fraction ((residue p roots b) @ poly_zero) (poly_linear b)

(* ================================================================ *)
(*  The fraction-level residue sum over a sublist `sub`:              *)
(*    Sum_{b in sub}  residue_b / (x - beta_b)                        *)
(*  built with the NAMED constructors fraction_add / fraction_zero.   *)
(* ================================================================ *)
let rec frac_sum (#t:Type) {| f: field t |} (p: polynomial t) (roots sub: list t)
  : Pure (fraction (polynomial_id #t))
         (requires (forall (b:t). L.memP b sub ==> L.memP b roots) /\ all_distinct roots)
         (ensures fun _ -> True)
         (decreases sub)
  = match sub with
    | [] -> fraction_zero (polynomial t)
    | b :: tl -> fraction_add (simple_term p roots b) (frac_sum p roots tl)

(* ================================================================ *)
(*  Base-case cross product:  poly_zero / q  =  fraction_zero.        *)
(*    via fraction_eq_reveal the goal is  0 * 1  =  q * 0  (both 0).   *)
(* ================================================================ *)
let frac_zero_cross (#t:Type) {| d: integral_domain t |} (q: t)
  : Lemma (((zero <: t) * (one <: t)) = (q * (zero <: t)))
  = assert (((zero <: t) * (one <: t)) = (q * (zero <: t)))
      by Core.Tactics.CanonRing.canon_ring ()

(* ================================================================ *)
(*  INDUCTION.  The polynomial residue-sum numerator over the common   *)
(*  denominator q = prod roots equals the fraction-level residue sum:  *)
(*    residue_sum p roots sub / q   =   frac_sum p roots sub.          *)
(* ================================================================ *)
let rec residue_sum_frac_decomp (#t:Type) {| f: field t |}
                                (p: polynomial t) (roots sub: list t)
  : Lemma (requires Cons? roots /\
                    (forall (b:t). L.memP b sub ==> L.memP b roots) /\
                    all_distinct roots)
          (ensures (let id_p = polynomial_id #t in
                    is_nonzero (poly_prod_linears roots) /\
                    (let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
                     (Fraction (residue_sum p roots sub) q)
                       = (frac_sum p roots sub))))
          (decreases sub)
  = let id_p = polynomial_id #t in
    prod_linears_nonzero roots;
    let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    match sub with
    | [] ->
        (* Fraction poly_zero q  =  fraction_zero (polynomial t). *)
        let w  : fraction id_p = Fraction (poly_zero #t) q in
        let fz : fraction id_p = fraction_zero (polynomial t) #id_p in
        fraction_zero_reveal (polynomial t) #id_p;        (* fz.num = poly_zero, fz.den = poly_one *)
        fraction_eq_reveal w fz;    (* goal <==> poly_zero*poly_one = q*poly_zero *)
        frac_zero_cross q
    | b :: tl ->
        let rb   = residue p roots b in
        let term = poly_scale rb (poly_prod_linears (prod_linears_peel b roots)) in
        let rest = residue_sum p roots tl in
        (* residue_sum p roots (b::tl) == poly_add term rest  (definitional). *)
        let fterm : fraction id_p = Fraction term q in
        let frest : fraction id_p = Fraction rest q in
        let st    : fraction id_p = simple_term p roots b in
        (* (1) split the same-denominator sum. *)
        frac_split_same_denom term rest q;          (* Fraction (term + rest) q = fterm (+) frest *)
        (* (2) the b-residue term over q is the simple fraction st. *)
        residue_term_as_simple p roots b;           (* fterm = st *)
        frac_add_cong fterm st frest;  (* fterm(+)frest = st(+)frest *)
        (* (3) inductive hypothesis on the tail. *)
        residue_sum_frac_decomp p roots tl;         (* frest = frac_sum tl *)
        frac_add_cong_r st frest (frac_sum p roots tl);
        (* chain:  Fraction (term + rest) q
                     = fterm(+)frest = st(+)frest = st(+)frac_sum tl = frac_sum (b::tl). *)
        transitivity (Fraction (term + rest) q)
                     (fraction_add #(polynomial t) #id_p fterm frest)
                     (fraction_add st frest);
        transitivity (Fraction (term + rest) q)
                     (fraction_add st frest)
                     (fraction_add st (frac_sum p roots tl))

(* ================================================================ *)
(*  CAPSTONE.  Fraction-level partial-fraction decomposition:         *)
(*    p / q  =  Sum_{b in roots} (p(b)/q'(b)) / (x - b)               *)
(*  whenever deg p < #roots and the roots are distinct.               *)
(* ================================================================ *)
let partial_fraction_decomposition (#t:Type) {| f: field t |}
                                   (p: polynomial t) (roots: list t)
  : Lemma (requires Cons? roots /\ all_distinct roots /\
                    deg p < L.length roots)
          (ensures (let id_p = polynomial_id #t in
                    is_nonzero (poly_prod_linears roots) /\
                    (let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
                     (Fraction p q)
                       = (frac_sum p roots roots))))
  = let id_p = polynomial_id #t in
    prod_linears_nonzero roots;
    let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    (* p/q = (residue_sum p roots roots)/q *)
    pf_same_denom p roots;
    (* (residue_sum p roots roots)/q = frac_sum p roots roots *)
    residue_sum_frac_decomp p roots roots;
    transitivity (Fraction p q)
                 (Fraction (residue_sum p roots roots) q)
                 (frac_sum p roots roots)

(* ================================================================ *)
(*  Logarithmic-derivative residues.                                  *)
(*  For v = prod_linears roots, the residue of v' at each root is 1.  *)
(* ================================================================ *)

(* Lemma 1.  residue(v') at b = 1, where v = poly_prod_linears roots. *)
let residue_of_deriv_is_one (#t:Type) {| f: field t |} (roots: list t) (b: t)
  : Lemma (requires L.memP b roots /\ all_distinct roots)
          (ensures residue (poly_deriv (poly_prod_linears roots)) roots b = one)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    (* x := q'(b), the denominator value; it is nonzero. *)
    let x : t = poly_eval (poly_deriv (poly_prod_linears roots)) b in
    split_deriv_nonzero b roots;                 (* not (x = zero), i.e. is_nonzero x *)
    (* residue (poly_deriv v) roots b
         = poly_eval (poly_deriv v) b * inv x = x * inv x   (defeq: poly_deriv v == poly_deriv (poly_prod_linears roots)). *)
    inversion_lemma x                    (* x * (inv x) = one *)

(* ================================================================ *)
(*  Generic degree upper bound for the derivative.                    *)
(*  If deg(D p) = Some m then m < deg p (when deg p is Some n>=1).     *)
(*  Mirrors the char0-free upper-bound branch of poly_deriv_degree.   *)
(* ================================================================ *)

let poly_deriv_deg_lt (#t:Type) {| f: field t |} (p: polynomial t)
  : Lemma (requires deg p >= 1)
          (ensures deg (poly_deriv p) < deg p)
  = H.elim_equatable_laws t ();
    let n = deg p in
    let dp = poly_deriv p in
    if deg dp >= 0 then begin
      let m = deg dp in
      if m >= n then begin
        (* leading coeff of dp at m is nonzero ... *)
        leading_coeff_nonzero dp;
        (* ... but coeff dp m = nat_scale (m+1) (coeff p (m+1)) = nat_scale (m+1) zero = zero. *)
        poly_deriv_coeff p m;
        coeff_above_degree p (m ++ 1);   (* coeff p (m+1) = zero  (m+1 > n) *)
        nat_scale_congruence (m ++ 1) (coeff p (m ++ 1)) zero;
        nat_scale_zero_element #t (m ++ 1);
        transitivity (coeff dp m)
                     (nat_scale (m ++ 1) (coeff p (m ++ 1)))
                     (nat_scale (m ++ 1) zero);
        transitivity (coeff dp m)
                     (nat_scale (m ++ 1) zero)
                     zero
      end else ()
    end else ()

(* ================================================================ *)
(*  Lemma 2.  Partial-fraction form of the logarithmic derivative:    *)
(*    v'/v = frac_sum of v' over the roots, for v = prod_linears.     *)
(* ================================================================ *)

let log_deriv_prod_linears (#t:Type) {| f: field t |} (roots: list t)
  : Lemma (requires Cons? roots /\ all_distinct roots)
          (ensures (let id_p = polynomial_id #t in
                    is_nonzero (poly_prod_linears roots) /\
                    (let v : (vv:polynomial t{is_nonzero vv}) = poly_prod_linears roots in
                     (Fraction (poly_deriv (poly_prod_linears roots)) v)
                       = (frac_sum (poly_deriv (poly_prod_linears roots)) roots roots))))
  = let v = poly_prod_linears roots in
    let pd = poly_deriv v in
    (* deg v = length roots, and length roots >= 1 since Cons? roots. *)
    poly_prod_linears_deg roots;
    (* discharge the degree precondition of partial_fraction_decomposition for p = pd:
       deg v = length roots >= 1, so deg(deriv v) < length roots. *)
    poly_deriv_deg_lt v;
    partial_fraction_decomposition pd roots

(* ================================================================ *)
(*  Scaled logarithmic-derivative residues.                          *)
(*  For v = prod_linears roots, the residue of (c.v') at each root    *)
(*  is the constant c.                                                *)
(* ================================================================ *)

(* Lemma 1.  residue(c.v') at b = c, where v = poly_prod_linears roots. *)
let residue_of_scaled_deriv_is_const (#t:Type) {| f: field t |} (c: t) (roots: list t) (b: t)
  : Lemma (requires L.memP b roots /\ all_distinct roots)
          (ensures residue (poly_scale c (poly_deriv (poly_prod_linears roots))) roots b = c)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pd = poly_deriv (poly_prod_linears roots) in
    let x : t = poly_eval pd b in
    split_deriv_nonzero b roots;                 (* not (x = zero), i.e. is_nonzero x *)
    let p = poly_scale c pd in
    (* poly_eval p b = poly_eval (c @ poly_zero) b * x. *)
    eval_mul (c @ poly_zero) pd b;
    (* poly_eval (c @ poly_zero) b = c. *)
    let _ : squash (poly_eval (c @ poly_zero) b = c) =
      if c = zero then begin
        eval_zero b;

        transitivity (poly_eval (c @ poly_zero) b) zero c
      end else
        eval_singleton c b in
    (* poly_eval p b = c * x. *)
    mul_congruence (poly_eval (c @ poly_zero) b) x c x;
    transitivity (poly_eval p b)
                 (poly_eval (c @ poly_zero) b * x)
                 (c * x);
    (* residue p roots b = poly_eval p b * inv x = (c*x) * inv x. *)
    let ix = inv x in
    mul_congruence (poly_eval p b) ix (c * x) ix;
    (* (c*x)*inv x = c*(x*inv x). *)
    mul_associativity c x ix;
    (* x*inv x = one. *)
    inversion_lemma x;
    mul_congruence c (x * ix) c one;
    (* c*one = c. *)
    H.x_mul_one c;
    (* chain. *)
    transitivity (residue p roots b) (poly_eval p b * ix) ((c * x) * ix);
    transitivity ((c * x) * ix) (c * (x * ix)) (c * one);
    transitivity (c * (x * ix)) (c * one) c;
    transitivity ((c * x) * ix) (c * (x * ix)) c;
    transitivity (residue p roots b) ((c * x) * ix) c

(* ================================================================ *)
(*  Lemma 2.  Partial-fraction form of the scaled log-derivative:     *)
(*    (c.v')/v = frac_sum of (c.v') over the roots, for v = prod.      *)
(* ================================================================ *)

let scaled_log_deriv (#t:Type) {| f: field t |} (c: t) (roots: list t)
  : Lemma (requires Cons? roots /\ all_distinct roots)
          (ensures (let id_p = polynomial_id #t in
                    is_nonzero (poly_prod_linears roots) /\
                    (let v : (vv:polynomial t{is_nonzero vv}) = poly_prod_linears roots in
                     (Fraction #(polynomial t) #id_p
                        (poly_scale c (poly_deriv (poly_prod_linears roots))) v)
                       = (frac_sum (poly_scale c (poly_deriv (poly_prod_linears roots))) roots roots))))
  = let v = poly_prod_linears roots in
    let pd = poly_deriv v in
    let p = poly_scale c pd in
    (* deg v = length roots, and length roots >= 1 since Cons? roots. *)
    poly_prod_linears_deg roots;
    (* discharge the degree precondition of partial_fraction_decomposition for p:
       deg v = length roots >= 1, so deg(deriv v) < length roots, and scaling
       keeps deg (poly_scale c pd) < length roots. *)
    poly_deriv_deg_lt v;
    poly_scale_deg_le_loc c pd (L.length roots);
    partial_fraction_decomposition p roots

(* ================================================================ *)
(*  FRACTION ADDITION LAWS (left identity, associativity) and the     *)
(*  consequent distribution of frac_sum over list concatenation.       *)
(* ================================================================ *)

(* Pure cross-product identity behind the left identity of fraction_add. *)
(*   num(0/1 (+) x) = 0*xd + 1*xn,  den = 1*xd ; goal <==> cross product. *)
let frac_add_zero_l_cross (#t:Type) {| d: integral_domain t |} (xn xd: t)
  : Lemma ((((zero <: t) * xd + (one <: t) * xn) * xd)
             = (((one <: t) * xd) * xn))
  = assert ((((zero <: t) * xd + (one <: t) * xn) * xd)
              = (((one <: t) * xd) * xn))
      by Core.Tactics.CanonRing.canon_ring ()

(* Helper A.  Left identity of fraction_add. *)
let frac_add_zero_l (#t:Type) {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_add (fraction_zero t #d) x = x)
  = let fz : fraction d = fraction_zero t #d in
    let s  : fraction d = fraction_add fz x in
    fraction_add_reveal fz x;                 (* num s = fz.num*x.den + fz.den*x.num, den s = fz.den*x.den *)
    fraction_zero_reveal t #d;                (* fz.num = zero, fz.den = one *)
    fraction_eq_reveal s x;                   (* goal <==> num s * x.den = den s * x.num *)
    frac_add_zero_l_cross x.num x.den

(* Pure cross-product identity behind associativity of fraction_add.      *)
(*   LHS = (x (+) y) (+) z, RHS = x (+) (y (+) z).                         *)
(*   num L = (a*dd + b*c)*f + (b*dd)*e,  den L = (b*dd)*f                  *)
(*   num R = a*(dd*f) + b*(c*f + dd*e),  den R = b*(dd*f)                  *)
(*   goal <==> num L * den R = den L * num R.                             *)
let frac_add_assoc_cross (#t:Type) {| d: integral_domain t |}
                         (a b c dd e f: t)
  : Lemma ((((a * dd + b * c) * f + (b * dd) * e) * (b * (dd * f)))
             = (((b * dd) * f) * (a * (dd * f) + b * (c * f + dd * e))))
  = assert ((((a * dd + b * c) * f + (b * dd) * e) * (b * (dd * f)))
              = (((b * dd) * f) * (a * (dd * f) + b * (c * f + dd * e))))
      by Core.Tactics.CanonRing.canon_ring ()

(* Helper B.  Associativity of fraction_add. *)
let frac_add_assoc (#t:Type) {| d: integral_domain t |} (x y z: fraction d)
  : Lemma (fraction_add (fraction_add x y) z
             = fraction_add x (fraction_add y z))
  = let xy = fraction_add x y in
    let yz = fraction_add y z in
    let lhs = fraction_add xy z in
    let rhs = fraction_add x yz in
    fraction_add_reveal x y;                  (* num/den xy *)
    fraction_add_reveal y z;                  (* num/den yz *)
    fraction_add_reveal xy z;                 (* num/den lhs *)
    fraction_add_reveal x yz;                 (* num/den rhs *)
    fraction_eq_reveal lhs rhs;               (* goal <==> num lhs * den rhs = den lhs * num rhs *)
    frac_add_assoc_cross x.num x.den y.num y.den z.num z.den

(* Membership-through-append, equipped with a pattern so the          *)
(* well-formedness check of frac_sum's precondition on (sub1 @ sub2)  *)
(* discharges automatically inside frac_sum_append's spec.            *)
let frac_sum_append_memP (#t:Type) (l1 l2: list t) (a: t)
  : Lemma (ensures (L.memP a (L.append l1 l2) <==> (L.memP a l1 \/ L.memP a l2)))
          [SMTPat (L.memP a (L.append l1 l2))]
  = L.append_memP l1 l2 a

(* ================================================================ *)
(*  Main.  frac_sum distributes over list concatenation:              *)
(*    frac_sum p roots (sub1 @ sub2)                                   *)
(*      = frac_sum p roots sub1  (+)  frac_sum p roots sub2.           *)
(* ================================================================ *)
let rec frac_sum_append (#t:Type) {| f: field t |}
                        (p: polynomial t) (roots sub1 sub2: list t)
  : Lemma (requires (forall (b:t). L.memP b sub1 ==> L.memP b roots) /\
                    (forall (b:t). L.memP b sub2 ==> L.memP b roots) /\
                    all_distinct roots)
          (ensures (frac_sum p roots (L.append sub1 sub2))
                 = (fraction_add (frac_sum p roots sub1)
                                 (frac_sum p roots sub2)))
          (decreases sub1)
  = let id_p = polynomial_id #t in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    match sub1 with
    | [] ->
        (* L.append [] sub2 == sub2 (defeq); frac_sum [] = fraction_zero. *)
        let fs2 : fraction id_p = frac_sum p roots sub2 in
        let fz  : fraction id_p = frac_sum p roots [] in
        (* fz == fraction_zero (polynomial t) #id_p definitionally. *)
        frac_add_zero_l fs2;
        (* fraction_add fz fs2 = fs2 ; want fs2 = fraction_add fz fs2. *)
        ()
    | b :: tl ->
        (* L.append (b::tl) sub2 == b :: (L.append tl sub2) (defeq). *)
        let st  : fraction id_p = simple_term p roots b in
        let ftl : fraction id_p = frac_sum p roots tl in
        let fs2 : fraction id_p = frac_sum p roots sub2 in
        let fts : fraction id_p = frac_sum p roots (L.append tl sub2) in
        (* IH on tl: fts = fraction_add ftl fs2. *)
        frac_sum_append p roots tl sub2;
        (* rewrite under  st (+) (.) :  st(+)fts = st(+)(ftl(+)fs2). *)
        frac_add_cong_r st fts
                        (fraction_add ftl fs2);
        (* regroup:  st(+)(ftl(+)fs2) = (st(+)ftl)(+)fs2. *)
        frac_add_assoc st ftl fs2;
        symmetry (fraction_add #(polynomial t) #id_p
                    (fraction_add st ftl) fs2)
                 (fraction_add st
                    (fraction_add ftl fs2));
        (* chain:  frac_sum (b::(tl@sub2)) = st(+)fts = st(+)(ftl(+)fs2)
                     = (st(+)ftl)(+)fs2 = frac_sum(b::tl) (+) fs2.        *)
        transitivity (fraction_add st fts)
                     (fraction_add st
                        (fraction_add ftl fs2))
                     (fraction_add #(polynomial t) #id_p
                        (fraction_add st ftl) fs2)

(* ================================================================ *)
(*  Per-term congruence: if the residues at b agree, the two simple  *)
(*  terms (same denominator x - b) are equal as fractions.           *)
(* ================================================================ *)
let simple_term_eq_of_residue_eq (#t:Type) {| f: field t |}
      (p1: polynomial t) (roots1: list t) (p2: polynomial t) (roots2: list t) (b: t)
  : Lemma (requires L.memP b roots1 /\ all_distinct roots1 /\
                    L.memP b roots2 /\ all_distinct roots2 /\
                    residue p1 roots1 b = residue p2 roots2 b)
          (ensures (simple_term p1 roots1 b) = (simple_term p2 roots2 b))
  = let id_p = polynomial_id #t in
    poly_linear_nonzero b;
    let lb : (ll:polynomial t{is_nonzero ll}) = poly_linear b in
    let r1 = residue p1 roots1 b in
    let r2 = residue p2 roots2 b in
    let s1 = r1 @ poly_zero in                          (* the singleton [r1] *)
    let s2 = r2 @ poly_zero in                          (* the singleton [r2] *)
    H.elim_equatable_laws (polynomial t) ();
    (* poly_eq [r1] [r2] from r1 = r2 (poly_eq poly_zero poly_zero is true). *)
    poly_eq_cons_cons_compute r1 (poly_zero #t) r2 (poly_zero #t);
    (* Cross-product goal (poly_eq):  s1 * lb  ~  lb * s2.        *)
    (* step 1: s1*lb ~ lb*s1  (comm). *)
    mul_commutativity s1 lb;
    (* step 2: lb*s1 ~ lb*s2  (congr: refl lb, poly_eq s1 s2). *)
    reflexivity lb;
    mul_congruence lb s1 lb s2;
    transitivity (s1 * lb)
                 (lb * s1)
                 (lb * s2);
    let xf : fraction id_p = simple_term p1 roots1 b in
    let yf : fraction id_p = simple_term p2 roots2 b in
    fraction_eq_reveal xf yf

(* ================================================================ *)
(*  Main: if residues agree on every element of sub, the fraction    *)
(*  sums over sub are equal.                                         *)
(* ================================================================ *)
let rec frac_sum_eq_of_residue_eq (#t:Type) {| f: field t |}
      (p1: polynomial t) (roots1: list t) (p2: polynomial t) (roots2: list t) (sub: list t)
  : Lemma (requires (forall (b:t). L.memP b sub ==> L.memP b roots1) /\ all_distinct roots1 /\
                    (forall (b:t). L.memP b sub ==> L.memP b roots2) /\ all_distinct roots2 /\
                    (forall (b:t). L.memP b sub ==> residue p1 roots1 b = residue p2 roots2 b))
          (ensures (frac_sum #t #f p1 roots1 sub) = (frac_sum #t #f p2 roots2 sub))
          (decreases sub)
  = let id_p = polynomial_id #t in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    match sub with
    | [] ->
        (* both frac_sum are fraction_zero; reflexivity. *)
        ()
    | b :: tl ->
        let st1 : fraction id_p = simple_term p1 roots1 b in
        let st2 : fraction id_p = simple_term p2 roots2 b in
        let fs1 : fraction id_p = frac_sum p1 roots1 tl in
        let fs2 : fraction id_p = frac_sum p2 roots2 tl in
        (* per-term: st1 = st2. *)
        simple_term_eq_of_residue_eq p1 roots1 p2 roots2 b;
        (* IH on tl: fs1 = fs2. *)
        frac_sum_eq_of_residue_eq p1 roots1 p2 roots2 tl;
        (* fraction_add st1 fs1 = fraction_add st2 fs1  (left cong). *)
        frac_add_cong st1 st2 fs1;
        (* fraction_add st2 fs1 = fraction_add st2 fs2  (right cong). *)
        frac_add_cong_r st2 fs1 fs2;
        (* chain. *)
        transitivity (fraction_add st1 fs1)
                     (fraction_add st2 fs1)
                     (fraction_add st2 fs2)

(* ================================================================ *)
(*  Membership-through-flatten: every element of (flatten groups)    *)
(*  lies in some group of groups.  Equipped with an SMTPat so the     *)
(*  precondition (flatten gs ⊆ roots) of frac_sum_append discharges.  *)
(* ================================================================ *)
let rec flatten_memP (#t:Type) (groups: list (list t)) (b: t)
  : Lemma (ensures (L.memP b (L.flatten groups)
                      <==> (exists (g:list t). L.memP g groups /\ L.memP b g)))
          (decreases groups)
          [SMTPat (L.memP b (L.flatten groups))]
  = match groups with
    | [] -> ()
    | g :: gs ->
        (* L.flatten (g::gs) == L.append g (L.flatten gs) (defeq). *)
        L.append_memP g (L.flatten gs) b;
        flatten_memP gs b

(* ================================================================ *)
(*  Σ over a list of root-groups.                                     *)
(* ================================================================ *)
let rec frac_sum_over_groups (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (groups: list (list t))
  : Pure (fraction (polynomial_id #t))
         (requires (forall (g:list t). L.memP g groups ==> (forall (b:t). L.memP b g ==> L.memP b roots)) /\ all_distinct roots)
         (ensures fun _ -> True)
         (decreases groups)
  = match groups with
    | [] -> fraction_zero (polynomial t)
    | g :: gs -> fraction_add (frac_sum p roots g) (frac_sum_over_groups p roots gs)

(* ================================================================ *)
(*  Σ over groups = frac_sum over the flattened list of roots.        *)
(* ================================================================ *)
let rec frac_sum_flatten (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (groups: list (list t))
  : Lemma (requires (forall (g:list t). L.memP g groups ==> (forall (b:t). L.memP b g ==> L.memP b roots)) /\ all_distinct roots)
          (ensures (frac_sum_over_groups p roots groups) = (frac_sum p roots (L.flatten groups)))
          (decreases groups)
  = let id_p = polynomial_id #t in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    match groups with
    | [] ->
        (* L.flatten [] == []; both sides fraction_zero. *)
        ()
    | g :: gs ->
        (* RHS: L.flatten (g::gs) == L.append g (L.flatten gs) (defeq). *)
        let fg  : fraction id_p = frac_sum p roots g in
        let fgs : fraction id_p = frac_sum_over_groups p roots gs in
        let ffl : fraction id_p = frac_sum p roots (L.flatten gs) in
        (* g ⊆ roots from head of groups hypothesis; flatten gs ⊆ roots via SMTPat. *)
        frac_sum_append p roots g (L.flatten gs);
        (* frac_sum (append g (flatten gs)) = fraction_add fg ffl. *)
        (* IH on gs: fgs = ffl. *)
        frac_sum_flatten p roots gs;
        (* rewrite under fg (+) (.) : fg(+)fgs = fg(+)ffl. *)
        frac_add_cong_r #(polynomial t) #id_p fg fgs ffl;
        (* chain: frac_sum_over_groups (g::gs) = fg(+)fgs = fg(+)ffl
                    = frac_sum (append g (flatten gs)). *)
        symmetry (fraction_add #(polynomial t) #id_p fg ffl)
                 (frac_sum p roots (L.append g (L.flatten gs)));
        transitivity (fraction_add #(polynomial t) #id_p fg fgs)
                     (fraction_add #(polynomial t) #id_p fg ffl)
                     (frac_sum p roots (L.append g (L.flatten gs)))


(* ================================================================ *)
(*  GROUPING.  One LRT log-term  c.log(prod g),  c = the group's      *)
(*  common residue (= residue of the head).  Its derivative is the    *)
(*  fraction  (c . (prod g)') / (prod g).                             *)
(* ================================================================ *)
let group_contribution (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
      (g: list t)
  : Pure (fraction (polynomial_id #t))
         (requires Cons? g /\ all_distinct g /\ all_distinct roots /\
                   (forall (b:t). L.memP b g ==> L.memP b roots))
         (ensures fun _ -> True)
  = prod_linears_nonzero g;
    let c : t = residue p roots (L.hd g) in
    let v : (vv:polynomial t{is_nonzero vv}) = poly_prod_linears g in
    Fraction #(polynomial t) #(polynomial_id #t)
      (poly_scale c (poly_deriv (poly_prod_linears g))) v

(* Per-element residue equality bridging the scaled-derivative form over the   *)
(* group `g` to the original residue over `roots`, under homogeneity.          *)
let per_group_residue_eq (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (g: list t) (b: t)
  : Lemma (requires all_distinct g /\ all_distinct roots /\ L.memP b g /\
                    (forall (bb:t). L.memP bb g ==> L.memP bb roots) /\
                    (forall (bb:t). L.memP bb g ==> residue p roots bb = residue p roots (L.hd g)))
          (ensures (let c : t = residue p roots (L.hd g) in
                    let pd = poly_scale c (poly_deriv (poly_prod_linears g)) in
                    residue pd g b = residue p roots b))
  = H.elim_equatable_laws t ();
    let c : t = residue p roots (L.hd g) in
    let pd = poly_scale c (poly_deriv (poly_prod_linears g)) in
    (* residue pd g b = c (root list is g). *)
    residue_of_scaled_deriv_is_const c g b;
    (* c = residue p roots b : hypothesis gives residue p roots b = residue p roots (hd g) = c. *)

    (* residue pd g b = c = residue p roots b. *)
    transitivity (residue pd g b) c (residue p roots b)

(* ================================================================ *)
(*  PER-GROUP EQUALITY.  Under homogeneity (all residues over the     *)
(*  group equal the head's), the group contribution equals the        *)
(*  partial-fraction terms of that group.                             *)
(* ================================================================ *)
let per_group_eq (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (g: list t)
  : Lemma (requires Cons? g /\ all_distinct g /\ all_distinct roots /\
                    (forall (b:t). L.memP b g ==> L.memP b roots) /\
                    (forall (b:t). L.memP b g ==> residue p roots b = residue p roots (L.hd g)))
          (ensures (group_contribution p roots g) = (frac_sum p roots g))
  = let id_p = polynomial_id #t in
    H.elim_equatable_laws (fraction id_p) ();
    prod_linears_nonzero g;
    let c : t = residue p roots (L.hd g) in
    let v : (vv:polynomial t{is_nonzero vv}) = poly_prod_linears g in
    let pd = poly_scale c (poly_deriv (poly_prod_linears g)) in
    (* (1) group_contribution p roots g == Fraction pd v  (definitional). *)
    (* (2) scaled_log_deriv : Fraction pd v = frac_sum pd g g. *)
    scaled_log_deriv c g;
    (* (3) per-element residue equality between (pd over g) and (p over roots). *)
    introduce forall (b:t). L.memP b g ==> residue pd g b = residue p roots b
    with introduce L.memP b g ==> residue pd g b = residue p roots b
    with _hb. per_group_residue_eq p roots g b;
    (*     frac_sum pd g g = frac_sum p roots g. *)
    frac_sum_eq_of_residue_eq pd g p roots g;
    (* (4) chain : Fraction pd v = frac_sum pd g g = frac_sum p roots g. *)
    transitivity (Fraction pd v)
                 (frac_sum pd g g)
                 (frac_sum p roots g)

(* ================================================================ *)
(*  DERIVATIVE OF THE LRT ANSWER.  Σ_i c_i·log(∏ group_i) has        *)
(*  derivative the fold of the per-group contributions.              *)
(* ================================================================ *)
let rec answer_deriv (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (groups: list (list t))
  : Pure (fraction (polynomial_id #t))
         (requires all_distinct roots /\
                   (forall (g:list t). L.memP g groups ==>
                       (Cons? g /\ all_distinct g /\ (forall (b:t). L.memP b g ==> L.memP b roots))))
         (ensures fun _ -> True)
         (decreases groups)
  = match groups with
    | [] -> fraction_zero (polynomial t)
    | g :: gs -> fraction_add (group_contribution p roots g) (answer_deriv p roots gs)

(* ================================================================ *)
(*  Termwise rewrite: under residue-homogeneity per group, the       *)
(*  answer derivative equals the Σ-over-groups of partial fractions.  *)
(* ================================================================ *)
let rec answer_eq_frac_sum_over_groups (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (groups: list (list t))
  : Lemma (requires all_distinct roots /\
                    (forall (g:list t). L.memP g groups ==>
                       (Cons? g /\ all_distinct g /\ (forall (b:t). L.memP b g ==> L.memP b roots) /\
                        (forall (b:t). L.memP b g ==> residue p roots b = residue p roots (L.hd g)))))
          (ensures (answer_deriv p roots groups) = (frac_sum_over_groups p roots groups))
          (decreases groups)
  = let id_p = polynomial_id #t in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    match groups with
    | [] ->
        (* both sides fraction_zero. *)
        ()
    | g :: gs ->
        let gc  : fraction id_p = group_contribution p roots g in
        let ad  : fraction id_p = answer_deriv p roots gs in
        let fg  : fraction id_p = frac_sum p roots g in
        let fgs : fraction id_p = frac_sum_over_groups p roots gs in
        (* per-group: gc = fg  (preconds from head, L.memP g (g::gs)). *)
        per_group_eq p roots g;
        (* IH on gs: ad = fgs. *)
        answer_eq_frac_sum_over_groups p roots gs;
        (* fraction_add gc ad = fraction_add fg ad  (left cong). *)
        frac_add_cong #(polynomial t) #id_p gc fg ad;
        (* fraction_add fg ad = fraction_add fg fgs  (right cong). *)
        frac_add_cong_r #(polynomial t) #id_p fg ad fgs;
        (* chain. *)
        transitivity (fraction_add #(polynomial t) #id_p gc ad)
                     (fraction_add #(polynomial t) #id_p fg ad)
                     (fraction_add #(polynomial t) #id_p fg fgs)

(* ================================================================ *)
(*  CAPSTONE.  Relative to a residue-homogeneous ordered partition    *)
(*  of the denominator's roots, the derivative of the LRT answer       *)
(*  equals p / q,  q = ∏ (x - root_i).                                 *)
(* ================================================================ *)
let rt_soundness_partition (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (groups: list (list t))
  : Lemma (requires Cons? roots /\ all_distinct roots /\
                    deg p < L.length roots /\
                    L.flatten groups == roots /\
                    (forall (g:list t). L.memP g groups ==>
                       (Cons? g /\ all_distinct g /\ (forall (b:t). L.memP b g ==> L.memP b roots) /\
                        (forall (b:t). L.memP b g ==> residue p roots b = residue p roots (L.hd g)))))
          (ensures (let id_p = polynomial_id #t in
                    is_nonzero (poly_prod_linears roots) /\
                    (let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
                     (answer_deriv p roots groups) = (Fraction p q))))
  = let id_p = polynomial_id #t in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    prod_linears_nonzero roots;
    let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
    (* answer_deriv = frac_sum_over_groups. *)
    answer_eq_frac_sum_over_groups p roots groups;
    (* frac_sum_over_groups = frac_sum p roots (flatten groups) = frac_sum p roots roots
       (the two frac_sum terms are identical since flatten groups == roots). *)
    frac_sum_flatten p roots groups;
    (* partial_fraction_decomposition: Fraction p q = frac_sum p roots roots. *)
    partial_fraction_decomposition p roots;
    symmetry (Fraction p q)
             (frac_sum p roots roots);
    (* chain: answer_deriv = frac_sum_over_groups = frac_sum p roots roots = Fraction p q. *)
    transitivity (answer_deriv p roots groups)
                 (frac_sum_over_groups p roots groups)
                 (frac_sum p roots roots);
    transitivity (answer_deriv p roots groups)
                 (frac_sum p roots roots)
                 (Fraction p q)

(* ================================================================ *)
(*  ROTHSTEIN-TRAGER ROOT CHARACTERISATION.                          *)
(*  For q = ∏(x - beta_i) and q' = q', a distinct root b of q is a    *)
(*  common root of (p - c.q') and q  iff  residue(p) at b equals c.   *)
(*  (b is automatically a root of q; the LHS reduces to b being a     *)
(*  root of (p - c.q'), i.e. p(b) - c.q'(b) = 0.)                     *)
(*                                                                    *)
(*  Eval of LHS: poly_eval (p -- (poly_scale c q')) b                 *)
(*             = p(b) + neg (c * x)         (x = q'(b), nonzero),      *)
(*  and residue p roots b = p(b) * inv x.                             *)
(*  (⇒) p(b) = c*x  ⟹  residue = (c*x)*inv x = c.                    *)
(*  (⇐) residue = c ⟹ p(b) = c*x ⟹ p(b) + neg(c*x) = zero.          *)
(* ================================================================ *)
let common_root_iff_residue (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (c: t) (b: t)
  : Lemma (requires L.memP b roots /\ all_distinct roots)
          (ensures (poly_eval
                      ((p -- (poly_scale c (poly_deriv (poly_prod_linears roots)))) <: polynomial t) b
                    = zero)
                   <==> (residue p roots b = c))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pd = poly_deriv (poly_prod_linears roots) in
    let x : t = poly_eval pd b in
    split_deriv_nonzero b roots;                 (* not (x = zero) *)
    let sc = poly_scale c pd in
    let d  : polynomial t = (p -- sc) in
    let pb : t = poly_eval p b in
    let ix = inv x in
    (* (A) poly_eval sc b = c * x  (mirror residue_of_scaled_deriv_is_const). *)
    eval_mul (c @ poly_zero) pd b;                     (* eval sc b = eval (c@0) b * x *)
    let _ : squash (poly_eval (c @ poly_zero) b = c) =
      if c = zero then begin
        eval_zero b;

        transitivity (poly_eval (c @ poly_zero) b) zero c
      end else
        eval_singleton c b in
    mul_congruence (poly_eval (c @ poly_zero) b) x c x;
    transitivity (poly_eval sc b) (poly_eval (c @ poly_zero) b * x) (c * x);
    (* (B) poly_eval d b = pb + neg (c * x). *)
    eval_add p (- sc) b;                        (* eval d b = pb + eval (neg sc) b *)
    eval_neg sc b;                                     (* eval (neg sc) b = neg (eval sc b) *)
    neg_congruence (poly_eval sc b) (c * x);           (* neg (eval sc b) = neg (c*x) *)
    add_congruence pb (poly_eval (- sc) b) pb (- (poly_eval sc b));
    transitivity (poly_eval d b)
                 (pb + poly_eval (- sc) b)
                 (pb + (- (poly_eval sc b)));
    add_congruence pb (- (poly_eval sc b)) pb (- (c * x));
    transitivity (poly_eval d b) (pb + (- (poly_eval sc b))) (pb + (- (c * x)));
    (* residue p roots b = pb * ix  (definitional, same denominator x). *)
    (* (⇒) eval d b = zero ⟹ pb = c*x ⟹ residue = c. *)
    introduce (poly_eval d b = zero) ==> (residue p roots b = c)
    with _hz. begin
      (* pb + neg (c*x) = zero ⟹ pb = c*x. *)

      transitivity (pb + (- (c * x))) (poly_eval d b) zero;
      lemma_sub_zero_imp_eq pb (c * x);   (* pb = c*x *)
      (* residue = pb * ix = (c*x) * ix = c*(x*ix) = c*one = c. *)
      mul_congruence pb ix (c * x) ix;                 (* pb*ix = (c*x)*ix *)
      mul_associativity c x ix;                        (* (c*x)*ix = c*(x*ix) *)
      inversion_lemma x;                 (* x*ix = one *)
      mul_congruence c (x * ix) c one;
      H.x_mul_one c;                                   (* c*one = c *)
      transitivity (c * (x * ix)) (c * one) c;
      transitivity ((c * x) * ix) (c * (x * ix)) c;
      transitivity (pb * ix) ((c * x) * ix) c;
      transitivity (residue p roots b) (pb * ix) c
    end;
    (* (⇐) residue = c ⟹ pb = c*x ⟹ eval d b = zero. *)
    introduce (residue p roots b = c) ==> (poly_eval d b = zero)
    with _hr. begin
      (* residue == pb * ix, so pb * ix = c. *)
      (* multiply by x:  (pb*ix)*x = c*x ;  LHS = pb*(ix*x) = pb*one = pb. *)
      mul_congruence (residue p roots b) x c x;  (* (pb*ix)*x = c*x *)
      mul_associativity pb ix x;                       (* (pb*ix)*x = pb*(ix*x) *)
      inversion_lemma x;                 (* ix*x = one *)
      mul_congruence pb (ix * x) pb one;
      H.x_mul_one pb;                                  (* pb*one = pb *)
      transitivity (pb * (ix * x)) (pb * one) pb;

      transitivity pb ((pb * ix) * x) (c * x);         (* pb = c*x *)
      (* pb + neg(c*x) = c*x + neg(c*x) = zero. *)
      add_congruence pb (- (c * x)) (c * x) (- (c * x));
      H.x_plus_neg_x (c * x);                          (* c*x + neg(c*x) = zero *)
      transitivity (pb + (- (c * x))) ((c * x) + (- (c * x))) zero;
      transitivity (poly_eval d b) (pb + (- (c * x))) zero
    end


(* ================================================================ *)
(*  A linear factor divides a gcd iff it divides both arguments.    *)
(* ================================================================ *)

let linear_divides_gcd_iff (#t:Type) {| f: field t |} (a b: polynomial t) (beta: t)
  : Lemma ((divides (poly_linear beta) (poly_gcd a b))
           <==> (divides (poly_linear beta) a /\ divides (poly_linear beta) b))
  = let lin = poly_linear beta in
    introduce (divides lin (poly_gcd a b))
              ==> (divides lin a /\ divides lin b)
    with _hd. begin
      Core.Polynomial.GCD.gcd_divides_left  a b; (* divides (gcd a b) a *)
      divides_trans lin (poly_gcd a b) a;        (* divides lin a *)
      Core.Polynomial.GCD.gcd_divides_right a b; (* divides (gcd a b) b *)
      divides_trans lin (poly_gcd a b) b         (* divides lin b *)
    end;
    introduce (divides lin a /\ divides lin b)
              ==> (divides lin (poly_gcd a b))
    with _hd. begin
      Core.Polynomial.GCD.gcd_is_maximal a b lin (* divides lin (gcd a b) *)
    end

(* ================================================================ *)
(*  ROTHSTEIN-TRAGER, gcd form.                                      *)
(*  (x - beta) | gcd(p - c.q', q)   iff   residue(p) at beta = c,     *)
(*  for q = poly_prod_linears roots and beta a root of q.            *)
(*  Chains the existing iff-lemmas:                                  *)
(*    linear_divides_gcd_iff : (x-b)|gcd <=> (x-b)|(p-c.q') /\ (x-b)|q*)
(*    (x-b)|q always (beta is a root of q),                          *)
(*    factor_theorem        : (x-b)|(p-c.q') <=> eval (p-c.q') b = 0  *)
(*    common_root_iff_residue: eval (p-c.q') b = 0 <=> residue = c.   *)
(* ================================================================ *)
let gcd_linear_factor_iff_residue (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (c: t) (beta: t)
  : Lemma (requires L.memP beta roots /\ all_distinct roots)
          (ensures (divides (poly_linear beta)
                      (poly_gcd #t #f
                         ((p -- (poly_scale c (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                         (poly_prod_linears roots)))
                   <==> (residue p roots beta = c))
  = let q = poly_prod_linears roots in
    let qd = poly_deriv q in
    let d  : polynomial t = (p -- (poly_scale c qd)) in
    let lin = poly_linear beta in
    (* (x - beta) | q  always (beta is a root of q). *)
    prod_linears_vanishes roots beta;            (* poly_eval q beta = zero *)
    factor_theorem q beta;                       (* eval q beta = 0 <==> lin | q *)
    (* (x - beta) | (p - c.q') <==> eval d beta = 0. *)
    factor_theorem d beta;
    (* eval d beta = 0 <==> residue p roots beta = c. *)
    common_root_iff_residue p roots c beta;
    (* lin | gcd(d, q)  <==>  lin | d /\ lin | q. *)
    linear_divides_gcd_iff d q beta

(* ================================================================ *)
(*  A root beta of q is a root of v_c = gcd(p - c.q', q)  iff its    *)
(*  residue is c.  (poly_eval form of gcd_linear_factor_iff_residue, *)
(*  via the factor theorem on the gcd.)                              *)
(* ================================================================ *)

let gcd_root_iff_residue (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (c: t) (beta: t)
  : Lemma (requires L.memP beta roots /\ all_distinct roots)
          (ensures (poly_eval
                      (poly_gcd #t #f
                         ((p -- (poly_scale c (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                         (poly_prod_linears roots)) beta
                    = zero)
                   <==> (residue p roots beta = c))
  = let g = poly_gcd #t #f
              ((p -- (poly_scale c (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
              (poly_prod_linears roots) in
    (* eval g beta = 0  <==>  (x - beta) | g *)
    factor_theorem g beta;
    (* (x - beta) | g  <==>  residue p roots beta = c *)
    gcd_linear_factor_iff_residue p roots c beta

(* ================================================================ *)
(*  Distinct residue values give root-disjoint LRT log-arguments.   *)
(*  A root beta of q cannot be a common root of v_c1 and v_c2,       *)
(*  where v_ci = gcd (p - ci.q') q, when c1 <> c2: either gcd-root   *)
(*  forces residue p roots beta to equal that constant.             *)
(* ================================================================ *)

let vc_disjoint (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (c1 c2: t) (beta: t)
  : Lemma (requires L.memP beta roots /\ all_distinct roots /\ not (c1 = c2))
          (ensures not (
             (poly_eval
                (poly_gcd #t #f
                   ((p -- (poly_scale c1 (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                   (poly_prod_linears roots)) beta = zero)
           /\ (poly_eval
                (poly_gcd #t #f
                   ((p -- (poly_scale c2 (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                   (poly_prod_linears roots)) beta = zero)))
  = H.elim_equatable_laws t ();
    let g1 = poly_eval
               (poly_gcd #t #f
                  ((p -- (poly_scale c1 (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                  (poly_prod_linears roots)) beta in
    let g2 = poly_eval
               (poly_gcd #t #f
                  ((p -- (poly_scale c2 (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                  (poly_prod_linears roots)) beta in
    introduce (g1 = zero /\ g2 = zero) ==> False
    with _h. begin
      let r = residue p roots beta in
      gcd_root_iff_residue p roots c1 beta;        (* r = c1 *)
      gcd_root_iff_residue p roots c2 beta;        (* r = c2 *)

      transitivity c1 r c2                               (* c1 = c2 *)
    end

(* ================================================================ *)
(*  A residue-c root makes v_c = gcd(p - c.q', q) a genuine          *)
(*  (degree >= 1) log argument.  Combines:                           *)
(*    gcd_linear_factor_iff_residue : residue = c ==> (x-beta) | g    *)
(*    gcd_pos (qq nonzero ==> deg(gcd) defined): g <> 0               *)
(*    divides_degree_le             : (x-beta) | g, g<>0              *)
(*                                    ==> deg(x-beta) <= deg g        *)
(*    poly_linear_deg               : deg (x-beta) = 1.               *)
(* ================================================================ *)
let residue_implies_gcd_nonconstant (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (c: t) (beta: t)
  : Lemma (requires L.memP beta roots /\ all_distinct roots /\ residue p roots beta = c)
          (ensures (let g = poly_gcd #t #f
                              ((p -- (poly_scale c (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                              (poly_prod_linears roots) in
                    deg g >= 1))
  = let q = poly_prod_linears roots in
    let qd = poly_deriv q in
    let d  : polynomial t = (p -- (poly_scale c qd)) in
    let g  = poly_gcd d q in
    let lin = poly_linear beta in
    (* (x - beta) | g, from residue p roots beta = c. *)
    gcd_linear_factor_iff_residue p roots c beta;  (* divides lin g *)
    (* q = prod roots is nonzero (Cons? roots from memP), so deg q defined; *)
    (* hence deg g defined (gcd_pos). *)
    poly_prod_linears_deg roots;                   (* deg q == length roots *)
    Core.Matrix.Resultant.gcd_pos d q;     (* deg g >= 0 *)
    (* deg lin = 1. *)
    poly_linear_deg beta;                          (* deg lin == 1 *)
    (* divisor-degree: deg lin <= deg g, i.e. 1 <= deg g. *)
    Core.Polynomial.Irreducible.divides_degree_le lin g

(* ================================================================ *)
(*  T6 STRUCTURE THEOREM — partial progress.                         *)
(*                                                                    *)
(*  Goal (vc_factorization, NOT fully reached):                      *)
(*    v_c = gcd(p - c.q', q)  ~  (lc v_c) . prod_{beta in cset}(x-beta)*)
(*  where q = prod roots and cset = { beta in roots : residue = c }.  *)
(*                                                                    *)
(*  We model cset abstractly: a distinct sublist of roots whose       *)
(*  every element is a residue-c root (the filter formulation is      *)
(*  blocked because `residue` carries a precondition and cannot be    *)
(*  used in a total boolean L.filter predicate).                      *)
(* ================================================================ *)

(* (EASY half)  Every residue-c root in cset is a root of v_c.        *)
(*  Immediate from gcd_root_iff_residue (the <== direction).          *)
let vc_roots_are_residue_c (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (c: t) (cset: list t)
  : Lemma (requires all_distinct roots /\
                    (forall (b:t). L.memP b cset ==> (L.memP b roots /\ residue p roots b = c)))
          (ensures (let vc = poly_gcd #t #f
                              ((p -- (poly_scale c (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                              (poly_prod_linears roots) in
                    (forall (b:t). L.memP b cset ==> poly_eval vc b = zero)))
  = let vc = poly_gcd #t #f
                ((p -- (poly_scale c (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                (poly_prod_linears roots) in
    let aux (b:t) : Lemma (requires L.memP b cset)
                          (ensures poly_eval vc b = zero) =
      gcd_root_iff_residue p roots c b
    in
    Classical.forall_intro (Classical.move_requires aux)

(* Each residue-c linear factor (x - beta) divides v_c.               *)
(*  Immediate from gcd_linear_factor_iff_residue (<== direction).     *)
let vc_linear_factors_divide (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (c: t) (cset: list t)
  : Lemma (requires all_distinct roots /\
                    (forall (b:t). L.memP b cset ==> (L.memP b roots /\ residue p roots b = c)))
          (ensures (let vc = poly_gcd #t #f
                              ((p -- (poly_scale c (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                              (poly_prod_linears roots) in
                    (forall (b:t). L.memP b cset ==> divides (poly_linear b) vc)))
  = let vc = poly_gcd #t #f
                ((p -- (poly_scale c (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                (poly_prod_linears roots) in
    let aux (b:t) : Lemma (requires L.memP b cset)
                          (ensures divides (poly_linear b) vc) =
      gcd_linear_factor_iff_residue p roots c b
    in
    Classical.forall_intro (Classical.move_requires aux)

(* v_c factorization GIVEN the count.  Once the (hard) counting step    *)
(*   L.length cset == deg v_c                                           *)
(* is supplied as a hypothesis, the structure tool                     *)
(* poly_split_distinct_roots factors v_c over cset.  This isolates the  *)
(* remaining T6 obligation to exactly that degree equality.            *)
let vc_factorization_given_count (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (c: t) (cset: list t)
  : Lemma (requires all_distinct roots /\ all_distinct cset /\
                    (forall (b:t). L.memP b cset ==> (L.memP b roots /\ residue p roots b = c)) /\
                    (let vc = poly_gcd #t #f
                                ((p -- (poly_scale c (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                                (poly_prod_linears roots) in
                     L.length cset == deg vc))
          (ensures (let vc = poly_gcd #t #f
                              ((p -- (poly_scale c (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                              (poly_prod_linears roots) in
                    (vc = (poly_scale (poly_lc vc) (poly_prod_linears cset)))))
  = let vc = poly_gcd #t #f
                ((p -- (poly_scale c (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                (poly_prod_linears roots) in
    vc_roots_are_residue_c p roots c cset;
    (* wrap the established `forall b in cset. eval vc b = 0` into the opaque pred *)
    let pf (b:t{L.memP b cset}) : Lemma (poly_eval vc b = zero) = () in
    all_roots_vanish_intro vc cset pf;
    poly_split_distinct_roots vc cset

(* ================================================================ *)
(*  THE T6 COUNT  (closes the last vc_factorization obligation).     *)
(*                                                                   *)
(*  cset = EXACTLY the residue-c roots (the iff).  Then              *)
(*    L.length cset == deg vc.                                       *)
(*                                                                   *)
(*  vc | q (gcd_divides_right) and q = ∏ distinct linears, so by     *)
(*  SplitDivisor.divisor_split_count deg vc = #(vc-roots among roots)*)
(*  and via gcd_root_iff_residue those roots ARE the residue-c set.  *)
(* ================================================================ *)
let vc_count (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (c: t) (cset: list t)
  : Lemma (requires all_distinct roots /\ all_distinct cset /\
                    (forall (b:t). L.memP b cset <==> (L.memP b roots /\ residue p roots b = c)))
          (ensures (let vc = poly_gcd #t #f
                              ((p -- (poly_scale c (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                              (poly_prod_linears roots) in
                    L.length cset == deg vc))
  =
    let q = poly_prod_linears roots in
    let d : polynomial t = (p -- (poly_scale c (poly_deriv q))) in
    let vc = poly_gcd d q in
    poly_prod_linears_deg roots;             (* deg q >= 0 *)
    Core.Matrix.Resultant.gcd_pos d q;       (* deg vc >= 0 *)
    GC.gcd_divides_right d q;                 (* divides vc q *)
    let iff_b (b:t)
      : Lemma (L.memP b cset <==> (L.memP b roots /\ poly_eval vc b = zero))
      = let aux () : Lemma (requires L.memP b roots)
                           (ensures  L.memP b cset <==> (L.memP b roots /\ poly_eval vc b = zero))
          = gcd_root_iff_residue p roots c b   (* eval vc b = 0 <==> residue = c, for b in roots *)
        in
        Classical.move_requires aux ()             (* b not in roots: memP b cset ==> memP b roots, so both sides false *)
    in
    FStar.Classical.forall_intro iff_b;
    SD.divisor_split_count vc roots cset

(* ================================================================ *)
(*  T6 vc_factorization (UNCONDITIONAL form).                         *)
(*    v_c = gcd(p - c.q', q)  =  (lc v_c) . ∏_{β∈cset}(x-β)          *)
(*  for cset = EXACTLY the residue-c roots.  Drops the count          *)
(*  hypothesis of vc_factorization_given_count by supplying it via    *)
(*  vc_count.  This is the last gap to fully-unconditional tier-2 T8. *)
(* ================================================================ *)
let vc_factorization (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (c: t) (cset: list t)
  : Lemma (requires all_distinct roots /\ all_distinct cset /\
                    (forall (b:t). L.memP b cset <==> (L.memP b roots /\ residue p roots b = c)))
          (ensures (let vc = poly_gcd #t #f
                              ((p -- (poly_scale c (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                              (poly_prod_linears roots) in
                    (vc = (poly_scale (poly_lc vc) (poly_prod_linears cset)))))
  = vc_count p roots c cset;
    vc_factorization_given_count p roots c cset

(* ===== merged from Core.Risch.RTCriterion - Rothstein-Trager criterion (R(c)=0 <=> deg gcd >= 1) ===== *)

#set-options "--fuel 2 --ifuel 2 --z3rlimit 60"

(* ---------------------------------------------------------------- *)
(*  Bounds shared by both directions: with the canonical N, DQ from  *)
(*  lrt_resultant_specializes, the pair (pp, q) satisfies the        *)
(*  length/degree bounds needed by the resultant lemmas.             *)
(* ---------------------------------------------------------------- *)

(* deg (p - c*q') < N+1, i.e. length pp <= N+1, with N the canonical max. *)
let pp_bound (#t:Type) {| f: field t |} (p q: polynomial t) (c: t)
  : Lemma (requires deg q >= 1)
          (ensures (let q'  = poly_deriv q in
                    let dp  = (if deg p < 0 then 0 else deg p) in
                    let dq' = (if deg q' < 0 then 0 else deg q') in
                    let n   = (if dp > dq' then dp else dq') in
                    let pp  : polynomial t = (p -- (SP.poly_scale c q')) in
                    L.length pp <= n ++ 1))
  = let q'  = poly_deriv q in
    let dp  = (if deg p < 0 then 0 else deg p) in
    let dq' = (if deg q' < 0 then 0 else deg q') in
    let n   = (if dp > dq' then dp else dq') in
    LR.poly_scale_deg_le c q' (n ++ 1);
    poly_sub_degree_bound p (SP.poly_scale c q') (n ++ 1)

(* ---------------------------------------------------------------- *)
(*  Backward direction:                                              *)
(*    resultant N DQ pp q = 0  ==>  deg (gcd pp q) >= 1.             *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 100"
let rt_backward (#t:Type) {| f: field t |} (p q: polynomial t) (c: t)
  : Lemma (requires deg q >= 1)
          (ensures (let q'  = poly_deriv q in
                    let pp  : polynomial t = (p -- (SP.poly_scale c q')) in
                    (poly_eval (LRT.lrt_resultant_raw p q) c = zero)
                    ==>
                    deg (GC.poly_gcd pp q) >= 1))
  = let q'  = poly_deriv q in
    let dq  = deg q in
    let dp  = (if deg p < 0 then 0 else deg p) in
    let dq' = (if deg q' < 0 then 0 else deg q') in
    let n   = (if dp > dq' then dp else dq') in
    let pp  : polynomial t = (p -- (SP.poly_scale c q')) in
    let aux ()
      : Lemma (requires poly_eval (LRT.lrt_resultant_raw p q) c = zero)
              (ensures deg (GC.poly_gcd pp q) >= 1)
      = H.elim_equatable_laws t ();
        LR.lrt_resultant_specializes p q c;
        (* poly_eval(raw) c = resultant n dq pp q  and  poly_eval(raw) c = zero *)
        let r = RES.resultant n dq pp q in

        transitivity r (poly_eval (LRT.lrt_resultant_raw p q) c) zero; (* r = zero *)
        pp_bound p q c;            (* L.length pp <= n+1 *)
        RC.resultant_converse n dq pp q
    in
    FStar.Classical.move_requires aux ()
#pop-options

(* ---------------------------------------------------------------- *)
(*  Forward direction:                                              *)
(*    deg (gcd pp q) >= 1  ==>  resultant N DQ pp q = 0.            *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 100"
let rt_forward (#t:Type) {| f: field t |} (p q: polynomial t) (c: t)
  : Lemma (requires deg q >= 1)
          (ensures (let q'  = poly_deriv q in
                    let pp  : polynomial t = (p -- (SP.poly_scale c q')) in
                    deg (GC.poly_gcd pp q) >= 1
                    ==>
                    (poly_eval (LRT.lrt_resultant_raw p q) c = zero)))
  = let q'  = poly_deriv q in
    let dq  = deg q in
    let dp  = (if deg p < 0 then 0 else deg p) in
    let dq' = (if deg q' < 0 then 0 else deg q') in
    let n   = (if dp > dq' then dp else dq') in
    let pp  : polynomial t = (p -- (SP.poly_scale c q')) in
    let aux ()
      : Lemma (requires deg (GC.poly_gcd pp q) >= 1)
              (ensures poly_eval (LRT.lrt_resultant_raw p q) c = zero)
      = H.elim_equatable_laws t ();
        LR.lrt_resultant_specializes p q c;   (* eval = resultant n dq pp q *)
        pp_bound p q c;                        (* L.length pp <= n+1 *)
        let r = RES.resultant n dq pp q in
        if deg pp >= 0 then begin
          let g = GC.poly_gcd pp q in
          GC.gcd_divides_left  pp q;           (* g | pp *)
          GC.gcd_divides_right pp q;           (* g | q *)
          RES.resultant_zero_of_common_divisor n dq pp q g  (* r = zero *)
        end else begin
          (* pp == [] : length 0, so deg pp < 0 *)
          RES.resultant_zero_when_p_all_zero n dq pp q     (* r = zero *)
        end;
        (* eval = r  and  r = zero  ==>  eval = zero *)
        transitivity (poly_eval (LRT.lrt_resultant_raw p q) c) r zero
    in
    FStar.Classical.move_requires aux ()
#pop-options

(* ---------------------------------------------------------------- *)
(*  The Rothstein-Trager criterion (iff).                            *)
(* ---------------------------------------------------------------- *)

let rt_criterion (#t:Type) {| f: field t |} (p q: polynomial t) (c: t)
  : Lemma (requires deg q >= 1)
          (ensures (let q' = poly_deriv q in
                    let pp : polynomial t = (p -- (SP.poly_scale c q')) in
                    (poly_eval (LRT.lrt_resultant_raw p q) c = zero)
                    <==>
                    deg (GC.poly_gcd pp q) >= 1))
  = rt_forward  p q c;
    rt_backward p q c
