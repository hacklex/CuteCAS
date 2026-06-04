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

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Subst
open Core.Polynomial.Derivative
open Core.Polynomial.Root
open Core.Polynomial.Product
open Core.Polynomial.Split
open Core.Fractions
open Core.Algebra.Divisibility

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  T1.  d/dx (x - a) = 1   (as poly_eq to poly_one).                *)
(* ================================================================ *)

let poly_deriv_linear (#t:Type) {| f: field t |} (a: t)
  : Lemma (poly_eq (poly_deriv (poly_linear #t #f a)) (poly_one #t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    let lin = poly_linear #t #f a in
    poly_linear_deg #t #f a;                       (* poly_deg lin = Some 1 *)
    let aux (j:nat) : Lemma (coeff (poly_deriv lin) j = coeff (poly_one #t) j) =
      poly_deriv_coeff lin j;                       (* coeff(deriv lin) j = nat_scale (j+1) (coeff lin (j+1)) *)
      if j = 0 then begin
        (* coeff (deriv lin) 0 = nat_scale 1 (coeff lin 1); coeff lin 1 = one = coeff poly_one 0 *)
        nat_scale_one (coeff lin 1);
        (* nat_scale 1 (coeff lin 1) = coeff lin 1, and coeff lin 1 == one == coeff poly_one 0 (defeq) *)
        transitivity (coeff (poly_deriv lin) j)
                     (nat_scale #t #((cr_of_id t #(id_of_f t)).cr_r.r_add) 1 (coeff lin 1))
                     (coeff (poly_one #t) j)
      end else begin
        (* coeff lin (j+1) = zero (deg lin = 1 < j+1) ; nat_scale (j+1) zero = zero = coeff poly_one j *)
        coeff_above_degree lin (Prims.op_Addition j 1);
        nat_scale_zero_element #t #((cr_of_id t #(id_of_f t)).cr_r.r_add) (Prims.op_Addition j 1);
        coeff_above_degree (poly_one #t) j;
        nat_scale_congruence #t #((cr_of_id t #(id_of_f t)).cr_r.r_add)
                             (Prims.op_Addition j 1) (coeff lin (Prims.op_Addition j 1)) (zero <: t);
        transitivity (coeff (poly_deriv lin) j)
                     (nat_scale #t #((cr_of_id t #(id_of_f t)).cr_r.r_add) (Prims.op_Addition j 1) (coeff lin (Prims.op_Addition j 1)))
                     (zero <: t);
        symmetry (coeff (poly_one #t) j) (zero <: t);
        transitivity (coeff (poly_deriv lin) j) (zero <: t) (coeff (poly_one #t) j)
      end
    in
    poly_eq_by_coeff (poly_deriv lin) (poly_one #t) aux

(* ================================================================ *)
(*  T2.  Leibniz cons-step for ∏ of linear factors.                 *)
(* ================================================================ *)

let deriv_prod_linears_step (#t:Type) {| f: field t |} (a: t) (rest: list t)
  : Lemma (poly_eq (poly_deriv (poly_prod_linears #t #f (a :: rest)))
                   (poly_add (poly_prod_linears #t #f rest)
                             (poly_mul (poly_linear #t #f a)
                                       (poly_deriv (poly_prod_linears #t #f rest)))))
  = let lin = poly_linear #t #f a in
    let w   = poly_prod_linears #t #f rest in
    let dw  = poly_deriv w in
    (* poly_prod_linears (a::rest) == poly_mul lin w (definitional) *)
    (* (1) Leibniz: D(lin·w) ~ D(lin)·w + lin·D(w) *)
    poly_deriv_mul lin w;
    (* (2) left summand: D(lin)·w ~ poly_one·w ~ w *)
    poly_deriv_linear #t #f a;                       (* D(lin) ~ poly_one *)
    poly_eq_reflexivity w;
    poly_mul_congruence (poly_deriv lin) w (poly_one #t) w;  (* D(lin)·w ~ poly_one·w *)
    poly_mul_one w;                                   (* poly_one·w ~ w *)
    poly_eq_transitivity (poly_mul (poly_deriv lin) w) (poly_mul (poly_one #t) w) w;
    (* (3) add-congruence on the left summand *)
    poly_eq_reflexivity (poly_mul lin dw);
    poly_add_congruence (poly_mul (poly_deriv lin) w) (poly_mul lin dw)
                        w                              (poly_mul lin dw);
    (* (4) chain (1) and (3) *)
    poly_eq_transitivity (poly_deriv (poly_mul lin w))
                         (poly_add (poly_mul (poly_deriv lin) w) (poly_mul lin dw))
                         (poly_add w (poly_mul lin dw))

(* ================================================================ *)
(*  Simple residue: if q ~ (x - b)·w then q'(b) = w(b).             *)
(* ================================================================ *)

let simple_residue (#t:Type) {| f: field t |} (b: t) (w q: polynomial t)
  : Lemma (requires poly_eq q (poly_mul (poly_linear #t #f b) w))
          (ensures poly_eval (poly_deriv q) b = poly_eval w b)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let lin = poly_linear #t #f b in
    let dlin = poly_deriv lin in
    let dw  = poly_deriv w in
    let lw  = poly_mul lin w in
    let leib = poly_add (poly_mul dlin w) (poly_mul lin dw) in
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
    eval_add (poly_mul dlin w) (poly_mul lin dw) b;
    eval_mul dlin w b;                                       (* = dlinb * wb *)
    eval_mul lin dw b;                                       (* = linb * dwb *)
    (* (4) dlinb = one : eval (deriv lin) b = one *)
    poly_deriv_linear #t #f b;                               (* poly_eq dlin poly_one *)
    eval_congruence dlin (poly_one #t) b;                    (* dlinb = eval poly_one b *)
    eval_one #t b;                                           (* eval poly_one b = one *)
    transitivity dlinb (poly_eval (poly_one #t) b) (one <: t);
    (* (5) linb = zero *)
    eval_linear_root b;                                      (* linb = zero *)
    (* (6) dlinb * wb = one * wb = wb *)
    mul_congruence dlinb wb (one <: t) wb;
    H.one_mul_x wb;                                          (* one * wb = wb *)
    transitivity (dlinb * wb) ((one <: t) * wb) wb;
    (* (7) linb * dwb = zero * dwb = zero *)
    mul_congruence linb dwb (zero <: t) dwb;
    H.zero_mul_x dwb;                                        (* zero * dwb = zero *)
    transitivity (linb * dwb) ((zero <: t) * dwb) (zero <: t);
    (* (8) eval leib b = eval(dlin·w)b + eval(lin·dw)b = dlinb*wb + linb*dwb *)
    add_congruence (poly_eval (poly_mul dlin w) b) (poly_eval (poly_mul lin dw) b)
                   (dlinb * wb) (linb * dwb);
    transitivity (poly_eval leib b)
                 (poly_eval (poly_mul dlin w) b + poly_eval (poly_mul lin dw) b)
                 (dlinb * wb + linb * dwb);
    (* = wb + zero = wb *)
    add_congruence (dlinb * wb) (linb * dwb) wb (zero <: t);
    transitivity (poly_eval leib b) (dlinb * wb + linb * dwb) (wb + (zero <: t));
    H.x_plus_zero wb;                                        (* wb + zero = wb *)
    transitivity (poly_eval leib b) (wb + (zero <: t)) wb;
    (* (9) chain: eval (deriv q) b = eval leib b = wb *)
    transitivity (poly_eval (poly_deriv q) b) (poly_eval leib b) wb

(* ================================================================ *)
(*  Interpolation uniqueness:  a polynomial whose degree is below    *)
(*  the number of distinct points at which it vanishes is zero.      *)
(* ================================================================ *)

let rec low_degree_many_roots_zero (#t:Type) {| f: field t |} (r: polynomial t) (roots: list t)
  : Lemma (requires all_distinct #t roots /\
                    (forall (b:t). L.memP b roots ==> poly_eval r b = (zero <: t)) /\
                    (Some? (poly_deg r) ==> Some?.v (poly_deg r) < L.length roots))
          (ensures poly_eq r (poly_zero #t))
          (decreases roots)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cr_p : commutative_ring (polynomial t) = TC.solve in
    match roots with
    | [] ->
        (* length roots = 0, so the precondition forces poly_deg r == None. *)
        assert (None? (poly_deg r));
        Core.Polynomial.Unique.degree_none_poly_eq_zero #t r
    | b :: rest ->
        (* b is a root: (x-b) | r, so r ~ (x-b)*r'. *)
        let _ : squash (L.memP b roots) = () in
        assert (poly_eval r b = (zero <: t));
        factor_forward #t #f r b;                         (* divides (x-b) r *)
        let la = poly_linear #t #f b in
        eliminate exists (q: polynomial t). poly_eq r (poly_mul la q)
        returns poly_eq r (poly_zero #t)
        with _hq.
        begin
          (* all_distinct (b::rest) gives the head distinctness and all_distinct rest. *)
          assert ((forall (d:t). L.memP d rest ==> not (b = d)) /\ all_distinct #t rest);
          (* (1) remaining roots survive in q. *)
          let rest_roots (c:t) : Lemma (requires L.memP c rest)
                                       (ensures poly_eval q c = (zero <: t)) =
            assert (L.memP c roots);                       (* c in rest ==> c in roots *)
            assert (poly_eval r c = (zero <: t));
            assert (not (b = c));                          (* from all_distinct head *)
            H.elim_equatable_laws t ();
            symmetry b c;                                  (* b=c <==> c=b *)
            assert (not (c = b));
            root_survives_division #t #f b c r q
          in
          let rest_roots_all (c:t) : Lemma (L.memP c rest ==> poly_eval q c = (zero <: t)) =
            Classical.move_requires rest_roots c
          in
          Classical.forall_intro rest_roots_all;
          (* (2) degree drop:  Some?(poly_deg q) ==> deg q < length rest. *)
          poly_linear_deg #t #f b;                          (* deg la = Some 1 *)
          if Some? (poly_deg q) then begin
            poly_deg_mul #t #(id_of_f t) la q;              (* deg(la*q) = 1 + deg q *)
            Core.Polynomial.Unique.degree_well_defined r (poly_mul la q);   (* poly_deg r == poly_deg (la*q) *)
            assert (Some? (poly_deg r));
            assert (Some?.v (poly_deg r) == Prims.op_Addition 1 (Some?.v (poly_deg q)));
            assert (Some?.v (poly_deg r) < L.length roots);
            assert (L.length roots == Prims.op_Addition (L.length rest) 1);
            assert (Some?.v (poly_deg q) < L.length rest)
          end;
          (* (3) IH on q. *)
          low_degree_many_roots_zero #t #f q rest;          (* poly_eq q poly_zero *)
          (* (4) r ~ la*q ~ la*0 ~ 0. *)
          reflexivity #(polynomial t) #(cr_p.cr_r.r_add.acg_eq) la;
          poly_mul_congruence la q la (poly_zero #t);        (* la*q ~ la*0 *)
          transitivity #(polynomial t) #(cr_p.cr_r.r_add.acg_eq)
                       r (poly_mul la q) (poly_mul la (poly_zero #t));
          H.x_mul_zero #(polynomial t) #(cr_p.cr_r) la;      (* la*0 ~ 0 *)
          transitivity #(polynomial t) #(cr_p.cr_r.r_add.acg_eq)
                       r (poly_mul la (poly_zero #t)) (poly_zero #t)
        end

(* ================================================================ *)
(*  Peel an occurring root b to the front of the product.           *)
(* ================================================================ *)

let rec prod_linears_peel (#t:Type) {| f: field t |} (b: t) (roots: list t)
  : Pure (list t)
         (requires L.memP b roots)
         (ensures fun rest ->
            L.length rest == L.length roots - 1 /\
            poly_eq (poly_prod_linears #t #f roots)
                    (poly_mul (poly_linear #t #f b) (poly_prod_linears #t #f rest)))
         (decreases roots)
  = H.elim_equatable_laws t ();
    match roots with
    | a :: tl ->
        let la = poly_linear #t #f a in
        let lb = poly_linear #t #f b in
        if a = b then begin
          (* poly_prod_linears (a::tl) == poly_mul la (poly_prod_linears tl). *)
          let ptl = poly_prod_linears #t #f tl in
          (* poly_eq la lb : [neg a; one] vs [neg b; one] *)
          neg_congruence a b;                              (* neg a = neg b *)
          assert (la == [neg a; one #t]);
          assert (lb == [neg b; one #t]);
          reflexivity (one #t);
          assert (poly_eq ([neg a; one #t] <: polynomial t) ([neg b; one #t] <: polynomial t) ==
                  ((neg a = neg b) && ((one #t = one #t) && true)))
            by (FStar.Tactics.norm [delta_only [`%poly_eq]; iota; zeta; primops]; FStar.Tactics.trefl ());
          assert (poly_eq la lb);
          poly_eq_reflexivity ptl;
          poly_mul_congruence la ptl lb ptl;              (* la*ptl ~ lb*ptl *)
          tl
        end
        else begin
          (* derive L.memP b tl from L.memP b (a::tl) and a<>b. *)
          eliminate (b == a) \/ (L.memP b tl)
          returns L.memP b tl
          with _h_eq.
            (H.leibniz_to_eq b a; symmetry b a)            (* b==a ==> a=b, contradiction *)
          and _h_tl. ();
          let rest' = prod_linears_peel #t #f b tl in
          let prest' = poly_prod_linears #t #f rest' in
          let ptl = poly_prod_linears #t #f tl in
          (* IH: poly_eq ptl (poly_mul lb prest') *)
          (* Goal: poly_eq (poly_mul la ptl) (poly_mul lb (poly_mul la prest')) *)
          (* step 1: la*ptl ~ la*(lb*prest') *)
          poly_eq_reflexivity la;
          poly_mul_congruence la ptl la (poly_mul lb prest');
          (* step 2: la*(lb*prest') ~ (la*lb)*prest'  (assoc, reversed) *)
          poly_mul_associativity la lb prest';
          poly_eq_symmetry (poly_mul (poly_mul la lb) prest') (poly_mul la (poly_mul lb prest'));
          poly_eq_transitivity (poly_mul la ptl)
                               (poly_mul la (poly_mul lb prest'))
                               (poly_mul (poly_mul la lb) prest');
          (* step 3: (la*lb)*prest' ~ (lb*la)*prest'  (comm + congruence) *)
          poly_mul_commutativity la lb;
          poly_eq_reflexivity prest';
          poly_mul_congruence (poly_mul la lb) prest' (poly_mul lb la) prest';
          poly_eq_transitivity (poly_mul la ptl)
                               (poly_mul (poly_mul la lb) prest')
                               (poly_mul (poly_mul lb la) prest');
          (* step 4: (lb*la)*prest' ~ lb*(la*prest')  (assoc) *)
          poly_mul_associativity lb la prest';
          poly_eq_transitivity (poly_mul la ptl)
                               (poly_mul (poly_mul lb la) prest')
                               (poly_mul lb (poly_mul la prest'));
          a :: rest'
        end

(* ================================================================ *)
(*  Derivative of the split product, evaluated at one of its roots:  *)
(*    q'(b) = (the cofactor product) evaluated at b = prod_{i!=b}(b - b_i).  *)
(*  Immediate from prod_linears_peel (q ~ (x-b)*cofactor) + simple_residue. *)
(* ================================================================ *)

let deriv_prod_at_root (#t:Type) {| f: field t |} (b: t) (roots: list t)
  : Lemma (requires L.memP b roots)
          (ensures poly_eval (poly_deriv (poly_prod_linears #t #f roots)) b
                 = poly_eval (poly_prod_linears #t #f (prod_linears_peel #t #f b roots)) b)
  = let rest = prod_linears_peel #t #f b roots in
    simple_residue #t #f b (poly_prod_linears #t #f rest) (poly_prod_linears #t #f roots)

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
          (ensures poly_eval (poly_prod_linears #t #f (prod_linears_peel #t #f b roots)) c
                 = (zero <: t))
  = H.elim_equatable_laws t ();
    let rest = prod_linears_peel #t #f b roots in
    let cof  = poly_prod_linears #t #f rest in
    let p    = poly_prod_linears #t #f roots in
    (* p ~ (x-b)*cof, from prod_linears_peel's ensures. *)
    assert (poly_eq p (poly_mul (poly_linear #t #f b) cof));
    (* p(c) = 0 since c is a root of the whole product. *)
    prod_linears_vanishes #t #f roots c;
    assert (poly_eval p c = (zero <: t));
    (* c <> b from not (b = c) by symmetry. *)
    symmetry b c;
    assert (not (c = b));
    (* domain-law argument packaged in root_survives_division. *)
    root_survives_division #t #f b c p cof

(* ================================================================ *)
(*  Every factor surviving the peel is distinct from the peeled root. *)
(*    a in (prod_linears_peel b roots)  /\ all_distinct roots         *)
(*      ==>  a <> b.                                                  *)
(*  Mirrors prod_linears_peel's own recursion.                       *)
(* ================================================================ *)

let rec peel_excludes (#t:Type) {| f: field t |} (b a: t) (roots: list t)
  : Lemma (requires L.memP b roots /\ all_distinct #t roots /\
                    L.memP a (prod_linears_peel #t #f b roots))
          (ensures  not (a = b))
          (decreases roots)
  = H.elim_equatable_laws t ();
    match roots with
    | h :: tl ->
        (* all_distinct (h::tl) = (forall d. memP d tl ==> not (h=d)) /\ all_distinct tl *)
        assert ((forall (d:t). L.memP d tl ==> not (h = d)) /\ all_distinct #t tl);
        if h = b then begin
          (* peel b (h::tl) == tl, so a in tl; distinctness gives not (h = a). *)
          assert (L.memP a tl);
          assert (not (h = a));               (* from the head-distinctness of h::tl *)
          symmetry h a;                        (* not (a = h) *)
          (* h = b (boolean true); if a = b then a = h, contradiction. *)
          if a = b then begin
            symmetry h b;                      (* b = h, from h = b *)
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
          let rest' = prod_linears_peel #t #f b tl in
          (* a == h \/ a in rest'. *)
          eliminate (a == h) \/ (L.memP a rest')
          returns not (a = b)
          with _h_ah.
            (* a == h, and the branch condition is not (h = b). *)
            (H.leibniz_to_eq a h;              (* a = h *)
             if a = b then begin
               symmetry a h;                   (* h = a *)
               transitivity h a b              (* h = a /\ a = b ==> h = b, contradiction *)
             end)
          and _h_ar.
            peel_excludes #t #f b a tl
        end

(* ================================================================ *)
(*  ∏_{a in rest}(neg a + b) is nonzero when every a <> b (field).   *)
(*    Induction:  base one <> 0 (f_one_ne_zero); cons via the domain *)
(*    law on nonzero factors (sub_nonzero_of_distinct + domain law). *)
(* ================================================================ *)

let rec eval_prod_sub_nonzero (#t:Type) {| f: field t |} (b: t) (rest: list t)
  : Lemma (requires (forall (a:t). L.memP a rest ==> not (a = b)))
          (ensures  not (eval_prod_sub #t #f rest b = (zero <: t)))
          (decreases rest)
  = H.elim_equatable_laws t ();
    match rest with
    | [] ->
        (* eval_prod_sub [] b == one; one <> zero. *)
        let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
        ()
    | a :: tl ->
        (* eval_prod_sub (a::tl) b == (neg a + b) * eval_prod_sub tl b. *)
        assert (not (a = b));                      (* a in (a::tl) *)
        symmetry a b;                               (* not (b = a) *)
        sub_nonzero_of_distinct #t #f a b;          (* not (neg a + b = zero) *)
        eval_prod_sub_nonzero #t #f b tl;           (* IH: tail product nonzero *)
        domain_nonzero_mul_nonzero #t #(d_of_id t #(id_of_f t))
                                   (neg a + b) (eval_prod_sub #t #f tl b)

(* ================================================================ *)
(*  Main:  q'(b) <> 0 for q = ∏_{a in roots}(x - a), roots distinct.  *)
(*    (residue denominator nonzero.)                                  *)
(*  q'(b) = eval (∏ (peel b roots)) b      (deriv_prod_at_root)       *)
(*        = eval_prod_sub (peel b roots) b (eval_poly_prod_linears)   *)
(*        <> 0                             (every peel factor <> b).  *)
(* ================================================================ *)

let split_deriv_nonzero (#t:Type) {| f: field t |} (b: t) (roots: list t)
  : Lemma (requires L.memP b roots /\ all_distinct #t roots)
          (ensures  not (poly_eval (poly_deriv (poly_prod_linears #t #f roots)) b
                         = (zero <: t)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let rest = prod_linears_peel #t #f b roots in
    (* q'(b) = eval (∏ rest) b. *)
    deriv_prod_at_root #t #f b roots;
    (* eval (∏ rest) b = eval_prod_sub rest b. *)
    eval_poly_prod_linears #t #f rest b;
    transitivity (poly_eval (poly_deriv (poly_prod_linears #t #f roots)) b)
                 (poly_eval (poly_prod_linears #t #f rest) b)
                 (eval_prod_sub #t #f rest b);
    (* every factor of rest excludes b. *)
    let peel_off (a:t) : Lemma (L.memP a rest ==> not (a = b)) =
      Classical.move_requires (peel_excludes #t #f b a) roots
    in
    Classical.forall_intro peel_off;
    (* product nonzero. *)
    eval_prod_sub_nonzero #t #f b rest


(* ================================================================ *)
(*  Residue scalar  r_b = p(b) * inv(q'(b))  with q = prod roots.    *)
(*  inv carries a nonzero precondition; split_deriv_nonzero          *)
(*  discharges it from  memP b roots /\ all_distinct roots.          *)
(* ================================================================ *)

let residue (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (b: t)
  : Pure t (requires L.memP b roots /\ all_distinct #t roots)
           (ensures fun _ -> True)
  = split_deriv_nonzero #t #f b roots;
    poly_eval p b * (f.f_sf.sf_mig).inv (poly_eval (poly_deriv (poly_prod_linears #t #f roots)) b)

(* ================================================================ *)
(*  Residue partial-fraction numerator over a sublist `sub`:         *)
(*    Sum_{b in sub}  r_b * (cofactor product of b).                 *)
(* ================================================================ *)

let rec residue_sum (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (sub: list t)
  : Pure (polynomial t)
         (requires (forall (b:t). L.memP b sub ==> L.memP b roots) /\ all_distinct #t roots)
         (ensures fun _ -> True)
         (decreases sub)
  = match sub with
    | [] -> poly_zero #t
    | b :: tl ->
        poly_add (poly_scale #t (residue #t #f p roots b)
                             (poly_prod_linears #t #f (prod_linears_peel #t #f b roots)))
                 (residue_sum #t #f p roots tl)

(* ================================================================ *)
(*  Off-root vanishing:  the residue sum over `sub` is zero at any    *)
(*  root c that differs from every element of `sub`.                  *)
(* ================================================================ *)

let rec eval_residue_sum_vanishes (#t:Type) {| f: field t |} (p: polynomial t) (roots sub: list t) (c: t)
  : Lemma (requires (forall (b:t). L.memP b sub ==> L.memP b roots) /\ all_distinct #t roots /\
                    L.memP c roots /\
                    (forall (b:t). L.memP b sub ==> not (b = c)))
          (ensures poly_eval (residue_sum #t #f p roots sub) c = (zero <: t))
          (decreases sub)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match sub with
    | [] -> eval_zero #t c
    | b :: tl ->
        let rb  = residue #t #f p roots b in
        let cof = poly_prod_linears #t #f (prod_linears_peel #t #f b roots) in
        let term = poly_scale #t rb cof in
        let rest = residue_sum #t #f p roots tl in
        eval_add term rest c;
        eval_mul (rb @ poly_zero) cof c;
        let _ : squash (poly_eval (rb @ poly_zero) c = rb) =
          if rb = (zero <: t) then begin
            eval_zero #t c;
            symmetry rb (zero <: t);
            transitivity (poly_eval (rb @ poly_zero) c) (zero <: t) rb
          end else
            eval_singleton #t #f rb c in
        mul_congruence (poly_eval (rb @ poly_zero) c) (poly_eval cof c) rb (poly_eval cof c);
        transitivity (poly_eval term c)
                     (poly_eval (rb @ poly_zero) c * poly_eval cof c)
                     (rb * poly_eval cof c);
        cofactor_eval_off #t #f b c roots;
        mul_congruence rb (poly_eval cof c) rb (zero <: t);
        H.x_mul_zero #t rb;
        transitivity (rb * poly_eval cof c) (rb * (zero <: t)) (zero <: t);
        transitivity (poly_eval term c) (rb * poly_eval cof c) (zero <: t);
        eval_residue_sum_vanishes #t #f p roots tl c;
        add_congruence (poly_eval term c) (poly_eval rest c) (zero <: t) (zero <: t);
        H.x_plus_zero #t (zero <: t);
        transitivity (poly_eval (residue_sum #t #f p roots sub) c)
                     (poly_eval term c + poly_eval rest c)
                     ((zero <: t) + (zero <: t));
        transitivity (poly_eval (residue_sum #t #f p roots sub) c)
                     ((zero <: t) + (zero <: t))
                     (zero <: t)

(* ================================================================ *)
(*  At-root value:  on a distinct sublist `sub` containing c, the     *)
(*  residue sum reproduces  p(c).                                     *)
(* ================================================================ *)

let rec eval_residue_sum_at_root (#t:Type) {| f: field t |} (p: polynomial t) (roots sub: list t) (c: t)
  : Lemma (requires (forall (b:t). L.memP b sub ==> L.memP b roots) /\ all_distinct #t roots /\
                    all_distinct #t sub /\ L.memP c sub)
          (ensures poly_eval (residue_sum #t #f p roots sub) c = poly_eval p c)
          (decreases sub)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match sub with
    | b :: tl ->
        assert ((forall (d:t). L.memP d tl ==> not (b = d)) /\ all_distinct #t tl);
        let rb  = residue #t #f p roots b in
        let cof = poly_prod_linears #t #f (prod_linears_peel #t #f b roots) in
        let term = poly_scale #t rb cof in
        let rest = residue_sum #t #f p roots tl in
        eval_add term rest c;
        eval_mul (rb @ poly_zero) cof c;
        let _ : squash (poly_eval (rb @ poly_zero) c = rb) =
          if rb = (zero <: t) then begin
            eval_zero #t c;
            symmetry rb (zero <: t);
            transitivity (poly_eval (rb @ poly_zero) c) (zero <: t) rb
          end else
            eval_singleton #t #f rb c in
        mul_congruence (poly_eval (rb @ poly_zero) c) (poly_eval cof c) rb (poly_eval cof c);
        transitivity (poly_eval term c)
                     (poly_eval (rb @ poly_zero) c * poly_eval cof c)
                     (rb * poly_eval cof c);
        if b = c then begin
          (* point congruence: for b = c, eval q b = eval q c. *)
          let rec cpow_congr (i:nat) : Lemma (ensures cpow b i = cpow c i) (decreases i) =
            if i = 0 then reflexivity (cpow b 0)
            else begin
              cpow_congr (i - 1);
              mul_congruence b (cpow b (i - 1)) c (cpow c (i - 1))
            end in
          let eval_pt_congr (q: polynomial t) : Lemma (poly_eval q b = poly_eval q c) =
            let step (i:nat{0 <= i /\ i < L.length q}) : Lemma (eval_term q b i = eval_term q c i) =
              cpow_congr i;
              mul_congruence (coeff q i) (cpow b i) (coeff q i) (cpow c i) in
            Core.FinSum.sum_range_congruence (eval_term q b) (eval_term q c) 0 (L.length q) step in
          (* tl excludes c (head distinctness, b = c), so eval rest c = 0 *)
          let off (d:t) : Lemma (L.memP d tl ==> not (d = c)) =
            let inner () : Lemma (requires L.memP d tl) (ensures not (d = c)) =
              symmetry b d in
            Classical.move_requires inner () in
          Classical.forall_intro off;
          eval_residue_sum_vanishes #t #f p roots tl c;
          (* q'(b) = eval cof b ; with point congruence, eval cof c = eval cof b *)
          deriv_prod_at_root #t #f b roots;
          eval_pt_congr cof;
          let qd : t = poly_eval (poly_deriv (poly_prod_linears #t #f roots)) b in
          symmetry qd (poly_eval cof b);
          transitivity (poly_eval cof c) (poly_eval cof b) qd;
          split_deriv_nonzero #t #f b roots;
          let pc : t = poly_eval p b in
          let iq : t = (f.f_sf.sf_mig).inv qd in
          (* rb == pc * iq  (residue definition, qd is the same denominator) *)
          mul_congruence rb (poly_eval cof c) (pc * iq) qd;
          transitivity (poly_eval term c) (rb * poly_eval cof c) ((pc * iq) * qd);
          mul_associativity pc iq qd;
          f.f_sf.sf_mig.inversion_lemma qd;
          mul_congruence pc (iq * qd) pc (one <: t);
          H.x_mul_one #t pc;
          transitivity (pc * (iq * qd)) (pc * (one <: t)) pc;
          transitivity ((pc * iq) * qd) (pc * (iq * qd)) pc;
          transitivity (poly_eval term c) ((pc * iq) * qd) pc;
          (* eval (term + rest) c = pc + zero = pc = eval p b ; bridge to eval p c *)
          add_congruence (poly_eval term c) (poly_eval rest c) pc (zero <: t);
          H.x_plus_zero #t pc;
          transitivity (poly_eval (residue_sum #t #f p roots sub) c)
                       (poly_eval term c + poly_eval rest c)
                       (pc + (zero <: t));
          transitivity (poly_eval (residue_sum #t #f p roots sub) c)
                       (pc + (zero <: t))
                       pc;
          eval_pt_congr p;
          transitivity (poly_eval (residue_sum #t #f p roots sub) c) pc (poly_eval p c)
        end else begin
          cofactor_eval_off #t #f b c roots;
          mul_congruence rb (poly_eval cof c) rb (zero <: t);
          H.x_mul_zero #t rb;
          transitivity (rb * poly_eval cof c) (rb * (zero <: t)) (zero <: t);
          transitivity (poly_eval term c) (rb * poly_eval cof c) (zero <: t);
          eliminate (c == b) \/ (L.memP c tl)
          returns L.memP c tl
          with _h_eq. (H.leibniz_to_eq c b; symmetry c b)
          and _h_tl. ();
          eval_residue_sum_at_root #t #f p roots tl c;
          add_congruence (poly_eval term c) (poly_eval rest c) (zero <: t) (poly_eval p c);
          H.zero_plus_x #t (poly_eval p c);
          transitivity (poly_eval (residue_sum #t #f p roots sub) c)
                       (poly_eval term c + poly_eval rest c)
                       ((zero <: t) + poly_eval p c);
          transitivity (poly_eval (residue_sum #t #f p roots sub) c)
                       ((zero <: t) + poly_eval p c)
                       (poly_eval p c)
        end

(* ================================================================ *)
(*  STEP 1 support.  Degree of a product of linear factors and a     *)
(*  scaled polynomial; degree bound on the residue partial-fraction  *)
(*  numerator.                                                       *)
(* ================================================================ *)

(* poly_deg poly_one = Some 0 (over a field, one <> zero). *)
let poly_one_deg (#t:Type) {| f: field t |} ()
  : Lemma (poly_deg (poly_one #t) == (Some 0 <: option nat))
  = H.elim_equatable_laws t ();
    let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    poly_lc_reveal (poly_one #t)

(* deg (poly_prod_linears roots) = Some (length roots). *)
let rec poly_prod_linears_deg (#t:Type) {| f: field t |} (roots: list t)
  : Lemma (ensures poly_deg (poly_prod_linears #t #f roots) == (Some (L.length roots) <: option nat))
          (decreases roots)
  = match roots with
    | []        -> poly_one_deg #t #f ()
    | a :: rest ->
        let la = poly_linear #t #f a in
        let pr = poly_prod_linears #t #f rest in
        poly_linear_deg #t #f a;                 (* deg la = Some 1 *)
        poly_prod_linears_deg #t #f rest;        (* IH: deg pr = Some (length rest) *)
        poly_deg_mul #t #(id_of_f t) la pr       (* deg (la*pr) = 1 + length rest *)

(* high coeffs of a scaled poly vanish (mirror of LRTResultant). *)
let coeff_zero_above_k_of_scale_loc (#t:Type) {| f: field t |} (c: t) (qq: polynomial t) (k:nat) (i:nat)
  : Lemma (requires i >= k /\ (None? (poly_deg qq) \/ Some?.v (poly_deg qq) < k))
          (ensures coeff (poly_scale #t c qq) i = (zero <: t))
  = H.elim_equatable_laws t ();
    coeff_above_degree qq i;                       (* coeff qq i = zero *)
    poly_mul_singleton_coeff c qq i;               (* coeff (poly_scale c qq) i = c * coeff qq i *)
    H.x_mul_zero c;                                (* c * zero = zero *)
    reflexivity c;
    mul_congruence c (coeff qq i) c (zero <: t);
    transitivity (coeff (poly_scale #t c qq) i) (c * coeff qq i) (c * (zero <: t));
    transitivity (coeff (poly_scale #t c qq) i) (c * (zero <: t)) (zero <: t)

(* deg (poly_scale c qq) < k when deg qq < k (mirror of LRTResultant). *)
let poly_scale_deg_le_loc (#t:Type) {| f: field t |} (c: t) (qq: polynomial t) (k:nat)
  : Lemma (requires (None? (poly_deg qq) \/ Some?.v (poly_deg qq) < k))
          (ensures (None? (poly_deg (poly_scale #t c qq)) \/
                    Some?.v (poly_deg (poly_scale #t c qq)) < k))
  = match poly_deg (poly_scale #t c qq) with
    | None   -> ()
    | Some d ->
        if d < k then ()
        else begin
          coeff_zero_above_k_of_scale_loc #t #f c qq k d;
          leading_coeff_nonzero (poly_scale #t c qq)
        end

(* degree bound on the residue partial-fraction numerator over `sub`. *)
let rec residue_sum_degree_bound (#t:Type) {| f: field t |} (p: polynomial t) (roots sub: list t)
  : Lemma (requires (forall (b:t). L.memP b sub ==> L.memP b roots) /\ all_distinct #t roots)
          (ensures Some? (poly_deg (residue_sum #t #f p roots sub)) ==>
                   Some?.v (poly_deg (residue_sum #t #f p roots sub)) < L.length roots)
          (decreases sub)
  = match sub with
    | []      -> ()                                (* residue_sum = poly_zero, deg = None *)
    | b :: tl ->
        let rb   = residue #t #f p roots b in
        let peel = prod_linears_peel #t #f b roots in
        let cof  = poly_prod_linears #t #f peel in
        let term = poly_scale #t rb cof in
        let rest = residue_sum #t #f p roots tl in
        (* deg cof = Some (length roots - 1) < length roots. *)
        poly_prod_linears_deg #t #f peel;
        (* term: deg < length roots. *)
        poly_scale_deg_le_loc #t #f rb cof (L.length roots);
        (* rest: deg < length roots by IH. *)
        residue_sum_degree_bound #t #f p roots tl;
        (* poly_add bound. *)
        poly_add_degree_bound #t #(cr_of_id t #(id_of_f t)) term rest (L.length roots)

(* ================================================================ *)
(*  Group cancellation:  x + (neg y) = zero  ==>  x = y.             *)
(* ================================================================ *)

let lemma_sub_zero_imp_eq (#u:Type) {| g: add_comm_group u |} (x y: u)
  : Lemma (requires (x + neg y) = (zero <: u)) (ensures x = y)
  = H.elim_equatable_laws u ();
    H.trans_for_calc u ();
    (* m = (x + neg y) + y *)
    add_associativity x (neg y) y;                 (* m = x + (neg y + y) *)
    H.neg_x_plus_x y;                              (* neg y + y = zero *)
    add_congruence x (neg y + y) x (zero <: u);    (* x+(neg y+y) = x+zero *)
    H.x_plus_zero x;                               (* x+zero = x *)
    transitivity ((x + neg y) + y) (x + (neg y + y)) (x + (zero <: u));
    transitivity ((x + neg y) + y) (x + (zero <: u)) x;     (* m = x *)
    add_congruence (x + neg y) y (zero <: u) y;    (* m = zero+y *)
    H.zero_plus_x y;                               (* zero+y = y *)
    transitivity ((x + neg y) + y) ((zero <: u) + y) y;     (* m = y *)
    symmetry ((x + neg y) + y) x;                  (* x = m *)
    transitivity x ((x + neg y) + y) y             (* x = y *)

(* ================================================================ *)
(*  STEP 2 — CAPSTONE.  Interpolation identity:                      *)
(*    p  ~  Sum_{b in roots} r_b * prod_{i<>b}(x - beta_i)           *)
(*  whenever deg p < #roots and the roots are distinct.              *)
(* ================================================================ *)

let interpolation_identity (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  : Lemma (requires all_distinct #t roots /\
                    (Some? (poly_deg p) ==> Some?.v (poly_deg p) < L.length roots))
          (ensures poly_eq p (residue_sum #t #f p roots roots))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cr_p : commutative_ring (polynomial t) = TC.solve in
    let g : add_comm_group (polynomial t) = cr_p.cr_r.r_add in
    let pp = residue_sum #t #f p roots roots in
    let d  = poly_sub p pp in
    (* (1) d vanishes at every root c. *)
    let vanish (c:t) : Lemma (requires L.memP c roots)
                            (ensures poly_eval d c = (zero <: t)) =
      eval_residue_sum_at_root #t #f p roots roots c;   (* poly_eval pp c = poly_eval p c *)
      poly_sub_reveal p pp;                             (* d == poly_add p (poly_neg pp) *)
      eval_add p (poly_neg pp) c;                       (* eval d c = eval p c + eval (neg pp) c *)
      eval_neg pp c;                                    (* eval (neg pp) c = neg (eval pp c) *)
      reflexivity (poly_eval p c);
      add_congruence (poly_eval p c) (poly_eval (poly_neg pp) c)
                     (poly_eval p c) (neg (poly_eval pp c));
      transitivity (poly_eval d c)
                   (poly_eval p c + poly_eval (poly_neg pp) c)
                   (poly_eval p c + neg (poly_eval pp c));
      (* eval pp c = eval p c, so neg (eval pp c) = neg (eval p c). *)
      neg_congruence (poly_eval pp c) (poly_eval p c);
      add_congruence (poly_eval p c) (neg (poly_eval pp c))
                     (poly_eval p c) (neg (poly_eval p c));
      transitivity (poly_eval d c)
                   (poly_eval p c + neg (poly_eval pp c))
                   (poly_eval p c + neg (poly_eval p c));
      H.x_plus_neg_x (poly_eval p c);                  (* p(c) + neg p(c) = zero *)
      transitivity (poly_eval d c)
                   (poly_eval p c + neg (poly_eval p c))
                   (zero <: t)
    in
    Classical.forall_intro (Classical.move_requires vanish);
    (* (2) degree bound on d. *)
    residue_sum_degree_bound #t #f p roots roots;       (* deg pp < #roots *)
    poly_sub_degree_bound #t #(cr_of_id t #(id_of_f t)) p pp (L.length roots);
    (* (3) interpolation uniqueness: d ~ poly_zero. *)
    low_degree_many_roots_zero #t #f d roots;
    (* (4) d = poly_add p (poly_neg pp) ~ 0  ==>  p ~ pp. *)
    poly_sub_reveal p pp;
    lemma_sub_zero_imp_eq #(polynomial t) #g p pp

(* ================================================================ *)
(*  FRACTION-LEVEL WRAP.  The polynomial interpolation identity       *)
(*    p ~ residue_sum p roots roots   (interpolation_identity)        *)
(*  lifts to an equality of rational functions over the common        *)
(*  denominator q = prod roots:  p/q = P/q  as elements of            *)
(*    fraction ((polynomial_integral_domain_instance).pid).           *)
(* ================================================================ *)

(* The product of linear factors is a nonzero denominator whenever     *)
(* roots is nonempty:  poly_deg = Some (length roots) >= 1, so it is   *)
(* not poly_eq to poly_zero (whose degree is None).                   *)
let prod_linears_nonzero (#t:Type) {| f: field t |} (roots: list t)
  : Lemma (requires Cons? roots)
          (ensures  is_nonzero #(polynomial t) (poly_prod_linears #t #f roots))
  = let q = poly_prod_linears #t #f roots in
    poly_prod_linears_deg #t #f roots;                 (* poly_deg q == Some (length roots) *)
    (* if q were poly_eq poly_zero, degree_well_defined forces deg q == deg poly_zero == None. *)
    let aux () : Lemma (requires poly_eq q (poly_zero #t)) (ensures False) =
      Core.Polynomial.Unique.degree_well_defined #t q (poly_zero #t);
      assert (poly_deg (poly_zero #t) == (None <: option nat))
    in
    Classical.move_requires aux ()

(* The same-denominator fraction wrap.  With q = prod roots (nonzero), the     *)
(* fractions p/q and P/q (P = residue_sum p roots roots) are equal as elements *)
(* of fraction over the polynomial integral domain.  By fraction_eq_reveal the *)
(* equality reduces to the cross-product  p * q = q * P  in poly_mul/poly_eq;  *)
(* interpolation_identity gives poly_eq p P, and a comm+congruence chain gives *)
(* poly_eq (poly_mul p q) (poly_mul q P).                                      *)
let pf_same_denom (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  : Lemma (requires Cons? roots /\ all_distinct #t roots /\
                    (Some? (poly_deg p) ==> Some?.v (poly_deg p) < L.length roots))
          (ensures (let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
                    is_nonzero #(polynomial t) (poly_prod_linears #t #f roots) /\
                    (let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears #t #f roots in
                     (Fraction #(polynomial t) #id_p p q)
                       = (Fraction #(polynomial t) #id_p (residue_sum #t #f p roots roots) q))))
  = let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
    prod_linears_nonzero #t #f roots;
    let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears #t #f roots in
    let pp = residue_sum #t #f p roots roots in
    let xf : fraction id_p = Fraction #(polynomial t) #id_p p q in
    let yf : fraction id_p = Fraction #(polynomial t) #id_p pp q in
    (* poly_eq p pp from the interpolation identity. *)
    interpolation_identity #t #f p roots;              (* poly_eq p pp *)
    (* poly_eq (poly_mul p q) (poly_mul q pp):  p*q ~ q*p ~ q*pp. *)
    poly_mul_commutativity #t p q;                     (* p*q ~ q*p *)
    poly_eq_reflexivity #t q;
    poly_mul_congruence #t q p q pp;                   (* q*p ~ q*pp *)
    poly_eq_transitivity #t (poly_mul p q) (poly_mul q p) (poly_mul q pp);
    (* fraction_eq_reveal:  (xf = yf) <==> (num xf * den yf = den xf * num yf) *)
    (*   num xf = p, den yf = q, den xf = q, num yf = pp.                       *)
    fraction_eq_reveal #(polynomial t) #id_p xf yf


(* ================================================================ *)
(*  poly_linear b is a nonzero polynomial (deg = Some 1).            *)
(* ================================================================ *)
let poly_linear_nonzero (#t:Type) {| f: field t |} (b: t)
  : Lemma (ensures is_nonzero #(polynomial t) (poly_linear #t #f b))
  = let lb = poly_linear #t #f b in
    poly_linear_deg #t #f b;                           (* poly_deg lb == Some 1 *)
    let aux () : Lemma (requires poly_eq lb (poly_zero #t)) (ensures False) =
      Core.Polynomial.Unique.degree_well_defined #t lb (poly_zero #t);
      assert (poly_deg (poly_zero #t) == (None <: option nat))
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
  : Lemma (requires L.memP b roots /\ all_distinct #t roots)
          (ensures (let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
                    is_nonzero #(polynomial t) (poly_prod_linears #t #f roots) /\
                    is_nonzero #(polynomial t) (poly_linear #t #f b) /\
                    (let q  : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears #t #f roots in
                     let lb : (ll:polynomial t{is_nonzero ll}) = poly_linear #t #f b in
                     let cof = poly_prod_linears #t #f (prod_linears_peel #t #f b roots) in
                     let rb : t = residue #t #f p roots b in
                     (Fraction #(polynomial t) #id_p (poly_scale #t rb cof) q)
                       = (Fraction #(polynomial t) #id_p (rb @ poly_zero) lb))))
  = let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
    (* nonzero denominators. *)
    prod_linears_nonzero #t #f roots;
    poly_linear_nonzero #t #f b;
    let q  : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears #t #f roots in
    let lb : (ll:polynomial t{is_nonzero ll}) = poly_linear #t #f b in
    let peel = prod_linears_peel #t #f b roots in      (* poly_eq roots-prod  (lb * cof) *)
    let cof = poly_prod_linears #t #f peel in
    let rb  = residue #t #f p roots b in
    let r1  = rb @ poly_zero in                        (* the singleton [rb] *)
    (* poly_scale rb cof == poly_mul r1 cof, definitionally. *)
    assert (poly_scale #t rb cof == poly_mul r1 cof);
    (* Cross-product goal (poly_eq):                                   *)
    (*   poly_mul (poly_mul r1 cof) lb  ~  poly_mul q r1               *)
    (* via the chain  (r1*cof)*lb ~ r1*(cof*lb) ~ r1*(lb*cof)          *)
    (*               ~ (lb*cof)*r1 ~ q*r1.                             *)
    (* step 1: (r1*cof)*lb ~ r1*(cof*lb)  (assoc). *)
    poly_mul_associativity #t r1 cof lb;
    (* step 2: cof*lb ~ lb*cof,  congr with refl r1. *)
    poly_mul_commutativity #t cof lb;
    poly_eq_reflexivity #t r1;
    poly_mul_congruence #t r1 (poly_mul cof lb) r1 (poly_mul lb cof);
    poly_eq_transitivity #t (poly_mul (poly_mul r1 cof) lb)
                            (poly_mul r1 (poly_mul cof lb))
                            (poly_mul r1 (poly_mul lb cof));
    (* step 3: r1*(lb*cof) ~ (lb*cof)*r1  (comm). *)
    poly_mul_commutativity #t r1 (poly_mul lb cof);
    poly_eq_transitivity #t (poly_mul (poly_mul r1 cof) lb)
                            (poly_mul r1 (poly_mul lb cof))
                            (poly_mul (poly_mul lb cof) r1);
    (* step 4: (lb*cof)*r1 ~ q*r1,  from q ~ lb*cof (peel, already in *)
    (* scope via cof's definition) reversed. *)
    poly_eq_symmetry #t q (poly_mul lb cof);
    poly_eq_reflexivity #t r1;
    poly_mul_congruence #t (poly_mul lb cof) r1 q r1;
    poly_eq_transitivity #t (poly_mul (poly_mul r1 cof) lb)
                            (poly_mul (poly_mul lb cof) r1)
                            (poly_mul q r1);
    (* hence poly_eq (poly_mul (poly_scale rb cof) lb) (poly_mul q r1). *)
    (* fraction_eq_reveal: (xf = yf) <==> num xf * den yf = den xf * num yf *)
    (*   num xf = poly_scale rb cof,  den yf = lb,  den xf = q,  num yf = r1. *)
    let xf : fraction id_p = Fraction #(polynomial t) #id_p (poly_scale #t rb cof) q in
    let yf : fraction id_p = Fraction #(polynomial t) #id_p r1 lb in
    fraction_eq_reveal #(polynomial t) #id_p xf yf

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
    reflexivity (yd * yd);
    mul_congruence (n1 * d2) (yd * yd) (d1 * n2) (yd * yd);
    reflexivity ((d1 * d2) * (yn * yd));
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
    frac_add_cong_cross #t #d x1.num x1.den x2.num x2.den y.num y.den ()

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
    frac_add_comm_cross #t #d x.num x.den y.num y.den

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
                          (q: polynomial t{is_nonzero #(polynomial t) q})
  : Lemma (let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
           (Fraction #(polynomial t) #id_p (poly_add a b) q)
             = (fraction_add #(polynomial t) #id_p
                  (Fraction #(polynomial t) #id_p a q)
                  (Fraction #(polynomial t) #id_p b q)))
  = let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
    let xa : fraction id_p = Fraction #(polynomial t) #id_p a q in
    let xb : fraction id_p = Fraction #(polynomial t) #id_p b q in
    let lhs : fraction id_p = Fraction #(polynomial t) #id_p (poly_add a b) q in
    let rhs : fraction id_p = fraction_add #(polynomial t) #id_p xa xb in
    fraction_add_reveal #(polynomial t) #id_p xa xb;   (* num rhs = a*q + q*b, den rhs = q*q *)
    fraction_eq_reveal #(polynomial t) #id_p lhs rhs;  (* goal <==> cross product *)
    frac_split_cross #(polynomial t) #id_p a b q

(* ================================================================ *)
(*  The simple fraction  residue_b / (x - beta_b)  for one root b.    *)
(* ================================================================ *)
let simple_term (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (b: t)
  : Pure (fraction (polynomial_integral_domain_instance #t #(id_of_f t)).pid)
         (requires L.memP b roots /\ all_distinct #t roots)
         (ensures fun _ -> True)
  = poly_linear_nonzero #t #f b;
    Fraction ((residue #t #f p roots b) @ poly_zero) (poly_linear #t #f b)

(* ================================================================ *)
(*  The fraction-level residue sum over a sublist `sub`:              *)
(*    Sum_{b in sub}  residue_b / (x - beta_b)                        *)
(*  built with the NAMED constructors fraction_add / fraction_zero.   *)
(* ================================================================ *)
let rec frac_sum (#t:Type) {| f: field t |} (p: polynomial t) (roots sub: list t)
  : Pure (fraction (polynomial_integral_domain_instance #t #(id_of_f t)).pid)
         (requires (forall (b:t). L.memP b sub ==> L.memP b roots) /\ all_distinct #t roots)
         (ensures fun _ -> True)
         (decreases sub)
  = match sub with
    | [] -> fraction_zero (polynomial t)
    | b :: tl -> fraction_add (simple_term #t #f p roots b) (frac_sum #t #f p roots tl)

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
                    all_distinct #t roots)
          (ensures (let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
                    is_nonzero #(polynomial t) (poly_prod_linears #t #f roots) /\
                    (let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears #t #f roots in
                     (Fraction #(polynomial t) #id_p (residue_sum #t #f p roots sub) q)
                       = (frac_sum #t #f p roots sub))))
          (decreases sub)
  = let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
    prod_linears_nonzero #t #f roots;
    let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears #t #f roots in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    match sub with
    | [] ->
        (* Fraction poly_zero q  =  fraction_zero (polynomial t). *)
        let w  : fraction id_p = Fraction #(polynomial t) #id_p (poly_zero #t) q in
        let fz : fraction id_p = fraction_zero (polynomial t) #id_p in
        fraction_zero_reveal (polynomial t) #id_p;        (* fz.num = poly_zero, fz.den = poly_one *)
        fraction_eq_reveal #(polynomial t) #id_p w fz;    (* goal <==> poly_zero*poly_one = q*poly_zero *)
        frac_zero_cross #(polynomial t) #id_p q
    | b :: tl ->
        let rb   = residue #t #f p roots b in
        let term = poly_scale #t rb (poly_prod_linears #t #f (prod_linears_peel #t #f b roots)) in
        let rest = residue_sum #t #f p roots tl in
        (* residue_sum p roots (b::tl) == poly_add term rest  (definitional). *)
        let fterm : fraction id_p = Fraction #(polynomial t) #id_p term q in
        let frest : fraction id_p = Fraction #(polynomial t) #id_p rest q in
        let st    : fraction id_p = simple_term #t #f p roots b in
        (* (1) split the same-denominator sum. *)
        frac_split_same_denom #t #f term rest q;          (* Fraction (poly_add term rest) q = fterm (+) frest *)
        (* (2) the b-residue term over q is the simple fraction st. *)
        residue_term_as_simple #t #f p roots b;           (* fterm = st *)
        frac_add_cong #(polynomial t) #id_p fterm st frest;  (* fterm(+)frest = st(+)frest *)
        (* (3) inductive hypothesis on the tail. *)
        residue_sum_frac_decomp #t #f p roots tl;         (* frest = frac_sum tl *)
        frac_add_cong_r #(polynomial t) #id_p st frest (frac_sum #t #f p roots tl);
        (* chain:  Fraction (poly_add term rest) q
                     = fterm(+)frest = st(+)frest = st(+)frac_sum tl = frac_sum (b::tl). *)
        transitivity (Fraction #(polynomial t) #id_p (poly_add term rest) q)
                     (fraction_add #(polynomial t) #id_p fterm frest)
                     (fraction_add #(polynomial t) #id_p st frest);
        transitivity (Fraction #(polynomial t) #id_p (poly_add term rest) q)
                     (fraction_add #(polynomial t) #id_p st frest)
                     (fraction_add #(polynomial t) #id_p st (frac_sum #t #f p roots tl))

(* ================================================================ *)
(*  CAPSTONE.  Fraction-level partial-fraction decomposition:         *)
(*    p / q  =  Sum_{b in roots} (p(b)/q'(b)) / (x - b)               *)
(*  whenever deg p < #roots and the roots are distinct.               *)
(* ================================================================ *)
let partial_fraction_decomposition (#t:Type) {| f: field t |}
                                   (p: polynomial t) (roots: list t)
  : Lemma (requires Cons? roots /\ all_distinct #t roots /\
                    (Some? (poly_deg p) ==> Some?.v (poly_deg p) < L.length roots))
          (ensures (let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
                    is_nonzero #(polynomial t) (poly_prod_linears #t #f roots) /\
                    (let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears #t #f roots in
                     (Fraction #(polynomial t) #id_p p q)
                       = (frac_sum #t #f p roots roots))))
  = let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
    prod_linears_nonzero #t #f roots;
    let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears #t #f roots in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    (* p/q = (residue_sum p roots roots)/q *)
    pf_same_denom #t #f p roots;
    (* (residue_sum p roots roots)/q = frac_sum p roots roots *)
    residue_sum_frac_decomp #t #f p roots roots;
    transitivity (Fraction #(polynomial t) #id_p p q)
                 (Fraction #(polynomial t) #id_p (residue_sum #t #f p roots roots) q)
                 (frac_sum #t #f p roots roots)

(* ================================================================ *)
(*  Logarithmic-derivative residues.                                  *)
(*  For v = prod_linears roots, the residue of v' at each root is 1.  *)
(* ================================================================ *)

(* Lemma 1.  residue(v') at b = 1, where v = poly_prod_linears roots. *)
let residue_of_deriv_is_one (#t:Type) {| f: field t |} (roots: list t) (b: t)
  : Lemma (requires L.memP b roots /\ all_distinct #t roots)
          (ensures residue #t #f (poly_deriv (poly_prod_linears #t #f roots)) roots b = (one <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    (* x := q'(b), the denominator value; it is nonzero. *)
    let x : t = poly_eval (poly_deriv (poly_prod_linears #t #f roots)) b in
    split_deriv_nonzero #t #f b roots;                 (* not (x = zero), i.e. is_nonzero x *)
    (* residue (poly_deriv v) roots b
         = poly_eval (poly_deriv v) b * inv x = x * inv x   (defeq: poly_deriv v == poly_deriv (poly_prod_linears roots)). *)
    f.f_sf.sf_mig.inversion_lemma x                    (* x * (inv x) = one *)

(* ================================================================ *)
(*  Generic degree upper bound for the derivative.                    *)
(*  If deg(D p) = Some m then m < deg p (when deg p is Some n>=1).     *)
(*  Mirrors the char0-free upper-bound branch of poly_deriv_degree.   *)
(* ================================================================ *)

let poly_deriv_deg_lt (#t:Type) {| f: field t |} (p: polynomial t)
  : Lemma (requires Some? (poly_deg p) /\ Some?.v (poly_deg p) >= 1)
          (ensures Some? (poly_deg (poly_deriv #t #(cr_of_id t #(id_of_f t)) p)) ==>
                   Some?.v (poly_deg (poly_deriv #t #(cr_of_id t #(id_of_f t)) p))
                     < Some?.v (poly_deg p))
  = H.elim_equatable_laws t ();
    let n = Some?.v (poly_deg p) in
    let dp = poly_deriv #t #(cr_of_id t #(id_of_f t)) p in
    introduce Some? (poly_deg dp) ==> Some?.v (poly_deg dp) < n
    with _pf. begin
      let m = Some?.v (poly_deg dp) in
      if m >= n then begin
        (* leading coeff of dp at m is nonzero ... *)
        leading_coeff_nonzero dp;
        (* ... but coeff dp m = nat_scale (m+1) (coeff p (m+1)) = nat_scale (m+1) zero = zero. *)
        poly_deriv_coeff p m;
        coeff_above_degree p (Prims.op_Addition m 1);   (* coeff p (m+1) = zero  (m+1 > n) *)
        nat_scale_congruence #t #((cr_of_id t #(id_of_f t)).cr_r.r_add)
                             (Prims.op_Addition m 1) (coeff p (Prims.op_Addition m 1)) (zero <: t);
        nat_scale_zero_element #t #((cr_of_id t #(id_of_f t)).cr_r.r_add) (Prims.op_Addition m 1);
        transitivity (coeff dp m)
                     (nat_scale #t #((cr_of_id t #(id_of_f t)).cr_r.r_add) (Prims.op_Addition m 1) (coeff p (Prims.op_Addition m 1)))
                     (nat_scale #t #((cr_of_id t #(id_of_f t)).cr_r.r_add) (Prims.op_Addition m 1) (zero <: t));
        transitivity (coeff dp m)
                     (nat_scale #t #((cr_of_id t #(id_of_f t)).cr_r.r_add) (Prims.op_Addition m 1) (zero <: t))
                     (zero <: t)
      end else ()
    end

(* ================================================================ *)
(*  Lemma 2.  Partial-fraction form of the logarithmic derivative:    *)
(*    v'/v = frac_sum of v' over the roots, for v = prod_linears.     *)
(* ================================================================ *)

let log_deriv_prod_linears (#t:Type) {| f: field t |} (roots: list t)
  : Lemma (requires Cons? roots /\ all_distinct #t roots)
          (ensures (let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
                    is_nonzero #(polynomial t) (poly_prod_linears #t #f roots) /\
                    (let v : (vv:polynomial t{is_nonzero vv}) = poly_prod_linears #t #f roots in
                     (Fraction #(polynomial t) #id_p (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots)) v)
                       = (frac_sum #t #f (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots)) roots roots))))
  = let v = poly_prod_linears #t #f roots in
    let pd = poly_deriv #t #(cr_of_id t #(id_of_f t)) v in
    (* deg v = Some (length roots), and length roots >= 1 since Cons? roots. *)
    poly_prod_linears_deg #t #f roots;
    (* discharge the degree precondition of partial_fraction_decomposition for p = pd. *)
    introduce Some? (poly_deg pd) ==> Some?.v (poly_deg pd) < L.length roots
    with _pf. begin
      (* deg v = Some (length roots) >= 1, so deg(deriv v) < length roots. *)
      poly_prod_linears_deg #t #f roots;
      poly_deriv_deg_lt #t #f v
    end;
    partial_fraction_decomposition #t #f pd roots

(* ================================================================ *)
(*  Scaled logarithmic-derivative residues.                          *)
(*  For v = prod_linears roots, the residue of (c.v') at each root    *)
(*  is the constant c.                                                *)
(* ================================================================ *)

(* Lemma 1.  residue(c.v') at b = c, where v = poly_prod_linears roots. *)
let residue_of_scaled_deriv_is_const (#t:Type) {| f: field t |} (c: t) (roots: list t) (b: t)
  : Lemma (requires L.memP b roots /\ all_distinct #t roots)
          (ensures residue #t #f (poly_scale #t c (poly_deriv (poly_prod_linears #t #f roots))) roots b = c)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pd = poly_deriv (poly_prod_linears #t #f roots) in
    let x : t = poly_eval pd b in
    split_deriv_nonzero #t #f b roots;                 (* not (x = zero), i.e. is_nonzero x *)
    let p = poly_scale #t c pd in
    (* poly_eval p b = poly_eval (c @ poly_zero) b * x. *)
    eval_mul (c @ poly_zero) pd b;
    (* poly_eval (c @ poly_zero) b = c. *)
    let _ : squash (poly_eval (c @ poly_zero) b = c) =
      if c = (zero <: t) then begin
        eval_zero #t b;
        symmetry c (zero <: t);
        transitivity (poly_eval (c @ poly_zero) b) (zero <: t) c
      end else
        eval_singleton #t #f c b in
    (* poly_eval p b = c * x. *)
    mul_congruence (poly_eval (c @ poly_zero) b) x c x;
    transitivity (poly_eval p b)
                 (poly_eval (c @ poly_zero) b * x)
                 (c * x);
    (* residue p roots b = poly_eval p b * inv x = (c*x) * inv x. *)
    let ix = (f.f_sf.sf_mig).inv x in
    mul_congruence (poly_eval p b) ix (c * x) ix;
    (* (c*x)*inv x = c*(x*inv x). *)
    mul_associativity c x ix;
    (* x*inv x = one. *)
    f.f_sf.sf_mig.inversion_lemma x;
    mul_congruence c (x * ix) c (one <: t);
    (* c*one = c. *)
    H.x_mul_one c;
    (* chain. *)
    transitivity (residue #t #f p roots b) (poly_eval p b * ix) ((c * x) * ix);
    transitivity ((c * x) * ix) (c * (x * ix)) (c * (one <: t));
    transitivity (c * (x * ix)) (c * (one <: t)) c;
    transitivity ((c * x) * ix) (c * (x * ix)) c;
    transitivity (residue #t #f p roots b) ((c * x) * ix) c

(* ================================================================ *)
(*  Lemma 2.  Partial-fraction form of the scaled log-derivative:     *)
(*    (c.v')/v = frac_sum of (c.v') over the roots, for v = prod.      *)
(* ================================================================ *)

let scaled_log_deriv (#t:Type) {| f: field t |} (c: t) (roots: list t)
  : Lemma (requires Cons? roots /\ all_distinct #t roots)
          (ensures (let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
                    is_nonzero #(polynomial t) (poly_prod_linears #t #f roots) /\
                    (let v : (vv:polynomial t{is_nonzero vv}) = poly_prod_linears #t #f roots in
                     (Fraction #(polynomial t) #id_p
                        (poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))) v)
                       = (frac_sum #t #f (poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))) roots roots))))
  = let v = poly_prod_linears #t #f roots in
    let pd = poly_deriv #t #(cr_of_id t #(id_of_f t)) v in
    let p = poly_scale #t c pd in
    (* deg v = Some (length roots), and length roots >= 1 since Cons? roots. *)
    poly_prod_linears_deg #t #f roots;
    (* discharge the degree precondition of partial_fraction_decomposition for p. *)
    introduce Some? (poly_deg p) ==> Some?.v (poly_deg p) < L.length roots
    with _pf. begin
      (* deg v = Some (length roots) >= 1, so deg(deriv v) < length roots. *)
      poly_prod_linears_deg #t #f roots;
      poly_deriv_deg_lt #t #f v;
      (* deg (poly_scale c pd) <= deg pd < length roots. *)
      poly_scale_deg_le_loc #t #f c pd (L.length roots)
    end;
    partial_fraction_decomposition #t #f p roots

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
    frac_add_zero_l_cross #t #d x.num x.den

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
    frac_add_assoc_cross #t #d x.num x.den y.num y.den z.num z.den

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
                    all_distinct #t roots)
          (ensures (frac_sum #t #f p roots (L.append sub1 sub2))
                 = (fraction_add (frac_sum #t #f p roots sub1)
                                 (frac_sum #t #f p roots sub2)))
          (decreases sub1)
  = let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    match sub1 with
    | [] ->
        (* L.append [] sub2 == sub2 (defeq); frac_sum [] = fraction_zero. *)
        let fs2 : fraction id_p = frac_sum #t #f p roots sub2 in
        let fz  : fraction id_p = frac_sum #t #f p roots [] in
        (* fz == fraction_zero (polynomial t) #id_p definitionally. *)
        frac_add_zero_l #(polynomial t) #id_p fs2;
        (* fraction_add fz fs2 = fs2 ; want fs2 = fraction_add fz fs2. *)
        symmetry (fraction_add #(polynomial t) #id_p fz fs2) fs2
    | b :: tl ->
        (* L.append (b::tl) sub2 == b :: (L.append tl sub2) (defeq). *)
        let st  : fraction id_p = simple_term #t #f p roots b in
        let ftl : fraction id_p = frac_sum #t #f p roots tl in
        let fs2 : fraction id_p = frac_sum #t #f p roots sub2 in
        let fts : fraction id_p = frac_sum #t #f p roots (L.append tl sub2) in
        (* IH on tl: fts = fraction_add ftl fs2. *)
        frac_sum_append #t #f p roots tl sub2;
        (* rewrite under  st (+) (.) :  st(+)fts = st(+)(ftl(+)fs2). *)
        frac_add_cong_r #(polynomial t) #id_p st fts
                        (fraction_add #(polynomial t) #id_p ftl fs2);
        (* regroup:  st(+)(ftl(+)fs2) = (st(+)ftl)(+)fs2. *)
        frac_add_assoc #(polynomial t) #id_p st ftl fs2;
        symmetry (fraction_add #(polynomial t) #id_p
                    (fraction_add #(polynomial t) #id_p st ftl) fs2)
                 (fraction_add #(polynomial t) #id_p st
                    (fraction_add #(polynomial t) #id_p ftl fs2));
        (* chain:  frac_sum (b::(tl@sub2)) = st(+)fts = st(+)(ftl(+)fs2)
                     = (st(+)ftl)(+)fs2 = frac_sum(b::tl) (+) fs2.        *)
        transitivity (fraction_add #(polynomial t) #id_p st fts)
                     (fraction_add #(polynomial t) #id_p st
                        (fraction_add #(polynomial t) #id_p ftl fs2))
                     (fraction_add #(polynomial t) #id_p
                        (fraction_add #(polynomial t) #id_p st ftl) fs2)

(* ================================================================ *)
(*  Per-term congruence: if the residues at b agree, the two simple  *)
(*  terms (same denominator x - b) are equal as fractions.           *)
(* ================================================================ *)
let simple_term_eq_of_residue_eq (#t:Type) {| f: field t |}
      (p1: polynomial t) (roots1: list t) (p2: polynomial t) (roots2: list t) (b: t)
  : Lemma (requires L.memP b roots1 /\ all_distinct #t roots1 /\
                    L.memP b roots2 /\ all_distinct #t roots2 /\
                    residue #t #f p1 roots1 b = residue #t #f p2 roots2 b)
          (ensures (simple_term #t #f p1 roots1 b) = (simple_term #t #f p2 roots2 b))
  = let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
    poly_linear_nonzero #t #f b;
    let lb : (ll:polynomial t{is_nonzero ll}) = poly_linear #t #f b in
    let r1 = residue #t #f p1 roots1 b in
    let r2 = residue #t #f p2 roots2 b in
    let s1 = r1 @ poly_zero in                          (* the singleton [r1] *)
    let s2 = r2 @ poly_zero in                          (* the singleton [r2] *)
    (* poly_eq [r1] [r2] from r1 = r2 (poly_eq poly_zero poly_zero is true). *)
    poly_eq_cons_cons_compute #t r1 (poly_zero #t) r2 (poly_zero #t);
    (* Cross-product goal (poly_eq):  poly_mul s1 lb  ~  poly_mul lb s2.        *)
    (* step 1: s1*lb ~ lb*s1  (comm). *)
    poly_mul_commutativity #t s1 lb;
    (* step 2: lb*s1 ~ lb*s2  (congr: refl lb, poly_eq s1 s2). *)
    poly_eq_reflexivity #t lb;
    poly_mul_congruence #t lb s1 lb s2;
    poly_eq_transitivity #t (poly_mul s1 lb)
                            (poly_mul lb s1)
                            (poly_mul lb s2);
    let xf : fraction id_p = simple_term #t #f p1 roots1 b in
    let yf : fraction id_p = simple_term #t #f p2 roots2 b in
    fraction_eq_reveal #(polynomial t) #id_p xf yf

(* ================================================================ *)
(*  Main: if residues agree on every element of sub, the fraction    *)
(*  sums over sub are equal.                                         *)
(* ================================================================ *)
let rec frac_sum_eq_of_residue_eq (#t:Type) {| f: field t |}
      (p1: polynomial t) (roots1: list t) (p2: polynomial t) (roots2: list t) (sub: list t)
  : Lemma (requires (forall (b:t). L.memP b sub ==> L.memP b roots1) /\ all_distinct #t roots1 /\
                    (forall (b:t). L.memP b sub ==> L.memP b roots2) /\ all_distinct #t roots2 /\
                    (forall (b:t). L.memP b sub ==> residue #t #f p1 roots1 b = residue #t #f p2 roots2 b))
          (ensures (frac_sum #t #f p1 roots1 sub) = (frac_sum #t #f p2 roots2 sub))
          (decreases sub)
  = let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    match sub with
    | [] ->
        (* both frac_sum are fraction_zero; reflexivity. *)
        reflexivity (frac_sum #t #f p1 roots1 [])
    | b :: tl ->
        let st1 : fraction id_p = simple_term #t #f p1 roots1 b in
        let st2 : fraction id_p = simple_term #t #f p2 roots2 b in
        let fs1 : fraction id_p = frac_sum #t #f p1 roots1 tl in
        let fs2 : fraction id_p = frac_sum #t #f p2 roots2 tl in
        (* per-term: st1 = st2. *)
        simple_term_eq_of_residue_eq #t #f p1 roots1 p2 roots2 b;
        (* IH on tl: fs1 = fs2. *)
        frac_sum_eq_of_residue_eq #t #f p1 roots1 p2 roots2 tl;
        (* fraction_add st1 fs1 = fraction_add st2 fs1  (left cong). *)
        frac_add_cong #(polynomial t) #id_p st1 st2 fs1;
        (* fraction_add st2 fs1 = fraction_add st2 fs2  (right cong). *)
        frac_add_cong_r #(polynomial t) #id_p st2 fs1 fs2;
        (* chain. *)
        transitivity (fraction_add #(polynomial t) #id_p st1 fs1)
                     (fraction_add #(polynomial t) #id_p st2 fs1)
                     (fraction_add #(polynomial t) #id_p st2 fs2)

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
        flatten_memP #t gs b

(* ================================================================ *)
(*  Σ over a list of root-groups.                                     *)
(* ================================================================ *)
let rec frac_sum_over_groups (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (groups: list (list t))
  : Pure (fraction (polynomial_integral_domain_instance #t #(id_of_f t)).pid)
         (requires (forall (g:list t). L.memP g groups ==> (forall (b:t). L.memP b g ==> L.memP b roots)) /\ all_distinct #t roots)
         (ensures fun _ -> True)
         (decreases groups)
  = match groups with
    | [] -> fraction_zero (polynomial t)
    | g :: gs -> fraction_add (frac_sum #t #f p roots g) (frac_sum_over_groups #t #f p roots gs)

(* ================================================================ *)
(*  Σ over groups = frac_sum over the flattened list of roots.        *)
(* ================================================================ *)
let rec frac_sum_flatten (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (groups: list (list t))
  : Lemma (requires (forall (g:list t). L.memP g groups ==> (forall (b:t). L.memP b g ==> L.memP b roots)) /\ all_distinct #t roots)
          (ensures (frac_sum_over_groups #t #f p roots groups) = (frac_sum #t #f p roots (L.flatten groups)))
          (decreases groups)
  = let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    match groups with
    | [] ->
        (* L.flatten [] == []; both sides fraction_zero. *)
        reflexivity (frac_sum_over_groups #t #f p roots [])
    | g :: gs ->
        (* RHS: L.flatten (g::gs) == L.append g (L.flatten gs) (defeq). *)
        let fg  : fraction id_p = frac_sum #t #f p roots g in
        let fgs : fraction id_p = frac_sum_over_groups #t #f p roots gs in
        let ffl : fraction id_p = frac_sum #t #f p roots (L.flatten gs) in
        (* g ⊆ roots from head of groups hypothesis; flatten gs ⊆ roots via SMTPat. *)
        frac_sum_append #t #f p roots g (L.flatten gs);
        (* frac_sum (append g (flatten gs)) = fraction_add fg ffl. *)
        (* IH on gs: fgs = ffl. *)
        frac_sum_flatten #t #f p roots gs;
        (* rewrite under fg (+) (.) : fg(+)fgs = fg(+)ffl. *)
        frac_add_cong_r #(polynomial t) #id_p fg fgs ffl;
        (* chain: frac_sum_over_groups (g::gs) = fg(+)fgs = fg(+)ffl
                    = frac_sum (append g (flatten gs)). *)
        symmetry (fraction_add #(polynomial t) #id_p fg ffl)
                 (frac_sum #t #f p roots (L.append g (L.flatten gs)));
        transitivity (fraction_add #(polynomial t) #id_p fg fgs)
                     (fraction_add #(polynomial t) #id_p fg ffl)
                     (frac_sum #t #f p roots (L.append g (L.flatten gs)))


(* ================================================================ *)
(*  GROUPING.  One LRT log-term  c.log(prod g),  c = the group's      *)
(*  common residue (= residue of the head).  Its derivative is the    *)
(*  fraction  (c . (prod g)') / (prod g).                             *)
(* ================================================================ *)
let group_contribution (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
      (g: list t)
  : Pure (fraction (polynomial_integral_domain_instance #t #(id_of_f t)).pid)
         (requires Cons? g /\ all_distinct #t g /\ all_distinct #t roots /\
                   (forall (b:t). L.memP b g ==> L.memP b roots))
         (ensures fun _ -> True)
  = prod_linears_nonzero #t #f g;
    let c : t = residue #t #f p roots (L.hd g) in
    let v : (vv:polynomial t{is_nonzero vv}) = poly_prod_linears #t #f g in
    Fraction #(polynomial t) #(polynomial_integral_domain_instance #t #(id_of_f t)).pid
      (poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f g))) v

(* Per-element residue equality bridging the scaled-derivative form over the   *)
(* group `g` to the original residue over `roots`, under homogeneity.          *)
let per_group_residue_eq (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (g: list t) (b: t)
  : Lemma (requires all_distinct #t g /\ all_distinct #t roots /\ L.memP b g /\
                    (forall (bb:t). L.memP bb g ==> L.memP bb roots) /\
                    (forall (bb:t). L.memP bb g ==> residue #t #f p roots bb = residue #t #f p roots (L.hd g)))
          (ensures (let c : t = residue #t #f p roots (L.hd g) in
                    let pd = poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f g)) in
                    residue #t #f pd g b = residue #t #f p roots b))
  = H.elim_equatable_laws t ();
    let c : t = residue #t #f p roots (L.hd g) in
    let pd = poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f g)) in
    (* residue pd g b = c (root list is g). *)
    residue_of_scaled_deriv_is_const #t #f c g b;
    (* c = residue p roots b : hypothesis gives residue p roots b = residue p roots (hd g) = c. *)
    symmetry (residue #t #f p roots b) c;
    (* residue pd g b = c = residue p roots b. *)
    transitivity (residue #t #f pd g b) c (residue #t #f p roots b)

(* ================================================================ *)
(*  PER-GROUP EQUALITY.  Under homogeneity (all residues over the     *)
(*  group equal the head's), the group contribution equals the        *)
(*  partial-fraction terms of that group.                             *)
(* ================================================================ *)
let per_group_eq (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (g: list t)
  : Lemma (requires Cons? g /\ all_distinct #t g /\ all_distinct #t roots /\
                    (forall (b:t). L.memP b g ==> L.memP b roots) /\
                    (forall (b:t). L.memP b g ==> residue #t #f p roots b = residue #t #f p roots (L.hd g)))
          (ensures (group_contribution #t #f p roots g) = (frac_sum #t #f p roots g))
  = let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
    H.elim_equatable_laws (fraction id_p) ();
    prod_linears_nonzero #t #f g;
    let c : t = residue #t #f p roots (L.hd g) in
    let v : (vv:polynomial t{is_nonzero vv}) = poly_prod_linears #t #f g in
    let pd = poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f g)) in
    (* (1) group_contribution p roots g == Fraction pd v  (definitional). *)
    (* (2) scaled_log_deriv : Fraction pd v = frac_sum pd g g. *)
    scaled_log_deriv #t #f c g;
    (* (3) per-element residue equality between (pd over g) and (p over roots). *)
    introduce forall (b:t). L.memP b g ==> residue #t #f pd g b = residue #t #f p roots b
    with introduce L.memP b g ==> residue #t #f pd g b = residue #t #f p roots b
    with _hb. per_group_residue_eq #t #f p roots g b;
    (*     frac_sum pd g g = frac_sum p roots g. *)
    frac_sum_eq_of_residue_eq #t #f pd g p roots g;
    (* (4) chain : Fraction pd v = frac_sum pd g g = frac_sum p roots g. *)
    transitivity (Fraction #(polynomial t) #id_p pd v)
                 (frac_sum #t #f pd g g)
                 (frac_sum #t #f p roots g)

(* ================================================================ *)
(*  DERIVATIVE OF THE LRT ANSWER.  Σ_i c_i·log(∏ group_i) has        *)
(*  derivative the fold of the per-group contributions.              *)
(* ================================================================ *)
let rec answer_deriv (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (groups: list (list t))
  : Pure (fraction (polynomial_integral_domain_instance #t #(id_of_f t)).pid)
         (requires all_distinct #t roots /\
                   (forall (g:list t). L.memP g groups ==>
                       (Cons? g /\ all_distinct #t g /\ (forall (b:t). L.memP b g ==> L.memP b roots))))
         (ensures fun _ -> True)
         (decreases groups)
  = match groups with
    | [] -> fraction_zero (polynomial t)
    | g :: gs -> fraction_add (group_contribution #t #f p roots g) (answer_deriv #t #f p roots gs)

(* ================================================================ *)
(*  Termwise rewrite: under residue-homogeneity per group, the       *)
(*  answer derivative equals the Σ-over-groups of partial fractions.  *)
(* ================================================================ *)
let rec answer_eq_frac_sum_over_groups (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (groups: list (list t))
  : Lemma (requires all_distinct #t roots /\
                    (forall (g:list t). L.memP g groups ==>
                       (Cons? g /\ all_distinct #t g /\ (forall (b:t). L.memP b g ==> L.memP b roots) /\
                        (forall (b:t). L.memP b g ==> residue #t #f p roots b = residue #t #f p roots (L.hd g)))))
          (ensures (answer_deriv #t #f p roots groups) = (frac_sum_over_groups #t #f p roots groups))
          (decreases groups)
  = let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    match groups with
    | [] ->
        (* both sides fraction_zero. *)
        reflexivity (answer_deriv #t #f p roots [])
    | g :: gs ->
        let gc  : fraction id_p = group_contribution #t #f p roots g in
        let ad  : fraction id_p = answer_deriv #t #f p roots gs in
        let fg  : fraction id_p = frac_sum #t #f p roots g in
        let fgs : fraction id_p = frac_sum_over_groups #t #f p roots gs in
        (* per-group: gc = fg  (preconds from head, L.memP g (g::gs)). *)
        per_group_eq #t #f p roots g;
        (* IH on gs: ad = fgs. *)
        answer_eq_frac_sum_over_groups #t #f p roots gs;
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
  : Lemma (requires Cons? roots /\ all_distinct #t roots /\
                    (Some? (poly_deg p) ==> Some?.v (poly_deg p) < L.length roots) /\
                    L.flatten groups == roots /\
                    (forall (g:list t). L.memP g groups ==>
                       (Cons? g /\ all_distinct #t g /\ (forall (b:t). L.memP b g ==> L.memP b roots) /\
                        (forall (b:t). L.memP b g ==> residue #t #f p roots b = residue #t #f p roots (L.hd g)))))
          (ensures (let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
                    is_nonzero #(polynomial t) (poly_prod_linears #t #f roots) /\
                    (let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears #t #f roots in
                     (answer_deriv #t #f p roots groups) = (Fraction #(polynomial t) #id_p p q))))
  = let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    prod_linears_nonzero #t #f roots;
    let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears #t #f roots in
    (* answer_deriv = frac_sum_over_groups. *)
    answer_eq_frac_sum_over_groups #t #f p roots groups;
    (* frac_sum_over_groups = frac_sum p roots (flatten groups) = frac_sum p roots roots
       (the two frac_sum terms are identical since flatten groups == roots). *)
    frac_sum_flatten #t #f p roots groups;
    (* partial_fraction_decomposition: Fraction p q = frac_sum p roots roots. *)
    partial_fraction_decomposition #t #f p roots;
    symmetry (Fraction #(polynomial t) #id_p p q)
             (frac_sum #t #f p roots roots);
    (* chain: answer_deriv = frac_sum_over_groups = frac_sum p roots roots = Fraction p q. *)
    transitivity (answer_deriv #t #f p roots groups)
                 (frac_sum_over_groups #t #f p roots groups)
                 (frac_sum #t #f p roots roots);
    transitivity (answer_deriv #t #f p roots groups)
                 (frac_sum #t #f p roots roots)
                 (Fraction #(polynomial t) #id_p p q)

(* ================================================================ *)
(*  ROTHSTEIN-TRAGER ROOT CHARACTERISATION.                          *)
(*  For q = ∏(x - beta_i) and q' = q', a distinct root b of q is a    *)
(*  common root of (p - c.q') and q  iff  residue(p) at b equals c.   *)
(*  (b is automatically a root of q; the LHS reduces to b being a     *)
(*  root of (p - c.q'), i.e. p(b) - c.q'(b) = 0.)                     *)
(*                                                                    *)
(*  Eval of LHS: poly_eval (poly_sub p (poly_scale c q')) b           *)
(*             = p(b) + neg (c * x)         (x = q'(b), nonzero),      *)
(*  and residue p roots b = p(b) * inv x.                             *)
(*  (⇒) p(b) = c*x  ⟹  residue = (c*x)*inv x = c.                    *)
(*  (⇐) residue = c ⟹ p(b) = c*x ⟹ p(b) + neg(c*x) = zero.          *)
(* ================================================================ *)
let common_root_iff_residue (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (c: t) (b: t)
  : Lemma (requires L.memP b roots /\ all_distinct #t roots)
          (ensures (poly_eval #t #(cr_of_id t #(id_of_f t))
                      (poly_sub #t #(cr_of_id t #(id_of_f t)) p
                         (poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots)))) b
                    = (zero <: t))
                   <==> (residue #t #f p roots b = c))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pd = poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots) in
    let x : t = poly_eval pd b in
    split_deriv_nonzero #t #f b roots;                 (* not (x = zero) *)
    let sc = poly_scale #t c pd in
    let d  = poly_sub #t #(cr_of_id t #(id_of_f t)) p sc in
    let pb : t = poly_eval p b in
    let ix = (f.f_sf.sf_mig).inv x in
    (* (A) poly_eval sc b = c * x  (mirror residue_of_scaled_deriv_is_const). *)
    eval_mul (c @ poly_zero) pd b;                     (* eval sc b = eval (c@0) b * x *)
    let _ : squash (poly_eval (c @ poly_zero) b = c) =
      if c = (zero <: t) then begin
        eval_zero #t b;
        symmetry c (zero <: t);
        transitivity (poly_eval (c @ poly_zero) b) (zero <: t) c
      end else
        eval_singleton #t #f c b in
    mul_congruence (poly_eval (c @ poly_zero) b) x c x;
    transitivity (poly_eval sc b) (poly_eval (c @ poly_zero) b * x) (c * x);
    (* (B) poly_eval d b = pb + neg (c * x). *)
    poly_sub_reveal #t #(cr_of_id t #(id_of_f t)) p sc;   (* d == poly_add p (poly_neg sc) *)
    eval_add p (poly_neg sc) b;                        (* eval d b = pb + eval (neg sc) b *)
    eval_neg sc b;                                     (* eval (neg sc) b = neg (eval sc b) *)
    neg_congruence (poly_eval sc b) (c * x);           (* neg (eval sc b) = neg (c*x) *)
    add_congruence pb (poly_eval (poly_neg sc) b) pb (neg (poly_eval sc b));
    transitivity (poly_eval d b)
                 (pb + poly_eval (poly_neg sc) b)
                 (pb + neg (poly_eval sc b));
    add_congruence pb (neg (poly_eval sc b)) pb (neg (c * x));
    transitivity (poly_eval d b) (pb + neg (poly_eval sc b)) (pb + neg (c * x));
    (* residue p roots b = pb * ix  (definitional, same denominator x). *)
    (* (⇒) eval d b = zero ⟹ pb = c*x ⟹ residue = c. *)
    introduce (poly_eval d b = (zero <: t)) ==> (residue #t #f p roots b = c)
    with _hz. begin
      (* pb + neg (c*x) = zero ⟹ pb = c*x. *)
      symmetry (poly_eval d b) (pb + neg (c * x));
      transitivity (pb + neg (c * x)) (poly_eval d b) (zero <: t);
      lemma_sub_zero_imp_eq #t #((cr_of_id t #(id_of_f t)).cr_r.r_add) pb (c * x);   (* pb = c*x *)
      (* residue = pb * ix = (c*x) * ix = c*(x*ix) = c*one = c. *)
      mul_congruence pb ix (c * x) ix;                 (* pb*ix = (c*x)*ix *)
      mul_associativity c x ix;                        (* (c*x)*ix = c*(x*ix) *)
      f.f_sf.sf_mig.inversion_lemma x;                 (* x*ix = one *)
      mul_congruence c (x * ix) c (one <: t);
      H.x_mul_one c;                                   (* c*one = c *)
      transitivity (c * (x * ix)) (c * (one <: t)) c;
      transitivity ((c * x) * ix) (c * (x * ix)) c;
      transitivity (pb * ix) ((c * x) * ix) c;
      transitivity (residue #t #f p roots b) (pb * ix) c
    end;
    (* (⇐) residue = c ⟹ pb = c*x ⟹ eval d b = zero. *)
    introduce (residue #t #f p roots b = c) ==> (poly_eval d b = (zero <: t))
    with _hr. begin
      (* residue == pb * ix, so pb * ix = c. *)
      (* multiply by x:  (pb*ix)*x = c*x ;  LHS = pb*(ix*x) = pb*one = pb. *)
      mul_congruence (residue #t #f p roots b) x c x;  (* (pb*ix)*x = c*x *)
      mul_associativity pb ix x;                       (* (pb*ix)*x = pb*(ix*x) *)
      f.f_sf.sf_mig.inversion_lemma x;                 (* ix*x = one *)
      mul_congruence pb (ix * x) pb (one <: t);
      H.x_mul_one pb;                                  (* pb*one = pb *)
      transitivity (pb * (ix * x)) (pb * (one <: t)) pb;
      symmetry ((pb * ix) * x) (pb * (ix * x));
      transitivity pb ((pb * ix) * x) (c * x);         (* pb = c*x *)
      (* pb + neg(c*x) = c*x + neg(c*x) = zero. *)
      add_congruence pb (neg (c * x)) (c * x) (neg (c * x));
      H.x_plus_neg_x (c * x);                          (* c*x + neg(c*x) = zero *)
      transitivity (pb + neg (c * x)) ((c * x) + neg (c * x)) (zero <: t);
      transitivity (poly_eval d b) (pb + neg (c * x)) (zero <: t)
    end


(* ================================================================ *)
(*  A linear factor divides a gcd iff it divides both arguments.    *)
(* ================================================================ *)

let linear_divides_gcd_iff (#t:Type) {| f: field t |} (a b: polynomial t) (beta: t)
  : Lemma ((divides (poly_linear #t #f beta) (poly_gcd #t #f a b))
           <==> (divides (poly_linear #t #f beta) a /\ divides (poly_linear #t #f beta) b))
  = let lin = poly_linear #t #f beta in
    introduce (divides lin (poly_gcd #t #f a b))
              ==> (divides lin a /\ divides lin b)
    with _hd. begin
      Core.Polynomial.GCD.gcd_divides_left  #t #f a b; (* divides (gcd a b) a *)
      divides_trans lin (poly_gcd #t #f a b) a;        (* divides lin a *)
      Core.Polynomial.GCD.gcd_divides_right #t #f a b; (* divides (gcd a b) b *)
      divides_trans lin (poly_gcd #t #f a b) b         (* divides lin b *)
    end;
    introduce (divides lin a /\ divides lin b)
              ==> (divides lin (poly_gcd #t #f a b))
    with _hd. begin
      Core.Polynomial.GCD.gcd_is_maximal #t #f a b lin (* divides lin (gcd a b) *)
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
  : Lemma (requires L.memP beta roots /\ all_distinct #t roots)
          (ensures (divides (poly_linear #t #f beta)
                      (poly_gcd #t #f
                         (poly_sub #t #(cr_of_id t #(id_of_f t)) p
                            (poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))))
                         (poly_prod_linears #t #f roots)))
                   <==> (residue #t #f p roots beta = c))
  = let q = poly_prod_linears #t #f roots in
    let qd = poly_deriv #t #(cr_of_id t #(id_of_f t)) q in
    let d  = poly_sub #t #(cr_of_id t #(id_of_f t)) p (poly_scale #t c qd) in
    let lin = poly_linear #t #f beta in
    (* (x - beta) | q  always (beta is a root of q). *)
    prod_linears_vanishes #t #f roots beta;            (* poly_eval q beta = zero *)
    factor_theorem #t #f q beta;                       (* eval q beta = 0 <==> lin | q *)
    (* (x - beta) | (p - c.q') <==> eval d beta = 0. *)
    factor_theorem #t #f d beta;
    (* eval d beta = 0 <==> residue p roots beta = c. *)
    common_root_iff_residue #t #f p roots c beta;
    (* lin | gcd(d, q)  <==>  lin | d /\ lin | q. *)
    linear_divides_gcd_iff #t #f d q beta

(* ================================================================ *)
(*  A root beta of q is a root of v_c = gcd(p - c.q', q)  iff its    *)
(*  residue is c.  (poly_eval form of gcd_linear_factor_iff_residue, *)
(*  via the factor theorem on the gcd.)                              *)
(* ================================================================ *)

let gcd_root_iff_residue (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (c: t) (beta: t)
  : Lemma (requires L.memP beta roots /\ all_distinct #t roots)
          (ensures (poly_eval #t #(cr_of_id t #(id_of_f t))
                      (poly_gcd #t #f
                         (poly_sub #t #(cr_of_id t #(id_of_f t)) p
                            (poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))))
                         (poly_prod_linears #t #f roots)) beta
                    = (zero <: t))
                   <==> (residue #t #f p roots beta = c))
  = let g = poly_gcd #t #f
              (poly_sub #t #(cr_of_id t #(id_of_f t)) p
                 (poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))))
              (poly_prod_linears #t #f roots) in
    (* eval g beta = 0  <==>  (x - beta) | g *)
    factor_theorem #t #f g beta;
    (* (x - beta) | g  <==>  residue p roots beta = c *)
    gcd_linear_factor_iff_residue #t #f p roots c beta

(* ================================================================ *)
(*  Distinct residue values give root-disjoint LRT log-arguments.   *)
(*  A root beta of q cannot be a common root of v_c1 and v_c2,       *)
(*  where v_ci = gcd (p - ci.q') q, when c1 <> c2: either gcd-root   *)
(*  forces residue p roots beta to equal that constant.             *)
(* ================================================================ *)

let vc_disjoint (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (c1 c2: t) (beta: t)
  : Lemma (requires L.memP beta roots /\ all_distinct #t roots /\ not (c1 = c2))
          (ensures not (
             (poly_eval #t #(cr_of_id t #(id_of_f t))
                (poly_gcd #t #f
                   (poly_sub #t #(cr_of_id t #(id_of_f t)) p
                      (poly_scale #t c1 (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))))
                   (poly_prod_linears #t #f roots)) beta = (zero <: t))
           /\ (poly_eval #t #(cr_of_id t #(id_of_f t))
                (poly_gcd #t #f
                   (poly_sub #t #(cr_of_id t #(id_of_f t)) p
                      (poly_scale #t c2 (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))))
                   (poly_prod_linears #t #f roots)) beta = (zero <: t))))
  = H.elim_equatable_laws t ();
    let g1 = poly_eval #t #(cr_of_id t #(id_of_f t))
               (poly_gcd #t #f
                  (poly_sub #t #(cr_of_id t #(id_of_f t)) p
                     (poly_scale #t c1 (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))))
                  (poly_prod_linears #t #f roots)) beta in
    let g2 = poly_eval #t #(cr_of_id t #(id_of_f t))
               (poly_gcd #t #f
                  (poly_sub #t #(cr_of_id t #(id_of_f t)) p
                     (poly_scale #t c2 (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))))
                  (poly_prod_linears #t #f roots)) beta in
    introduce (g1 = (zero <: t) /\ g2 = (zero <: t)) ==> False
    with _h. begin
      let r = residue #t #f p roots beta in
      gcd_root_iff_residue #t #f p roots c1 beta;        (* r = c1 *)
      gcd_root_iff_residue #t #f p roots c2 beta;        (* r = c2 *)
      symmetry r c1;                                     (* c1 = r *)
      transitivity c1 r c2                               (* c1 = c2 *)
    end

(* ================================================================ *)
(*  A residue-c root makes v_c = gcd(p - c.q', q) a genuine          *)
(*  (degree >= 1) log argument.  Combines:                           *)
(*    gcd_linear_factor_iff_residue : residue = c ==> (x-beta) | g    *)
(*    gcd_pos (qq nonzero ==> deg(gcd) defined): g <> 0               *)
(*    divides_degree_le             : (x-beta) | g, g<>0              *)
(*                                    ==> deg(x-beta) <= deg g        *)
(*    poly_linear_deg               : deg (x-beta) = Some 1.          *)
(* ================================================================ *)
let residue_implies_gcd_nonconstant (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (c: t) (beta: t)
  : Lemma (requires L.memP beta roots /\ all_distinct #t roots /\ residue #t #f p roots beta = c)
          (ensures (let g = poly_gcd #t #f
                              (poly_sub #t #(cr_of_id t #(id_of_f t)) p
                                 (poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))))
                              (poly_prod_linears #t #f roots) in
                    Some? (poly_deg g) /\ Some?.v (poly_deg g) >= 1))
  = let q = poly_prod_linears #t #f roots in
    let qd = poly_deriv #t #(cr_of_id t #(id_of_f t)) q in
    let d  = poly_sub #t #(cr_of_id t #(id_of_f t)) p (poly_scale #t c qd) in
    let g  = poly_gcd #t #f d q in
    let lin = poly_linear #t #f beta in
    (* (x - beta) | g, from residue p roots beta = c. *)
    gcd_linear_factor_iff_residue #t #f p roots c beta;  (* divides lin g *)
    (* q = prod roots is nonzero (Cons? roots from memP), so deg q defined; *)
    (* hence deg g defined (gcd_pos). *)
    poly_prod_linears_deg #t #f roots;                   (* poly_deg q == Some (length roots) *)
    Core.Matrix.ResultantConverse.gcd_pos #t #f d q;     (* Some? (poly_deg g) *)
    (* deg lin = Some 1. *)
    poly_linear_deg #t #f beta;                          (* poly_deg lin == Some 1 *)
    (* divisor-degree: deg lin <= deg g, i.e. 1 <= Some?.v (poly_deg g). *)
    Core.Polynomial.Irreducible.divides_degree_le #t #f lin g

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
  : Lemma (requires all_distinct #t roots /\
                    (forall (b:t). L.memP b cset ==> (L.memP b roots /\ residue #t #f p roots b = c)))
          (ensures (let vc = poly_gcd #t #f
                              (poly_sub #t #(cr_of_id t #(id_of_f t)) p
                                 (poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))))
                              (poly_prod_linears #t #f roots) in
                    (forall (b:t). L.memP b cset ==> poly_eval #t #(cr_of_id t #(id_of_f t)) vc b = (zero <: t))))
  = let vc = poly_gcd #t #f
                (poly_sub #t #(cr_of_id t #(id_of_f t)) p
                   (poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))))
                (poly_prod_linears #t #f roots) in
    let aux (b:t) : Lemma (requires L.memP b cset)
                          (ensures poly_eval #t #(cr_of_id t #(id_of_f t)) vc b = (zero <: t)) =
      gcd_root_iff_residue #t #f p roots c b
    in
    Classical.forall_intro (Classical.move_requires aux)

(* Each residue-c linear factor (x - beta) divides v_c.               *)
(*  Immediate from gcd_linear_factor_iff_residue (<== direction).     *)
let vc_linear_factors_divide (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (c: t) (cset: list t)
  : Lemma (requires all_distinct #t roots /\
                    (forall (b:t). L.memP b cset ==> (L.memP b roots /\ residue #t #f p roots b = c)))
          (ensures (let vc = poly_gcd #t #f
                              (poly_sub #t #(cr_of_id t #(id_of_f t)) p
                                 (poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))))
                              (poly_prod_linears #t #f roots) in
                    (forall (b:t). L.memP b cset ==> divides (poly_linear #t #f b) vc)))
  = let vc = poly_gcd #t #f
                (poly_sub #t #(cr_of_id t #(id_of_f t)) p
                   (poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))))
                (poly_prod_linears #t #f roots) in
    let aux (b:t) : Lemma (requires L.memP b cset)
                          (ensures divides (poly_linear #t #f b) vc) =
      gcd_linear_factor_iff_residue #t #f p roots c b
    in
    Classical.forall_intro (Classical.move_requires aux)

(* v_c factorization GIVEN the count.  Once the (hard) counting step    *)
(*   L.length cset == Some?.v (poly_deg v_c)                            *)
(* is supplied as a hypothesis, the structure tool                     *)
(* poly_split_distinct_roots factors v_c over cset.  This isolates the  *)
(* remaining T6 obligation to exactly that degree equality.            *)
let vc_factorization_given_count (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (c: t) (cset: list t)
  : Lemma (requires all_distinct #t roots /\ all_distinct #t cset /\
                    (forall (b:t). L.memP b cset ==> (L.memP b roots /\ residue #t #f p roots b = c)) /\
                    (let vc = poly_gcd #t #f
                                (poly_sub #t #(cr_of_id t #(id_of_f t)) p
                                   (poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))))
                                (poly_prod_linears #t #f roots) in
                     Some? (poly_deg vc) /\ L.length cset == Some?.v (poly_deg vc)))
          (ensures (let vc = poly_gcd #t #f
                              (poly_sub #t #(cr_of_id t #(id_of_f t)) p
                                 (poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))))
                              (poly_prod_linears #t #f roots) in
                    poly_eq vc (poly_scale #t (poly_lc vc) (poly_prod_linears #t #f cset))))
  = let vc = poly_gcd #t #f
                (poly_sub #t #(cr_of_id t #(id_of_f t)) p
                   (poly_scale #t c (poly_deriv #t #(cr_of_id t #(id_of_f t)) (poly_prod_linears #t #f roots))))
                (poly_prod_linears #t #f roots) in
    vc_roots_are_residue_c #t #f p roots c cset;
    poly_split_distinct_roots #t #f vc cset
