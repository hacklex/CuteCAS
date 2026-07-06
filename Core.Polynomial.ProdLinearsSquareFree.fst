module Core.Polynomial.ProdLinearsSquareFree

(*
   A product of DISTINCT linear factors is square-free.

      d = (x - r1) * (x - r2) * ... * (x - rn),   ri pairwise distinct
      ==>  square_free d   (i.e. coprime d (poly_deriv d)).

   Math: for distinct ri each is a SIMPLE root, so
      d'(ri) = prod_{j<>i} (ri - rj) <> 0,
   hence no (x - ri) divides d'; since the monic irreducible factors of d
   are exactly the (x - ri), gcd(d, d') is a unit, i.e. coprime.

   The proof shows directly: for every listed root a,
      poly_eval (poly_deriv d) a <> 0,
   so (poly_deriv d) is coprime to each (x - a) [nonroot_coprime_linear],
   and combining over the product [coprime_mul_right] gives
      coprime (poly_deriv d) d, whence coprime d (poly_deriv d).
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module IR = Core.Polynomial.Irreducible

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.GCD
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree
open Core.Polynomial.Eval
open Core.Polynomial.Roots
open Core.Polynomial.SplitDivisor

(* ================================================================ *)
(*  coeff of poly_one (= [one] in a field): coeff 0 = one, else 0.   *)
(* ================================================================ *)

private let poly_one_coeff (#t:Type) {| f: field t |} (j: nat)
  : Lemma (coeff (poly_one #t) j == (if j = 0 then (one <: t) else (zero <: t)))
  = let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    (* in a field one <> zero, so poly_one == [one] definitionally *)
    assert (poly_one #t == ([one] <: polynomial t))

(* ================================================================ *)
(*  Derivative of a linear factor:  (x - r)' ~ poly_one.             *)
(* ================================================================ *)

private let deriv_linear_eq_one (#t:Type) {| f: field t |} (r: t)
  : Lemma ((poly_deriv (poly_linear r)) = (poly_one #t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    let la = poly_linear r in
    assert (la == ([(- r); one] <: polynomial t));
    assert (L.length la == 2);
    let aux (j:nat) : Lemma (coeff #t (poly_deriv la) j = coeff #t (poly_one #t) j) =
      poly_deriv_coeff la j;                  (* coeff (deriv la) j = (j+1) . coeff la (j+1) *)
      poly_one_coeff #t #f j;
      if j = 0 then begin
        (* coeff la 1 = one ; nat_scale 1 one = one *)
        assert (coeff la (j ++ 1) == (one <: t));
        nat_scale_one (one <: t)    (* nat_scale 1 one = one *)
        (* coeff (deriv la) 0 = nat_scale 1 (coeff la 1) = nat_scale 1 one = one *)
      end else begin
        (* j >= 1: coeff la (j+1) = 0 (j+1 >= 2 = length la) ; nat_scale _ 0 = 0 *)
        assert (coeff la (j ++ 1) == (zero <: t));
        nat_scale_zero_element #t (j ++ 1)
      end
    in
    poly_eq_by_coeff (poly_deriv la) (poly_one #t) aux

(* eval of (x - r)' at any point is one. *)
private let eval_deriv_linear (#t:Type) {| f: field t |} (r c: t)
  : Lemma (poly_eval (poly_deriv (poly_linear r)) c = (one <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    deriv_linear_eq_one r;                                (* (x-r)' ~ poly_one *)
    eval_congruence (poly_deriv (poly_linear r)) (poly_one #t) c;
    eval_one c                                         (* eval poly_one c = one *)

(* ================================================================ *)
(*  eval (prod_linears roots) a <> 0  when  a is NOT in roots,       *)
(*  and the roots are pairwise distinct.                             *)
(* ================================================================ *)

private let rec prod_linears_eval_nonroot (#t:Type) {| f: field t |}
  (roots: list t) (a: t)
  : Lemma (requires (forall (d:t). L.memP d roots ==> not (a = d)))
          (ensures  not (poly_eval (poly_prod_linears roots) a = (zero <: t)))
          (decreases roots)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match roots with
    | [] ->
        (* prod_linears [] = poly_one, eval = one <> 0 *)
        eval_one a;                                     (* eval poly_one a = one *)
        f.f_one_ne_zero                                    (* not (one = zero) *)
    | b :: rest ->
        (* a <> b (b is a member) and a <> d for all d in rest *)
        let la = poly_linear b in
        let pr = poly_prod_linears rest in
        eval_mul la pr a;                                  (* eval (la*pr) a = eval la a * eval pr a *)
        eval_linear b a;                                   (* eval la a = neg b + a *)
        assert (L.memP b roots);                           (* b is the head member *)
        assert (not (a = b));                              (* from the forall with d = b *)
        sub_nonzero_of_distinct b a;                       (* neg b + a <> 0 (a <> b) *)
        (* eval pr a <> 0 by IH: a <> d for all d in rest (rest ⊆ roots) *)
        prod_linears_eval_nonroot rest a;
        (* product of two nonzero is nonzero *)
        let lhs = poly_eval la a in
        let rhs = poly_eval pr a in
        (* eval (la*pr) a = 0, but = lhs*rhs, so lhs*rhs = 0; domain_law splits,
           both factors nonzero (lhs = neg b + a <> 0, rhs = eval pr a <> 0). *)
        Classical.move_requires (fun () -> domain_law lhs rhs) ()

(* ================================================================ *)
(*  THE SIMPLE-ROOT FACT: d'(a) <> 0 for every listed root a,        *)
(*  when the roots are pairwise distinct.                            *)
(*    d = (x-b) * d1,   d' = (x-b)'*d1 + (x-b)*d1'.                   *)
(*    - a = b:    d'(b) = 1*d1(b) + 0 = d1(b) <> 0   (b not in rest). *)
(*    - a in rest: d'(a) = 1*d1(a) + (a-b)*d1'(a)                     *)
(*                       = 0 + (a-b)*d1'(a) <> 0     (IH + a<>b).     *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
private let rec deriv_prod_linears_at_root (#t:Type) {| f: field t |}
  (roots: list t) (a: t)
  : Lemma (requires all_distinct roots /\ L.memP a roots)
          (ensures  not (poly_eval (poly_deriv (poly_prod_linears roots)) a
                         = (zero <: t)))
          (decreases roots)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match roots with
    | b :: rest ->
        let la = poly_linear b in
        let d1 = poly_prod_linears rest in
        (* d = la * d1 ; d' = la'*d1 + la*d1' *)
        poly_deriv_mul la d1;
        (* eval d' a = eval (la'*d1 + la*d1') a
                     = eval (la'*d1) a + eval (la*d1') a
                     = eval la' a * eval d1 a + eval la a * eval d1' a   *)
        let dla  = poly_deriv la in
        let dd1  = poly_deriv d1 in
        let term1 = (dla * d1) in
        let term2 = (la * dd1) in
        eval_congruence (poly_deriv (la * d1)) (term1 + term2) a;
        eval_add term1 term2 a;
        eval_mul dla d1 a;                                 (* eval (la'*d1) a = eval la' a * eval d1 a *)
        eval_mul la dd1 a;                                 (* eval (la*d1') a = eval la a * eval d1' a *)
        eval_deriv_linear b a;                             (* eval la' a = one *)
        eval_linear b a;                                   (* eval la a = neg b + a *)
        (* assemble: eval d' a = (eval la' a)*(eval d1 a) + (eval la a)*(eval d1' a) *)
        let e_dla  = poly_eval dla a in   (* = one *)
        let e_d1   = poly_eval d1 a in
        let e_la   = poly_eval la a in    (* = neg b + a *)
        let e_dd1  = poly_eval dd1 a in
        (* ASSEMBLE: eval d' a = e_dla*e_d1 + e_la*e_dd1.
           eval (deriv (la*d1)) a = eval (term1+term2) a            [eval_congruence]
                                  = eval term1 a + eval term2 a     [eval_add]
                                  = (e_dla*e_d1) + (e_la*e_dd1)      [eval_mul x2, add_congruence] *)
        add_congruence (poly_eval term1 a) (poly_eval term2 a)
                       (e_dla * e_d1) (e_la * e_dd1);
        (* eval (poly_deriv (prod roots)) a == eval (poly_deriv (la*d1)) a (prod roots = la*d1) *)
        assert (poly_eval (poly_deriv (poly_prod_linears roots)) a
                = ((e_dla * e_d1) + (e_la * e_dd1)));
        eliminate (b == a) \/ (L.memP a rest)
        returns not (poly_eval (poly_deriv (poly_prod_linears roots)) a = (zero <: t))
        with _h.
          begin
            (* a = b. e_la = neg b + a = neg b + b = 0, so second term = 0.
               e_dla = one. e_d1 = eval d1 b <> 0 (b distinct from all of rest).
               eval d' a = one * e_d1 + 0 = e_d1 <> 0. *)
            assert (forall (d:t). L.memP d rest ==> not (b = d));  (* all_distinct head *)
            prod_linears_eval_nonroot rest b;              (* e_d1 (= eval d1 b) <> 0 ; here a=b *)
            (* one * e_d1 <> 0 *)
            f.f_one_ne_zero;
            domain_law e_dla e_d1;                 (* e_dla*e_d1 = 0 ==> e_dla=0 \/ e_d1=0 *)
            (* second term: e_la = neg b + a = neg a + a = 0  ==> e_la*e_dd1 = 0 *)
            H.neg_x_plus_x a;                              (* neg a + a = 0 ; e_la = neg b + a, b=a *)
            (* show eval d' a <> 0 *)
            let fin () : Lemma (requires poly_eval (poly_deriv (poly_prod_linears roots)) a = (zero <: t))
                              (ensures False) =
              (* eval d' a = e_dla*e_d1 + e_la*e_dd1 ; need this = 0 leads to contra *)
              (* e_la = neg b + a, and b == a so e_la = neg a + a = 0 *)
              (* e_la*e_dd1 = 0 *)
              mul_congruence e_la e_dd1 zero e_dd1;
              H.zero_mul_x e_dd1;
              (* eval d' a = e_dla*e_d1 + e_la*e_dd1 = e_dla*e_d1 + 0 = e_dla*e_d1 *)
              add_congruence (e_dla * e_d1) (e_la * e_dd1) (e_dla * e_d1) zero;
              H.x_plus_zero (e_dla * e_d1);
              (* e_dla = one <> 0, e_d1 <> 0 (note a = b so eval d1 a = eval d1 b) *)
              (* domain_law gives e_dla=0 \/ e_d1=0, both false -> handled by SMT with the facts *)
              domain_law e_dla e_d1
            in
            Classical.move_requires fin ()
          end
        and _h.
          begin
            (* a in rest, a <> b. e_d1 = eval d1 a = 0 (a is root of d1).
               first term = e_dla * 0 = 0.
               e_la = neg b + a <> 0 (a <> b), e_dd1 = eval d1' a <> 0 (IH).
               eval d' a = 0 + e_la*e_dd1 <> 0. *)
            prod_linears_vanishes rest a;                  (* e_d1 = eval d1 a = 0 *)
            deriv_prod_linears_at_root rest a;             (* IH: e_dd1 <> 0 *)
            (* a <> b: from all_distinct head, forall d in rest, b<>d, so b<>a, so a<>b *)
            assert (forall (d:t). L.memP d rest ==> not (b = d));
            assert (not (b = a));
            assert (not (a = b));
            sub_nonzero_of_distinct b a;                   (* neg b + a <> 0 *)
            let fin () : Lemma (requires poly_eval (poly_deriv (poly_prod_linears roots)) a = (zero <: t))
                              (ensures False) =
              (* first term e_dla*e_d1: e_d1 = 0 ==> term1 = 0 *)
              mul_congruence e_dla e_d1 e_dla zero;
              H.x_mul_zero e_dla;
              (* eval d' a = e_dla*e_d1 + e_la*e_dd1 = 0 + e_la*e_dd1 = e_la*e_dd1 *)
              add_congruence (e_dla * e_d1) (e_la * e_dd1) zero (e_la * e_dd1);
              H.zero_plus_x (e_la * e_dd1);
              (* domain: e_la = 0 \/ e_dd1 = 0, both false *)
              domain_law e_la e_dd1
            in
            Classical.move_requires fin ()
          end
#pop-options

(* ================================================================ *)
(*  d <> 0  ==>  Some? (poly_deg d).  Used for nonroot_coprime_linear *)
(*  and coprime_mul_right side-conditions on the derivative.          *)
(* ================================================================ *)

private let eval_nonzero_has_degree (#t:Type) {| f: field t |}
  (q: polynomial t) (a: t)
  : Lemma (requires not (poly_eval q a = (zero <: t)))
          (ensures  deg q >= 0)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if deg q < 0 then begin
      degree_none_poly_eq_zero q;                          (* q ~ poly_zero *)
      eval_congruence q (poly_zero #t) a;                  (* eval q a = eval poly_zero a *)
      eval_zero a                                       (* eval poly_zero a = 0 *)
    end

(* ================================================================ *)
(*  prod_linears has a degree  (it is a nonzero polynomial).          *)
(*  In fact eval at any point not among roots is nonzero, but for     *)
(*  the empty list we just need eval = one <> 0.                      *)
(* ================================================================ *)

private let prod_linears_has_degree (#t:Type) {| f: field t |}
  (roots: list t)
  : Lemma (ensures deg (poly_prod_linears roots) >= 0)
  = poly_prod_linears_deg roots

(* ================================================================ *)
(*  coprime (poly_deriv d)  (x - a)  for every listed root a.        *)
(*  via nonroot_coprime_linear: eval (poly_deriv d) a <> 0.          *)
(* ================================================================ *)

private let deriv_coprime_linear_at_root (#t:Type) {| f: field t |}
  (roots: list t) (a: t)
  : Lemma (requires all_distinct roots /\ L.memP a roots)
          (ensures  coprime (poly_deriv (poly_prod_linears roots))
                                  (poly_linear a))
  = let d  = poly_prod_linears roots in
    let dd = poly_deriv d in
    deriv_prod_linears_at_root roots a;                    (* eval dd a <> 0 *)
    eval_nonzero_has_degree dd a;                          (* Some? (poly_deg dd) *)
    nonroot_coprime_linear dd a                            (* coprime dd (x-a) *)

(* ================================================================ *)
(*  coprime (poly_deriv (prod_linears roots)) (prod_linears roots)   *)
(*  combine over the product with coprime_mul_right.                 *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
private let rec deriv_coprime_prod (#t:Type) {| f: field t |}
  (full: list t) (roots: list t)
  : Lemma (requires all_distinct full /\
                    deg (poly_deriv (poly_prod_linears full)) >= 0 /\
                    (forall (a:t). L.memP a roots ==> L.memP a full))
          (ensures  coprime (poly_deriv (poly_prod_linears full))
                                  (poly_prod_linears roots))
          (decreases roots)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let d  = poly_prod_linears full in
    let dd = poly_deriv d in
    match roots with
    | [] ->
        (* prod_linears [] = poly_one ; coprime dd poly_one : gcd(dd,1) has deg 0. *)
        let po = poly_prod_linears roots in                 (* = poly_one *)
        coprime_reveal dd po;
        let g = poly_gcd dd po in
        gcd_divides_right dd po;                             (* g | poly_one *)
        prod_linears_has_degree roots;                      (* deg poly_one = Some 0 *)
        gcd_has_degree dd po;                               (* Some? deg g (dd has degree) *)
        IR.divides_degree_le g po                           (* deg g <= deg poly_one = 0 *)
    | b :: rest ->
        (* coprime dd (la * d1) from coprime dd la and coprime dd d1 *)
        let la = poly_linear b in
        let d1 = poly_prod_linears rest in
        assert (L.memP b full);                            (* b is in roots ⊆ full *)
        deriv_coprime_linear_at_root full b;               (* coprime dd la *)
        deriv_coprime_prod full rest;                      (* IH: coprime dd d1 *)
        IR.coprime_mul_right dd la d1                     (* coprime dd (la*d1) *)
#pop-options

(* dd = poly_deriv (prod_linears roots) has a degree when roots is nonempty:
   its head root gives a point where dd evaluates nonzero. *)
private let deriv_prod_has_degree (#t:Type) {| f: field t |}
  (roots: list t)
  : Lemma (requires all_distinct roots /\ Cons? roots)
          (ensures  deg (poly_deriv (poly_prod_linears roots)) >= 0)
  = let b = L.hd roots in
    assert (L.memP b roots);
    deriv_prod_linears_at_root roots b;                    (* eval dd b <> 0 *)
    eval_nonzero_has_degree (poly_deriv (poly_prod_linears roots)) b

(* ================================================================ *)
(*  MAIN THEOREM.                                                     *)
(* ================================================================ *)

let prod_linears_square_free (#t:Type) {| f: field t |} (roots: list t)
  : Lemma (requires all_distinct roots)
          (ensures  square_free (poly_prod_linears roots))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let d  = poly_prod_linears roots in
    let dd = poly_deriv d in
    prod_linears_has_degree roots;                         (* Some? deg d *)
    match roots with
    | [] ->
        (* d = poly_one ; dd = poly_deriv poly_one = poly_zero.
           square_free d = coprime d poly_zero = (gcd(d, 0) has deg 0) = (deg d = 0).
           deg poly_one = 0, so square_free. *)
        coprime_reveal d dd;
        let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
        poly_one_deg #t #f ();                             (* poly_deg poly_one = Some 0 ; d = poly_one *)
        assert (L.length (poly_one #t) <= 1);              (* poly_one == [one] in a field *)
        poly_deriv_const (poly_one #t);                    (* poly_deriv poly_one == poly_zero *)
        (* d = poly_one, dd = poly_deriv d == poly_zero (propositional ==) *)
        assert (dd == (poly_zero #t));
        (* poly_gcd d dd == poly_gcd d poly_zero (== congruence) == d (poly_gcd_base) *)
        poly_gcd_base d (poly_zero #t);                    (* poly_gcd d poly_zero == d *)
        assert (poly_gcd d dd == d);                 (* deg (poly_gcd d dd) == deg d == Some 0 *)
        assert (deg (poly_gcd d dd) == 0)
    | _ :: _ ->
        (* d nonempty ==> dd nonzero (head root gives eval dd a <> 0) ==> Some? deg dd *)
        deriv_prod_has_degree roots;                       (* Some? deg dd *)
        deriv_coprime_prod roots roots;                    (* coprime dd d *)
        IR.coprime_symmetric dd d                          (* coprime d dd = square_free d *)
