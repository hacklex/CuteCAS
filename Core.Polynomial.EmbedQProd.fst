module Core.Polynomial.EmbedQProd

(* ================================================================ *)
(*  §D bound step (c1a): an INTEGER product-of-linears and the      *)
(*  push of the ℤ→ℚ embedding through it.                           *)
(*                                                                   *)
(*  `poly_linear`/`poly_prod_linears` (Core.Polynomial.Roots) are    *)
(*  field-only.  There is no `field int`, only `int_cr`/`int_id`, so *)
(*  we DEFINE the integer analogues over `int_cr` (using            *)
(*  `int_id.id_one_ne_zero` for the `[neg a; one]` trimming witness) *)
(*  and prove `embed_zq` pushes through them up to the polynomial    *)
(*  equatable `=` on ℚ[X].                                           *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Roots
open Core.Fractions
open Core.Polynomial.EmbedQ

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* The ℚ field instance and its commutative_ring (= EmbedQ's `crq`). *)
let ff : field qq = fraction_field int int_id

(* ================================================================ *)
(*  1. Integer constructions (mirror Roots but over `int_cr`).       *)
(* ================================================================ *)

(* (X - a) = [neg a; one] over `int_cr`; trimmed since one <> zero. *)
#push-options "--fuel 3 --ifuel 1"
let int_linear (a: int) : polynomial int #int_cr =
  let l : list int = [(- a); one] in
  assert (L.last l == (one <: int));
  assert (not ((one <: int) = (zero <: int)));
  assert (is_trimmed #int #int_cr l);
  l
#pop-options

let rec int_prod_linears (roots: list int) : Tot (polynomial int #int_cr) (decreases roots)
  = match roots with
    | []        -> poly_one #int
    | a :: rest -> int_linear a * int_prod_linears rest

(* ================================================================ *)
(*  2. Per-factor:  embed_zq (X - a)  ≈  (X - embed a).              *)
(* ================================================================ *)

(* embed_zq_const (neg a)  =  neg (embed_zq_const a)  in ℚ.
   Derived via negation uniqueness: both `embed (neg a)` and `neg (embed a)`
   are right-inverses of `embed a`, so they are equal by left-cancellation. *)
private let embed_const_neg (a: int)
  : Lemma (embed_zq_const (- a) = - (embed_zq_const a))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let ea  = embed_zq_const a in
    let ena = embed_zq_const (- a) in
    let nea = - ea in
    (* (1) ea + ena =eq= zero. *)
    (* ea + ena == fraction_add ea ena =eq= embed (a + neg a) = embed 0 =eq= zero *)
    fraction_ring_add_reveal #int #int_id ea ena;       (* ea + ena == fraction_add ea ena *)
    embed_zq_const_add a (- a);                          (* fraction_add ea ena = embed (a + neg a) *)
    assert ((a ++ (- a)) == 0);
    embed_zq_const_zero ();                              (* embed 0 =eq= crq.zero *)
    (* (2) ea + nea =eq= zero. *)
    H.x_plus_neg_x ea;                                   (* ea + nea =eq= zero *)
    (* (3) cancel: ea + ena =eq= ea + nea  ==>  ena =eq= nea. *)
    H.group_cancel_left ea ena nea

(* embed_zq_const 1  =  crq.one  in ℚ (re-derived; EmbedQ's is private). *)
private let embed_const_one_local (_:unit)
  : Lemma (embed_zq_const 1 = one)
  = let e1 = embed_zq_const 1 in
    let o  : qq = one in
    H.elim_equatable_laws qq ();
    H.x_mul_one e1;                              (* e1 *_qq o =eq= e1 *)
    fraction_ring_mul_reveal #int #int_id e1 o;  (* e1 *_qq o == fraction_mul e1 o *)
    fraction_mul_reveal #int #int_id e1 o

(* coeff i of (X - embed a) = poly_linear #qq #ff (embed a). *)
#push-options "--fuel 2 --ifuel 2"
let embed_zq_linear (a: int)
  : Lemma (embed_zq (int_linear a)
           = poly_linear #qq #ff (embed_zq_const a))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let _ : squash (not (one #int = (zero <: int))) = int_id.id_one_ne_zero in
    let lhs = embed_zq (int_linear a) in
    let rhs = poly_linear #qq #ff (embed_zq_const a) in
    let aux (j:nat) : Lemma (coeff lhs j = coeff rhs j) =
      H.elim_equatable_laws qq ();
      H.trans_for_calc qq ();
      (* coeff lhs j =eq= embed_zq_const (coeff (int_linear a) j) *)
      embed_zq_coeff (int_linear a) j;
      if j = 0 then begin
        (* coeff (int_linear a) 0 == neg a ; coeff rhs 0 == neg (embed a) *)
        embed_const_neg a
      end else if j = 1 then begin
        (* coeff (int_linear a) 1 == one#int == 1 ; coeff rhs 1 == one#qq = crq.one *)
        embed_const_one_local ()
      end else begin
        (* both out of range: coeff lhs j =eq= embed_zq_const 0 =eq= crq.zero = coeff rhs j *)
        embed_zq_const_zero ()
      end
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs
#pop-options

(* ================================================================ *)
(*  3. embed_zq poly_one  ≈  poly_one  in ℚ[X].                      *)
(* ================================================================ *)

(* poly_one over any commutative_ring with 1 <> 0 has degree Some 0,
   lc one (mirror Berlekamp.poly_one_deg_lc; nontriviality provided). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
private let cr_poly_one_deg_lc (#t:Type) {| cr: commutative_ring t |}
  (_: squash (not (one #t = (zero <: t))))
  : Lemma (deg (poly_one #t) == 0 /\
           poly_lc (poly_one #t) = one)
  = H.elim_equatable_laws t ();
    poly_lc_reveal (poly_one #t)
#pop-options

(* coeff facts for poly_one over a field. *)
private let poly_one_coeff_zero (#t:Type) {| f: field t |} ()
  : Lemma (coeff (poly_one #t) 0 = one)
  = H.elim_equatable_laws t ();
    cr_poly_one_deg_lc #t f.f_one_ne_zero;        (* deg poly_one = Some 0, lc one ⇒ length 1 *)
    last_eq_index #t (poly_one #t) 0;             (* L.last = L.index 0 = coeff 0 *)
    poly_lc_reveal (poly_one #t)

private let poly_one_coeff_high (#t:Type) {| f: field t |} (j:nat{j >= 1})
  : Lemma (coeff (poly_one #t) j == (zero <: t))
  = cr_poly_one_deg_lc #t f.f_one_ne_zero;        (* deg poly_one = Some 0 *)
    coeff_above_degree (poly_one #t) j            (* j > 0 = deg ⇒ coeff = zero *)

private let int_poly_one_coeff_zero (_:unit)
  : Lemma (coeff (poly_one #int) 0 = one)
  = H.elim_equatable_laws int ();
    cr_poly_one_deg_lc #int #int_cr ();           (* deg Some 0 ⇒ length 1 *)
    last_eq_index (poly_one #int) 0;
    poly_lc_reveal (poly_one #int)

private let int_poly_one_coeff_high (j:nat{j >= 1})
  : Lemma (coeff (poly_one #int) j == (zero <: int))
  = cr_poly_one_deg_lc #int #int_cr ();
    coeff_above_degree (poly_one #int) j

let embed_zq_one (_:unit)
  : Lemma (embed_zq (poly_one #int) = poly_one #qq #crq)
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let lhs = embed_zq (poly_one #int) in
    let rhs = poly_one #qq #crq in
    let aux (j:nat) : Lemma (coeff lhs j = coeff rhs j) =
      H.elim_equatable_laws qq ();
      embed_zq_coeff (poly_one #int) j;          (* coeff lhs j =eq= embed_zq_const (coeff poly_one j) *)
      if j = 0 then begin
        (* coeff (poly_one#int) 0 == 1 ; coeff (poly_one#qq) 0 == crq.one *)
        int_poly_one_coeff_zero ();
        poly_one_coeff_zero #qq #ff ();
        embed_const_one_local ()                  (* embed_zq_const 1 =eq= crq.one *)
      end else begin
        (* both out of range: lhs =eq= embed_zq_const 0 =eq= crq.zero ;
           coeff rhs j == zero for j >= 1 *)
        int_poly_one_coeff_high j;
        poly_one_coeff_high #qq #ff j;
        embed_zq_const_zero ()
      end
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* ================================================================ *)
(*  4. Main:  embed_zq pushes through the product of linears.        *)
(* ================================================================ *)

#push-options "--fuel 2 --ifuel 2"
let rec embed_zq_prod_linears (roots: list int)
  : Lemma (ensures poly_eq
             (embed_zq (int_prod_linears roots))
             (poly_prod_linears #qq #ff (L.map embed_zq_const roots)))
          (decreases roots)
  = match roots with
    | [] ->
        (* int_prod_linears [] = poly_one#int ; poly_prod_linears [] = poly_one#qq *)
        embed_zq_one ()
    | a :: rest ->
        let la_i  = int_linear a in
        let pr_i  = int_prod_linears rest in
        let la_q  = poly_linear #qq #ff (embed_zq_const a) in
        let pr_q  = poly_prod_linears #qq #ff (L.map embed_zq_const rest) in
        let lhs   = embed_zq (int_prod_linears (a :: rest)) in
        (* int_prod_linears (a::rest) = poly_mul la_i pr_i *)
        (* embed_zq (poly_mul la_i pr_i) ≈ poly_mul (embed la_i) (embed pr_i) *)
        embed_zq_mul la_i pr_i;
        (* embed la_i ≈ la_q  ;  embed pr_i ≈ pr_q  (step 2 + IH) *)
        embed_zq_linear a;
        embed_zq_prod_linears rest;
        (* poly_mul (embed la_i) (embed pr_i) ≈ poly_mul la_q pr_q *)
        poly_mul_congruence
          (embed_zq la_i) (embed_zq pr_i) la_q pr_q;
        (* chain: lhs ≈ poly_mul (embed la_i)(embed pr_i) ≈ poly_mul la_q pr_q
                  = poly_prod_linears (map embed (a::rest)) *)
        poly_eq_transitivity
          lhs
          (embed_zq la_i * embed_zq pr_i)
          (la_q * pr_q)
#pop-options
