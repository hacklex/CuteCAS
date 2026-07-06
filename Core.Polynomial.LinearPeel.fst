module Core.Polynomial.LinearPeel

(*
   §E1-linear — the SAME-LEVEL peel.

   When a polynomial over a field has a DEGREE-1 (irreducible) factor,
   its root already lies in the base field and one linear factor peels
   off with NO field extension.  Four results:

     1. linear_root / linear_root_is_root — a degree-1 polynomial r has
        an explicit root  a = -(coeff r 0)/(coeff r 1)  in t.
     2. linear_factor_peel — a root a of d (deg d >= 1) peels off a
        linear factor:  d = (X - a) * q  with  deg q = deg d - 1.
     3. divisor_of_square_free — a divisor of a square-free polynomial
        is square-free.
     4. root_of_divisor — a root of a factor is a root of the whole.

   NO admit / assume / sorry.
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module IR = Core.Polynomial.Irreducible

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.GCD
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree
open Core.Polynomial.Eval
open Core.Polynomial.Roots
open Core.FinSum

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  1a. Evaluation of a degree-1 polynomial.                         *)
(*      poly_eval r a = coeff r 0 + coeff r 1 * a.                    *)
(* ================================================================ *)

let eval_deg1 (#t:Type) {| f: field t |} (r: polynomial t{deg r == 1}) (a: t)
  : Lemma (poly_eval r a = ((coeff r 0) + (coeff r 1) * a))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    assert (L.length r == 2);
    let g = eval_term r a in
    sum_range_unfold_left g 0 2;                 (* sum02 = g0 + sum12 *)
    sum_range_unfold_left g 1 2;                 (* sum12 = g1 + sum22 *)
    sum_range_empty g 2 2;                        (* sum22 = zero *)
    (* g 0 == coeff r 0 * one == coeff r 0 *)
    H.x_mul_one (coeff r 0);
    (* g 1 == coeff r 1 * (a * one) == coeff r 1 * a *)
    H.x_mul_one a;
    mul_congruence (coeff r 1) (a * one) (coeff r 1) a;
    (* sum12 = g1 + zero = g1 = coeff r 1 * a *)
    H.x_plus_zero (g 1);
    add_congruence (g 1) (sum_range g 2 2) (g 1) zero;
    (* sum02 = g0 + sum12 = coeff r 0 + coeff r 1 * a *)
    add_congruence (g 0) (sum_range g 1 2) (coeff r 0) ((coeff r 1) * a)

(* ================================================================ *)
(*  1b. The explicit root of a degree-1 polynomial.                  *)
(* ================================================================ *)

let linear_root (#t:Type) {| f: field t |} (r: polynomial t{deg r == 1}) : t =
  leading_coeff_nonzero r;                       (* not (coeff r 1 = zero) *)
  ((- (coeff r 0)) * (inv (coeff r 1)))

let linear_root_is_root (#t:Type) {| f: field t |} (r: polynomial t{deg r == 1})
  : Lemma (poly_eval r (linear_root r) = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    leading_coeff_nonzero r;                      (* c1 nonzero *)
    let c0 = coeff r 0 in
    let c1 = coeff r 1 in
    let y  = inv c1 in
    let a  = ((- c0) * y) in
    assert (linear_root r == a);
    eval_deg1 r a;                                (* poly_eval r a = c0 + c1 * a *)
    (* c1 * a = c1 * (y * (-c0)) = (c1 * y) * (-c0) = one * (-c0) = -c0 *)
    H.mul_commutativity_cr (- c0) y;              (* (-c0) * y = y * (-c0) *)
    mul_congruence c1 a c1 (y * (- c0));          (* c1 * a = c1 * (y * (-c0)) *)
    mul_associativity c1 y (- c0);                (* (c1*y)*(-c0) = c1*(y*(-c0)) *)
    inversion_lemma c1;                           (* c1 * y = one *)
    mul_congruence (c1 * y) (- c0) one (- c0);    (* (c1*y)*(-c0) = one*(-c0) *)
    H.one_mul_x (- c0);                           (* one * (-c0) = -c0 *)
    (* c0 + c1*a = c0 + (-c0) = zero *)
    H.x_plus_neg_x c0;                            (* c0 + (-c0) = zero *)
    add_congruence c0 (c1 * a) c0 (- c0)

(* ================================================================ *)
(*  2. Peeling one linear factor from a polynomial with a root.      *)
(* ================================================================ *)

let linear_factor_peel (#t:Type) {| f: field t |} (d: polynomial t) (a: t)
  : Lemma (requires deg d >= 1 /\ poly_eval d a = zero)
          (ensures  (exists (q: polynomial t).
                       (d = ((poly_linear a) * q)) /\ deg q == deg d - 1))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    factor_forward d a;                           (* divides (poly_linear a) d *)
    let la = poly_linear a in
    poly_linear_deg a;                            (* deg la == 1 *)
    eliminate exists (q: polynomial t). (d = (la * q))
    returns (exists (q: polynomial t).
               (d = (la * q)) /\ deg q == deg d - 1)
    with hq.
    begin
      mul_linear_nonzero_quotient a d q;          (* deg q >= 0 *)
      deg_mul la q;                               (* deg (la*q) = 1 + deg q *)
      degree_well_defined d (la * q);             (* deg d == deg (la*q) *)
      introduce exists (q2: polynomial t).
                  (d = (la * q2)) /\ deg q2 == deg d - 1
      with q
      and ()
    end

(* ================================================================ *)
(*  3. A divisor of a square-free polynomial is square-free.         *)
(*                                                                   *)
(*  g = gcd(a, a').  From a | d (d = a*m) and the product rule,      *)
(*  g | a | d and g | a'*m + a*m' = d'.  So g | gcd(d, d'), whose    *)
(*  degree is 0 (square_free d).  Hence deg g <= 0; with deg g >= 0  *)
(*  we get deg g = 0, i.e. coprime a a' = square_free a.             *)
(* ================================================================ *)

let divisor_of_square_free (#t:Type) {| f: field t |} (a d: polynomial t)
  : Lemma (requires square_free d /\ divides a d /\ deg a >= 1)
          (ensures  square_free a)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let a' = poly_deriv a in
    let d' = poly_deriv d in
    let g  = poly_gcd a a' in
    coprime_reveal a a';                          (* square_free a = (deg g = 0) *)
    gcd_has_degree a a';                          (* deg g >= 0 *)
    gcd_divides_left a a';                         (* g | a *)
    gcd_divides_right a a';                        (* g | a' *)
    eliminate exists (m: polynomial t). (d = (a * m))
    returns square_free a
    with hm.
    begin
      let m' = poly_deriv m in
      (* g | d *)
      divides_intro a d m;                        (* a | d *)
      divides_trans g a d;                         (* g | d *)
      (* d' = a'*m + a*m' *)
      poly_deriv_congruence d (a * m);            (* d' = poly_deriv (a*m) *)
      poly_deriv_mul a m;                          (* poly_deriv (a*m) = a'*m + a*m' *)
      (* g | a'*m + a*m' *)
      divides_mul_right g a' m;                    (* g | a'*m *)
      divides_mul_right g a m';                    (* g | a*m' *)
      divides_add g (a' * m) (a * m');             (* g | a'*m + a*m' *)
      divides_congruence_right g ((a' * m) + (a * m')) d';   (* g | d' *)
      (* g | gcd(d, d') and deg gcd(d,d') = 0 *)
      gcd_is_maximal d d' g;                        (* g | poly_gcd d d' *)
      coprime_reveal d d';                          (* square_free d = (deg gcd(d,d') = 0) *)
      IR.divides_degree_le g (poly_gcd d d')        (* deg g <= 0 *)
    end

(* ================================================================ *)
(*  4. A root of a factor is a root of the whole polynomial.         *)
(* ================================================================ *)

let root_of_divisor (#t:Type) {| f: field t |} (r d: polynomial t) (a: t)
  : Lemma (requires divides r d /\ poly_eval r a = zero)
          (ensures  poly_eval d a = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    eliminate exists (c: polynomial t). (d = (r * c))
    returns poly_eval d a = zero
    with hc.
    begin
      eval_congruence d (r * c) a;                (* poly_eval d a = poly_eval (r*c) a *)
      eval_mul r c a;                              (* = poly_eval r a * poly_eval c a *)
      mul_congruence (poly_eval r a) (poly_eval c a) zero (poly_eval c a);
      H.zero_mul_x (poly_eval c a)                 (* zero * poly_eval c a = zero *)
    end

(* ================================================================ *)
(*  5. Peeling preserves freshness: after peeling (X - a) off a      *)
(*     SQUARE-FREE d, the quotient q has NO root at a — otherwise    *)
(*     (X - a)^2 would divide d, contradicting square-freeness.      *)
(* ================================================================ *)

#push-options "--fuel 4 --ifuel 2"
let peel_preserves_freshness (#t:Type) {| f: field t |} (d q: polynomial t) (a: t)
  : Lemma (requires square_free d /\ deg d >= 1 /\ (d = ((poly_linear a) * q)))
          (ensures  not (poly_eval q a = zero))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if poly_eval q a = zero then begin
      let la = poly_linear a in
      poly_linear_deg a;                          (* deg la == 1 *)
      mul_linear_nonzero_quotient a d q;          (* deg q >= 0 *)
      deg_mul la q;                               (* deg (la*q) == 1 + deg q *)
      degree_well_defined d (la * q);             (* deg d == deg (la*q) *)
      if deg q = 0 then begin
        (* q is a nonzero constant, so q(a) = q <> zero — contradiction. *)
        match q with
        | [c0] ->
            leading_coeff_nonzero q;              (* not (c0 = zero) *)
            eval_singleton c0 a                   (* poly_eval q a = c0 : contra *)
      end else begin
        (* a is a root of q too: peel again, so (X - a)^2 | d. *)
        linear_factor_peel q a;
        eliminate exists (q2: polynomial t). (q = (la * q2)) /\ deg q2 == deg q - 1
        returns False
        with hq2.
        begin
          mul_congruence la q la (la * q2);       (* la*q = la*(la*q2) *)
          mul_associativity la la q2;             (* (la*la)*q2 = la*(la*q2) *)
          assert ((la * q) = ((la * la) * q2));
          H.x_mul_one la;                         (* la * poly_one = la *)
          mul_congruence la la la (la * (poly_one #t));   (* la*la = la*(la*one) *)
          assert ((la * la) = (poly_power la 2));
          mul_congruence (la * la) q2 (poly_power la 2) q2;
          assert (d = ((poly_power la 2) * q2));
          divides_intro (poly_power la 2) d q2;   (* (X-a)^2 | d *)
          IR.not_square_free_of_repeated_factor la d 2   (* square_free d = false *)
        end
      end
    end
#pop-options
