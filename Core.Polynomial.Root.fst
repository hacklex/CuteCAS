module Core.Polynomial.Root

(* Root theory (prereq B for the Risch/LRT integrator):
     - the linear polynomial  x - a = [neg a; one]  and its evaluation,
     - the FACTOR THEOREM:  poly_eval p a = 0  <==>  (x - a) | p,
     - SQUARE-FREE ==> simple roots:  square_free q /\ q(a)=0 ==> q'(a) <> 0.

   Everything rests on `poly_eval` being a ring homomorphism
   (Core.Polynomial.Eval) plus Euclidean division and the gcd API. *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Unique
open Core.Polynomial.Irreducible
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree
open Core.FinSum
open Core.Polynomial.Eval

(* ================================================================ *)
(*  The linear polynomial  x - a  =  [neg a; one].                   *)
(*  (trimmed because the leading coeff `one` <> zero in a field).    *)
(* ================================================================ *)

let poly_linear (#t:Type) {| f: field t |} (a: t) : polynomial t =
  let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
  [neg a; one]

let poly_linear_deg (#t:Type) {| f: field t |} (a: t)
  : Lemma (poly_deg (poly_linear #t #f a) == Some 1)
  = let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    ()

(* leading coefficient of x - a is one (monic). *)
let poly_linear_lc (#t:Type) {| f: field t |} (a: t)
  : Lemma (poly_lc (poly_linear #t #f a) = (one <: t))
  = H.elim_equatable_laws t ();
    let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    poly_linear_deg #t #f a;
    poly_lc_reveal (poly_linear #t #f a);     (* lc = L.last [neg a; one] = one *)
    reflexivity (one <: t)

(* ================================================================ *)
(*  Evaluation of small polynomials.                                 *)
(* ================================================================ *)

(* poly_eval [c0] c = c0   (for c0 <> 0 so [c0] is a valid polynomial) *)
let eval_singleton (#t:Type) {| f: field t |} (c0 c: t)
  : Lemma (requires not (c0 = (zero <: t)))
          (ensures  poly_eval ([c0] <: polynomial t) c = c0)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let p : polynomial t = [c0] in
    let g = eval_term p c in
    sum_range_unfold_left g 0 1;                 (* sum01 = g0 + sum11 *)
    sum_range_empty g 1 1;                        (* sum11 = zero *)
    H.x_mul_one c0;                               (* c0 * one = c0 ; g0 == c0 * one *)
    H.x_plus_zero (g 0);
    add_congruence (g 0) (sum_range g 1 1) (g 0) (zero <: t);
    transitivity (sum_range g 0 1) (g 0 + sum_range g 1 1) (g 0 + (zero <: t));
    transitivity (sum_range g 0 1) (g 0 + (zero <: t)) (g 0);
    transitivity (sum_range g 0 1) (g 0) c0

(* poly_eval (x - a) c = c - a   (here written  neg a + c). *)
let eval_linear (#t:Type) {| f: field t |} (a c: t)
  : Lemma (poly_eval (poly_linear #t #f a) c = (neg a + c))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    let la = poly_linear #t #f a in
    let g = eval_term la c in
    sum_range_unfold_left g 0 2;                 (* sum02 = g0 + sum12 *)
    sum_range_unfold_left g 1 2;                 (* sum12 = g1 + sum22 *)
    sum_range_empty g 2 2;                        (* sum22 = zero *)
    (* g 0 == neg a * one == neg a *)
    H.x_mul_one (neg a);
    (* g 1 == one * (c * one) == one * c == c *)
    H.x_mul_one c;
    reflexivity (one <: t);
    mul_congruence (one <: t) (c * one) (one <: t) c;    (* one*(c*one) = one*c *)
    H.one_mul_x c;                                       (* one*c = c *)
    transitivity (g 1) ((one <: t) * c) c;
    (* sum12 = g1 + zero = g1 = c *)
    H.x_plus_zero (g 1);
    add_congruence (g 1) (sum_range g 2 2) (g 1) (zero <: t);
    transitivity (sum_range g 1 2) (g 1 + sum_range g 2 2) (g 1 + (zero <: t));
    transitivity (sum_range g 1 2) (g 1 + (zero <: t)) (g 1);
    transitivity (sum_range g 1 2) (g 1) c;
    (* sum02 = g0 + sum12 = neg a + c *)
    add_congruence (g 0) (sum_range g 1 2) (neg a) c;
    transitivity (sum_range g 0 2) (g 0 + sum_range g 1 2) (neg a + c)

(* poly_eval (x - a) a = 0  : a is a root of x - a. *)
let eval_linear_root (#t:Type) {| f: field t |} (a: t)
  : Lemma (poly_eval (poly_linear #t #f a) a = (zero <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    eval_linear #t #f a a;                               (* eval = neg a + a *)
    H.neg_x_plus_x a;                                    (* neg a + a = zero *)
    transitivity (poly_eval (poly_linear #t #f a) a) (neg a + a) (zero <: t)

(* ================================================================ *)
(*  Factor theorem.                                                  *)
(* ================================================================ *)

(* If (x - a) | p, then a is a root of p. *)
let factor_backward (#t:Type) {| f: field t |} (p: polynomial t) (a: t)
  : Lemma (requires (let cr_p : commutative_ring (polynomial t) = TC.solve in
                     divides #(polynomial t) #cr_p (poly_linear #t #f a) p))
          (ensures  poly_eval p a = (zero <: t))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let la = poly_linear #t #f a in
    eliminate exists (c: polynomial t). poly_eq p (poly_mul la c)
    returns poly_eval p a = (zero <: t)
    with _.
      begin
        eval_congruence p (poly_mul la c) a;             (* eval p a = eval (la*c) a *)
        eval_mul la c a;                                 (* eval (la*c) a = eval la a * eval c a *)
        eval_linear_root a;                              (* eval la a = zero *)
        mul_congruence (poly_eval la a) (poly_eval c a) (zero <: t) (poly_eval c a);
        H.zero_mul_x (poly_eval c a);                    (* zero * eval c a = zero *)
        transitivity (poly_eval (poly_mul la c) a)
                     (poly_eval la a * poly_eval c a)
                     ((zero <: t) * poly_eval c a);
        transitivity (poly_eval (poly_mul la c) a)
                     ((zero <: t) * poly_eval c a) (zero <: t);
        transitivity (poly_eval p a) (poly_eval (poly_mul la c) a) (zero <: t)
      end

(* A constant remainder (deg <= 0) vanishing at one point is the zero polynomial. *)
let small_eval_zero_is_zero (#t:Type) {| f: field t |} (rem: polynomial t) (a: t)
  : Lemma (requires (None? (poly_deg rem) \/ poly_deg rem == (Some 0 <: option nat)) /\
                    poly_eval rem a = (zero <: t))
          (ensures  poly_eq rem (poly_zero #t))
  = if None? (poly_deg rem) then degree_none_poly_eq_zero rem
    else begin
      degree_zero_is_singleton rem;                     (* rem == [poly_lc rem], lc <> zero *)
      let c0 : t = poly_lc rem in
      eval_singleton c0 a;                              (* poly_eval [c0] a = c0 *)
      (* rem == [c0] ==> poly_eval rem a = c0; with eval rem a = zero gives c0 = zero (contra) *)
      symmetry (poly_eval rem a) c0;
      transitivity c0 (poly_eval rem a) (zero <: t)
    end

(* If a is a root of p, then (x - a) | p. *)
let factor_forward (#t:Type) {| f: field t |} (p: polynomial t) (a: t)
  : Lemma (requires poly_eval p a = (zero <: t))
          (ensures  (let cr_p : commutative_ring (polynomial t) = TC.solve in
                     divides #(polynomial t) #cr_p (poly_linear #t #f a) p))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let la = poly_linear #t #f a in
    poly_linear_deg #t #f a;                            (* poly_deg la = Some 1 *)
    let q  = poly_div #t #f p la in
    let rm = poly_rem #t #f p la in
    poly_div_reveal #t #f p la;
    poly_rem_reveal #t #f p la;
    poly_divmod_correct #t #f p la;                     (* poly_eq p (add (mul la q) rm) *)
    poly_divmod_correct_degree #t #f p la;              (* deg rm None \/ < 1 *)
    (* eval at a: eval p a = eval (mul la q) a + eval rm a ; first summand = 0 *)
    eval_congruence p (poly_add (poly_mul la q) rm) a;
    eval_add (poly_mul la q) rm a;
    eval_mul la q a;
    eval_linear_root a;
    mul_congruence (poly_eval la a) (poly_eval q a) (zero <: t) (poly_eval q a);
    H.zero_mul_x (poly_eval q a);
    transitivity (poly_eval (poly_mul la q) a)
                 (poly_eval la a * poly_eval q a)
                 ((zero <: t) * poly_eval q a);
    transitivity (poly_eval (poly_mul la q) a)
                 ((zero <: t) * poly_eval q a) (zero <: t);
    (* eval (add (mul la q) rm) a = zero + eval rm a = eval rm a *)
    add_congruence (poly_eval (poly_mul la q) a) (poly_eval rm a) (zero <: t) (poly_eval rm a);
    H.zero_plus_x (poly_eval rm a);
    transitivity (poly_eval (poly_add (poly_mul la q) rm) a)
                 (poly_eval (poly_mul la q) a + poly_eval rm a)
                 ((zero <: t) + poly_eval rm a);
    transitivity (poly_eval (poly_add (poly_mul la q) rm) a)
                 ((zero <: t) + poly_eval rm a) (poly_eval rm a);
    transitivity (poly_eval p a)
                 (poly_eval (poly_add (poly_mul la q) rm) a) (poly_eval rm a);
    symmetry (poly_eval p a) (poly_eval rm a);
    transitivity (poly_eval rm a) (poly_eval p a) (zero <: t);  (* eval rm a = zero *)
    (* rm is constant and vanishes => rm ~ 0 => p ~ la*q => (x-a) | p *)
    small_eval_zero_is_zero rm a;                       (* poly_eq rm poly_zero *)
    poly_add_zero (poly_mul la q);                      (* (la*q) + 0 ~ (la*q) *)
    reflexivity #(polynomial t) #(cr_p.cr_r.r_add.acg_eq) (poly_mul la q);
    poly_add_congruence (poly_mul la q) rm (poly_mul la q) (poly_zero #t);
    transitivity (poly_add (poly_mul la q) rm)
                 (poly_add (poly_mul la q) (poly_zero #t)) (poly_mul la q);
    transitivity p (poly_add (poly_mul la q) rm) (poly_mul la q);  (* poly_eq p (la*q) *)
    divides_intro #(polynomial t) #cr_p la p q

let factor_theorem (#t:Type) {| f: field t |} (p: polynomial t) (a: t)
  : Lemma ((poly_eval p a = (zero <: t)) <==>
           (let cr_p : commutative_ring (polynomial t) = TC.solve in
            divides #(polynomial t) #cr_p (poly_linear #t #f a) p))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    Classical.move_requires (factor_forward #t #f p) a;
    Classical.move_requires (factor_backward #t #f p) a

(* ================================================================ *)
(*  Square-free  ==>  simple roots:  q(a)=0 ==> q'(a) <> 0.           *)
(*  If both vanished, (x-a) would divide gcd(q,q'), forcing          *)
(*  deg(gcd) >= 1, contradicting coprime q q' (= square_free q).      *)
(* ================================================================ *)

let squarefree_root_deriv_nonzero (#t:Type) {| f: field t |} (q: polynomial t) (a: t)
  : Lemma (requires square_free q /\ poly_eval q a = (zero <: t))
          (ensures  not (poly_eval (poly_deriv q) a = (zero <: t)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    let la = poly_linear #t #f a in
    poly_linear_deg #t #f a;                            (* deg la = Some 1 *)
    factor_forward #t #f q a;                            (* la | q *)
    let aux () : Lemma (requires poly_eval (poly_deriv q) a = (zero <: t))
                       (ensures False)
      = factor_forward #t #f (poly_deriv q) a;           (* la | q' *)
        gcd_is_maximal #t #f q (poly_deriv q) la;        (* la | gcd q q' *)
        coprime_reveal #t #f q (poly_deriv q);           (* deg (gcd q q') = Some 0 *)
        (* la | gcd, deg la = 1, deg gcd = 0  ==>  1 <= 0 *)
        divides_degree_le #t #f la (poly_gcd #t #f q (poly_deriv q))
    in
    Classical.move_requires aux ()
