module Core.Polynomial.Product

(* Products of polynomials and the evaluation homomorphism over them
   (prereq for the Poisson resultant formula and the Rothstein-Trager
   log-argument products  v_c = prod (x - alpha)).

     poly_prod [p1;...;pn]            = p1 * ... * pn
     poly_prod_linears [a1;...;an]    = (x-a1) * ... * (x-an)

   and  poly_eval (poly_prod ps) c = prod (poly_eval pi c)   (ring hom),
        poly_eval (poly_prod_linears as) c = prod (c - ai),
        a in as  ==>  poly_eval (poly_prod_linears as) a = 0. *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Root

(* ================================================================ *)
(*  Product of a list of polynomials, and the matching scalar fold.  *)
(* ================================================================ *)

let rec poly_prod (#t:Type) {| cr: commutative_ring t |} (ps: list (polynomial t))
  : Tot (polynomial t) (decreases ps)
  = match ps with
    | []        -> poly_one #t
    | p :: rest -> poly_mul p (poly_prod rest)

let rec eval_prod (#t:Type) {| cr: commutative_ring t |} (ps: list (polynomial t)) (c: t)
  : Tot t (decreases ps)
  = match ps with
    | []        -> one #t
    | p :: rest -> poly_eval p c * eval_prod rest c

(* poly_eval is a ring homomorphism over the product. *)
let rec eval_poly_prod (#t:Type) {| cr: commutative_ring t |} (ps: list (polynomial t)) (c: t)
  : Lemma (ensures poly_eval (poly_prod ps) c = eval_prod ps c) (decreases ps)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match ps with
    | []        -> eval_one #t c
    | p :: rest ->
      eval_mul p (poly_prod rest) c;             (* eval (p * prod rest) = eval p * eval (prod rest) *)
      eval_poly_prod rest c;                      (* IH: eval (prod rest) = eval_prod rest *)
      mul_congruence (poly_eval p c) (poly_eval (poly_prod rest) c)
                     (poly_eval p c) (eval_prod rest c);
      transitivity (poly_eval (poly_prod (p :: rest)) c)
                   (poly_eval p c * poly_eval (poly_prod rest) c)
                   (poly_eval p c * eval_prod rest c)

(* ================================================================ *)
(*  Products of linear factors  (x - a1) * ... * (x - an).           *)
(* ================================================================ *)

let rec poly_prod_linears (#t:Type) {| f: field t |} (roots: list t)
  : Tot (polynomial t) (decreases roots)
  = match roots with
    | []        -> poly_one #t
    | a :: rest -> poly_mul (poly_linear #t #f a) (poly_prod_linears rest)

let rec eval_prod_sub (#t:Type) {| f: field t |} (roots: list t) (c: t)
  : Tot t (decreases roots)
  = match roots with
    | []        -> one #t
    | a :: rest -> (neg a + c) * eval_prod_sub rest c

(* poly_eval of a product of linear factors = prod (c - a). *)
let rec eval_poly_prod_linears (#t:Type) {| f: field t |} (roots: list t) (c: t)
  : Lemma (ensures poly_eval (poly_prod_linears roots) c = eval_prod_sub roots c)
          (decreases roots)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match roots with
    | []        -> eval_one #t c
    | a :: rest ->
      eval_mul (poly_linear #t #f a) (poly_prod_linears rest) c;
      eval_linear #t #f a c;                      (* eval (x-a) c = neg a + c *)
      eval_poly_prod_linears rest c;              (* IH *)
      mul_congruence (poly_eval (poly_linear #t #f a) c)
                     (poly_eval (poly_prod_linears rest) c)
                     (neg a + c) (eval_prod_sub rest c);
      transitivity (poly_eval (poly_prod_linears roots) c)
                   (poly_eval (poly_linear #t #f a) c * poly_eval (poly_prod_linears rest) c)
                   ((neg a + c) * eval_prod_sub rest c)

(* Every listed root is genuinely a root of the factored polynomial. *)
let rec prod_linears_vanishes (#t:Type) {| f: field t |} (roots: list t) (a: t)
  : Lemma (requires L.memP a roots)
          (ensures  poly_eval (poly_prod_linears roots) a = (zero <: t))
          (decreases roots)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match roots with
    | []        -> ()                             (* memP a [] is False *)
    | b :: rest ->
      eval_mul (poly_linear #t #f b) (poly_prod_linears rest) a;
      let lhs = poly_eval (poly_linear #t #f b) a in
      let rhs = poly_eval (poly_prod_linears rest) a in
      eliminate (b == a) \/ (L.memP a rest)
      returns poly_eval (poly_prod_linears (b :: rest)) a = (zero <: t)
      with _h.
        begin                                     (* a is this factor's root: lhs = 0 *)
          eval_linear_root #t #f b;               (* eval (x-b) b = 0 ; b == a *)
          mul_congruence lhs rhs (zero <: t) rhs;
          H.zero_mul_x rhs;                        (* zero * rhs = zero *)
          transitivity (poly_eval (poly_prod_linears (b :: rest)) a) (lhs * rhs) ((zero <: t) * rhs);
          transitivity (poly_eval (poly_prod_linears (b :: rest)) a) ((zero <: t) * rhs) (zero <: t)
        end
      and _h.
        begin                                     (* a is a root of the rest: rhs = 0 *)
          prod_linears_vanishes rest a;
          mul_congruence lhs rhs lhs (zero <: t);
          H.x_mul_zero lhs;                        (* lhs * zero = zero *)
          transitivity (poly_eval (poly_prod_linears (b :: rest)) a) (lhs * rhs) (lhs * (zero <: t));
          transitivity (poly_eval (poly_prod_linears (b :: rest)) a) (lhs * (zero <: t)) (zero <: t)
        end
