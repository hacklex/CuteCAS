module Core.Fractions.DerivativeQuotient

(*
   Rational-derivative RECIPROCAL rule (and the QUOTIENT rule):

     D(1/y)   =  - y' * (1/y)^2                    (y nonzero)
     D(x/y)   =  D(x)*(1/y) + x*(- y'*(1/y)^2)     (y nonzero)

   for rational functions x, y over a field t, where D = `rational_deriv`,
   `inv` is the field inverse on `fraction id_p` (reached through
   `fraction_field`), and `*`/`+`/`neg`/`one` are the ring/field ops of
   `cr_fr` (the commutative ring on `fraction id_p`).

   Both are derived PURELY from already-proven derivation laws
   (`rmul_field`, `rcong_field`, `rational_deriv_one`) plus the field
   inverse law `y * inv y = one` (the `mul_is_group.inversion_lemma`).
   No core-interface change; no admit/assume/sorry.

   Strategy.  Let iy = inv y, a = D y, r = D iy.  The inverse law gives
   y*iy = one.  Differentiating y*iy = one with the congruence + Leibniz
   + D(one)=0 laws yields  a*iy + y*r = zero.  The reciprocal value is then
   a pure commutative-ring rearrangement GIVEN the side fact y*iy = one:
     a*iy + y*r = 0  /\  y*iy = 1   ==>   r = neg (a*(iy*iy)).
   That rearrangement is proved generically in `recip_solve` (explicit
   congruence/associativity chains; canon_ring cannot use the y*iy=1 side
   fact, so we chain by hand).
*)

module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Fractions
open Core.Fractions.Derivative
open Core.Fractions.DerivativeSum
open Core.Fractions.DerivationInstance

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  Generic group fact:  p + r = zero  ==>  r = neg p.               *)
(* ================================================================ *)
let solve_neg (#s:Type) {| g: add_comm_group s |} (p r: s)
  : Lemma (requires (p + r) = (zero <: s)) (ensures r = (- p))
  = H.elim_equatable_laws s ();
    H.trans_for_calc s ();
    (* neg p + (p + r) = neg p + zero *)
    add_congruence ((- p)) (p + r) ((- p)) (zero <: s);
    H.x_plus_zero ((- p));                                  (* neg p + zero = neg p *)
    (* (neg p + p) + r = neg p + (p + r) *)
    add_associativity ((- p)) p r;
    H.neg_x_plus_x p;                                       (* neg p + p = zero *)
    add_congruence ((- p) + p) r (zero <: s) r;             (* (neg p + p)+r = zero+r *)
    H.zero_plus_x r;                                        (* zero + r = r *)
    (* chain:  r = (neg p + p) + r = neg p + (p+r) = neg p + zero = neg p *)
    H.trans4 r (((- p) + p) + r) ((- p) + (p + r)) ((- p) + (zero <: s)) ((- p))

(* ================================================================ *)
(*  Generic commutative-ring rearrangement (the heart of D(1/y)).    *)
(*                                                                   *)
(*  Given  y*iy = one  and  a*iy + y*r = zero,  conclude             *)
(*    r = neg (a * (iy * iy)).                                        *)
(* ================================================================ *)
#push-options "--z3rlimit 60"
let recip_solve (#s:Type) {| cr: commutative_ring s |}
  (y iy a r: s)
  : Lemma (requires (y * iy) = (one <: s) /\
                    ((a * iy) + (y * r)) = (zero <: s))
          (ensures  r = (- (a * (iy * iy))))
  = H.elim_equatable_laws s ();
    H.trans_for_calc s ();
    let p : s = a * (iy * iy) in
    (* ---- multiply the hypothesis sum by iy ---- *)
    (* (a*iy + y*r) * iy = zero * iy *)
    mul_congruence ((a * iy) + (y * r)) iy (zero <: s) iy;
    H.zero_mul_x iy;                                        (* zero*iy = zero *)
    (* so ((a*iy)+(y*r))*iy = zero *)
    H.trans2 (((a * iy) + (y * r)) * iy) ((zero <: s) * iy) (zero <: s);
    (* ---- distribute the left product ---- *)
    (* ((a*iy)+(y*r))*iy = (a*iy)*iy + (y*r)*iy *)
    right_distributivity iy (a * iy) (y * r);
    (* so (a*iy)*iy + (y*r)*iy = zero *)
    H.trans2 (((a * iy) * iy) + ((y * r) * iy))
             (((a * iy) + (y * r)) * iy)
             (zero <: s);
    (* ---- simplify (y*r)*iy = r ---- *)
    H.mul_commutativity_cr y r;                             (* y*r = r*y *)
    mul_congruence (y * r) iy (r * y) iy;                   (* (y*r)*iy = (r*y)*iy *)
    mul_associativity r y iy;                               (* (r*y)*iy = r*(y*iy) *)
    mul_congruence r (y * iy) r (one <: s);                 (* r*(y*iy) = r*one *)
    H.x_mul_one r;                                          (* r*one = r *)
    H.trans4 ((y * r) * iy) ((r * y) * iy) (r * (y * iy)) (r * (one <: s)) r;
    (* ---- simplify (a*iy)*iy = a*(iy*iy) = p ---- *)
    mul_associativity a iy iy;                              (* (a*iy)*iy = a*(iy*iy) = p *)
    (* ---- substitute into  (a*iy)*iy + (y*r)*iy = zero ---- *)
    add_congruence ((a * iy) * iy) ((y * r) * iy) p r;      (* = p + r *)
    H.trans2 (p + r) (((a * iy) * iy) + ((y * r) * iy)) (zero <: s);
    (* ---- p + r = zero  ==>  r = neg p ---- *)
    solve_neg p r
#pop-options

(* ================================================================ *)
(*  The differentiated inverse law:  a*iy + y*r = zero.              *)
(*                                                                   *)
(*  Here a = D y, r = D iy, and y*iy = one (inversion law).          *)
(*  Differentiate both sides of y*iy = one:                          *)
(*    D(y*iy) = D(one) = zero            (congruence + D(one)=0)      *)
(*    D(y*iy) = (D y)*iy + y*(D iy)      (Leibniz)                    *)
(*  hence (D y)*iy + y*(D iy) = zero.                                *)
(* ================================================================ *)
#push-options "--z3rlimit 60"
let deriv_inv_law (#t:Type) {| f: field t |}
  (y: fraction (polynomial_id #t #(id_of_f t))
        { is_nonzero y })
  : Lemma ((((rational_deriv y) * (inv y))
              + (y * (rational_deriv (inv y))))
             = (zero <: fraction (polynomial_id #t #(id_of_f t))))
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    let iy : fraction id_p = inv y in
    (* ---- inversion law: y * iy = one ---- *)
    inversion_lemma y;                                      (* y*iy = one /\ iy*y = one *)
    (* ---- differentiate y*iy = one ---- *)
    rcong_field (y * iy) (one <: fraction id_p);      (* D(y*iy) = D(one) *)
    rational_deriv_one #t #f;                               (* D(one) = zero *)
    H.trans2 (rational_deriv (y * iy))
             (rational_deriv (one <: fraction id_p))
             (zero <: fraction id_p);
    (* D(y*iy) = (D y)*iy + y*(D iy)  (Leibniz) *)
    rmul_field y iy;
    (* hence (D y)*iy + y*(D iy) = D(y*iy) = zero *)
    H.trans2 (((rational_deriv y) * iy) + (y * (rational_deriv iy)))
             (rational_deriv (y * iy))
             (zero <: fraction id_p)
#pop-options

(* ================================================================ *)
(*  RECIPROCAL RULE:  D(1/y) = - y' * (1/y)^2.                        *)
(*                                                                   *)
(*  Stated with the field/ring ops of `cr_fr` (inv, neg, mul).       *)
(* ================================================================ *)
#push-options "--z3rlimit 60"
let rational_deriv_inv (#t:Type) {| f: field t |}
  (y: fraction (polynomial_id #t #(id_of_f t))
        { is_nonzero y })
  : Lemma ((rational_deriv (inv y))
             = (- ((rational_deriv y) * (inv y * inv y))))
  = let id_p = polynomial_id #t #(id_of_f t) in
    let iy : fraction id_p = inv y in
    (* differentiated inverse law:  (D y)*iy + y*(D iy) = zero *)
    deriv_inv_law y;
    (* inversion law:  y*iy = one *)
    inversion_lemma y;
    (* pure commutative-ring rearrangement with the side fact y*iy=one *)
    recip_solve #(fraction id_p) #(cr_fr #t #f)
      y iy (rational_deriv y) (rational_deriv iy)
#pop-options

(* ================================================================ *)
(*  QUOTIENT RULE:  D(x/y) = D(x)*(1/y) + x*(- y'*(1/y)^2).           *)
(*                                                                   *)
(*  x * inv y  is the field division;  combine the Leibniz product   *)
(*  rule (rmul_field x iy) with the reciprocal rule via congruence.  *)
(* ================================================================ *)
#push-options "--z3rlimit 60"
let rational_deriv_div (#t:Type) {| f: field t |}
  (x: fraction (polynomial_id #t #(id_of_f t)))
  (y: fraction (polynomial_id #t #(id_of_f t))
        { is_nonzero y })
  : Lemma ((rational_deriv (x * inv y))
             = (((rational_deriv x) * inv y)
                + (x * (- ((rational_deriv y) * (inv y * inv y))))))
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    let iy : fraction id_p = inv y in
    let dx = rational_deriv x in
    let dy = rational_deriv y in
    let diy = rational_deriv iy in
    (* Leibniz:  D(x*iy) = (D x)*iy + x*(D iy) *)
    rmul_field x iy;
    (* reciprocal:  D iy = neg ((D y)*(iy*iy)) *)
    rational_deriv_inv y;
    (* rewrite the second summand:  x*(D iy) = x*(neg ((D y)*(iy*iy))) *)
    mul_congruence x diy x ((- (dy * (iy * iy))));
    add_congruence (dx * iy) (x * diy)
                   (dx * iy) (x * (- (dy * (iy * iy))));
    (* chain:  D(x*iy) = (D x)*iy + x*(D iy)
                       = (D x)*iy + x*(neg ((D y)*(iy*iy))) *)
    H.trans2 (rational_deriv (x * iy))
             ((dx * iy) + (x * diy))
             ((dx * iy) + (x * (- (dy * (iy * iy)))))
#pop-options
