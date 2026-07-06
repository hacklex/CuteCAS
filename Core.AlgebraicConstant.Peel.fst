module Core.AlgebraicConstant.Peel

(*
   §E splitting-field peel step.

   Over the extension field  algebraic r  (r irreducible), the embedded
   base polynomial  ext_embed_poly d  has theta as a root (theta_root_ext).
   The factor theorem then peels the linear factor (X - theta):

       (X - theta)  |  ext_embed_poly d     in  (algebraic r)[X].
*)

module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Roots
open Core.Polynomial.Irreducible
open Core.AlgebraicConstant
open Core.AlgebraicConstant.Root
open Core.AlgebraicConstant.Eval

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* theta evaluates the embedded multiple to the FIELD zero, w.r.t. the resolved
   commutative ring (= acr r = algebraic_commutative_ring r), using its eq.
   This is the one place we bridge ac_eq into the published-ring's abstract eq
   (via algebraic_eq_zero_pointwise — the base does not expose the ring body, so
   this reveal is the only available bridge).  *)
let theta_eval_field_zero (#t:Type) {| f: field t |}
  (r: polynomial t {proper_extension r})
  (d: polynomial t)
  : Lemma (requires divides r d)
          (ensures ((acr r).cr_r.r_add.acg_eq.eq
                      (poly_eval #(algebraic r) #(acr r) (ext_embed_poly #t #f #r d)
                                 (theta #t #f #r))
                      ((acr r).cr_r.r_add.zero)))
  = theta_root_ext #t #f #r d;                       (* ac_eq (poly_eval (embed d) theta) ac_zero *)
    algebraic_eq_zero_pointwise r                    (* (acr r).eq x ac_zero <==> ac_eq x ac_zero *)

(* ================================================================= *)
(*  Peel:  (X - theta) | (ext_embed_poly d)  over algebraic r.     *)
(*                                                                   *)
(*  The field that factor_forward resolves over is the published     *)
(*  algebraic_field instance; its derived commutative ring is        *)
(*  cr_of_id (id_of_f (algebraic_field r)) — which is now DEFEQ to   *)
(*  acr r (= the transparently-defined algebraic_commutative_ring),  *)
(*  so no coerce_eq / type bridge is needed: ext_embed_poly d (acr-  *)
(*  indexed) IS already the field-derived-indexed polynomial.        *)
(* ================================================================= *)
let peel_root_factor (#t:Type) {| f: field t |}
  (r: polynomial t {proper_extension r})
  (d: polynomial t)
  : Lemma (requires divides r d)
          (ensures divides #(polynomial (algebraic r) #(acr r))
                     (poly_linear #(algebraic r) #(algebraic_field #t #f r) (theta #t #f #r))
                     (ext_embed_poly #t #f #r d))
  = theta_eval_field_zero r d;
    factor_forward #(algebraic r) #(algebraic_field #t #f r)
      (ext_embed_poly #t #f #r d) (theta #t #f #r)
