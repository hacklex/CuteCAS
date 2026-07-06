module Core.AlgebraicConstant.EmbedSquareFree

(*
   §E splitting-field bridge (E2):  squarefreeness is preserved under the
   coefficient-wise field embedding  ext_embed_poly : t[X] -> (algebraic r)[X].

   Main deliverable:
     ext_embed_square_free d :  deg d >= 1 /\ square_free d
                                ==> square_free (ext_embed_poly d)

   Route (Bezout transport):
     - square_free d  =  coprime d (poly_deriv d)   (over the base field t)
     - Bezout: bl*d + br*d' = 1                     (bezout_identity)
     - ext_embed_poly is a ring hom (EmbedHom): embed both sides
     - the derivative commutes with the embedding  (deriv_commutes)
     - so  (emb bl)*(emb d) + (emb br)*(poly_deriv (emb d))  =  1  over algebraic r
     - a Bezout combination = 1  ==>  coprime  (bezout_implies_coprime)
*)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.Derivative
open Core.Polynomial.GCD
open Core.Polynomial.Irreducible
open Core.Polynomial.PartialFraction
open Core.Polynomial.SquareFree
open Core.Polynomial.SplitDivisor        (* poly_one_deg, bezout_implies_coprime *)
open Core.AlgebraicConstant
open Core.AlgebraicConstant.Root
open Core.AlgebraicConstant.Eval
open Core.AlgebraicConstant.EmbedHom
open Core.AlgebraicConstant.EmbedEval      (* ac_const_one, ext_embed_congr *)
open Core.AlgebraicConstant.EmbedTransport (* embed_one *)

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  A.  Generic Bezout-implies-coprime helpers now live in           *)
(*      Core.Polynomial.SplitDivisor (divisor_of_one_deg_ge0,        *)
(*      bezout_implies_coprime).                                     *)
(* ================================================================ *)

(* ================================================================ *)
(*  B.  ac_const one ~ ac_one  is EmbedEval.ac_const_one.           *)
(* ================================================================ *)

(* ================================================================ *)
(*  C.  ac_const commutes with nat_scale (repeated addition).         *)
(* ================================================================ *)

let rec ac_const_nat_scale (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
  (n: nat) (c: t)
  : Lemma (ensures (ac_eq (ac_const #_ #_ #r (nat_scale n c))
                          (nat_scale n (ac_const #_ #_ #r c))))
          (decreases n)
  = ac_elim_equatable_laws r;
    algebraic_eq_zero_pointwise r;
    if n = 0 then begin
      nat_scale_zero c;                              (* nat_scale 0 c        == zero(t) *)
      nat_scale_zero (ac_const #_ #_ #r c);          (* nat_scale 0 (ac_const c) == zero(ext) *)
      ac_const_zero #_ #_ #r ()                      (* ac_const zero ~ ac_zero == zero(ext) *)
    end
    else begin
      let cc : algebraic r = ac_const c in
      nat_scale_succ (n - 1) c;                      (* nat_scale n c  == c  + nat_scale (n-1) c *)
      nat_scale_succ (n - 1) cc;                     (* nat_scale n cc == cc + nat_scale (n-1) cc *)
      (* nat_scale n c == c + nat_scale (n-1) c *)
      ac_const_add #_ #_ #r c (nat_scale (n - 1) c);
        (* ac_const (c + nat_scale(n-1)c) = ac_const c + ac_const (nat_scale(n-1)c) *)
      ac_const_nat_scale #_ #_ #r (n - 1) c;         (* IH *)
      add_congruence cc (ac_const (nat_scale (n - 1) c))
                     cc (nat_scale (n - 1) cc);
      (* chain to nat_scale n cc == cc + nat_scale (n-1) cc *)
      transitivity
        (ac_const (nat_scale n c))
        (cc + ac_const (nat_scale (n - 1) c))
        (cc + nat_scale (n - 1) cc)
    end

(* ================================================================ *)
(*  D.  The derivative commutes with the coefficient embedding.       *)
(* ================================================================ *)

let deriv_commutes (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
  (d: polynomial t)
  : Lemma ((ext_embed_poly #_ #_ #r (poly_deriv d))
           = (poly_deriv (ext_embed_poly #_ #_ #r d)))
  = ac_elim_equatable_laws r;
    let ed  : polynomial (algebraic r) = ext_embed_poly d in
    let lhs : polynomial (algebraic r) = ext_embed_poly (poly_deriv d) in
    let rhs : polynomial (algebraic r) = poly_deriv ed in
    let aux (k:nat) : Lemma (coeff lhs k = coeff rhs k) =
      (* LHS: coeff lhs k = ac_const (coeff (poly_deriv d) k)
                          = ac_const (nat_scale (k+1) (coeff d (k+1)))
                          = nat_scale (k+1) (ac_const (coeff d (k+1))) *)
      embed_coeff #_ #_ #r (poly_deriv d) k;
      poly_deriv_coeff d k;
      ac_const_congr #_ #_ #r (coeff (poly_deriv d) k)
                              (nat_scale (k ++ 1) (coeff d (k ++ 1)));
      ac_const_nat_scale #_ #_ #r (k ++ 1) (coeff d (k ++ 1));
      (* RHS: coeff rhs k = nat_scale (k+1) (coeff ed (k+1))
                          = nat_scale (k+1) (ac_const (coeff d (k+1))) *)
      poly_deriv_coeff ed k;
      embed_coeff #_ #_ #r d (k ++ 1);
      nat_scale_congruence (k ++ 1) (coeff ed (k ++ 1))
                           (ac_const #_ #_ #r (coeff d (k ++ 1)));
      (* both sides equal the common middle nat_scale (k+1)(ac_const(coeff d (k+1))) *)
      transitivity
        (coeff lhs k)
        (ac_const (nat_scale (k ++ 1) (coeff d (k ++ 1))))
        (nat_scale (k ++ 1) (ac_const #_ #_ #r (coeff d (k ++ 1))));
      transitivity
        (coeff lhs k)
        (nat_scale (k ++ 1) (ac_const #_ #_ #r (coeff d (k ++ 1))))
        (coeff rhs k)
    in
    poly_eq_by_coeff lhs rhs aux

(* ================================================================ *)
(*  E.  ext_embed_poly respects poly_eq (EmbedEval.ext_embed_congr)  *)
(*      and sends 1 to 1 (EmbedTransport.embed_one).                 *)
(* ================================================================ *)

(* ================================================================ *)
(*  F.  Main theorem: squarefreeness transports through the embedding. *)
(* ================================================================ *)

#push-options "--z3rlimit 80"
let ext_embed_square_free (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
  (d: polynomial t)
  : Lemma (requires deg d >= 1 /\ square_free d)
          (ensures  square_free (ext_embed_poly #_ #_ #r d))
  = H.elim_equatable_laws (polynomial (algebraic r)) ();
    H.trans_for_calc (polynomial (algebraic r)) ();
    ac_elim_equatable_laws r;
    let d'  : polynomial t = poly_deriv d in
    let bl  : polynomial t = bezout_left  d d' in
    let br  : polynomial t = bezout_right d d' in
    bezout_identity d d';                           (* (bl*d + br*d') = poly_one *)
    let ed  : polynomial (algebraic r) = ext_embed_poly d in
    let ed' : polynomial (algebraic r) = ext_embed_poly d' in
    let ebl : polynomial (algebraic r) = ext_embed_poly bl in
    let ebr : polynomial (algebraic r) = ext_embed_poly br in
    let dd  : polynomial (algebraic r) = poly_deriv ed in
    (* Embed both sides of the Bezout identity. *)
    ext_embed_congr #_ #_ #r ((bl * d) + (br * d')) (poly_one #t);    (* F1 *)
    embed_one #_ #_ #r ();                                            (* F2 *)
    (* Ring-hom decomposition of the LHS. *)
    ext_embed_poly_add #_ #_ #r (bl * d) (br * d');                   (* F3 *)
    ext_embed_poly_mul #_ #_ #r bl d;                                (* F4 *)
    ext_embed_poly_mul #_ #_ #r br d';                               (* F5 *)
    add_congruence
      (ext_embed_poly (bl * d)) (ext_embed_poly (br * d'))
      (ebl * ed) (ebr * ed');                                        (* F6 *)
    (* Replace ed' by poly_deriv ed. *)
    deriv_commutes #_ #_ #r d;                                       (* ed' = dd *)
    mul_congruence ebr ed' ebr dd;
    add_congruence (ebl * ed) (ebr * ed') (ebl * ed) (ebr * dd);     (* F8 *)
    (* armed trans/sym chain: (ebl*ed)+(ebr*dd) = ... = 1(ext) *)
    (* Conclude coprimality of ed with its derivative. *)
    bezout_implies_coprime ed dd ebl ebr
#pop-options
