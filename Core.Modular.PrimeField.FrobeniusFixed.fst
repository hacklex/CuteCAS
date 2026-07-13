module Core.Modular.PrimeField.FrobeniusFixed

(* ================================================================ *)
(*  #29 STAGE B: per-component Frobenius fixed points.               *)
(*                                                                   *)
(*  Over the prime field  fp p  (p prime), an irreducible modulus    *)
(*  f  with  proper_extension f  (= poly_irreducible f /\ deg f>=2)  *)
(*  yields the residue field  algebraic f.  The Frobenius-fixed      *)
(*  residues  a : algebraic f  with  a^p ~ a  are EXACTLY the        *)
(*  constants  { ac_const c : c in fp p }.                           *)
(*                                                                   *)
(*  Power = cpow (Core.Polynomial.Eval), the canonical power of any  *)
(*  commutative_ring, and the one the ac_const / ext_embed / eval    *)
(*  machinery is built on.                                            *)
(*                                                                   *)
(*  B1 const_is_frobenius_fixed  : (ac_const c)^p ~ ac_const c.       *)
(*  B2 frobenius_fixed_is_const  : a^p ~ a  ==>  exists c. a ~ ac_const c. *)
(*  B3 const_injective_on_fixed  : c<>c'  ==>  ac_const c <> ac_const c'.  *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module PW = Core.Algebra.Power
module CF = Core.Modular.PrimeField.Frobenius
module ET = Core.AlgebraicConstant.EmbedTransport
module EE = Core.AlgebraicConstant.EmbedEval
module EH = Core.AlgebraicConstant.EmbedHom
module AE = Core.AlgebraicConstant.Eval

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
open Core.Modular.PrimeField
open Core.Modular.PrimeField.Berlekamp
open Core.NumberTheory

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  0.  Fermat in cpow form:  cpow #(fp p) c p == c.                  *)
(*      The ac_const / eval machinery uses cpow (commutative_ring    *)
(*      power); Frobenius.fermat_fp is stated with PW.rpow (ring     *)
(*      power).  The two recursions coincide over fp p.              *)
(* ================================================================ *)

let rec cpow_eq_rpow (p:int{is_prime p}) (c: fp p) (n:nat)
  : Lemma (ensures cpow #(fp p) c n == PW.rpow #(fp p) c n)
          (decreases n)
  = if n = 0 then () else cpow_eq_rpow p c (n-1)

let fermat_cpow (p:int{is_prime p}) (c: fp p)
  : Lemma (cpow #(fp p) c p == c)
  = cpow_eq_rpow p c p;
    CF.fermat_fp p c

(* ================================================================ *)
(*  B1.  Each constant is Frobenius-fixed.                           *)
(* ================================================================ *)

let const_is_frobenius_fixed
      (#p:int{is_prime p}) (f: polynomial (fp p){proper_extension f}) (c: fp p)
  : Lemma (ac_eq (cpow (ac_const #_ #_ #f c) p) (ac_const #_ #_ #f c))
  = ac_elim_equatable_laws f;
    fermat_cpow p c;                          (* cpow c p == c  in fp p *)
    EE.ac_const_power #_ #_ #f c p            (* ac_eq (ac_const (cpow c p)) (cpow (ac_const c) p) *)

(* ================================================================ *)
(*  B3.  ac_const is injective on the fixed set (constants distinct).*)
(* ================================================================ *)

let const_injective_on_fixed
      (#p:int{is_prime p}) (f: polynomial (fp p){proper_extension f}) (c c': fp p)
  : Lemma (requires not (c = c'))
          (ensures  not (ac_eq (ac_const #_ #_ #f c) (ac_const #_ #_ #f c')))
  = ET.ac_const_inj #_ #_ #f c c'

(* ================================================================ *)
(*  B2 machinery.  The route (working in the field K = algebraic f): *)
(*    X^p - X  splits over fp p as  prod_{c}(X - c)  (xpx_splits).    *)
(*    Embed into K[X] (ext_embed_poly hom) and evaluate at a:         *)
(*      a^p - a  =  poly_eval (ext_embed (X^p-X)) a                   *)
(*              =  eval_prod_sub (map ac_const (fp_enum p)) a.        *)
(*    If a^p ~ a the value is 0; field has no zero divisors, so some  *)
(*    factor  (a - ac_const c)  is 0, i.e.  a ~ ac_const c.           *)
(* ================================================================ *)

(* cpow respects the ring equality of its base. *)
let rec cpow_congr (#t:Type) {| cr: commutative_ring t |} (x y: t) (k:nat)
  : Lemma (requires x = y) (ensures cpow x k = cpow y k) (decreases k)
  = H.elim_equatable_laws t ();
    if k = 0 then ()
    else begin
      cpow_congr x y (k-1);
      mul_congruence x (cpow x (k-1)) y (cpow y (k-1))
    end

(* ext_embed_poly is a negation homomorphism (coefficient-wise ac_const_neg). *)
let ext_embed_poly_neg (#t:Type) {| ff: field t |} (#r: polynomial t {proper_extension r})
                       (b: polynomial t)
  : Lemma (ext_embed_poly #_ #_ #r (poly_neg b) = poly_neg (ext_embed_poly #_ #_ #r b))
  = let eb  : polynomial (algebraic r) = ext_embed_poly #_ #_ #r b in
    let enb : polynomial (algebraic r) = ext_embed_poly #_ #_ #r (poly_neg b) in
    let h (j:nat) : Lemma (coeff enb j = coeff (poly_neg eb) j) =
      ac_elim_equatable_laws r;
      embed_coeff #_ #_ #r (poly_neg b) j;      (* coeff enb j = ac_const (coeff (poly_neg b) j) *)
      poly_neg_coeff b j;                        (* coeff (poly_neg b) j = - coeff b j *)
      EH.ac_const_congr #_ #_ #r (coeff (poly_neg b) j) (- (coeff b j));
      ET.ac_const_neg #_ #_ #r (coeff b j);      (* ac_const (- coeff b j) = - ac_const (coeff b j) *)
      embed_coeff #_ #_ #r b j;                  (* coeff eb j = ac_const (coeff b j) *)
      neg_congruence (ac_const #_ #_ #r (coeff b j)) (coeff eb j);
      poly_neg_coeff eb j                        (* coeff (poly_neg eb) j = - coeff eb j *)
    in
    poly_eq_by_coeff enb (poly_neg eb) h

(* ext_embed_poly is a power homomorphism. *)
let rec embed_poly_power (#t:Type) {| ff: field t |} (#r: polynomial t {proper_extension r})
                         (g: polynomial t) (k:nat)
  : Lemma (ensures ext_embed_poly #_ #_ #r (poly_power g k)
                   = poly_power (ext_embed_poly #_ #_ #r g) k)
          (decreases k)
  = H.elim_equatable_laws (polynomial (algebraic r)) ();
    if k = 0 then
      ET.embed_one #_ #_ #r ()
    else begin
      let eg = ext_embed_poly #_ #_ #r g in
      EH.ext_embed_poly_mul #_ #_ #r g (poly_power g (k-1));
      embed_poly_power #_ #_ #r g (k-1);
      mul_congruence eg (ext_embed_poly #_ #_ #r (poly_power g (k-1)))
                     eg (poly_power eg (k-1));
      transitivity
        (ext_embed_poly #_ #_ #r (poly_power g k))
        (eg * (ext_embed_poly #_ #_ #r (poly_power g (k-1))))
        (eg * (poly_power eg (k-1)))
    end

(* poly_eval is a power homomorphism:  eval (g^k) c = (eval g c)^k. *)
let rec eval_poly_pow_gen (#t:Type) {| cr: commutative_ring t |}
                          (g: polynomial t) (c: t) (k:nat)
  : Lemma (ensures poly_eval (poly_power g k) c = cpow (poly_eval g c) k)
          (decreases k)
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    if k = 0 then
      eval_one #t c
    else begin
      eval_mul g (poly_power g (k-1)) c;
      eval_poly_pow_gen g c (k-1);
      mul_congruence (poly_eval g c) (poly_eval (poly_power g (k-1)) c)
                     (poly_eval g c) (cpow (poly_eval g c) (k-1))
    end

(* eval of embedded X at any a is a  (X = polyX = poly_linear 0, embeds to (x - ac_const 0)). *)
let eval_embed_polyX (#p:int{is_prime p}) (f: polynomial (fp p){proper_extension f})
                     (a: algebraic f)
  : Lemma (ac_eq (poly_eval (ext_embed_poly #_ #_ #f (polyX p)) a) a)
  = ac_elim_equatable_laws f;
    polyX_reveal p;                                (* polyX p == poly_linear (fp_zero p) *)
    let e0 : algebraic f = ac_const #_ #_ #f (fp_zero p) in
    ET.embed_linear #_ #_ #f (fp_zero p);          (* ext_embed(polyX) = poly_linear e0 *)
    eval_congruence (ext_embed_poly #_ #_ #f (polyX p)) (poly_linear e0) a;
    eval_linear #(algebraic f) e0 a;               (* eval (poly_linear e0) a = (-e0) + a *)
    EH.ac_const_zero #_ #_ #f ();                  (* e0 ~ ac_zero *)
    algebraic_eq_zero_pointwise f;                 (* zero == ac_zero, so e0 ~ zero *)
    neg_congruence e0 (zero <: algebraic f);       (* -e0 ~ -zero *)
    H.neg_zero #(algebraic f) ();                  (* -zero ~ zero *)
    add_congruence (- e0) a (zero <: algebraic f) a;  (* (-e0)+a ~ zero+a *)
    H.zero_plus_x a                                (* zero + a ~ a *)

(* eval of embedded X^p at a is a^p. *)
let eval_embed_xp (#p:int{is_prime p}) (f: polynomial (fp p){proper_extension f})
                  (a: algebraic f)
  : Lemma (ac_eq (poly_eval (ext_embed_poly #_ #_ #f (poly_power (polyX p) (p <: nat))) a)
                 (cpow a p))
  = ac_elim_equatable_laws f;
    let ex : polynomial (algebraic f) = ext_embed_poly #_ #_ #f (polyX p) in
    embed_poly_power #_ #_ #f (polyX p) (p <: nat);  (* ext_embed(X^p) = ex^p *)
    eval_congruence (ext_embed_poly #_ #_ #f (poly_power (polyX p) (p <: nat)))
                    (poly_power ex (p <: nat)) a;
    eval_poly_pow_gen ex a (p <: nat);               (* eval (ex^p) a = cpow (eval ex a) p *)
    eval_embed_polyX #p f a;                         (* eval ex a ~ a *)
    cpow_congr (poly_eval ex a) a (p <: nat)         (* cpow (eval ex a) p ~ cpow a p *)

(* eval of embedded X^p - X at a is a^p - a. *)
let eval_embed_xpx (#p:int{is_prime p}) (f: polynomial (fp p){proper_extension f})
                   (a: algebraic f)
  : Lemma (ac_eq (poly_eval (ext_embed_poly #_ #_ #f (xpx p)) a)
                 ((cpow a p) + (- a)))
  = ac_elim_equatable_laws f;
    H.elim_equatable_laws (polynomial (algebraic f)) ();
    let bigA : polynomial (fp p) = poly_power (polyX p) (p <: nat) in
    let bigB : polynomial (fp p) = polyX p in
    let eA : polynomial (algebraic f) = ext_embed_poly #_ #_ #f bigA in
    let eB : polynomial (algebraic f) = ext_embed_poly #_ #_ #f bigB in
    xpx_reveal p;                                   (* xpx p == bigA -- bigB == bigA + (- bigB) *)
    assert (xpx p == (bigA + (- bigB)));
    EH.ext_embed_poly_add #_ #_ #f bigA (- bigB);   (* embed(bigA + (-bigB)) = eA + embed(-bigB) *)
    ext_embed_poly_neg #_ #_ #f bigB;               (* embed(-bigB) = - eB *)
    add_congruence eA (ext_embed_poly #_ #_ #f (- bigB)) eA (- eB);
    transitivity (ext_embed_poly #_ #_ #f (xpx p))
                 (eA + (ext_embed_poly #_ #_ #f (- bigB)))
                 (eA + (- eB));
    (* eval at a *)
    eval_congruence (ext_embed_poly #_ #_ #f (xpx p)) (eA + (- eB)) a;
    eval_add eA (- eB) a;                           (* eval(eA + (-eB)) a = eval eA a + eval(-eB) a *)
    eval_neg eB a;                                  (* eval(-eB) a = - eval eB a *)
    add_congruence (poly_eval eA a) (poly_eval (- eB) a)
                   (poly_eval eA a) (- (poly_eval eB a));
    eval_embed_xp #p f a;                           (* eval eA a ~ cpow a p *)
    eval_embed_polyX #p f a;                        (* eval eB a ~ a *)
    neg_congruence (poly_eval eB a) a;              (* - eval eB a ~ - a *)
    add_congruence (poly_eval eA a) (- (poly_eval eB a))
                   (cpow a p) (- a)

(* A product of linear differences that vanishes exposes a coincident root. *)
let rec prod_sub_zero_gives_root (#t:Type) {| ff: field t |} (b: t) (roots: list t)
  : Lemma (requires eval_prod_sub roots b = zero)
          (ensures  (exists (y:t). L.memP y roots /\ b = y))
          (decreases roots)
  = H.elim_equatable_laws t ();
    match roots with
    | [] ->
        let _ : squash (not (one #t = zero)) = ff.f_one_ne_zero in
        ()
    | x :: rest ->
        domain_law ((- x) + b) (eval_prod_sub rest b);
        eliminate (((- x) + b) = zero) \/ ((eval_prod_sub rest b) = zero)
        returns (exists (y:t). L.memP y roots /\ b = y)
        with _hl.
          begin
            H.neg_x_plus_x x;                       (* (-x)+x = zero *)
            symmetry (zero <: t) ((- x) + x);       (* zero = (-x)+x *)
            transitivity ((- x) + b) (zero <: t) ((- x) + x);  (* (-x)+b = (-x)+x *)
            H.group_cancel_left (- x) b x;          (* ==> b = x *)
            introduce exists (y:t). L.memP y roots /\ b = y
            with x and ()
          end
        and _hr.
          begin
            prod_sub_zero_gives_root b rest;
            eliminate exists (y:t). L.memP y rest /\ b = y
            returns (exists (z:t). L.memP z roots /\ b = z)
            with _pf.
              introduce exists (z:t). L.memP z roots /\ b = z
              with y and ()
          end

(* ================================================================ *)
(*  B2.  Every Frobenius-fixed residue is a constant.                *)
(* ================================================================ *)

let frobenius_fixed_is_const
      (#p:int{is_prime p}) (f: polynomial (fp p){proper_extension f}) (a: algebraic f)
  : Lemma (requires ac_eq (cpow a p) a)
          (ensures  (exists (c: fp p). ac_eq a (ac_const #_ #_ #f c)))
  = ac_elim_equatable_laws f;
    H.elim_equatable_laws (polynomial (algebraic f)) ();
    let cs : list (algebraic f) = L.map (ac_const #_ #_ #f) (fp_enum p) in
    (* Fact A:  ext_embed(xpx) = poly_prod_linears cs. *)
    xpx_splits p;                                     (* xpx = poly_prod_linears (fp_enum p) *)
    EE.ext_embed_congr #_ #_ #f (xpx p) (poly_prod_linears (fp_enum p));
    ET.embed_prod_linears #_ #_ #f (fp_enum p);       (* embed(prod_linears roots) = prod_linears cs *)
    transitivity (ext_embed_poly #_ #_ #f (xpx p))
                 (ext_embed_poly #_ #_ #f (poly_prod_linears (fp_enum p)))
                 (poly_prod_linears cs);
    (* eval both descriptions at a *)
    eval_congruence (ext_embed_poly #_ #_ #f (xpx p)) (poly_prod_linears cs) a;
    eval_poly_prod_linears cs a;                      (* eval(prod_linears cs) a = eval_prod_sub cs a *)
    (* Fact B:  eval(ext_embed xpx) a ~ cpow a p + (-a) ~ zero (Frobenius fixed). *)
    eval_embed_xpx #p f a;
    add_congruence (cpow a p) (- a) a (- a);          (* cpow a p + (-a) ~ a + (-a) *)
    H.x_plus_neg_x a;                                 (* a + (-a) ~ zero *)
    (* hence  eval_prod_sub cs a ~ zero *)
    (* product zero ==> some listed root coincides with a *)
    prod_sub_zero_gives_root #(algebraic f) a cs;
    eliminate exists (e: algebraic f). L.memP e cs /\ a = e
    returns (exists (c: fp p). ac_eq a (ac_const #_ #_ #f c))
    with _pf.
      begin
        L.memP_map_elim (ac_const #_ #_ #f) e (fp_enum p);
        eliminate exists (c0: fp p). L.memP c0 (fp_enum p) /\ e == ac_const #_ #_ #f c0
        returns (exists (c: fp p). ac_eq a (ac_const #_ #_ #f c))
        with _pf2.
          introduce exists (c: fp p). ac_eq a (ac_const #_ #_ #f c)
          with c0 and ()
      end
