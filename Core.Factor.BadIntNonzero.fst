module Core.Factor.BadIntNonzero

(* ================================================================ *)
(*  C4c — completeness closure:  bad_int B <> 0  for squarefree B.   *)
(*                                                                   *)
(*  Makes `Core.Factor.PrimeExists.good_prime_exists` UNCONDITIONAL: *)
(*  its only hypothesis is  bad_int B = lc B · res(B, B') <> 0, and  *)
(*  we discharge it from  square_free (embed_zq B)  over ℚ.          *)
(*                                                                   *)
(*  Route (det-hom transport ℤ→ℚ, the SAME pattern C4b proved for    *)
(*  ℤ→𝔽ₚ in Core.Factor.ResultantReduction):                        *)
(*    1. res_embed_commute  : embed(res B B') = res (embed B)(embed B')│ℚ *)
(*         via Core.Matrix.DetHom.det_hom on embed_zq's coeff hom.    *)
(*    2. embed_zq_deriv     : embed (B') = (embed B)'  over ℚ.        *)
(*    3. res_int_nonzero    : square_free (embed B) ⟹ res(B,B') <> 0. *)
(*         coprime (embed B)(embed B)' ⟹ (vanishing_iff over ℚ)      *)
(*         res(embed B)(embed B') <> 0 ⟹ (1) embed(res) <> 0 ⟹       *)
(*         res <> 0 (embed_zq_const injective).                      *)
(*    4. bad_int_nonzero    : lc B <> 0 ∧ res <> 0 ⟹ bad_int B <> 0. *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L   = FStar.List.Tot
module Cl  = FStar.Classical
module H   = Core.Algebra.Helpers
module DH  = Core.Matrix.DetHom
module DET = Core.Matrix.Determinant
module SYL = Core.Polynomial.Sylvester
module RES = Core.Polynomial.Resultant
module GC  = Core.Polynomial.GCD
module RR  = Core.Factor.ResultantReduction

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Int
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Permutation
open Core.Vector
open Core.Matrix
open Core.Polynomial.Derivative
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.GCD
open Core.Polynomial.SquareFree
open Core.Fractions
open Core.Polynomial.EmbedQ

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* The ℚ field instance (= EmbedQProd.ff). *)
let ff : field qq = fraction_field int int_id

(* ---------------------------------------------------------------- *)
(*  0.  embed_zq_const ring-hom laws (ℚ RING form).  EmbedQ's are    *)
(*      private, so we re-derive the public forms det_hom needs.     *)
(* ---------------------------------------------------------------- *)

let embed_const_add (a b:int)
  : Lemma (embed_zq_const (a + b) = embed_zq_const a + embed_zq_const b)
  = H.elim_equatable_laws qq ();
    embed_zq_const_add a b;                          (* fraction_add ea eb = embed (a ++ b) *)
    fraction_ring_add_reveal (embed_zq_const a) (embed_zq_const b)          (* ea + eb == fraction_add ea eb *)

let embed_const_mul (a b:int)
  : Lemma (embed_zq_const (a * b) = embed_zq_const a * embed_zq_const b)
  = H.elim_equatable_laws qq ();
    embed_zq_const_mul a b;                          (* fraction_mul ea eb = embed (a*b) *)
    fraction_ring_mul_reveal (embed_zq_const a) (embed_zq_const b)          (* ea * eb == fraction_mul ea eb *)

(* embed 1 = one_qq (re-derived; EmbedQ/EmbedQProd copies are private). *)
let embed_const_one (_:unit)
  : Lemma (embed_zq_const 1 = (one <: qq))
  = let e1 = embed_zq_const 1 in
    let o  : qq = one in
    H.elim_equatable_laws qq ();
    H.x_mul_one e1;                                  (* e1 * o =eq= e1 *)
    fraction_ring_mul_reveal e1 o;      (* e1 * o == fraction_mul e1 o *)
    fraction_mul_reveal e1 o

(* embed (neg a) = neg (embed a)  (negation uniqueness / left cancel). *)
let embed_const_neg (a:int)
  : Lemma (embed_zq_const (- a) = - (embed_zq_const a))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let ea  = embed_zq_const a in
    let ena = embed_zq_const (- a) in
    let nea = - ea in
    fraction_ring_add_reveal ea ena;    (* ea + ena == fraction_add ea ena *)
    embed_zq_const_add a (- a);                       (* fraction_add ea ena = embed (a + neg a) *)
    assert ((a ++ (- a)) == 0);
    embed_zq_const_zero ();                           (* embed 0 =eq= zero *)
    H.x_plus_neg_x ea;                                (* ea + nea =eq= zero *)
    H.group_cancel_left ea ena nea

(* embed commutes with nat_scale (mirror RR.phi_c_nat_scale). *)
let rec embed_const_nat_scale (n:nat) (x:int)
  : Lemma (ensures embed_zq_const (nat_scale n x) = nat_scale n (embed_zq_const x))
          (decreases n)
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    if n = 0 then begin
      nat_scale_zero x;
      nat_scale_zero (embed_zq_const x);
      embed_zq_const_zero ()
    end else begin
      let m : nat = n - 1 in
      nat_scale_succ m x;
      nat_scale_succ m (embed_zq_const x);
      embed_const_add x (nat_scale m x);
      embed_const_nat_scale m x;
      add_congruence (embed_zq_const x) (embed_zq_const (nat_scale m x))
                     (embed_zq_const x) (nat_scale m (embed_zq_const x));
      transitivity (embed_zq_const (nat_scale n x))
                   (embed_zq_const x + embed_zq_const (nat_scale m x))
                   (embed_zq_const x + nat_scale m (embed_zq_const x))
    end

(* ---------------------------------------------------------------- *)
(*  1.  res_embed_commute — the resultant embeds coefficient-wise.   *)
(*      Mirror RR.resultant_reduces with embed_zq_const : ℤ→ℚ.       *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let res_embed_commute
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (b b': polynomial int)
  : Lemma (RES.resultant m_deg n_deg (embed_zq b) (embed_zq b')
         = embed_zq_const (RES.resultant m_deg n_deg b b'))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let sz : pos = m_deg ++ n_deg in
    let eb  = embed_zq b in
    let eb' = embed_zq b' in
    let sB  : square_matrix int sz = SYL.sylvester_matrix m_deg n_deg b b' in
    let sEB : square_matrix qq sz  = SYL.sylvester_matrix m_deg n_deg eb eb' in
    let mapS : square_matrix qq sz = DH.map_matrix embed_zq_const sB in
    let syl_entry (i j: fin sz) : Lemma (sEB i j = mapS i j) =
      H.elim_equatable_laws qq ();
      if (i <: nat) < n_deg then begin
        SYL.sylvester_p_block_lookup m_deg n_deg eb eb' i j;
        SYL.sylvester_p_block_lookup m_deg n_deg b b' i j;
        embed_zq_coeff b ((m_deg ++ (i <: nat)) - (j <: nat))
      end else begin
        SYL.sylvester_q_block_lookup m_deg n_deg eb eb' i j;
        SYL.sylvester_q_block_lookup m_deg n_deg b b' i j;
        embed_zq_coeff b' ((i <: nat) - (j <: nat))
      end
    in
    Cl.forall_intro_2 syl_entry;
    DET.det_pointwise_eq #qq #crq sEB mapS;          (* det sEB = det mapS *)
    embed_zq_const_zero ();
    embed_const_one ();
    DH.det_hom #int #qq #int_cr #crq embed_zq_const () ()
      embed_const_add embed_const_mul embed_const_neg sB;
                                                     (* embed (det sB) = det mapS *)
    RES.resultant_unfold m_deg n_deg b b';           (* res b b' == det sB *)
    RES.resultant_unfold m_deg n_deg eb eb';         (* res(embed) == det sEB *)
    symmetry (embed_zq_const (DET.det sB)) (DET.det #qq #crq mapS);
    transitivity (RES.resultant m_deg n_deg eb eb') (DET.det #qq #crq sEB) (DET.det #qq #crq mapS);
    transitivity (RES.resultant m_deg n_deg eb eb') (DET.det #qq #crq mapS)
                 (embed_zq_const (RES.resultant m_deg n_deg b b'))
#pop-options

(* ---------------------------------------------------------------- *)
(*  2.  embed_zq_deriv — embedding commutes with the derivative.     *)
(*      Mirror RR.deriv_reduce_commute with embed_zq_const.          *)
(* ---------------------------------------------------------------- *)

let embed_zq_deriv (b: polynomial int)
  : Lemma (poly_eq (embed_zq (poly_deriv b)) (poly_deriv (embed_zq b)))
  = let lhs = embed_zq (poly_deriv b) in
    let rhs = poly_deriv (embed_zq b) in
    let h (j:nat) : Lemma (coeff lhs j = coeff rhs j) =
      H.elim_equatable_laws qq ();
      H.trans_for_calc qq ();
      let cbj1 = coeff b (j ++ 1) in
      (* LHS: coeff lhs j =eq= embed (coeff (poly_deriv b) j) = embed (nat_scale (j+1) cbj1) *)
      embed_zq_coeff (poly_deriv b) j;
      poly_deriv_coeff #int b j;                      (* coeff (poly_deriv b) j = nat_scale (j+1) cbj1 *)
      embed_const_nat_scale (j ++ 1) cbj1;            (* embed (nat_scale (j+1) cbj1) = nat_scale (j+1) (embed cbj1) *)
      (* RHS: coeff rhs j = nat_scale (j+1) (coeff (embed b) (j+1)) *)
      poly_deriv_coeff #qq #crq (embed_zq b) j;
      embed_zq_coeff b (j ++ 1);                      (* coeff (embed b) (j+1) =eq= embed cbj1 *)
      nat_scale_congruence (j ++ 1)
        (coeff (embed_zq b) (j ++ 1)) (embed_zq_const cbj1)
    in
    poly_eq_by_coeff lhs rhs h

(* ---------------------------------------------------------------- *)
(*  3a.  Exact derivative degree over ℤ (char 0).                    *)
(* ---------------------------------------------------------------- *)

(* nat_scale over ℤ is plain multiplication: nat_scale n x == n * x. *)
let rec nat_scale_int_eq (n:nat) (x:int)
  : Lemma (ensures nat_scale n x == n * x) (decreases n)
  = if n = 0 then nat_scale_zero x
    else begin
      nat_scale_succ #int (n - 1) x;
      nat_scale_int_eq (n - 1) x
    end

let deriv_deg_exact_int (b: polynomial int{deg b >= 1})
  : Lemma (deg (poly_deriv b) == deg b - 1)
  = let d : nat = deg b in
    let lc = coeff b d in
    leading_coeff_nonzero b;                          (* lc <> 0 *)
    RR.deriv_deg_lt #int b;                           (* deg (poly_deriv b) <= d - 1 *)
    (* coeff (poly_deriv b) (d-1) = nat_scale d lc <> 0 ⇒ deg >= d - 1 *)
    poly_deriv_coeff #int b (d - 1);                  (* coeff (poly_deriv b) (d-1) = nat_scale ((d-1)+1) (coeff b ((d-1)+1)) *)
    nat_scale_int_eq d lc;                            (* nat_scale d lc == d * lc *)
    let _ : squash (deg (poly_deriv b) >= d - 1) =
      if deg (poly_deriv b) < d - 1 then coeff_above_degree (poly_deriv b) (d - 1) else () in
    ()

(* ---------------------------------------------------------------- *)
(*  3b.  Coprimality transfers across a poly_eq second argument (ℚ). *)
(* ---------------------------------------------------------------- *)

let coprime_transfer_q (x y1 y2: polynomial qq #crq)
  : Lemma (requires (y1 = y2) /\ coprime #qq #ff x y1)
          (ensures coprime #qq #ff x y2)
  = H.elim_equatable_laws (polynomial qq #crq) ();
    reflexivity x;
    gcd_congruence #qq #ff x x y1 y2;
    degree_well_defined (GC.poly_gcd #qq #ff x y1) (GC.poly_gcd #qq #ff x y2);
    coprime_reveal #qq #ff x y1;
    coprime_reveal #qq #ff x y2

(* ---------------------------------------------------------------- *)
(*  3c.  res(B, B') <> 0 over ℤ from squarefreeness over ℚ.          *)
(* ---------------------------------------------------------------- *)

(* Degenerate case  deg B == 1  (n_deg = 0): res 1 0 B B' = coeff B' 0
   = lc B <> 0, via the 1x1 Sylvester determinant. *)
let res_deg1_nonzero (b: polynomial int{deg b == 1})
  : Lemma (RES.resultant 1 0 b (poly_deriv b) <> 0)
  = let b' = poly_deriv b in
    let s = SYL.sylvester_matrix 1 0 b b' in
    H.elim_equatable_laws int ();
    DET.determinant_size_one s;                       (* det s = s 0 0 *)
    SYL.sylvester_q_block_lookup 1 0 b b'
      (0 <: fin (SYL.nat_add 1 0)) (0 <: fin (SYL.nat_add 1 0));
                                                     (* s 0 0 == coeff b' 0 *)
    RES.resultant_unfold 1 0 b b';                    (* res == det s *)
    poly_deriv_coeff #int b 0;                        (* coeff b' 0 = nat_scale 1 (coeff b 1) *)
    nat_scale_one (coeff b 1);                   (* nat_scale 1 (coeff b 1) = coeff b 1 *)
    leading_coeff_nonzero b                           (* coeff b (deg b) = coeff b 1 <> 0 *)

(* the ℚ image of a nonzero-forced resultant is nonzero, so the ℤ one is. *)
#push-options "--z3rlimit 40"
let res_int_nonzero_of_squarefree (b: polynomial int{deg b >= 1})
  : Lemma (requires square_free #qq #ff (embed_zq b))
          (ensures RES.resultant (deg b) (deg b - 1) b (poly_deriv b) <> 0)
  = let d : nat = deg b in
    if d = 1 then res_deg1_nonzero b
    else begin
      let b'  = poly_deriv b in
      let eb  = embed_zq b in
      let eb' = embed_zq b' in
      H.elim_equatable_laws qq ();
      H.trans_for_calc qq ();
      (* degrees *)
      embed_zq_deg b;                                 (* deg eb == d *)
      deriv_deg_exact_int b;                          (* deg b' == d - 1 *)
      embed_zq_deg b';                                (* deg eb' == d - 1 *)
      (* coprimality: square_free ⟹ coprime eb (poly_deriv eb) ⟹ coprime eb eb' *)
      embed_zq_deriv b;                               (* eb' = poly_deriv eb *)
      H.elim_equatable_laws (polynomial qq #crq) ();
      symmetry eb' (poly_deriv eb);                   (* poly_deriv eb = eb' *)
      assert (coprime #qq #ff eb (poly_deriv eb));    (* from square_free hypothesis *)
      coprime_transfer_q eb (poly_deriv eb) eb';      (* coprime eb eb' *)
      coprime_reveal #qq #ff eb eb';                  (* deg (gcd eb eb') = 0 *)
      (* vanishing_iff over ℚ: res(eb, eb') = 0 <==> deg gcd >= 1 (false) *)
      RES.resultant_vanishing_iff #qq #ff d (d - 1) eb eb';
      (* res(eb, eb') <> 0 ; res_embed_commute ⟹ embed(res_ℤ) <> 0 ⟹ res_ℤ <> 0 *)
      res_embed_commute d (d - 1) b b';               (* res(eb, eb') = embed (res_ℤ) *)
      embed_zq_const_zero_iff (RES.resultant d (d - 1) b b')
    end
#pop-options

(* ---------------------------------------------------------------- *)
(*  4.  bad_int B <> 0  for squarefree B.                            *)
(* ---------------------------------------------------------------- *)

let bad_int_nonzero (b: polynomial int{deg b >= 1})
  : Lemma (requires square_free #qq #ff (embed_zq b))
          (ensures RR.bad_int b <> 0)
  = leading_coeff_nonzero b;                          (* poly_lc b <> 0 *)
    poly_lc_reveal b;
    res_int_nonzero_of_squarefree b;                  (* res(B,B') <> 0 *)
    RR.bad_int_unfold b                                (* bad_int = lc * res ; product of nonzero ints *)
