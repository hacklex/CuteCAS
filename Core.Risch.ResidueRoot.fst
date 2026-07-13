module Core.Risch.ResidueRoot

(* ================================================================ *)
(*  Residue <-> resultant-root correspondence (Rothstein-Trager).    *)
(*                                                                    *)
(*  A constant c is a RESIDUE of p/q iff the RT log-argument gcd      *)
(*    v_c = gcd(p - c*q', q)                                          *)
(*  is nontrivial (deg v_c >= 1), iff c is a root of the RT           *)
(*  resultant  R = lrt_resultant_raw p q  (R(c) = 0).                 *)
(*                                                                    *)
(*  Inputs (already proven):                                          *)
(*   - Core.Risch.LRT.lrt_resultant_specializes:                      *)
(*       R(c) = res_x(p - c*q', q).                                   *)
(*   - Core.Polynomial.Resultant.resultant_vanishing_iff / _converse /    *)
(*     _zero_of_common_divisor / _zero_when_p_all_zero /              *)
(*     gcd_deg_when_pp_zero:                                          *)
(*       over a field,  res(A,B)=0  <=>  deg(gcd A B) >= 1.           *)
(* ================================================================ *)

module L   = FStar.List.Tot
module T   = FStar.Tactics
module H   = Core.Algebra.Helpers
module SP  = Core.Polynomial.Roots
module RES = Core.Polynomial.Resultant
module LRT = Core.Risch.LRT

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Derivative
open Core.Polynomial.Eval
open Core.Polynomial.Resultant
open Core.Risch.LRT

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(* ---------------------------------------------------------------- *)
(*  DELIVERABLE 1:                                                    *)
(*    R(c) = 0  <=>  deg( gcd(p - c*q', q) ) >= 1                     *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
let resultant_zero_iff_gcd (#t:Type) {| f: field t |}
  (p q: polynomial t) (c: t)
  : Lemma (requires deg q >= 1)
          (ensures poly_eval (lrt_resultant_raw p q) c = (zero <: t)
                   <==>
                   deg (poly_gcd (p -- SP.poly_scale c (poly_deriv q)) q) >= 1)
  = H.elim_equatable_laws t ();
    let q'  = poly_deriv q in
    let dq  = deg q in
    let dp  = (if deg p < 0 then 0 else deg p) in
    let dq' = (if deg q' < 0 then 0 else deg q') in
    let n   = (if dp > dq' then dp else dq') in
    let pp  : polynomial t = (p -- SP.poly_scale c q') in
    (* R(c) = res_x(p - c*q', q) *)
    LRT.lrt_resultant_specializes p q c;
    let rc  = poly_eval (lrt_resultant_raw p q) c in
    let res = RES.resultant n dq pp q in
    (* rc = res  (unconditional, from specializes).  Transport rc=0 <=> res=0. *)
    let e_fwd () : Lemma (requires rc = (zero <: t)) (ensures res = (zero <: t))
      = symmetry rc res; transitivity res rc (zero <: t) in
    let e_bwd () : Lemma (requires res = (zero <: t)) (ensures rc = (zero <: t))
      = transitivity rc res (zero <: t) in
    FStar.Classical.move_requires e_fwd ();
    FStar.Classical.move_requires e_bwd ();
    (* length bounds:  deg pp < n+1  =>  L.length pp <= n+1 *)
    LRT.poly_scale_deg_le c q' (n ++ 1);
    poly_sub_degree_bound p (SP.poly_scale c q') (n ++ 1);
    if deg pp >= 0 then
      (* res = zero <=> deg gcd >= 1 *)
      RES.resultant_vanishing_iff n dq pp q
    else begin
      (* pp == [] : res = zero AND deg gcd = deg q >= 1, so both sides hold *)
      deg_neg_one_iff_zero pp;
      RES.gcd_deg_when_pp_zero pp q;
      RES.resultant_zero_when_p_all_zero n dq pp q
    end
#pop-options

(* ---------------------------------------------------------------- *)
(*  Bridge: the LRT log-argument subtrahend  embed_const c * q'  and  *)
(*  poly_scale c q'  are DEFINITIONALLY equal, since                  *)
(*    c @ poly_zero  =  (if c=0 then [] else [c])  =  embed_const c.  *)
(* ---------------------------------------------------------------- *)

let scale_eq_embed_mul (#t:Type) {| f: field t |}
  (c: t) (q': polynomial t)
  : Lemma (SP.poly_scale c q' == LRT.embed_const c * q')
  = assert (SP.poly_scale c q' == LRT.embed_const c * q')
      by (T.norm [delta_only [`%SP.poly_scale; `%LRT.embed_const]; iota; primops; zeta];
          T.trefl ())

(* ---------------------------------------------------------------- *)
(*  DELIVERABLE 2:  residue predicate and the equivalence.           *)
(* ---------------------------------------------------------------- *)

(* lrt_log_argument is (definitionally) the gcd of (p - embed_const c * q') and q. *)
let lrt_log_arg_reveal (#t:Type) {| f: field t |}
  (p q q': polynomial t) (c: t)
  : Lemma (requires deg q >= 0)
          (ensures LRT.lrt_log_argument p q q' c
                   == poly_gcd (p -- (LRT.embed_const c * q')) q)
  = ()

(* c is a residue of p/q iff its RT log-argument gcd is nonconstant. *)
let is_residue (#t:Type) {| f: field t |}
  (p: polynomial t) (q: polynomial t{deg q >= 0}) (c: t) : prop
  = deg (LRT.lrt_log_argument p q (poly_deriv q) c) >= 1

let is_residue_reveal (#t:Type) {| f: field t |}
  (p: polynomial t) (q: polynomial t{deg q >= 0}) (c: t)
  : Lemma (is_residue p q c
           == (b2t (deg (LRT.lrt_log_argument p q (poly_deriv q) c) >= 1)))
  = ()

#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
let residue_iff_resultant_root (#t:Type) {| f: field t |}
  (p: polynomial t) (q: polynomial t{deg q >= 0}) (c: t)
  : Lemma (requires deg q >= 1)
          (ensures is_residue p q c
                   <==>
                   poly_eval (lrt_resultant_raw p q) c = (zero <: t))
  = let q' = poly_deriv q in
    is_residue_reveal p q c;                (* is_residue = deg(lrt_log_argument..) >= 1 *)
    lrt_log_arg_reveal p q q' c;            (* lrt_log_argument = gcd(p - embed c*q') q *)
    scale_eq_embed_mul c q';                (* poly_scale c q' == embed c * q' *)
    (* congruence: deg(gcd(p - poly_scale c q') q) == deg(gcd(p - embed c*q') q) *)
    resultant_zero_iff_gcd p q c            (* R=0 <=> deg(gcd(p - poly_scale c q') q) >= 1 *)
#pop-options
