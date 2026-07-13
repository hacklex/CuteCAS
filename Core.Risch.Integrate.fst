module Core.Risch.Integrate

(* ================================================================ *)
(*  CAPSTONE — every rational function over a char-zero field has     *)
(*  an ELEMENTARY antiderivative (Liouville form: a rational part     *)
(*  plus a finite sum of logarithmic terms).                          *)
(*                                                                    *)
(*  Two theorems, whose conjunction is the statement                  *)
(*  "p/q is elementarily integrable for every q <> 0":                *)
(*                                                                    *)
(*   (1) `rational_integrable p q` :  p/q reduces to a rational part  *)
(*       plus proper fractions over squarefree denominators —         *)
(*         D(R)  (+)  Sigma_j (rem_j / d_j)  =  p / q,                 *)
(*       with each d_j squarefree of degree >= 1 and deg rem_j <      *)
(*       deg d_j  (`logspec_ok`).  Total for ALL p and ALL q <> 0     *)
(*       (constant denominators included).                            *)
(*                                                                    *)
(*   (2) `logspec_rt_integrable` :  each such proper squarefree piece *)
(*       rem_j / d_j IS elementarily integrable — its Rothstein-      *)
(*       Trager / RootSum logarithmic part has derivative rem_j / d_j *)
(*       over a splitting field (`rt_unconditionally_sound`, proven   *)
(*       unconditionally in RTUnconditional).                         *)
(*                                                                    *)
(*  Together: D(R) + Sigma_j (integrable logs) = p/q, i.e. every      *)
(*  rational function has an elementary antiderivative.               *)
(*                                                                    *)
(*  NO admit / assume / sorry.                                        *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module PA = Core.Risch.PolyAntideriv
module RI = Core.Risch.RationalIntegrate
module RU = Core.Risch.RTUnconditional

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.Derivative
open Core.Fractions
open Core.Fractions.Derivative
open Core.Risch.Hermite
open Core.Risch.RationalSound
open Core.Risch.RationalSplitField
open Core.Risch.RationalIntegrate

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ---------------------------------------------------------------- *)
(*  Elementary integrability of p/q:  a rational part R and a list   *)
(*  of PROPER squarefree log specs whose derivative-sum is p/q.      *)
(*  (Body identical to `RI.rational_reduces`'s conclusion.)          *)
(* ---------------------------------------------------------------- *)
let elem_integrable (#t:Type) {| f: field t |} (p q: polynomial t) : prop =
  is_nonzero q /\
  (exists (rr: rational_function f) (logspecs: list (RI.log_spec f)).
     (let id_p = polynomial_id #t #(id_of_f t) in
      let qn : (x:polynomial t{is_nonzero x}) = q in
      (fraction_add (rational_deriv rr)
                    (RI.frac_sum_list (L.map RI.log_frac logspecs)))
        = (Fraction #(polynomial t) #id_p p qn)) /\
     L.for_all RI.logspec_ok logspecs)

(* ---------------------------------------------------------------- *)
(*  Smart constructor (no destructuring): `elem_integrable` follows   *)
(*  from its body given whole (the existential is passed through).    *)
(* ---------------------------------------------------------------- *)
let mk_elem_integrable (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires
             is_nonzero q /\
             (exists (rr: rational_function f) (logspecs: list (RI.log_spec f)).
                (let id_p = polynomial_id #t #(id_of_f t) in
                 let qn : (x:polynomial t{is_nonzero x}) = q in
                 (fraction_add (rational_deriv rr)
                               (RI.frac_sum_list (L.map RI.log_frac logspecs)))
                   = (Fraction #(polynomial t) #id_p p qn)) /\
                L.for_all RI.logspec_ok logspecs))
          (ensures elem_integrable p q)
  = ()

(* Witness form: introduce `elem_integrable` from EXPLICIT witnesses. *)
let mk_elem_from_witness (#t:Type) {| f: field t |} (p q: polynomial t)
  (rr: rational_function f) (logspecs: list (RI.log_spec f))
  : Lemma (requires
             is_nonzero q /\
             (let id_p = polynomial_id #t #(id_of_f t) in
              let qn : (x:polynomial t{is_nonzero x}) = q in
              (fraction_add (rational_deriv rr)
                            (RI.frac_sum_list (L.map RI.log_frac logspecs)))
                = (Fraction #(polynomial t) #id_p p qn)) /\
             L.for_all RI.logspec_ok logspecs)
          (ensures elem_integrable p q)
  = ()

(* When  p = quot * q  (exact division), the whole fraction p/q is the  *)
(* polynomial quot, i.e.  quot/1 = p/q.                                  *)
let frac_quot_whole (#t:Type) {| f: field t |}
  (quot p: polynomial t) (q: polynomial t{is_nonzero q})
  : Lemma (requires p = (quot * q))
          (ensures (poly_to_rational quot)
                     = (Fraction #(polynomial t) #(polynomial_id #t #(id_of_f t)) p q))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* cross-mult goal:  quot * q  =  one * p,  with p = quot * q. *)
    H.one_mul_x p;                                  (* one * p = p *)
    fraction_eq_reveal (poly_to_rational quot)
      (Fraction #(polynomial t) #(polynomial_id #t #(id_of_f t)) p q)

(* ---------------------------------------------------------------- *)
(*  Per-spec elementary integrability: a proper fraction over a       *)
(*  squarefree denom is RT-integrable (its RootSum log part has        *)
(*  derivative rem/d over a splitting field).  `logspec_ok` is        *)
(*  exactly `rt_unconditional`'s precondition.                        *)
(* ---------------------------------------------------------------- *)
let logspec_rt_integrable (#t:Type) {| f: field t |} (s: RI.log_spec f)
  : Lemma (requires RI.logspec_ok s)
          (ensures  RU.rt_unconditionally_sound (fst s) (snd s))
  = RU.rt_unconditional (fst s) (snd s)

(* ---------------------------------------------------------------- *)
(*  Non-constant denominator: the master reduction identity (A3).    *)
(* ---------------------------------------------------------------- *)
let rational_integrable_pos (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires char_zero f /\ is_nonzero q /\ deg q >= 1)
          (ensures  elem_integrable p q)
  = RI.rational_reduces p q;
    mk_elem_integrable p q

(* ---------------------------------------------------------------- *)
(*  Constant (degree-0) denominator: p/q is a polynomial; integrate  *)
(*  it (no log part).                                                 *)
(* ---------------------------------------------------------------- *)
let rational_integrable_const (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires char_zero f /\ is_nonzero q /\ deg q == 0)
          (ensures  elem_integrable p q)
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let qr = RI.divmod_qr p q in
    let quot : polynomial t = fst qr in
    let rem  : polynomial t = snd qr in
    (* p = quot*q + rem  and  deg rem < deg q = 0  =>  rem = poly_zero  =>  p = quot*q *)
    degree_none_poly_eq_zero rem;                        (* rem = poly_zero *)
    poly_add_congruence (quot * q) rem (quot * q) (poly_zero #t);
    poly_add_zero (quot * q);                            (* quot*q + poly_zero = quot*q *)
    poly_eq_transitivity p ((quot * q) + rem) (quot * q);
    (* now  p = quot * q *)
    let rr : rational_function f = poly_to_rational (PA.antideriv quot) in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    poly_part_correct quot;                              (* D rr = poly_to_rational quot *)
    frac_quot_whole quot p q;                            (* poly_to_rational quot = Fraction p q *)
    RI.frac_add_zero_r (rational_deriv rr);              (* (D rr) (+) 0 = D rr *)
    mk_elem_from_witness p q rr []

(* ================================================================ *)
(*  CAPSTONE.  Every rational function p/q (q <> 0) over a char-zero  *)
(*  field is elementarily integrable.                                *)
(* ================================================================ *)
let rational_integrable (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires char_zero f /\ is_nonzero q)
          (ensures  elem_integrable p q)
  = if deg q >= 1 then rational_integrable_pos p q
    else rational_integrable_const p q
