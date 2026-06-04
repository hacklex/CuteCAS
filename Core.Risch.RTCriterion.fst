module Core.Risch.RTCriterion

(* ================================================================ *)
(*  Rothstein-Trager criterion (plan §5.1.c):                        *)
(*                                                                   *)
(*    poly_eval (lrt_resultant_raw p q) c = 0                        *)
(*      <==>                                                         *)
(*    deg (gcd (p - c*q') q) >= 1                                    *)
(*                                                                   *)
(*  Assembled from three already-proven lemmas:                      *)
(*    - LR.lrt_resultant_specializes : rewrites the LHS eval=0 to    *)
(*      resultant N DQ (p - c*q') q = 0.                             *)
(*    - RES.resultant_zero_of_common_divisor : forward (g|pp, g|q,   *)
(*      deg g>=1  ==>  resultant = 0).                               *)
(*    - RC.resultant_converse : backward (resultant = 0  ==>         *)
(*      deg(gcd pp q) >= 1).                                         *)
(*  + RES.resultant_zero_when_p_all_zero for the pp == [] subcase of *)
(*    the forward direction.                                         *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L   = FStar.List.Tot
module H   = Core.Algebra.Helpers
module LRT = Core.Risch.LRT
module LR  = Core.Risch.LRTResultant
module SP  = Core.Polynomial.Split
module RES = Core.Matrix.Resultant
module RC  = Core.Matrix.ResultantConverse
module GC  = Core.Polynomial.GCD

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Div
open Core.Polynomial.Derivative

#set-options "--fuel 2 --ifuel 2 --z3rlimit 60"

(* ---------------------------------------------------------------- *)
(*  Bounds shared by both directions: with the canonical N, DQ from  *)
(*  lrt_resultant_specializes, the pair (pp, q) satisfies the        *)
(*  length/degree bounds needed by the resultant lemmas.             *)
(* ---------------------------------------------------------------- *)

(* deg (p - c*q') < N+1, i.e. length pp <= N+1, with N the canonical max. *)
let pp_bound (#t:Type) {| f: field t |} (p q: polynomial t) (c: t)
  : Lemma (requires Some? (poly_deg q) /\ Some?.v (poly_deg q) >= 1)
          (ensures (let cr  = cr_of_id t #(id_of_f t) in
                    let q'  = poly_deriv #t #cr q in
                    let dp  = (match poly_deg p with | None -> 0 | Some d -> d) in
                    let dq' = (match poly_deg q' with | None -> 0 | Some d -> d) in
                    let n   = (if dp > dq' then dp else dq') in
                    let pp  = poly_sub p (SP.poly_scale c q') in
                    L.length pp <= Prims.op_Addition n 1))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let q'  = poly_deriv #t #cr q in
    let dp  = (match poly_deg p with | None -> 0 | Some d -> d) in
    let dq' = (match poly_deg q' with | None -> 0 | Some d -> d) in
    let n   = (if dp > dq' then dp else dq') in
    LR.poly_scale_deg_le #t #f c q' (Prims.op_Addition n 1);
    poly_sub_degree_bound #t #cr p (SP.poly_scale c q') (Prims.op_Addition n 1)

(* ---------------------------------------------------------------- *)
(*  Backward direction:                                              *)
(*    resultant N DQ pp q = 0  ==>  deg (gcd pp q) >= 1.             *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 100"
let rt_backward (#t:Type) {| f: field t |} (p q: polynomial t) (c: t)
  : Lemma (requires Some? (poly_deg q) /\ Some?.v (poly_deg q) >= 1)
          (ensures (let cr  = cr_of_id t #(id_of_f t) in
                    let q'  = poly_deriv #t #cr q in
                    let pp  = poly_sub p (SP.poly_scale c q') in
                    (poly_eval (LRT.lrt_resultant_raw p q) c = (zero <: t))
                    ==>
                    (Some? (poly_deg (GC.poly_gcd #t #f pp q)) /\
                     Some?.v (poly_deg (GC.poly_gcd #t #f pp q)) >= 1)))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let q'  = poly_deriv #t #cr q in
    let dq  = Some?.v (poly_deg q) in
    let dp  = (match poly_deg p with | None -> 0 | Some d -> d) in
    let dq' = (match poly_deg q' with | None -> 0 | Some d -> d) in
    let n   = (if dp > dq' then dp else dq') in
    let pp  = poly_sub p (SP.poly_scale c q') in
    let aux ()
      : Lemma (requires poly_eval (LRT.lrt_resultant_raw p q) c = (zero <: t))
              (ensures Some? (poly_deg (GC.poly_gcd #t #f pp q)) /\
                       Some?.v (poly_deg (GC.poly_gcd #t #f pp q)) >= 1)
      = let cr2 : commutative_ring t = cr_of_id t #(id_of_f t) in
        H.elim_equatable_laws t ();
        LR.lrt_resultant_specializes #t #f p q c;
        (* poly_eval(raw) c = resultant n dq pp q  and  poly_eval(raw) c = zero *)
        let r = RES.resultant #t #cr2 n dq pp q in
        symmetry (poly_eval (LRT.lrt_resultant_raw p q) c) r;  (* r = eval *)
        transitivity r (poly_eval (LRT.lrt_resultant_raw p q) c) (zero <: t); (* r = zero *)
        pp_bound #t #f p q c;            (* L.length pp <= n+1 *)
        RC.resultant_converse #t #f n dq pp q
    in
    FStar.Classical.move_requires aux ()
#pop-options

(* ---------------------------------------------------------------- *)
(*  Forward direction:                                              *)
(*    deg (gcd pp q) >= 1  ==>  resultant N DQ pp q = 0.            *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 100"
let rt_forward (#t:Type) {| f: field t |} (p q: polynomial t) (c: t)
  : Lemma (requires Some? (poly_deg q) /\ Some?.v (poly_deg q) >= 1)
          (ensures (let cr  = cr_of_id t #(id_of_f t) in
                    let q'  = poly_deriv #t #cr q in
                    let pp  = poly_sub p (SP.poly_scale c q') in
                    (Some? (poly_deg (GC.poly_gcd #t #f pp q)) /\
                     Some?.v (poly_deg (GC.poly_gcd #t #f pp q)) >= 1)
                    ==>
                    (poly_eval (LRT.lrt_resultant_raw p q) c = (zero <: t))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let q'  = poly_deriv #t #cr q in
    let dq  = Some?.v (poly_deg q) in
    let dp  = (match poly_deg p with | None -> 0 | Some d -> d) in
    let dq' = (match poly_deg q' with | None -> 0 | Some d -> d) in
    let n   = (if dp > dq' then dp else dq') in
    let pp  = poly_sub p (SP.poly_scale c q') in
    let aux ()
      : Lemma (requires Some? (poly_deg (GC.poly_gcd #t #f pp q)) /\
                        Some?.v (poly_deg (GC.poly_gcd #t #f pp q)) >= 1)
              (ensures poly_eval (LRT.lrt_resultant_raw p q) c = (zero <: t))
      = let cr2 : commutative_ring t = cr_of_id t #(id_of_f t) in
        H.elim_equatable_laws t ();
        LR.lrt_resultant_specializes #t #f p q c;   (* eval = resultant n dq pp q *)
        pp_bound #t #f p q c;                        (* L.length pp <= n+1 *)
        let r = RES.resultant #t #cr2 n dq pp q in
        if Some? (poly_deg pp) then begin
          let g = GC.poly_gcd #t #f pp q in
          GC.gcd_divides_left  #t #f pp q;           (* g | pp *)
          GC.gcd_divides_right #t #f pp q;           (* g | q *)
          RES.resultant_zero_of_common_divisor #t #f n dq pp q g  (* r = zero *)
        end else begin
          (* pp == [] : length 0, so deg None *)
          RES.resultant_zero_when_p_all_zero #t #cr2 n dq pp q     (* r = zero *)
        end;
        (* eval = r  and  r = zero  ==>  eval = zero *)
        transitivity (poly_eval (LRT.lrt_resultant_raw p q) c) r (zero <: t)
    in
    FStar.Classical.move_requires aux ()
#pop-options

(* ---------------------------------------------------------------- *)
(*  The Rothstein-Trager criterion (iff).                            *)
(* ---------------------------------------------------------------- *)

let rt_criterion (#t:Type) {| f: field t |} (p q: polynomial t) (c: t)
  : Lemma (requires Some? (poly_deg q) /\ Some?.v (poly_deg q) >= 1)
          (ensures (let cr = cr_of_id t #(id_of_f t) in
                    let q' = poly_deriv #t #cr q in
                    let pp = poly_sub p (SP.poly_scale c q') in
                    (poly_eval (LRT.lrt_resultant_raw p q) c = (zero <: t))
                    <==>
                    (Some? (poly_deg (GC.poly_gcd #t #f pp q)) /\
                     Some?.v (poly_deg (GC.poly_gcd #t #f pp q)) >= 1)))
  = rt_forward  #t #f p q c;
    rt_backward #t #f p q c
