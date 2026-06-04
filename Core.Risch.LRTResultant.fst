module Core.Risch.LRTResultant

(* ================================================================ *)
(*  Rothstein-Trager resultant specialization (plan §5.1.b, final     *)
(*  application of det_eval):                                         *)
(*    R(c) = poly_eval (lrt_resultant_raw p q) c = res_x(p-c*q', q).  *)
(*                                                                   *)
(*  R = resultant over k[z] of (p - z*q') and q (LRT).  Specializing  *)
(*  z := c is poly_eval at c; det_eval pushes it through det, and     *)
(*  the Sylvester ENTRIES specialize coefficient-wise:                *)
(*    poly_eval (embed_const (coeff q i)) c          = coeff q i      *)
(*    poly_eval (p_minus_z_qprime_coeff p q' i) c    = coeff p i      *)
(*                                              - c * coeff q' i.     *)
(*  These entry lemmas are the content here; the full assembly        *)
(*  (eval_matrix (sylvester ...) c = sylvester (p-c*q') q via         *)
(*  det_pointwise_eq, then DetEval.resultant_eval) follows.           *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module LRT = Core.Risch.LRT
module RT  = Core.Polynomial.Root
module SP  = Core.Polynomial.Split
module SYL = Core.Matrix.Sylvester
module DET = Core.Matrix.Determinant
module RES = Core.Matrix.Resultant
module DE  = Core.Matrix.DetEval

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Div
open Core.Polynomial.Derivative
open Core.FinSum

#set-options "--fuel 2 --ifuel 2 --z3rlimit 60"

(* Evaluating the constant embedding gives the constant back. *)
let embed_const_eval (#t:Type) {| f: field t |} (c0 c: t)
  : Lemma (poly_eval #t #(cr_of_id t #(id_of_f t)) (LRT.embed_const #t #(cr_of_id t #(id_of_f t)) c0) c = c0)
  = let cr = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    assert (LRT.embed_const #t #cr c0
            == (if c0 = (zero <: t) then (poly_zero #t) else ([c0] <: polynomial t)))
      by (FStar.Tactics.norm [delta_only [`%LRT.embed_const]; primops]; FStar.Tactics.trefl ());
    if c0 = (zero <: t) then begin
      eval_zero #t #cr c;                   (* eval poly_zero c = zero *)
      symmetry c0 (zero <: t)
    end else
      RT.eval_singleton #t #f c0 c          (* poly_eval [c0] c = c0 *)

(* deg-1 evaluation:  poly_eval [a; b] c = a + b*c   (b<>0 so [a;b] is trimmed).
   Mirrors Core.Polynomial.Root.eval_linear (which is this with a=neg a0, b=one). *)
let eval_deg1 (#t:Type) {| f: field t |} (a b c: t)
  : Lemma (requires not (b = (zero <: t)))
          (ensures  poly_eval ([a; b] <: polynomial t) c = (a + b * c))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let la : polynomial t = [a; b] in
    let g = eval_term la c in
    sum_range_unfold_left g 0 2;                 (* sum02 = g0 + sum12 *)
    sum_range_unfold_left g 1 2;                 (* sum12 = g1 + sum22 *)
    sum_range_empty g 2 2;                        (* sum22 = zero *)
    H.x_mul_one a;
    H.x_mul_one c;                               (* c * one = c *)
    reflexivity (b <: t);
    mul_congruence b (c * one) b c;              (* b*(c*one) = b*c  (== g1 = b*c) *)
    assert (cpow c 1 == c * one);
    assert (g 0 == a * one);
    assert (g 1 == b * (c * one));
    assert (g 1 = b * c);
    assert (g 0 = a);
    H.x_plus_zero (g 1);
    add_congruence (g 1) (sum_range g 2 2) (g 1) (zero <: t);
    transitivity (sum_range g 1 2) (g 1 + sum_range g 2 2) (g 1 + (zero <: t));
    transitivity (sum_range g 1 2) (g 1 + (zero <: t)) (g 1);
    transitivity (sum_range g 1 2) (g 1) (b * c);
    add_congruence (g 0) (sum_range g 1 2) a (b * c);
    transitivity (sum_range g 0 2) (g 0 + sum_range g 1 2) (a + b * c)

(* Evaluating the i-th k[z]-coefficient of (p - z*q') at z=c:
   poly_eval (p_minus_z_qprime_coeff p q' i) c = coeff p i + neg (c * coeff q' i). *)
#push-options "--z3rlimit 100"
let pzq_coeff_eval (#t:Type) {| f: field t |} (p q' : polynomial t) (i: nat) (c: t)
  : Lemma (poly_eval (LRT.p_minus_z_qprime_coeff p q' i) c
           = coeff p i + neg (c * coeff q' i))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pi : t = coeff p i in
    let qi : t = coeff q' i in
    let neg_qi : t = neg qi in
    let m : polynomial t = LRT.p_minus_z_qprime_coeff p q' i in
    if neg_qi = (zero <: t) then begin
      (* Case A: m == embed_const pi; poly_eval m c = pi *)
      assert (m == LRT.embed_const pi);
      embed_const_eval pi c;
      assert (poly_eval m c = pi);
      H.zero_of_neg qi;                        (* qi = zero *)
      H.x_mul_zero c;                          (* c * zero = zero *)
      mul_congruence c qi c (zero <: t);       (* c*qi = c*zero *)
      transitivity (c * qi) (c * (zero <: t)) (zero <: t);  (* c*qi = zero *)
      neg_congruence (c * qi) (zero <: t);     (* neg(c*qi) = neg zero *)
      H.neg_zero #t ();                        (* zero = neg zero *)
      symmetry (zero <: t) (neg (zero <: t));  (* neg zero = zero *)
      transitivity (neg (c * qi)) (neg (zero <: t)) (zero <: t);  (* neg(c*qi) = zero *)
      H.x_plus_zero pi;                        (* pi + zero = pi *)
      add_congruence pi (neg (c * qi)) pi (zero <: t);   (* pi+neg(c*qi) = pi+zero *)
      transitivity (pi + neg (c * qi)) (pi + (zero <: t)) pi;  (* pi+neg(c*qi) = pi *)
      symmetry (pi + neg (c * qi)) pi;          (* pi = pi+neg(c*qi) *)
      transitivity (poly_eval m c) pi (pi + neg (c * qi))
    end else begin
      (* common conversion:  neg_qi * c = neg (c * qi) *)
      H.neg_mul_l qi c;                        (* (neg qi)*c = neg(qi*c) *)
      mul_commutativity qi c;                  (* qi*c = c*qi *)
      neg_congruence (qi * c) (c * qi);        (* neg(qi*c) = neg(c*qi) *)
      transitivity (neg_qi * c) (neg (qi * c)) (neg (c * qi));  (* neg_qi*c = neg(c*qi) *)
      if pi = (zero <: t) then begin
        (* Case B: m == zero @ (embed_const neg_qi) == [zero; neg_qi] *)
        assert (LRT.embed_const neg_qi
                == (if neg_qi = (zero <: t) then (poly_zero #t) else ([neg_qi] <: polynomial t)))
          by (FStar.Tactics.norm [delta_only [`%LRT.embed_const]; primops];
              FStar.Tactics.trefl ());
        assert (LRT.embed_const neg_qi == ([neg_qi] <: polynomial t));
        assert (m == ((zero <: t) @ (LRT.embed_const neg_qi)));
        assert (((zero <: t) @ ([neg_qi] <: polynomial t)) == ([(zero <: t); neg_qi] <: polynomial t));
        assert (m == ([(zero <: t); neg_qi] <: polynomial t));
        eval_deg1 (zero <: t) neg_qi c;        (* poly_eval [zero;neg_qi] c = zero + neg_qi*c *)
        assert (poly_eval m c = (zero <: t) + neg_qi * c);
        symmetry pi (zero <: t);               (* zero = pi *)
        add_congruence (zero <: t) (neg_qi * c) pi (neg (c * qi));  (* zero+neg_qi*c = pi+neg(c*qi) *)
        transitivity (poly_eval m c) ((zero <: t) + neg_qi * c) (pi + neg (c * qi))
      end else begin
        (* Case C: m == [pi; neg_qi] *)
        assert (m == ([pi; neg_qi] <: polynomial t));
        eval_deg1 pi neg_qi c;                 (* poly_eval [pi;neg_qi] c = pi + neg_qi*c *)
        assert (poly_eval m c = pi + neg_qi * c);
        add_congruence pi (neg_qi * c) pi (neg (c * qi));  (* pi+neg_qi*c = pi+neg(c*qi) *)
        transitivity (poly_eval m c) (pi + neg_qi * c) (pi + neg (c * qi))
      end
    end
#pop-options

(* coeff of (p - c*q') at i, with c*q' = poly_scale c q'.  Matches pzq_coeff_eval's RHS. *)
let sub_scale_coeff (#t:Type) {| f: field t |} (p q' : polynomial t) (c: t) (i: nat)
  : Lemma (coeff (poly_sub p (SP.poly_scale c q')) i = coeff p i + neg (c * coeff q' i))
  = H.elim_equatable_laws t ();
    poly_sub_coeff p (SP.poly_scale c q') i;     (* coeff(p - s) i = coeff p i + neg(coeff s i) *)
    poly_mul_singleton_coeff c q' i;             (* coeff(poly_scale c q') i = c * coeff q' i *)
    neg_congruence (coeff (SP.poly_scale c q') i) (c * coeff q' i);
    reflexivity (coeff p i);
    add_congruence (coeff p i) (neg (coeff (SP.poly_scale c q') i))
                   (coeff p i) (neg (c * coeff q' i));
    transitivity (coeff (poly_sub p (SP.poly_scale c q')) i)
                 (coeff p i + neg (coeff (SP.poly_scale c q') i))
                 (coeff p i + neg (c * coeff q' i))

(* ================================================================ *)
(*  Per-entry evaluation of the Sylvester inputs (q_emb / pzq).      *)
(* ================================================================ *)

(* generic map index/length helpers *)
let rec index_map (#a #b:Type) (g: a -> b) (l: list a) (k:nat)
  : Lemma (requires k < L.length l)
          (ensures L.length (L.map g l) == L.length l /\
                   L.index (L.map g l) k == g (L.index l k))
          (decreases l)
  = match l with
    | [] -> ()
    | x :: xs -> if k = 0 then () else index_map g xs (k - 1)

let rec map_length (#a #b:Type) (g: a -> b) (l: list a)
  : Lemma (ensures L.length (L.map g l) == L.length l) (decreases l)
  = match l with
    | [] -> ()
    | _ :: xs -> map_length g xs

let embed_const_zero_eq (#t:Type) {| cr: commutative_ring t |} (c: t)
  : Lemma (requires c = (zero <: t)) (ensures LRT.embed_const c == (poly_zero #t))
  = ()

(* the canonical commutative_ring (polynomial t) used by lrt_resultant_raw *)
unfold let crp (#t:Type) (f: field t) : commutative_ring (polynomial t)
  = cr_of_id (polynomial t) #((polynomial_integral_domain_instance #t #(id_of_f t)).pid)

(* coeff of the embedded denominator q_emb = trim (embed_poly q)  (= is poly_eq). *)
let coeff_qemb_eq (#t:Type) {| f: field t |} (q: polynomial t) (k: nat)
  : Lemma (eq #(polynomial t) #((crp f).cr_r.r_add.acg_eq)
             (coeff #(polynomial t) #(crp f)
                (trim #(polynomial t) #(crp f) (LRT.embed_poly q)) k)
             (LRT.embed_const (coeff q k)))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws (polynomial t) #((crp f).cr_r.r_add.acg_eq) ();
    coeff_trim #(polynomial t) #(crp f) (LRT.embed_poly q) k;
    assert (LRT.embed_poly q == L.map (fun (c:t) -> LRT.embed_const #t #cr c) q);
    map_length (fun (c:t) -> LRT.embed_const #t #cr c) q;
    if k < L.length q then begin
      index_map (fun (c:t) -> LRT.embed_const #t #cr c) q k;
      assert (coeff q k == L.index q k)
    end else begin
      assert (coeff q k == (zero <: t));
      reflexivity (zero <: t);
      embed_const_zero_eq #t #cr (coeff q k)
    end

(* eval of the q-block entry: poly_eval (coeff q_emb k) c = coeff q k. *)
let qemb_entry_eval (#t:Type) {| f: field t |} (q: polynomial t) (k: nat) (c: t)
  : Lemma (poly_eval (coeff #(polynomial t) #(crp f)
                        (trim #(polynomial t) #(crp f) (LRT.embed_poly q)) k) c
           = coeff q k)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let qe = coeff #(polynomial t) #(crp f) (trim #(polynomial t) #(crp f) (LRT.embed_poly q)) k in
    coeff_qemb_eq #t #f q k;
    eval_congruence #t #cr qe (LRT.embed_const (coeff q k)) c;
    embed_const_eval (coeff q k) c;
    transitivity (poly_eval qe c) (poly_eval (LRT.embed_const (coeff q k)) c) (coeff q k)

(* coeff of the trimmed (p - z*q') builder = the k-th z-coefficient, for k <= n. *)
let coeff_pzq_eq (#t:Type) {| f: field t |} (p q': polynomial t) (n: nat) (k: nat)
  : Lemma (requires k <= n)
          (ensures eq #(polynomial t) #((crp f).cr_r.r_add.acg_eq)
                     (coeff #(polynomial t) #(crp f)
                        (trim #(polynomial t) #(crp f)
                           (LRT.build_p_minus_z_qprime p q' (Prims.op_Addition n 1))) k)
                     (LRT.p_minus_z_qprime_coeff p q' k))
  = H.elim_equatable_laws (polynomial t) #((crp f).cr_r.r_add.acg_eq) ();
    LRT.build_aux_length p q' 0 (Prims.op_Addition n 1);
    LRT.build_aux_index  p q' 0 (Prims.op_Addition n 1) k;
    coeff_trim #(polynomial t) #(crp f)
      (LRT.build_p_minus_z_qprime p q' (Prims.op_Addition n 1)) k

(* eval of the p-block entry: poly_eval (coeff pzq k) c = coeff (p - c*q') k, for k <= n. *)
let pzq_entry_eval (#t:Type) {| f: field t |} (p q': polynomial t) (n: nat) (k: nat) (c: t)
  : Lemma (requires k <= n)
          (ensures poly_eval (coeff #(polynomial t) #(crp f)
                     (trim #(polynomial t) #(crp f)
                        (LRT.build_p_minus_z_qprime p q' (Prims.op_Addition n 1))) k) c
                   = coeff (poly_sub p (SP.poly_scale c q')) k)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let pz = coeff #(polynomial t) #(crp f)
               (trim #(polynomial t) #(crp f)
                  (LRT.build_p_minus_z_qprime p q' (Prims.op_Addition n 1))) k in
    coeff_pzq_eq #t #f p q' n k;
    eval_congruence #t #cr pz (LRT.p_minus_z_qprime_coeff p q' k) c;
    pzq_coeff_eval #t #f p q' k c;
    sub_scale_coeff #t #f p q' c k;
    symmetry (coeff (poly_sub p (SP.poly_scale c q')) k) (coeff p k + neg (c * coeff q' k));
    transitivity (poly_eval pz c) (poly_eval (LRT.p_minus_z_qprime_coeff p q' k) c)
                 (coeff p k + neg (c * coeff q' k));
    transitivity (poly_eval pz c) (coeff p k + neg (c * coeff q' k))
                 (coeff (poly_sub p (SP.poly_scale c q')) k)

(* ================================================================ *)
(*  Sylvester-entry specialization + the RT resultant specialization. *)
(* ================================================================ *)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let eval_sylvester_entry (#t:Type) {| f: field t |} (p q' q: polynomial t) (n dq: nat) (c: t)
  (i j: Core.Permutation.fin (Prims.op_Addition n dq))
  : Lemma (requires dq >= 1 /\
                    L.length (trim #(polynomial t) #(crp f)
                       (LRT.build_p_minus_z_qprime p q' (Prims.op_Addition n 1))) <= Prims.op_Addition n 1 /\
                    L.length (poly_sub p (SP.poly_scale c q')) <= Prims.op_Addition n 1 /\
                    L.length (trim #(polynomial t) #(crp f) (LRT.embed_poly q)) <= Prims.op_Addition dq 1 /\
                    L.length q <= Prims.op_Addition dq 1)
          (ensures
             poly_eval #t #(cr_of_id t #(id_of_f t))
               (SYL.sylvester_matrix #(polynomial t) #(crp f) n dq
                  (trim #(polynomial t) #(crp f) (LRT.build_p_minus_z_qprime p q' (Prims.op_Addition n 1)))
                  (trim #(polynomial t) #(crp f) (LRT.embed_poly q)) i j) c
             = SYL.sylvester_matrix #t #(cr_of_id t #(id_of_f t)) n dq
                  (poly_sub p (SP.poly_scale c q')) q i j)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let pzq : polynomial (polynomial t) =
      trim #(polynomial t) #(crp f) (LRT.build_p_minus_z_qprime p q' (Prims.op_Addition n 1)) in
    let qe  : polynomial (polynomial t) = trim #(polynomial t) #(crp f) (LRT.embed_poly q) in
    let pp  : polynomial t = poly_sub p (SP.poly_scale c q') in
    let mi : nat = i in
    let mj : nat = j in
    (* LHS matrix entry (polynomial t) and RHS matrix entry (t) *)
    let lhs_e : polynomial t = SYL.sylvester_matrix #(polynomial t) #(crp f) n dq pzq qe i j in
    let rhs_e : t            = SYL.sylvester_matrix #t #cr n dq pp q i j in
    if mi < dq then begin
      (* p-block *)
      if mj >= mi && mj <= mi + n then begin
        (* in range *)
        SYL.sylvester_p_block_in_range #(polynomial t) #(crp f) n dq pzq qe i j;
        SYL.sylvester_p_block_in_range #t #cr n dq pp q i j;
        let idx : nat = SYL.nat_sub (SYL.nat_add n mi) mj in
        (* lhs_e == coeff pzq idx, rhs_e == coeff pp idx *)
        assert (lhs_e == coeff #(polynomial t) #(crp f) pzq idx);
        assert (rhs_e == coeff #t #cr pp idx);
        pzq_entry_eval #t #f p q' n idx c;
        (* poly_eval (coeff pzq idx) c = coeff pp idx = rhs_e *)
        assert (poly_eval #t #cr lhs_e c = rhs_e)
      end else if mj > mi + n then begin
        (* right zero *)
        SYL.sylvester_p_block_right_zero #(polynomial t) #(crp f) n dq pzq qe i j;
        SYL.sylvester_p_block_right_zero #t #cr n dq pp q i j;
        assert (lhs_e == (poly_zero #t));
        eval_zero #t #cr c;
        assert (poly_eval #t #cr lhs_e c = (zero <: t));
        assert (rhs_e == (zero <: t))
      end else begin
        (* left zero: mj < mi *)
        SYL.sylvester_p_block_left_zero #(polynomial t) #(crp f) n dq pzq qe i j;
        SYL.sylvester_p_block_left_zero #t #cr n dq pp q i j;
        assert (lhs_e == (poly_zero #t));
        eval_zero #t #cr c;
        assert (poly_eval #t #cr lhs_e c = (zero <: t));
        assert (rhs_e == (zero <: t))
      end
    end else begin
      (* q-block: mi >= dq *)
      if mj <= mi then begin
        (* in range *)
        SYL.sylvester_q_block_in_range #(polynomial t) #(crp f) n dq pzq qe i j;
        SYL.sylvester_q_block_in_range #t #cr n dq pp q i j;
        let idx : nat = SYL.nat_sub mi mj in
        assert (lhs_e == coeff #(polynomial t) #(crp f) qe idx);
        assert (rhs_e == coeff #t #cr q idx);
        qemb_entry_eval #t #f q idx c;
        assert (poly_eval #t #cr lhs_e c = rhs_e)
      end else begin
        (* right zero: mj > mi *)
        SYL.sylvester_q_block_right_zero #(polynomial t) #(crp f) n dq pzq qe i j;
        SYL.sylvester_q_block_right_zero #t #cr n dq pp q i j;
        assert (lhs_e == (poly_zero #t));
        eval_zero #t #cr c;
        assert (poly_eval #t #cr lhs_e c = (zero <: t));
        assert (rhs_e == (zero <: t))
      end
    end
#pop-options

(* THE RT SPECIALIZATION (generic n,dq form):
   poly_eval (resultant pzq q_emb) c = resultant (p - c*q') q. *)
#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let resultant_eval_specialized (#t:Type) {| f: field t |} (p q' q: polynomial t) (n dq: nat) (c: t)
  : Lemma (requires dq >= 1 /\
                    L.length (trim #(polynomial t) #(crp f)
                       (LRT.build_p_minus_z_qprime p q' (Prims.op_Addition n 1))) <= Prims.op_Addition n 1 /\
                    L.length (poly_sub p (SP.poly_scale c q')) <= Prims.op_Addition n 1 /\
                    L.length (trim #(polynomial t) #(crp f) (LRT.embed_poly q)) <= Prims.op_Addition dq 1 /\
                    L.length q <= Prims.op_Addition dq 1)
          (ensures poly_eval #t #(cr_of_id t #(id_of_f t))
                     (RES.resultant #(polynomial t) #(crp f) n dq
                        (trim #(polynomial t) #(crp f) (LRT.build_p_minus_z_qprime p q' (Prims.op_Addition n 1)))
                        (trim #(polynomial t) #(crp f) (LRT.embed_poly q))) c
                   = RES.resultant #t #(cr_of_id t #(id_of_f t)) n dq (poly_sub p (SP.poly_scale c q')) q)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    assert (crp f == (polynomial_commutative_ring_instance #t #cr).pcr);
    let pzq = trim #(polynomial t) #(crp f) (LRT.build_p_minus_z_qprime p q' (Prims.op_Addition n 1)) in
    let qe  = trim #(polynomial t) #(crp f) (LRT.embed_poly q) in
    let pp  = poly_sub p (SP.poly_scale c q') in
    let m1 = DE.eval_matrix #t #cr (SYL.sylvester_matrix #(polynomial t) #(crp f) n dq pzq qe) c in
    let m2 = SYL.sylvester_matrix #t #cr n dq pp q in
    let aux (i j: Core.Permutation.fin (Prims.op_Addition n dq)) : Lemma (m1 i j = m2 i j)
      = eval_sylvester_entry #t #f p q' q n dq c i j in
    FStar.Classical.forall_intro_2 aux;
    DET.det_pointwise_eq #t #cr m1 m2;
    DE.resultant_eval #t #cr n dq pzq qe c;
    RES.resultant_unfold #t #cr n dq pp q;
    transitivity (poly_eval #t #cr (RES.resultant #(polynomial t) #(crp f) n dq pzq qe) c)
                 (DET.det #t #cr m1) (DET.det #t #cr m2);
    transitivity (poly_eval #t #cr (RES.resultant #(polynomial t) #(crp f) n dq pzq qe) c)
                 (DET.det #t #cr m2) (RES.resultant #t #cr n dq pp q)
#pop-options

(* ================================================================ *)
(*  Literal lrt_resultant_raw specialization (degree bounds + corollary). *)
(* ================================================================ *)
(* local: trim never lengthens *)
let rec trim_length_le (#t:Type) {| cr: commutative_ring t |} (cs: list t)
  : Lemma (ensures L.length (trim #t #cr cs) <= L.length cs) (decreases cs)
  = match cs with
    | [] -> ()
    | _ :: cs' -> trim_length_le #t #cr cs'

(* high coeffs of a scaled poly vanish *)
let coeff_zero_above_k_of_scale (#t:Type) {| f: field t |} (c: t) (qq: polynomial t) (k:nat) (i:nat)
  : Lemma (requires i >= k /\ (None? (poly_deg qq) \/ Some?.v (poly_deg qq) < k))
          (ensures coeff (SP.poly_scale c qq) i = (zero <: t))
  = H.elim_equatable_laws t ();
    coeff_above_degree qq i;                       (* coeff qq i = zero *)
    poly_mul_singleton_coeff c qq i;               (* coeff (poly_scale c qq) i = c * coeff qq i *)
    H.x_mul_zero c;                                (* c * zero = zero *)
    reflexivity c;
    mul_congruence c (coeff qq i) c (zero <: t);   (* c*coeff qq i = c*zero *)
    transitivity (coeff (SP.poly_scale c qq) i) (c * coeff qq i) (c * (zero <: t));
    transitivity (coeff (SP.poly_scale c qq) i) (c * (zero <: t)) (zero <: t)

(* deg(poly_scale c qq) < k  when deg qq < k  (mirrors poly_add_degree_bound) *)
let poly_scale_deg_le (#t:Type) {| f: field t |} (c: t) (qq: polynomial t) (k:nat)
  : Lemma (requires (None? (poly_deg qq) \/ Some?.v (poly_deg qq) < k))
          (ensures (None? (poly_deg (SP.poly_scale c qq)) \/
                    Some?.v (poly_deg (SP.poly_scale c qq)) < k))
  = match poly_deg (SP.poly_scale c qq) with
    | None   -> ()
    | Some d ->
        if d < k then ()
        else begin
          coeff_zero_above_k_of_scale #t #f c qq k d;   (* coeff (scale) d = zero *)
          leading_coeff_nonzero (SP.poly_scale c qq)    (* coeff (scale) d <> zero — contradiction *)
        end

(* the literal lrt_resultant_raw specialization *)
#push-options "--z3rlimit 150 --fuel 2 --ifuel 2"
let lrt_resultant_specializes (#t:Type) {| f: field t |} (p q: polynomial t) (c: t)
  : Lemma (requires Some? (poly_deg q) /\ Some?.v (poly_deg q) >= 1)
          (ensures (let q'  = poly_deriv #t #(cr_of_id t #(id_of_f t)) q in
                    let dq  = Some?.v (poly_deg q) in
                    let dp  = (match poly_deg p with | None -> 0 | Some d -> d) in
                    let dq' = (match poly_deg q' with | None -> 0 | Some d -> d) in
                    let n   = (if dp > dq' then dp else dq') in
                    poly_eval (LRT.lrt_resultant_raw p q) c
                    = RES.resultant #t #(cr_of_id t #(id_of_f t)) n dq
                        (poly_sub p (SP.poly_scale c q')) q))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let q'  = poly_deriv #t #cr q in
    let dq  = Some?.v (poly_deg q) in
    let dp  = (match poly_deg p with | None -> 0 | Some d -> d) in
    let dq' = (match poly_deg q' with | None -> 0 | Some d -> d) in
    let n   = (if dp > dq' then dp else dq') in
    LRT.build_aux_length p q' 0 (Prims.op_Addition n 1);
    trim_length_le #(polynomial t) #(crp f)
      (LRT.build_p_minus_z_qprime p q' (Prims.op_Addition n 1));      (* bound 1 *)
    map_length (fun (cc:t) -> LRT.embed_const #t #cr cc) q;
    trim_length_le #(polynomial t) #(crp f) (LRT.embed_poly q);       (* bounds 3,4 *)
    poly_scale_deg_le #t #f c q' (Prims.op_Addition n 1);            (* deg(scale) < n+1 *)
    poly_sub_degree_bound #t #cr p (SP.poly_scale c q') (Prims.op_Addition n 1);  (* bound 2 *)
    resultant_eval_specialized #t #f p q' q n dq c
#pop-options
