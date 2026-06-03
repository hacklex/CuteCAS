module Core.Matrix.DetEval

(* ================================================================ *)
(*  DETERMINANT SPECIALIZATION (plan §5.1.b):                        *)
(*    poly_eval (at c) is a ring homomorphism polynomial t -> t      *)
(*    (#15), so it commutes with the determinant:                    *)
(*       poly_eval (det M) c  =  det (eval_matrix M c)               *)
(*    where (eval_matrix M c) i j = poly_eval (M i j) c.             *)
(*                                                                   *)
(*  This is the base for resultant specialization                    *)
(*    R(c) = res_x(p - c*q', q)  and the Rothstein-Trager criterion. *)
(*                                                                   *)
(*  Pieces (drilled below):                                          *)
(*    eval_sum_over_perms : eval commutes with sum_over_perms        *)
(*    perm_product_eval   : eval commutes with perm_product          *)
(*    leibniz_eval        : eval commutes with leibniz_term          *)
(*    det_eval            : eval commutes with det                   *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module ES = Core.Polynomial.EvalSum
module PS = Core.Permutation.Sum
module DET = Core.Matrix.Determinant
module RES = Core.Matrix.Resultant
module SYL = Core.Matrix.Sylvester
module T  = FStar.Tactics

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Eval
open Core.FinSum
open Core.Permutation
open Core.Permutation.Enum
open Core.Vector
open Core.Matrix

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* map fusion: map (eval . _) (map f l) = map (fun p -> eval (f p) c) l. *)
let rec map_eval_map (#t:Type) {| cr: commutative_ring t |} (#n:nat)
  (f: permutation n -> polynomial t) (c: t) (l: list (permutation n))
  : Lemma (ensures L.map (fun (q: polynomial t) -> poly_eval #t #cr q c) (L.map f l)
                   == L.map (fun (p: permutation n) -> poly_eval #t #cr (f p) c) l)
          (decreases l)
  = match l with
    | [] -> ()
    | x :: rest -> map_eval_map #t #cr #n f c rest

(* eval (sum_over_perms n f) = sum_over_perms n (eval . f). *)
let eval_sum_over_perms (#t:Type) {| cr: commutative_ring t |} (n: nat)
  (f: permutation n -> polynomial t) (c: t)
  : Lemma (poly_eval #t #cr
             (PS.sum_over_perms #(polynomial t) #(polynomial_acg cr) n f) c
           = PS.sum_over_perms #t #(cr.cr_r.r_add) n
               (fun (p: permutation n) -> poly_eval #t #cr (f p) c))
  = H.elim_equatable_laws t ();
    PS.sum_over_perms_reveal #(polynomial t) #(polynomial_acg cr) n f;
    PS.sum_over_perms_reveal #t #(cr.cr_r.r_add) n
      (fun (p: permutation n) -> poly_eval #t #cr (f p) c);
    ES.eval_sum_list #t #cr (L.map f (all_permutations n)) c;
    map_eval_map #t #cr #n f c (all_permutations n)

(* entrywise-evaluated matrix. *)
let eval_matrix (#t:Type) {| cr: commutative_ring t |} (#n:pos)
  (m: square_matrix (polynomial t) n) (c: t) : square_matrix t n
  = fun (i:fin n) (j:fin n) -> poly_eval #t #cr (m i j) c

(* eval (perm_product m p) = perm_product (eval_matrix m c) p.
   Uses the NAMED perm_entry (via perm_product_via) so both sides share a
   function symbol and eval_prod_range applies cleanly. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let perm_product_eval (#t:Type) {| cr: commutative_ring t |} (#n:pos)
  (m: square_matrix (polynomial t) n) (p: permutation n) (c: t)
  : Lemma (poly_eval #t #cr
             (DET.perm_product #(polynomial t)
                #((polynomial_commutative_ring_instance #t #cr).pcr) m p) c
           = DET.perm_product #t #cr (eval_matrix m c) p)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pr = (polynomial_commutative_ring_instance #t #cr).pcr.cr_r in
    let ev : nat -> t = (fun (i:nat) -> poly_eval #t #cr (DET.perm_entry m p i) c) in
    DET.perm_product_via #(polynomial t)
      #((polynomial_commutative_ring_instance #t #cr).pcr) m p;   (* perm_product m p == prod_range (perm_entry m p) 0 n *)
    DET.perm_product_via #t #cr (eval_matrix m c) p;              (* perm_product (evalM) p == prod_range (perm_entry (evalM) p) 0 n *)
    ES.eval_prod_range #t #cr (DET.perm_entry m p) c 0 n;         (* eval (prod_range (perm_entry m p)) = prod_range ev *)
    let h (i:nat{0 <= i /\ i < n}) : Lemma (ev i = DET.perm_entry #t #cr (eval_matrix m c) p i)
      = H.elim_equatable_laws t ();
        assert (DET.perm_entry m p i == m i (p.fwd i));
        assert (ev i == poly_eval #t #cr (m i (p.fwd i)) c);
        assert (DET.perm_entry #t #cr (eval_matrix m c) p i == poly_eval #t #cr (m i (p.fwd i)) c);
        reflexivity #t (poly_eval #t #cr (m i (p.fwd i)) c)
    in
    prod_range_congruence #t #(cr.cr_r) ev (DET.perm_entry #t #cr (eval_matrix m c) p) 0 n h;
    transitivity (poly_eval #t #cr (prod_range #(polynomial t) #pr (DET.perm_entry m p) 0 n) c)
                 (prod_range #t #(cr.cr_r) ev 0 n)
                 (prod_range #t #(cr.cr_r) (DET.perm_entry #t #cr (eval_matrix m c) p) 0 n)
#pop-options

(* eval (leibniz_term m p) = leibniz_term (eval_matrix m c) p. *)
#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let leibniz_eval (#t:Type) {| cr: commutative_ring t |} (#n:pos)
  (m: square_matrix (polynomial t) n) (p: permutation n) (c: t)
  : Lemma (poly_eval #t #cr
             (DET.leibniz_term #(polynomial t)
                #((polynomial_commutative_ring_instance #t #cr).pcr) m p) c
           = DET.leibniz_term #t #cr (eval_matrix m c) p)
  = H.elim_equatable_laws t ();
    perm_product_eval m p c;                                   (* eval(perm_product m p) c = perm_product (evalM) p *)
    if parity p then ()
    else begin
      let ppm = DET.perm_product #(polynomial t)
                  #((polynomial_commutative_ring_instance #t #cr).pcr) m p in
      eval_neg #t #cr ppm c;                                   (* eval(poly_neg ppm) c = neg (eval ppm c) *)
      neg_congruence #t #(cr.cr_r.r_add)
        (poly_eval #t #cr ppm c)
        (DET.perm_product #t #cr (eval_matrix m c) p);          (* neg (eval ppm c) = neg (perm_product (evalM) p) *)
      transitivity (poly_eval #t #cr (DET.leibniz_term #(polynomial t)
                       #((polynomial_commutative_ring_instance #t #cr).pcr) m p) c)
                   (neg #t #(cr.cr_r.r_add) (poly_eval #t #cr ppm c))
                   (neg #t #(cr.cr_r.r_add) (DET.perm_product #t #cr (eval_matrix m c) p))
    end
#pop-options

(* THE DETERMINANT SPECIALIZATION:  poly_eval (det m) c = det (eval_matrix m c). *)
#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let det_eval (#t:Type) {| cr: commutative_ring t |} (#n:pos)
  (m: square_matrix (polynomial t) n) (c: t)
  : Lemma (poly_eval #t #cr
             (DET.det #(polynomial t) #((polynomial_commutative_ring_instance #t #cr).pcr) m) c
           = DET.det #t #cr (eval_matrix m c))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    (* the poly add-group used by det's sum_over_perms is the canonical polynomial_acg *)
    assert (polynomial_acg cr == (polynomial_commutative_ring_instance #t #cr).pcr.cr_r.r_add);
    let lt = DET.leibniz_term #(polynomial t)
               #((polynomial_commutative_ring_instance #t #cr).pcr) m in
    let lhsf : permutation n -> t =
      (fun (p: permutation n) -> poly_eval #t #cr (lt p) c) in
    let lt' = DET.leibniz_term #t #cr (eval_matrix m c) in
    DET.det_unfold #(polynomial t)
      #((polynomial_commutative_ring_instance #t #cr).pcr) m;   (* det m == sum_over_perms n lt *)
    DET.det_unfold #t #cr (eval_matrix m c);                    (* det (evalM) == sum_over_perms n lt' *)
    eval_sum_over_perms #t #cr n lt c;                          (* eval (sum_over_perms n lt) = sum_over_perms n lhsf *)
    PS.sum_over_perms_congruence #t #(cr.cr_r.r_add) n lhsf lt'
      (fun (p: permutation n) -> leibniz_eval m p c);            (* sum_over_perms n lhsf = sum_over_perms n lt' *)
    transitivity (poly_eval #t #cr
                    (PS.sum_over_perms #(polynomial t) #(polynomial_acg cr) n lt) c)
                 (PS.sum_over_perms #t #(cr.cr_r.r_add) n lhsf)
                 (PS.sum_over_perms #t #(cr.cr_r.r_add) n lt')
#pop-options

(* RESULTANT SPECIALIZATION (det level):  evaluating the resultant of two
   k[z]-polynomials at z = c is the determinant of the entrywise-evaluated
   Sylvester matrix.  (Corollary of det_eval + resultant_unfold.)

   The remaining step to the RT criterion R(c) = res_x(p - c*q', q) is to
   show eval_matrix (sylvester_matrix P Q) c = sylvester_matrix (P@c) (Q@c)
   for P = build_p_minus_z_qprime p q' and Q = embed_poly q, i.e. that
   poly_eval (p_minus_z_qprime_coeff p q' i) c = coeff (p - c*q') i and
   poly_eval (embed_const (coeff q i)) c = coeff q i  (entry-by-entry,
   then det_pointwise_eq) — a bounded follow-up. *)
let resultant_eval (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (pp qq: polynomial (polynomial t)) (c: t)
  : Lemma (poly_eval #t #cr
             (RES.resultant #(polynomial t)
                #((polynomial_commutative_ring_instance #t #cr).pcr) m_deg n_deg pp qq) c
           = DET.det #t #cr
               (eval_matrix (SYL.sylvester_matrix #(polynomial t)
                  #((polynomial_commutative_ring_instance #t #cr).pcr) m_deg n_deg pp qq) c))
  = RES.resultant_unfold #(polynomial t)
      #((polynomial_commutative_ring_instance #t #cr).pcr) m_deg n_deg pp qq;
    det_eval #t #cr
      (SYL.sylvester_matrix #(polynomial t)
         #((polynomial_commutative_ring_instance #t #cr).pcr) m_deg n_deg pp qq) c
