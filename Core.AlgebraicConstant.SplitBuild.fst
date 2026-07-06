module Core.AlgebraicConstant.SplitBuild

(*
   §E — building the splitting-field certificate (E3).

   Stage 1 (this file, top half):
     - ext_embed_is_embedding : one tower level is a certified embedding
       (assembles the per-level P-facts from EmbedHom / EmbedTransport /
        EmbedEval into SplittingField.is_embedding);
     - splits_deg1 : the recursion base — a degree-1 polynomial splits over
       its own field (l = t, identity embedding, root = linear_root d).
   Stage 2 (below): the tower recursion build_splitting_field.
*)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module GC = Core.Polynomial.GCD

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Roots
open Core.Polynomial.Unique
open Core.Polynomial.Irreducible
open Core.Polynomial.SquareFree
open Core.Polynomial.LinearPeel
open Core.AlgebraicConstant
open Core.AlgebraicConstant.Root
open Core.AlgebraicConstant.Eval
open Core.AlgebraicConstant.EmbedHom
open Core.AlgebraicConstant.EmbedEval
open Core.AlgebraicConstant.EmbedTransport
open Core.AlgebraicConstant.EmbedSquareFree
open Core.AlgebraicConstant.PeelQuotient
open Core.AlgebraicConstant.ExtendStep
open Core.AlgebraicConstant.SplittingField

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------- *)
(*  One tower level is a certified embedding.                        *)
(* ---------------------------------------------------------------- *)

(* Named per-level pair (the repo's named-function discipline). *)
let ac_embed_fn (#t:Type) {| f: field t |} (r: polynomial t {proper_extension r})
  : t -> algebraic r
  = fun x -> ac_const #t #f #r x

unfold let ext_embed_fn (#t:Type) {| f: field t |} (r: polynomial t {proper_extension r})
  : polynomial t -> poly_over (algebraic r) #(algebraic_field r)
  = fun p -> ext_embed_poly #t #f #r p

#push-options "--z3rlimit 80 --split_queries always"
let ext_embed_is_embedding (#t:Type) {| f: field t |}
  (r: polynomial t {proper_extension r})
  : Lemma (is_embedding (algebraic r) #(algebraic_field r)
             (ac_embed_fn r) (ext_embed_fn r))
  = algebraic_eq_zero_pointwise r;         (* eq == ac_eq ; zero == ac_zero *)
    let e   = ac_embed_fn r in
    let emb = ext_embed_fn r in
    introduce forall (p q: polynomial t). emb (p + q) = emb p + emb q
      with ext_embed_poly_add #t #f #r p q;
    introduce forall (p q: polynomial t). emb (p * q) = emb p * emb q
      with ext_embed_poly_mul #t #f #r p q;
    introduce forall (a: t). emb (poly_linear a) = poly_linear (e a)
      with embed_linear #t #f #r a;
    introduce forall (p: polynomial t). deg (emb p) == deg p
      with embed_deg #t #f #r p;
    introduce forall (p: polynomial t) (a: t).
        poly_eval (emb p) (e a) = e (poly_eval p a)
      with embed_eval_transport #t #f #r p a;
    introduce forall (x: t). x <> zero ==> e x <> zero
      with introduce _ ==> _
      with hx. ac_const_nonzero #t #f #r x;
    introduce forall (p q: polynomial t). p = q ==> emb p = emb q
      with introduce _ ==> _
      with hpq. ext_embed_congr #t #f #r p q;
    introduce forall (x y: t). x = y ==> e x = e y
      with introduce _ ==> _
      with hxy. ac_const_congr #t #f #r x y;
    is_embedding_intro (algebraic r) #(algebraic_field r) e emb
#pop-options

(* ---------------------------------------------------------------- *)
(*  Base case: deg d == 1 splits over t itself.                      *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 80"
let splits_deg1 (#t:Type) {| f: field t |} (d: polynomial t)
  : Lemma (requires deg d == 1)
          (ensures  splits d)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let a : t = linear_root d in
    linear_root_is_root d;                       (* poly_eval d a = zero *)
    linear_factor_peel d a;                      (* exists q. d = (X-a)*q /\ deg q == 0 *)
    eliminate exists (q: polynomial t).
        (d = (poly_linear a) * q) /\ deg q == deg d - 1
      returns splits d
      with _.
      begin
        (* q is the constant poly_lc q, and poly_lc d = poly_lc q *)
        GC.degree_zero_is_singleton q;           (* q == [poly_lc q], lc <> zero *)
        poly_eq_lc d ((poly_linear a) * q);      (* lc d = lc ((X-a)*q) *)
        poly_lc_mul_linear a q;                  (* lc ((X-a)*q) = lc q *)
        (* q = poly_const (poly_lc q), coefficient-wise *)
        let cq : t = poly_lc q in
        let qc : polynomial t = poly_const cq in
        poly_eq_by_coeff q qc (fun (j:nat) ->
          if j = 0 then poly_const_coeff0 cq
          else poly_const_coeff_high cq j);
        (* chain d = (X-a)*q -> poly_const (lc d) * ((X-a) * one) *)
        poly_const_congr cq (poly_lc d);         (* qc = poly_const (lc d) *)
        (* (X-a)*q = (X-a)*const(lc d) *)
        mul_congruence (poly_linear a) q
                       (poly_linear a) (poly_const (poly_lc d));
        (* commute *)
        mul_commutativity (poly_linear a) (poly_const (poly_lc d));
        (* (X-a) = (X-a)*one *)
        H.x_mul_one (poly_linear a);
        mul_congruence (poly_const (poly_lc d)) (poly_linear a)
                       (poly_const (poly_lc d)) ((poly_linear a) * (poly_one #t));
        (* roots facts *)
        assert (all_distinct [a]);
        (* payload *)
        id_is_embedding #t #f ();
        assert (poly_prod_linears [a] == (poly_linear a) * (poly_one #t));
        splits_with_intro d t #f (id_map t) id_poly_map [a];
        splits_intro d t #f (id_map t) id_poly_map [a]
      end
#pop-options

(* ---------------------------------------------------------------- *)
(*  Lift, same-level case: d = (X-a)*q with q split at l.            *)
(*  (core carries the packed field as an instance binder)            *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 100 --split_queries always"
private let split_lift_linear_core (#t:Type) {| f: field t |}
  (d: polynomial t) (a: t) (q: polynomial t)
  (l: Type0) {| fl: field l |}
  (e: t -> l) (emb: polynomial t -> poly_over l #fl) (roots_q: list l)
  : Lemma (requires
            square_free d /\ deg d >= 2 /\
            (d = (poly_linear a) * q) /\ deg q == deg d - 1 /\
            splits_with q l #fl e emb roots_q)
          (ensures splits d)
  = splits_with_elim q l #fl e emb roots_q;
    is_embedding_elim l #fl e emb;
    H.elim_equatable_laws (polynomial l) ();
    H.trans_for_calc (polynomial l) ();
    H.elim_equatable_laws l ();
    H.trans_for_calc l ();
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    (* freshness at the base, transported up *)
    peel_preserves_freshness d q a;            (* not (q(a) = zero)      *)
    let rho : l = e a in
    assert (poly_eval (emb q) rho = e (poly_eval q a));   (* P6 *)
    assert (not (e (poly_eval q a) = zero));              (* P7 *)
    assert (not (poly_eval (emb q) rho = zero));
    let prodq : poly_over l #fl = poly_prod_linears roots_q in
    let cq    : l = e (poly_lc q) in
    fresh_root_all_distinct rho roots_q (emb q) cq;
    (* lc bookkeeping at t: lc d = lc q, then up via P8e *)
    poly_eq_lc d ((poly_linear a) * q);
    poly_lc_mul_linear a q;
    assert (poly_lc d = poly_lc q);
    assert (e (poly_lc q) = e (poly_lc d));               (* P8e + sym *)
    (* P5 assembly at l *)
    assert (emb d = emb ((poly_linear a) * q));           (* P8 *)
    assert (emb ((poly_linear a) * q) = emb (poly_linear a) * emb q);  (* P1 *)
    assert (emb (poly_linear a) = poly_linear rho);       (* P2 *)
    (* emb q = cst * prodq  is P5 of q *)
    let cst : poly_over l #fl = poly_const cq in
    mul_congruence (emb (poly_linear a)) (emb q)
                   (poly_linear rho) (cst * prodq);
    (* swap (X-rho) * (cst * prodq)  ->  cst * ((X-rho) * prodq) *)
    mul_associativity (poly_linear rho) cst prodq;
    mul_commutativity (poly_linear rho) cst;
    mul_congruence ((poly_linear rho) * cst) prodq
                   (cst * (poly_linear rho)) prodq;
    mul_associativity cst (poly_linear rho) prodq;
    (* product over the extended root list *)
    assert (poly_prod_linears (rho :: roots_q) ==
              (poly_linear rho) * prodq);
    (* rename the constant to e (lc d) *)
    poly_const_congr cq (e (poly_lc d));
    mul_congruence cst ((poly_linear rho) * prodq)
                   (poly_const (e (poly_lc d))) ((poly_linear rho) * prodq);
    (* roots facts *)
    assert (L.length (rho :: roots_q) == deg d);
    splits_with_intro d l #fl e emb (rho :: roots_q);
    splits_intro d l #fl e emb (rho :: roots_q)
#pop-options

(* ---------------------------------------------------------------- *)
(*  Lift, extension case: (ext_embed d) = (X-theta)*q' with q'       *)
(*  split at l over the middle level m = algebraic r.                *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 120 --split_queries always"
private let split_lift_extend_core (#t:Type) {| f: field t |}
  (r: polynomial t {proper_extension r})
  (d: polynomial t) (q': polynomial (algebraic r))
  (l: Type0) {| fl: field l |}
  (e': algebraic r -> l)
  (emb': poly_over (algebraic r) #(algebraic_field r) -> poly_over l #fl)
  (roots_q: list l)
  : Lemma (requires
            square_free d /\ deg d >= 2 /\ divides r d /\
            ((ext_embed_fn r d) = (poly_linear theta) * q') /\
            deg q' == deg d - 1 /\
            splits_with q' l #fl e' emb' roots_q)
          (ensures splits d)
  = splits_with_elim q' l #fl e' emb' roots_q;
    is_embedding_elim l #fl e' emb';
    ext_embed_is_embedding r;
    compose_is_embedding (algebraic r) #(algebraic_field r) l #fl
      (ac_embed_fn r) (ext_embed_fn r) e' emb';
    let e  : t -> l = compose_base (ac_embed_fn r) e' in
    let emb : polynomial t -> poly_over l #fl =
      compose_poly (algebraic r) #(algebraic_field r) l #fl
        (ext_embed_fn r) emb' in
    H.elim_equatable_laws (polynomial l) ();
    H.trans_for_calc (polynomial l) ();
    H.elim_equatable_laws l ();
    H.trans_for_calc l ();
    H.elim_equatable_laws (polynomial (algebraic r)) ();
    H.trans_for_calc (polynomial (algebraic r)) ();
    ac_elim_equatable_laws r;
    algebraic_eq_zero_pointwise r;
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let dm : poly_over (algebraic r) #(algebraic_field r) = ext_embed_fn r d in
    embed_deg #t #f #r d;                    (* deg dm == deg d *)
    ext_embed_square_free #t #f #r d;        (* square_free dm  *)
    (* freshness at the middle level *)
    peel_preserves_freshness dm q' (theta #t #f #r);
    let rho : l = e' (theta #t #f #r) in
    assert (poly_eval (emb' q') rho = e' (poly_eval q' (theta #t #f #r)));
    assert (not (e' (poly_eval q' (theta #t #f #r)) = zero));
    assert (not (poly_eval (emb' q') rho = zero));
    let prodq : poly_over l #fl = poly_prod_linears roots_q in
    let cql : l = e' (poly_lc q') in
    fresh_root_all_distinct rho roots_q (emb' q') cql;
    (* lc chain: lc dm = lc q' at m ; lc dm = ac_const (lc d) *)
    poly_eq_lc dm ((poly_linear (theta #t #f #r)) * q');
    poly_lc_mul_linear (theta #t #f #r) q';
    embed_lc #t #f #r d;                     (* lc dm = ac_const (lc d) *)
    assert (ac_const #t #f #r (poly_lc d) = poly_lc q');
    assert (e' (ac_const #t #f #r (poly_lc d)) = cql);   (* P8e' *)
    assert (e (poly_lc d) == e' (ac_const #t #f #r (poly_lc d)));
    (* P5 assembly at l *)
    assert (emb d == emb' dm);
    assert (emb' dm = emb' ((poly_linear (theta #t #f #r)) * q'));  (* P8' *)
    assert (emb' ((poly_linear (theta #t #f #r)) * q')
              = emb' (poly_linear (theta #t #f #r)) * emb' q');     (* P1' *)
    assert (emb' (poly_linear (theta #t #f #r)) = poly_linear rho); (* P2' *)
    mul_congruence (emb' (poly_linear (theta #t #f #r))) (emb' q')
                   (poly_linear rho) ((poly_const cql) * prodq);
    mul_associativity (poly_linear rho) (poly_const cql) prodq;
    mul_commutativity (poly_linear rho) (poly_const cql);
    mul_congruence ((poly_linear rho) * (poly_const cql)) prodq
                   ((poly_const cql) * (poly_linear rho)) prodq;
    mul_associativity (poly_const cql) (poly_linear rho) prodq;
    assert (poly_prod_linears (rho :: roots_q) ==
              (poly_linear rho) * prodq);
    poly_const_congr cql (e (poly_lc d));
    mul_congruence (poly_const cql) ((poly_linear rho) * prodq)
                   (poly_const (e (poly_lc d))) ((poly_linear rho) * prodq);
    assert (L.length (rho :: roots_q) == deg d);
    splits_with_intro d l #fl e emb (rho :: roots_q);
    splits_intro d l #fl e emb (rho :: roots_q)
#pop-options

(* ---------------------------------------------------------------- *)
(*  E3 — the tower recursion.                                        *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 80"
let rec build_splitting_field (#t:Type) {| f: field t |}
  (d: polynomial t)
  : Lemma (requires deg d >= 1 /\ square_free d)
          (ensures  splits d)
          (decreases (deg d))
  = if deg d = 1 then splits_deg1 d
    else begin
      irreducible_factor_exists d;
      eliminate exists (r0: polynomial t). poly_irreducible r0 /\ divides r0 d
        returns splits d
        with _.
        begin
          if deg r0 = 1 then begin
            (* SAME-LEVEL: the factor's root is already in t *)
            let a : t = linear_root r0 in
            linear_root_is_root r0;
            root_of_divisor r0 d a;             (* poly_eval d a = zero *)
            linear_factor_peel d a;
            eliminate exists (q: polynomial t).
                (d = (poly_linear a) * q) /\ deg q == deg d - 1
              returns splits d
              with _.
              begin
                H.elim_equatable_laws (polynomial t) ();
                H.trans_for_calc (polynomial t) ();
                (* q | d, so q is squarefree *)
                mul_commutativity (poly_linear a) q;
                divides_intro q d (poly_linear a);
                divisor_of_square_free q d;
                build_splitting_field q;         (* IH: deg q = deg d - 1 >= 1 *)
                splits_elim q;
                eliminate exists (l: Type0) (fl: field l)
                    (e: t -> l) (emb: polynomial t -> poly_over l #fl)
                    (roots_q: list l).
                    splits_with q l #fl e emb roots_q
                  returns splits d
                  with _. split_lift_linear_core d a q l #fl e emb roots_q
              end
          end
          else begin
            (* EXTENSION: deg r0 >= 2, adjoin a root *)
            extend_gains_linear_factor r0 d;
            eliminate exists (q': polynomial (algebraic r0)).
                ((embed_poly r0 d) = (poly_linear theta * q')) /\
                (deg (embed_poly r0 d) >= 0 ==>
                   deg q' >= 0 /\ deg q' < deg (embed_poly r0 d))
              returns splits d
              with _.
              begin
                H.elim_equatable_laws (polynomial (algebraic r0)) ();
                H.trans_for_calc (polynomial (algebraic r0)) ();
                embed_deg #t #f #r0 d;           (* deg (ext_embed d) == deg d *)
                (* exact degree drop: deg q' == deg d - 1 *)
                deg_mul (poly_linear (theta #t #f #r0)) q';
                poly_linear_deg (theta #t #f #r0);
                degree_well_defined (ext_embed_fn r0 d)
                  ((poly_linear (theta #t #f #r0)) * q');
                assert (deg q' == deg d - 1);
                (* q' | ext_embed d, squarefree transport *)
                ext_embed_square_free #t #f #r0 d;
                mul_commutativity (poly_linear (theta #t #f #r0)) q';
                divides_intro q' (ext_embed_fn r0 d)
                  (poly_linear (theta #t #f #r0));
                divisor_of_square_free q' (ext_embed_fn r0 d);
                build_splitting_field q';                     (* IH *)
                splits_elim q';
                eliminate exists (l: Type0) (fl: field l)
                    (e': algebraic r0 -> l)
                    (emb': poly_over (algebraic r0) #(algebraic_field r0)
                             -> poly_over l #fl)
                    (roots_q: list l).
                    splits_with q' l #fl e' emb' roots_q
                  returns splits d
                  with _. split_lift_extend_core r0 d q' l #fl e' emb' roots_q
              end
          end
        end
    end
#pop-options
