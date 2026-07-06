module Core.Polynomial.LagrangeDenomQ

(* ================================================================ *)
(*  §D bound step (c1): the INTEGER Lagrange denominator              *)
(*    int_prod_sub roots c = prod_{a in roots} (c - a)                *)
(*  its ℚ-embedding (embed pushes through eval_prod_sub on the        *)
(*  mapped roots), the |·| >= 1 bound for distinct nodes, and the     *)
(*  embedding of the field-level `lagrange_denom` over the mapped     *)
(*  node list.                                                        *)
(*                                                                   *)
(*  `eval_prod_sub`/`lagrange_denom` (Core.Polynomial.Roots/.Lagrange)*)
(*  are field-only.  There is no `field int`, so the integer analogue *)
(*  `int_prod_sub` is defined with primitive integer arithmetic       *)
(*  (= `int_cr`'s neg/+/* up to defeq), letting the `iabs` reasoning   *)
(*  and the embed bridges (`embed_const_neg`, `embed_zq_const_add`,    *)
(*  `embed_zq_const_mul`) both apply cleanly.                          *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module ML = FStar.Math.Lemmas
module LB = Core.Modular.LagrangeBound

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Roots
open Core.Polynomial.Lagrange
open Core.Fractions
open Core.Polynomial.EmbedQ
open Core.Polynomial.EmbedQProd

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  1. The integer scalar product  prod_{a in roots} (c - a).         *)
(*     Defined with primitive integer arithmetic so the `iabs`        *)
(*     reasoning is direct; equals `int_cr`'s neg/+/* up to defeq.     *)
(* ================================================================ *)

let rec int_prod_sub (roots: list int) (c: int) : Tot int (decreases roots)
  = match roots with
    | []        -> 1
    | a :: rest -> Prims.op_Star ((Prims.op_Minus a) ++ c)
                                 (int_prod_sub rest c)

(* ================================================================ *)
(*  Local re-derivation of  embed_zq_const 1 = crq.one  (EmbedQ's is  *)
(*  private).                                                         *)
(* ================================================================ *)

private let embed_const_one_loc (_:unit)
  : Lemma ((embed_zq_const 1) = (one <: qq))
  = let e1 = embed_zq_const 1 in
    let o  = (one <: qq) in
    H.elim_equatable_laws qq ();
    H.x_mul_one e1;                          (* e1 *_qq o =eq= e1 *)
    fraction_ring_mul_reveal e1 o;  (* e1 *_qq o == fraction_mul e1 o *)
    fraction_mul_reveal e1 o

(* embed_zq_const (neg a) =eq= neg (embed_zq_const a) in ℚ.
   Re-derived (EmbedQProd's `embed_const_neg` is private). *)
private let embed_const_neg_loc (a: int)
  : Lemma ((embed_zq_const (Prims.op_Minus a))
             = (- (embed_zq_const a) <: qq))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let ea  = embed_zq_const a in
    let ena = embed_zq_const (Prims.op_Minus a) in
    let nea = (- ea <: qq) in
    (* (1) ea + ena =eq= zero. *)
    fraction_ring_add_reveal ea ena;       (* ea + ena == fraction_add ea ena *)
    embed_zq_const_add a (Prims.op_Minus a);            (* fraction_add ea ena = embed (a + neg a) *)
    assert ((a ++ (Prims.op_Minus a)) == 0);
    embed_zq_const_zero ();                              (* embed 0 =eq= crq.zero *)
    (* (2) ea + nea =eq= zero. *)
    H.x_plus_neg_x ea;
    (* (3) cancel. *)
    H.group_cancel_left ea ena nea

(* The qq RING `+`/`*` are fraction_add/fraction_mul (re-derived here so
   this module does not depend on EmbedQ's private reveals). *)
private let qq_ring_add_reveal_loc (a b: qq)
  : Lemma ((a + b) == fraction_add a b)
  = fraction_ring_add_reveal a b

private let qq_ring_mul_reveal_loc (a b: qq)
  : Lemma ((a * b) == fraction_mul a b)
  = fraction_ring_mul_reveal a b

(* ================================================================ *)
(*  2. Embedding pushes through the scalar product.                   *)
(*     eval_prod_sub #qq #ff (map embed roots) (embed c)              *)
(*       =eq= embed_zq_const (int_prod_sub roots c).                  *)
(* ================================================================ *)

#push-options "--fuel 2 --ifuel 2"
let rec eval_prod_sub_embed (roots: list int) (c: int)
  : Lemma (ensures
             (eval_prod_sub #qq #ff (L.map embed_zq_const roots) (embed_zq_const c))
             = (embed_zq_const (int_prod_sub roots c)))
          (decreases roots)
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    match roots with
    | [] ->
        (* eval_prod_sub #qq #ff [] (embed c) == one #qq == crq.one;
           int_prod_sub [] c == 1; embed 1 =eq= crq.one. *)
        embed_const_one_loc ()
    | a :: rest ->
        let ec  = embed_zq_const c in
        let ea  = embed_zq_const a in
        let nea = (- ea <: qq) in
        (* eval_prod_sub (embed a :: map embed rest) ec
             == (neg (embed a) + ec) * eval_prod_sub (map embed rest) ec   (qq ops) *)
        let tail_q = eval_prod_sub #qq #ff (L.map embed_zq_const rest) ec in
        (* head factor in qq:  (neg ea + ec)  =eq=  embed (neg a + c) *)
        (* embed_const_neg_loc: embed (neg a) =eq= neg ea  ⇒ neg ea =eq= embed (neg a) *)
        embed_const_neg_loc a;
        (* nea =eq= embed (neg a)  (symmetry is in scope) *)
        (* neg ea + ec =eq= embed (neg a) + ec  (add_congruence) *)
        add_congruence
          nea ec (embed_zq_const (Prims.op_Minus a)) ec;
        (* embed (neg a) + ec == fraction_add (embed (neg a)) ec =eq= embed (neg a + c) *)
        qq_ring_add_reveal_loc (embed_zq_const (Prims.op_Minus a)) ec;
        embed_zq_const_add (Prims.op_Minus a) c;          (* fraction_add =eq= embed (neg a + c) *)
        (* assemble:  neg ea + ec  =eq=  embed (neg a + c) *)
        (* IH on the tail:  tail_q =eq= embed (int_prod_sub rest c) *)
        eval_prod_sub_embed rest c;
        (* product congruence in qq:
             (neg ea + ec) * tail_q
               =eq= embed (neg a + c) * embed (int_prod_sub rest c) *)
        mul_congruence
          (nea + ec) tail_q
          (embed_zq_const ((Prims.op_Minus a) ++ c))
          (embed_zq_const (int_prod_sub rest c));
        (* embed (neg a + c) * embed (...) == fraction_mul (...) =eq= embed ((neg a + c) * (...)) *)
        qq_ring_mul_reveal_loc
          (embed_zq_const ((Prims.op_Minus a) ++ c))
          (embed_zq_const (int_prod_sub rest c));
        embed_zq_const_mul
          ((Prims.op_Minus a) ++ c)
          (int_prod_sub rest c)
#pop-options

(* ================================================================ *)
(*  3. |int_prod_sub roots c| >= 1  for distinct nodes.               *)
(* ================================================================ *)

#push-options "--fuel 2 --ifuel 2"
let rec int_prod_sub_abs_ge_one (roots: list int) (c: int)
  : Lemma (requires (forall (m:int). L.memP m roots ==> m <> c))
          (ensures LB.iabs (int_prod_sub roots c) >= 1)
          (decreases roots)
  = match roots with
    | [] ->
        (* iabs 1 = 1 *)
        ()
    | a :: rest ->
        let head = (Prims.op_Minus a) ++ c in
        let tail = int_prod_sub rest c in
        (* a <> c ⇒ head = c - a <> 0 ⇒ iabs head >= 1 *)
        assert (L.memP a (a :: rest));
        assert (a <> c);
        assert (head <> 0);
        LB.iabs_ge_one head;                              (* iabs head >= 1 *)
        (* IH:  iabs tail >= 1 *)
        int_prod_sub_abs_ge_one rest c;
        LB.iabs_ge_one head;
        (* iabs (head * tail) = iabs head * iabs tail >= 1*1 = 1 *)
        LB.iabs_mul head tail;
        ML.lemma_mult_le_left (LB.iabs head) 1 (LB.iabs tail)   (* head*1 <= head*tail *)
#pop-options

(* ================================================================ *)
(*  4. The field-level lagrange_denom over the mapped node list       *)
(*     is the embedding of the integer scalar product.                *)
(* ================================================================ *)

(* index of a mapped list:  index (map g l) i == g (index l i). *)
private let rec index_map_loc (#a #b:Type) (g: a -> b) (l: list a) (i:nat{i < L.length l})
  : Lemma (ensures (L.map_lemma g l; L.index (L.map g l) i == g (L.index l i)))
          (decreases i)
  = L.map_lemma g l;
    if i = 0 then ()
    else index_map_loc g (L.tl l) (i - 1)

(* delete_index commutes with map. *)
#push-options "--fuel 2 --ifuel 2"
let rec delete_index_map (#a #b:Type) (g: a -> b) (l: list a) (j: nat{j < L.length l})
  : Lemma (ensures (L.map_lemma g l;
                    delete_index (L.map g l) j == L.map g (delete_index l j)))
          (decreases l)
  = L.map_lemma g l;
    match l with
    | x :: rest ->
      if j = 0 then ()
      else begin
        L.map_lemma g rest;
        delete_index_map g rest (j - 1)
      end
#pop-options

let lagrange_denom_embed (int_cs: list int) (j: nat{j < L.length int_cs})
  : Lemma ((j < L.length (L.map embed_zq_const int_cs)) /\
           (lagrange_denom #qq #ff (L.map embed_zq_const int_cs) j)
             = (embed_zq_const (int_prod_sub (delete_index int_cs j) (L.index int_cs j))))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let qcs = L.map embed_zq_const int_cs in
    L.map_lemma embed_zq_const int_cs;                   (* length qcs == length int_cs *)
    (* index commutes: index qcs j == embed (index int_cs j) *)
    index_map_loc embed_zq_const int_cs j;
    (* delete commutes: delete_index qcs j == map embed (delete_index int_cs j) *)
    delete_index_map embed_zq_const int_cs j;
    (* lagrange_denom qcs j == eval_prod_sub (delete_index qcs j) (index qcs j)
                            == eval_prod_sub (map embed (delete_index int_cs j))
                                             (embed (index int_cs j)) *)
    eval_prod_sub_embed (delete_index int_cs j) (L.index int_cs j)
