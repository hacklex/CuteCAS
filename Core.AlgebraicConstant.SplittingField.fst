module Core.AlgebraicConstant.SplittingField

(*
   §E — the splitting-field certificate (SPLITTING-FIELD-PLAN.md, E3/E4).

   `splits d` says: there is a field l, reached from t by a certified
   embedding, over which d factors completely into distinct linear factors.
   The certificate is a GHOST existential (the tower is built from the ghost
   irreducible_factor_exists), packaged per the repo's opaque-predicate
   discipline; consumers use the _elim bridges.

   Structure:
     is_embedding l e emb   — the embedding payload (P-facts):
        P0' emb additive                P1  emb multiplicative
        P2  emb (X - a) = X - e a       P3  deg (emb p) == deg p
        P6  (emb p)(e a) = e (p(a))     P7  e preserves nonzero
        P8  emb respects =              P8e e respects =
     splits_with d l e emb roots — is_embedding + the split data:
        P4  roots nonempty, distinct, exactly deg d of them
        P5  emb d = e(lc d) · ∏ (X - β)
     splits d — the existential package over (l, fl, e, emb, roots).

   KEY ERGONOMIC PIN (P0-tested): `poly_over l #fl` spells the CR-indexed
   polynomial type identically at binders/witnesses/signatures, avoiding the
   instance-unification trap.  Multi-binder introduce must nest the Type0
   binder first.
*)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Roots
open Core.Polynomial.Irreducible

#set-options "--fuel 2 --ifuel 1 --z3rlimit 30"

(* The extension-side polynomial type, with its commutative_ring derived
   DETERMINISTICALLY from the packed field instance. *)
unfold let poly_over (l: Type0) {| fl: field l |} : Type = polynomial l

(* ---------------------------------------------------------------- *)
(*  The embedding payload.                                           *)
(* ---------------------------------------------------------------- *)

[@@"opaque_to_smt"]
let is_embedding (#t:Type) {| f: field t |}
  (l: Type0) {| fl: field l |}
  (e: t -> l) (emb: polynomial t -> poly_over l #fl)
  : prop
  = (forall (p q: polynomial t). emb (p + q) = emb p + emb q) /\
    (forall (p q: polynomial t). emb (p * q) = emb p * emb q) /\
    (forall (a: t). emb (poly_linear a) = poly_linear (e a)) /\
    (forall (p: polynomial t). deg (emb p) == deg p) /\
    (forall (p: polynomial t) (a: t).
       poly_eval (emb p) (e a) = e (poly_eval p a)) /\
    (forall (x: t). x <> zero ==> e x <> zero) /\
    (forall (p q: polynomial t). p = q ==> emb p = emb q) /\
    (forall (x y: t). x = y ==> e x = e y)

let is_embedding_elim (#t:Type) {| f: field t |}
  (l: Type0) {| fl: field l |}
  (e: t -> l) (emb: polynomial t -> poly_over l #fl)
  : Lemma (requires is_embedding l #fl e emb)
          (ensures
            (forall (p q: polynomial t). emb (p + q) = emb p + emb q) /\
            (forall (p q: polynomial t). emb (p * q) = emb p * emb q) /\
            (forall (a: t). emb (poly_linear a) = poly_linear (e a)) /\
            (forall (p: polynomial t). deg (emb p) == deg p) /\
            (forall (p: polynomial t) (a: t).
               poly_eval (emb p) (e a) = e (poly_eval p a)) /\
            (forall (x: t). x <> zero ==> e x <> zero) /\
            (forall (p q: polynomial t). p = q ==> emb p = emb q) /\
            (forall (x y: t). x = y ==> e x = e y))
  = reveal_opaque (`%is_embedding) (is_embedding #t #f l #fl e emb)

let is_embedding_intro (#t:Type) {| f: field t |}
  (l: Type0) {| fl: field l |}
  (e: t -> l) (emb: polynomial t -> poly_over l #fl)
  : Lemma (requires
            (forall (p q: polynomial t). emb (p + q) = emb p + emb q) /\
            (forall (p q: polynomial t). emb (p * q) = emb p * emb q) /\
            (forall (a: t). emb (poly_linear a) = poly_linear (e a)) /\
            (forall (p: polynomial t). deg (emb p) == deg p) /\
            (forall (p: polynomial t) (a: t).
               poly_eval (emb p) (e a) = e (poly_eval p a)) /\
            (forall (x: t). x <> zero ==> e x <> zero) /\
            (forall (p q: polynomial t). p = q ==> emb p = emb q) /\
            (forall (x y: t). x = y ==> e x = e y))
          (ensures is_embedding l #fl e emb)
  = reveal_opaque (`%is_embedding) (is_embedding #t #f l #fl e emb)

(* ---------------------------------------------------------------- *)
(*  Identity embedding (base case of the tower).                     *)
(* ---------------------------------------------------------------- *)

let id_map (t: Type) : t -> t = fun x -> x

let id_poly_map (#t:Type) {| f: field t |} : polynomial t -> poly_over t #f =
  fun p -> p

let id_is_embedding (#t:Type) {| f: field t |} ()
  : Lemma (is_embedding t #f (id_map t) id_poly_map)
  = H.elim_equatable_laws (polynomial t) ();
    H.elim_equatable_laws t ();
    is_embedding_intro t #f (id_map t) id_poly_map

(* ---------------------------------------------------------------- *)
(*  Composition: embeddings stack (the tower's lift step).           *)
(* ---------------------------------------------------------------- *)

unfold let compose_base (#t:Type) (#m: Type) (#l: Type)
  (e1: t -> m) (e2: m -> l) : t -> l = fun x -> e2 (e1 x)

unfold let compose_poly (#t:Type) {| f: field t |}
  (m: Type) {| fm: field m |} (l: Type) {| fl: field l |}
  (emb1: polynomial t -> poly_over m #fm)
  (emb2: poly_over m #fm -> poly_over l #fl)
  : polynomial t -> poly_over l #fl
  = fun p -> emb2 (emb1 p)

#push-options "--z3rlimit 60 --split_queries always"
let compose_is_embedding (#t:Type) {| f: field t |}
  (m: Type) {| fm: field m |} (l: Type) {| fl: field l |}
  (e1: t -> m) (emb1: polynomial t -> poly_over m #fm)
  (e2: m -> l) (emb2: poly_over m #fm -> poly_over l #fl)
  : Lemma (requires
            is_embedding m #fm e1 emb1 /\
            is_embedding #m #fm l #fl e2 emb2)
          (ensures
            is_embedding l #fl (compose_base e1 e2)
                               (compose_poly m #fm l #fl emb1 emb2))
  = is_embedding_elim m #fm e1 emb1;
    is_embedding_elim #m #fm l #fl e2 emb2;
    let e : t -> l = compose_base e1 e2 in
    let emb : polynomial t -> poly_over l #fl =
      compose_poly m #fm l #fl emb1 emb2 in
    H.elim_equatable_laws (polynomial l) ();
    H.trans_for_calc (polynomial l) ();
    H.elim_equatable_laws l ();
    H.trans_for_calc l ();
    (* P0' add: emb (p+q) = emb2 (emb1 (p+q)) = emb2 (emb1 p + emb1 q)
                = emb2 (emb1 p) + emb2 (emb1 q)  (P8₂ then P0'₂) *)
    introduce forall (p q: polynomial t). emb (p + q) = emb p + emb q
    with begin
      assert (emb1 (p + q) = emb1 p + emb1 q);
      assert (emb2 (emb1 (p + q)) = emb2 (emb1 p + emb1 q));
      assert (emb2 (emb1 p + emb1 q) = emb2 (emb1 p) + emb2 (emb1 q))
    end;
    (* P1 mul *)
    introduce forall (p q: polynomial t). emb (p * q) = emb p * emb q
    with begin
      let a1 : poly_over m #fm = emb1 p in
      let b1 : poly_over m #fm = emb1 q in
      let ab : poly_over m #fm = a1 * b1 in
      assert (emb1 (p * q) = ab);
      assert (emb2 (emb1 (p * q)) = emb2 ab);
      assert (emb2 ab = emb2 a1 * emb2 b1)
    end;
    (* P2 linear *)
    introduce forall (a: t). emb (poly_linear a) = poly_linear (e a)
    with begin
      assert (emb1 (poly_linear a) = poly_linear (e1 a));
      assert (emb2 (emb1 (poly_linear a)) = emb2 (poly_linear (e1 a)));
      assert (emb2 (poly_linear (e1 a)) = poly_linear (e2 (e1 a)))
    end;
    (* P6 eval *)
    introduce forall (p: polynomial t) (a: t).
        poly_eval (emb p) (e a) = e (poly_eval p a)
    with begin
      assert (poly_eval (emb2 (emb1 p)) (e2 (e1 a))
                = e2 (poly_eval (emb1 p) (e1 a)));
      assert (poly_eval (emb1 p) (e1 a) = e1 (poly_eval p a));
      assert (e2 (poly_eval (emb1 p) (e1 a)) = e2 (e1 (poly_eval p a)))
    end;
    is_embedding_intro l #fl e emb
#pop-options

(* ---------------------------------------------------------------- *)
(*  The splitting certificate.                                       *)
(* ---------------------------------------------------------------- *)

[@@"opaque_to_smt"]
let splits_with (#t:Type) {| f: field t |} (d: polynomial t)
  (l: Type0) {| fl: field l |}
  (e: t -> l) (emb: polynomial t -> poly_over l #fl) (roots: list l)
  : prop
  = is_embedding l #fl e emb /\
    Cons? roots /\ all_distinct roots /\
    L.length roots == deg d /\
    (emb d = (poly_const (e (poly_lc d))) * (poly_prod_linears roots))

let splits_with_elim (#t:Type) {| f: field t |} (d: polynomial t)
  (l: Type0) {| fl: field l |}
  (e: t -> l) (emb: polynomial t -> poly_over l #fl) (roots: list l)
  : Lemma (requires splits_with d l #fl e emb roots)
          (ensures
            is_embedding l #fl e emb /\
            Cons? roots /\ all_distinct roots /\
            L.length roots == deg d /\
            (emb d = (poly_const (e (poly_lc d))) * (poly_prod_linears roots)))
  = reveal_opaque (`%splits_with) (splits_with d l #fl e emb roots)

let splits_with_intro (#t:Type) {| f: field t |} (d: polynomial t)
  (l: Type0) {| fl: field l |}
  (e: t -> l) (emb: polynomial t -> poly_over l #fl) (roots: list l)
  : Lemma (requires
            is_embedding l #fl e emb /\
            Cons? roots /\ all_distinct roots /\
            L.length roots == deg d /\
            (emb d = (poly_const (e (poly_lc d))) * (poly_prod_linears roots)))
          (ensures splits_with d l #fl e emb roots)
  = reveal_opaque (`%splits_with) (splits_with d l #fl e emb roots)

(* The headline certificate: such an extension exists. *)
[@@"opaque_to_smt"]
let splits (#t:Type) {| f: field t |} (d: polynomial t) : prop =
  exists (l: Type0) (fl: field l)
    (e: t -> l) (emb: polynomial t -> poly_over l #fl) (roots: list l).
    splits_with d l #fl e emb roots

let splits_intro (#t:Type) {| f: field t |} (d: polynomial t)
  (l: Type0) {| fl: field l |}
  (e: t -> l) (emb: polynomial t -> poly_over l #fl) (roots: list l)
  : Lemma (requires splits_with d l #fl e emb roots)
          (ensures  splits d)
  = reveal_opaque (`%splits) (splits #t #f d);
    introduce exists (l: Type0).
        (exists (fl: field l)
           (e: t -> l) (emb: polynomial t -> poly_over l #fl) (roots: list l).
           splits_with d l #fl e emb roots)
      with l
      and introduce exists (fl: field l)
            (e: t -> l) (emb: polynomial t -> poly_over l #fl) (roots: list l).
            splits_with d l #fl e emb roots
          with fl e emb roots and ()

let splits_elim (#t:Type) {| f: field t |} (d: polynomial t)
  : Lemma (requires splits d)
          (ensures
            exists (l: Type0) (fl: field l)
              (e: t -> l) (emb: polynomial t -> poly_over l #fl) (roots: list l).
              splits_with d l #fl e emb roots)
  = reveal_opaque (`%splits) (splits #t #f d)

(* ---------------------------------------------------------------- *)
(*  Root-distinctness bookkeeping (used by the tower recursion).     *)
(* ---------------------------------------------------------------- *)

(* poly_eval respects `=` in the POINT argument:
   Core.Polynomial.Eval.eval_point_congruence. *)

(* A member of the root list zeroes the linear product:
   Core.Polynomial.Roots.prod_linears_vanishes. *)

(* The fresh-root lift: if the remaining factor (already split at l)
   does NOT vanish at rho, then rho is distinct from all its roots.   *)
let fresh_root_all_distinct (#l:Type) {| fl: field l |}
  (rho: l) (roots_q: list l) (embq: polynomial l) (cq: l)
  : Lemma (requires all_distinct roots_q /\
                    (embq = (poly_const cq) * (poly_prod_linears roots_q)) /\
                    not (poly_eval embq rho = zero))
          (ensures  all_distinct (rho :: roots_q))
  = H.elim_equatable_laws l ();
    H.trans_for_calc l ();
    introduce forall (d: l). L.memP d roots_q ==> not (rho = d)
    with introduce L.memP d roots_q ==> not (rho = d)
    with hmem. begin
      if rho = d then begin
        (* eval embq d = eval(const*prod) d = w * 0 = 0, then point congr *)
        prod_linears_vanishes roots_q d;
        eval_congruence embq ((poly_const cq) * (poly_prod_linears roots_q)) d;
        eval_mul (poly_const cq) (poly_prod_linears roots_q) d;
        mul_congruence (poly_eval (poly_const cq) d)
                       (poly_eval (poly_prod_linears roots_q) d)
                       (poly_eval (poly_const cq) d) (zero <: l);
        H.x_mul_zero (poly_eval (poly_const cq) d);
        eval_point_congruence embq rho d
      end else ()
    end
