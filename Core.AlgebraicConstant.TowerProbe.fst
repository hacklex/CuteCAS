module Core.AlgebraicConstant.TowerProbe

(*
   P0 de-risk probe for SPLITTING-FIELD-PLAN.md §5 (NOT on the build list).

   Tests, in isolation, the four mechanics the §E tower recursion (E3) needs:
     T1  nested carrier typing:  algebraic r2  with  r2 : polynomial (algebraic r1)
         (TC must resolve field (algebraic r1) = algebraic_field r1 everywhere);
     T2  ghost certificate: exists (l:Type0) (fl: field l). ...  — intro + elim
         (irreducible_factor_exists is ghost, so the tower is a PROPOSITION);
     T3  recursion shape: a Lemma that eliminates the inner-level existential and
         introduces the outer one (the E3 step, 2-level miniature);
     T4  roots transport: mapping a root list through the level embedding.
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Roots
open Core.Polynomial.Irreducible
open Core.AlgebraicConstant
open Core.AlgebraicConstant.Root
open Core.AlgebraicConstant.Eval
open Core.AlgebraicConstant.PeelQuotient
open Core.AlgebraicConstant.ExtendStep

#set-options "--fuel 2 --ifuel 1 --z3rlimit 30"

(* ---------------------------------------------------------------- *)
(*  T1 — nested carrier: level-2 extension over a level-1 extension. *)
(* ---------------------------------------------------------------- *)

(* Does `algebraic r2` typecheck when r2 lives over `algebraic r1`?  The inner
   field instance must resolve via TC (algebraic_field r1). *)
let probe_nested_carrier (#t:Type) {| f: field t |}
  (r1: polynomial t {proper_extension r1})
  (r2: polynomial (algebraic r1) {proper_extension r2})
  : Type
  = algebraic r2

(* Apply the proven one-level step AT level 2 (over the extension). *)
let probe_nested_step (#t:Type) {| f: field t |}
  (r1: polynomial t {proper_extension r1})
  (r2: polynomial (algebraic r1) {proper_extension r2})
  (d2: polynomial (algebraic r1) {deg d2 >= 1 /\ divides r2 d2})
  : Lemma (exists (q: polynomial (algebraic r2)).
             (embed_poly r2 d2) = (poly_linear theta * q))
  = extend_gains_linear_factor r2 d2

(* ---------------------------------------------------------------- *)
(*  T2 — ghost certificate over a Type: intro and elim.              *)
(* ---------------------------------------------------------------- *)

(* Minimal payload: "there is a field l, an embedding of t into l, and a root
   list in l of a given length".  Just enough structure to exercise the
   quantifier mechanics; E3's real payload adds the split equation. *)
unfold let probe_cert (#t:Type) {| f: field t |} (n: nat) : prop =
  exists (l: Type0) (fl: field l) (emb: t -> l) (roots: list l).
    L.length roots == n

(* Intro at level 1: witness l = algebraic r1. *)
let probe_cert_intro (#t:Type) {| f: field t |}
  (r1: polynomial t {proper_extension r1})
  : Lemma (probe_cert #t 1)
  = let l : Type0 = algebraic r1 in
    let fl : field l = algebraic_field r1 in
    let emb : t -> l = fun (x: t) -> class_of r1 (poly_const x) in
    let roots : list l = [theta #t #f #r1] in
    assert (L.length roots == 1);
    introduce exists (l: Type0) (fl: field l) (emb: t -> l) (roots: list l).
        L.length roots == 1
      with l fl emb roots and ()

(* Elim: consume the certificate through a helper with an instance binder
   (the pattern all of E4/E5's consumption will use). *)
let probe_consume_aux (l: Type0) {| fl: field l |} (roots: list l)
  : Lemma (L.length roots >= 0)
  = ()

let probe_cert_elim (#t:Type) {| f: field t |} (n: nat)
  : Lemma (requires probe_cert #t n)
          (ensures  n >= 0)
  = eliminate exists (l: Type0) (fl: field l) (emb: t -> l) (roots: list l).
        L.length roots == n
      returns n >= 0
      with _. probe_consume_aux l #fl roots

(* ---------------------------------------------------------------- *)
(*  T3 — the recursion shape: eliminate inner cert, introduce outer. *)
(*  (2-level miniature of E3's step: compose the embedding.)         *)
(* ---------------------------------------------------------------- *)

let probe_step_compose (#t:Type) {| f: field t |}
  (r1: polynomial t {proper_extension r1})
  (n: nat)
  : Lemma (requires probe_cert #(algebraic r1) n)   (* inner-level certificate *)
          (ensures  probe_cert #t (n ++ 1))          (* outer: one more root    *)
  = eliminate exists (l: Type0) (fl: field l)
        (emb: algebraic r1 -> l) (roots: list l).
        L.length roots == n
      returns probe_cert #t (n ++ 1)
      with _.
      begin
        (* the new root: theta's image at the inner level, then up via emb *)
        let root0 : l = emb (theta #t #f #r1) in
        let roots' : list l = root0 :: roots in
        let emb'  : t -> l = fun (x: t) -> emb (class_of r1 (poly_const x)) in
        assert (L.length roots' == n ++ 1);
        introduce exists (l: Type0) (fl: field l) (emb: t -> l) (roots: list l).
            L.length roots == n ++ 1
          with l fl emb' roots' and ()
      end

(* ---------------------------------------------------------------- *)
(*  T4 — fuel recursion skeleton, mirroring E3's true shape:         *)
(*  irreducible_factor_exists (ghost) → eliminate → case-split on    *)
(*  deg r → extend → eliminate the split → TYPE-CHANGING recursive   *)
(*  call under the double elimination, decreasing on fuel.           *)
(*  Payload deliberately trivial (probe_cert #t 0): the mechanics    *)
(*  are what is being tested, T3 already tests the lift.             *)
(* ---------------------------------------------------------------- *)

let probe_cert_trivial (#t:Type) {| f: field t |} ()
  : Lemma (probe_cert #t 0)
  = let emb0 : t -> t = fun x -> x in
    introduce exists (l: Type0) (fl: field l) (emb: t -> l) (roots: list l).
        L.length roots == 0
      with t f emb0 ([] <: list t) and ()

let rec probe_build (#t:Type) {| f: field t |}
  (d: polynomial t {deg d >= 1})
  (fuel: nat)
  : Lemma (ensures probe_cert #t 0) (decreases fuel)
  = if fuel = 0 then probe_cert_trivial #t ()
    else begin
      irreducible_factor_exists d;
      eliminate exists (r: polynomial t). poly_irreducible r /\ divides r d
        returns probe_cert #t 0
        with _.
        begin
          if deg r >= 2 then begin
            (* proper_extension r holds: irreducible /\ deg >= 2 *)
            extend_gains_linear_factor r d;
            eliminate exists (q: polynomial (algebraic r)).
                (embed_poly r d) = (poly_linear theta * q) /\
                (deg (embed_poly r d) >= 0 ==>
                   deg q >= 0 /\ deg q < deg (embed_poly r d))
              returns probe_cert #t 0
              with _.
              begin
                (* THE test: type-changing recursive call under double elim *)
                if deg q >= 1
                then probe_build #(algebraic r) #(algebraic_field r) q (fuel - 1)
                else ();
                probe_cert_trivial #t ()
              end
          end
          else probe_cert_trivial #t ()
        end
    end
