module Core.Polynomial.EmbedQInterp

(* ================================================================ *)
(*  §D step (b) — instantiate the field-generic Lagrange             *)
(*  interpolation identity at ℚ for an embedded INTEGER polynomial.  *)
(*                                                                   *)
(*  For distinct integer nodes cs (deg g < #nodes), the canonical    *)
(*  embedding  embed_zq g : ℚ[X]  equals its own Lagrange interpolant*)
(*  over the embedded nodes  map embed_zq_const cs.                  *)
(*                                                                   *)
(*  Plumbing only:                                                   *)
(*   1. embed_zq_const is injective w.r.t. the ℚ equatable           *)
(*      (n/1 = m/1  iff  n == m, via fraction_eq_reveal).            *)
(*   2. an injective map preserves all_distinct (generic helper).    *)
(*   3. embed_zq is degree-preserving (embed_zq_deg) and             *)
(*      length (map f cs) == length cs, so the degree precondition   *)
(*      transports.                                                  *)
(*   4. apply lagrange_interpolation at ℚ.                           *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Polynomial
open Core.Fractions
open Core.Polynomial.Roots
open Core.Polynomial.EmbedQ
open Core.Polynomial.Lagrange
open Core.Polynomial.LagrangeInterp
open Core.Polynomial.LagrangeInterpId

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------- *)
(*  1. embed_zq_const is injective w.r.t. the ℚ equatable `=`.       *)
(*     n/1 = m/1  <==>  n*1 = 1*m  <==>  n == m   (integer arith).    *)
(* ---------------------------------------------------------------- *)

let embed_zq_const_inj (n m: int)
  : Lemma (requires (embed_zq_const n = embed_zq_const m))
          (ensures  n == m)
  = fraction_eq_reveal (embed_zq_const n) (embed_zq_const m)
    (* (n/1 = m/1) <==> (num(n/1) * den(m/1) = den(n/1) * num(m/1))
                    <==> (n * 1 = 1 * m)  <==>  n == m. *)

(* Contrapositive form: distinct integers map to distinct fractions. *)
let embed_zq_const_inj_contra (n m: int)
  : Lemma (requires not (n = m))
          (ensures  not (embed_zq_const n = embed_zq_const m))
  = Classical.move_requires_2 embed_zq_const_inj n m

(* ---------------------------------------------------------------- *)
(*  2. Injective map preserves all_distinct.                         *)
(*     If cs is all_distinct over ℤ and embed_zq_const is injective, *)
(*     then (map embed_zq_const cs) is all_distinct over ℚ.          *)
(* ---------------------------------------------------------------- *)

let rec embed_all_distinct_map (cs: list int)
  : Lemma (requires all_distinct #int #int_cr cs)
          (ensures  all_distinct #qq #crq (L.map embed_zq_const cs))
          (decreases cs)
  = match cs with
    | [] -> ()
    | c :: rest ->
      (* all_distinct (c::rest) =
           (forall d. memP d rest ==> not (c = d)) /\ all_distinct rest *)
      embed_all_distinct_map rest;                  (* tail distinct over ℚ *)
      let ec = embed_zq_const c in
      (* head goal: forall e. memP e (map embed rest) ==> not (ec = e) *)
      let head (e: qq)
        : Lemma (requires L.memP e (L.map embed_zq_const rest))
                (ensures  not (ec = e))
        = L.memP_map_elim embed_zq_const e rest;
          (* exists d. memP d rest /\ embed_zq_const d == e *)
          eliminate exists (d: int). L.memP d rest /\ embed_zq_const d == e
          returns not (ec = e)
          with _hd.
            (* from all_distinct head: not (c = d) over ℤ, i.e. c <> d *)
            embed_zq_const_inj_contra c d
      in
      let head' (e: qq)
        : Lemma (L.memP e (L.map embed_zq_const rest) ==> not (ec = e))
        = Classical.move_requires head e
      in
      Classical.forall_intro head'

(* ---------------------------------------------------------------- *)
(*  3. Length / degree transport for the map.                        *)
(* ---------------------------------------------------------------- *)

let embed_map_length_eq (cs: list int)
  : Lemma (L.length (L.map embed_zq_const cs) == L.length cs)
  = L.map_lemma embed_zq_const cs

(* ---------------------------------------------------------------- *)
(*  4. The instantiated interpolation identity over ℚ.               *)
(* ---------------------------------------------------------------- *)

let embed_interpolation (g: polynomial int #int_cr) (cs: list int)
  : Lemma (requires all_distinct #int #int_cr cs /\
                    deg #int #int_cr g < L.length cs)
          (ensures all_distinct #qq #crq (L.map embed_zq_const cs) /\
                   embed_zq g
                   = lagrange_interpolant #qq #(fraction_field int int_id)
                        (embed_zq g) (L.map embed_zq_const cs)
                        #())
  = let qcs = L.map embed_zq_const cs in
    (* (2) embedded nodes are distinct over ℚ. *)
    embed_all_distinct_map cs;
    let sq : squash (all_distinct #qq #crq qcs) = () in
    (* (3) degree precondition transports. *)
    embed_zq_deg g;                                 (* deg(embed g) == deg g *)
    embed_map_length_eq cs;                         (* length qcs == length cs *)
    (* (4) apply the field-generic identity at ℚ. *)
    lagrange_interpolation (embed_zq g) qcs #sq
