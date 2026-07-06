module Core.AlgebraicConstant.ExtendStep

(*
   §E splitting-field extend step.

   Given a PROPER irreducible factor r of d (degree ≥ 2 — a genuine extension; a
   degree-1 factor X-a has its root already in the base field t and needs no
   extension, so it is split directly over t, NOT here), peel_root_quotient says
   that over the extension field algebraic r the embedded d splits off the linear
   factor (X - theta) with a strict degree drop — the recursable form for the
   splitting-field construction. The factor r is supplied by the caller (the
   splitting recursion picks a degree-≥2 irreducible factor when d is not yet split
   over the current field); this step does not search for it.
*)

module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Roots
open Core.Polynomial.Irreducible
open Core.Polynomial.Unique
open Core.AlgebraicConstant
open Core.AlgebraicConstant.Root
open Core.AlgebraicConstant.Eval
open Core.AlgebraicConstant.Peel
open Core.AlgebraicConstant.PeelQuotient

let extend_gains_linear_factor (#t:Type) {| f: field t |}
  (r: polynomial t {proper_extension r})
  (d: polynomial t {deg d >= 1 /\ divides r d})
  : Lemma (ensures
        (exists (q: polynomial (algebraic r)).
           (embed_poly r d) = (poly_linear theta * q) /\
           (deg (embed_poly r d) >= 0 ==>
              deg q >= 0 /\
              deg q < deg (embed_poly r d))))
  = peel_root_quotient r d
