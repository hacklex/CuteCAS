module Core.Polynomial.EuclideanNotation

(*
   `/` and `%` for polynomials over a field: quotient and remainder of
   `poly_divmod`.  Operator form (operand-directed), in its own module so int-`%`
   modules keep native `%`.  Poly-SPECIFIC (over `poly_div`/`poly_rem`, not the
   generic `euclidean_domain` class) — registering `euclidean_domain (polynomial t)`
   would diamond `commutative_ring (polynomial t)` against the existing instance.

   The divisibility fact `r | (p - p%r)` is published with an SMTPat on `p % r`,
   so it is available for free wherever a remainder appears (this is the old
   `mk_mod`, now ambient).
*)

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div

unfold let ( / ) (#t:Type) {| f: field t |} (p r: polynomial t) : polynomial t = poly_div p r
unfold let ( % ) (#t:Type) {| f: field t |} (p r: polynomial t) : polynomial t = poly_rem p r

(* SMTPat: the div/mod identity  p ~ r*(p/r) + (p%r)  (= poly_divmod_correct),
   revealed for free wherever `p % r` appears. From it, `r | (p - p%r)` follows. *)
let poly_div_mod (#t:Type) {| f: field t |} (p r: polynomial t)
  : Lemma (p = r * (p / r) + (p % r))
    [SMTPatOr [[SMTPat (p / r)]; [SMTPat (p % r)]]]
  = ()
