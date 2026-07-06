module Core.Modular.PrimeField.Poly

(* ================================================================ *)
(*  Polynomial ring over the prime field 𝔽_p, as a directly-        *)
(*  resolvable typeclass instance.                                   *)
(*                                                                   *)
(*  `commutative_ring (fp p)` resolves (via the field → integral_    *)
(*  domain → commutative_ring chain), but that chain does NOT        *)
(*  compose *nested* inside `polynomial_cr` for the concrete carrier *)
(*  `fp p`, so `commutative_ring (polynomial (fp p))` (and the       *)
(*  `add_comm_group` / `equatable` reached from it) fail to resolve  *)
(*  on their own.  This single instance — `polynomial_cr` at the     *)
(*  carrier `fp p`, with the coefficient ring resolved by TC —       *)
(*  makes the whole polynomial-over-𝔽_p instance tower resolve, so   *)
(*  consumers need no explicit `polynomial_cr`/`pacg`/`pcr`/`cr`     *)
(*  plumbing.  It is the SAME instance the generic poly layer        *)
(*  produces at `fp p`, so it introduces no duality/mismatch.        *)
(* ================================================================ *)

open Core.Algebra
open Core.Polynomial
open Core.Modular.PrimeField
open FStar.Math.Euclid

instance fp_poly_cr (p:int{is_prime p}) : commutative_ring (polynomial (fp p)) =
  polynomial_cr #(fp p)
