module Core.Fractions

(*
   Field-of-fractions construction for the new diamond-free tower.

   Public interface: given `integral_domain t`, build `fraction d` and
   publish `field (fraction d)`. All intermediate instances
   (`equatable`, `add_comm_group`, `ring`, `commutative_ring`,
   `domain`, `integral_domain`, `skewfield`) are derived automatically
   from `fraction_field` via the foundation's projection chain
   (`sf_of_f`, `id_of_f`, `cr_of_id`, `d_of_id`, `r_of_cr`,
   `acg_of_r`, `eq_of_acg`). We only need to ship one instance.

   Design notes:
   - Source constraint is `{| d: integral_domain t |}`. The
     `id_one_ne_zero` axiom is part of `integral_domain` now, so no
     separate `zero_ne_one` constraint anywhere in this interface.
   - Equality of fractions is cross-multiplication: `a/b = c/d` iff
     `a * d = c * b` in `t`.
   - Operators (`+`, `*`, unary `-`, `--`, `=`, `<>`) work on
     `fraction d` once `Core.Algebra.Notation` is open.
   - Named functions (`fraction_add`, `fraction_mul`, `fraction_neg`,
     `fraction_inv`, `fraction_zero`, `fraction_one`) are exposed as
     plain `val`s for direct reference in proofs (avoids opaque
     projection-chain expressions like `f.f_sf.sf_d.d_r.r_add.add`).
*)

module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation

(* ------------------------------------------------------------------ *)
(* Core type                                                           *)
(* ------------------------------------------------------------------ *)

(* A fraction over `d`: pair of numerator (any element of `t`) and
   nonzero denominator. Stored unreduced; canonicalization is a
   correctness lemma not a representation invariant. *)
type fraction (#t:Type) (d: integral_domain t) =
  | Fraction : (num: t) -> (den: t{is_nonzero den}) -> fraction d

(* ------------------------------------------------------------------ *)
(* Constants and operations                                            *)
(*   `t` is explicit on 0-arg vals (can't be inferred from a call).   *)
(*   `t` is implicit on operations (derivable from `fraction d` args).*)
(* ------------------------------------------------------------------ *)

val fraction_zero (t:Type) {| d: integral_domain t |} : fraction d

val fraction_one  (t:Type) {| d: integral_domain t |} : fraction d

val fraction_add (#t:Type) {| d: integral_domain t |}
                 (x y: fraction d) : fraction d

val fraction_neg (#t:Type) {| d: integral_domain t |}
                 (x: fraction d) : fraction d

val fraction_mul (#t:Type) {| d: integral_domain t |}
                 (x y: fraction d) : fraction d

(* ------------------------------------------------------------------ *)
(* The one published instance                                          *)
(*   Everything downstream (equatable, acg, ring, cr, domain, id,     *)
(*   skewfield) is reachable from `fraction_field` via the           *)
(*   foundation's projection chain. We deliberately do NOT publish    *)
(*   intermediate instances — that would create alternative search    *)
(*   paths and risk diamonds.                                        *)
(*                                                                    *)
(*   Inversion is reached via the foundation's `inv` (from            *)
(*   `mul_is_group`), not published separately here.                 *)
(* ------------------------------------------------------------------ *)

instance val fraction_field (t:Type) (d: integral_domain t)
  : field (fraction d)

(* ------------------------------------------------------------------ *)
(* Reveal lemmas: let external modules reason about the numerator and  *)
(* denominator of a fraction sum, and bridge the published `=`         *)
(* operator on `fraction d` to cross-multiplication in `t`.            *)
(* ------------------------------------------------------------------ *)

(* num/den of a sum: matches the body of `fraction_add`.               *)
val fraction_add_reveal (#t:Type) {| d: integral_domain t |} (x y: fraction d)
  : Lemma (Fraction?.num (fraction_add x y)
             == ((Fraction?.num x * Fraction?.den y)
               + (Fraction?.den x * Fraction?.num y)) /\
           Fraction?.den (fraction_add x y)
             == (Fraction?.den x * Fraction?.den y))

(* num/den of the additive constant `fraction_zero`: `0/1`. *)
val fraction_zero_reveal (t:Type) {| d: integral_domain t |}
  : Lemma (Fraction?.num (fraction_zero t #d) == (zero <: t) /\
           Fraction?.den (fraction_zero t #d) == (one  <: t))

(* The published `=` on `fraction d` (resolved through `fraction_field`)
   is cross-multiplication in `t`. *)
val fraction_eq_reveal (#t:Type) {| d: integral_domain t |} (x y: fraction d)
  : Lemma ((x = y) <==> ((Fraction?.num x * Fraction?.den y)
                       = (Fraction?.den x * Fraction?.num y)))

(* ------------------------------------------------------------------ *)
(* Convenience: division as a partial operation on raw t              *)
(* ------------------------------------------------------------------ *)

val ( / ) (#t:Type) {| d: integral_domain t |}
          (x: t) (y: t)
  : Pure (fraction d)
         (requires is_nonzero y)
         (ensures fun _ -> True)
