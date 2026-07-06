module Core.Polynomial.Unique

(*
   Uniqueness of Euclidean division for univariate polynomials over a field.

   Ported from legacy `FStar.CAS.Polynomial.Euclidean.poly_divmod_unique`
   (lines 1158–1226) to the new `Core.Polynomial` tower.

   Supporting lemmas:
     - degree_well_defined
     - degree_none_poly_eq_zero
     - sub_zero_implies_eq
     - degree_mul                (integral_domain coefficients)
     - only_mul_zero_decreases_poly_degree
     - poly_mul_sub_distrib
     - add_rearrange
   Main result:
     - poly_divmod_unique
*)

module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div

(* ------------------------------------------------------------------ *)

val degree_well_defined (#t:Type) {| cr: commutative_ring t |}
                        (p q: polynomial t)
  : Lemma (requires p = q)
          (ensures  deg p == deg q)

(* is_nonzero p  <==>  deg p >= 0  (deg characterises the zero polynomial). *)
val nonzero_iff_some_deg (#t:Type) {| cr: commutative_ring t |}
                         (p: polynomial t)
  : Lemma (is_nonzero p <==> deg p >= 0)

val degree_none_poly_eq_zero (#t:Type) {| cr: commutative_ring t |}
                             (p: polynomial t)
  : Lemma (requires deg p < 0)
          (ensures  p = (poly_zero #t))

val sub_zero_implies_eq (#t:Type) {| cr: commutative_ring t |}
                        (a b: polynomial t)
  : Lemma (requires (a -- b) = (poly_zero #t))
          (ensures  a = b)

val degree_mul (#t:Type) {| id: integral_domain t |}
               (p q: polynomial t)
  : Lemma (requires deg p >= 0 /\ deg q >= 0)
          (ensures  deg (p * q) == deg p + deg q)

val only_mul_zero_decreases_poly_degree
    (#t:Type) {| f: field t |} (q d s: polynomial t)
  : Lemma (requires deg q >= 0 /\
                    (q * d) = s /\
                    deg s < deg q)
          (ensures  deg d < 0)

val poly_mul_sub_distrib (#t:Type) {| cr: commutative_ring t |}
                         (q a b: polynomial t)
  : Lemma ((q * (a -- b))
                   = ((q * a) -- (q * b)))

val add_rearrange (#t:Type) {| cr: commutative_ring t |}
                  (x y r1 r2: polynomial t)
  : Lemma (requires (x + r1) = (y + r2))
          (ensures  (x -- y) = (r2 -- r1))

val poly_divmod_unique (#t:Type) {| f: field t |}
                       (q a1 a2 r1 r2: polynomial t)
  : Lemma (requires
            deg q >= 0 /\
            ((q * a1) + r1)
                    = ((q * a2) + r2) /\
            deg r1 < deg q /\
            deg r2 < deg q)
          (ensures  a1 = a2 /\ r1 = r2)
