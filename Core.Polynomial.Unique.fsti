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
  : Lemma (requires poly_eq p q)
          (ensures  poly_deg p == poly_deg q)

val degree_none_poly_eq_zero (#t:Type) {| cr: commutative_ring t |}
                             (p: polynomial t)
  : Lemma (requires None? (poly_deg p))
          (ensures  poly_eq p (poly_zero #t))

val sub_zero_implies_eq (#t:Type) {| cr: commutative_ring t |}
                        (a b: polynomial t)
  : Lemma (requires poly_eq (poly_sub a b) (poly_zero #t))
          (ensures  poly_eq a b)

val degree_mul (#t:Type) {| id: integral_domain t |}
               (p q: polynomial t)
  : Lemma (requires Some? (poly_deg p) /\ Some? (poly_deg q))
          (ensures  Some? (poly_deg (poly_mul p q)) /\
                    Some?.v (poly_deg (poly_mul p q)) ==
                    Prims.op_Addition (Some?.v (poly_deg p))
                                      (Some?.v (poly_deg q)))

val only_mul_zero_decreases_poly_degree
    (#t:Type) {| f: field t |} (q d s: polynomial t)
  : Lemma (requires Some? (poly_deg q) /\
                    poly_eq (poly_mul q d) s /\
                    (None? (poly_deg s) \/
                     (Some? (poly_deg s) /\
                      Some?.v (poly_deg s) < Some?.v (poly_deg q))))
          (ensures  None? (poly_deg d))

val poly_mul_sub_distrib (#t:Type) {| cr: commutative_ring t |}
                         (q a b: polynomial t)
  : Lemma (poly_eq (poly_mul q (poly_sub a b))
                   (poly_sub (poly_mul q a) (poly_mul q b)))

val add_rearrange (#t:Type) {| cr: commutative_ring t |}
                  (x y r1 r2: polynomial t)
  : Lemma (requires poly_eq (poly_add x r1) (poly_add y r2))
          (ensures  poly_eq (poly_sub x y) (poly_sub r2 r1))

val poly_divmod_unique (#t:Type) {| f: field t |}
                       (q a1 a2 r1 r2: polynomial t)
  : Lemma (requires
            Some? (poly_deg q) /\
            poly_eq (poly_add (poly_mul q a1) r1)
                    (poly_add (poly_mul q a2) r2) /\
            (None? (poly_deg r1) \/
             (Some? (poly_deg r1) /\
              Some?.v (poly_deg r1) < Some?.v (poly_deg q))) /\
            (None? (poly_deg r2) \/
             (Some? (poly_deg r2) /\
              Some?.v (poly_deg r2) < Some?.v (poly_deg q))))
          (ensures  poly_eq a1 a2 /\ poly_eq r1 r2)
