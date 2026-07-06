module Core.Fractions.DerivationInstance

(*
   Differential structure on ℚ(x) (rational functions) packaged as a
   `derivation_on` record (§F Phase-3 umbrella object).

   We wrap `rational_deriv` (the quotient-rule derivative from
   Core.Fractions.Derivative) together with its additivity, Leibniz, and
   congruence proofs (Core.Fractions.DerivativeSum) into the foundation's
   `derivation_on` record, targeting the commutative_ring of
   `fraction id_p` PROJECTED from the one published `fraction_field`
   instance (no new instances introduced — diamond-free).
*)

module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Fractions
open Core.Fractions.Derivative
open Core.Fractions.DerivativeSum
open Core.Algebra.Derivation

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* The commutative_ring on `fraction id_p`, obtained by projection from the
   single published `fraction_field` instance via the foundation chain
   id_of_f ∘ cr_of_id.  No new instance is published. *)
let cr_fr (#t:Type) {| f: field t |}
  : commutative_ring (fraction (polynomial_id #t #(id_of_f t)))
  = let id_p = polynomial_id #t #(id_of_f t) in
    cr_of_id (fraction id_p) #(id_of_f (fraction id_p) #(fraction_field (polynomial t) id_p))

(* ---------------------------------------------------------------- *)
(*  Field helpers of the derivation record.                          *)
(*                                                                   *)
(*  Each obligation is stated with the ring ops/eq of `cr_fr`.       *)
(*  The reveal lemmas `fraction_ring_add_reveal` /                   *)
(*  `fraction_ring_mul_reveal` collapse the published `+`/`*` to     *)
(*  `fraction_add`/`fraction_mul` (Leibniz `==`), so the DerivativeSum*)
(*  lemmas (stated over `fraction_add`/`fraction_mul`) discharge the *)
(*  `=` goal directly.                                               *)
(* ---------------------------------------------------------------- *)

let rcong_field (#t:Type) {| f: field t |}
  (a b: fraction (polynomial_id #t #(id_of_f t)))
  : Lemma (requires a = b)
          (ensures (rational_deriv a) = (rational_deriv b))
  = rational_deriv_cong a b

let radd_field (#t:Type) {| f: field t |}
  (a b: fraction (polynomial_id #t #(id_of_f t)))
  : Lemma (ensures (rational_deriv (a + b))
                   = ((rational_deriv a) + (rational_deriv b)))
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    (* (a + b) == fraction_add a b, so rational_deriv (a+b) is the SAME term
       as rational_deriv (fraction_add a b). *)
    fraction_ring_add_reveal a b;
    (* rational_deriv (fraction_add a b) = fraction_add (Da) (Db) *)
    rational_deriv_add a b;
    (* (Da + Db) == fraction_add (Da) (Db), so RHS matches. *)
    fraction_ring_add_reveal
      (rational_deriv a) (rational_deriv b)

let rmul_field (#t:Type) {| f: field t |}
  (a b: fraction (polynomial_id #t #(id_of_f t)))
  : Lemma (ensures (rational_deriv (a * b))
                   = (((rational_deriv a) * b)
                      + (a * (rational_deriv b))))
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    (* (a * b) == fraction_mul a b *)
    fraction_ring_mul_reveal a b;
    (* rational_deriv (fraction_mul a b)
         = fraction_add (fraction_mul (Da) b) (fraction_mul a (Db)) *)
    rational_deriv_mul a b;
    (* collapse the two products and the outer sum on the RHS *)
    fraction_ring_mul_reveal (rational_deriv a) b;
    fraction_ring_mul_reveal a (rational_deriv b);
    fraction_ring_add_reveal
      ((rational_deriv a) * b) (a * (rational_deriv b))

(* ---------------------------------------------------------------- *)
(*  The rational-function derivation (§F Phase-3 umbrella object).   *)
(* ---------------------------------------------------------------- *)

let rational_derivation (#t:Type) {| f: field t |}
  : derivation_on #(fraction (polynomial_id #t #(id_of_f t)))
                  cr_fr
  = {
    deriv            = rational_deriv;
    deriv_congruence = rcong_field;
    deriv_add        = radd_field;
    deriv_leibniz    = rmul_field;
  }

(* ---------------------------------------------------------------- *)
(*  Corollaries: constants have zero derivative on ℚ(x), etc.        *)
(*                                                                   *)
(*  Each just instantiates the generic derived lemma from            *)
(*  Core.Algebra.Derivation at `rational_derivation`.  Since the     *)
(*  record field `deriv` is `fun x -> rational_deriv x`, the         *)
(*  conclusion (stated over `rational_deriv`) matches the generic    *)
(*  lemma's `d.deriv` by normalization.  The `zero`/`one`/`neg`/`+`  *)
(*  are the `cr_fr` ring ops, exactly as the generic lemma delivers. *)
(* ---------------------------------------------------------------- *)

let rational_deriv_zero (#t:Type) {| f: field t |}
  : Lemma (rational_deriv (zero <: fraction (polynomial_id #t #(id_of_f t)))
             = (zero <: fraction (polynomial_id #t #(id_of_f t))))
  = deriv_zero (rational_derivation #t #f)

let rational_deriv_one (#t:Type) {| f: field t |}
  : Lemma (rational_deriv (one <: fraction (polynomial_id #t #(id_of_f t)))
             = (zero <: fraction (polynomial_id #t #(id_of_f t))))
  = deriv_one (rational_derivation #t #f)

let rational_deriv_neg (#t:Type) {| f: field t |}
  (a: fraction (polynomial_id #t #(id_of_f t)))
  : Lemma (rational_deriv ((- a)) = (- (rational_deriv a)))
  = deriv_neg (rational_derivation #t #f) a

let rational_deriv_sub (#t:Type) {| f: field t |}
  (a b: fraction (polynomial_id #t #(id_of_f t)))
  : Lemma (rational_deriv (a + (- b))
           = (rational_deriv a) + (- (rational_deriv b)))
  = deriv_sub (rational_derivation #t #f) a b
