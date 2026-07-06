module Core.Risch.RationalSplitField

(* ================================================================ *)
(*  Rational-integrator soundness RELATIVE TO A SPLITTING FIELD of   *)
(*  the squarefree denominator — the UNCONDITIONAL version.          *)
(*                                                                   *)
(*  The log part is discharged by the already-proven                 *)
(*  `rt_answer_constructed` (the LRT answer's derivative folded over  *)
(*  the constructed residue-class partition equals p/q), NOT left as  *)
(*  a hypothesis.                                                     *)
(*                                                                   *)
(*  Three lemmas:                                                     *)
(*   (1) split_sound_frac — Euclidean split with the proper-part      *)
(*       DERIVATIVE as an abstract fraction `pd`.                     *)
(*   (2) proper_part_sound_split — proper-part soundness relative to  *)
(*       a splitting field (UNCONDITIONAL).                           *)
(*   (3) rational_single_factor_sound_split — full single-factor      *)
(*       soundness relative to a splitting field (UNCONDITIONAL).     *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                        *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module PA = Core.Risch.PolyAntideriv
module RP = Core.Risch.ResiduePartition

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree
open Core.Polynomial.Irreducible
open Core.Polynomial.Roots
open Core.Fractions
open Core.Fractions.Derivative
open Core.Risch.Hermite
open Core.Risch.HermiteFracLift
open Core.Risch.RationalSound
open Core.Risch.RationalEuclid
open Core.Risch.RTSoundness
open Core.Risch.RTAnswerEnd

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  (1)  Euclidean split, fraction-derivative-abstract version.      *)
(*                                                                   *)
(*  Same as `rational_split_sound` (Core.Risch.RationalSplit) but     *)
(*  with the proper-part DERIVATIVE supplied as an abstract fraction  *)
(*  `pd = Fraction rem q`, since the true log part's derivative is    *)
(*  `answer_deriv`, not `rational_deriv` of a rational function.      *)
(* ================================================================ *)
let split_sound_frac (#t:Type) {| f: field t |}
  (p q quot rem: polynomial t)
  (pd: fraction (polynomial_id #t #(id_of_f t)))
  : Lemma (requires char_zero f /\ is_nonzero q /\
                    p = (quot * q) + rem /\
                    pd = Fraction rem q)
          (ensures
            (fraction_add
               (rational_deriv (poly_to_rational (PA.antideriv quot)))
               pd)
            = (Fraction p q))
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    let a   : fraction id_p =
      rational_deriv (poly_to_rational (PA.antideriv quot)) in
    let b   : fraction id_p = pd in
    let pq  : fraction id_p = poly_to_rational quot in
    let rq  : fraction id_p = Fraction rem q in
    let rhs : fraction id_p = fraction_add pq rq in
    (* (1)  a = poly_to_rational quot. *)
    poly_part_correct quot;
    (* (2)  b = pd = Fraction rem q   (hypothesis). *)
    (* (3)  Fraction p q = fraction_add (poly_to_rational quot) (Fraction rem q). *)
    euclid_fraction_identity p q quot rem;
    (* LHS congruence:  fraction_add a b = fraction_add pq rq. *)
    frac_add_cong   a pq b;          (* a+b = pq+b *)
    frac_add_cong_r pq b rq;          (* pq+b = pq+rq *)
    transitivity (fraction_add a b)
                 (fraction_add pq b)
                 rhs;
    (* chain with the (symmetric) Euclidean identity. *)
    symmetry (Fraction p q) rhs;
    transitivity (fraction_add a b)
                 rhs
                 (Fraction p q)

(* ================================================================ *)
(*  (2)  Proper-part soundness relative to a splitting field         *)
(*       (UNCONDITIONAL).                                             *)
(*                                                                   *)
(*    D( nn / d^(n-1) )  (+)  answer_deriv final roots (partition)    *)
(*       =  rem / d^n                                                 *)
(*                                                                   *)
(*  The log part `answer_deriv final roots (residue_partition …)` is  *)
(*  discharged by `rt_answer_constructed`: since d = ∏ (X - root),    *)
(*  it equals  final / d.                                            *)
(* ================================================================ *)
let proper_part_sound_split (#t:Type) {| f: field t |}
  (rem d: polynomial t) (n: nat{n >= 1}) (roots: list t)
  : Lemma (requires deg d >= 0 /\ square_free d /\ char_zero f /\
                    Cons? roots /\ all_distinct roots /\
                    d == poly_prod_linears roots /\
                    deg (snd (hermite_reduce_power rem d n)) < L.length roots)
          (ensures
            fraction_add
              (rational_deriv
                 (Fraction
                    (combined_num (fst (hermite_reduce_power rem d n)) d)
                    (poly_power d (n - 1))))
              (answer_deriv (snd (hermite_reduce_power rem d n)) roots
                 (RP.residue_partition (snd (hermite_reduce_power rem d n)) roots))
            = Fraction rem (poly_power d n))
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    let (parts, final) = hermite_reduce_power rem d n in
    let nn   = combined_num parts d in
    let dm   = poly_power d (n - 1) in
    let dn   = poly_power d n in
    let hf   = Fraction nn dm in
    (* is_nonzero d  (from d = ∏ linears over Cons? roots). *)
    prod_linears_nonzero roots;
    let ffinal = Fraction final d in
    (* (1)  answer_deriv final roots (residue_partition final roots)
            = Fraction final (poly_prod_linears roots) = Fraction final d. *)
    rt_answer_constructed final roots;
    (* (2)  right-congruence: rewrite the second summand from answer_deriv to ffinal. *)
    frac_add_cong_r
      (rational_deriv hf)
      (answer_deriv final roots (RP.residue_partition final roots))
      ffinal;
    (* (3)  Hermite fraction identity:  D(hf) (+) final/d = rem / d^n. *)
    hermite_fraction_identity rem d n;
    (* chain over fraction id_p. *)
    transitivity
      (fraction_add
         (rational_deriv hf)
         (answer_deriv final roots (RP.residue_partition final roots)))
      (fraction_add (rational_deriv hf) ffinal)
      (Fraction rem dn)

(* ================================================================ *)
(*  (3)  Full single-factor soundness relative to a splitting field  *)
(*       (UNCONDITIONAL headline).                                    *)
(*                                                                   *)
(*    D( ∫quot )  (+)                                                 *)
(*      ( D( nn / d^(n-1) )  (+)  answer_deriv final roots (part.) )  *)
(*        =  p / d^n                                                  *)
(* ================================================================ *)
let rational_single_factor_sound_split (#t:Type) {| f: field t |}
  (p d: polynomial t) (n: nat{n >= 1}) (roots: list t)
  : Lemma (requires deg d >= 0 /\ square_free d /\ char_zero f /\
                    Cons? roots /\ all_distinct roots /\
                    d == poly_prod_linears roots /\
                    deg (snd (hermite_reduce_power
                               (snd (poly_divmod p (poly_power d n))) d n))
                       < L.length roots)
          (ensures
            fraction_add
              (rational_deriv
                 (poly_to_rational (PA.antideriv (fst (poly_divmod p (poly_power d n))))))
              (fraction_add
                 (rational_deriv
                    (Fraction
                       (combined_num
                          (fst (hermite_reduce_power
                                  (snd (poly_divmod p (poly_power d n))) d n))
                          d)
                       (poly_power d (n - 1))))
                 (answer_deriv
                    (snd (hermite_reduce_power
                            (snd (poly_divmod p (poly_power d n))) d n))
                    roots
                    (RP.residue_partition
                       (snd (hermite_reduce_power
                               (snd (poly_divmod p (poly_power d n))) d n))
                       roots)))
            = Fraction p (poly_power d n))
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let dn   = poly_power d n in
    let (quot, rem) = poly_divmod p dn in
    let (parts, final) = hermite_reduce_power rem d n in
    let nn   = combined_num parts d in
    (* (1)  Euclidean split, flipped product:  p ~ quot·dn + rem.
            poly_eq p (poly_add (poly_mul dn quot) rem) is auto-adjoined
            from the `let (quot, rem) = poly_divmod p dn` binding above. *)
    poly_mul_commutativity dn quot;
    poly_add_congruence
      (dn * quot) rem (quot * dn) rem;
    poly_eq_transitivity
      p
      ((dn * quot) + rem)
      ((quot * dn) + rem);
    (* (2)  is_nonzero dn  (from deg d >= 0, n >= 1). *)
    poly_power_has_degree d n;
    poly_zero_is_unique (poly_power d n);
    (* (3)  proper-part soundness relative to the splitting field:
            pd = D(nn/d^(n-1)) (+) answer_deriv … = Fraction rem dn. *)
    let pd : fraction id_p =
      fraction_add
        (rational_deriv (Fraction nn (poly_power d (n - 1))))
        (answer_deriv final roots (RP.residue_partition final roots)) in
    proper_part_sound_split rem d n roots;
    (* (4)  Compose with the Euclidean split. *)
    split_sound_frac p dn quot rem pd
