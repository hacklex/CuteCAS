module Core.Risch.AnswerCheck

(* ================================================================ *)
(*  VERIFIED ANSWER CHECKER — the trust cap for the integrator.      *)
(*                                                                   *)
(*  Given a candidate antiderivative `a` (rational part + a list of  *)
(*  logarithmic terms cᵢ·log(vᵢ)) and an integrand p/q, `check`      *)
(*  SYMBOLICALLY DIFFERENTIATES `a` and compares to p/q.  A `true`    *)
(*  verdict is a MACHINE-CHECKED guarantee that                      *)
(*                                                                   *)
(*      d/dx [ ratl + Σ cᵢ·log(vᵢ) ]  =  p/q      (as fractions).     *)
(*                                                                   *)
(*  The whole integrator can be distrusted and a user still gets a   *)
(*  per-answer certificate from this small verified core.            *)
(*                                                                   *)
(*  The derivative is assembled from proven pieces:                  *)
(*    - rational part:  `rational_deriv` (the quotient rule, proven  *)
(*      by `rational_deriv_reveal` = (P'Q − PQ')/Q²);                *)
(*    - each log term:  d/dx[c·log v] = c·v'/v  as the fraction       *)
(*      Fraction (poly_scale c (poly_deriv v)) v  (v ≠ 0).           *)
(*                                                                   *)
(*  SCOPE: the rational-constant answer form (coefficients cᵢ : t).  *)
(*  The RootSum / algebraic-constant log part is a later extension.  *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L = FStar.List.Tot

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Roots        (* poly_scale *)
open Core.Polynomial.Derivative   (* poly_deriv *)
open Core.Fractions
open Core.Fractions.Derivative     (* rational_function, rational_deriv, rational_deriv_reveal *)

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(* ---------------------------------------------------------------- *)
(*  A single logarithmic term  c · log(v)  with v ≠ 0.               *)
(* ---------------------------------------------------------------- *)
let log_term (#t:Type) {| f: field t |} = (t & (v:polynomial t{is_nonzero v}))

(* ---------------------------------------------------------------- *)
(*  The candidate answer:  a rational function plus Σ cᵢ·log(vᵢ).    *)
(* ---------------------------------------------------------------- *)
noeq type answer_form (#t:Type) {| f: field t |} = {
  ratl: rational_function f;      (* the combined rational part P + G/H *)
  logs: list (log_term #t #f);    (* the log terms  cᵢ · log(vᵢ)        *)
}

(* ---------------------------------------------------------------- *)
(*  d/dx [ c · log v ]  =  c · v' / v  =  (c·v') / v   as a fraction.*)
(* ---------------------------------------------------------------- *)
let log_deriv_term (#t:Type) {| f: field t |} (cv: log_term #t #f)
  : rational_function f
  = let (c, v) = cv in
    Fraction #(polynomial t) #(polynomial_id #t)
             (poly_scale c (poly_deriv v)) v

(* d/dx [ Σ cᵢ·log(vᵢ) ]  =  Σ (cᵢ·vᵢ') / vᵢ   (folded as one fraction). *)
let rec log_part_deriv (#t:Type) {| f: field t |} (logs: list (log_term #t #f))
  : rational_function f
  = match logs with
    | []       -> fraction_zero (polynomial t) #(polynomial_id #t)
    | cv :: tl -> fraction_add (log_deriv_term cv) (log_part_deriv tl)

(* ---------------------------------------------------------------- *)
(*  The full derivative of the answer:                               *)
(*    d/dx [ ratl + Σ cᵢ·log(vᵢ) ]  =  D(ratl) ⊕ Σ (cᵢ·vᵢ')/vᵢ .     *)
(* ---------------------------------------------------------------- *)
let answer_deriv (#t:Type) {| f: field t |} (a: answer_form #t #f)
  : rational_function f
  = fraction_add (rational_deriv a.ratl) (log_part_deriv a.logs)

(* ---------------------------------------------------------------- *)
(*  THE CHECKER.  Tot, decidable: cross-multiply and compare with    *)
(*  polynomial equality (the `=` on `fraction (polynomial_id t)`).   *)
(* ---------------------------------------------------------------- *)
let check (#t:Type) {| f: field t |}
  (a: answer_form #t #f)
  (p: polynomial t) (q: polynomial t{is_nonzero q})
  : bool
  = (answer_deriv a) = Fraction #(polynomial t) #(polynomial_id #t) p q

(* ================================================================ *)
(*  SOUNDNESS.                                                        *)
(* ================================================================ *)

(* The primary guarantee a consumer needs: `check` returning true      *)
(* means the symbolic derivative of the answer equals the integrand    *)
(* p/q (as fractions, i.e. cross-multiplied polynomial equality).      *)
let check_sound (#t:Type) {| f: field t |}
  (a: answer_form #t #f)
  (p: polynomial t) (q: polynomial t{is_nonzero q})
  : Lemma (requires check a p q)
          (ensures  (answer_deriv a)
                      = Fraction #(polynomial t) #(polynomial_id #t) p q)
  = ()

(* ================================================================ *)
(*  answer_deriv IS the formal derivative of the answer TREE.         *)
(*                                                                   *)
(*  The following reveal lemmas tie `answer_deriv` — the value the    *)
(*  checker actually compares — to the term-by-term formal            *)
(*  derivation of  ratl + Σ cᵢ·log(vᵢ):                               *)
(*    (1) it splits as D(ratl) ⊕ D(log part)  [additivity of D];     *)
(*    (2) the rational part IS the proven quotient rule (P'Q−PQ')/Q²; *)
(*    (3) the log part folds Σ (cᵢ·vᵢ')/vᵢ  term by term;             *)
(*    (4) each log term IS the log-derivative  (c·v') / v.            *)
(* ================================================================ *)

(* (1) additivity: D(answer) = D(rational part) ⊕ D(log part). *)
let answer_deriv_decomp (#t:Type) {| f: field t |} (a: answer_form #t #f)
  : Lemma (answer_deriv a
             == fraction_add (rational_deriv a.ratl) (log_part_deriv a.logs))
  = ()

(* (2) the rational part of the derivative is the genuine quotient rule:
       num = P'·Q − P·Q',  den = Q².  (Reuses the proven reveal.) *)
let answer_deriv_rational_quotient_rule (#t:Type) {| f: field t |}
  (a: answer_form #t #f)
  : Lemma (Fraction?.num (rational_deriv a.ratl)
             == ((poly_deriv (Fraction?.num a.ratl) * Fraction?.den a.ratl)
                 -- (Fraction?.num a.ratl * poly_deriv (Fraction?.den a.ratl))) /\
           Fraction?.den (rational_deriv a.ratl)
             == (Fraction?.den a.ratl * Fraction?.den a.ratl))
  = rational_deriv_reveal a.ratl

(* (3) the log part unfolds term by term:  Σ  =  head ⊕ Σ(tail). *)
let log_part_deriv_cons (#t:Type) {| f: field t |}
  (cv: log_term #t #f) (tl: list (log_term #t #f))
  : Lemma (log_part_deriv (cv :: tl)
             == fraction_add (log_deriv_term cv) (log_part_deriv tl))
  = ()

(* (4) the log-derivative identity:  d/dx[c·log v] = (c·v') / v. *)
let log_deriv_term_reveal (#t:Type) {| f: field t |}
  (c: t) (v: polynomial t{is_nonzero v})
  : Lemma (let cv : log_term #t #f = (c, v) in
           Fraction?.num (log_deriv_term cv) == poly_scale c (poly_deriv v) /\
           Fraction?.den (log_deriv_term cv) == v)
  = ()

(* ================================================================ *)
(*  UPSHOT.  Combining check_sound with the decomposition above:     *)
(*  a `true` verdict certifies that the formal derivative of the      *)
(*  answer — D(ratl) ⊕ Σ (cᵢ·vᵢ')/vᵢ — equals the integrand p/q.     *)
(* ================================================================ *)
let check_certifies_derivative (#t:Type) {| f: field t |}
  (a: answer_form #t #f)
  (p: polynomial t) (q: polynomial t{is_nonzero q})
  : Lemma (requires check a p q)
          (ensures  (fraction_add (rational_deriv a.ratl) (log_part_deriv a.logs))
                      = Fraction #(polynomial t) #(polynomial_id #t) p q)
  = ()
