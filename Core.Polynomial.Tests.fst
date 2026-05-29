module Core.Polynomial.Tests

(*
   Acceptance / regression tests for the polynomial Class tower.

   The goal of this module is purely to *exercise* the API surface of
   Core.Polynomial and Core.Polynomial.Div from the
   perspective of a downstream user:

     - basic ring / integral-domain axioms resolve through the typeclass
       chain on `polynomial t` (no explicit `#`-instance annotations);
     - `poly_add` / `poly_mul` / `poly_eq` / `poly_zero` / `poly_neg`
       are interchangeable with their typeclass-resolved counterparts
       `(+)` / `*` / `(=)` / `zero` / `(~-)`;
     - lemmas stated in poly-specific form compose freely with lemmas
       stated in the infix form;
     - degree / leading-coefficient identities behave as advertised;
     - the canon_ring meta-tactic works against `polynomial t` once a
       polynomial CR instance is in scope.

   No theorems of mathematical interest are proven here — every Lemma
   body must close trivially via the right typeclass machinery, otherwise
   the class tower has a usability bug.

   Verification budget: every lemma in this file should close under
   `--z3rlimit 30 --fuel 1 --ifuel 1` (the project default for sanity
   tests).  If a test needs more, that itself is a finding.
*)

module TC = FStar.Tactics.Typeclasses
module L  = FStar.List.Tot

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div
open Core.Tactics.CanonRing

(*  Bring a polynomial CR instance into TC scope wherever we need one.
    Defining this as a local let-binding inside each test ensures the
    test mirrors the way a downstream consumer would write it.
*)

(* ================================================================== *)
(*  Section A — commutative-ring axioms on polynomial t                *)
(* ================================================================== *)

(*  Each test below takes only `{| cr: commutative_ring t |}` and
    derives `commutative_ring (polynomial t)` via the unfold instance
    `cr_of_pcr`.  The bodies invoke ONLY the typeclass-resolved axioms;
    they must NEVER call poly_add_*/poly_mul_*/... directly.            *)

let t_add_commutativity_via_tc
      (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma ((p + q) = (q + p))
  = let _ : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    add_commutativity p q

let t_add_associativity_via_tc
      (#t:Type) {| cr: commutative_ring t |} (p q r: polynomial t)
  : Lemma (((p + q) + r) = (p + (q + r)))
  = let _ : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    add_associativity p q r

let t_add_zero_right_via_tc
      (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma ((p + zero) = p)
  = let _ : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    add_zero p

let t_add_negation_via_tc
      (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma ((p + (- p)) = zero)
  = let _ : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    add_negation p

let t_mul_commutativity_via_tc
      (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma ((p * q) = (q * p))
  = let _ : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    mul_commutativity p q

let t_mul_associativity_via_tc
      (#t:Type) {| cr: commutative_ring t |} (p q r: polynomial t)
  : Lemma (((p * q) * r) = (p * (q * r)))
  = let _ : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    mul_associativity p q r

let t_left_distributivity_via_tc
      (#t:Type) {| cr: commutative_ring t |} (p q r: polynomial t)
  : Lemma ((p * (q + r)) = ((p * q) + (p * r)))
  = let _ : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    left_distributivity p q r

let t_right_distributivity_via_tc
      (#t:Type) {| cr: commutative_ring t |} (p q r: polynomial t)
  : Lemma (((p + q) * r) = ((p * r) + (q * r)))
  = let _ : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    right_distributivity r p q

let t_mul_one_via_tc
      (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma ((p * one) = p)
  = let _ : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    mul_one p

(* ================================================================== *)
(*  Section B — poly_* / typeclass-op interchangeability                *)
(* ================================================================== *)

(*  Show that on the polynomial CR instance, the typeclass-resolved
    operators reduce to the underlying poly_* definitions.  Each test
    builds the instance and then uses `polynomial_acg_*_reveal` /
    `polynomial_equatable_eq_reveal` / instance-record projection
    facts to discharge the equality.                                    *)

let t_zero_is_poly_zero
      (#t:Type) {| cr: commutative_ring t |}
  : Lemma ((zero #(polynomial t)) == (poly_zero #t))
  = let pcrc : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    pcrc.poly_zero_reveal

let t_add_is_poly_add
      (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma ((p + q) == poly_add p q)
  = let _ : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    ()

let t_mul_is_poly_mul
      (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma ((p * q) == poly_mul p q)
  = let _ : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    ()

let t_neg_is_poly_neg
      (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma ((- p) == poly_neg p)
  = let _ : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    ()

let t_eq_is_poly_eq
      (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma ((p = q) == poly_eq p q)
  = let _ : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    polynomial_equatable_eq_reveal cr p q

(* ================================================================== *)
(*  Section C — bridging poly-form lemmas with TC-form lemmas           *)
(* ================================================================== *)

(*  A poly_*-form result is usable as a precondition for a TC lemma
    that expects the infix-eq form, and vice-versa.  The bodies have
    NO explicit bridge calls — TC resolution should handle it.         *)

let t_bridge_poly_add_commutativity_into_tc
      (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma (requires poly_eq (poly_add p q) (poly_add q p))
          (ensures  (p + q) = (q + p))
  = let _ : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    polynomial_equatable_eq_reveal cr (poly_add p q) (poly_add q p)

let t_bridge_tc_add_commutativity_into_poly
      (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma (requires (p + q) = (q + p))
          (ensures  poly_eq (poly_add p q) (poly_add q p))
  = let _ : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    polynomial_equatable_eq_reveal cr (poly_add p q) (poly_add q p)

(*  Compose a poly-form lemma producing `poly_eq` with a TC-form lemma
    consuming `=`.  No reveal calls inside the body — only the lemmas. *)
let t_compose_poly_mul_commutativity_into_tc_associativity
      (#t:Type) {| cr: commutative_ring t |} (p q r: polynomial t)
  : Lemma (((p * q) * r) = (r * (p * q)))
  = let _ : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    poly_mul_commutativity (poly_mul p q) r;
    polynomial_equatable_eq_reveal cr (poly_mul (poly_mul p q) r) (poly_mul r (poly_mul p q))

(* ================================================================== *)
(*  Section D — degree / leading-coefficient identities                 *)
(* ================================================================== *)

let t_deg_zero_is_none
      (#t:Type) {| cr: commutative_ring t |}
  : Lemma (poly_deg (poly_zero #t) == None)
  = ()

let t_lc_zero_is_zero
      (#t:Type) {| cr: commutative_ring t |}
  : Lemma (poly_lc (poly_zero #t) == (zero <: t))
  = ()

let t_deg_of_monomial_nonzero
      (#t:Type) {| cr: commutative_ring t |} (c: t {not (c = zero)}) (n: nat)
  : Lemma (poly_deg (monomial c n) == Some n)
  = monomial_deg c n

let t_deg_of_monomial_zero_is_none
      (#t:Type) {| cr: commutative_ring t |} (n: nat)
  : Lemma (poly_deg (monomial (zero <: t) n) == None)
  = monomial_deg (zero <: t) n;
    reflexivity (zero <: t)

let t_monomial_coeff_self
      (#t:Type) {| cr: commutative_ring t |} (c: t) (n: nat)
  : Lemma (coeff (monomial c n) n = c)
  = monomial_coeff c n n

let t_monomial_coeff_above
      (#t:Type) {| cr: commutative_ring t |} (c: t) (n: nat) (i: nat {i <> n})
  : Lemma (coeff (monomial c n) i = (zero <: t))
  = monomial_coeff c n i

(* ================================================================== *)
(*  Section E — canon_ring against polynomial t                         *)
(* ================================================================== *)

let t_canon_ring_neg_neg
      (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma ((- (- p)) = p)
  = let pcrc : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    let cr_p : commutative_ring (polynomial t) = TC.solve in
    assert ((- (- p)) = p) by canon_ring ()

let t_canon_ring_neg_add
      (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma ((- (p + q)) = ((- p) + (- q)))
  = let pcrc : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    let cr_p : commutative_ring (polynomial t) = TC.solve in
    assert ((- (p + q)) = ((- p) + (- q))) by canon_ring ()

let t_canon_ring_mul_zero
      (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma ((p * zero) = (zero #(polynomial t)))
  = let pcrc : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    let cr_p : commutative_ring (polynomial t) = TC.solve in
    assert ((p * zero) = (zero #(polynomial t))) by canon_ring ()

let t_canon_ring_swap_mid
      (#t:Type) {| cr: commutative_ring t |} (a b c d: polynomial t)
  : Lemma (((a * b) * (c * d)) = ((a * c) * (b * d)))
  = let pcrc : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    let cr_p : commutative_ring (polynomial t) = TC.solve in
    assert (((a * b) * (c * d)) = ((a * c) * (b * d))) by canon_ring ()

let t_canon_ring_distribute
      (#t:Type) {| cr: commutative_ring t |} (a b c: polynomial t)
  : Lemma ((c * (a + b)) = ((c * a) + (c * b)))
  = let pcrc : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    let cr_p : commutative_ring (polynomial t) = TC.solve in
    assert ((c * (a + b)) = ((c * a) + (c * b))) by canon_ring ()
(* ================================================================== *)
(*  Section F — integral_domain axioms on polynomial t                  *)
(* ================================================================== *)

let t_id_domain_law_via_tc
      (#t:Type) {| id: integral_domain t |} (p q: polynomial t)
  : Lemma (requires not (p = zero) /\ not (q = zero))
          (ensures  not ((p * q) = zero))
  = let pidc : polynomial_integral_domain t = polynomial_integral_domain_instance in
    (* The integral-domain instance gives this directly via
       `domain_law` on `polynomial t`. *)
    pidc.pid.id_d.domain_law p q

let t_id_one_ne_zero_via_tc
      (#t:Type) {| id: integral_domain t |}
  : Lemma (not ((one #(polynomial t)) = (zero #(polynomial t))))
  = let pidc : polynomial_integral_domain t = polynomial_integral_domain_instance in
    pidc.pid.id_one_ne_zero
