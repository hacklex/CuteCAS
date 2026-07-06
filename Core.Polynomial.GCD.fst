module Core.Polynomial.GCD

(*
   Implementation of polynomial GCD via the Euclidean algorithm.
   See the .fsti for the exposed surface and the deferred-work notes.
*)

module H  = Core.Algebra.Helpers
module L  = FStar.List.Tot

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Unique

(* ------------------------------------------------------------------ *)
(*  Termination measure                                               *)
(* ------------------------------------------------------------------ *)

let degree_measure (#t:Type) {| cr: commutative_ring t |}
                   (p: polynomial t) : nat
  = L.length p

let degree_measure_zero_iff_zero
    (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (degree_measure p == 0 <==> deg p < 0)
  = ()

(* Generic CR helper: from `c = a + b`, conclude `c + -a = b`.
   Used to bridge `poly_divmod_correct` to a divisibility-of-remainder
   statement in the polynomial commutative ring. *)
private let cancel_helper
    (#t:Type) {| cr: commutative_ring t |} (a b c: t)
  : Lemma (requires c = a + b)
          (ensures  c + -a = b)
  = H.elim_equatable_laws t ();
    add_congruence c (-a) (a + b) (-a);
    assert ((a + b) + -a = b) by Core.Tactics.CanonRing.canon_ring ();
    transitivity (c + -a) ((a + b) + -a) b

(* Key termination lemma. *)
private let degree_measure_decreases
    (#t:Type) {| f: field t |}
    (p q: polynomial t)
  : Lemma (requires deg q >= 0)
          (ensures  (let (_, r) = poly_divmod p q in
                     degree_measure r < degree_measure q))
  = let _ = poly_rem p q in ()

(* ------------------------------------------------------------------ *)
(*  Euclidean GCD                                                     *)
(* ------------------------------------------------------------------ *)

let rec poly_gcd (#t:Type) {| f: field t |} (p q: polynomial t)
  : Tot (polynomial t) (decreases (degree_measure q))
  = if deg q < 0 then p
    else begin
      let (_, r) = poly_divmod p q in
      degree_measure_decreases p q;
      poly_gcd q r
    end

let poly_gcd_base
    (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires deg q < 0)
          (ensures  poly_gcd p q == p)
  = ()

let poly_gcd_step
    (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires deg q >= 0)
          (ensures  (let (_, r) = poly_divmod p q in
                     poly_gcd p q == poly_gcd q r))
  = ()

(* ------------------------------------------------------------------ *)
(*  GCD divisibility: gcd | p AND gcd | q                             *)
(*                                                                    *)
(*  Proven jointly via induction on `degree_measure q`.               *)
(* ------------------------------------------------------------------ *)

let rec gcd_divides_both
    (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (ensures  divides (poly_gcd p q) p /\
                    divides (poly_gcd p q) q)
          (decreases (degree_measure q))
  = let g = poly_gcd p q in
    if deg q < 0 then begin
      divides_refl p;
      (* deg q < 0 ⟹ q = []; poly_zero #t == ([] <: polynomial t) *)
      assert (q == (poly_zero #t));
      divides_zero p
    end
    else begin
      let (qot, r) = poly_divmod p q in
      degree_measure_decreases p q;
      gcd_divides_both q r;
      (* IH: divides g q  AND  divides g r *)
      assert (g == poly_gcd q r);
      divides_mul_right g q qot;
      divides_add g (q * qot) r;
      let s = ((q * qot) + r) in
      symmetry p s;
      divides_congruence_right g s p
    end

let gcd_divides_left
    (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (divides (poly_gcd p q) p)
  = gcd_divides_both p q

let gcd_divides_right
    (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (divides (poly_gcd p q) q)
  = gcd_divides_both p q

(* ------------------------------------------------------------------ *)
(*  GCD maximality: d | p ∧ d | q ⟹ d | gcd p q                       *)
(* ------------------------------------------------------------------ *)

let rec gcd_is_maximal
    (#t:Type) {| f: field t |} (p q d: polynomial t)
  : Lemma (requires divides d p /\ divides d q)
          (ensures  divides d (poly_gcd p q))
          (decreases (degree_measure q))
  = if deg q < 0 then ()
    else begin
        let (qot, r) = poly_divmod p q in
        degree_measure_decreases p q;
        divides_mul_right d q qot;
        divides_sub d p (q * qot);
        cancel_helper (q * qot) r p;
        divides_congruence_right d (p + -(q * qot)) r;
        gcd_is_maximal q r d
    end

(* ------------------------------------------------------------------ *)
(*  Extended GCD (Bézout)                                             *)
(* ------------------------------------------------------------------ *)

(* CR helper: base-case identity 1*p + 0*q = p.  Single-CR scope so
   canon_ring picks the right instance. *)
private let bezout_base_helper
    (#t:Type) {| cr: commutative_ring t |} (p q: t)
  : Lemma ((one * p + zero * q) = p)
  = assert ((one * p + zero * q) = p)
      by Core.Tactics.CanonRing.canon_ring ()

(* CR helper: step-case Bézout rearrangement.

   Given:
     p ~ q*quot + rem                               (poly_divmod_correct)
     a'*q + b'*rem ~ gv                             (IH)
   Conclude:
     b'*p + (a' - b'*quot)*q ~ gv

   The intermediate identity
     b'*(q*quot + rem) + (a' - b'*quot)*q  ==  a'*q + b'*rem
   is pure CR algebra and is discharged by canon_ring.  We chain it
   together with mul_congruence (substituting p) and transitivity. *)
private let bezout_step_helper
    (#t:Type) {| cr: commutative_ring t |}
    (q quot rem b' a' p gv: t)
  : Lemma (requires (p = q * quot + rem) /\
                    (a' * q + b' * rem = gv))
          (ensures  (b' * p + (a' + -(b' * quot)) * q = gv))
  = H.elim_equatable_laws t ();
    let coeff_term = a' + -(b' * quot) in
    let lhs = b' * p + coeff_term * q in
    let mid = b' * (q * quot + rem) + coeff_term * q in
    let rhs = a' * q + b' * rem in
    (* b' * p ~ b' * (q * quot + rem) *)
    mul_congruence b' p b' (q * quot + rem);
    (* lhs ~ mid by congruence of (+) on the left summand *)
    add_congruence (b' * p) (coeff_term * q)
                   (b' * (q * quot + rem)) (coeff_term * q);
    (* mid = rhs (pure CR identity).  Spell both sides out (don't reuse the
       let-bound `mid`/`rhs`) so canon_ring doesn't see them as opaque atoms. *)
    assert ((b' * (q * quot + rem) + (a' + -(b' * quot)) * q)
              = (a' * q + b' * rem))
      by Core.Tactics.CanonRing.canon_ring ();
    (* lhs ~ mid ~ rhs ~ gv *)
    transitivity lhs mid rhs;
    transitivity lhs rhs gv

let rec poly_ext_gcd (#t:Type) {| f: field t |} (p q: polynomial t)
  : Tot (polynomial t & polynomial t & polynomial t)
  = if deg q < 0 then (one, zero, p)
    else begin
        let (quot, r) = poly_divmod p q in
        degree_measure_decreases p q;
        let (a', b', gv) = poly_ext_gcd q r in
        (b', a' + -(b' * quot), gv)
    end

let rec ext_gcd_correct (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (ensures (let (a, b, g) = poly_ext_gcd p q in
                    ((a * p + b * q) = g)))
  =
    if deg q < 0 then
        bezout_base_helper p q
    else begin
        let (quot, r) = poly_divmod p q in
        degree_measure_decreases p q;
        ext_gcd_correct q r;
        let (a', b', gv) = poly_ext_gcd q r in
        (* poly_divmod's ensures adjoins: poly_eq p (poly_add (poly_mul q quot) r) *)
        bezout_step_helper q quot r b' a' p gv
    end

let rec ext_gcd_is_gcd (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (ensures (let (_, _, g) = poly_ext_gcd p q in
                    (g = poly_gcd p q)))
  = if deg q < 0 then
        poly_eq_reflexivity p
    else begin
        let r = poly_rem p q in
        degree_measure_decreases p q;
        ext_gcd_is_gcd q r
    end


(* ================================================================== *)
(*  GCD congruence                                                    *)
(* ================================================================== *)

(* CR-level helper: from x1 ~ y1*a1 + r1, x2 ~ y2*a2 + r2, x1 ~ x2, y1 ~ y2,
   conclude y1*a1 + r1 ~ y1*a2 + r2.  Single-CR scope to dodge the
   canon_ring carrier-resolution bug. *)
private let gcd_chain_helper
    (#t:Type) {| cr: commutative_ring t |}
    (y1 y2 x1 x2 a1 a2 r1 r2: t)
  : Lemma (requires (x1 = y1 * a1 + r1) /\
                    (x2 = y2 * a2 + r2) /\
                    (x1 = x2) /\ (y1 = y2))
          (ensures  (y1 * a1 + r1 = y1 * a2 + r2))
  = H.elim_equatable_laws t ();
    transitivity (y1 * a1 + r1) x1 x2;
    transitivity (y1 * a1 + r1) x2 (y2 * a2 + r2);
    mul_congruence y1 a2 y2 a2;
    add_congruence (y1 * a2) r2 (y2 * a2) r2;
    transitivity (y1 * a1 + r1)
                 (y2 * a2 + r2)
                 (y1 * a2 + r2)

let rec gcd_congruence (#t:Type) {| f: field t |}
                       (x1 x2 y1 y2: polynomial t)
  : Lemma (requires (x1 = x2) /\ (y1 = y2))
          (ensures  (poly_gcd x1 y1 = poly_gcd x2 y2))
  = degree_well_defined y1 y2;
    if deg y1 < 0 then begin
        poly_gcd_base x1 y1;
        poly_gcd_base x2 y2
    end
    else begin
        let (a1, r1) = poly_divmod x1 y1 in
        let (a2, r2) = poly_divmod x2 y2 in
        gcd_chain_helper y1 y2 x1 x2 a1 a2 r1 r2;
        poly_divmod_unique y1 a1 a2 r1 r2;
        poly_gcd_step x1 y1;
        poly_gcd_step x2 y2;
        degree_measure_decreases x1 y1;
        gcd_congruence y1 y2 r1 r2
    end


(* ================================================================== *)
(*  Chain instances: gcd_domain → ufd → euclidean_domain              *)
(* ================================================================== *)

instance polynomial_gcd_domain_instance
    (#t:Type) {| f: field t |}
  : gcd_domain (polynomial t)
  = {
    gcd_id            = polynomial_id;
    gcd               = poly_gcd;
    gcd_congruence    = gcd_congruence;
    gcd_divides_left  = gcd_divides_left;
    gcd_divides_right = gcd_divides_right;
    gcd_is_maximal    = gcd_is_maximal;
  }

instance polynomial_ufd_instance
    (#t:Type) {| f: field t |}
  : ufd (polynomial t)
  = { ufd_gd = polynomial_gcd_domain_instance }

private let poly_euclidean_norm
    (#t:Type) {| cr: commutative_ring t |} (p: polynomial t) : nat
  = if deg p < 0 then 0 else deg p

(* norm_monotonicity for the degree norm: for nonzero p, q over a field
   `deg (p * q) = deg p + deg q >= deg p`, so the norm cannot decrease. *)
private let poly_norm_monotonicity
    (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires is_nonzero p /\ is_nonzero q)
          (ensures  poly_euclidean_norm p <= poly_euclidean_norm (p * q))
  = poly_zero_is_unique p;
    poly_zero_is_unique q;
    deg_mul p q

(* Single division primitive whose `Pure` postcondition carries correctness
   AND the strict norm-decrease (folds the former poly_ed_divmod_correct /
   _decreasing into one). *)
private let poly_ed_divmod
    (#t:Type) {| f: field t |} (p q: polynomial t)
  : Pure (polynomial t & polynomial t)
         (requires is_nonzero q)
         (ensures  fun (a, r) -> p = ((q * a) + r) /\
                                 (is_nonzero r ==> poly_euclidean_norm r < poly_euclidean_norm q))
  = poly_zero_is_unique q;
    let (a, r) = poly_divmod p q in
    (if deg r >= 0 then poly_zero_is_unique r);
    (a, r)

instance polynomial_euclidean_domain_chain_instance
    (#t:Type) {| f: field t |}
  : euclidean_domain (polynomial t)
  = {
    ed_ufd            = polynomial_ufd_instance;
    euclidean_norm    = poly_euclidean_norm;
    norm_monotonicity = poly_norm_monotonicity;
    divmod            = poly_ed_divmod;
  }

(* ================================================================== *)
(*  Coprimality and Euclid's lemma                                    *)
(* ================================================================== *)

let coprime (#t:Type) {| f: field t |} (p q: polynomial t) : bool
  = deg (poly_gcd p q) = 0

let coprime_reveal (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (coprime p q = (deg (poly_gcd p q) = 0))
  = ()


(* ================================================================== *)
(*  Euclid's lemma: coprime(p, q) /\ p | a*q  ⟹  p | a                *)
(* ================================================================== *)

(* When poly_deg p = Some 0, the polynomial is a singleton list whose
   sole element is its leading coefficient and is nonzero. *)
let degree_zero_is_singleton
    (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (requires deg p == 0)
          (ensures  p == [poly_lc p] /\ not (poly_lc p = zero))
  = leading_coeff_nonzero p;
    assert (L.length p == 1);
    match p with
    | [a] -> assert (poly_lc p == a)

(* For c <> zero, the singleton [inv c] times the singleton [c] equals
   poly_one (the polynomial-ring identity).  Proven via direct list
   inspection and the field inversion law. *)
let singleton_inv_mul_singleton
    (#t:Type) {| f: field t |} (c: t)
  : Lemma (requires not (c = zero))
          (ensures [inv c] * [c] = poly_one)
  = let cinv = inv c in
    let lhs : polynomial t = [cinv] in
    let rhs : polynomial t = [c] in
    (* monomial cinv 0 == [cinv] (since cinv <> zero) *)
    monomial_zero_n_reveal cinv;
    assert (monomial cinv 0 == lhs);
    (* coeff (poly_mul lhs rhs) 0 = cinv * coeff rhs 0 = cinv * c *)
    monomial_mul_coeff cinv 0 rhs 0;
    assert (coeff (lhs * rhs) 0 = cinv * c);
    (* By field inversion: cinv * c ~ one *)
    inversion_lemma c;
    assert ((cinv * c) = one);
    transitivity (coeff (lhs * rhs) 0) (cinv * c) one;
    (* For i >= 1: coeff above degree is zero on both sides.
       poly_deg lhs = Some 0, poly_deg rhs = Some 0,
       poly_deg (poly_mul lhs rhs) = either None or Some 0 (it's a
       product of two trimmed singletons; either result is [(cinv*c)]
       if nonzero, or [] if cinv*c = zero — but cinv*c = one ≠ zero,
       so product is [(cinv*c)], degree 0). *)
    let aux (i:nat) : Lemma (coeff (lhs * rhs) i = coeff (poly_one #t) i)
      = if i = 0 then ()
        else begin
          (* poly_mul lhs rhs has degree at most 0+0 = 0 by monomial product *)
          monomial_mul_coeff cinv 0 rhs i;
          assert (coeff (lhs * rhs) i = cinv * coeff rhs i);
          (* coeff rhs i = zero for i >= 1 *)
          coeff_above_degree rhs i;
          assert (coeff rhs i = zero);
          reflexivity cinv;
          mul_congruence cinv (coeff rhs i) cinv zero;
          assert ((cinv * zero) = zero)
            by Core.Tactics.CanonRing.canon_ring ();
          transitivity (cinv * coeff rhs i) (cinv * zero) zero;
          transitivity (coeff (lhs * rhs) i) (cinv * coeff rhs i) zero;
          (* coeff poly_one i for i >= 1 = zero *)
          coeff_above_degree (poly_one #t) i;
          symmetry (coeff (poly_one #t) i) zero;
          transitivity (coeff (lhs * rhs) i) zero (coeff (poly_one #t) i)
        end
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (lhs * rhs) (poly_one #t)

(* CR helper: a + b ~ a*1 + b in polynomial CR — but we need the
   euclid_lemma-shaped algebraic identity.  This helper assembles
   p | a*s*p, p | (a*q)*t, into p | a*g where g ~ s*p + t*q. *)
private let euclid_bezout_helper
    (#t:Type) {| cr: commutative_ring t |}
    (p q a s tt g: t)
  : Lemma (requires (s * p + tt * q = g))
          (ensures  (a * (s * p) + a * (tt * q) = a * g))
  = H.elim_equatable_laws t ();
    mul_congruence a (s * p + tt * q) a g;
    assert ((a * (s * p + tt * q)) = (a * (s * p) + a * (tt * q)))
      by Core.Tactics.CanonRing.canon_ring ();
    transitivity (a * (s * p) + a * (tt * q))
                 (a * (s * p + tt * q))
                 (a * g)

(* Helper: p | x  /\  eq y x  ⟹  p | y  is just divides_congruence_right
   with a small twist of argument order.  Also pre-bundle: a*(s*p) = (a*s)*p
   so p | (a*s)*p follows from p | p*c via divides_mul_right. *)
private let divides_a_times_sp
    (#t:Type) {| cr: commutative_ring t |} (p a s: t)
  : Lemma (divides p (a * (s * p)))
  = divides_refl p;
    divides_mul_right p p (a * s);
    assert ((p * (a * s)) = (a * (s * p)))
      by Core.Tactics.CanonRing.canon_ring ();
    divides_congruence_right p (p * (a * s)) (a * (s * p))

private let divides_a_times_tq
    (#t:Type) {| cr: commutative_ring t |} (p a q tt: t)
  : Lemma (requires divides p (a * q))
          (ensures  divides p (a * (tt * q)))
  = divides_mul_right p (a * q) tt;
    assert (((a * q) * tt) = (a * (tt * q)))
      by Core.Tactics.CanonRing.canon_ring ();
    divides_congruence_right p ((a * q) * tt) (a * (tt * q))

(* CR helper: a*1 ~ a. *)
private let mul_one_right_helper
    (#t:Type) {| cr: commutative_ring t |} (a: t)
  : Lemma (a * one = a)
  = assert (a * one = a) by Core.Tactics.CanonRing.canon_ring ()

let euclid_lemma (#t:Type) {| f: field t |} (p q a: polynomial t)
  : Lemma (requires deg p >= 0 /\
                    coprime p q /\
                    divides p (a * q))
          (ensures  divides p a)
  = H.elim_equatable_laws (polynomial t) ();
    let g = poly_gcd p q in
    assert (deg g == 0);
    ext_gcd_correct p q;
    ext_gcd_is_gcd  p q;
    let (s, tt, gv) = poly_ext_gcd p q in
    (* gv ~ g *)
    (* Step 1: p | a*s*p *)
    divides_a_times_sp p a s;
    (* Step 2: p | a*tt*q (from p | a*q given) *)
    divides_a_times_tq p a q tt;
    (* Step 3: p | a*s*p + a*tt*q *)
    divides_add p (a * (s * p)) (a * (tt * q));
    (* Step 4: a*s*p + a*tt*q ~ a * (s*p + tt*q) ~ a * gv (via Bezout) *)
    euclid_bezout_helper p q a s tt gv;
    divides_congruence_right p (a * (s * p) + a * (tt * q)) (a * gv);
    (* Step 5: gv ~ g, so a*gv ~ a*g *)
    mul_congruence a gv a g;
    divides_congruence_right p (a * gv) (a * g);
    (* Step 6: g = [c] for some c ≠ zero (degree_zero_is_singleton) *)
    degree_zero_is_singleton g;
    let c : t = poly_lc g in
    assert (g == [c]);
    assert (not (c = zero));
    let cinv : t = inv c in
    let g_inv : polynomial t = [cinv] in
    (* Step 7: poly_mul g_inv g ~ poly_one *)
    singleton_inv_mul_singleton c;
    assert ((g_inv * g) = poly_one);
    (* Step 8: p | (a*g) * g_inv = a * (g * g_inv) ~ a * (g_inv * g) ~ a*1 ~ a *)
    divides_mul_right p (a * g) g_inv;
    (* (a*g)*g_inv ~ a*(g*g_inv) ~ a*(g_inv*g) ~ a*poly_one ~ a *)
    let assoc_helper (#u:Type) {| cr: commutative_ring u |} (x y z: u)
      : Lemma ((x * y) * z = x * (y * z))
      = assert ((x * y) * z = x * (y * z))
          by Core.Tactics.CanonRing.canon_ring ()
    in
    let comm_helper (#u:Type) {| cr: commutative_ring u |} (x y: u)
      : Lemma (x * y = y * x)
      = assert (x * y = y * x) by Core.Tactics.CanonRing.canon_ring ()
    in
    assoc_helper a g g_inv;
    comm_helper g g_inv;
    mul_congruence a (g * g_inv) a (g_inv * g);
    transitivity ((a * g) * g_inv) (a * (g * g_inv)) (a * (g_inv * g));
    mul_congruence a (g_inv * g) a poly_one;
    transitivity ((a * g) * g_inv) (a * (g_inv * g)) (a * poly_one);
    mul_one_right_helper a;
    transitivity ((a * g) * g_inv) (a * poly_one) a;
    divides_congruence_right p ((a * g) * g_inv) a
