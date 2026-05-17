module FStar.CAS.Polynomial.GCD

(*
  Polynomial GCD over a field via the Euclidean algorithm.

  Defines: poly_divides, poly_gcd.
  Proves: GCD divides both inputs, GCD is maximal (any common divisor divides GCD),
          basic divisibility lemmas (divides_sum, divides_sub, divides_mul_right, etc.)
*)

open FStar.CAS.Equatable
open FStar.CAS.Grouplikes
open FStar.CAS.Ringlikes
open FStar.CAS.Polynomial
open FStar.CAS.Polynomial.Euclidean

module L = FStar.List.Tot.Base

(* Private helpers for nat arithmetic, since + is overloaded by Grouplikes *)
private let ( +% ) (x y: nat) : nat = Prims.op_Addition x y
private let ( -% ) (x y: nat{y <= x}) : nat = Prims.op_Subtraction x y

(* ====================================================================== *)
(*  TC-diamond helpers: extract all instances from field once              *)
(* ====================================================================== *)

let field_sr (#t:Type) (f: field t) : semiring t = f.division_ring.domain.ring.semiring
let field_hz (#t:Type) (f: field t) : has_zero t = semiring_has_zero (field_sr f)
let field_am (#t:Type) (f: field t) : add_monoid t = (field_sr f).add_comm_monoid.add_monoid
let field_rng (#t:Type) (f: field t) : ring t = f.division_ring.domain.ring
let field_g (#t:Type) (f: field t) : add_comm_group t = (field_rng f).add_comm_group

(* ====================================================================== *)
(*  Degree measure for termination                                         *)
(* ====================================================================== *)

let degree_measure (#t:Type) {| h: has_zero t |} (p: polynomial t) : nat =
  match degree p with
  | None -> 0
  | Some n -> n +% 1

let poly_mod_decreases_measure (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires Some? (degree q))
          (ensures degree_measure (poly_mod p q) < degree_measure q)
  = poly_divmod_degree p q

(* ====================================================================== *)
(*  Divisibility                                                           *)
(* ====================================================================== *)

let poly_divides (#t:Type) {| f: field t |} (d p: polynomial t) : bool =
  if None? (degree d) then None? (degree p)
  else None? (degree (poly_mod p d))

(* ====================================================================== *)
(*  Helper: degree of poly_zero is None                                     *)
(* ====================================================================== *)

let degree_poly_zero_field (#t:Type) {| f: field t |} (u: unit)
  : Lemma (degree #t #(field_hz f) (poly_zero #t) == None)
  = degree_poly_zero #t #(field_hz f) ()

(* ====================================================================== *)
(*  Simple divisibility lemmas                                              *)
(* ====================================================================== *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let divides_zero (#t:Type) {| f: field t |} (d: polynomial t)
  : Lemma (requires Some? (degree d))
          (ensures poly_divides d (poly_zero #t))
  = let sr = field_sr f in
    let hz = field_hz f in
    let am = field_am f in
    semiring_has_zero_unfold sr;
    let z : polynomial t = poly_zero #t in
    degree_poly_zero #t #hz ();
    // Strategy: show d*0 + 0 ≡ 0, then by uniqueness with divmod, poly_mod 0 d ≡ 0
    poly_mul_zero_right #t #sr d;
    poly_add_right_identity #t #am (poly_mul d z);
    poly_eq_transitivity #t #hz
      (poly_add (poly_mul d z) z) (poly_mul d z) z;
    poly_divmod_correct z d;
    poly_eq_symmetry #t #hz
      (poly_add (poly_mul d (poly_div z d)) (poly_mod z d)) z;
    poly_eq_transitivity #t #hz
      (poly_add (poly_mul d z) z) z
      (poly_add (poly_mul d (poly_div z d)) (poly_mod z d));
    poly_divmod_degree z d;
    poly_divmod_unique #t #f d z (poly_div z d) z (poly_mod z d);
    // uniqueness gives: poly_eq z (poly_mod z d)
    poly_eq_symmetry #t #hz z (poly_mod z d);
    degree_well_defined #t #hz (poly_mod z d) z
#pop-options

(* If d | p (with deg d ≥ 0), then d * (p/d) ≡ p *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let divides_implies_exact (#t:Type) {| f: field t |} (d p: polynomial t)
  : Lemma (requires Some? (degree d) /\ poly_divides d p)
          (ensures (let hz = field_hz f in
                    poly_eq #t #hz (poly_mul d (poly_div p d)) p))
  = let sr = field_sr f in
    let hz = field_hz f in
    let am = field_am f in
    semiring_has_zero_unfold sr;
    poly_divmod_correct p d;
    let q = poly_div p d in
    let r = poly_mod p d in
    // poly_divides d p means degree (poly_mod p d) = None
    // degree_none_poly_eq_zero: degree r = None → poly_eq r poly_zero
    degree_none_poly_eq_zero #t #f r;
    // Now: poly_eq r poly_zero, and poly_eq (poly_add (mul d q) r) p
    // Use congruence to replace r with poly_zero:
    poly_eq_reflexivity #t #hz (poly_mul d q);
    poly_add_congruence #t #am (poly_mul d q) r (poly_mul d q) (poly_zero #t);
    // Now: poly_eq (poly_add (mul d q) r) (poly_add (mul d q) poly_zero)
    poly_add_right_identity #t #am (poly_mul d q);
    // Now: poly_eq (poly_add (mul d q) poly_zero) (mul d q)
    poly_eq_transitivity #t #hz
      (poly_add (poly_mul d q) r) (poly_add (poly_mul d q) (poly_zero #t)) (poly_mul d q);
    // Now: poly_eq (poly_add (mul d q) r) (mul d q)
    poly_eq_symmetry #t #hz (poly_add (poly_mul d q) r) (poly_mul d q);
    // Now: poly_eq (mul d q) (poly_add (mul d q) r)
    poly_eq_transitivity #t #hz
      (poly_mul d q) (poly_add (poly_mul d q) r) p
#pop-options

(* ====================================================================== *)
(*  divides_sum: if d | q and d | r, then d | (q*a + r)                   *)
(*  This is the KEY workhorse for GCD correctness proofs.                  *)
(* ====================================================================== *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let divides_sum (#t:Type) {| f: field t |} (d q a r: polynomial t)
  : Lemma (requires Some? (degree d) /\ poly_divides d q /\ poly_divides d r)
          (ensures poly_divides d (poly_add (poly_mul q a) r))
  = let sr = field_sr f in
    let hz = field_hz f in
    let am = field_am f in
    semiring_has_zero_unfold sr;
    let p = poly_add (poly_mul q a) r in
    let qd = poly_div q d in
    let rd = poly_div r d in
    let c = poly_add #t #am (poly_mul qd a) rd in
    // Step A: d*qd ≡ q and d*rd ≡ r
    divides_implies_exact d q;
    divides_implies_exact d r;
    // Step B: (d*qd)*a ≡ q*a [mul congruence]
    poly_eq_reflexivity #t #hz a;
    poly_mul_congruence #t #sr (poly_mul d qd) a q a;
    // Step C: d*(qd*a) ≡ (d*qd)*a [associativity + symmetry]
    poly_mul_associative #t #sr d qd a;
    poly_eq_symmetry #t #hz (poly_mul (poly_mul d qd) a) (poly_mul d (poly_mul qd a));
    // Step D: d*(qd*a) ≡ q*a [trans: C + B]
    poly_eq_transitivity #t #hz
      (poly_mul d (poly_mul qd a)) (poly_mul (poly_mul d qd) a) (poly_mul q a);
    // Step E: d*(qd*a) + d*rd ≡ q*a + r [add congruence: D + A(rd)]
    poly_add_congruence #t #am
      (poly_mul d (poly_mul qd a)) (poly_mul d rd) (poly_mul q a) r;
    // Step F: d*c ≡ d*(qd*a) + d*rd [right distributivity]
    poly_mul_right_distrib #t #sr d (poly_mul qd a) rd;
    // Step G: d*c ≡ p [trans: F + E]
    poly_eq_transitivity #t #hz
      (poly_mul d c)
      (poly_add (poly_mul d (poly_mul qd a)) (poly_mul d rd))
      p;
    // Step H: d*c + 0 ≡ d*c
    poly_add_right_identity #t #am (poly_mul d c);
    poly_eq_symmetry #t #hz
      (poly_add (poly_mul d c) (poly_zero #t)) (poly_mul d c);
    // Step I: d*c + 0 ≡ p [trans: H + G]
    poly_eq_transitivity #t #hz
      (poly_add (poly_mul d c) (poly_zero #t)) (poly_mul d c) p;
    // Step J: d*(p/d) + (p mod d) ≡ p [divmod_correct on p by d]
    poly_divmod_correct p d;
    // Step K: d*c + 0 ≡ d*(p/d) + (p mod d) [both ≡ p, trans]
    poly_eq_symmetry #t #hz
      (poly_add (poly_mul d (poly_div p d)) (poly_mod p d)) p;
    poly_eq_transitivity #t #hz
      (poly_add (poly_mul d c) (poly_zero #t))
      p
      (poly_add (poly_mul d (poly_div p d)) (poly_mod p d));
    // Step L: by uniqueness, 0 ≡ p mod d
    poly_divmod_degree p d;
    degree_poly_zero_field #t #f ();
    poly_divmod_unique #t #f d c (poly_div p d) (poly_zero #t) (poly_mod p d);
    // Step M: degree (p mod d) = None
    poly_eq_symmetry #t #hz (poly_zero #t) (poly_mod p d);
    degree_well_defined #t #hz (poly_mod p d) (poly_zero #t)
#pop-options

(* ====================================================================== *)
(*  poly_divides_congruence: divisibility respects poly_eq                 *)
(* ====================================================================== *)

let poly_divides_congruence (#t:Type) {| f: field t |} (d p1 p2: polynomial t)
  : Lemma (requires Some? (degree d) /\
                   (let hz = field_hz f in poly_eq #t #hz p1 p2) /\
                   poly_divides d p1)
          (ensures poly_divides d p2)
  = let sr = field_sr f in
    let hz = field_hz f in
    semiring_has_zero_unfold sr;
    poly_mod_congruence #t #f p1 p2 d;
    degree_well_defined #t #hz (poly_mod #t #f p1 d) (poly_mod #t #f p2 d)

(* ====================================================================== *)
(*  divides_mod_implies_divides: d | q, d | (p mod q) → d | p             *)
(* ====================================================================== *)

let divides_mod_implies_divides (#t:Type) {| f: field t |}
  (d p q: polynomial t)
  : Lemma (requires Some? (degree d) /\ Some? (degree q) /\
                   poly_divides d q /\ poly_divides d (poly_mod p q))
          (ensures poly_divides d p)
  = let sr = field_sr f in
    let hz = field_hz f in
    semiring_has_zero_unfold sr;
    // p ≡ q*quot + r, so d | q and d | r → d | (q*quot + r) by divides_sum
    let quot = poly_div p q in
    let r = poly_mod p q in
    divides_sum d q quot r;
    // divides_sum gives: d | (q*quot + r)
    // poly_divmod_correct gives: poly_eq (q*quot + r) p
    poly_divmod_correct p q;
    // bridge: d | (q*quot + r) and (q*quot + r) ≡ p → d | p
    poly_divides_congruence d (poly_add (poly_mul q quot) r) p

(* ====================================================================== *)
(*  Self-divisibility: p | p                                               *)
(* ====================================================================== *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let divides_self (#t:Type) {| f: field t |} (p: polynomial t)
  : Lemma (requires Some? (degree p))
          (ensures poly_divides p p)
  = let sr = field_sr f in
    let hz = field_hz f in
    let am = field_am f in
    semiring_has_zero_unfold sr;
    poly_mul_one_right #t #sr p;
    poly_add_right_identity #t #am (poly_mul p (poly_one #t));
    poly_eq_transitivity #t #hz
      (poly_add (poly_mul p (poly_one #t)) (poly_zero #t))
      (poly_mul p (poly_one #t))
      p;
    poly_divmod_correct p p;
    poly_eq_symmetry #t #hz
      (poly_add (poly_mul p (poly_div p p)) (poly_mod p p)) p;
    poly_eq_transitivity #t #hz
      (poly_add (poly_mul p (poly_one #t)) (poly_zero #t))
      p
      (poly_add (poly_mul p (poly_div p p)) (poly_mod p p));
    poly_divmod_degree p p;
    degree_poly_zero_field #t #f ();
    poly_divmod_unique #t #f p (poly_one #t) (poly_div p p) (poly_zero #t) (poly_mod p p);
    poly_eq_symmetry #t #hz (poly_zero #t) (poly_mod p p);
    degree_well_defined #t #hz (poly_mod p p) (poly_zero #t)
#pop-options

(* Divisibility of poly_zero: p | q when degree q = None *)
let divides_zero_degree (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires Some? (degree p) /\
                   (let hz = field_hz f in degree #t #hz q == None))
          (ensures poly_divides p q)
  = let sr = field_sr f in
    let hz = field_hz f in
    semiring_has_zero_unfold sr;
    divides_zero p;
    degree_none_poly_eq_zero #t #f q;
    poly_eq_symmetry #t #hz q (poly_zero #t);
    poly_divides_congruence p (poly_zero #t) q

(* ====================================================================== *)
(*  GCD definition                                                         *)
(* ====================================================================== *)

let rec poly_gcd (#t:Type) {| f: field t |} (p q: polynomial t)
  : Tot (polynomial t) (decreases (degree_measure q))
  = if None? (degree q) then p
    else begin
      poly_mod_decreases_measure p q;
      poly_gcd q (poly_mod p q)
    end

(* ====================================================================== *)
(*  GCD divides both inputs                                                *)
(* ====================================================================== *)

let rec gcd_divides_first (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (ensures (Some? (degree (poly_gcd p q)) ==>
                    poly_divides (poly_gcd p q) p))
          (decreases (degree_measure q))
  = let sr = field_sr f in
    semiring_has_zero_unfold sr;
    if None? (degree q) then begin
      if Some? (degree p) then divides_self p else ()
    end
    else begin
      poly_mod_decreases_measure p q;
      let r = poly_mod p q in
      gcd_divides_first q r;
      gcd_divides_second q r;
      if Some? (degree (poly_gcd q r)) then
        divides_mod_implies_divides (poly_gcd q r) p q
      else ()
    end

and gcd_divides_second (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (ensures (Some? (degree (poly_gcd p q)) ==>
                    poly_divides (poly_gcd p q) q))
          (decreases (degree_measure q))
  = let sr = field_sr f in
    semiring_has_zero_unfold sr;
    if None? (degree q) then begin
      if Some? (degree p) then
        divides_zero_degree p q
      else ()
    end
    else begin
      poly_mod_decreases_measure p q;
      gcd_divides_first q (poly_mod p q)
    end

(* ====================================================================== *)
(*  Sub-congruence helper (for divides_sub)                                *)
(* ====================================================================== *)

let poly_sub_congruence (#t:Type) {| f: field t |}
  (a b c d_: polynomial t)
  : Lemma (requires (let hz = field_hz f in
                     poly_eq #t #hz a b /\ poly_eq #t #hz c d_))
          (ensures (let hz = field_hz f in
                    poly_eq #t #hz (poly_sub a c) (poly_sub b d_)))
  = let sr = field_sr f in
    let hz = field_hz f in
    let am = field_am f in
    let g = field_g f in
    semiring_has_zero_unfold sr;
    poly_sub_unfold #t #g a c;
    poly_sub_unfold #t #g b d_;
    poly_neg_congruence #t #g c d_;
    poly_add_congruence #t #am a (poly_neg c) b (poly_neg d_)

(* ====================================================================== *)
(*  divides_sub: d | p, d | q → d | (p - q)                               *)
(* ====================================================================== *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let divides_sub (#t:Type) {| f: field t |} (d p q: polynomial t)
  : Lemma (requires Some? (degree d) /\ poly_divides d p /\ poly_divides d q)
          (ensures poly_divides d (poly_sub p q))
  = let sr = field_sr f in
    let hz = field_hz f in
    let am = field_am f in
    let rng = field_rng f in
    let g = field_g f in
    semiring_has_zero_unfold sr;
    let pd = poly_div p d in
    let qd = poly_div q d in
    let c = poly_sub #t #g pd qd in
    // A: d*pd ≡ p, d*qd ≡ q
    divides_implies_exact d p;
    divides_implies_exact d q;
    // B: d*c ≡ d*pd - d*qd [poly_mul_sub_distrib]
    poly_mul_sub_distrib #t #rng d pd qd;
    // C: d*pd - d*qd ≡ p - q [sub congruence]
    poly_sub_congruence #t #f (poly_mul d pd) p (poly_mul d qd) q;
    // Oops, direction: sub_congruence(d*pd, p, d*qd, q) gives (d*pd - d*qd) ≡ (p - q)
    // D: d*c ≡ p - q [trans: B + C]
    poly_eq_transitivity #t #hz
      (poly_mul d c)
      (poly_sub (poly_mul d pd) (poly_mul d qd))
      (poly_sub p q);
    // E: d*c + 0 ≡ d*c ≡ p - q
    poly_add_right_identity #t #am (poly_mul d c);
    poly_eq_symmetry #t #hz
      (poly_add (poly_mul d c) (poly_zero #t)) (poly_mul d c);
    poly_eq_transitivity #t #hz
      (poly_add (poly_mul d c) (poly_zero #t)) (poly_mul d c) (poly_sub p q);
    // F: d*(div) + (mod) ≡ p - q [divmod_correct]
    let s = poly_sub p q in
    poly_divmod_correct s d;
    // G: uniqueness → mod ≡ 0
    poly_eq_symmetry #t #hz
      (poly_add (poly_mul d (poly_div s d)) (poly_mod s d)) s;
    poly_eq_transitivity #t #hz
      (poly_add (poly_mul d c) (poly_zero #t)) s
      (poly_add (poly_mul d (poly_div s d)) (poly_mod s d));
    poly_divmod_degree s d;
    degree_poly_zero_field #t #f ();
    poly_divmod_unique #t #f d c (poly_div s d) (poly_zero #t) (poly_mod s d);
    poly_eq_symmetry #t #hz (poly_zero #t) (poly_mod s d);
    degree_well_defined #t #hz (poly_mod s d) (poly_zero #t)
#pop-options

(* ====================================================================== *)
(*  divides_mul_right: d | p → d | (p * a)                                *)
(* ====================================================================== *)

let divides_mul_right (#t:Type) {| f: field t |} (d p a: polynomial t)
  : Lemma (requires Some? (degree d) /\ poly_divides d p)
          (ensures poly_divides d (poly_mul p a))
  = let sr = field_sr f in
    let hz = field_hz f in
    let am = field_am f in
    semiring_has_zero_unfold sr;
    // Use divides_sum: d | p and d | 0 → d | (p*a + 0)
    divides_zero d;
    divides_sum d p a (poly_zero #t);
    // Bridge: (p*a + 0) ≡ p*a
    poly_add_right_identity #t #am (poly_mul p a);
    poly_divides_congruence d (poly_add (poly_mul p a) (poly_zero #t)) (poly_mul p a)

(* ====================================================================== *)
(*  poly_add_left_cancel: avoids ring_add_left_cancellation TC diamond     *)
(* ====================================================================== *)

let poly_add_left_cancel (#t:Type) {| f: field t |} (a b c: polynomial t)
  : Lemma (requires (let hz = field_hz f in poly_eq #t #hz (poly_add a b) (poly_add a c)))
          (ensures (let hz = field_hz f in poly_eq #t #hz b c))
  = let sr = field_sr f in
    let hz = field_hz f in
    let am = field_am f in
    let g = field_g f in
    semiring_has_zero_unfold sr;
    let na = poly_neg #t #g a in
    poly_eq_reflexivity #t #hz na;
    poly_add_congruence #t #am na (poly_add a b) na (poly_add a c);
    let simplify (x: polynomial t)
      : Lemma (poly_eq #t #hz (poly_add na (poly_add a x)) x)
      = poly_add_associative #t #am na a x;
        poly_eq_symmetry #t #hz
          (poly_add (poly_add na a) x) (poly_add na (poly_add a x));
        poly_neg_inversion #t #g a;
        poly_eq_reflexivity #t #hz x;
        poly_add_congruence #t #am (poly_add na a) x (poly_zero #t) x;
        poly_add_left_identity #t #am x;
        poly_eq_transitivity #t #hz
          (poly_add na (poly_add a x)) (poly_add (poly_add na a) x) (poly_add (poly_zero #t) x);
        poly_eq_transitivity #t #hz
          (poly_add na (poly_add a x)) (poly_add (poly_zero #t) x) x
    in
    simplify b;
    simplify c;
    poly_eq_symmetry #t #hz (poly_add na (poly_add a b)) b;
    poly_eq_transitivity #t #hz
      b (poly_add na (poly_add a b)) (poly_add na (poly_add a c));
    poly_eq_transitivity #t #hz b (poly_add na (poly_add a c)) c

(* ====================================================================== *)
(*  divides_mod: d | p, d | q → d | (p mod q)                             *)
(* ====================================================================== *)

let divides_mod (#t:Type) {| f: field t |} (d p q: polynomial t)
  : Lemma (requires Some? (degree d) /\ Some? (degree q) /\
                   poly_divides d p /\ poly_divides d q)
          (ensures poly_divides d (poly_mod p q))
  = let sr = field_sr f in
    let hz = field_hz f in
    let am = field_am f in
    let g = field_g f in
    semiring_has_zero_unfold sr;
    let quot = poly_div p q in
    let r = poly_mod p q in
    // d | (q*quot) from d | q
    divides_mul_right d q quot;
    // d | (p - q*quot) from d | p and d | (q*quot)
    divides_sub d p (poly_mul q quot);
    // From divmod: q*quot + r ≡ p
    poly_divmod_correct p q;
    // From group: q*quot + (p - q*quot) ≡ p
    poly_add_sub_cancel #t #g (poly_mul q quot) p;
    // Both are q*quot + X ≡ p. By left cancellation: r ≡ p - q*quot.
    poly_eq_symmetry #t #hz (poly_add (poly_mul q quot) (poly_sub p (poly_mul q quot))) p;
    poly_eq_transitivity #t #hz
      (poly_add (poly_mul q quot) r) p
      (poly_add (poly_mul q quot) (poly_sub p (poly_mul q quot)));
    poly_add_left_cancel #t #f (poly_mul q quot) r (poly_sub p (poly_mul q quot));
    // Bridge: d | (p - q*quot) and (p - q*quot) ≡ r → d | r
    poly_eq_symmetry #t #hz r (poly_sub p (poly_mul q quot));
    poly_divides_congruence d (poly_sub p (poly_mul q quot)) r

(* ====================================================================== *)
(*  GCD is maximal: any common divisor divides gcd(p,q)                   *)
(* ====================================================================== *)

let rec gcd_is_maximal (#t:Type) {| f: field t |} (p q d: polynomial t)
  : Lemma (requires Some? (degree d) /\
                   poly_divides d p /\ poly_divides d q)
          (ensures poly_divides d (poly_gcd p q))
          (decreases (degree_measure q))
  = let sr = field_sr f in
    semiring_has_zero_unfold sr;
    if None? (degree q) then ()
    else begin
      poly_mod_decreases_measure p q;
      divides_mod d p q;
      gcd_is_maximal q (poly_mod p q) d
    end
