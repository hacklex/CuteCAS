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
let field_acm (#t:Type) (f: field t) : add_comm_monoid t = (field_sr f).add_comm_monoid
let field_cr (#t:Type) (f: field t) : commutative_ring t = f.commutative_ring

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

(* ====================================================================== *)
(*  Extended GCD: Bézout identity                                          *)
(* ====================================================================== *)

(* Helper: (a + b) + (c + neg(a)) ≡ b + c
   All poly_add/poly_neg, no poly_sub in the goal to avoid TC diamond *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let poly_add_neg_rearrange (#t:Type) {| f: field t |} (a b c: polynomial t)
  : Lemma (let am = field_am f in
           let g = field_g f in
           let hz = field_hz f in
           let na = poly_neg #t #g a in
           poly_eq #t #hz
             (poly_add #t #am (poly_add #t #am a b) (poly_add #t #am c na))
             (poly_add #t #am b c))
  = let sr = field_sr f in
    let hz = field_hz f in
    let am = field_am f in
    let g = field_g f in
    let acm = field_acm f in
    semiring_has_zero_unfold sr;
    let na = poly_neg #t #g a in
    let add = poly_add #t #am in
    // (a+b)+(c+na) → a+(b+(c+na))
    poly_add_associative #t #am a b (add c na);
    // c+na → na+c
    poly_add_commutative #t #acm c na;
    // b+(c+na) ≡ b+(na+c)
    poly_eq_reflexivity #t #hz b;
    poly_add_congruence #t #am b (add c na) b (add na c);
    // (b+na)+c ≡ b+(na+c) [standard assoc direction]
    poly_add_associative #t #am b na c;
    // b+(na+c) ≡ (b+na)+c
    poly_eq_symmetry #t #hz (add (add b na) c) (add b (add na c));
    // b+(c+na) ≡ (b+na)+c
    poly_eq_transitivity #t #hz (add b (add c na)) (add b (add na c)) (add (add b na) c);
    // a+(b+(c+na)) ≡ a+((b+na)+c)
    poly_eq_reflexivity #t #hz a;
    poly_add_congruence #t #am a (add b (add c na)) a (add (add b na) c);
    // (a+(b+na))+c ≡ a+((b+na)+c) [standard assoc direction]
    poly_add_associative #t #am a (add b na) c;
    // a+((b+na)+c) ≡ (a+(b+na))+c
    poly_eq_symmetry #t #hz (add (add a (add b na)) c) (add a (add (add b na) c));
    // (a+b)+(c+na) ≡ (a+(b+na))+c
    poly_eq_transitivity #t #hz
      (add (add a b) (add c na))
      (add a (add b (add c na)))
      (add a (add (add b na) c));
    poly_eq_transitivity #t #hz
      (add (add a b) (add c na))
      (add a (add (add b na) c))
      (add (add a (add b na)) c);
    // Now: (a+(b+na)) ≡ b
    // (a+b)+na ≡ a+(b+na) [standard assoc]
    poly_add_associative #t #am a b na;
    // (a+b)+na ≡ na+(a+b)
    poly_add_commutative #t #acm (add a b) na;
    // na+(a+b) ≡ (na+a)+b [reverse assoc]
    poly_add_associative #t #am na a b;
    poly_eq_symmetry #t #hz (add (add na a) b) (add na (add a b));
    // (a+b)+na ≡ (na+a)+b
    poly_eq_transitivity #t #hz (add (add a b) na) (add na (add a b)) (add (add na a) b);
    // na+a ≡ 0
    poly_neg_inversion #t #g a;
    // (na+a)+b ≡ 0+b
    poly_eq_reflexivity #t #hz b;
    poly_add_congruence #t #am (add na a) b (poly_zero #t) b;
    // 0+b ≡ b
    poly_add_left_identity #t #am b;
    // (a+b)+na ≡ b
    poly_eq_transitivity #t #hz (add (add a b) na) (add (add na a) b) (add (poly_zero #t) b);
    poly_eq_transitivity #t #hz (add (add a b) na) (add (poly_zero #t) b) b;
    // a+(b+na) ≡ b
    poly_eq_symmetry #t #hz (add (add a b) na) (add a (add b na));
    poly_eq_transitivity #t #hz (add a (add b na)) (add (add a b) na) b;
    // (a+(b+na))+c ≡ b+c
    poly_eq_reflexivity #t #hz c;
    poly_add_congruence #t #am (add a (add b na)) c b c;
    // (a+b)+(c+na) ≡ b+c
    poly_eq_transitivity #t #hz
      (add (add a b) (add c na))
      (add (add a (add b na)) c)
      (add b c)
#pop-options

(* Extended GCD: returns (a, b, g) where a*p + b*q ≡ g = gcd(p,q) *)
let rec poly_ext_gcd (#t:Type) {| f: field t |} (p q: polynomial t)
  : Tot (polynomial t & polynomial t & polynomial t)
    (decreases (degree_measure q))
  = let sr = field_sr f in
    semiring_has_zero_unfold sr;
    if None? (degree q) then
      (poly_one #t, poly_zero #t, p)
    else begin
      poly_mod_decreases_measure p q;
      let (a', b', g) = poly_ext_gcd q (poly_mod p q) in
      let quot = poly_div p q in
      (b', poly_sub #t #(field_g f) a' (poly_mul #t #sr b' quot), g)
    end

(* Bézout identity: ext_gcd returns (a, b, g) such that a*p + b*q ≡ g *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let rec ext_gcd_correct (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (ensures (let sr = field_sr f in
                    let hz = field_hz f in
                    let am = field_am f in
                    let (a, b, g) = poly_ext_gcd p q in
                    poly_eq #t #hz
                      (poly_add #t #am (poly_mul #t #sr a p) (poly_mul #t #sr b q))
                      g))
          (decreases (degree_measure q))
  = let sr = field_sr f in
    let hz = field_hz f in
    let am = field_am f in
    let g = field_g f in
    let acm = field_acm f in
    let cr = field_cr f in
    let rng = field_rng f in
    semiring_has_zero_unfold sr;
    let add = poly_add #t #am in
    let mul = poly_mul #t #sr in
    let neg = poly_neg #t #g in
    let sub = poly_sub #t #g in
    if None? (degree q) then begin
      let one_p = poly_one #t in
      let zero_p = poly_zero #t in
      poly_mul_one_left #t #sr p;
      poly_mul_zero_left #t #sr q;
      poly_eq_reflexivity #t #hz (mul one_p p);
      poly_add_congruence #t #am (mul one_p p) (mul zero_p q) (mul one_p p) zero_p;
      poly_add_right_identity #t #am (mul one_p p);
      poly_eq_transitivity #t #hz
        (add (mul one_p p) (mul zero_p q))
        (add (mul one_p p) zero_p)
        (mul one_p p);
      poly_eq_transitivity #t #hz (add (mul one_p p) (mul zero_p q)) (mul one_p p) p
    end
    else begin
      poly_mod_decreases_measure p q;
      ext_gcd_correct q (poly_mod p q);
      let (a', b', gv) = poly_ext_gcd q (poly_mod p q) in
      let quot = poly_div p q in
      let r = poly_mod p q in
      // IH: a'*q + b'*r ≡ gv.  Need: b'*p + (sub a' (mul b' quot))*q ≡ gv
      // (1) p ≡ q*quot + r  then (2) b'*p ≡ b'*(q*quot + r) ≡ b'*(q*quot) + b'*r
      poly_divmod_correct p q;
      poly_eq_reflexivity #t #hz b';
      poly_eq_symmetry #t #hz (add (mul q quot) r) p;
      poly_mul_congruence #t #sr b' p b' (add (mul q quot) r);
      poly_mul_right_distrib #t #sr b' (mul q quot) r;
      poly_eq_transitivity #t #hz
        (mul b' p) (mul b' (add (mul q quot) r))
        (add (mul b' (mul q quot)) (mul b' r));
      // (5) b'*(q*quot) ≡ (b'*quot)*q via comm then assoc
      poly_mul_commutative #t #cr q quot;
      poly_eq_reflexivity #t #hz b';
      poly_mul_congruence #t #sr b' (mul q quot) b' (mul quot q);
      poly_mul_associative #t #sr b' quot q;
      poly_eq_symmetry #t #hz (mul (mul b' quot) q) (mul b' (mul quot q));
      poly_eq_transitivity #t #hz (mul b' (mul q quot)) (mul b' (mul quot q)) (mul (mul b' quot) q);
      // (6) sub a' (mul b' quot) == add a' (neg (mul b' quot))
      poly_sub_unfold #t #g a' (mul b' quot);
      // (7) (sub a' X)*q ≡ a'*q + (neg X)*q via left distrib
      poly_mul_left_distrib #t #sr a' (neg (mul b' quot)) q;
      // (8) (neg X)*q ≡ -((b'*quot)*q) via comm + neg
      poly_mul_commutative #t #cr (neg (mul b' quot)) q;
      poly_mul_neg #t #rng q (mul b' quot);
      poly_eq_transitivity #t #hz (mul (neg (mul b' quot)) q) (mul q (neg (mul b' quot))) (neg (mul q (mul b' quot)));
      poly_mul_commutative #t #cr q (mul b' quot);
      poly_neg_congruence #t #g (mul q (mul b' quot)) (mul (mul b' quot) q);
      poly_eq_transitivity #t #hz (mul (neg (mul b' quot)) q) (neg (mul q (mul b' quot))) (neg (mul (mul b' quot) q));
      // (9) (sub a' X)*q ≡ a'*q + neg((b'*quot)*q)
      poly_eq_reflexivity #t #hz (mul a' q);
      poly_add_congruence #t #am (mul a' q) (mul (neg (mul b' quot)) q) (mul a' q) (neg (mul (mul b' quot) q));
      poly_eq_transitivity #t #hz
        (mul (sub a' (mul b' quot)) q)
        (add (mul a' q) (mul (neg (mul b' quot)) q))
        (add (mul a' q) (neg (mul (mul b' quot) q)));
      // (10) b'*p ≡ (b'*quot)*q + b'*r
      poly_eq_reflexivity #t #hz (mul b' r);
      poly_add_congruence #t #am (mul b' (mul q quot)) (mul b' r) (mul (mul b' quot) q) (mul b' r);
      poly_eq_transitivity #t #hz (mul b' p) (add (mul b' (mul q quot)) (mul b' r)) (add (mul (mul b' quot) q) (mul b' r));
      // (11) LHS ≡ ((b'*quot)*q + b'*r) + (a'*q + neg((b'*quot)*q))
      poly_add_congruence #t #am
        (mul b' p) (mul (sub a' (mul b' quot)) q)
        (add (mul (mul b' quot) q) (mul b' r)) (add (mul a' q) (neg (mul (mul b' quot) q)));
      // (12) rearrangement: (A+B)+(C+neg(A)) ≡ B+C
      poly_add_neg_rearrange #t #f (mul (mul b' quot) q) (mul b' r) (mul a' q);
      // (13) LHS ≡ b'*r + a'*q
      let lhs = add (mul b' p) (mul (sub a' (mul b' quot)) q) in
      poly_eq_transitivity #t #hz lhs
        (add (add (mul (mul b' quot) q) (mul b' r)) (add (mul a' q) (neg (mul (mul b' quot) q))))
        (add (mul b' r) (mul a' q));
      // (14) b'*r + a'*q ≡ a'*q + b'*r ≡ gv
      poly_add_commutative #t #acm (mul b' r) (mul a' q);
      poly_eq_transitivity #t #hz lhs (add (mul b' r) (mul a' q)) (add (mul a' q) (mul b' r));
      poly_eq_transitivity #t #hz lhs (add (mul a' q) (mul b' r)) gv
    end
#pop-options

(* ====================================================================== *)
(*  ext_gcd produces the same g as poly_gcd                               *)
(* ====================================================================== *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let rec ext_gcd_is_gcd (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (ensures (let hz = field_hz f in
                    let (_, _, g) = poly_ext_gcd p q in
                    poly_eq #t #hz g (poly_gcd p q)))
          (decreases (degree_measure q))
  = let sr = field_sr f in
    let hz = field_hz f in
    semiring_has_zero_unfold sr;
    if None? (degree q) then
      poly_eq_reflexivity #t #hz p
    else begin
      poly_mod_decreases_measure p q;
      ext_gcd_is_gcd q (poly_mod p q)
    end
#pop-options

(* ====================================================================== *)
(*  Degree-0 polynomial is poly_eq to its singleton [lc(p)]              *)
(* ====================================================================== *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let degree_zero_eq_singleton (#t:Type) {| f: field t |} (p: polynomial t)
  : Lemma (requires (let hz = field_hz f in degree #t #hz p == Some 0))
          (ensures (let hz = field_hz f in
                    poly_eq #t #hz p [leading_coefficient #t #hz p]))
  = let sr = field_sr f in
    let hz = field_hz f in
    semiring_has_zero_unfold sr;
    let lc = leading_coefficient #t #hz p in
    coeff_at_degree_eq_lc #t #hz p;
    // coeff_at p 0 = lc(p)
    let q : polynomial t = [lc] in
    let aux (i:nat) : Lemma (coeff_at #t #hz p i = coeff_at #t #hz q i)
      = if i = 0 then begin
          coeff_at_unfold #t #hz q 0;
          assert (L.length q = 1);
          assert (L.index q 0 == lc)
        end
        else begin
          coeff_above_degree_is_zero #t #hz p i;
          coeff_at_unfold #t #hz q i;
          assert (i >= L.length q)
        end
    in
    Classical.forall_intro aux;
    coeff_at_to_poly_eq #t #hz p q
#pop-options

(* ====================================================================== *)
(*  Singleton multiplication inverse over a field                          *)
(* ====================================================================== *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let singleton_mul_inverse (#t:Type) {| f: field t |} (c: t{c <> zero})
  : Lemma (ensures (let sr = field_sr f in
                    let hz = field_hz f in
                    let c_inv = f.division_ring.inv c in
                    poly_eq #t #hz
                      (poly_mul #t #sr [c_inv] [c])
                      (poly_one #t)))
  = let sr = field_sr f in
    let hz = field_hz f in
    semiring_has_zero_unfold sr;
    let c_inv = f.division_ring.inv c in
    let x = sr.mul_monoid.mul_semigroup.has_mul.op_Star c_inv c in
    let e : polynomial t = [] in
    // Step A: scalar_mul c_inv [c] == [x]
    poly_mul_singleton #t #sr c_inv [c];
    scalar_mul_cons #t #sr c_inv c e;
    scalar_mul_nil #t #sr c_inv;
    // Step B: poly_one == [one]
    poly_one_def #t ();
    // Step C: poly_eq [x] [one]
    poly_eq_nil_right #t #hz e;
    all_zero_nil #t #hz ();
    // poly_eq [] [] == all_zero [] == true
    let one_ = sr.mul_monoid.has_one.one in
    poly_eq_cons_cons #t #hz x e one_ e;
    // poly_eq [x] [one_] == (x = one_ && poly_eq [] []) == (x = one_ && true)
    // Step D: x = one_ from inv spec
    // c_inv * c = one from division_ring.inv, and * = sr.mul..., one = sr.mul...has_one.one
    // Step E: bridge with poly_mul_singleton
    let sm = scalar_mul #t #sr c_inv [c] in
    let target = poly_one #t in
    // sm == [x], target == [one_]
    // poly_eq sm target follows since sm == [x] and target == [one_]
    // and poly_eq [x] [one_] is established in step C
    // Final: poly_eq result target via transitivity with sm
    let result = poly_mul #t #sr [c_inv] [c] in
    poly_eq_transitivity #t #hz result sm target
#pop-options

(* ====================================================================== *)
(*  Degree-0 polynomial has a multiplicative inverse over a field          *)
(* ====================================================================== *)

(* Note: we avoid `inv` in the ensures to sidestep TC-diamond refinement
   issues. The concrete inverse [lc_inv] is constructed in call sites. *)

(* ====================================================================== *)
(*  Euclid's lemma: coprime(p,q) ∧ p | a*q → p | a                       *)
(* ====================================================================== *)

let coprime (#t:Type) {| f: field t |} (p q: polynomial t) : bool =
  let hz = field_hz f in
  semiring_has_zero_unfold (field_sr f);
  degree #t #hz (poly_gcd p q) = Some 0

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let euclid_lemma (#t:Type) {| f: field t |} (p q a: polynomial t)
  : Lemma (requires Some? (degree p) /\
                   degree #t #(field_hz f) (poly_gcd p q) == Some 0 /\
                   poly_divides p (poly_mul #t #(field_sr f) a q))
          (ensures poly_divides p a)
  = let sr = field_sr f in
    let hz = field_hz f in
    let am = field_am f in
    let g = field_g f in
    let cr = field_cr f in
    semiring_has_zero_unfold sr;
    let mul = poly_mul #t #sr in
    let add = poly_add #t #am in
    // From Bézout: s*p + t*q ≡ gv, where gv ≡ gcd(p,q)
    ext_gcd_correct p q;
    ext_gcd_is_gcd p q;
    let (s, t_, gv) = poly_ext_gcd p q in
    let gcd_pq = poly_gcd p q in
    // gv ≡ gcd_pq, degree gcd_pq = Some 0
    // Transfer degree: degree gv = Some 0
    degree_well_defined #t #hz gv gcd_pq;
    // Step 1: p | p (self), p | p*a, p | (p*a)*s
    divides_self p;
    divides_mul_right p p a;
    divides_mul_right p (mul p a) s;
    // (p*a)*s ≡ s*(p*a) by comm
    poly_mul_commutative #t #cr (mul p a) s;
    poly_divides_congruence p (mul (mul p a) s) (mul s (mul p a));
    // s*(p*a) ≡ (s*p)*a by assoc (symmetric)
    poly_mul_associative #t #sr s p a;
    poly_eq_symmetry #t #hz (mul (mul s p) a) (mul s (mul p a));
    poly_divides_congruence p (mul s (mul p a)) (mul (mul s p) a);
    // So: p | (s*p)*a
    // Step 2: p | a*q (hypothesis), p | (a*q)*t_
    divides_mul_right p (mul a q) t_;
    // (a*q)*t_ ≡ t_*(a*q) by comm
    poly_mul_commutative #t #cr (mul a q) t_;
    poly_divides_congruence p (mul (mul a q) t_) (mul t_ (mul a q));
    // t_*(a*q) ≡ t_*(q*a) by comm inside + mul_cong
    poly_mul_commutative #t #cr a q;
    poly_eq_reflexivity #t #hz t_;
    poly_mul_congruence #t #sr t_ (mul a q) t_ (mul q a);
    poly_divides_congruence p (mul t_ (mul a q)) (mul t_ (mul q a));
    // t_*(q*a) ≡ (t_*q)*a by assoc (symmetric)
    poly_mul_associative #t #sr t_ q a;
    poly_eq_symmetry #t #hz (mul (mul t_ q) a) (mul t_ (mul q a));
    poly_divides_congruence p (mul t_ (mul q a)) (mul (mul t_ q) a);
    // So: p | (t_*q)*a
    // Step 3: p | ((s*p)*a)*1 + (t_*q)*a by divides_sum
    divides_sum p (mul (mul s p) a) (poly_one #t) (mul (mul t_ q) a);
    // ((s*p)*a)*1 ≡ (s*p)*a
    poly_mul_one_right #t #sr (mul (mul s p) a);
    poly_eq_reflexivity #t #hz (mul (mul t_ q) a);
    poly_add_congruence #t #am
      (mul (mul (mul s p) a) (poly_one #t)) (mul (mul t_ q) a)
      (mul (mul s p) a) (mul (mul t_ q) a);
    poly_divides_congruence p
      (add (mul (mul (mul s p) a) (poly_one #t)) (mul (mul t_ q) a))
      (add (mul (mul s p) a) (mul (mul t_ q) a));
    // So: p | (s*p)*a + (t_*q)*a
    // Step 4: (s*p)*a + (t_*q)*a ≡ (s*p + t_*q)*a by left_distrib (symmetric)
    poly_mul_left_distrib #t #sr (mul s p) (mul t_ q) a;
    poly_eq_symmetry #t #hz
      (mul (add (mul s p) (mul t_ q)) a)
      (add (mul (mul s p) a) (mul (mul t_ q) a));
    poly_divides_congruence p
      (add (mul (mul s p) a) (mul (mul t_ q) a))
      (mul (add (mul s p) (mul t_ q)) a);
    // So: p | (s*p + t_*q)*a
    // Step 5: s*p + t_*q ≡ gv → (s*p + t_*q)*a ≡ gv*a
    poly_eq_reflexivity #t #hz a;
    poly_mul_congruence #t #sr (add (mul s p) (mul t_ q)) a gv a;
    poly_divides_congruence p (mul (add (mul s p) (mul t_ q)) a) (mul gv a);
    // So: p | gv*a
    // Step 6: construct gv_inv = [lc_inv], show [lc_inv]*gv ≡ poly_one
    lc_nonzero_of_degree_some #t #hz gv;
    let lc = leading_coefficient #t #hz gv in
    let lc_inv = f.division_ring.inv lc in
    let gv_inv : polynomial t = [lc_inv] in
    // Inline degree-zero inverse proof: gv ≡ [lc], [lc_inv]*gv ≡ [lc_inv]*[lc] ≡ poly_one
    degree_zero_eq_singleton #t #f gv;
    poly_eq_reflexivity #t #hz gv_inv;
    poly_mul_congruence #t #sr gv_inv gv gv_inv [lc];
    singleton_mul_inverse #t #f lc;
    poly_eq_transitivity #t #hz (mul gv_inv gv) (mul gv_inv [lc]) (poly_one #t);
    // Step 7: p | (gv*a)*gv_inv
    divides_mul_right p (mul gv a) gv_inv;
    // Step 8: (gv*a)*gv_inv ≡ gv_inv*(gv*a) by comm
    poly_mul_commutative #t #cr (mul gv a) gv_inv;
    poly_divides_congruence p (mul (mul gv a) gv_inv) (mul gv_inv (mul gv a));
    // Step 9: gv_inv*(gv*a) ≡ (gv_inv*gv)*a by assoc (sym)
    poly_mul_associative #t #sr gv_inv gv a;
    poly_eq_symmetry #t #hz (mul (mul gv_inv gv) a) (mul gv_inv (mul gv a));
    poly_divides_congruence p (mul gv_inv (mul gv a)) (mul (mul gv_inv gv) a);
    // Step 10: gv_inv*gv ≡ poly_one (proved inline above)
    // → (gv_inv*gv)*a ≡ poly_one * a
    poly_eq_reflexivity #t #hz a;
    poly_mul_congruence #t #sr (mul gv_inv gv) a (poly_one #t) a;
    poly_divides_congruence p (mul (mul gv_inv gv) a) (mul (poly_one #t) a);
    // Step 11: poly_one * a ≡ a
    poly_mul_one_left #t #sr a;
    poly_divides_congruence p (mul (poly_one #t) a) a
#pop-options
