module Core.Polynomial.Irreducible

(*
   Irreducibility theory for univariate polynomials over a field
   of characteristic zero.

   Main results:
     - poly_irreducible : polynomial t -> prop
     - irreducible_factor_exists : every polynomial of degree >= 1 has an irreducible factor
     - poly_deriv_degree_char0 : in char 0, deg(D(p)) = deg(p) - 1
     - irreducible_coprime_deriv : irreducible q ==> coprime(q, D(q))
     - coprime_quotients : after dividing by GCD, quotients are coprime
     - b0_is_square_free : the key correctness theorem for Yun's algorithm

   Supporting infrastructure:
     - Power divisibility: deriv_power_divisibility, repeated_factor_divides_deriv/gcd
     - Degree bounds: divides_degree_le, coprime_divisor
     - not_square_free_of_repeated_factor (contrapositive characterization)
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.GCD
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree

(* ================================================================ *)
(*  Power divisibility: p | p^n for n ≥ 1                           *)
(* ================================================================ *)

let poly_power_divides (#t:Type) {| f: field t |}
  (p: polynomial t) (n: pos)
  : Lemma (ensures divides p (poly_power p n))
  = 
    (* poly_power p n = poly_mul p (poly_power p (n-1)) definitionally for n ≥ 1.
       Witness: poly_power p (n-1). *)
    poly_eq_reflexivity (p * (poly_power p (n - 1)));
    divides_intro  p (p * (poly_power p (n - 1))) (poly_power p (n - 1))

(* ================================================================ *)
(*  Derivative of product rule (Leibniz) — available from Derivative *)
(*  D(p·q) = D(p)·q + p·D(q)                                       *)
(*  (This is poly_deriv_mul in Core.Polynomial.Derivative.)          *)
(* ================================================================ *)

(* For Yun correctness, the key algebraic identity is:
   If f = ∏ pᵢ^eᵢ (distinct irreducible factors), then
   f' = f · ∑ (eᵢ · pᵢ' / pᵢ)
   This "logarithmic derivative" structure is what makes Yun work.
   Proving it formally requires unique factorization (UFD theory)
   which is available via polynomial_ufd_instance but the full
   inductive factorization argument is substantial. *)

(* ================================================================ *)
(*  Helper: poly_one divides everything                            *)
(* ================================================================ *)

let one_divides_all (#t:Type) {| f: field t |}
  (x: polynomial t)
  : Lemma (divides (poly_one #t) x)
  = 
    poly_mul_one x;
    (* poly_mul_one gives: poly_eq (poly_mul poly_one x) x *)
    poly_eq_symmetry ((poly_one #t) * x) x;
    (* poly_eq x (poly_mul poly_one x) *)
    divides_intro  (poly_one #t) x x

(* ================================================================ *)
(*  Helper: d|a ⟹ (c·d) | (c·a)                                  *)
(* ================================================================ *)

let divides_mul_both_sides (#t:Type) {| f: field t |}
  (d a c: polynomial t)
  : Lemma (requires divides d a)
          (ensures  divides (c * d) (c * a))
  =
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    eliminate exists (s: polynomial t). (a = (d * s))
    returns divides (c * d) (c * a)
    with _.
    begin
      (* c·a ≈ c·(d·s) by congruence *)
      poly_mul_right_congruence c a (d * s);
      (* c·(d·s) ≈ (c·d)·s by assoc (reversed) *)
      mul_associativity c d s;
      poly_eq_transitivity (c * a)
        (c * (d * s))
        ((c * d) * s);
      divides_intro  (c * d) (c * a) s
    end

(* ================================================================ *)
(*  Derivative of power: q^(k-1) | D(q^k) for k ≥ 1               *)
(* ================================================================ *)

let rec deriv_power_divisibility (#t:Type) {| f: field t |}
  (q: polynomial t) (k: pos)
  : Lemma (ensures divides (poly_power q (k - 1)) (poly_deriv (poly_power q k)))
          (decreases k)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if k = 1 then
      (* poly_power q 0 = poly_one.
         Need: divides poly_one (D(q^1)). poly_one divides anything. *)
      one_divides_all (poly_deriv (poly_power q k))
    else begin
      (* k ≥ 2. Definitionally: poly_power q k == poly_mul q (poly_power q (k-1)).
         Product rule: D(q · q^(k-1)) ≈ D(q)·q^(k-1) + q·D(q^(k-1)).
         IH: q^(k-2) | D(q^(k-1)).
         Goal: q^(k-1) | D(q^k). *)
      let qk1 = poly_power q (k - 1) in
      let qk2 = poly_power q (k - 2) in
      let dq  = poly_deriv q in
      let dqk1 = poly_deriv qk1 in
      let sum1 = (dq * qk1) in
      let sum2 = (q * dqk1) in

      (* Product rule on q · q^(k-1) *)
      poly_deriv_mul q qk1;
      (* poly_eq (poly_deriv (poly_mul q qk1)) (poly_add sum1 sum2) *)

      (* --- Summand 1: qk1 | dq·qk1 --- *)
      mul_commutativity dq qk1;
      (* poly_eq (poly_mul dq qk1) (poly_mul qk1 dq) *)
      (* poly_eq (poly_mul qk1 dq) sum1 *)
      divides_intro  qk1 sum1 dq;

      (* --- Summand 2: qk1 | q·D(q^(k-1)) --- *)
      (* IH: q^(k-2) | D(q^(k-1)) *)
      deriv_power_divisibility q (k - 1);
      (* divides_mul_both_sides: q^(k-2)|D(q^(k-1)) ⟹ (q·q^(k-2))|(q·D(q^(k-1))) *)
      divides_mul_both_sides qk2 dqk1 q;
      (* divides (poly_mul q qk2) (poly_mul q dqk1)
         = divides (poly_mul q (poly_power q (k-2))) sum2
         And poly_mul q (poly_power q (k-2)) == poly_power q (k-1) == qk1 [definitional] *)

      (* --- Combine: qk1 | sum1 + sum2 --- *)
      divides_add  qk1 sum1 sum2;

      (* --- Transfer via poly_eq to poly_deriv (poly_power q k) --- *)
      (* poly_power q k == poly_mul q qk1 definitionally, so
         poly_deriv (poly_power q k) == poly_deriv (poly_mul q qk1)
         ≈ poly_add sum1 sum2 [product rule above] *)
      divides_congruence_right  qk1
        (sum1 + sum2)
        (poly_deriv (poly_power q k))
    end

(* ================================================================ *)
(*  Repeated factor ⟹ derivative divisibility                      *)
(*  If q^k | p (k ≥ 2) then q^(k-1) | D(p)                       *)
(* ================================================================ *)

let repeated_factor_divides_deriv (#t:Type) {| f: field t |}
  (q p: polynomial t) (k: nat{k >= 2})
  : Lemma (requires divides (poly_power q k) p)
          (ensures  divides (poly_power q (k - 1)) (poly_deriv p))
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let qk   = poly_power q k in
    let qk1  = poly_power q (k - 1) in
    (* From q^k | p: ∃r. p ≈ q^k · r *)
    eliminate exists (r: polynomial t). (p = (qk * r))
    returns divides qk1 (poly_deriv p)
    with _.
    begin
      (* D(p) ≈ D(q^k · r) by congruence *)
      poly_deriv_congruence p (qk * r);
      (* D(q^k · r) ≈ D(q^k)·r + q^k·D(r) by product rule *)
      poly_deriv_mul qk r;
      let dqk = poly_deriv qk in
      let dr  = poly_deriv r in
      let sum1 = (dqk * r) in
      let sum2 = (qk * dr) in
      poly_eq_transitivity (poly_deriv p)
        (poly_deriv (qk * r))
        (sum1 + sum2);

      (* --- Term 1: qk1 | D(q^k)·r --- *)
      deriv_power_divisibility q k;
      (* qk1 | D(q^k) *)
      divides_mul_right  qk1 dqk r;
      (* qk1 | dqk · r = sum1 *)

      (* --- Term 2: qk1 | q^k · D(r) --- *)
      (* qk1 | qk because q^k = q · q^(k-1) ≈ q^(k-1) · q *)
      mul_commutativity q qk1;
      (* poly_eq (poly_mul q qk1) (poly_mul qk1 q), i.e. poly_eq qk (poly_mul qk1 q) *)
      divides_intro  qk1 qk q;
      (* qk1 | qk *)
      divides_mul_right  qk1 qk dr;
      (* qk1 | qk · dr = sum2 *)

      (* --- Combine --- *)
      divides_add  qk1 sum1 sum2;
      (* qk1 | poly_add sum1 sum2 *)
      divides_congruence_right  qk1
        (sum1 + sum2)
        (poly_deriv p)
    end

(* ================================================================ *)
(*  Repeated factor ⟹ divides GCD                                  *)
(*  If q^k | p (k ≥ 2) then q^(k-1) | gcd(p, D(p))               *)
(* ================================================================ *)

let repeated_factor_divides_gcd (#t:Type) {| f: field t |}
  (q p: polynomial t) (k: nat{k >= 2})
  : Lemma (requires divides (poly_power q k) p /\ deg p >= 0)
          (ensures  divides (poly_power q (k - 1))
                            (poly_gcd p (poly_deriv p)))
  = 
    let qk1 = poly_power q (k - 1) in
    let dp  = poly_deriv p in
    let g   = poly_gcd p dp in
    (* qk1 | p: by transitivity, qk1 | q^k | p *)
    (* q^k = q · q^(k-1) ≈ q^(k-1) · q *)
    mul_commutativity q qk1;
    divides_intro  qk1 (poly_power q k) q;
    divides_trans  qk1 (poly_power q k) p;
    (* qk1 | p *)
    (* qk1 | D(p) *)
    repeated_factor_divides_deriv q p k;
    (* qk1 | gcd(p, D(p)) by maximality:
       gcd_is_maximal says: if d|p and d|q then d | gcd(p,q) *)
    gcd_is_maximal p dp qk1

(* ================================================================ *)
(*  Degree of power: deg(q^k) ≥ deg(q) for k ≥ 1                  *)
(* ================================================================ *)

let rec poly_power_has_degree (#t:Type) {| f: field t |}
  (q: polynomial t) (k: pos)
  : Lemma (requires deg q >= 0)
          (ensures  deg (poly_power q k) >= 0 /\
                    deg (poly_power q k) >= deg q)
          (decreases k)
  = if k = 1 then
      degree_mul q (poly_one #t)
    else begin
      poly_power_has_degree q (k - 1);
      degree_mul q (poly_power q (k - 1))
    end

(* ================================================================ *)
(*  Divisibility degree bound: d|g and deg d ≥ 1 ⟹ deg g ≥ 1      *)
(* ================================================================ *)

private let divides_degree_lower_bound (#t:Type) {| f: field t |}
  (d g: polynomial t)
  : Lemma (requires divides d g /\ deg d >= 1
                    /\ deg g >= 0)
          (ensures  deg g >= 1)
  = let aux (c: polynomial t)
      : Lemma (requires (g = (d * c)))
              (ensures  deg g >= 1)
      = degree_well_defined g (d * c);
        (* poly_deg (poly_mul d c) == poly_deg g == Some _ *)
        if Nil? c then begin
          (* c = [] = poly_zero. poly_mul d poly_zero ≈ poly_zero by x_mul_zero *)
          H.x_mul_zero d;
          degree_well_defined (d * c) (poly_zero #(polynomial t))
          (* deg (poly_mul d c) < 0, contradicts Some? above *)
        end else begin
          (* Both d and c are nonempty: use degree_mul *)
          degree_mul d c
        end
    in
    Classical.forall_intro (Classical.move_requires aux)

(* ================================================================ *)
(*  Square-free characterization (contrapositive):                  *)
(*  If q^k | p with k ≥ 2 and deg(q) ≥ 1, then p is NOT square-free *)
(* ================================================================ *)

#push-options "--z3rlimit 30 --fuel 4 --ifuel 3"
let not_square_free_of_repeated_factor (#t:Type) {| f: field t |}
  (q p: polynomial t) (k: nat{k >= 2})
  : Lemma (requires divides (poly_power q k) p /\
                    deg q >= 1 /\
                    deg p >= 0)
          (ensures  square_free p = false)
  = let dp = poly_deriv p in
    let g  = poly_gcd p dp in
    let qk1 = poly_power q (k - 1) in
    repeated_factor_divides_gcd q p k;
    poly_power_has_degree q (k - 1);
    gcd_has_degree p dp;
    coprime_reveal p dp;
    (* Now: divides qk1 g, deg qk1 >= 0 with val >= 1, deg g >= 0 *)
    (* Inline the degree bound argument via existential elimination *)
    let aux (c: polynomial t)
      : Lemma (requires (g = (qk1 * c)))
              (ensures  square_free p = false)
      = degree_well_defined g (qk1 * c);
        if Nil? c then begin
          H.x_mul_zero qk1;
          degree_well_defined (qk1 * c) (poly_zero #(polynomial t))
        end else
          degree_mul qk1 c
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

(* ================================================================ *)
(*  Coprime quotients: after dividing by GCD, quotients are coprime *)
(*                                                                  *)
(*  If g = gcd(p, q), b = p/g, c = q/g, then gcd(b,c) = 1.         *)
(*  This is the key lemma for showing b₀ is square-free.            *)
(* ================================================================ *)

(* Helper: if g nonzero and poly_eq (poly_mul g b) p with p nonzero,
   then b is nonzero. *)
private let poly_div_nonzero (#t:Type) {| f: field t |}
  (p g: polynomial t)
  : Lemma (requires deg p >= 0 /\ deg g >= 0 /\
                    ((g * (poly_div p g)) = p))
          (ensures  deg (poly_div p g) >= 0)
  = let b = poly_div p g in
    if deg b >= 0 then () else begin
        (* b = poly_zero, so poly_mul g b ≈ poly_zero *)
        assert (b == (poly_zero));
        H.x_mul_zero g;
        (* poly_eq (poly_mul g poly_zero) poly_zero *)
        degree_well_defined (g * b) (poly_zero);
        (* deg (poly_mul g b) < 0 *)
        degree_well_defined p (g * b)
    end
        (* poly_deg p == deg (poly_mul g b) < 0, contradicts Some? *)

(* Helper: extracted from coprime_quotients. If g is nonzero and
   g = (g*d)*e, then deg d = 0. Isolated as a top-level query so the
   degree arithmetic is not re-searched per case branch. *)
private let coprime_quotients_deg_aux (#t:Type) {| f: field t |}
  (g d e: polynomial t)
  : Lemma (requires deg g >= 0 /\ (g = ((g * d) * e)))
          (ensures  deg d = 0)
  = mul_associativity g d e;
    (* poly_eq ((g*d)*e) (g*(d*e)) and poly_eq g ((g*d)*e) (hyp) *)
    degree_well_defined g ((g * d) * e);
    degree_well_defined ((g * d) * e) (g * (d * e));
    assert (deg g == deg (g * (d * e)));
    (if deg (d * e) < 0 then begin
         assert ((d * e) == (poly_zero));
         H.x_mul_zero g;
         degree_well_defined (g * (d * e)) (poly_zero)
     end else begin
         degree_mul g (d * e);
         assert (deg (g * (d * e)) == Prims.op_Addition (deg g) (deg (d * e)));
         assert (deg (d * e) == 0);
         (if deg e < 0 then begin
              assert (e == (poly_zero));
              H.x_mul_zero d;
              degree_well_defined (d * e) (poly_zero)
          end else begin
              degree_mul d e;
              assert (deg (d * e) == Prims.op_Addition (deg d) (deg e))
          end)
     end)

#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
let coprime_quotients (#t:Type) {| f: field t |}
  (p q: polynomial t)
  : Lemma (requires deg p >= 0)
          (ensures  (let g = poly_gcd p q in
                     let b = poly_div p g in
                     let c = poly_div q g in
                     coprime b c))
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let g = poly_gcd p q in
    let b = poly_div p g in
    let c = poly_div q g in
    coprime_reveal b c;
    gcd_has_degree p q;                  // deg g >= 0
    gcd_divides_left p q;                // g | p
    gcd_divides_right p q;               // g | q
    poly_div_correct p g;               // poly_eq (poly_mul g b) p
    poly_div_correct q g;               // poly_eq (poly_mul g c) q
    poly_div_nonzero p g;               // deg b >= 0
    let d = poly_gcd b c in
    gcd_has_degree b c;                  // deg d >= 0
    gcd_divides_left b c;                // d | b
    gcd_divides_right b c;               // d | c
    (* g*d | g*b via divides_mul_both_sides *)
    divides_mul_both_sides d b g;              // (g*d) | (g*b)
    (* g*b ≈ p, so g*d | p *)
    divides_congruence_right
      (g * d) (g * b) p;
    (* g*d | g*c similarly *)
    divides_mul_both_sides d c g;              // (g*d) | (g*c)
    divides_congruence_right
      (g * d) (g * c) q;
    (* By maximality of gcd: g*d | gcd(p,q) = g *)
    gcd_is_maximal p q (g * d);
    (* Now: divides (poly_mul g d) g with deg g >= 0.
       Extract witness and use degree_mul to show deg d = 0. *)
    let aux (e: polynomial t)
      : Lemma (requires (g = ((g * d) * e)))
              (ensures  deg d = 0)
      = coprime_quotients_deg_aux g d e
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

(* ================================================================ *)
(*  Degree bound for divisors: if d | p (both nonzero), deg d ≤ deg p *)
(* ================================================================ *)

let divides_degree_le (#t:Type) {| f: field t |}
  (d p: polynomial t)
  : Lemma (requires divides d p /\ deg d >= 0 /\ deg p >= 0)
          (ensures  deg d <= deg p)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let aux (c: polynomial t)
      : Lemma (requires (p = (d * c)))
              (ensures  deg d <= deg p)
      = if deg c < 0 then begin
            (* c = 0, so d*c ≈ 0, but poly_eq p (d*c) and p nonzero: contradiction *)
            assert (c == (poly_zero));
            H.x_mul_zero d;
            degree_well_defined p (poly_zero)
        end else begin
            degree_mul d c;
            degree_well_defined p (d * c)
        end
    in
    Classical.forall_intro (Classical.move_requires aux)

(* ================================================================ *)
(*  Coprime divisor: if coprime(a, b) and d | a, then coprime(d, b) *)
(* ================================================================ *)

#push-options "--z3rlimit 30 --fuel 4 --ifuel 3"
let coprime_divisor (#t:Type) {| f: field t |}
  (a b d: polynomial t)
  : Lemma (requires coprime a b /\ divides d a /\ deg d >= 0)
          (ensures  coprime d b)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    coprime_reveal a b;
    coprime_reveal d b;
    let e = poly_gcd d b in
    gcd_divides_left d b;              // e | d
    gcd_divides_right d b;             // e | b
    (* e | d and d | a, so e | a by transitivity *)
    divides_trans  e d a;
    (* e | a and e | b, so e | gcd(a, b) *)
    gcd_is_maximal a b e;
    (* coprime(a, b) means deg(gcd(a,b)) = 0. And e | gcd(a,b).
       Since e divides d which is nonzero, e is nonzero (Some? deg e). *)
    gcd_has_degree d b;                // deg e >= 0
    (* deg(gcd(a,b)) = 0 and e | gcd(a,b) with e nonzero: deg e ≤ 0, so deg e = 0 *)
    divides_degree_le e (poly_gcd a b);
    (* Now: deg e <= 0, and deg e >= 0, so deg e = 0 *)
    assert (deg e <= 0)
#pop-options

(* ================================================================ *)
(*  Irreducible polynomials and factor existence                     *)
(* ================================================================ *)

(* A polynomial q is irreducible if deg q ≥ 1 and whenever q = a·b,
   one of a or b has degree 0 (is a unit/scalar). *)
let poly_irreducible (#t:Type) {| f: field t |} (q: polynomial t) : prop
  = deg q >= 1 /\
    (forall (a b: polynomial t).
      ((q = (a * b)) == true) ==>
      (deg a == 0 \/ deg a < 0 \/
       deg b == 0 \/ deg b < 0))

(* A PROPER field extension modulus: irreducible AND degree >= 2, so the quotient
   t[X]/(r) genuinely adjoins a new element. Degree-1 (r = X - a) is excluded on
   purpose: its root already lies in the base field and t[X]/(X-a) ≅ t adjoins
   nothing. `unfold` so a refinement `{ proper_extension r }` reduces to
   `poly_irreducible r /\ deg r >= 2`, exposing `deg r >= 2` (hence the old
   `deg r >= 0`) and the opaque irreducibility — without unfolding poly_irreducible's
   quantifier. *)
unfold let proper_extension (#t:Type) {| f: field t |} (r: polynomial t) : prop =
  poly_irreducible r /\ deg r >= 2

(* Every polynomial of degree ≥ 1 has an irreducible factor.
   Proof by strong induction on degree. *)
#push-options "--z3rlimit 60"
let rec irreducible_factor_exists (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires deg p >= 1)
          (ensures exists (q: polynomial t). poly_irreducible q /\ divides q p)
          (decreases (if deg p >= 0 then deg p else 0))
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    Classical.excluded_middle (poly_irreducible p);
    (* Case 1: p is irreducible — witness q = p *)
    let case_irred (_: unit)
      : Lemma (requires poly_irreducible p)
              (ensures exists (q: polynomial t). poly_irreducible q /\ divides q p)
      = poly_mul_one p;
        divides_intro  p p (poly_one #t)
    in
    (* Case 2: p is not irreducible — factor and recurse *)
    let case_factor (a b: polynomial t)
      : Lemma (requires (p = (a * b)) == true /\
                        deg a >= 1 /\
                        deg b >= 1)
              (ensures exists (q: polynomial t). poly_irreducible q /\ divides q p)
      = (* deg(a*b) = deg a + deg b, and poly_eq p (a*b) so deg p = deg a + deg b *)
        degree_mul a b;
        degree_well_defined p (a * b);
        (* Therefore deg a = deg p - deg b <= deg p - 1 < deg p *)
        assert (deg (a * b) == deg a + deg b);               (* degree_mul *)
        assert (deg p == deg a + deg b);                     (* degree_well_defined *)
        assert (deg a >= 0);                                 (* deg a >= 1 *)
        assert (deg a < deg p);                              (* deg b >= 1, sandwich *)
        (* Recurse on a (smaller degree) *)
        irreducible_factor_exists a;
        (* Now: exists q. poly_irreducible q /\ divides q a *)
        (* a | p because p ≈ a*b *)
        divides_intro  a p b;
        (* Chain: q | a and a | p → q | p *)
        let chain (q: polynomial t)
          : Lemma (requires poly_irreducible q /\ divides q a)
                  (ensures exists (q: polynomial t). poly_irreducible q /\ divides q p)
          = divides_trans  q a p
        in
        Classical.forall_intro (Classical.move_requires chain)
    in
    Classical.move_requires case_irred ();
    Classical.forall_intro_2 (Classical.move_requires_2 case_factor)
#pop-options

(* ================================================================ *)
(*  Characteristic zero: nat_scale n one ≠ zero for n ≥ 1           *)
(* ================================================================ *)

(* A field of characteristic zero: every positive natural, when
   viewed as a field element via repeated addition of one, is nonzero. *)
let char_zero (#t:Type) (f: field t) : prop
  = forall (n:pos). ~(nat_scale n (one #t) = (zero #t))

(* Helper: if coeff q k ≠ zero, then degree q ≥ k *)
private let nonzero_coeff_degree_lb (#t:Type) {| cr: commutative_ring t |}
  (q: polynomial t) (k: nat)
  : Lemma (requires not (coeff q k = zero))
          (ensures  deg q >= k)
  = // By contrapositive of coeff_above_degree:
    // if None?(poly_deg q) or Some?.v(poly_deg q) < k, then coeff q k = zero.
    // Since coeff q k ≠ zero, we get Some?(poly_deg q) and Some?.v(poly_deg q) >= k.
    Classical.move_requires (coeff_above_degree q) k

(* Helper: in a domain, nat_scale n a ≠ zero when char_zero and a ≠ zero and n ≥ 1 *)
private let nat_scale_nonzero_in_domain (#t:Type) {| f: field t |}
  (n: pos) (a: t)
  : Lemma (requires char_zero f /\ not (a = zero))
          (ensures  not (nat_scale n a = zero))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    // nat_scale n one * a = nat_scale n (one * a)  [nat_scale_mul_left]
    nat_scale_mul_left n (one #t) a;
    // one * a = a
    H.one_mul_x a;
    // nat_scale n (one * a) = nat_scale n a   [congruence]
    nat_scale_congruence n (one * a) a;
    // Combine: nat_scale n one * a = nat_scale n a
    // char_zero: nat_scale n one ≠ zero; hypothesis: a ≠ zero
    // domain: product of nonzero is nonzero
    domain_nonzero_mul_nonzero (nat_scale n one) a

(* In char 0: the derivative of a polynomial of degree n ≥ 1
   has degree exactly n - 1. The leading coefficient is n · lc(p). *)
let poly_deriv_degree_char0 (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires char_zero f /\ deg p >= 1)
         (ensures  deg (poly_deriv p) >= 0 /\
                   deg (poly_deriv p) == ((deg p) - 1))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let n = deg p in
    let dp = poly_deriv p in
    // Step 1: coeff dp (n-1) = nat_scale n (coeff p n)
    poly_deriv_coeff p (n - 1);
    // Step 2: coeff p n ≠ zero (leading coefficient is nonzero)
    leading_coeff_nonzero p;
    // Step 3: nat_scale n (coeff p n) ≠ zero
    nat_scale_nonzero_in_domain n (coeff p n);
    // Step 4: coeff dp (n-1) ≠ zero → deg dp >= n-1
    nonzero_coeff_degree_lb dp (n - 1);
    // Step 5: upper bound — deg dp ≤ n-1
    // If deg dp = m >= n, then coeff dp m ≠ zero (leading coeff).
    // But coeff dp m = nat_scale (m+1) (coeff p (m+1)) = nat_scale (m+1) zero = zero.
    // Contradiction. So deg dp < n.
    let m = deg dp in
    if m >= n then (
      leading_coeff_nonzero dp;
      poly_deriv_coeff p m;
      coeff_above_degree p (m ++ 1);
      nat_scale_zero_element #t (m ++ 1)
    ) else ()

(* If q is irreducible in char 0 with deg q ≥ 1, then coprime(q, D(q)). *)
#push-options "--z3rlimit 40"
let irreducible_coprime_deriv (#t:Type) {| f: field t |}
  (q: polynomial t)
  : Lemma (requires char_zero f /\ poly_irreducible q)
         (ensures  coprime q (poly_deriv q))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let g = poly_gcd q (poly_deriv q) in
    // g | q and g | D(q)
    gcd_divides_left q (poly_deriv q);
    gcd_divides_right q (poly_deriv q);
    // From poly_irreducible q: for any factorization q = a*b,
    // one of deg(a), deg(b) is 0 or None.
    // g | q means exists h. poly_eq q (poly_mul g h).
    // We show deg g = 0 by contradiction:
    // - If None? poly_deg g: g = zero, so divides zero q → q = zero. But deg q ≥ 1.
    // - If Some?.v poly_deg g >= 1: then in the factorization q = g*h,
    //   irreducibility gives deg(h) = 0 or None.
    //   If deg(h) = None: h = zero, poly_mul g zero = zero, q = zero. Contradiction.
    //   If deg(h) = Some 0: degree_mul gives deg(q) = deg(g) + 0 = deg(g).
    //     But g | D(q) and D(q) is nonzero (deg D(q) = deg(q)-1 ≥ 0).
    //     divides_degree_le gives deg(g) ≤ deg(D(q)) = deg(q) - 1 < deg(q) = deg(g). ⊥
    // Therefore deg(g) = Some 0, i.e., coprime.
    poly_deriv_degree_char0 q;
    coprime_reveal q (poly_deriv q);
    let aux (h: polynomial t)
      : Lemma (requires (q = (g * h)) == true)
              (ensures  deg g == 0)
      = assert (deg g == 0 \/ deg g < 0 \/
                deg h == 0 \/ deg h < 0);
        if deg g < 0 then (
          degree_none_poly_eq_zero g;
          poly_eq_reflexivity h;
          poly_mul_congruence g h (poly_zero) h;
          H.zero_mul_x h;
          poly_eq_transitivity (g * h) ((poly_zero) * h) (poly_zero);
          poly_eq_transitivity q (g * h) (poly_zero);
          degree_well_defined q (poly_zero)
        ) else if deg h < 0 then (
          degree_none_poly_eq_zero h;
          poly_eq_reflexivity g;
          poly_mul_congruence g h g (poly_zero);
          H.x_mul_zero g;
          poly_eq_transitivity (g * h) (g * (poly_zero)) (poly_zero);
          poly_eq_transitivity q (g * h) (poly_zero);
          degree_well_defined q (poly_zero)
        ) else if deg g = 0 then ()
        else (
          // deg(g) ≥ 1, so from disjunction: deg(h) must be 0 (only remaining option)
          assert (deg h = 0);
          // degree_mul: deg(poly_mul g h) = deg(g) + deg(h)
          degree_mul g h;
          // Bridge: poly_eq q (poly_mul g h) → poly_deg q == poly_deg (poly_mul g h)
          degree_well_defined q (g * h);
          // Now: deg(q) = deg(g) + 0 = deg(g)
          // g | D(q), so deg(g) ≤ deg(D(q)) = deg(q) - 1 < deg(q) = deg(g). ⊥
          divides_degree_le g (poly_deriv q)
          // Now: deg(g) ≤ deg(q) - 1 and deg(g) = deg(q). Contradiction.
        )
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

(* ================================================================ *)
(*  Helper: product of divisibilities — d₁|a ∧ d₂|b → (d₁·d₂)|(a·b) *)
(* ================================================================ *)

let divides_product (#t:Type) {| f: field t |}
  (d1 a d2 b: polynomial t)
  : Lemma (requires divides d1 a /\ divides d2 b)
          (ensures  divides (d1 * d2) (a * b))
  =
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let aux1 (c1: polynomial t)
      : Lemma (requires (a = (d1 * c1)))
              (ensures  divides (d1 * d2) (a * b))
      = let aux2 (c2: polynomial t)
          : Lemma (requires (b = (d2 * c2)))
                  (ensures  divides (d1 * d2) (a * b))
          = (* a·b ≈ (d1·c1)·(d2·c2) ≈ (d1·d2)·(c1·c2) by assoc/comm *)
            poly_mul_left_congruence a (d1 * c1) b;
            poly_mul_right_congruence (d1 * c1) b (d2 * c2);
            poly_eq_transitivity (a * b)
              ((d1 * c1) * b)
              ((d1 * c1) * (d2 * c2));
            (* (d1·c1)·(d2·c2) = d1·(c1·(d2·c2)) *)
            mul_associativity d1 c1 (d2 * c2);
            poly_eq_symmetry ((d1 * c1) * (d2 * c2))
                             (d1 * (c1 * (d2 * c2)));
            (* c1·(d2·c2) = (c1·d2)·c2 = (d2·c1)·c2 = d2·(c1·c2) *)
            mul_associativity c1 d2 c2;
            poly_eq_symmetry ((c1 * d2) * c2)
                             (c1 * (d2 * c2));
            mul_commutativity c1 d2;
            poly_mul_left_congruence (c1 * d2) (d2 * c1) c2;
            mul_associativity d2 c1 c2;
            poly_eq_transitivity (c1 * (d2 * c2))
              ((c1 * d2) * c2)
              ((d2 * c1) * c2);
            poly_eq_transitivity (c1 * (d2 * c2))
              ((d2 * c1) * c2)
              (d2 * (c1 * c2));
            (* d1·(c1·(d2·c2)) = d1·(d2·(c1·c2)) *)
            poly_mul_right_congruence d1
              (c1 * (d2 * c2))
              (d2 * (c1 * c2));
            (* d1·(d2·(c1·c2)) = (d1·d2)·(c1·c2) *)
            mul_associativity d1 d2 (c1 * c2);
            poly_eq_symmetry ((d1 * d2) * (c1 * c2))
                             (d1 * (d2 * (c1 * c2)));
            poly_eq_transitivity (d1 * (c1 * (d2 * c2)))
              (d1 * (d2 * (c1 * c2)))
              ((d1 * d2) * (c1 * c2));
            (* chain all: a·b ≈ (d1·d2)·(c1·c2) *)
            poly_eq_transitivity (a * b)
              ((d1 * c1) * (d2 * c2))
              (d1 * (c1 * (d2 * c2)));
            poly_eq_transitivity (a * b)
              (d1 * (c1 * (d2 * c2)))
              ((d1 * d2) * (c1 * c2));
            divides_intro
              (d1 * d2) (a * b) (c1 * c2)
        in
        Classical.forall_intro (Classical.move_requires aux2)
    in
    Classical.forall_intro (Classical.move_requires aux1)

(* ================================================================ *)
(*  Helper: poly_power q (n+m) ≈ poly_mul (poly_power q n) (poly_power q m) *)
(* ================================================================ *)

let rec poly_power_add (#t:Type) {| cr: commutative_ring t |}
  (q: polynomial t) (n m: nat)
  : Lemma (ensures (poly_power q (n ++ m)) =
                           ((poly_power q n) * (poly_power q m)))
          (decreases n)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if n = 0 then begin
      (* poly_power q (0+m) = poly_power q m
         poly_mul (poly_power q 0) (poly_power q m) = poly_mul poly_one (poly_power q m)
         poly_mul_one gives the bridge *)
      poly_mul_one (poly_power q m)
    end else begin
      (* poly_power q (n+m) = poly_mul q (poly_power q (n+m-1)) [definitional for n+m ≥ 1]
         poly_power q n = poly_mul q (poly_power q (n-1))       [definitional for n ≥ 1]
         IH: poly_power q ((n-1)+m) ≈ poly_mul (poly_power q (n-1)) (poly_power q m)
         Goal: poly_mul q (poly_power q (n+m-1)) ≈ poly_mul (poly_mul q (poly_power q (n-1))) (poly_power q m)
         Chain: LHS ≈ poly_mul q (poly_mul (poly_power q (n-1)) (poly_power q m))  [by IH + congruence]
                    ≈ poly_mul (poly_mul q (poly_power q (n-1))) (poly_power q m)  [by associativity] *)
      poly_power_add q (n - 1) m;
      poly_mul_right_congruence q
        (poly_power q (((n - 1) ++ m)))
        ((poly_power q (n - 1)) * (poly_power q m));
      mul_associativity q (poly_power q (n - 1)) (poly_power q m);
      poly_eq_symmetry
        ((q * (poly_power q (n - 1))) * (poly_power q m))
        (q * ((poly_power q (n - 1)) * (poly_power q m)));
      poly_eq_transitivity
        (poly_power q (n ++ m))
        (q * ((poly_power q (n - 1)) * (poly_power q m)))
        ((q * (poly_power q (n - 1))) * (poly_power q m))
    end

(* ================================================================ *)
(*  Ascent step: qⁿ | g ∧ q² | b₀ → q^(n+1) | g                    *)
(*  where g = gcd(p, D(p)), b₀ = p/g.                               *)
(*  Uses repeated_factor_divides_gcd with k = n+2.                  *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
private let g_ascent_step (#t:Type) {| f: field t |}
  (q p: polynomial t) (n: pos)
  : Lemma (requires (let g = poly_gcd p (poly_deriv p) in
                     let b0 = poly_div p g in
                     divides (poly_power q n) g /\
                     divides (poly_power q 2) b0 /\
                     deg q >= 1 /\
                     deg p >= 0))
          (ensures  (let g = poly_gcd p (poly_deriv p) in
                     divides (poly_power q (n ++ 1)) g))
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let g  = poly_gcd p (poly_deriv p) in
    let b0 = poly_div p g in
    (* Step 1: establish p ≈ g · b₀ *)
    gcd_has_degree p (poly_deriv p);
    gcd_divides_left p (poly_deriv p);
    poly_div_correct p g;
    (* poly_eq (poly_mul g b0) p *)
    (* Step 2: q^(n+2) | p *)
    divides_product (poly_power q n) g (poly_power q 2) b0;
    (* divides (poly_mul (poly_power q n) (poly_power q 2)) (poly_mul g b0) *)
    poly_power_add q n 2;
    poly_eq_symmetry (poly_power q (n ++ 2))
                     ((poly_power q n) * (poly_power q 2));
    divides_congruence_left 
      ((poly_power q n) * (poly_power q 2))
      (poly_power q (n ++ 2))
      (g * b0);
    (* divides (poly_power q (n+2)) (poly_mul g b0) *)
    divides_congruence_right 
      (poly_power q (n ++ 2))
      (g * b0) p;
    (* divides (poly_power q (n+2)) p *)
    (* Step 3: apply repeated_factor_divides_gcd *)
    repeated_factor_divides_gcd q p (n ++ 2)
    (* gives: divides (poly_power q (n+1)) (poly_gcd p (poly_deriv p)) = g *)
#pop-options

(* ================================================================ *)
(*  Full ascent: ∀n≥1. qⁿ | g                                       *)
(*  Base: q¹ | g (from q | p ∧ q | D(p) via gcd_is_maximal).        *)
(*  Step: n → n+1 via g_ascent_step.                                *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
let rec g_ascent (#t:Type) {| f: field t |}
  (q p: polynomial t) (n: pos)
  : Lemma (requires (let g = poly_gcd p (poly_deriv p) in
                     let b0 = poly_div p g in
                     divides q g /\
                     divides (poly_power q 2) b0 /\
                     deg q >= 1 /\
                     deg p >= 0))
          (ensures  (let g = poly_gcd p (poly_deriv p) in
                     divides (poly_power q n) g))
          (decreases n)
  = 
    let g  = poly_gcd p (poly_deriv p) in
    let b0 = poly_div p g in
    if n = 1 then begin
      (* poly_power q 1 = poly_mul q (poly_power q 0) = poly_mul q poly_one.
         Need: divides (poly_mul q poly_one) g, given divides q g.
         poly_mul q poly_one ≈ q by mul_one. *)
      H.elim_equatable_laws (polynomial t) ();
      poly_mul_one q;
      divides_congruence_left  q (poly_power q 1) g
    end else begin
      (* IH: poly_power q (n-1) | g *)
      g_ascent q p (n - 1);
      (* Step: g_ascent_step gives poly_power q n | g *)
      g_ascent_step q p (n - 1)
    end
#pop-options

(* ================================================================ *)
(*  Helper: (a+b) - b ≈ a (ring identity for polynomials)           *)
(* ================================================================ *)

private let poly_add_sub_cancel (#t:Type) {| cr: commutative_ring t |}
  (a b: polynomial t)
  : Lemma (ensures (((a + b) -- b) = a))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* x -- y == poly_add x (poly_neg y) by defeq *)
    (* Now SMT knows: (poly_add a b) -- b == poly_add (poly_add a b) (poly_neg b) *)
    (* (a+b) + (-b) ≈ a + (b + (-b)) ≈ a + 0 ≈ a *)
    add_associativity a b (- b);
    add_negation b;
    poly_add_congruence a (b + (- b)) a (poly_zero);
    add_zero a;
    let s1 = ((a + b) + (- b)) in
    let s2 = (a + (b + (- b))) in
    let s3 = (a + zero) in
    poly_eq_transitivity s1 s2 s3;
    poly_eq_transitivity s1 s3 a

(* ================================================================ *)
(*  Helper: d | (a+b) ∧ d | b → d | a                              *)
(* ================================================================ *)

private let divides_of_sum (#t:Type) {| f: field t |}
  (d a b: polynomial t)
  : Lemma (requires divides d (a + b) /\ divides d b)
          (ensures  divides d a)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* d | (a+b) and d | b → d | (a+b) + (-b) [divides_neg + divides_add] *)
    divides_neg  d b;
    divides_add  d (a + b) (- b);
    (* Now: divides d (poly_add (poly_add a b) (poly_neg b)) *)
    (* (a+b) + (-b) ≈ a + (b + (-b)) ≈ a + 0 ≈ a *)
    add_associativity a b (- b);
    add_negation b;
    poly_add_congruence a (b + (- b)) a (poly_zero);
    add_zero a;
    let s1 = ((a + b) + (- b)) in
    let s2 = (a + (b + (- b))) in
    let s3 = (a + zero) in
    divides_congruence_right  d
      ((a + b) + (- b)) a

(* ================================================================ *)
(*  q² | b₀: from irreducible q with q|b₀ and q|D(b₀) in char 0   *)
(* ================================================================ *)

(* Helper extracted from q_squared_divides_b0's inner aux2. Given b0 = q*r
   and r = q*s, conclude (poly_power q 2) | b0. Isolated as a top-level
   query so the poly_eq transitivity chain is not re-searched under fuel 4. *)
private let q_sq_divides_from_factor (#t:Type) {| f: field t |}
  (q r b0 s: polynomial t)
  : Lemma (requires (b0 = (q * r)) /\ (r = (q * s)))
          (ensures  divides (poly_power q 2) b0)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    poly_mul_right_congruence q r (q * s);
    mul_associativity q q s;
    assert ((q * r) = (q * (q * s)));
    poly_eq_transitivity (q * r) (q * (q * s))
                         ((q * q) * s);
    assert ((q * r) = ((q * q) * s));
    poly_mul_one q;
    poly_mul_right_congruence q q (q * (poly_one #t));
    assert ((q * q) = (poly_power q 2));
    poly_mul_left_congruence (q * q) (poly_power q 2) s;
    assert (((q * q) * s) = ((poly_power q 2) * s));
    poly_eq_transitivity (q * r) ((q * q) * s)
                         ((poly_power q 2) * s);
    assert ((q * r) = ((poly_power q 2) * s));
    divides_intro  (poly_power q 2) b0 s

#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
private let q_squared_divides_b0 (#t:Type) {| f: field t |}
  (q b0: polynomial t)
  : Lemma (requires char_zero f /\ poly_irreducible q /\
                    divides q b0 /\ divides q (poly_deriv b0))
          (ensures  divides (poly_power q 2) b0)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* q | b₀ means ∃r. b₀ ≈ q·r *)
    let aux (r: polynomial t)
      : Lemma (requires (b0 = (q * r)))
              (ensures  divides (poly_power q 2) b0)
      = (* D(b₀) ≈ D(q·r) ≈ D(q)·r + q·D(r) *)
        poly_deriv_congruence b0 (q * r);
        poly_deriv_mul q r;
        let dq  = poly_deriv q in
        let dr  = poly_deriv r in
        let sum = ((dq * r) + (q * dr)) in
        (* q | D(b₀), transfer to: q | sum *)
        divides_congruence_right  q (poly_deriv b0) sum;
        (* q | poly_mul q dr: q divides its own product *)
        divides_intro  q (q * dr) dr;
        (* q | sum and q | poly_mul q dr → q | poly_mul dq r *)
        divides_of_sum q (dq * r) (q * dr);
        (* Need: q | poly_mul r dq (commuted) for euclid_lemma *)
        mul_commutativity dq r;
        divides_congruence_right  q (dq * r) (r * dq);
        (* coprime(q, D(q)) → by euclid: q | r·D(q) → q | r *)
        irreducible_coprime_deriv q;
        euclid_lemma q dq r;
        (* q | r means ∃s. r ≈ q·s. Then b₀ ≈ q·r ≈ q·(q·s) = q²·s. *)
        let aux2 (s: polynomial t)
          : Lemma (requires (r = (q * s)))
                  (ensures  divides (poly_power q 2) b0)
          = q_sq_divides_from_factor q r b0 s
        in
        Classical.forall_intro (Classical.move_requires aux2)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

(* ================================================================ *)
(*  Degree of poly_power (strong bound): poly_deg (poly_power q n)   *)
(*  = n * deg(q). Needed for the contradiction in b0_is_sq_free.     *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 4 --ifuel 3"
private let rec poly_power_degree_bound (#t:Type) {| f: field t |}
  (q: polynomial t) (n: pos)
  : Lemma (requires deg q >= 1)
          (ensures  deg (poly_power q n) >= 0 /\
                    deg (poly_power q n) >= n)
          (decreases n)
  = if n = 1 then begin
      assert (poly_power q 0 == (poly_one #t));
      degree_mul q (poly_one #t)
    end else begin
      poly_power_degree_bound q (n - 1);
      degree_mul q (poly_power q (n - 1))
    end
#pop-options

(* ================================================================ *)
(*  Exact degree of poly_power: deg(q^n) = n * deg(q)               *)
(* ================================================================ *)

let rec poly_power_degree_exact (#t:Type) {| f: field t |}
  (q: polynomial t) (n: pos)
  : Lemma (requires deg q >= 0)
          (ensures  deg (poly_power q n) ==
                    n * (deg q))
          (decreases n)
  = if n = 1 then begin
      degree_mul q poly_one 
    end else begin
      poly_power_degree_exact q (n - 1); 
      degree_mul q (poly_power q (n - 1));
      calc (=) {
        deg q ++ ((n - 1) * deg q); = {}
        1 * deg q ++ ((n - 1) * deg q); = { right_distributivity (deg q) 1 (n - 1) }
        (1 ++ (n - 1)) * deg q; == {}
        n * deg q;
      }
    end

(* ================================================================ *)
(*  Degree of flat_product: deg(∏ ds) = Σ deg(dᵢ)                   *)
(* ================================================================ *)

#push-options "--z3rlimit 40 --fuel 4 --ifuel 2"
let rec degree_flat_product (#t:Type) {| f: field t |}
  (ds: list (polynomial t))
  : Lemma (requires (forall (k:nat). k < L.length ds ==> deg (L.index ds k) >= 0))
          (ensures  (match ds with
                     | [] -> deg (flat_product ds) == 0
                     | _  -> deg (flat_product ds) >= 0))
          (decreases ds)
  = match ds with
    | [] -> ()  (* flat_product [] = poly_one, deg poly_one = Some 0 *)
    | [d] ->
        (* flat_product [d] = poly_mul d poly_one. deg = deg d + 0 = deg d. *)
        degree_mul d (poly_one #t)
    | d :: rest ->
        assert (forall (k:nat). k < L.length rest ==>
                  L.index rest k == L.index (d :: rest) (k ++ 1));
        assert (forall (k:nat). k < L.length rest ==> deg (L.index rest k) >= 0);
        degree_flat_product rest;
        degree_mul d (flat_product rest)
#pop-options

(* ================================================================ *)
(*  Aux for b0_is_square_free: the product-rule sub-chain.          *)
(*  Given p ≈ g·b0 and q | b0, q | D(b0), conclude q | D(p).        *)
(* ================================================================ *)

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private let b0_sf_qdivD (#t:Type) {| f: field t |}
  (p g b0 q: polynomial t)
  : Lemma (requires divides q b0 /\ divides q (poly_deriv b0) /\
                    ((g * b0) = p))
          (ensures  divides q (poly_deriv p))
  =
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let dg  = poly_deriv g in
    let db0 = poly_deriv b0 in
    poly_deriv_mul g b0;
    poly_deriv_congruence (g * b0) p;
    (* q | (dg · b0): from q | b0 *)
    divides_mul_left  q dg b0;
    (* q | (g · D(b0)): from q | D(b0) *)
    divides_mul_left  q g db0;
    (* q | (dg·b0 + g·D(b0)) *)
    divides_add  q (dg * b0) (g * db0);
    (* q | D(p) by congruence:  D(p) = D(g·b0) = dg·b0 + g·db0 *)
    divides_congruence_right  q
      ((dg * b0) + (g * db0))
      (poly_deriv p)
#pop-options

(* ================================================================ *)
(*  Aux for b0_is_square_free: an irreducible factor q of           *)
(*  gcd(b0, D(b0)) leads to a contradiction (via q² | b0, q | g,    *)
(*  qⁿ | g for n = deg g + 1, contradicting finite degree).         *)
(* ================================================================ *)

#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
private let b0_sf_factor_absurd (#t:Type) {| f: field t |}
  (p g b0 gb q: polynomial t)
  : Lemma (requires char_zero f /\
                    poly_irreducible q /\ divides q gb /\
                    g  == poly_gcd p (poly_deriv p) /\
                    b0 == poly_div p g /\
                    gb == poly_gcd b0 (poly_deriv b0) /\
                    ((g * b0) = p) /\ deg p >= 0)
          (ensures  False)
  =
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* 3b+3c (q | g) FIRST, in the CLEAN context (only this lemma's own
       preconditions, no derived `divides q _` clutter yet): the FOCUSED NESTED
       helper re-derives q|b0, q|D(b0), q|p, q|D(p) and concludes q | g from the
       single hypothesis `divides q gb`.  Doing it first means its goal discharge
       does NOT run an existential `divides`-witness search over the products
       introduced by steps 1-2 below.  Kept NESTED so it installs no global
       quantified axiom. *)
    let q_div_g (_: unit)
      : Lemma (ensures divides q g)
      = gcd_divides_left b0 (poly_deriv b0);
        gcd_divides_right b0 (poly_deriv b0);
        divides_trans  q gb b0;
        divides_trans  q gb (poly_deriv b0);
        mul_commutativity g b0;
        divides_intro  b0 p g;
        divides_trans  q b0 p;
        b0_sf_qdivD p g b0 q;             (* q | D(p) — fresh, uncluttered *)
        gcd_is_maximal p (poly_deriv p) q (* q | gcd(p,D(p)) = g *)
    in
    q_div_g ();
    (* Step 1: q | b0 and q | D(b0) *)
    gcd_divides_left b0 (poly_deriv b0);
    gcd_divides_right b0 (poly_deriv b0);
    divides_trans  q gb b0;
    divides_trans  q gb (poly_deriv b0);
    (* Step 2: q² | b0 via q_squared_divides_b0 *)
    q_squared_divides_b0 q b0;
    (* Step 4: g_ascent → q^n | g for n = deg g + 1 *)
    let n : pos = ((deg g) ++ 1) in
    g_ascent q p n;
    (* Step 5: contradiction via degree *)
    poly_power_degree_bound q n;
    divides_degree_le (poly_power q n) g
    (* deg(poly_power q n) >= n = deg g + 1 > deg g,
       but divides_degree_le says deg(poly_power q n) <= deg g. Contradiction. *)
#pop-options

(* ================================================================ *)
(*  b₀ is square-free: the main theorem                             *)
(*                                                                  *)
(*  If g = gcd(p, p'), b₀ = p/g, then square_free(b₀).              *)
(*  Proof by contradiction: assume ¬square_free(b₀). Extract an     *)
(*  irreducible factor q of gcd(b₀, D(b₀)). Show q² | b₀, then     *)
(*  q | g by gcd_is_maximal, then iterate g_ascent to get qⁿ | g    *)
(*  for all n, contradicting finite degree of g.                     *)
(*                                                                  *)
(*  Requires characteristic zero (for D(q) degree bound).           *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
let b0_is_square_free (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires char_zero f /\ deg p >= 1)
         (ensures  (let g = poly_gcd p (poly_deriv p) in
                    let b0 = poly_div p g in
                    square_free b0))
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();     
    let g  = poly_gcd p (poly_deriv p) in
    let b0 = poly_div p g in
    (* Establish p ≈ g·b0 *)
    gcd_has_degree p (poly_deriv p);
    gcd_divides_left p (poly_deriv p);
    poly_div_correct p g;
    (* poly_eq (poly_mul g b0) p *)
    (* Proof by contradiction: assume ~(square_free b0) *)
    Classical.excluded_middle (square_free b0 = true);
    let case_not_sf (_: unit)
      : Lemma (requires square_free b0 <> true)
              (ensures  False)
      = (* square_free b0 = coprime b0 (poly_deriv b0) = false means
           gcd(b0, D(b0)) has degree != 0, hence >= 1 *)
        coprime_reveal b0 (poly_deriv b0);
        (* Need: deg b0 >= 0 — from p ≈ g·b0, deg p = deg g + deg b0 *)
        mul_commutativity g b0;
        divides_intro  b0 p g;
        divides_degree_le b0 p;
        (* gcd_has_degree for b0 and D(b0): *)
        gcd_has_degree b0 (poly_deriv b0);
        let gb = poly_gcd b0 (poly_deriv b0) in
        (* gb has degree >= 1 (from coprime_reveal + square_free = false) *)
        (* irreducible_factor_exists on gb *)
        irreducible_factor_exists gb;
        let aux_q (q: polynomial t)
          : Lemma (requires poly_irreducible q /\ divides q gb)
                  (ensures  False)
          = (* Step 1: q | b0 and q | D(b0) *)
            gcd_divides_left b0 (poly_deriv b0);
            gcd_divides_right b0 (poly_deriv b0);
            divides_trans  q gb b0;
            divides_trans  q gb (poly_deriv b0);
            (* Step 2: q² | b0 via q_squared_divides_b0 *)
            q_squared_divides_b0 q b0;
            (* Step 3: Show q | g *)
            (* 3a: q | p (from q | b0 and b0 | p) *)
            divides_trans  q b0 p;
            (* 3b: q | D(p) via product rule on p ≈ g·b0 *)
            let dg  = poly_deriv g in
            let db0 = poly_deriv b0 in
            poly_deriv_mul g b0;
            poly_deriv_congruence (g * b0) p;
            poly_eq_transitivity (poly_deriv p) (poly_deriv (g * b0))
              ((dg * b0) + (g * db0));
            (* q | (dg · b0): from q | b0 *)
            divides_mul_left  q dg b0;
            (* q | (g · D(b0)): from q | D(b0) *)
            divides_mul_left  q g db0;
            (* q | (dg·b0 + g·D(b0)) *)
            divides_add  q (dg * b0) (g * db0);
            (* q | D(p) by congruence *)
            poly_eq_symmetry (poly_deriv p)
              ((dg * b0) + (g * db0));
            divides_congruence_right  q
              ((dg * b0) + (g * db0))
              (poly_deriv p);
            (* 3c: q | p and q | D(p) → q | gcd(p, D(p)) = g *)
            gcd_is_maximal p (poly_deriv p) q;
            (* Step 4: g_ascent → q^n | g for all n *)
            (* Pick n = deg(g) + 1 *)
            let n : pos = ((deg g) ++ 1) in
            g_ascent q p n;
            (* Step 5: contradiction via degree *)
            poly_power_degree_bound q n;
            divides_degree_le (poly_power q n) g
            (* deg(poly_power q n) >= n = deg g + 1 > deg g,
               but divides_degree_le says deg(poly_power q n) <= deg g. Contradiction. *)
        in
        Classical.forall_intro (Classical.move_requires aux_q)
    in
    Classical.move_requires case_not_sf ()
#pop-options

(* ================================================================ *)
(*  Divisor of a square-free polynomial is square-free               *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
let divisor_of_square_free (#t:Type) {| f: field t |}
  (d b0: polynomial t)
  : Lemma (requires char_zero f /\ square_free b0 /\
                   divides d b0 /\ deg d >= 0 /\ deg b0 >= 0)
          (ensures  square_free d)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    Classical.excluded_middle (square_free d = true);
    let case_not (_: unit)
      : Lemma (requires square_free d <> true)
              (ensures  False)
      = coprime_reveal d (poly_deriv d);
        gcd_has_degree d (poly_deriv d);
        let gd = poly_gcd d (poly_deriv d) in
        irreducible_factor_exists gd;
        let aux_q (q: polynomial t)
          : Lemma (requires poly_irreducible q /\ divides q gd)
                 (ensures  False)
          = (* q | d and q | D(d) *)
            gcd_divides_left d (poly_deriv d);
            gcd_divides_right d (poly_deriv d);
            divides_trans  q gd d;
            divides_trans  q gd (poly_deriv d);
            (* q² | d via q_squared_divides_b0 applied to d *)
            q_squared_divides_b0 q d;
            (* q² | b₀ by transitivity *)
            divides_trans  (poly_power q 2) d b0;
            (* q | D(b₀) via repeated_factor_divides_deriv *)
            repeated_factor_divides_deriv q b0 2;
            (* poly_power q 1 | D(b₀), bridge to q | D(b₀) *)
            poly_mul_one q;
            divides_congruence_left 
              (poly_power q 1) q (poly_deriv b0);
            (* q | b₀ (from q | d | b₀) *)
            divides_trans  q d b0;
            (* q | gcd(b₀, D(b₀)) *)
            gcd_is_maximal b0 (poly_deriv b0) q;
            (* But square_free b₀ means deg(gcd(b₀, D(b₀))) = 0 *)
            coprime_reveal b0 (poly_deriv b0);
            gcd_has_degree b0 (poly_deriv b0);
            divides_degree_le q (poly_gcd b0 (poly_deriv b0))
            (* deg q >= 1 but deg(gcd) = 0, contradiction *)
        in
        Classical.forall_intro (Classical.move_requires aux_q)
    in
    Classical.move_requires case_not ()
#pop-options

(* ================================================================ *)
(*  Square-free product → coprime factors                            *)
(* ================================================================ *)

(* If p is square-free and p ≈ a·b, then coprime(a, b).
   Proof: if q | a and q | b (irreducible q), then q² | a·b ≈ p,
   so q | D(p), hence q | gcd(p, D(p)) — contradicts coprime(p, D(p)). *)

#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
let square_free_coprime_factors (#t:Type) {| f: field t |}
  (p a b: polynomial t)
  : Lemma (requires char_zero f /\ square_free p /\
                    (p = (a * b)) /\
                    deg p >= 0 /\ deg a >= 0 /\ deg b >= 0)
          (ensures  coprime a b)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    coprime_reveal a b;
    Classical.excluded_middle (coprime a b = true);
    let case_not (_: unit)
      : Lemma (requires coprime a b <> true)
              (ensures  False)
      = gcd_has_degree a b;
        let gab = poly_gcd a b in
        irreducible_factor_exists gab;
        let aux_q (q: polynomial t)
          : Lemma (requires poly_irreducible q /\ divides q gab)
                  (ensures  False)
          = gcd_divides_left a b;
            gcd_divides_right a b;
            divides_trans  q gab a;
            divides_trans  q gab b;
            (* q|a and q|b → q²|a·b via divides_product *)
            divides_product q a q b;
            (* Bridge: poly_eq (poly_mul q q) (poly_power q 2) *)
            (* poly_power q 2 == poly_mul q (poly_mul q poly_one) definitionally *)
            assert (poly_power q 2 == (q * (q * (poly_one #t))));
            (* poly_mul_one q: poly_eq (poly_mul q poly_one) q *)
            poly_mul_one q;
            (* symmetry: poly_eq q (poly_mul q poly_one) *)
            (* poly_mul_right_congruence q q (poly_mul q poly_one):
               requires poly_eq q (poly_mul q poly_one)
               gives poly_eq (poly_mul q q) (poly_mul q (poly_mul q poly_one)) *)
            poly_mul_right_congruence q q (q * (poly_one #t));
            (* So: poly_eq (poly_mul q q) (poly_power q 2) *)
            divides_congruence_left 
              (q * q) (poly_power q 2) (a * b);
            (* q² | a·b, transfer to: q² | p *)
            divides_congruence_right 
              (poly_power q 2) (a * b) p;
            (* q² | p → poly_power q 1 | D(p) *)
            repeated_factor_divides_deriv q p 2;
            (* Bridge: poly_power q 1 ≈ q, so divides q (poly_deriv p) *)
            poly_mul_one q;
            divides_congruence_left 
              (poly_power q 1) q (poly_deriv p);
            (* q | p: from q | a, a | a·b ≈ p *)
            divides_intro  a (a * b) b;
            divides_trans  q a (a * b);
            divides_congruence_right 
              q (a * b) p;
            (* q | gcd(p, D(p)) *)
            gcd_is_maximal p (poly_deriv p) q;
            (* But square_free p → deg(gcd(p, D(p))) = 0 *)
            coprime_reveal p (poly_deriv p);
            gcd_has_degree p (poly_deriv p);
            divides_degree_le q (poly_gcd p (poly_deriv p))
        in
        Classical.forall_intro (Classical.move_requires aux_q)
    in
    Classical.move_requires case_not ()
#pop-options

(* ================================================================ *)
(*  coprime(a, b) and d|b → coprime(a, d)                           *)
(* ================================================================ *)

let coprime_of_divisor (#t:Type) {| f: field t |}
  (a b d: polynomial t)
  : Lemma (requires coprime a b /\ divides d b /\ deg a >= 0)
          (ensures  coprime a d)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    coprime_reveal a d;
    let gad = poly_gcd a d in
    gcd_has_degree a d;
    (* gad | a and gad | d *)
    gcd_divides_left a d;
    gcd_divides_right a d;
    (* gad | b (transitivity: gad | d | b) *)
    divides_trans  gad d b;
    (* gad | gcd(a, b) by maximality *)
    gcd_is_maximal a b gad;
    (* deg(gcd(a, b)) = 0 from coprime(a, b) *)
    coprime_reveal a b;
    gcd_has_degree a b;
    (* deg(gad) ≤ deg(gcd(a,b)) = 0 *)
    divides_degree_le gad (poly_gcd a b);    
    assert (deg (poly_gcd a d) <= 0)

(* ================================================================ *)
(*  coprime(gcd(b,d), b/gcd(b,d)) when b is square-free             *)
(* ================================================================ *)

(* At each Yun step, the factor aₖ = gcd(b,d) is coprime with
   the quotient bₖ = b/aₖ, because b is square-free and b = aₖ · bₖ. *)
let yun_step_coprime (#t:Type) {| f: field t |}
  (b d: polynomial t)
  : Lemma (requires char_zero f /\ square_free b /\
                    deg b >= 1)
          (ensures  (let a = poly_gcd b d in
                     let b' = poly_div b a in
                     coprime a b'))
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let a = poly_gcd b d in
    let b' = poly_div b a in
    gcd_has_degree b d;
    gcd_divides_left b d;
    poly_div_correct b a;
    poly_div_nonzero b a;
    (* poly_eq (poly_mul a b') b *)
    (* b is square-free, so coprime(a, b') *)
    square_free_coprime_factors b a b'

(* ================================================================ *)
(*  coprime(aₖ, aⱼ) for j > k: aⱼ divides bₖ, coprime(aₖ, bₖ)     *)
(* ================================================================ *)

(* coprime is symmetric (via mutual divisibility of gcds) *)
let coprime_symmetric (#t:Type) {| f: field t |}
  (a b: polynomial t)
  : Lemma (requires coprime a b /\ deg a >= 0 /\ deg b >= 0)
          (ensures  coprime b a)
  = 
    coprime_reveal a b;
    coprime_reveal b a;
    let gab = poly_gcd a b in
    let gba = poly_gcd b a in
    gcd_has_degree a b;
    gcd_has_degree b a;
    (* gab | a, gab | b → gab | gcd(b, a) *)
    gcd_divides_left a b;
    gcd_divides_right a b;
    gcd_is_maximal b a gab;
    (* gba | b, gba | a → gba | gcd(a, b) *)
    gcd_divides_left b a;
    gcd_divides_right b a;
    gcd_is_maximal a b gba;
    (* deg(gba) ≤ deg(gab) = 0, and deg(gab) ≤ deg(gba) *)
    divides_degree_le gba gab

(* ================================================================ *)
(*  List helpers for Yun loop index reasoning                        *)
(* ================================================================ *)

private let rec append_index_left (#a:Type) (l1: list a) (l2: list a)
  (k: nat{k < L.length l1})
  : Lemma (ensures k < L.length (L.append l1 l2) /\
                   L.index (L.append l1 l2) k == L.index l1 k)
          (decreases l1)
  = match l1 with
    | h :: t ->
        L.append_length l1 l2;
        if k = 0 then ()
        else begin
          append_index_left t l2 (k - 1)
        end

private let rec append_snoc_index (#a:Type) (l1: list a) (x: a)
  : Lemma (ensures L.length (L.append l1 [x]) == ((L.length l1) ++ 1) /\
                   L.index (L.append l1 [x]) (L.length l1) == x)
          (decreases l1)
  = match l1 with
    | [] -> ()
    | _ :: t -> append_snoc_index t x

(* The yun_loop output is always at least as long as acc *)
private let rec yun_loop_acc_length (#t:Type) {| f: field t |}
  (b d: polynomial t) (acc: list (polynomial t)) (fuel: nat)
  : Lemma (ensures L.length (yun_loop b d acc fuel) >= L.length acc)
          (decreases fuel)
  = if fuel = 0 then L.append_length acc [b]
    else if deg b < 0 then L.append_length acc [b]
    else if deg b = 0 then L.append_length acc [b]
    else begin
      let a = poly_gcd b d in
      let b' = poly_div b a in
      let c' = poly_div d a in
      let d' = (c' -- (poly_deriv b')) in
      let acc' = L.append acc [a] in
      yun_loop_acc_length b' d' acc' (fuel - 1);
      L.append_length acc [a]
    end

(* Elements originally in acc are preserved in yun_loop output *)
private let rec yun_loop_preserves_acc (#t:Type) {| f: field t |}
  (b d: polynomial t) (acc: list (polynomial t)) (fuel: nat)
  (k: nat{k < L.length acc})
  : Lemma (ensures k < L.length (yun_loop b d acc fuel) /\
                   L.index (yun_loop b d acc fuel) k == L.index acc k)
          (decreases fuel)
  = yun_loop_acc_length b d acc fuel;
    if fuel = 0 then
      append_index_left acc [b] k
    else if deg b < 0 then
      append_index_left acc [b] k
    else if deg b = 0 then
      append_index_left acc [b] k
    else begin
      let a = poly_gcd b d in
      let b' = poly_div b a in
      let c' = poly_div d a in
      let d' = (c' -- (poly_deriv b')) in
      let acc' = L.append acc [a] in
      L.append_length acc [a];
      append_index_left acc [a] k;
      yun_loop_preserves_acc b' d' acc' (fuel - 1) k
    end

(* ================================================================ *)
(*  Coprimality of Yun loop factors (internals)                      *)
(* ================================================================ *)

(* Old acc element coprime with all NEW output factors from the loop.
   Requires: acc[k] is coprime with b (the current quotient). *)
#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
private let rec yun_loop_old_coprime_new (#t:Type) {| f: field t |}
  (b d: polynomial t) (acc: list (polynomial t)) (fuel: nat)
  (k: nat) (j: nat)
  : Lemma (requires char_zero f /\ square_free b /\ deg b >= 0 /\
                    k < L.length acc /\ j >= L.length acc /\
                    j < L.length (yun_loop b d acc fuel) /\
                    deg (L.index acc k) >= 0 /\
                    coprime (L.index acc k) b)
          (ensures  coprime (L.index acc k) (L.index (yun_loop b d acc fuel) j))
          (decreases fuel)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if fuel = 0 then begin
      (* result = append acc [b], j = |acc|, output[j] = b *)
      L.append_length acc [b];
      append_snoc_index acc b
      (* coprime (acc[k]) b is given *)
    end
    else if deg b < 0 then begin
      (* result = append acc [b], j = |acc|, output[j] = b *)
      L.append_length acc [b];
      append_snoc_index acc b
    end
    else if deg b = 0 then begin
      (* result = append acc [b], j = |acc|, output[j] = b *)
      L.append_length acc [b];
      append_snoc_index acc b
    end
    else begin
      let a = poly_gcd b d in
      let b' = poly_div b a in
      let c' = poly_div d a in
      let d' = (c' -- (poly_deriv b')) in
      let acc' = L.append acc [a] in
      L.append_length acc [a];
      if j = L.length acc then begin
        (* output[j] = a (preserved from acc') *)
        yun_loop_preserves_acc b' d' acc' (fuel - 1) j;
        append_snoc_index acc a;
        (* coprime(acc[k], a): acc[k] coprime with b, and a | b *)
        gcd_divides_left b d;
        gcd_has_degree b d;
        coprime_of_divisor (L.index acc k) b a
      end
      else begin
        (* j > |acc|, so j >= |acc'| *)
        (* Need: coprime(acc[k], b') and square_free b' for the IH *)
        gcd_has_degree b d;
        gcd_divides_left b d;
        poly_div_correct b a;
        poly_div_nonzero b a;
        (* b' | b: from b ≈ a · b' *)
        mul_commutativity a b';
        divides_intro  b' b a;
        (* square_free b' by divisor_of_square_free *)
        divisor_of_square_free b' b;
        (* coprime(acc[k], b') by coprime_of_divisor *)
        coprime_of_divisor (L.index acc k) b b';
        (* Prepare for IH: acc'[k] == acc[k] *)
        append_index_left acc [a] k;
        (* Apply IH *)
        yun_loop_old_coprime_new b' d' acc' (fuel - 1) k j
      end
    end
#pop-options

(* New factor at step coprime with all LATER output factors.
   Uses: coprime(a, b') from yun_step_coprime, then old_coprime_new. *)
#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
private let yun_loop_new_coprime_later (#t:Type) {| f: field t |}
  (b d: polynomial t) (acc: list (polynomial t)) (fuel: nat)
  (j: nat)
  : Lemma (requires char_zero f /\ square_free b /\ deg b >= 1 /\
                    j > L.length acc /\
                    j < L.length (yun_loop b d acc fuel))
          (ensures  coprime (L.index (yun_loop b d acc fuel) (L.length acc))
                                  (L.index (yun_loop b d acc fuel) j))
  =
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if fuel = 0 then begin
      (* result = append acc [b], |output| = |acc|+1, j > |acc| → j >= |acc|+1 but j < |acc|+1: impossible *)
      L.append_length acc [b]
    end
    else if deg b < 0 then
      (* result = append acc [b], |result| = |acc|+1, j > |acc| → j >= |acc|+1 but j < |acc|+1: impossible *)
      L.append_length acc [b]
    else if deg b = 0 then
      (* result = append acc [b], |result| = |acc|+1, j > |acc| → j >= |acc|+1 but j < |acc|+1: impossible *)
      L.append_length acc [b]
    else begin
      let a = poly_gcd b d in
      let b' = poly_div b a in
      let c' = poly_div d a in
      let d' = (c' -- (poly_deriv b')) in
      let acc' = L.append acc [a] in
      L.append_length acc [a];
      (* output[|acc|] = a (preserved from acc') *)
      yun_loop_preserves_acc b' d' acc' (fuel - 1) (L.length acc);
      append_snoc_index acc a;
      (* Establish key facts about a and b' *)
      gcd_has_degree b d;
      gcd_divides_left b d;
      poly_div_correct b a;
      poly_div_nonzero b a;
      (* b' divides b: from b ≈ a · b' → b ≈ b' · a *)
      mul_commutativity a b';
      divides_intro  b' b a;
      (* square_free b' by divisor_of_square_free *)
      divisor_of_square_free b' b;
      (* coprime(a, b') from yun_step_coprime *)
      yun_step_coprime b d;
      (* j >= |acc'| = |acc|+1, so apply yun_loop_old_coprime_new on (b', d', acc', fuel-1, |acc|, j) *)
      (* acc'[|acc|] = a and coprime(a, b') *)
      yun_loop_old_coprime_new b' d' acc' (fuel - 1) (L.length acc) j
    end
#pop-options


(* ================================================================ *)
(*  Yun loop factors are square-free                                 *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
private let rec yun_loop_square_free (#t:Type) {| f: field t |}
  (b d: polynomial t) (acc: list (polynomial t)) (fuel: nat) (k: nat)
  : Lemma (requires char_zero f /\ square_free b /\ deg b >= 0 /\
                    k >= L.length acc /\ k < L.length (yun_loop b d acc fuel))
          (ensures  square_free (L.index (yun_loop b d acc fuel) k))
          (decreases fuel)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if fuel = 0 then begin
      (* result = append acc [b], k >= |acc|, k < |acc|+1 → k = |acc| *)
      L.append_length acc [b];
      append_snoc_index acc b
      (* L.index result k = b, and square_free b is in the requires *)
    end
    else if deg b < 0 then ()  (* impossible: contradicts deg b >= 0 *)
    else if deg b = 0 then begin
      (* result = append acc [b], k = |acc|, factor at k is b *)
      L.append_length acc [b];
      append_snoc_index acc b;
      (* b has degree 0 → L.length b = 1 → poly_deriv b = poly_zero *)
      poly_deriv_const b;
      (* poly_gcd b (poly_deriv b) == poly_gcd b poly_zero == b *)
      poly_gcd_base b (poly_deriv b)
      (* poly_deg(gcd(b, D(b))) = deg b = 0 → coprime → square_free *)
    end
    else begin
      let a = poly_gcd b d in
      let b' = poly_div b a in
      let c' = poly_div d a in
      let d' = (c' -- (poly_deriv b')) in
      let acc' = L.append acc [a] in
      L.append_length acc [a];
      if k = L.length acc then begin
        (* Factor at index |acc| is a = gcd(b, d) *)
        yun_loop_preserves_acc b' d' acc' (fuel - 1) k;
        append_snoc_index acc a;
        (* L.index result k == a *)
        (* a | b by gcd_divides_left *)
        gcd_divides_left b d;
        gcd_has_degree b d;
        (* square_free a by divisor_of_square_free *)
        divisor_of_square_free a b
      end
      else begin
        (* k > |acc|, so k >= |acc'| *)
        (* Need: square_free b' /\ deg b' >= 0 *)
        yun_step_reconstruction b d;
        (* poly_eq (poly_mul a b') b *)
        gcd_has_degree b d;
        poly_div_nonzero b a;
        (* deg b' >= 0 *)
        (* divides b' b: from poly_eq (poly_mul a b') b *)
        mul_commutativity a b';
        divides_intro  b' b a;
        (* square_free b' by divisor_of_square_free *)
        divisor_of_square_free b' b;
        (* Apply IH *)
        yun_loop_square_free b' d' acc' (fuel - 1) k
      end
    end
#pop-options

(* ================================================================ *)
(*  Top-level: Yun output factors are square-free                    *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
let yun_factors_square_free (#t:Type) {| f: field t |}
  (p: polynomial t) (k: nat)
  : Lemma (requires char_zero f /\ deg p >= 1 /\
                    k < L.length (yun p))
          (ensures  square_free (L.index (yun p) k))
  = let p' = poly_deriv p in
    let a0 = poly_gcd p p' in
    let b0 = poly_div p a0 in
    let c0 = poly_div p' a0 in
    let d0 = (c0 -- (poly_deriv b0)) in
    let fuel = (if deg a0 < 0 then 0 else ((deg a0) ++ 1)) in
    (* b₀ is square-free by b0_is_square_free *)
    gcd_has_degree p p';
    gcd_divides_left p p';
    poly_div_correct p a0;
    poly_div_nonzero p a0;
    b0_is_square_free p;
    (* b₀ has positive degree (from poly_div_nonzero) *)
    yun_loop_square_free b0 d0 [] fuel k
#pop-options

(* ================================================================ *)
(*  Pairwise coprimality of Yun output factors                       *)
(* ================================================================ *)

(* Any two distinct NEW factors from the loop are coprime. *)
#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
private let rec yun_loop_pairwise_coprime (#t:Type) {| f: field t |}
  (b d: polynomial t) (acc: list (polynomial t)) (fuel: nat)
  (i j: nat)
  : Lemma (requires char_zero f /\ square_free b /\ deg b >= 0 /\
                    i >= L.length acc /\ i < j /\
                    j < L.length (yun_loop b d acc fuel))
          (ensures  coprime (L.index (yun_loop b d acc fuel) i)
                                  (L.index (yun_loop b d acc fuel) j))
          (decreases fuel)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if fuel = 0 then begin
      (* output = append acc [b], so |output| = |acc|+1, i >= |acc|, j < |acc|+1 *)
      (* → i = |acc|, j >= |acc|+1 impossible: contradiction *)
      L.append_length acc [b]
    end
    else if deg b < 0 then
      (* result = append acc [b], |result| = |acc|+1, i >= |acc|, i < j < |acc|+1: impossible *)
      L.append_length acc [b]
    else if deg b = 0 then
      (* result = append acc [b], |result| = |acc|+1, i >= |acc|, i < j < |acc|+1: impossible *)
      L.append_length acc [b]
    else begin
      let a = poly_gcd b d in
      let b' = poly_div b a in
      let c' = poly_div d a in
      let d' = (c' -- (poly_deriv b')) in
      let acc' = L.append acc [a] in
      L.append_length acc [a];
      if i = L.length acc then
        (* i is the current gcd, j > i, use yun_loop_new_coprime_later *)
        yun_loop_new_coprime_later b d acc fuel j
      else begin
        (* i > |acc|, so i >= |acc'|. Recurse. *)
        (* Need: square_free b', deg b' >= 0, deg b' >= 1 *)
        gcd_has_degree b d;
        gcd_divides_left b d;
        poly_div_correct b a;
        poly_div_nonzero b a;
        mul_commutativity a b';
        divides_intro  b' b a;
        divisor_of_square_free b' b;
        yun_loop_pairwise_coprime b' d' acc' (fuel - 1) i j
      end
    end
#pop-options

(* Top-level: Yun output factors are pairwise coprime. *)
#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
let yun_factors_coprime (#t:Type) {| f: field t |}
  (p: polynomial t) (i j: nat)
  : Lemma (requires char_zero f /\ deg p >= 1 /\
                    i < j /\ j < L.length (yun p))
          (ensures  coprime (L.index (yun p) i)
                                  (L.index (yun p) j))
  = let p' = poly_deriv p in
    let a0 = poly_gcd p p' in
    let b0 = poly_div p a0 in
    let c0 = poly_div p' a0 in
    let d0 = (c0 -- (poly_deriv b0)) in
    let fuel = (if deg a0 < 0 then 0 else ((deg a0) ++ 1)) in
    gcd_has_degree p p';
    gcd_divides_left p p';
    poly_div_correct p a0;
    poly_div_nonzero p a0;
    b0_is_square_free p;
    yun_loop_pairwise_coprime b0 d0 [] fuel i j
#pop-options

(* ================================================================ *)
(*  Powered product infrastructure: poly_power lemmas                *)
(* ================================================================ *)

(* poly_power p 0 = poly_one definitionally *)

private let poly_power_one (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t)
  : Lemma ((poly_power p 1) = p)
  = (* poly_power p 1 == poly_mul p (poly_power p 0) == poly_mul p poly_one *)
    poly_mul_one p

private let rec poly_power_congruence (#t:Type) {| cr: commutative_ring t |}
  (a b: polynomial t) (n: nat)
  : Lemma (requires (a = b))
          (ensures  ((poly_power a n) = (poly_power b n)))
          (decreases n)
  = if n = 0 then poly_eq_reflexivity (poly_one #t)
    else begin
      poly_power_congruence a b (n - 1);
      poly_mul_congruence a (poly_power a (n-1)) b (poly_power b (n-1))
    end

(* (a · b)^n ≈ a^n · b^n in a commutative ring *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec poly_power_mul (#t:Type) {| cr: commutative_ring t |}
  (a b: polynomial t) (n: nat)
  : Lemma (ensures (poly_power (a * b) n) =
                           ((poly_power a n) * (poly_power b n)))
          (decreases n)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if n = 0 then begin
      (* Both sides: poly_one. LHS = poly_power (a·b) 0 = poly_one.
         RHS = poly_mul (poly_power a 0) (poly_power b 0) = poly_mul poly_one poly_one ≈ poly_one. *)
      poly_mul_one (poly_one #t);
      poly_eq_symmetry ((poly_one #t) * (poly_one #t)) (poly_one #t)
    end
    else begin
      let ab = (a * b) in
      let an1 = poly_power a (n-1) in
      let bn1 = poly_power b (n-1) in
      poly_power_mul a b (n-1);
      (* IH: (a·b)^(n-1) ≈ a^(n-1) · b^(n-1) *)
      poly_mul_right_congruence ab (poly_power ab (n-1)) (an1 * bn1);
      (* (a·b)·(a·b)^(n-1) ≈ (a·b)·(a^(n-1)·b^(n-1)) *)
      let x = (an1 * bn1) in
      (* Rearrange (a·b)·(an1·bn1) to (a·an1)·(b·bn1): *)
      mul_associativity a b x;
      (* ab·x ≈ a·(b·x) *)
      mul_associativity b an1 bn1;
      mul_commutativity b an1;
      poly_mul_left_congruence (b * an1) (an1 * b) bn1;
      mul_associativity an1 b bn1;
      (* b·(an1·bn1) ≈ (b·an1)·bn1 ≈ (an1·b)·bn1 ≈ an1·(b·bn1) *)
      let m1 = (b * x) in
      let m2 = ((b * an1) * bn1) in
      let m3 = ((an1 * b) * bn1) in
      let m4 = (an1 * (b * bn1)) in
      poly_mul_right_congruence a m1 m4;
      mul_associativity a an1 (b * bn1);
      poly_eq_symmetry ((a * an1) * (b * bn1))
                       (a * (an1 * (b * bn1)));
      (* Full chain *)
      let lhs = poly_power ab n in
      let s1 = (ab * x) in
      let s2 = (a * m1) in
      let s3 = (a * m4) in
      let rhs = ((a * an1) * (b * bn1)) in
      poly_eq_transitivity lhs s3 rhs
    end
#pop-options

(* powered_product_aux distributes over snoc *)
#push-options "--z3rlimit 60 --fuel 3 --ifuel 2"
let rec powered_product_aux_snoc (#t:Type) {| cr: commutative_ring t |}
  (xs: list (polynomial t)) (y: polynomial t) (s: pos)
  : Lemma (ensures (powered_product_aux (L.append xs [y]) s) =
                           ((powered_product_aux xs s)
                                     * (poly_power y ((s ++ (L.length xs))))))
          (decreases xs)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    match xs with
    | [] ->
        (* LHS = pp_aux [y] s = poly_mul (poly_power y s) poly_one
           RHS = poly_mul poly_one (poly_power y s)
           Both ≈ poly_power y s *)
        poly_mul_one (poly_power y s);
        mul_commutativity (poly_one #t) (poly_power y s);
        poly_eq_transitivity
          ((poly_power y s) * (poly_one #t))
          (poly_power y s)
          ((poly_one #t) * (poly_power y s));
        poly_eq_symmetry
          ((poly_power y s) * (poly_one #t))
          ((poly_one #t) * (poly_power y s))
    | a :: rest ->
        (* LHS = poly_mul (poly_power a s) (pp_aux(append rest [y], s+1))
           IH: pp_aux(append rest [y], s+1) ≈ pp_aux(rest, s+1) · poly_power y (s+1+|rest|)
           RHS = poly_mul (poly_mul (poly_power a s) (pp_aux rest (s+1))) (poly_power y (s+1+|rest|))
           Chain via assoc *)
        let s1 : pos = (s ++ 1) in
        powered_product_aux_snoc rest y s1;
        let pas = poly_power a s in
        let pp_rest = powered_product_aux rest s1 in
        let py = poly_power y ((s1 ++ (L.length rest))) in
        poly_mul_right_congruence pas
          (powered_product_aux (L.append rest [y]) s1)
          (pp_rest * py);
        mul_associativity pas pp_rest py;
        poly_eq_symmetry ((pas * pp_rest) * py)
                         (pas * (pp_rest * py));
        poly_eq_transitivity
          (pas * (powered_product_aux (L.append rest [y]) s1))
          (pas * (pp_rest * py))
          ((pas * pp_rest) * py)
#pop-options

(* ================================================================ *)
(*  Coprimality with products and powers                             *)
(* ================================================================ *)

(* coprime(a, b) ∧ coprime(a, c) → coprime(a, b·c)
   Proof via Euclid's lemma: let g = gcd(a, b·c).
   g|a, coprime(a,b) → coprime(g,b) [coprime_divisor].
   coprime(g,b), g|b·c → g|c [euclid_lemma].
   g|a, g|c → g|gcd(a,c). coprime(a,c) → deg(gcd(a,c))=0.
   divides_degree_le gives deg(g) = 0. *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let coprime_mul_right (#t:Type) {| f: field t |}
  (a b c: polynomial t)
  : Lemma (requires coprime a b /\ coprime a c /\ deg a >= 0)
          (ensures  coprime a (b * c))
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    coprime_reveal a (b * c);
    let g = poly_gcd a (b * c) in
    gcd_has_degree a (b * c);
    gcd_divides_left a (b * c);
    gcd_divides_right a (b * c);
    (* g | a and coprime(a, b): coprime(g, b) *)
    coprime_divisor a b g;
    (* g | b·c, need g | c·b for euclid_lemma g b c *)
    mul_commutativity b c;
    divides_congruence_right  g (b * c) (c * b);
    (* euclid_lemma g b c: coprime(g,b) ∧ g|(c·b) ⟹ g|c *)
    euclid_lemma g b c;
    (* g | a and g | c → g | gcd(a, c) *)
    gcd_is_maximal a c g;
    (* coprime(a, c) → deg(gcd(a, c)) = 0, so deg(g) ≤ 0 *)
    coprime_reveal a c;
    divides_degree_le g (poly_gcd a c)
#pop-options

(* coprime(a, b) → coprime(a, b^n) for all n ≥ 1
   Base: n=1, bridge via gcd_congruence (poly_power b 1 ≈ b).
   Step: coprime(a, b) ∧ coprime(a, b^(n-1)) → coprime(a, b · b^(n-1)) = coprime(a, b^n). *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec coprime_power_right (#t:Type) {| f: field t |}
  (a b: polynomial t) (n: pos)
  : Lemma (requires coprime a b /\ deg a >= 0)
          (ensures  coprime a (poly_power b n))
          (decreases n)
  = if n = 1 then begin
      (* poly_power b 1 == poly_mul b poly_one ≈ b via poly_mul_one *)
      coprime_reveal a (poly_power b n);
      coprime_reveal a b;
      poly_mul_one b;
      (* poly_eq (poly_power b 1) b — direct from poly_mul_one *)
      poly_eq_reflexivity a;
      (* gcd_congruence: poly_eq a a ∧ poly_eq (poly_power b 1) b
         → poly_eq (gcd a (poly_power b 1)) (gcd a b) *)
      gcd_congruence a a (poly_power b 1) b;
      degree_well_defined (poly_gcd a (poly_power b 1)) (poly_gcd a b)
    end
    else begin
      coprime_power_right a b (n - 1);
      coprime_mul_right a b (poly_power b (n - 1))
    end
#pop-options

(* Full version: coprime(a, b) → coprime(a^m, b^n).
   Chain: coprime(a,b) → coprime(b,a) → coprime(b, a^m) → coprime(a^m, b) → coprime(a^m, b^n). *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let coprime_powers (#t:Type) {| f: field t |}
  (a b: polynomial t) (m n: pos)
  : Lemma (requires coprime a b /\ deg a >= 0 /\ deg b >= 0)
          (ensures  coprime (poly_power a m) (poly_power b n))
  = (* Step 1: coprime(a, b) → coprime(b, a) *)
    coprime_symmetric a b;
    (* Step 2: coprime(b, a) → coprime(b, a^m) *)
    coprime_power_right b a m;
    (* Step 3: coprime(b, a^m) → coprime(a^m, b) *)
    poly_power_has_degree a m;
    coprime_symmetric b (poly_power a m);
    (* Step 4: coprime(a^m, b) → coprime(a^m, b^n) *)
    coprime_power_right (poly_power a m) b n
#pop-options

(* coprime(d₁, d₂) ∧ d₁|x ∧ d₂|x → (d₁·d₂)|x
   Proof: d₂|x gives x ≈ d₂·s. d₁|(d₂·s) and coprime(d₁,d₂) →
   d₁|s by Euclid. s ≈ d₁·t. x ≈ d₂·d₁·t ≈ (d₁·d₂)·t. *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let coprime_divides_product (#t:Type) {| f: field t |}
  (d1 d2 x: polynomial t)
  : Lemma (requires coprime d1 d2 /\ divides d1 x /\ divides d2 x /\
                    deg d1 >= 0)
          (ensures  divides (d1 * d2) x)
  =
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* d2 | x means ∃ s. poly_eq x (poly_mul d2 s) *)
    eliminate exists (s: polynomial t). (x = (d2 * s))
    returns divides (d1 * d2) x
    with _.
    begin
      (* d1 | x ≈ d2·s, so d1 | d2·s *)
      divides_congruence_right d1 x (d2 * s);
      (* For euclid_lemma: need d1 | s·d2. Comm: d2·s ≈ s·d2 *)
      mul_commutativity d2 s;
      divides_congruence_right d1 (d2 * s) (s * d2);
      (* euclid_lemma d1 d2 s: coprime(d1, d2) ∧ d1|(s·d2) → d1|s *)
      euclid_lemma d1 d2 s;
      (* d1 | s means ∃ t. poly_eq s (poly_mul d1 t) *)
      eliminate exists (u: polynomial t). (s = (d1 * u))
      returns divides (d1 * d2) x
      with _.
      begin
        (* x ≈ d2·s ≈ d2·(d1·u) ≈ (d2·d1)·u ≈ (d1·d2)·u *)
        poly_mul_right_congruence d2 s (d1 * u);
        mul_associativity d2 d1 u;
        poly_eq_transitivity (d2 * s) (d2 * (d1 * u))
                             ((d2 * d1) * u);
        mul_commutativity d2 d1;
        poly_mul_left_congruence (d2 * d1) (d1 * d2) u;
        poly_eq_transitivity (d2 * s) ((d2 * d1) * u)
                             ((d1 * d2) * u);
        divides_intro (d1 * d2) x u
      end
    end
#pop-options

(* ================================================================ *)
(*  n-ary coprime product: pairwise coprime factors combine          *)
(* ================================================================ *)

(* Helper: coprime(a, b) ∧ coprime(a, c) → coprime(a, b·c) [already proved as coprime_mul_right]
   Iterated version: coprime(a, dᵢ) for all i → coprime(a, flat_product(ds)) *)
#push-options "--z3rlimit 50 --fuel 3 --ifuel 2"
private let rec coprime_flat_product (#t:Type) {| f: field t |}
  (a: polynomial t) (ds: list (polynomial t))
  : Lemma (requires deg a >= 0 /\
                    (forall (k:nat). k < L.length ds ==> coprime a (L.index ds k)))
          (ensures  coprime a (flat_product ds))
          (decreases ds)
  = match ds with
    | [] ->
        (* flat_product [] = poly_one. coprime(a, poly_one)? Yes: gcd(a, 1) has deg 0. *)
        coprime_reveal a (poly_one #t);
        gcd_has_degree a (poly_one #t);
        gcd_divides_right a (poly_one #t);
        (* gcd | poly_one, and gcd has Some? deg. poly_one has deg 0. *)
        divides_degree_le (poly_gcd a (poly_one #t)) (poly_one #t)
    | d :: rest ->
        (* flat_product (d::rest) = poly_mul d (flat_product rest) *)
        assert (coprime a d);
        (* index shifting: index (d::rest) (k+1) = index rest k *)
        assert (forall (k:nat). k < L.length rest ==>
                  L.index (d :: rest) (k ++ 1) == L.index rest k);
        assert (forall (k:nat). k < L.length rest ==>
                  coprime a (L.index rest k));
        coprime_flat_product a rest;
        coprime_mul_right a d (flat_product rest)
#pop-options

(* Main n-ary theorem: if dᵢ | x for all i, and the dᵢ are pairwise coprime,
   then flat_product(ds) | x. *)
#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
let rec pairwise_coprime_divides (#t:Type) {| f: field t |}
  (ds: list (polynomial t)) (x: polynomial t)
  : Lemma (requires (forall (k:nat). k < L.length ds ==> divides (L.index ds k) x) /\
                    (forall (k:nat). k < L.length ds ==> deg (L.index ds k) >= 0) /\
                    (forall (i j:nat). i < L.length ds /\ j < L.length ds /\ i <> j ==>
                      coprime (L.index ds i) (L.index ds j)))
          (ensures  divides (flat_product ds) x)
          (decreases ds)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    match ds with
    | [] ->
        one_divides_all x
    | [d] ->
        (* flat_product [d] = poly_mul d poly_one. divides d x. Bridge. *)
        assert (divides d x);
        poly_mul_one d;
        (* poly_eq d (poly_mul d (poly_one #t)). Use divides_congruence_left d (flat_product[d]) x *)
        divides_congruence_left  d (d * (poly_one #t)) x
    | d :: rest ->
        (* Shift quantifiers for rest *)
        assert (forall (k:nat). k < L.length rest ==>
                  L.index rest k == L.index (d :: rest) (k ++ 1));
        assert (forall (k:nat). k < L.length rest ==> divides (L.index rest k) x);
        assert (forall (k:nat). k < L.length rest ==> deg (L.index rest k) >= 0);
        assert (forall (i j:nat). i < L.length rest /\ j < L.length rest /\ i <> j ==>
                  coprime (L.index rest i) (L.index rest j));
        (* IH: flat_product(rest) | x *)
        pairwise_coprime_divides rest x;
        (* d | x *)
        assert (divides d x);
        assert (deg d >= 0);
        (* coprime(d, each element of rest): from pairwise on ds at i=0, j=k+1 *)
        assert (forall (k:nat). k < L.length rest ==>
                  coprime (L.index (d :: rest) 0) (L.index (d :: rest) (k ++ 1)));
        assert (forall (k:nat). k < L.length rest ==> coprime d (L.index rest k));
        coprime_flat_product d rest;
        coprime_divides_product d (flat_product rest) x
#pop-options

(* ================================================================ *)
(*  Key derivative lemma: q^(k-1) | D(q^k · r)                      *)
(*  This is the foundational building block for the GCD              *)
(*  characterization theorem gcd(p, p') = ∏ sᵢ^(i-1) when           *)
(*  p = ∏ sᵢ^i with pairwise coprime square-free factors.           *)
(* ================================================================ *)

(* Proof strategy:
   D(q^k · r) = D(q^k)·r + q^k·D(r)  [Leibniz rule]
   - q^(k-1) | D(q^k)    [deriv_power_divisibility]
     ⟹ q^(k-1) | D(q^k)·r  [divides_mul_right]
   - q^(k-1) | q^k       [trivially: q^k = q · q^(k-1)]
     ⟹ q^(k-1) | q^k·D(r)  [divides_mul_right]
   - Therefore q^(k-1) | (D(q^k)·r + q^k·D(r))  [divides_add]
   - Transfer to D(q^k · r) via congruence *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let power_factor_divides_deriv_product (#t:Type) {| f: field t |}
  (q r: polynomial t) (k: pos)
  : Lemma (ensures divides (poly_power q (k - 1))
                           (poly_deriv ((poly_power q k) * r)))
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let qk = poly_power q k in
    let qk1 = poly_power q (k - 1) in
    let dqk = poly_deriv qk in
    let dr = poly_deriv r in
    let sum1 = (dqk * r) in
    let sum2 = (qk * dr) in
    (* Product rule: D(q^k · r) ≈ D(q^k)·r + q^k·D(r) *)
    poly_deriv_mul qk r;
    (* Summand 1: q^(k-1) | D(q^k)·r *)
    deriv_power_divisibility q k;
    divides_mul_right  qk1 dqk r;
    (* Summand 2: q^(k-1) | q^k·D(r).
       First establish q^(k-1) | q^k: q^k = q · q^(k-1) definitionally,
       and poly_mul q qk1 = poly_mul qk1 q by commutativity *)
    mul_commutativity q qk1;
    divides_intro  qk1 qk q;
    divides_mul_right  qk1 qk dr;
    (* Combine: q^(k-1) | sum1 + sum2 *)
    divides_add  qk1 sum1 sum2;
    (* Transfer via congruence: D(q^k·r) ≈ sum1 + sum2 *)
    divides_congruence_right  qk1
      (sum1 + sum2) (poly_deriv (qk * r))
#pop-options

(* Consequence: q^(k-1) | gcd(q^k · r, D(q^k · r))
   Proof: q^(k-1) divides both the product and its derivative,
   hence divides their GCD by maximality. *)
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let power_factor_divides_gcd (#t:Type) {| f: field t |}
  (q r: polynomial t) (k: pos)
  : Lemma (ensures divides (poly_power q (k - 1))
                           (poly_gcd ((poly_power q k) * r)
                                           (poly_deriv ((poly_power q k) * r))))
  = 
    H.elim_equatable_laws (polynomial t) ();
    let p = ((poly_power q k) * r) in
    let dp = poly_deriv p in
    let qk1 = poly_power q (k - 1) in
    (* q^(k-1) | p: q^k = q·q^(k-1), so q^(k-1) | q^k, hence q^(k-1) | q^k·r = p *)
    mul_commutativity q qk1;
    divides_intro  qk1 (poly_power q k) q;
    divides_mul_right  qk1 (poly_power q k) r;
    (* q^(k-1) | D(p) *)
    power_factor_divides_deriv_product q r k;
    (* q^(k-1) divides both p and D(p), so it divides their gcd *)
    gcd_is_maximal p dp qk1
#pop-options

(* ================================================================ *)
(*  Bridge: if p ≈ q^k · r then q^(k-1) | gcd(p, D(p))            *)
(*                                                                  *)
(*  This lifts power_factor_divides_gcd to work with any p that    *)
(*  is poly_eq to a power-times-rest product.                      *)
(* ================================================================ *)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let power_factor_divides_gcd_of_eq (#t:Type) {| f: field t |}
  (p q r: polynomial t) (k: pos)
  : Lemma (requires (p = ((poly_power q k) * r)))
          (ensures  divides (poly_power q (k - 1))
                            (poly_gcd p (poly_deriv p)))
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let qkr = ((poly_power q k) * r) in
    (* gcd(q^k·r, D(q^k·r)) has q^(k-1) as a divisor *)
    power_factor_divides_gcd q r k;
    (* D(p) ≈ D(q^k·r) via congruence *)
    poly_deriv_congruence p qkr;
    (* gcd(p, D(p)) ≈ gcd(q^k·r, D(q^k·r)) via gcd_congruence *)
    gcd_congruence qkr p (poly_deriv qkr) (poly_deriv p);
    (* Transfer divisibility via congruence *)
    divides_congruence_right  (poly_power q (k - 1))
      (poly_gcd qkr (poly_deriv qkr))
      (poly_gcd p (poly_deriv p))
#pop-options

(* ================================================================ *)
(*  PP shift identity: PP(xs, s+1) ≈ flat_product(xs) · PP(xs, s)   *)
(*                                                                  *)
(*  Key algebraic identity for decomposing the powered product.     *)
(*  PP(factors, 1) ≈ flat_product(factors) · PP(tail(factors), 1)   *)
(*  follows as a corollary with s=1 and the head term being x^1.   *)
(* ================================================================ *)

(* Helper: (a·b)·(c·d) ≈ (a·c)·(b·d) in polynomial ring *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
private let mul_four_rearrange (#t:Type) {| cr: commutative_ring t |}
  (a b c d: polynomial t)
  : Lemma (ensures ((a * b) * (c * d)) =
                           ((a * c) * (b * d)))
  = (* (a·b)·(c·d) ≈ a·(b·(c·d)) *)
    mul_associativity a b (c * d);
    (* b·(c·d) ≈ (b·c)·d *)
    mul_associativity b c d;
    poly_eq_symmetry ((b * c) * d) (b * (c * d));
    (* (b·c) ≈ (c·b) *)
    mul_commutativity b c;
    (* (b·c)·d ≈ (c·b)·d *)
    poly_mul_left_congruence (b * c) (c * b) d;
    (* (c·b)·d ≈ c·(b·d) *)
    mul_associativity c b d;
    (* chain: b·(c·d) ≈ (b·c)·d ≈ (c·b)·d ≈ c·(b·d) *)
    poly_eq_transitivity (b * (c * d))
                         ((b * c) * d)
                         ((c * b) * d);
    poly_eq_transitivity (b * (c * d))
                         ((c * b) * d)
                         (c * (b * d));
    (* lift: a·(b·(c·d)) ≈ a·(c·(b·d)) *)
    poly_mul_right_congruence a (b * (c * d))
                                (c * (b * d));
    (* a·(c·(b·d)) ≈ (a·c)·(b·d) *)
    mul_associativity a c (b * d);
    poly_eq_symmetry ((a * c) * (b * d))
                     (a * (c * (b * d)));
    (* full chain: (a·b)·(c·d) ≈ a·(b·(c·d)) ≈ a·(c·(b·d)) ≈ (a·c)·(b·d) *)
    poly_eq_transitivity ((a * b) * (c * d))
                         (a * (b * (c * d)))
                         (a * (c * (b * d)));
    poly_eq_transitivity ((a * b) * (c * d))
                         (a * (c * (b * d)))
                         ((a * c) * (b * d))
#pop-options

(* Main PP shift: powered_product_aux xs (s+1) ≈ flat_product(xs) · powered_product_aux xs s *)
#push-options "--z3rlimit 60 --fuel 4 --ifuel 2"
let rec pp_shift (#t:Type) {| f: field t |}
  (xs: list (polynomial t)) (s: pos)
  : Lemma (ensures (powered_product_aux xs (s ++ 1)) =
                           ((flat_product xs) * (powered_product_aux xs s)))
          (decreases xs)
  =
    match xs with
    | [] ->
        (* PP([], s+1) = poly_one. flat_product([]) · PP([], s) = poly_one · poly_one ≈ poly_one *)
        poly_mul_one (poly_one #t);
        poly_eq_symmetry ((poly_one #t) * (poly_one #t)) (poly_one #t)
    | x :: rest ->
        let s1 = (s ++ 1) in
        let s2 = (s ++ 2) in
        (* IH: PP(rest, s+2) ≈ flat_product(rest) · PP(rest, s+1) *)
        pp_shift rest s1;
        (* LHS = poly_mul (poly_power x (s+1)) (PP(rest, s+2))
           RHS = poly_mul (poly_mul x (flat_product rest)) (poly_mul (poly_power x s) (PP(rest, s+1)))
           
           Substitute IH into LHS:
           LHS ≈ poly_mul (poly_power x (s+1)) (poly_mul (flat_product rest) (PP(rest, s+1)))
           
           poly_power x (s+1) == poly_mul x (poly_power x s)  [definitional]
           
           So LHS ≈ poly_mul (poly_mul x (poly_power x s)) (poly_mul (flat_product rest) (PP(rest, s+1)))
           RHS     = poly_mul (poly_mul x (flat_product rest)) (poly_mul (poly_power x s) (PP(rest, s+1)))
           
           Use mul_four_rearrange: (a·b)·(c·d) ≈ (a·c)·(b·d)
           with a=x, b=poly_power x s, c=flat_product rest, d=PP(rest, s+1)
        *)
        let pp_rest_s1 = powered_product_aux rest s1 in
        let pp_rest_s2 = powered_product_aux rest s2 in
        let fp_rest = flat_product rest in
        let xps = poly_power x s in
        (* Step 1: substitute IH into LHS *)
        poly_mul_right_congruence (poly_power x s1) pp_rest_s2
                                  (fp_rest * pp_rest_s1);
        (* Now: PP(x::rest, s+1) ≈ poly_mul (poly_power x s1) (poly_mul fp_rest pp_rest_s1) *)
        (* Step 2: poly_power x (s+1) == poly_mul x (poly_power x s) [definitional] *)
        poly_eq_reflexivity (x * xps);
        poly_mul_left_congruence (poly_power x s1) (x * xps)
                                 (fp_rest * pp_rest_s1);
        (* Now have: poly_mul (poly_power x s1) (poly_mul fp_rest pp_rest_s1)
                   ≈ poly_mul (poly_mul x xps) (poly_mul fp_rest pp_rest_s1) *)
        (* Step 3: rearrange (x · xps) · (fp_rest · pp_rest_s1) ≈ (x · fp_rest) · (xps · pp_rest_s1) *)
        mul_four_rearrange x xps fp_rest pp_rest_s1;
        (* Chain: PP(x::rest, s+1)
                ≈ poly_mul (poly_power x s1) pp_rest_s2         [def of PP]
                ≈ poly_mul (poly_power x s1) (poly_mul fp_rest pp_rest_s1) [IH]
                ≈ poly_mul (poly_mul x xps) (poly_mul fp_rest pp_rest_s1) [def of power]
                ≈ poly_mul (poly_mul x fp_rest) (poly_mul xps pp_rest_s1) [rearrange]
                = poly_mul (flat_product (x::rest)) (PP(x::rest, s))      [def] *)
        let t0 = powered_product_aux (x :: rest) s1 in
        let t1 = ((poly_power x s1) * pp_rest_s2) in
        let t2 = ((poly_power x s1) * (fp_rest * pp_rest_s1)) in
        let t3 = ((x * xps) * (fp_rest * pp_rest_s1)) in
        let t4 = ((x * fp_rest) * (xps * pp_rest_s1)) in
        poly_eq_reflexivity t0;
        poly_eq_transitivity t0 t2 t3;
        poly_eq_transitivity t0 t3 t4
#pop-options

(* Corollary: PP(x :: rest, 1) ≈ flat_product(x :: rest) · PP(rest, 1)
   i.e., PP(factors, 1) ≈ flat_product(factors) · PP(tail, 1) *)
#push-options "--z3rlimit 60 --fuel 4 --ifuel 2"
let pp_split_head (#t:Type) {| f: field t |}
  (x: polynomial t) (rest: list (polynomial t))
  : Lemma (ensures (powered_product_aux (x :: rest) 1) =
                           ((flat_product (x :: rest))
                                     * (powered_product_aux rest 1)))
  =
    let pp_rest_1 = powered_product_aux rest 1 in
    let pp_rest_2 = powered_product_aux rest 2 in
    let fp_rest = flat_product rest in
    (* Step 1: PP(rest, 2) ≈ flat_product(rest) · PP(rest, 1) via pp_shift *)
    pp_shift rest 1;
    (* Step 2: poly_power x 1 = poly_mul x poly_one. Bridge: poly_mul x poly_one ≈ x *)
    poly_mul_one x;
    (* Step 3: PP(x::rest, 1) = poly_mul (poly_power x 1) pp_rest_2
                               = poly_mul (poly_mul x poly_one) pp_rest_2
       Substitute poly_mul_one: ≈ poly_mul x pp_rest_2 *)
    poly_mul_left_congruence (x * (poly_one #t)) x pp_rest_2;
    (* Step 4: substitute pp_shift: poly_mul x pp_rest_2 ≈ poly_mul x (poly_mul fp_rest pp_rest_1) *)
    poly_mul_right_congruence x pp_rest_2 (fp_rest * pp_rest_1);
    (* Step 5: associativity: poly_mul x (poly_mul fp_rest pp_rest_1) ≈ poly_mul (poly_mul x fp_rest) pp_rest_1 *)
    mul_associativity x fp_rest pp_rest_1;
    poly_eq_symmetry ((x * fp_rest) * pp_rest_1)
                     (x * (fp_rest * pp_rest_1));
    (* Chain everything *)
    let t0 = powered_product_aux (x :: rest) 1 in
    let t1 = ((x * (poly_one #t)) * pp_rest_2) in
    let t2 = (x * pp_rest_2) in
    let t3 = (x * (fp_rest * pp_rest_1)) in
    let t4 = ((x * fp_rest) * pp_rest_1) in
    poly_eq_reflexivity t0;
    poly_eq_transitivity t0 t2 t3;
    poly_eq_transitivity t0 t3 t4
#pop-options

(* ================================================================ *)
(*  Degree pinch: divides + same degree → witness is degree 0       *)
(*                                                                  *)
(*  If d | p and deg(d) = deg(p), then the witness c with           *)
(*  p ≈ d · c has deg(c) = 0 (c is a constant/scalar).             *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let divides_same_degree (#t:Type) {| f: field t |}
  (d p: polynomial t)
  : Lemma (requires divides d p /\
                    deg d >= 0 /\ deg p >= 0 /\
                    deg d == deg p)
          (ensures  (
                     exists (c: polynomial t).
                       (p = (d * c)) /\
                       deg c == 0))
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let aux (c: polynomial t)
      : Lemma (requires (p = (d * c)))
              (ensures  deg c == 0)
      = if deg c < 0 then begin
            (* c ≈ zero → d·c ≈ zero → p ≈ zero. But deg p >= 0. Contradiction. *)
            assert (c == (poly_zero #t));
            H.x_mul_zero d;
            degree_well_defined p (poly_zero #t)
        end else begin
            (* deg(d·c) = deg(d) + deg(c). poly_eq p (d·c) → deg(p) = deg(d) + deg(c). *)
            degree_mul d c;
            degree_well_defined p (d * c)
        end
            (* Now: deg p == deg d + dc.
               But deg p == deg d.
               Hence dc = 0. *)
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

(* ================================================================ *)
(*  Powered product has degree: PP(xs, s) has Some? degree when     *)
(*  all factors in xs have Some? degree.                            *)
(* ================================================================ *)

#push-options "--z3rlimit 40 --fuel 4 --ifuel 2"
let rec pp_has_degree (#t:Type) {| f: field t |}
  (xs: list (polynomial t)) (s: pos)
  : Lemma (requires (forall (k:nat). k < L.length xs ==> deg (L.index xs k) >= 0))
          (ensures  deg (powered_product_aux xs s) >= 0)
          (decreases xs)
  = match xs with
    | [] -> ()  (* poly_one has degree Some 0 *)
    | x :: rest ->
        assert (deg x >= 0);
        assert (forall (k:nat). k < L.length rest ==>
                  L.index rest k == L.index (x :: rest) (k ++ 1));
        assert (forall (k:nat). k < L.length rest ==> deg (L.index rest k) >= 0);
        poly_power_degree_exact x s;
        pp_has_degree rest (s ++ 1);
        degree_mul (poly_power x s) (powered_product_aux rest (s ++ 1))
#pop-options

(* ================================================================ *)
(*  poly_div preserves Some? degree                                *)
(* ================================================================ *)

let poly_div_has_degree (#t:Type) {| f: field t |}
  (p d: polynomial t)
  : Lemma (requires deg d >= 0 /\ deg p >= 0 /\ divides d p)
          (ensures  deg (poly_div p d) >= 0)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    poly_div_correct p d;
    let q = poly_div p d in
    if deg q >= 0 then () else begin
        degree_none_poly_eq_zero q;
        poly_mul_congruence d q d (poly_zero #t);
        H.x_mul_zero d;
        degree_well_defined p (poly_zero #t)
    end

(* ================================================================ *)
(*  poly_div degree formula                                        *)
(* ================================================================ *)

let poly_div_degree (#t:Type) {| f: field t |}
  (p d: polynomial t)
  : Lemma (requires deg d >= 0 /\ deg p >= 0 /\ divides d p)
          (ensures  deg (poly_div p d) >= 0 /\
                    deg (poly_div p d) ==
                    deg p - deg d)
  = poly_div_has_degree p d;
    poly_div_correct p d;
    let q = poly_div p d in
    degree_mul d q;
    poly_eq_symmetry (d * q) p;
    degree_well_defined p (d * q)

(* ================================================================ *)
(*  Irreducible ⟹ coprime or divides                               *)
(*                                                                  *)
(*  For an irreducible q: for any r with Some? degree, either       *)
(*  coprime(q, r) or q | r.                                         *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 4 --ifuel 3"
let irreducible_coprime_or_divides (#t:Type) {| f: field t |}
  (q r: polynomial t)
  : Lemma (requires poly_irreducible q /\ deg r >= 0)
          (ensures  coprime q r \/ divides q r)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let g = poly_gcd q r in
    gcd_has_degree q r;
    gcd_divides_left q r;
    gcd_divides_right q r;
    coprime_reveal q r;
    if deg g = 0 then ()
    else begin
      (* deg(g) ≥ 1. Show q | r via Euclid's lemma. *)
      let combined (h d: polynomial t)
        : Lemma (requires (q = (g * h)) /\ (r = (g * d)))
                (ensures  divides q r)
        = (* From irreducibility: deg(h) = 0 or None *)
          assert ((q = (g * h)) == true);
          assert (deg g == 0 \/ deg g < 0 \/
                  deg h == 0 \/ deg h < 0);
          assert (deg h == 0 \/ deg h < 0);
          (* Eliminate None: h ≈ 0 → q ≈ 0. Contradiction. *)
          (if deg h < 0 then (
            degree_none_poly_eq_zero h;
            poly_mul_congruence g h g (poly_zero #t);
            H.x_mul_zero g;
            degree_well_defined q (poly_zero #t)
          ) else ());
          assert (deg h == 0);
          (* coprime(q, h): gcd(q,h) | h with deg(h) = 0,
             so deg(gcd(q,h)) ≤ 0 = Some 0. *)
          gcd_has_degree q h;
          gcd_divides_right q h;
          divides_degree_le (poly_gcd q h) h;
          coprime_reveal q h;
          assert (coprime q h);
          (* Show q | (r·h) via ring chain:
             r·h ≈ (g·d)·h ≈ g·(d·h) ≈ g·(h·d) ≈ (g·h)·d ≈ q·d *)
          poly_mul_left_congruence r (g * d) h;
          mul_associativity g d h;
          poly_eq_symmetry ((g * d) * h)
                           (g * (d * h));
          mul_commutativity d h;
          poly_mul_right_congruence g (d * h) (h * d);
          mul_associativity g h d;
          poly_mul_left_congruence (g * h) q d;
          let rh = (r * h) in
          let gdh = ((g * d) * h) in
          let g_dh = (g * (d * h)) in
          let g_hd = (g * (h * d)) in
          let ghd = ((g * h) * d) in
          let qd = (q * d) in
          divides_intro  q rh d;
          (* euclid_lemma: coprime(q, h) ∧ q | (r·h) → q | r *)
          euclid_lemma q h r
      in
      Classical.forall_intro_2 (Classical.move_requires_2 combined)
    end
#pop-options

(* ================================================================ *)
(*  Factor out maximal power of an irreducible from a polynomial    *)
(*                                                                  *)
(*  For irreducible q dividing p, there exist e ≥ 1 and r such     *)
(*  that p ≈ q^e · r and coprime(q, r).                            *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 4 --ifuel 3"
let rec factor_out_irreducible (#t:Type) {| f: field t |}
  (q p: polynomial t)
  : Lemma (requires poly_irreducible q /\ divides q p /\ deg p >= 0)
          (ensures  exists (e: pos) (r: polynomial t).
            (p = ((poly_power q e) * r)) /\
            coprime q r /\
            deg r >= 0)
          (decreases (if deg p >= 0 then deg p else 0))
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    poly_div_correct p q;
    poly_div_has_degree p q;
    poly_div_degree p q;
    let p1 = poly_div p q in
    assert (deg p1 < deg p);
    irreducible_coprime_or_divides q p1;
    if coprime q p1 then begin
      (* Base: e = 1, r = p1. poly_power q 1 = q. *)
      poly_mul_one q;
      assert ((poly_power q 1) = q);
      poly_mul_left_congruence q (poly_power q 1) p1;
      poly_eq_transitivity p (q * p1) ((poly_power q 1) * p1)
    end else begin
      (* Inductive: q | p1, recurse *)
      assert (divides q p1);
      factor_out_irreducible q p1;
      let chain (e': pos) (r': polynomial t)
        : Lemma (requires (p1 = ((poly_power q e') * r')) /\
                          coprime q r' /\ deg r' >= 0)
                (ensures  exists (e: pos) (r: polynomial t).
                  (p = ((poly_power q e) * r)) /\
                  coprime q r /\ deg r >= 0)
        = let e = (e' ++ 1) in
          (* q · (q^e' · r') ≈ (q · q^e') · r' by associativity *)
          poly_mul_right_congruence q p1 ((poly_power q e') * r');
          mul_associativity q (poly_power q e') r';
          poly_eq_symmetry ((q * (poly_power q e')) * r')
                           (q * ((poly_power q e') * r'));
          poly_eq_transitivity (q * p1)
                               (q * ((poly_power q e') * r'))
                               ((q * (poly_power q e')) * r');
          (* poly_power q e == poly_mul q (poly_power q e') *)
          assert (poly_power q e == (q * (poly_power q e')));
          poly_mul_left_congruence (q * (poly_power q e'))
                                  (poly_power q e) r';
          poly_eq_transitivity ((q * (poly_power q e')) * r')
                               ((poly_power q e) * r')
                               ((poly_power q e) * r');
          poly_eq_transitivity (q * p1)
                               ((q * (poly_power q e')) * r')
                               ((poly_power q e) * r');
          poly_eq_transitivity p (q * p1) ((poly_power q e) * r')
      in
      Classical.forall_intro_2 (Classical.move_requires_2 chain)
    end
#pop-options

(* ================================================================ *)
(*  Composition: irreducible q | p → q^(e-1) | gcd(p, D(p))        *)
(* ================================================================ *)

let irred_factor_gcd_valuation (#t:Type) {| f: field t |}
  (q p: polynomial t)
  : Lemma (requires poly_irreducible q /\ divides q p /\ deg p >= 0)
          (ensures  exists (e: pos).
            divides (poly_power q (e - 1))
                    (poly_gcd p (poly_deriv p)))
  = factor_out_irreducible q p;
    let aux (e: pos) (r: polynomial t)
      : Lemma (requires (p = ((poly_power q e) * r)) /\
                        coprime q r /\ deg r >= 0)
              (ensures  exists (e: pos).
                divides (poly_power q (e - 1))
                        (poly_gcd p (poly_deriv p)))
      = power_factor_divides_gcd_of_eq p q r e
    in
    Classical.forall_intro_2 (Classical.move_requires_2 aux)

(* ================================================================ *)
(*  Irreducible factors from coprime remainder are pairwise coprime *)
(* ================================================================ *)

let irred_factor_of_remainder_coprime (#t:Type) {| f: field t |}
  (q r q2: polynomial t)
  : Lemma (requires poly_irreducible q /\ coprime q r /\
                    poly_irreducible q2 /\ divides q2 r /\
                    deg r >= 0)
          (ensures  coprime q q2)
  = coprime_symmetric q r;
    coprime_divisor r q q2;
    coprime_symmetric q2 q
