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
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    (* poly_power p n = poly_mul p (poly_power p (n-1)) definitionally for n ≥ 1.
       Witness: poly_power p (n-1). *)
    poly_eq_reflexivity (poly_mul p (poly_power p (n - 1)));
    divides_intro #(polynomial t) #cr_p p (poly_mul p (poly_power p (n - 1))) (poly_power p (n - 1))

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
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    poly_mul_one x;
    (* poly_mul_one gives: poly_eq (poly_mul poly_one x) x *)
    poly_eq_symmetry (poly_mul (poly_one #t) x) x;
    (* poly_eq x (poly_mul poly_one x) *)
    divides_intro #(polynomial t) #cr_p (poly_one #t) x x

(* ================================================================ *)
(*  Helper: d|a ⟹ (c·d) | (c·a)                                  *)
(* ================================================================ *)

private let divides_mul_both_sides (#t:Type) {| f: field t |}
  (d a c: polynomial t)
  : Lemma (requires divides d a)
          (ensures  divides (poly_mul c d) (poly_mul c a))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    eliminate exists (s: polynomial t). poly_eq a (poly_mul d s)
    returns divides (poly_mul c d) (poly_mul c a)
    with _.
    begin
      (* c·a ≈ c·(d·s) by congruence *)
      poly_mul_right_congruence c a (poly_mul d s);
      (* c·(d·s) ≈ (c·d)·s by assoc (reversed) *)
      poly_mul_associativity c d s;
      poly_eq_symmetry (poly_mul (poly_mul c d) s) (poly_mul c (poly_mul d s));
      poly_eq_transitivity (poly_mul c a)
        (poly_mul c (poly_mul d s))
        (poly_mul (poly_mul c d) s);
      divides_intro #(polynomial t) #cr_p (poly_mul c d) (poly_mul c a) s
    end

(* ================================================================ *)
(*  Derivative of power: q^(k-1) | D(q^k) for k ≥ 1               *)
(* ================================================================ *)

let rec deriv_power_divisibility (#t:Type) {| f: field t |}
  (q: polynomial t) (k: pos)
  : Lemma (ensures divides (poly_power q (k - 1)) (poly_deriv (poly_power q k)))
          (decreases k)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if k = 1 then
      (* poly_power q 0 = poly_one.
         Need: divides poly_one (D(q^1)). poly_one divides anything. *)
      one_divides_all #t #f (poly_deriv (poly_power q k))
    else begin
      (* k ≥ 2. Definitionally: poly_power q k == poly_mul q (poly_power q (k-1)).
         Product rule: D(q · q^(k-1)) ≈ D(q)·q^(k-1) + q·D(q^(k-1)).
         IH: q^(k-2) | D(q^(k-1)).
         Goal: q^(k-1) | D(q^k). *)
      let qk1 = poly_power q (k - 1) in
      let qk2 = poly_power q (k - 2) in
      let dq  = poly_deriv q in
      let dqk1 = poly_deriv qk1 in
      let sum1 = poly_mul dq qk1 in
      let sum2 = poly_mul q dqk1 in

      (* Product rule on q · q^(k-1) *)
      poly_deriv_mul q qk1;
      (* poly_eq (poly_deriv (poly_mul q qk1)) (poly_add sum1 sum2) *)

      (* --- Summand 1: qk1 | dq·qk1 --- *)
      poly_mul_commutativity dq qk1;
      (* poly_eq (poly_mul dq qk1) (poly_mul qk1 dq) *)
      poly_eq_symmetry (poly_mul dq qk1) (poly_mul qk1 dq);
      (* poly_eq (poly_mul qk1 dq) sum1 *)
      divides_intro #(polynomial t) #cr_p qk1 sum1 dq;

      (* --- Summand 2: qk1 | q·D(q^(k-1)) --- *)
      (* IH: q^(k-2) | D(q^(k-1)) *)
      deriv_power_divisibility q (k - 1);
      (* divides_mul_both_sides: q^(k-2)|D(q^(k-1)) ⟹ (q·q^(k-2))|(q·D(q^(k-1))) *)
      divides_mul_both_sides #t #f qk2 dqk1 q;
      (* divides (poly_mul q qk2) (poly_mul q dqk1)
         = divides (poly_mul q (poly_power q (k-2))) sum2
         And poly_mul q (poly_power q (k-2)) == poly_power q (k-1) == qk1 [definitional] *)

      (* --- Combine: qk1 | sum1 + sum2 --- *)
      divides_add #(polynomial t) #cr_p qk1 sum1 sum2;

      (* --- Transfer via poly_eq to poly_deriv (poly_power q k) --- *)
      (* poly_power q k == poly_mul q qk1 definitionally, so
         poly_deriv (poly_power q k) == poly_deriv (poly_mul q qk1)
         ≈ poly_add sum1 sum2 [product rule above] *)
      poly_eq_symmetry (poly_deriv (poly_mul q qk1)) (poly_add sum1 sum2);
      divides_congruence_right #(polynomial t) #cr_p qk1
        (poly_add sum1 sum2)
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
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let qk   = poly_power q k in
    let qk1  = poly_power q (k - 1) in
    (* From q^k | p: ∃r. p ≈ q^k · r *)
    eliminate exists (r: polynomial t). poly_eq p (poly_mul qk r)
    returns divides qk1 (poly_deriv p)
    with _.
    begin
      (* D(p) ≈ D(q^k · r) by congruence *)
      poly_deriv_congruence p (poly_mul qk r);
      (* D(q^k · r) ≈ D(q^k)·r + q^k·D(r) by product rule *)
      poly_deriv_mul qk r;
      let dqk = poly_deriv qk in
      let dr  = poly_deriv r in
      let sum1 = poly_mul dqk r in
      let sum2 = poly_mul qk dr in
      poly_eq_transitivity (poly_deriv p)
        (poly_deriv (poly_mul qk r))
        (poly_add sum1 sum2);

      (* --- Term 1: qk1 | D(q^k)·r --- *)
      deriv_power_divisibility #t #f q k;
      (* qk1 | D(q^k) *)
      divides_mul_right #(polynomial t) #cr_p qk1 dqk r;
      (* qk1 | dqk · r = sum1 *)

      (* --- Term 2: qk1 | q^k · D(r) --- *)
      (* qk1 | qk because q^k = q · q^(k-1) ≈ q^(k-1) · q *)
      poly_mul_commutativity q qk1;
      (* poly_eq (poly_mul q qk1) (poly_mul qk1 q), i.e. poly_eq qk (poly_mul qk1 q) *)
      divides_intro #(polynomial t) #cr_p qk1 qk q;
      (* qk1 | qk *)
      divides_mul_right #(polynomial t) #cr_p qk1 qk dr;
      (* qk1 | qk · dr = sum2 *)

      (* --- Combine --- *)
      divides_add #(polynomial t) #cr_p qk1 sum1 sum2;
      (* qk1 | poly_add sum1 sum2 *)
      divides_congruence_right #(polynomial t) #cr_p qk1
        (poly_add sum1 sum2)
        (poly_deriv p)
    end

(* ================================================================ *)
(*  Repeated factor ⟹ divides GCD                                  *)
(*  If q^k | p (k ≥ 2) then q^(k-1) | gcd(p, D(p))               *)
(* ================================================================ *)

let repeated_factor_divides_gcd (#t:Type) {| f: field t |}
  (q p: polynomial t) (k: nat{k >= 2})
  : Lemma (requires divides (poly_power q k) p /\ Some? (poly_deg p))
          (ensures  divides (poly_power q (k - 1))
                            (poly_gcd #t #f p (poly_deriv p)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    let qk1 = poly_power q (k - 1) in
    let dp  = poly_deriv p in
    let g   = poly_gcd #t #f p dp in
    (* qk1 | p: by transitivity, qk1 | q^k | p *)
    (* q^k = q · q^(k-1) ≈ q^(k-1) · q *)
    poly_mul_commutativity q qk1;
    divides_intro #(polynomial t) #cr_p qk1 (poly_power q k) q;
    divides_trans #(polynomial t) #cr_p qk1 (poly_power q k) p;
    (* qk1 | p *)
    (* qk1 | D(p) *)
    repeated_factor_divides_deriv #t #f q p k;
    (* qk1 | gcd(p, D(p)) by maximality:
       gcd_is_maximal says: if d|p and d|q then d | gcd(p,q) *)
    gcd_is_maximal #t #f p dp qk1

(* ================================================================ *)
(*  Degree of power: deg(q^k) ≥ deg(q) for k ≥ 1                  *)
(* ================================================================ *)

let rec poly_power_has_degree (#t:Type) {| f: field t |}
  (q: polynomial t) (k: pos)
  : Lemma (requires Some? (poly_deg q))
          (ensures  Some? (poly_deg (poly_power q k)) /\
                    Some?.v (poly_deg (poly_power q k)) >= Some?.v (poly_deg q))
          (decreases k)
  = if k = 1 then
      degree_mul #t #(id_of_f t) q (poly_one #t)
    else begin
      poly_power_has_degree #t #f q (k - 1);
      degree_mul #t #(id_of_f t) q (poly_power q (k - 1))
    end

(* ================================================================ *)
(*  Divisibility degree bound: d|g and deg d ≥ 1 ⟹ deg g ≥ 1      *)
(* ================================================================ *)

private let divides_degree_lower_bound (#t:Type) {| f: field t |}
  (d g: polynomial t)
  : Lemma (requires divides d g /\ Some? (poly_deg d) /\ Some?.v (poly_deg d) >= 1
                    /\ Some? (poly_deg g))
          (ensures  Some?.v (poly_deg g) >= 1)
  = let aux (c: polynomial t)
      : Lemma (requires poly_eq g (poly_mul d c))
              (ensures  Some?.v (poly_deg g) >= 1)
      = degree_well_defined g (poly_mul d c);
        (* poly_deg (poly_mul d c) == poly_deg g == Some _ *)
        if Nil? c then begin
          (* c = [] = poly_zero. poly_mul d poly_zero ≈ poly_zero by x_mul_zero *)
          H.x_mul_zero #(polynomial t) d;
          degree_well_defined (poly_mul d c) (poly_zero #(polynomial t))
          (* poly_deg (poly_mul d c) == None, contradicts Some? above *)
        end else begin
          (* Both d and c are nonempty: use degree_mul *)
          degree_mul #t #(id_of_f t) d c
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
                    Some? (poly_deg q) /\ Some?.v (poly_deg q) >= 1 /\
                    Some? (poly_deg p))
          (ensures  square_free #t #f p = false)
  = let dp = poly_deriv p in
    let g  = poly_gcd #t #f p dp in
    let qk1 = poly_power q (k - 1) in
    repeated_factor_divides_gcd #t #f q p k;
    poly_power_has_degree #t #f q (k - 1);
    gcd_has_degree #t #f p dp;
    coprime_reveal #t #f p dp;
    (* Now: divides qk1 g, Some? (poly_deg qk1) with val >= 1, Some? (poly_deg g) *)
    (* Inline the degree bound argument via existential elimination *)
    let aux (c: polynomial t)
      : Lemma (requires poly_eq g (poly_mul qk1 c))
              (ensures  square_free #t #f p = false)
      = degree_well_defined g (poly_mul qk1 c);
        if Nil? c then begin
          H.x_mul_zero #(polynomial t) qk1;
          degree_well_defined (poly_mul qk1 c) (poly_zero #(polynomial t))
        end else
          degree_mul #t #(id_of_f t) qk1 c
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
  : Lemma (requires Some? (poly_deg p) /\ Some? (poly_deg g) /\
                    poly_eq (poly_mul g (poly_div #t #f p g)) p)
          (ensures  Some? (poly_deg (poly_div #t #f p g)))
  = let b = poly_div #t #f p g in
    match poly_deg b with
    | Some _ -> ()
    | None ->
        (* b = poly_zero, so poly_mul g b ≈ poly_zero *)
        assert (b == (poly_zero #t));
        H.x_mul_zero #(polynomial t) g;
        (* poly_eq (poly_mul g poly_zero) poly_zero *)
        degree_well_defined (poly_mul g b) (poly_zero #t);
        (* poly_deg (poly_mul g b) == None *)
        degree_well_defined p (poly_mul g b)
        (* poly_deg p == poly_deg (poly_mul g b) == None, contradicts Some? *)

#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
let coprime_quotients (#t:Type) {| f: field t |}
  (p q: polynomial t)
  : Lemma (requires Some? (poly_deg p))
          (ensures  (let g = poly_gcd #t #f p q in
                     let b = poly_div #t #f p g in
                     let c = poly_div #t #f q g in
                     coprime #t #f b c))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let g = poly_gcd #t #f p q in
    let b = poly_div #t #f p g in
    let c = poly_div #t #f q g in
    coprime_reveal #t #f b c;
    gcd_has_degree #t #f p q;                  // Some? (poly_deg g)
    gcd_divides_left #t #f p q;                // g | p
    gcd_divides_right #t #f p q;               // g | q
    poly_div_correct #t #f p g;               // poly_eq (poly_mul g b) p
    poly_div_correct #t #f q g;               // poly_eq (poly_mul g c) q
    poly_div_nonzero #t #f p g;               // Some? (poly_deg b)
    let d = poly_gcd #t #f b c in
    gcd_has_degree #t #f b c;                  // Some? (poly_deg d)
    gcd_divides_left #t #f b c;                // d | b
    gcd_divides_right #t #f b c;               // d | c
    (* g*d | g*b via divides_mul_both_sides *)
    divides_mul_both_sides d b g;              // (g*d) | (g*b)
    (* g*b ≈ p, so g*d | p *)
    divides_congruence_right #(polynomial t) #cr_p
      (poly_mul g d) (poly_mul g b) p;
    (* g*d | g*c similarly *)
    divides_mul_both_sides d c g;              // (g*d) | (g*c)
    divides_congruence_right #(polynomial t) #cr_p
      (poly_mul g d) (poly_mul g c) q;
    (* By maximality of gcd: g*d | gcd(p,q) = g *)
    gcd_is_maximal #t #f p q (poly_mul g d);
    (* Now: divides (poly_mul g d) g with Some? (poly_deg g).
       Extract witness and use degree_mul to show deg d = 0. *)
    let aux (e: polynomial t)
      : Lemma (requires poly_eq g (poly_mul (poly_mul g d) e))
              (ensures  poly_deg d = Some 0)
      = (* g ≈ (g*d)*e = g*(d*e) by associativity *)
        poly_mul_associativity g d e;
        (* poly_eq (poly_mul (poly_mul g d) e) (poly_mul g (poly_mul d e)) *)
        degree_well_defined g (poly_mul (poly_mul g d) e);
        degree_well_defined (poly_mul (poly_mul g d) e) (poly_mul g (poly_mul d e));
        (* poly_deg g == poly_deg (poly_mul g (poly_mul d e)) *)
        (* Case: if d*e is zero, then g*(d*e) = g*0 ≈ 0, but deg g = Some _, contradiction *)
        (match poly_deg (poly_mul d e) with
         | None ->
             assert (poly_mul d e == (poly_zero #t));
             H.x_mul_zero #(polynomial t) g;
             degree_well_defined (poly_mul g (poly_mul d e)) (poly_zero #t)
             (* poly_deg (poly_mul g (poly_mul d e)) == None, but it equals poly_deg g = Some _ *)
         | Some nde ->
             degree_mul #t #(id_of_f t) g (poly_mul d e);
             (* deg(g*(d*e)) = deg g + nde, but deg(g*(d*e)) == deg g, so nde = 0 *)
             (* From nde = 0 and degree_mul d e: deg d + deg e = 0, hence deg d = 0 *)
             (match poly_deg e with
              | None ->
                  (* e = 0. Then d*e = 0. But we're in Some nde case. Contradiction. *)
                  assert (e == (poly_zero #t));
                  H.x_mul_zero #(polynomial t) d;
                  degree_well_defined (poly_mul d e) (poly_zero #t)
              | Some ne ->
                  degree_mul #t #(id_of_f t) d e
                  (* Now: nde = deg d + deg e.
                     And deg g + nde = deg g (from above).
                     So nde = 0, hence deg d + deg e = 0, hence deg d = 0. *)
             ))
    in
    Classical.forall_intro (Classical.move_requires aux)
#pop-options

(* ================================================================ *)
(*  Degree bound for divisors: if d | p (both nonzero), deg d ≤ deg p *)
(* ================================================================ *)

let divides_degree_le (#t:Type) {| f: field t |}
  (d p: polynomial t)
  : Lemma (requires divides d p /\ Some? (poly_deg d) /\ Some? (poly_deg p))
          (ensures  Some?.v (poly_deg d) <= Some?.v (poly_deg p))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let aux (c: polynomial t)
      : Lemma (requires poly_eq p (poly_mul d c))
              (ensures  Some?.v (poly_deg d) <= Some?.v (poly_deg p))
      = match poly_deg c with
        | None ->
            (* c = 0, so d*c ≈ 0, but poly_eq p (d*c) and p nonzero: contradiction *)
            assert (c == (poly_zero #t));
            H.x_mul_zero #(polynomial t) d;
            poly_eq_symmetry (poly_mul d c) (poly_zero #t);
            poly_eq_transitivity p (poly_mul d c) (poly_zero #t);
            degree_well_defined p (poly_zero #t)
        | Some _ ->
            degree_mul #t #(id_of_f t) d c;
            degree_well_defined p (poly_mul d c)
    in
    Classical.forall_intro (Classical.move_requires aux)

(* ================================================================ *)
(*  Coprime divisor: if coprime(a, b) and d | a, then coprime(d, b) *)
(* ================================================================ *)

#push-options "--z3rlimit 30 --fuel 4 --ifuel 3"
let coprime_divisor (#t:Type) {| f: field t |}
  (a b d: polynomial t)
  : Lemma (requires coprime #t #f a b /\ divides d a /\ Some? (poly_deg d))
          (ensures  coprime #t #f d b)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    coprime_reveal #t #f a b;
    coprime_reveal #t #f d b;
    let e = poly_gcd #t #f d b in
    gcd_divides_left #t #f d b;              // e | d
    gcd_divides_right #t #f d b;             // e | b
    (* e | d and d | a, so e | a by transitivity *)
    divides_trans #(polynomial t) #cr_p e d a;
    (* e | a and e | b, so e | gcd(a, b) *)
    gcd_is_maximal #t #f a b e;
    (* coprime(a, b) means deg(gcd(a,b)) = 0. And e | gcd(a,b).
       Since e divides d which is nonzero, e is nonzero (Some? deg e). *)
    gcd_has_degree #t #f d b;                // Some? (poly_deg e)
    (* deg(gcd(a,b)) = 0 and e | gcd(a,b) with e nonzero: deg e ≤ 0, so deg e = 0 *)
    divides_degree_le e (poly_gcd #t #f a b)
    (* Now: Some?.v (poly_deg e) <= 0, and Some? (poly_deg e), so poly_deg e = Some 0 *)
#pop-options

(* ================================================================ *)
(*  Irreducible polynomials and factor existence                     *)
(* ================================================================ *)

(* A polynomial q is irreducible if deg q ≥ 1 and whenever q = a·b,
   one of a or b has degree 0 (is a unit/scalar). *)
let poly_irreducible (#t:Type) {| f: field t |} (q: polynomial t) : prop
  = Some? (poly_deg q) /\ Some?.v (poly_deg q) >= 1 /\
    (forall (a b: polynomial t).
      (poly_eq q (poly_mul a b) == true) ==>
      (poly_deg a == Some 0 \/ poly_deg a == None \/
       poly_deg b == Some 0 \/ poly_deg b == None))

(* Every polynomial of degree ≥ 1 has an irreducible factor.
   Proof by strong induction on degree. *)
#push-options "--z3rlimit 60"
let rec irreducible_factor_exists (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires Some? (poly_deg p) /\ Some?.v (poly_deg p) >= 1)
          (ensures exists (q: polynomial t). poly_irreducible q /\ divides q p)
          (decreases (if Some? (poly_deg p) then Some?.v (poly_deg p) else 0))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    Classical.excluded_middle (poly_irreducible p);
    (* Case 1: p is irreducible — witness q = p *)
    let case_irred (_: unit)
      : Lemma (requires poly_irreducible p)
              (ensures exists (q: polynomial t). poly_irreducible q /\ divides q p)
      = poly_mul_one p;
        divides_intro #(polynomial t) #cr_p p p (poly_one #t)
    in
    (* Case 2: p is not irreducible — factor and recurse *)
    let case_factor (a b: polynomial t)
      : Lemma (requires poly_eq p (poly_mul a b) == true /\
                        Some? (poly_deg a) /\ Some?.v (poly_deg a) >= 1 /\
                        Some? (poly_deg b) /\ Some?.v (poly_deg b) >= 1)
              (ensures exists (q: polynomial t). poly_irreducible q /\ divides q p)
      = (* deg(a*b) = deg a + deg b, and poly_eq p (a*b) so deg p = deg a + deg b *)
        degree_mul #t #(id_of_f t) a b;
        degree_well_defined p (poly_mul a b);
        (* Therefore deg a = deg p - deg b <= deg p - 1 < deg p *)
        (* Recurse on a (smaller degree) *)
        irreducible_factor_exists a;
        (* Now: exists q. poly_irreducible q /\ divides q a *)
        (* a | p because p ≈ a*b *)
        poly_eq_symmetry p (poly_mul a b);
        divides_intro #(polynomial t) #cr_p a p b;
        (* Chain: q | a and a | p → q | p *)
        let chain (q: polynomial t)
          : Lemma (requires poly_irreducible q /\ divides q a)
                  (ensures exists (q: polynomial t). poly_irreducible q /\ divides q p)
          = divides_trans #(polynomial t) #cr_p q a p
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
  : Lemma (requires not (coeff q k = (zero <: t)))
          (ensures  Some? (poly_deg q) /\ Some?.v (poly_deg q) >= k)
  = // By contrapositive of coeff_above_degree:
    // if None?(poly_deg q) or Some?.v(poly_deg q) < k, then coeff q k = zero.
    // Since coeff q k ≠ zero, we get Some?(poly_deg q) and Some?.v(poly_deg q) >= k.
    Classical.move_requires (coeff_above_degree q) k

(* Helper: in a domain, nat_scale n a ≠ zero when char_zero and a ≠ zero and n ≥ 1 *)
private let nat_scale_nonzero_in_domain (#t:Type) {| f: field t |}
  (n: pos) (a: t)
  : Lemma (requires char_zero f /\ not (a = (zero <: t)))
          (ensures  not (nat_scale #t #((cr_of_id t).cr_r.r_add) n a = (zero <: t)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cr : commutative_ring t = cr_of_id t in
    let acg = cr.cr_r.r_add in
    // nat_scale n one * a = nat_scale n (one * a)  [nat_scale_mul_left]
    nat_scale_mul_left #t #cr n (one #t) a;
    // one * a = a
    H.one_mul_x #t #(cr.cr_r) a;
    // nat_scale n (one * a) = nat_scale n a   [congruence]
    nat_scale_congruence #t #acg n (one * a) a;
    // Combine: nat_scale n one * a = nat_scale n a
    // char_zero: nat_scale n one ≠ zero; hypothesis: a ≠ zero
    // domain: product of nonzero is nonzero
    let d : domain t = d_of_sf t in
    domain_nonzero_mul_nonzero #t #d (nat_scale #t #acg n (one <: t)) a

(* In char 0: the derivative of a polynomial of degree n ≥ 1
   has degree exactly n - 1. The leading coefficient is n · lc(p). *)
let poly_deriv_degree_char0 (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires char_zero f /\ Some? (poly_deg p) /\ Some?.v (poly_deg p) >= 1)
         (ensures  Some? (poly_deg (poly_deriv p)) /\
                   Some?.v (poly_deg (poly_deriv p)) == Prims.op_Subtraction (Some?.v (poly_deg p)) 1)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let n = Some?.v (poly_deg p) in
    let dp = poly_deriv p in
    // Step 1: coeff dp (n-1) = nat_scale n (coeff p n)
    poly_deriv_coeff p (n - 1);
    // Step 2: coeff p n ≠ zero (leading coefficient is nonzero)
    leading_coeff_nonzero p;
    // Step 3: nat_scale n (coeff p n) ≠ zero
    nat_scale_nonzero_in_domain #t #f n (coeff p n);
    // Step 4: coeff dp (n-1) ≠ zero → deg dp >= n-1
    nonzero_coeff_degree_lb dp (n - 1);
    // Step 5: upper bound — deg dp ≤ n-1
    // If deg dp = m >= n, then coeff dp m ≠ zero (leading coeff).
    // But coeff dp m = nat_scale (m+1) (coeff p (m+1)) = nat_scale (m+1) zero = zero.
    // Contradiction. So deg dp < n.
    let m = Some?.v (poly_deg dp) in
    if m >= n then (
      leading_coeff_nonzero dp;
      poly_deriv_coeff p m;
      coeff_above_degree p (Prims.op_Addition m 1);
      nat_scale_zero_element #t #((cr_of_id t).cr_r.r_add) (Prims.op_Addition m 1)
    ) else ()

(* If q is irreducible in char 0 with deg q ≥ 1, then coprime(q, D(q)). *)
#push-options "--z3rlimit 40"
let irreducible_coprime_deriv (#t:Type) {| f: field t |}
  (q: polynomial t)
  : Lemma (requires char_zero f /\ poly_irreducible q)
         (ensures  coprime #t #f q (poly_deriv q))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let g = poly_gcd #t #f q (poly_deriv q) in
    // g | q and g | D(q)
    gcd_divides_left #t #f q (poly_deriv q);
    gcd_divides_right #t #f q (poly_deriv q);
    // From poly_irreducible q: for any factorization q = a*b,
    // one of deg(a), deg(b) is 0 or None.
    // g | q means exists h. poly_eq q (poly_mul g h).
    // We show poly_deg g = Some 0 by contradiction:
    // - If None? poly_deg g: g = zero, so divides zero q → q = zero. But deg q ≥ 1.
    // - If Some?.v poly_deg g >= 1: then in the factorization q = g*h,
    //   irreducibility gives deg(h) = 0 or None.
    //   If deg(h) = None: h = zero, poly_mul g zero = zero, q = zero. Contradiction.
    //   If deg(h) = Some 0: degree_mul gives deg(q) = deg(g) + 0 = deg(g).
    //     But g | D(q) and D(q) is nonzero (deg D(q) = deg(q)-1 ≥ 0).
    //     divides_degree_le gives deg(g) ≤ deg(D(q)) = deg(q) - 1 < deg(q) = deg(g). ⊥
    // Therefore deg(g) = Some 0, i.e., coprime.
    poly_deriv_degree_char0 q;
    coprime_reveal #t #f q (poly_deriv q);
    let aux (h: polynomial t)
      : Lemma (requires poly_eq q (poly_mul g h) == true)
              (ensures  poly_deg g == Some 0)
      = assert (poly_deg g == Some 0 \/ poly_deg g == None \/
                poly_deg h == Some 0 \/ poly_deg h == None);
        if None? (poly_deg g) then (
          degree_none_poly_eq_zero g;
          poly_eq_reflexivity h;
          poly_mul_congruence g h (poly_zero #t) h;
          H.zero_mul_x #(polynomial t) h;
          poly_eq_transitivity (poly_mul g h) (poly_mul (poly_zero #t) h) (poly_zero #t);
          poly_eq_transitivity q (poly_mul g h) (poly_zero #t);
          degree_well_defined q (poly_zero #t)
        ) else if None? (poly_deg h) then (
          degree_none_poly_eq_zero h;
          poly_eq_reflexivity g;
          poly_mul_congruence g h g (poly_zero #t);
          H.x_mul_zero #(polynomial t) g;
          poly_eq_transitivity (poly_mul g h) (poly_mul g (poly_zero #t)) (poly_zero #t);
          poly_eq_transitivity q (poly_mul g h) (poly_zero #t);
          degree_well_defined q (poly_zero #t)
        ) else if poly_deg g = (Some 0 <: option nat) then ()
        else (
          // deg(g) ≥ 1, so from disjunction: deg(h) must be Some 0 (only remaining option)
          assert (Some? (poly_deg h) /\ Some?.v (poly_deg h) = 0);
          // degree_mul: deg(poly_mul g h) = deg(g) + deg(h)
          let id : integral_domain t = id_of_f t in
          degree_mul #t #id g h;
          // Bridge: poly_eq q (poly_mul g h) → poly_deg q == poly_deg (poly_mul g h)
          degree_well_defined q (poly_mul g h);
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
          (ensures  divides (poly_mul d1 d2) (poly_mul a b))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let aux1 (c1: polynomial t)
      : Lemma (requires poly_eq a (poly_mul d1 c1))
              (ensures  divides (poly_mul d1 d2) (poly_mul a b))
      = let aux2 (c2: polynomial t)
          : Lemma (requires poly_eq b (poly_mul d2 c2))
                  (ensures  divides (poly_mul d1 d2) (poly_mul a b))
          = (* a·b ≈ (d1·c1)·(d2·c2) ≈ (d1·d2)·(c1·c2) by assoc/comm *)
            poly_mul_left_congruence a (poly_mul d1 c1) b;
            poly_mul_right_congruence (poly_mul d1 c1) b (poly_mul d2 c2);
            poly_eq_transitivity (poly_mul a b)
              (poly_mul (poly_mul d1 c1) b)
              (poly_mul (poly_mul d1 c1) (poly_mul d2 c2));
            (* (d1·c1)·(d2·c2) = d1·(c1·(d2·c2)) *)
            poly_mul_associativity d1 c1 (poly_mul d2 c2);
            poly_eq_symmetry (poly_mul (poly_mul d1 c1) (poly_mul d2 c2))
                             (poly_mul d1 (poly_mul c1 (poly_mul d2 c2)));
            (* c1·(d2·c2) = (c1·d2)·c2 = (d2·c1)·c2 = d2·(c1·c2) *)
            poly_mul_associativity c1 d2 c2;
            poly_eq_symmetry (poly_mul (poly_mul c1 d2) c2)
                             (poly_mul c1 (poly_mul d2 c2));
            poly_mul_commutativity c1 d2;
            poly_mul_left_congruence (poly_mul c1 d2) (poly_mul d2 c1) c2;
            poly_mul_associativity d2 c1 c2;
            poly_eq_transitivity (poly_mul c1 (poly_mul d2 c2))
              (poly_mul (poly_mul c1 d2) c2)
              (poly_mul (poly_mul d2 c1) c2);
            poly_eq_transitivity (poly_mul c1 (poly_mul d2 c2))
              (poly_mul (poly_mul d2 c1) c2)
              (poly_mul d2 (poly_mul c1 c2));
            (* d1·(c1·(d2·c2)) = d1·(d2·(c1·c2)) *)
            poly_mul_right_congruence d1
              (poly_mul c1 (poly_mul d2 c2))
              (poly_mul d2 (poly_mul c1 c2));
            (* d1·(d2·(c1·c2)) = (d1·d2)·(c1·c2) *)
            poly_mul_associativity d1 d2 (poly_mul c1 c2);
            poly_eq_symmetry (poly_mul (poly_mul d1 d2) (poly_mul c1 c2))
                             (poly_mul d1 (poly_mul d2 (poly_mul c1 c2)));
            poly_eq_transitivity (poly_mul d1 (poly_mul c1 (poly_mul d2 c2)))
              (poly_mul d1 (poly_mul d2 (poly_mul c1 c2)))
              (poly_mul (poly_mul d1 d2) (poly_mul c1 c2));
            (* chain all: a·b ≈ (d1·d2)·(c1·c2) *)
            poly_eq_transitivity (poly_mul a b)
              (poly_mul (poly_mul d1 c1) (poly_mul d2 c2))
              (poly_mul d1 (poly_mul c1 (poly_mul d2 c2)));
            poly_eq_transitivity (poly_mul a b)
              (poly_mul d1 (poly_mul c1 (poly_mul d2 c2)))
              (poly_mul (poly_mul d1 d2) (poly_mul c1 c2));
            divides_intro #(polynomial t) #cr_p
              (poly_mul d1 d2) (poly_mul a b) (poly_mul c1 c2)
        in
        Classical.forall_intro (Classical.move_requires aux2)
    in
    Classical.forall_intro (Classical.move_requires aux1)

(* ================================================================ *)
(*  Helper: poly_power q (n+m) ≈ poly_mul (poly_power q n) (poly_power q m) *)
(* ================================================================ *)

let rec poly_power_add (#t:Type) {| cr: commutative_ring t |}
  (q: polynomial t) (n m: nat)
  : Lemma (ensures poly_eq (poly_power q (Prims.op_Addition n m))
                           (poly_mul (poly_power q n) (poly_power q m)))
          (decreases n)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if n = 0 then begin
      (* poly_power q (0+m) = poly_power q m
         poly_mul (poly_power q 0) (poly_power q m) = poly_mul poly_one (poly_power q m)
         poly_mul_one gives the bridge *)
      poly_mul_one (poly_power q m);
      poly_eq_symmetry (poly_mul (poly_one #t) (poly_power q m)) (poly_power q m)
    end else begin
      (* poly_power q (n+m) = poly_mul q (poly_power q (n+m-1)) [definitional for n+m ≥ 1]
         poly_power q n = poly_mul q (poly_power q (n-1))       [definitional for n ≥ 1]
         IH: poly_power q ((n-1)+m) ≈ poly_mul (poly_power q (n-1)) (poly_power q m)
         Goal: poly_mul q (poly_power q (n+m-1)) ≈ poly_mul (poly_mul q (poly_power q (n-1))) (poly_power q m)
         Chain: LHS ≈ poly_mul q (poly_mul (poly_power q (n-1)) (poly_power q m))  [by IH + congruence]
                    ≈ poly_mul (poly_mul q (poly_power q (n-1))) (poly_power q m)  [by associativity] *)
      poly_power_add q (n - 1) m;
      poly_mul_right_congruence q
        (poly_power q (Prims.op_Addition (n - 1) m))
        (poly_mul (poly_power q (n - 1)) (poly_power q m));
      poly_mul_associativity q (poly_power q (n - 1)) (poly_power q m);
      poly_eq_symmetry
        (poly_mul (poly_mul q (poly_power q (n - 1))) (poly_power q m))
        (poly_mul q (poly_mul (poly_power q (n - 1)) (poly_power q m)));
      poly_eq_transitivity
        (poly_power q (Prims.op_Addition n m))
        (poly_mul q (poly_mul (poly_power q (n - 1)) (poly_power q m)))
        (poly_mul (poly_mul q (poly_power q (n - 1))) (poly_power q m))
    end

(* ================================================================ *)
(*  Ascent step: qⁿ | g ∧ q² | b₀ → q^(n+1) | g                    *)
(*  where g = gcd(p, D(p)), b₀ = p/g.                               *)
(*  Uses repeated_factor_divides_gcd with k = n+2.                  *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
private let g_ascent_step (#t:Type) {| f: field t |}
  (q p: polynomial t) (n: pos)
  : Lemma (requires (let g = poly_gcd #t #f p (poly_deriv p) in
                     let b0 = poly_div #t #f p g in
                     divides (poly_power q n) g /\
                     divides (poly_power q 2) b0 /\
                     Some? (poly_deg q) /\ Some?.v (poly_deg q) >= 1 /\
                     Some? (poly_deg p)))
          (ensures  (let g = poly_gcd #t #f p (poly_deriv p) in
                     divides (poly_power q (Prims.op_Addition n 1)) g))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let g  = poly_gcd #t #f p (poly_deriv p) in
    let b0 = poly_div #t #f p g in
    (* Step 1: establish p ≈ g · b₀ *)
    gcd_has_degree #t #f p (poly_deriv p);
    gcd_divides_left #t #f p (poly_deriv p);
    poly_div_correct #t #f p g;
    (* poly_eq (poly_mul g b0) p *)
    (* Step 2: q^(n+2) | p *)
    divides_product #t #f (poly_power q n) g (poly_power q 2) b0;
    (* divides (poly_mul (poly_power q n) (poly_power q 2)) (poly_mul g b0) *)
    poly_power_add q n 2;
    poly_eq_symmetry (poly_power q (Prims.op_Addition n 2))
                     (poly_mul (poly_power q n) (poly_power q 2));
    divides_congruence_left #(polynomial t) #cr_p
      (poly_mul (poly_power q n) (poly_power q 2))
      (poly_power q (Prims.op_Addition n 2))
      (poly_mul g b0);
    (* divides (poly_power q (n+2)) (poly_mul g b0) *)
    divides_congruence_right #(polynomial t) #cr_p
      (poly_power q (Prims.op_Addition n 2))
      (poly_mul g b0) p;
    (* divides (poly_power q (n+2)) p *)
    (* Step 3: apply repeated_factor_divides_gcd *)
    repeated_factor_divides_gcd #t #f q p (Prims.op_Addition n 2)
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
  : Lemma (requires (let g = poly_gcd #t #f p (poly_deriv p) in
                     let b0 = poly_div #t #f p g in
                     divides q g /\
                     divides (poly_power q 2) b0 /\
                     Some? (poly_deg q) /\ Some?.v (poly_deg q) >= 1 /\
                     Some? (poly_deg p)))
          (ensures  (let g = poly_gcd #t #f p (poly_deriv p) in
                     divides (poly_power q n) g))
          (decreases n)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    let g  = poly_gcd #t #f p (poly_deriv p) in
    let b0 = poly_div #t #f p g in
    if n = 1 then begin
      (* poly_power q 1 = poly_mul q (poly_power q 0) = poly_mul q poly_one.
         Need: divides (poly_mul q poly_one) g, given divides q g.
         poly_mul q poly_one ≈ q by mul_one. *)
      H.elim_equatable_laws (polynomial t) ();
      poly_mul_one q;
      poly_eq_symmetry (poly_mul q (poly_one #t)) q;
      divides_congruence_left #(polynomial t) #cr_p q (poly_power q 1) g
    end else begin
      (* IH: poly_power q (n-1) | g *)
      g_ascent #t #f q p (n - 1);
      (* Step: g_ascent_step gives poly_power q n | g *)
      g_ascent_step #t #f q p (n - 1)
    end
#pop-options

(* ================================================================ *)
(*  Helper: (a+b) - b ≈ a (ring identity for polynomials)           *)
(* ================================================================ *)

private let poly_add_sub_cancel (#t:Type) {| cr: commutative_ring t |}
  (a b: polynomial t)
  : Lemma (ensures poly_eq (poly_sub (poly_add a b) b) a)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* Reveal: poly_sub x y == poly_add x (poly_neg y) *)
    poly_sub_reveal (poly_add a b) b;
    (* Now SMT knows: poly_sub (poly_add a b) b == poly_add (poly_add a b) (poly_neg b) *)
    (* (a+b) + (-b) ≈ a + (b + (-b)) ≈ a + 0 ≈ a *)
    poly_add_associativity a b (poly_neg b);
    poly_add_negation b;
    poly_eq_reflexivity a;
    poly_add_congruence a (poly_add b (poly_neg b)) a (poly_zero #t);
    poly_add_zero a;
    let s1 = poly_add (poly_add a b) (poly_neg b) in
    let s2 = poly_add a (poly_add b (poly_neg b)) in
    let s3 = poly_add a (poly_zero #t) in
    poly_eq_transitivity s1 s2 s3;
    poly_eq_transitivity s1 s3 a

(* ================================================================ *)
(*  Helper: d | (a+b) ∧ d | b → d | a                              *)
(* ================================================================ *)

private let divides_of_sum (#t:Type) {| f: field t |}
  (d a b: polynomial t)
  : Lemma (requires divides d (poly_add a b) /\ divides d b)
          (ensures  divides d a)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* d | (a+b) and d | b → d | (a+b) + (-b) [divides_neg + divides_add] *)
    divides_neg #(polynomial t) #cr_p d b;
    divides_add #(polynomial t) #cr_p d (poly_add a b) (poly_neg b);
    (* Now: divides d (poly_add (poly_add a b) (poly_neg b)) *)
    (* (a+b) + (-b) ≈ a + (b + (-b)) ≈ a + 0 ≈ a *)
    poly_add_associativity a b (poly_neg b);
    poly_add_negation b;
    poly_eq_reflexivity a;
    poly_add_congruence a (poly_add b (poly_neg b)) a (poly_zero #t);
    poly_add_zero a;
    let s1 = poly_add (poly_add a b) (poly_neg b) in
    let s2 = poly_add a (poly_add b (poly_neg b)) in
    let s3 = poly_add a (poly_zero #t) in
    poly_eq_transitivity s1 s2 s3;
    poly_eq_transitivity s1 s3 a;
    divides_congruence_right #(polynomial t) #cr_p d
      (poly_add (poly_add a b) (poly_neg b)) a

(* ================================================================ *)
(*  q² | b₀: from irreducible q with q|b₀ and q|D(b₀) in char 0   *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
private let q_squared_divides_b0 (#t:Type) {| f: field t |}
  (q b0: polynomial t)
  : Lemma (requires char_zero f /\ poly_irreducible q /\
                    divides q b0 /\ divides q (poly_deriv b0))
          (ensures  divides (poly_power q 2) b0)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* q | b₀ means ∃r. b₀ ≈ q·r *)
    let aux (r: polynomial t)
      : Lemma (requires poly_eq b0 (poly_mul q r))
              (ensures  divides (poly_power q 2) b0)
      = (* D(b₀) ≈ D(q·r) ≈ D(q)·r + q·D(r) *)
        poly_deriv_congruence b0 (poly_mul q r);
        poly_deriv_mul q r;
        let dq  = poly_deriv q in
        let dr  = poly_deriv r in
        let sum = poly_add (poly_mul dq r) (poly_mul q dr) in
        poly_eq_transitivity (poly_deriv b0) (poly_deriv (poly_mul q r)) sum;
        (* q | D(b₀), transfer to: q | sum *)
        divides_congruence_right #(polynomial t) #cr_p q (poly_deriv b0) sum;
        (* q | poly_mul q dr: q divides its own product *)
        poly_eq_reflexivity (poly_mul q dr);
        divides_intro #(polynomial t) #cr_p q (poly_mul q dr) dr;
        (* q | sum and q | poly_mul q dr → q | poly_mul dq r *)
        divides_of_sum #t #f q (poly_mul dq r) (poly_mul q dr);
        (* Need: q | poly_mul r dq (commuted) for euclid_lemma *)
        poly_mul_commutativity dq r;
        divides_congruence_right #(polynomial t) #cr_p q (poly_mul dq r) (poly_mul r dq);
        (* coprime(q, D(q)) → by euclid: q | r·D(q) → q | r *)
        irreducible_coprime_deriv #t #f q;
        euclid_lemma #t #f q dq r;
        (* q | r means ∃s. r ≈ q·s. Then b₀ ≈ q·r ≈ q·(q·s) = q²·s. *)
        let aux2 (s: polynomial t)
          : Lemma (requires poly_eq r (poly_mul q s))
                  (ensures  divides (poly_power q 2) b0)
          = (* b₀ ≈ q·r ≈ q·(q·s) = (q·q)·s = poly_power q 2 · s *)
            poly_mul_right_congruence q r (poly_mul q s);
            poly_mul_associativity q q s;
            poly_eq_symmetry (poly_mul (poly_mul q q) s) (poly_mul q (poly_mul q s));
            poly_eq_transitivity (poly_mul q r) (poly_mul q (poly_mul q s))
                                 (poly_mul (poly_mul q q) s);
            (* poly_mul q q == poly_power q 2 [definitionally: poly_mul q (poly_power q 1)
               and poly_power q 1 = poly_mul q poly_one, so poly_power q 2 = poly_mul q (poly_mul q poly_one)]
               Need: poly_eq (poly_mul q q) (poly_power q 2) *)
            poly_mul_one q;
            poly_mul_right_congruence q q (poly_mul q (poly_one #t));
            poly_eq_symmetry (poly_mul q q) (poly_mul q (poly_mul q (poly_one #t)));
            (* Now poly_power q 2 = poly_mul q (poly_power q 1) = poly_mul q (poly_mul q (poly_one))
               which is == poly_mul q (poly_mul q poly_one) definitionally.
               And poly_mul q q ≈ poly_mul q (poly_mul q poly_one) [by mul_one on q] *)
            (* poly_eq (poly_mul (poly_mul q q) s) (poly_mul (poly_power q 2) s) *)
            poly_mul_left_congruence (poly_mul q q) (poly_power q 2) s;
            poly_eq_transitivity (poly_mul q r) (poly_mul (poly_mul q q) s)
                                 (poly_mul (poly_power q 2) s);
            (* b₀ ≈ q·r ≈ (poly_power q 2)·s *)
            poly_eq_transitivity b0 (poly_mul q r) (poly_mul (poly_power q 2) s);
            poly_eq_symmetry b0 (poly_mul (poly_power q 2) s);
            divides_intro #(polynomial t) #cr_p (poly_power q 2) b0 s
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
  : Lemma (requires Some? (poly_deg q) /\ Some?.v (poly_deg q) >= 1)
          (ensures  Some? (poly_deg (poly_power q n)) /\
                    Some?.v (poly_deg (poly_power q n)) >= n)
          (decreases n)
  = if n = 1 then begin
      assert (poly_power q 0 == (poly_one #t));
      degree_mul #t #(id_of_f t) q (poly_one #t)
    end else begin
      poly_power_degree_bound q (n - 1);
      degree_mul #t #(id_of_f t) q (poly_power q (n - 1))
    end
#pop-options

(* ================================================================ *)
(*  Exact degree of poly_power: deg(q^n) = n * deg(q)               *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 4 --ifuel 2"
let rec poly_power_degree_exact (#t:Type) {| f: field t |}
  (q: polynomial t) (n: pos)
  : Lemma (requires Some? (poly_deg q))
          (ensures  Some? (poly_deg (poly_power q n)) /\
                    Some?.v (poly_deg (poly_power q n)) ==
                    Prims.op_Star n (Some?.v (poly_deg q)))
          (decreases n)
  = if n = 1 then
      degree_mul #t #(id_of_f t) q (poly_one #t)
    else begin
      poly_power_degree_exact q (n - 1);
      assert (Some? (poly_deg (poly_power q (n - 1))));
      degree_mul #t #(id_of_f t) q (poly_power q (n - 1));
      assert (Some? (poly_deg (poly_mul q (poly_power q (n - 1)))));
      let dq = Some?.v (poly_deg q) in
      let dpn1 = Some?.v (poly_deg (poly_power q (n - 1))) in
      assert (dpn1 == Prims.op_Star (n - 1) dq);
      assert (Some?.v (poly_deg (poly_mul q (poly_power q (n - 1)))) ==
              Prims.op_Addition dq dpn1)
    end
#pop-options

(* ================================================================ *)
(*  Degree of flat_product: deg(∏ ds) = Σ deg(dᵢ)                   *)
(* ================================================================ *)

#push-options "--z3rlimit 40 --fuel 4 --ifuel 2"
let rec degree_flat_product (#t:Type) {| f: field t |}
  (ds: list (polynomial t))
  : Lemma (requires (forall (k:nat). k < L.length ds ==> Some? (poly_deg (L.index ds k))))
          (ensures  (match ds with
                     | [] -> poly_deg (flat_product ds) == Some 0
                     | _  -> Some? (poly_deg (flat_product ds))))
          (decreases ds)
  = match ds with
    | [] -> ()  (* flat_product [] = poly_one, deg poly_one = Some 0 *)
    | [d] ->
        (* flat_product [d] = poly_mul d poly_one. deg = deg d + 0 = deg d. *)
        degree_mul #t #(id_of_f t) d (poly_one #t)
    | d :: rest ->
        assert (forall (k:nat). k < L.length rest ==>
                  L.index rest k == L.index (d :: rest) (Prims.op_Addition k 1));
        assert (forall (k:nat). k < L.length rest ==> Some? (poly_deg (L.index rest k)));
        degree_flat_product rest;
        degree_mul #t #(id_of_f t) d (flat_product rest)
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
  : Lemma (requires char_zero f /\ Some? (poly_deg p) /\ Some?.v (poly_deg p) >= 1)
         (ensures  (let g = poly_gcd #t #f p (poly_deriv p) in
                    let b0 = poly_div #t #f p g in
                    square_free #t #f b0))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let g  = poly_gcd #t #f p (poly_deriv p) in
    let b0 = poly_div #t #f p g in
    (* Establish p ≈ g·b0 *)
    gcd_has_degree #t #f p (poly_deriv p);
    gcd_divides_left #t #f p (poly_deriv p);
    poly_div_correct #t #f p g;
    (* poly_eq (poly_mul g b0) p *)
    (* Proof by contradiction: assume ~(square_free b0) *)
    Classical.excluded_middle (square_free #t #f b0 = true);
    let case_not_sf (_: unit)
      : Lemma (requires square_free #t #f b0 <> true)
              (ensures  False)
      = (* square_free b0 = coprime b0 (poly_deriv b0) = false means
           gcd(b0, D(b0)) has degree != 0, hence >= 1 *)
        coprime_reveal #t #f b0 (poly_deriv b0);
        (* Need: Some? (poly_deg b0) — from p ≈ g·b0, deg p = deg g + deg b0 *)
        poly_mul_commutativity g b0;
        poly_eq_transitivity (poly_mul b0 g) (poly_mul g b0) p;
        divides_intro #(polynomial t) #cr_p b0 p g;
        divides_degree_le b0 p;
        (* gcd_has_degree for b0 and D(b0): *)
        gcd_has_degree #t #f b0 (poly_deriv b0);
        let gb = poly_gcd #t #f b0 (poly_deriv b0) in
        (* gb has degree >= 1 (from coprime_reveal + square_free = false) *)
        (* irreducible_factor_exists on gb *)
        irreducible_factor_exists #t #f gb;
        let aux_q (q: polynomial t)
          : Lemma (requires poly_irreducible q /\ divides q gb)
                  (ensures  False)
          = (* Step 1: q | b0 and q | D(b0) *)
            gcd_divides_left #t #f b0 (poly_deriv b0);
            gcd_divides_right #t #f b0 (poly_deriv b0);
            divides_trans #(polynomial t) #cr_p q gb b0;
            divides_trans #(polynomial t) #cr_p q gb (poly_deriv b0);
            (* Step 2: q² | b0 via q_squared_divides_b0 *)
            q_squared_divides_b0 #t #f q b0;
            (* Step 3: Show q | g *)
            (* 3a: q | p (from q | b0 and b0 | p) *)
            divides_trans #(polynomial t) #cr_p q b0 p;
            (* 3b: q | D(p) via product rule on p ≈ g·b0 *)
            let dg  = poly_deriv g in
            let db0 = poly_deriv b0 in
            poly_deriv_mul g b0;
            poly_deriv_congruence (poly_mul g b0) p;
            poly_eq_symmetry (poly_deriv (poly_mul g b0)) (poly_deriv p);
            poly_eq_transitivity (poly_deriv p) (poly_deriv (poly_mul g b0))
              (poly_add (poly_mul dg b0) (poly_mul g db0));
            (* q | (dg · b0): from q | b0 *)
            divides_mul_left #(polynomial t) #cr_p q dg b0;
            (* q | (g · D(b0)): from q | D(b0) *)
            divides_mul_left #(polynomial t) #cr_p q g db0;
            (* q | (dg·b0 + g·D(b0)) *)
            divides_add #(polynomial t) #cr_p q (poly_mul dg b0) (poly_mul g db0);
            (* q | D(p) by congruence *)
            poly_eq_symmetry (poly_deriv p)
              (poly_add (poly_mul dg b0) (poly_mul g db0));
            divides_congruence_right #(polynomial t) #cr_p q
              (poly_add (poly_mul dg b0) (poly_mul g db0))
              (poly_deriv p);
            (* 3c: q | p and q | D(p) → q | gcd(p, D(p)) = g *)
            gcd_is_maximal #t #f p (poly_deriv p) q;
            (* Step 4: g_ascent → q^n | g for all n *)
            (* Pick n = deg(g) + 1 *)
            let n : pos = Prims.op_Addition (Some?.v (poly_deg g)) 1 in
            g_ascent #t #f q p n;
            (* Step 5: contradiction via degree *)
            poly_power_degree_bound #t #f q n;
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
  : Lemma (requires char_zero f /\ square_free #t #f b0 /\
                   divides d b0 /\ Some? (poly_deg d) /\ Some? (poly_deg b0))
          (ensures  square_free #t #f d)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    Classical.excluded_middle (square_free #t #f d = true);
    let case_not (_: unit)
      : Lemma (requires square_free #t #f d <> true)
              (ensures  False)
      = coprime_reveal #t #f d (poly_deriv d);
        gcd_has_degree #t #f d (poly_deriv d);
        let gd = poly_gcd #t #f d (poly_deriv d) in
        irreducible_factor_exists #t #f gd;
        let aux_q (q: polynomial t)
          : Lemma (requires poly_irreducible q /\ divides q gd)
                 (ensures  False)
          = (* q | d and q | D(d) *)
            gcd_divides_left #t #f d (poly_deriv d);
            gcd_divides_right #t #f d (poly_deriv d);
            divides_trans #(polynomial t) #cr_p q gd d;
            divides_trans #(polynomial t) #cr_p q gd (poly_deriv d);
            (* q² | d via q_squared_divides_b0 applied to d *)
            q_squared_divides_b0 #t #f q d;
            (* q² | b₀ by transitivity *)
            divides_trans #(polynomial t) #cr_p (poly_power q 2) d b0;
            (* q | D(b₀) via repeated_factor_divides_deriv *)
            repeated_factor_divides_deriv #t #f q b0 2;
            (* poly_power q 1 | D(b₀), bridge to q | D(b₀) *)
            poly_mul_one q;
            poly_eq_symmetry (poly_mul q (poly_one #t)) q;
            divides_congruence_left #(polynomial t) #cr_p
              (poly_power q 1) q (poly_deriv b0);
            (* q | b₀ (from q | d | b₀) *)
            divides_trans #(polynomial t) #cr_p q d b0;
            (* q | gcd(b₀, D(b₀)) *)
            gcd_is_maximal #t #f b0 (poly_deriv b0) q;
            (* But square_free b₀ means deg(gcd(b₀, D(b₀))) = 0 *)
            coprime_reveal #t #f b0 (poly_deriv b0);
            gcd_has_degree #t #f b0 (poly_deriv b0);
            divides_degree_le q (poly_gcd #t #f b0 (poly_deriv b0))
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
  : Lemma (requires char_zero f /\ square_free #t #f p /\
                    poly_eq p (poly_mul a b) /\
                    Some? (poly_deg p) /\ Some? (poly_deg a) /\ Some? (poly_deg b))
          (ensures  coprime #t #f a b)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    coprime_reveal #t #f a b;
    Classical.excluded_middle (coprime #t #f a b = true);
    let case_not (_: unit)
      : Lemma (requires coprime #t #f a b <> true)
              (ensures  False)
      = gcd_has_degree #t #f a b;
        let gab = poly_gcd #t #f a b in
        irreducible_factor_exists #t #f gab;
        let aux_q (q: polynomial t)
          : Lemma (requires poly_irreducible q /\ divides q gab)
                  (ensures  False)
          = gcd_divides_left #t #f a b;
            gcd_divides_right #t #f a b;
            divides_trans #(polynomial t) #cr_p q gab a;
            divides_trans #(polynomial t) #cr_p q gab b;
            (* q|a and q|b → q²|a·b via divides_product *)
            divides_product #t #f q a q b;
            (* Bridge: poly_eq (poly_mul q q) (poly_power q 2) *)
            (* poly_power q 2 == poly_mul q (poly_mul q poly_one) definitionally *)
            assert (poly_power q 2 == poly_mul q (poly_mul q (poly_one #t)));
            (* poly_mul_one q: poly_eq (poly_mul q poly_one) q *)
            poly_mul_one q;
            (* symmetry: poly_eq q (poly_mul q poly_one) *)
            poly_eq_symmetry (poly_mul q (poly_one #t)) q;
            (* poly_mul_right_congruence q q (poly_mul q poly_one):
               requires poly_eq q (poly_mul q poly_one)
               gives poly_eq (poly_mul q q) (poly_mul q (poly_mul q poly_one)) *)
            poly_mul_right_congruence q q (poly_mul q (poly_one #t));
            (* So: poly_eq (poly_mul q q) (poly_power q 2) *)
            divides_congruence_left #(polynomial t) #cr_p
              (poly_mul q q) (poly_power q 2) (poly_mul a b);
            (* q² | a·b, transfer to: q² | p *)
            poly_eq_symmetry p (poly_mul a b);
            divides_congruence_right #(polynomial t) #cr_p
              (poly_power q 2) (poly_mul a b) p;
            (* q² | p → poly_power q 1 | D(p) *)
            repeated_factor_divides_deriv #t #f q p 2;
            (* Bridge: poly_power q 1 ≈ q, so divides q (poly_deriv p) *)
            poly_mul_one q;
            divides_congruence_left #(polynomial t) #cr_p
              (poly_power q 1) q (poly_deriv p);
            (* q | p: from q | a, a | a·b ≈ p *)
            poly_eq_reflexivity (poly_mul a b);
            divides_intro #(polynomial t) #cr_p a (poly_mul a b) b;
            divides_trans #(polynomial t) #cr_p q a (poly_mul a b);
            divides_congruence_right #(polynomial t) #cr_p
              q (poly_mul a b) p;
            (* q | gcd(p, D(p)) *)
            gcd_is_maximal #t #f p (poly_deriv p) q;
            (* But square_free p → deg(gcd(p, D(p))) = 0 *)
            coprime_reveal #t #f p (poly_deriv p);
            gcd_has_degree #t #f p (poly_deriv p);
            divides_degree_le q (poly_gcd #t #f p (poly_deriv p))
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
  : Lemma (requires coprime #t #f a b /\ divides d b /\ Some? (poly_deg a))
          (ensures  coprime #t #f a d)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    coprime_reveal #t #f a d;
    let gad = poly_gcd #t #f a d in
    gcd_has_degree #t #f a d;
    (* gad | a and gad | d *)
    gcd_divides_left #t #f a d;
    gcd_divides_right #t #f a d;
    (* gad | b (transitivity: gad | d | b) *)
    divides_trans #(polynomial t) #cr_p gad d b;
    (* gad | gcd(a, b) by maximality *)
    gcd_is_maximal #t #f a b gad;
    (* deg(gcd(a, b)) = 0 from coprime(a, b) *)
    coprime_reveal #t #f a b;
    gcd_has_degree #t #f a b;
    (* deg(gad) ≤ deg(gcd(a,b)) = 0 *)
    divides_degree_le gad (poly_gcd #t #f a b)

(* ================================================================ *)
(*  coprime(gcd(b,d), b/gcd(b,d)) when b is square-free             *)
(* ================================================================ *)

(* At each Yun step, the factor aₖ = gcd(b,d) is coprime with
   the quotient bₖ = b/aₖ, because b is square-free and b = aₖ · bₖ. *)
let yun_step_coprime (#t:Type) {| f: field t |}
  (b d: polynomial t)
  : Lemma (requires char_zero f /\ square_free #t #f b /\
                    Some? (poly_deg b) /\ Some?.v (poly_deg b) >= 1)
          (ensures  (let a = poly_gcd #t #f b d in
                     let b' = poly_div #t #f b a in
                     coprime #t #f a b'))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let a = poly_gcd #t #f b d in
    let b' = poly_div #t #f b a in
    gcd_has_degree #t #f b d;
    gcd_divides_left #t #f b d;
    poly_div_correct #t #f b a;
    poly_div_nonzero #t #f b a;
    (* poly_eq (poly_mul a b') b *)
    (* b is square-free, so coprime(a, b') *)
    poly_eq_symmetry (poly_mul a b') b;
    square_free_coprime_factors #t #f b a b'

(* ================================================================ *)
(*  coprime(aₖ, aⱼ) for j > k: aⱼ divides bₖ, coprime(aₖ, bₖ)     *)
(* ================================================================ *)

(* coprime is symmetric (via mutual divisibility of gcds) *)
let coprime_symmetric (#t:Type) {| f: field t |}
  (a b: polynomial t)
  : Lemma (requires coprime #t #f a b /\ Some? (poly_deg a) /\ Some? (poly_deg b))
          (ensures  coprime #t #f b a)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    coprime_reveal #t #f a b;
    coprime_reveal #t #f b a;
    let gab = poly_gcd #t #f a b in
    let gba = poly_gcd #t #f b a in
    gcd_has_degree #t #f a b;
    gcd_has_degree #t #f b a;
    (* gab | a, gab | b → gab | gcd(b, a) *)
    gcd_divides_left #t #f a b;
    gcd_divides_right #t #f a b;
    gcd_is_maximal #t #f b a gab;
    (* gba | b, gba | a → gba | gcd(a, b) *)
    gcd_divides_left #t #f b a;
    gcd_divides_right #t #f b a;
    gcd_is_maximal #t #f a b gba;
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
  : Lemma (ensures L.length (L.append l1 [x]) == Prims.op_Addition (L.length l1) 1 /\
                   L.index (L.append l1 [x]) (L.length l1) == x)
          (decreases l1)
  = match l1 with
    | [] -> ()
    | _ :: t -> append_snoc_index t x

(* The yun_loop output is always at least as long as acc *)
private let rec yun_loop_acc_length (#t:Type) {| f: field t |}
  (b d: polynomial t) (acc: list (polynomial t)) (fuel: nat)
  : Lemma (ensures L.length (yun_loop #t #f b d acc fuel) >= L.length acc)
          (decreases fuel)
  = if fuel = 0 then L.append_length acc [b]
    else if None? (poly_deg b) then L.append_length acc [b]
    else if Some?.v (poly_deg b) = 0 then L.append_length acc [b]
    else begin
      let a = poly_gcd #t #f b d in
      let b' = poly_div #t #f b a in
      let c' = poly_div #t #f d a in
      let d' = poly_sub c' (poly_deriv b') in
      let acc' = L.append acc [a] in
      yun_loop_acc_length #t #f b' d' acc' (fuel - 1);
      L.append_length acc [a]
    end

(* Elements originally in acc are preserved in yun_loop output *)
private let rec yun_loop_preserves_acc (#t:Type) {| f: field t |}
  (b d: polynomial t) (acc: list (polynomial t)) (fuel: nat)
  (k: nat{k < L.length acc})
  : Lemma (ensures k < L.length (yun_loop #t #f b d acc fuel) /\
                   L.index (yun_loop #t #f b d acc fuel) k == L.index acc k)
          (decreases fuel)
  = yun_loop_acc_length #t #f b d acc fuel;
    if fuel = 0 then
      append_index_left acc [b] k
    else if None? (poly_deg b) then
      append_index_left acc [b] k
    else if Some?.v (poly_deg b) = 0 then
      append_index_left acc [b] k
    else begin
      let a = poly_gcd #t #f b d in
      let b' = poly_div #t #f b a in
      let c' = poly_div #t #f d a in
      let d' = poly_sub c' (poly_deriv b') in
      let acc' = L.append acc [a] in
      L.append_length acc [a];
      append_index_left acc [a] k;
      yun_loop_preserves_acc #t #f b' d' acc' (fuel - 1) k
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
  : Lemma (requires char_zero f /\ square_free #t #f b /\ Some? (poly_deg b) /\
                    k < L.length acc /\ j >= L.length acc /\
                    j < L.length (yun_loop #t #f b d acc fuel) /\
                    Some? (poly_deg (L.index acc k)) /\
                    coprime #t #f (L.index acc k) b)
          (ensures  coprime #t #f (L.index acc k) (L.index (yun_loop #t #f b d acc fuel) j))
          (decreases fuel)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if fuel = 0 then begin
      (* result = append acc [b], j = |acc|, output[j] = b *)
      L.append_length acc [b];
      append_snoc_index acc b
      (* coprime (acc[k]) b is given *)
    end
    else if None? (poly_deg b) then begin
      (* result = append acc [b], j = |acc|, output[j] = b *)
      L.append_length acc [b];
      append_snoc_index acc b
    end
    else if Some?.v (poly_deg b) = 0 then begin
      (* result = append acc [b], j = |acc|, output[j] = b *)
      L.append_length acc [b];
      append_snoc_index acc b
    end
    else begin
      let a = poly_gcd #t #f b d in
      let b' = poly_div #t #f b a in
      let c' = poly_div #t #f d a in
      let d' = poly_sub c' (poly_deriv b') in
      let acc' = L.append acc [a] in
      L.append_length acc [a];
      if j = L.length acc then begin
        (* output[j] = a (preserved from acc') *)
        yun_loop_preserves_acc #t #f b' d' acc' (fuel - 1) j;
        append_snoc_index acc a;
        (* coprime(acc[k], a): acc[k] coprime with b, and a | b *)
        gcd_divides_left #t #f b d;
        gcd_has_degree #t #f b d;
        coprime_of_divisor #t #f (L.index acc k) b a
      end
      else begin
        (* j > |acc|, so j >= |acc'| *)
        (* Need: coprime(acc[k], b') and square_free b' for the IH *)
        gcd_has_degree #t #f b d;
        gcd_divides_left #t #f b d;
        poly_div_correct #t #f b a;
        poly_div_nonzero #t #f b a;
        (* b' | b: from b ≈ a · b' *)
        poly_eq_symmetry (poly_mul a b') b;
        poly_mul_commutativity a b';
        poly_eq_transitivity b (poly_mul a b') (poly_mul b' a);
        divides_intro #(polynomial t) #cr_p b' b a;
        (* square_free b' by divisor_of_square_free *)
        divisor_of_square_free #t #f b' b;
        (* coprime(acc[k], b') by coprime_of_divisor *)
        coprime_of_divisor #t #f (L.index acc k) b b';
        (* Prepare for IH: acc'[k] == acc[k] *)
        append_index_left acc [a] k;
        (* Apply IH *)
        yun_loop_old_coprime_new #t #f b' d' acc' (fuel - 1) k j
      end
    end
#pop-options

(* New factor at step coprime with all LATER output factors.
   Uses: coprime(a, b') from yun_step_coprime, then old_coprime_new. *)
#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
private let rec yun_loop_new_coprime_later (#t:Type) {| f: field t |}
  (b d: polynomial t) (acc: list (polynomial t)) (fuel: nat)
  (j: nat)
  : Lemma (requires char_zero f /\ square_free #t #f b /\ Some? (poly_deg b) /\
                    Some?.v (poly_deg b) >= 1 /\
                    j > L.length acc /\
                    j < L.length (yun_loop #t #f b d acc fuel))
          (ensures  coprime #t #f (L.index (yun_loop #t #f b d acc fuel) (L.length acc))
                                  (L.index (yun_loop #t #f b d acc fuel) j))
          (decreases fuel)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if fuel = 0 then begin
      (* result = append acc [b], |output| = |acc|+1, j > |acc| → j >= |acc|+1 but j < |acc|+1: impossible *)
      L.append_length acc [b]
    end
    else if None? (poly_deg b) then
      (* result = append acc [b], |result| = |acc|+1, j > |acc| → j >= |acc|+1 but j < |acc|+1: impossible *)
      L.append_length acc [b]
    else if Some?.v (poly_deg b) = 0 then
      (* result = append acc [b], |result| = |acc|+1, j > |acc| → j >= |acc|+1 but j < |acc|+1: impossible *)
      L.append_length acc [b]
    else begin
      let a = poly_gcd #t #f b d in
      let b' = poly_div #t #f b a in
      let c' = poly_div #t #f d a in
      let d' = poly_sub c' (poly_deriv b') in
      let acc' = L.append acc [a] in
      L.append_length acc [a];
      (* output[|acc|] = a (preserved from acc') *)
      yun_loop_preserves_acc #t #f b' d' acc' (fuel - 1) (L.length acc);
      append_snoc_index acc a;
      (* Establish key facts about a and b' *)
      gcd_has_degree #t #f b d;
      gcd_divides_left #t #f b d;
      poly_div_correct #t #f b a;
      poly_div_nonzero #t #f b a;
      (* b' divides b: from b ≈ a · b' → b ≈ b' · a *)
      poly_eq_symmetry (poly_mul a b') b;
      poly_mul_commutativity a b';
      poly_eq_transitivity b (poly_mul a b') (poly_mul b' a);
      divides_intro #(polynomial t) #cr_p b' b a;
      (* square_free b' by divisor_of_square_free *)
      divisor_of_square_free #t #f b' b;
      (* coprime(a, b') from yun_step_coprime *)
      yun_step_coprime #t #f b d;
      (* j >= |acc'| = |acc|+1, so apply yun_loop_old_coprime_new on (b', d', acc', fuel-1, |acc|, j) *)
      (* acc'[|acc|] = a and coprime(a, b') *)
      yun_loop_old_coprime_new #t #f b' d' acc' (fuel - 1) (L.length acc) j
    end
#pop-options


(* ================================================================ *)
(*  Yun loop factors are square-free                                 *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
private let rec yun_loop_square_free (#t:Type) {| f: field t |}
  (b d: polynomial t) (acc: list (polynomial t)) (fuel: nat) (k: nat)
  : Lemma (requires char_zero f /\ square_free #t #f b /\ Some? (poly_deg b) /\
                    k >= L.length acc /\ k < L.length (yun_loop #t #f b d acc fuel))
          (ensures  square_free #t #f (L.index (yun_loop #t #f b d acc fuel) k))
          (decreases fuel)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if fuel = 0 then begin
      (* result = append acc [b], k >= |acc|, k < |acc|+1 → k = |acc| *)
      L.append_length acc [b];
      append_snoc_index acc b
      (* L.index result k = b, and square_free b is in the requires *)
    end
    else if None? (poly_deg b) then ()  (* impossible: contradicts Some? (poly_deg b) *)
    else if Some?.v (poly_deg b) = 0 then begin
      (* result = append acc [b], k = |acc|, factor at k is b *)
      L.append_length acc [b];
      append_snoc_index acc b;
      (* b has degree 0 → L.length b = 1 → poly_deriv b = poly_zero *)
      poly_deriv_const b;
      (* poly_gcd b (poly_deriv b) == poly_gcd b poly_zero == b *)
      poly_gcd_base b (poly_deriv b)
      (* poly_deg(gcd(b, D(b))) = poly_deg b = Some 0 → coprime → square_free *)
    end
    else begin
      let a = poly_gcd #t #f b d in
      let b' = poly_div #t #f b a in
      let c' = poly_div #t #f d a in
      let d' = poly_sub c' (poly_deriv b') in
      let acc' = L.append acc [a] in
      L.append_length acc [a];
      if k = L.length acc then begin
        (* Factor at index |acc| is a = gcd(b, d) *)
        yun_loop_preserves_acc #t #f b' d' acc' (fuel - 1) k;
        append_snoc_index acc a;
        (* L.index result k == a *)
        (* a | b by gcd_divides_left *)
        gcd_divides_left #t #f b d;
        gcd_has_degree #t #f b d;
        (* square_free a by divisor_of_square_free *)
        divisor_of_square_free #t #f a b
      end
      else begin
        (* k > |acc|, so k >= |acc'| *)
        (* Need: square_free b' /\ Some? (poly_deg b') *)
        yun_step_reconstruction #t #f b d;
        (* poly_eq (poly_mul a b') b *)
        gcd_has_degree #t #f b d;
        poly_div_nonzero #t #f b a;
        (* Some? (poly_deg b') *)
        (* divides b' b: from poly_eq (poly_mul a b') b *)
        poly_eq_symmetry (poly_mul a b') b;
        poly_mul_commutativity a b';
        poly_eq_transitivity b (poly_mul a b') (poly_mul b' a);
        divides_intro #(polynomial t) #cr_p b' b a;
        (* square_free b' by divisor_of_square_free *)
        divisor_of_square_free #t #f b' b;
        (* Apply IH *)
        yun_loop_square_free #t #f b' d' acc' (fuel - 1) k
      end
    end
#pop-options

(* ================================================================ *)
(*  Top-level: Yun output factors are square-free                    *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
let yun_factors_square_free (#t:Type) {| f: field t |}
  (p: polynomial t) (k: nat)
  : Lemma (requires char_zero f /\ Some? (poly_deg p) /\
                    Some?.v (poly_deg p) >= 1 /\
                    k < L.length (yun #t #f p))
          (ensures  square_free #t #f (L.index (yun #t #f p) k))
  = let p' = poly_deriv p in
    let a0 = poly_gcd #t #f p p' in
    let b0 = poly_div #t #f p a0 in
    let c0 = poly_div #t #f p' a0 in
    let d0 = poly_sub c0 (poly_deriv b0) in
    let fuel = (match poly_deg a0 with | None -> 0 | Some n -> Prims.op_Addition n 1) in
    (* b₀ is square-free by b0_is_square_free *)
    gcd_has_degree #t #f p p';
    gcd_divides_left #t #f p p';
    poly_div_correct #t #f p a0;
    poly_div_nonzero #t #f p a0;
    b0_is_square_free #t #f p;
    (* b₀ has positive degree (from poly_div_nonzero) *)
    yun_loop_square_free #t #f b0 d0 [] fuel k
#pop-options

(* ================================================================ *)
(*  Pairwise coprimality of Yun output factors                       *)
(* ================================================================ *)

(* Any two distinct NEW factors from the loop are coprime. *)
#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
private let rec yun_loop_pairwise_coprime (#t:Type) {| f: field t |}
  (b d: polynomial t) (acc: list (polynomial t)) (fuel: nat)
  (i j: nat)
  : Lemma (requires char_zero f /\ square_free #t #f b /\ Some? (poly_deg b) /\
                    i >= L.length acc /\ i < j /\
                    j < L.length (yun_loop #t #f b d acc fuel))
          (ensures  coprime #t #f (L.index (yun_loop #t #f b d acc fuel) i)
                                  (L.index (yun_loop #t #f b d acc fuel) j))
          (decreases fuel)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if fuel = 0 then begin
      (* output = append acc [b], so |output| = |acc|+1, i >= |acc|, j < |acc|+1 *)
      (* → i = |acc|, j >= |acc|+1 impossible: contradiction *)
      L.append_length acc [b]
    end
    else if None? (poly_deg b) then
      (* result = append acc [b], |result| = |acc|+1, i >= |acc|, i < j < |acc|+1: impossible *)
      L.append_length acc [b]
    else if Some?.v (poly_deg b) = 0 then
      (* result = append acc [b], |result| = |acc|+1, i >= |acc|, i < j < |acc|+1: impossible *)
      L.append_length acc [b]
    else begin
      let a = poly_gcd #t #f b d in
      let b' = poly_div #t #f b a in
      let c' = poly_div #t #f d a in
      let d' = poly_sub c' (poly_deriv b') in
      let acc' = L.append acc [a] in
      L.append_length acc [a];
      if i = L.length acc then
        (* i is the current gcd, j > i, use yun_loop_new_coprime_later *)
        yun_loop_new_coprime_later #t #f b d acc fuel j
      else begin
        (* i > |acc|, so i >= |acc'|. Recurse. *)
        (* Need: square_free b', Some? (poly_deg b'), Some?.v (poly_deg b') >= 1 *)
        gcd_has_degree #t #f b d;
        gcd_divides_left #t #f b d;
        poly_div_correct #t #f b a;
        poly_div_nonzero #t #f b a;
        poly_eq_symmetry (poly_mul a b') b;
        poly_mul_commutativity a b';
        poly_eq_transitivity b (poly_mul a b') (poly_mul b' a);
        divides_intro #(polynomial t) #cr_p b' b a;
        divisor_of_square_free #t #f b' b;
        yun_loop_pairwise_coprime #t #f b' d' acc' (fuel - 1) i j
      end
    end
#pop-options

(* Top-level: Yun output factors are pairwise coprime. *)
#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
let yun_factors_coprime (#t:Type) {| f: field t |}
  (p: polynomial t) (i j: nat)
  : Lemma (requires char_zero f /\ Some? (poly_deg p) /\
                    Some?.v (poly_deg p) >= 1 /\
                    i < j /\ j < L.length (yun #t #f p))
          (ensures  coprime #t #f (L.index (yun #t #f p) i)
                                  (L.index (yun #t #f p) j))
  = let p' = poly_deriv p in
    let a0 = poly_gcd #t #f p p' in
    let b0 = poly_div #t #f p a0 in
    let c0 = poly_div #t #f p' a0 in
    let d0 = poly_sub c0 (poly_deriv b0) in
    let fuel = (match poly_deg a0 with | None -> 0 | Some n -> Prims.op_Addition n 1) in
    gcd_has_degree #t #f p p';
    gcd_divides_left #t #f p p';
    poly_div_correct #t #f p a0;
    poly_div_nonzero #t #f p a0;
    b0_is_square_free #t #f p;
    yun_loop_pairwise_coprime #t #f b0 d0 [] fuel i j
#pop-options

(* ================================================================ *)
(*  Powered product infrastructure: poly_power lemmas                *)
(* ================================================================ *)

(* poly_power p 0 = poly_one definitionally *)

private let poly_power_one (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t)
  : Lemma (poly_eq (poly_power p 1) p)
  = (* poly_power p 1 == poly_mul p (poly_power p 0) == poly_mul p poly_one *)
    poly_mul_one p

private let rec poly_power_congruence (#t:Type) {| cr: commutative_ring t |}
  (a b: polynomial t) (n: nat)
  : Lemma (requires poly_eq a b)
          (ensures  poly_eq (poly_power a n) (poly_power b n))
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
  : Lemma (ensures poly_eq (poly_power (poly_mul a b) n)
                           (poly_mul (poly_power a n) (poly_power b n)))
          (decreases n)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if n = 0 then begin
      (* Both sides: poly_one. LHS = poly_power (a·b) 0 = poly_one.
         RHS = poly_mul (poly_power a 0) (poly_power b 0) = poly_mul poly_one poly_one ≈ poly_one. *)
      poly_mul_one (poly_one #t);
      poly_eq_symmetry (poly_mul (poly_one #t) (poly_one #t)) (poly_one #t)
    end
    else begin
      let ab = poly_mul a b in
      let an1 = poly_power a (n-1) in
      let bn1 = poly_power b (n-1) in
      poly_power_mul a b (n-1);
      (* IH: (a·b)^(n-1) ≈ a^(n-1) · b^(n-1) *)
      poly_mul_right_congruence ab (poly_power ab (n-1)) (poly_mul an1 bn1);
      (* (a·b)·(a·b)^(n-1) ≈ (a·b)·(a^(n-1)·b^(n-1)) *)
      let x = poly_mul an1 bn1 in
      (* Rearrange (a·b)·(an1·bn1) to (a·an1)·(b·bn1): *)
      poly_mul_associativity a b x;
      (* ab·x ≈ a·(b·x) *)
      poly_mul_associativity b an1 bn1;
      poly_mul_commutativity b an1;
      poly_mul_left_congruence (poly_mul b an1) (poly_mul an1 b) bn1;
      poly_mul_associativity an1 b bn1;
      (* b·(an1·bn1) ≈ (b·an1)·bn1 ≈ (an1·b)·bn1 ≈ an1·(b·bn1) *)
      let m1 = poly_mul b x in
      let m2 = poly_mul (poly_mul b an1) bn1 in
      let m3 = poly_mul (poly_mul an1 b) bn1 in
      let m4 = poly_mul an1 (poly_mul b bn1) in
      poly_eq_symmetry m2 m1;
      poly_eq_transitivity m1 m2 m3;
      poly_eq_transitivity m1 m3 m4;
      poly_mul_right_congruence a m1 m4;
      poly_mul_associativity a an1 (poly_mul b bn1);
      poly_eq_symmetry (poly_mul (poly_mul a an1) (poly_mul b bn1))
                       (poly_mul a (poly_mul an1 (poly_mul b bn1)));
      (* Full chain *)
      let lhs = poly_power ab n in
      let s1 = poly_mul ab x in
      let s2 = poly_mul a m1 in
      let s3 = poly_mul a m4 in
      let rhs = poly_mul (poly_mul a an1) (poly_mul b bn1) in
      poly_eq_transitivity lhs s1 s2;
      poly_eq_transitivity lhs s2 s3;
      poly_eq_transitivity lhs s3 rhs
    end
#pop-options

(* powered_product_aux distributes over snoc *)
#push-options "--z3rlimit 60 --fuel 3 --ifuel 2"
let rec powered_product_aux_snoc (#t:Type) {| cr: commutative_ring t |}
  (xs: list (polynomial t)) (y: polynomial t) (s: pos)
  : Lemma (ensures poly_eq (powered_product_aux (L.append xs [y]) s)
                           (poly_mul (powered_product_aux xs s)
                                     (poly_power y (Prims.op_Addition s (L.length xs)))))
          (decreases xs)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    match xs with
    | [] ->
        (* LHS = pp_aux [y] s = poly_mul (poly_power y s) poly_one
           RHS = poly_mul poly_one (poly_power y s)
           Both ≈ poly_power y s *)
        poly_mul_one (poly_power y s);
        poly_mul_commutativity (poly_one #t) (poly_power y s);
        poly_eq_transitivity
          (poly_mul (poly_power y s) (poly_one #t))
          (poly_power y s)
          (poly_mul (poly_one #t) (poly_power y s));
        poly_eq_symmetry
          (poly_mul (poly_power y s) (poly_one #t))
          (poly_mul (poly_one #t) (poly_power y s))
    | a :: rest ->
        (* LHS = poly_mul (poly_power a s) (pp_aux(append rest [y], s+1))
           IH: pp_aux(append rest [y], s+1) ≈ pp_aux(rest, s+1) · poly_power y (s+1+|rest|)
           RHS = poly_mul (poly_mul (poly_power a s) (pp_aux rest (s+1))) (poly_power y (s+1+|rest|))
           Chain via assoc *)
        let s1 : pos = Prims.op_Addition s 1 in
        powered_product_aux_snoc rest y s1;
        let pas = poly_power a s in
        let pp_rest = powered_product_aux rest s1 in
        let py = poly_power y (Prims.op_Addition s1 (L.length rest)) in
        poly_mul_right_congruence pas
          (powered_product_aux (L.append rest [y]) s1)
          (poly_mul pp_rest py);
        poly_mul_associativity pas pp_rest py;
        poly_eq_symmetry (poly_mul (poly_mul pas pp_rest) py)
                         (poly_mul pas (poly_mul pp_rest py));
        poly_eq_transitivity
          (poly_mul pas (powered_product_aux (L.append rest [y]) s1))
          (poly_mul pas (poly_mul pp_rest py))
          (poly_mul (poly_mul pas pp_rest) py)
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
  : Lemma (requires coprime #t #f a b /\ coprime #t #f a c /\ Some? (poly_deg a))
          (ensures  coprime #t #f a (poly_mul b c))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    coprime_reveal #t #f a (poly_mul b c);
    let g = poly_gcd #t #f a (poly_mul b c) in
    gcd_has_degree #t #f a (poly_mul b c);
    gcd_divides_left #t #f a (poly_mul b c);
    gcd_divides_right #t #f a (poly_mul b c);
    (* g | a and coprime(a, b): coprime(g, b) *)
    coprime_divisor a b g;
    (* g | b·c, need g | c·b for euclid_lemma g b c *)
    poly_mul_commutativity b c;
    divides_congruence_right #(polynomial t) #cr_p g (poly_mul b c) (poly_mul c b);
    (* euclid_lemma g b c: coprime(g,b) ∧ g|(c·b) ⟹ g|c *)
    euclid_lemma #t #f g b c;
    (* g | a and g | c → g | gcd(a, c) *)
    gcd_is_maximal #t #f a c g;
    (* coprime(a, c) → deg(gcd(a, c)) = 0, so deg(g) ≤ 0 *)
    coprime_reveal #t #f a c;
    divides_degree_le g (poly_gcd #t #f a c)
#pop-options

(* coprime(a, b) → coprime(a, b^n) for all n ≥ 1
   Base: n=1, bridge via gcd_congruence (poly_power b 1 ≈ b).
   Step: coprime(a, b) ∧ coprime(a, b^(n-1)) → coprime(a, b · b^(n-1)) = coprime(a, b^n). *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec coprime_power_right (#t:Type) {| f: field t |}
  (a b: polynomial t) (n: pos)
  : Lemma (requires coprime #t #f a b /\ Some? (poly_deg a))
          (ensures  coprime #t #f a (poly_power b n))
          (decreases n)
  = if n = 1 then begin
      (* poly_power b 1 == poly_mul b poly_one ≈ b via poly_mul_one *)
      coprime_reveal #t #f a (poly_power b n);
      coprime_reveal #t #f a b;
      poly_mul_one b;
      (* poly_eq (poly_power b 1) b — direct from poly_mul_one *)
      poly_eq_reflexivity a;
      (* gcd_congruence: poly_eq a a ∧ poly_eq (poly_power b 1) b
         → poly_eq (gcd a (poly_power b 1)) (gcd a b) *)
      gcd_congruence #t #f a a (poly_power b 1) b;
      degree_well_defined (poly_gcd #t #f a (poly_power b 1)) (poly_gcd #t #f a b)
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
  : Lemma (requires coprime #t #f a b /\ Some? (poly_deg a) /\ Some? (poly_deg b))
          (ensures  coprime #t #f (poly_power a m) (poly_power b n))
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
  : Lemma (requires coprime #t #f d1 d2 /\ divides d1 x /\ divides d2 x /\
                    Some? (poly_deg d1))
          (ensures  divides (poly_mul d1 d2) x)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* d2 | x means ∃ s. poly_eq x (poly_mul d2 s) *)
    eliminate exists (s: polynomial t). poly_eq x (poly_mul d2 s)
    returns divides (poly_mul d1 d2) x
    with _.
    begin
      (* d1 | x ≈ d2·s, so d1 | d2·s *)
      poly_eq_symmetry x (poly_mul d2 s);
      divides_congruence_right #(polynomial t) #cr_p d1 x (poly_mul d2 s);
      (* For euclid_lemma: need d1 | s·d2. Comm: d2·s ≈ s·d2 *)
      poly_mul_commutativity d2 s;
      divides_congruence_right #(polynomial t) #cr_p d1 (poly_mul d2 s) (poly_mul s d2);
      (* euclid_lemma d1 d2 s: coprime(d1, d2) ∧ d1|(s·d2) → d1|s *)
      euclid_lemma #t #f d1 d2 s;
      (* d1 | s means ∃ t. poly_eq s (poly_mul d1 t) *)
      eliminate exists (u: polynomial t). poly_eq s (poly_mul d1 u)
      returns divides (poly_mul d1 d2) x
      with _.
      begin
        (* x ≈ d2·s ≈ d2·(d1·u) ≈ (d2·d1)·u ≈ (d1·d2)·u *)
        poly_mul_right_congruence d2 s (poly_mul d1 u);
        poly_mul_associativity d2 d1 u;
        poly_eq_symmetry (poly_mul (poly_mul d2 d1) u) (poly_mul d2 (poly_mul d1 u));
        poly_eq_transitivity (poly_mul d2 s) (poly_mul d2 (poly_mul d1 u))
                             (poly_mul (poly_mul d2 d1) u);
        poly_mul_commutativity d2 d1;
        poly_mul_left_congruence (poly_mul d2 d1) (poly_mul d1 d2) u;
        poly_eq_transitivity (poly_mul d2 s) (poly_mul (poly_mul d2 d1) u)
                             (poly_mul (poly_mul d1 d2) u);
        poly_eq_symmetry x (poly_mul d2 s);
        poly_eq_transitivity x (poly_mul d2 s) (poly_mul (poly_mul d1 d2) u);
        poly_eq_symmetry x (poly_mul (poly_mul d1 d2) u);
        divides_intro #(polynomial t) #cr_p (poly_mul d1 d2) x u
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
  : Lemma (requires Some? (poly_deg a) /\
                    (forall (k:nat). k < L.length ds ==> coprime #t #f a (L.index ds k)))
          (ensures  coprime #t #f a (flat_product ds))
          (decreases ds)
  = match ds with
    | [] ->
        (* flat_product [] = poly_one. coprime(a, poly_one)? Yes: gcd(a, 1) has deg 0. *)
        coprime_reveal #t #f a (poly_one #t);
        gcd_has_degree #t #f a (poly_one #t);
        gcd_divides_right #t #f a (poly_one #t);
        (* gcd | poly_one, and gcd has Some? deg. poly_one has deg 0. *)
        divides_degree_le (poly_gcd #t #f a (poly_one #t)) (poly_one #t)
    | d :: rest ->
        (* flat_product (d::rest) = poly_mul d (flat_product rest) *)
        assert (coprime #t #f a d);
        (* index shifting: index (d::rest) (k+1) = index rest k *)
        assert (forall (k:nat). k < L.length rest ==>
                  L.index (d :: rest) (Prims.op_Addition k 1) == L.index rest k);
        assert (forall (k:nat). k < L.length rest ==>
                  coprime #t #f a (L.index rest k));
        coprime_flat_product a rest;
        coprime_mul_right a d (flat_product rest)
#pop-options

(* Main n-ary theorem: if dᵢ | x for all i, and the dᵢ are pairwise coprime,
   then flat_product(ds) | x. *)
#push-options "--z3rlimit 80 --fuel 4 --ifuel 3"
let rec pairwise_coprime_divides (#t:Type) {| f: field t |}
  (ds: list (polynomial t)) (x: polynomial t)
  : Lemma (requires (forall (k:nat). k < L.length ds ==> divides (L.index ds k) x) /\
                    (forall (k:nat). k < L.length ds ==> Some? (poly_deg (L.index ds k))) /\
                    (forall (i j:nat). i < L.length ds /\ j < L.length ds /\ i <> j ==>
                      coprime #t #f (L.index ds i) (L.index ds j)))
          (ensures  divides (flat_product ds) x)
          (decreases ds)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    match ds with
    | [] ->
        one_divides_all #t #f x
    | [d] ->
        (* flat_product [d] = poly_mul d poly_one. divides d x. Bridge. *)
        assert (divides d x);
        poly_mul_one d;
        poly_eq_symmetry (poly_mul d (poly_one #t)) d;
        (* poly_eq d (poly_mul d (poly_one #t)). Use divides_congruence_left d (flat_product[d]) x *)
        divides_congruence_left #(polynomial t) #cr_p d (poly_mul d (poly_one #t)) x
    | d :: rest ->
        (* Shift quantifiers for rest *)
        assert (forall (k:nat). k < L.length rest ==>
                  L.index rest k == L.index (d :: rest) (Prims.op_Addition k 1));
        assert (forall (k:nat). k < L.length rest ==> divides (L.index rest k) x);
        assert (forall (k:nat). k < L.length rest ==> Some? (poly_deg (L.index rest k)));
        assert (forall (i j:nat). i < L.length rest /\ j < L.length rest /\ i <> j ==>
                  coprime #t #f (L.index rest i) (L.index rest j));
        (* IH: flat_product(rest) | x *)
        pairwise_coprime_divides rest x;
        (* d | x *)
        assert (divides d x);
        assert (Some? (poly_deg d));
        (* coprime(d, each element of rest): from pairwise on ds at i=0, j=k+1 *)
        assert (forall (k:nat). k < L.length rest ==>
                  coprime #t #f (L.index (d :: rest) 0) (L.index (d :: rest) (Prims.op_Addition k 1)));
        assert (forall (k:nat). k < L.length rest ==> coprime #t #f d (L.index rest k));
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
                           (poly_deriv (poly_mul (poly_power q k) r)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let qk = poly_power q k in
    let qk1 = poly_power q (k - 1) in
    let dqk = poly_deriv qk in
    let dr = poly_deriv r in
    let sum1 = poly_mul dqk r in
    let sum2 = poly_mul qk dr in
    (* Product rule: D(q^k · r) ≈ D(q^k)·r + q^k·D(r) *)
    poly_deriv_mul qk r;
    (* Summand 1: q^(k-1) | D(q^k)·r *)
    deriv_power_divisibility q k;
    divides_mul_right #(polynomial t) #cr_p qk1 dqk r;
    (* Summand 2: q^(k-1) | q^k·D(r).
       First establish q^(k-1) | q^k: q^k = q · q^(k-1) definitionally,
       and poly_mul q qk1 = poly_mul qk1 q by commutativity *)
    poly_mul_commutativity q qk1;
    divides_intro #(polynomial t) #cr_p qk1 qk q;
    divides_mul_right #(polynomial t) #cr_p qk1 qk dr;
    (* Combine: q^(k-1) | sum1 + sum2 *)
    divides_add #(polynomial t) #cr_p qk1 sum1 sum2;
    (* Transfer via congruence: D(q^k·r) ≈ sum1 + sum2 *)
    poly_eq_symmetry (poly_deriv (poly_mul qk r)) (poly_add sum1 sum2);
    divides_congruence_right #(polynomial t) #cr_p qk1
      (poly_add sum1 sum2) (poly_deriv (poly_mul qk r))
#pop-options

(* Consequence: q^(k-1) | gcd(q^k · r, D(q^k · r))
   Proof: q^(k-1) divides both the product and its derivative,
   hence divides their GCD by maximality. *)
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let power_factor_divides_gcd (#t:Type) {| f: field t |}
  (q r: polynomial t) (k: pos)
  : Lemma (ensures divides (poly_power q (k - 1))
                           (poly_gcd #t #f (poly_mul (poly_power q k) r)
                                           (poly_deriv (poly_mul (poly_power q k) r))))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    let p = poly_mul (poly_power q k) r in
    let dp = poly_deriv p in
    let qk1 = poly_power q (k - 1) in
    (* q^(k-1) | p: q^k = q·q^(k-1), so q^(k-1) | q^k, hence q^(k-1) | q^k·r = p *)
    poly_mul_commutativity q qk1;
    divides_intro #(polynomial t) #cr_p qk1 (poly_power q k) q;
    divides_mul_right #(polynomial t) #cr_p qk1 (poly_power q k) r;
    (* q^(k-1) | D(p) *)
    power_factor_divides_deriv_product #t #f q r k;
    (* q^(k-1) divides both p and D(p), so it divides their gcd *)
    gcd_is_maximal #t #f p dp qk1
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
  : Lemma (requires poly_eq p (poly_mul (poly_power q k) r))
          (ensures  divides (poly_power q (k - 1))
                            (poly_gcd #t #f p (poly_deriv p)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let qkr = poly_mul (poly_power q k) r in
    (* gcd(q^k·r, D(q^k·r)) has q^(k-1) as a divisor *)
    power_factor_divides_gcd q r k;
    (* D(p) ≈ D(q^k·r) via congruence *)
    poly_deriv_congruence p qkr;
    (* gcd(p, D(p)) ≈ gcd(q^k·r, D(q^k·r)) via gcd_congruence *)
    poly_eq_symmetry p qkr;
    poly_eq_symmetry (poly_deriv p) (poly_deriv qkr);
    gcd_congruence #t #f qkr p (poly_deriv qkr) (poly_deriv p);
    (* Transfer divisibility via congruence *)
    divides_congruence_right #(polynomial t) #cr_p (poly_power q (k - 1))
      (poly_gcd #t #f qkr (poly_deriv qkr))
      (poly_gcd #t #f p (poly_deriv p))
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
  : Lemma (ensures poly_eq (poly_mul (poly_mul a b) (poly_mul c d))
                           (poly_mul (poly_mul a c) (poly_mul b d)))
  = (* (a·b)·(c·d) ≈ a·(b·(c·d)) *)
    poly_mul_associativity a b (poly_mul c d);
    (* b·(c·d) ≈ (b·c)·d *)
    poly_mul_associativity b c d;
    poly_eq_symmetry (poly_mul (poly_mul b c) d) (poly_mul b (poly_mul c d));
    (* (b·c) ≈ (c·b) *)
    poly_mul_commutativity b c;
    (* (b·c)·d ≈ (c·b)·d *)
    poly_mul_left_congruence (poly_mul b c) (poly_mul c b) d;
    (* (c·b)·d ≈ c·(b·d) *)
    poly_mul_associativity c b d;
    (* chain: b·(c·d) ≈ (b·c)·d ≈ (c·b)·d ≈ c·(b·d) *)
    poly_eq_transitivity (poly_mul b (poly_mul c d))
                         (poly_mul (poly_mul b c) d)
                         (poly_mul (poly_mul c b) d);
    poly_eq_transitivity (poly_mul b (poly_mul c d))
                         (poly_mul (poly_mul c b) d)
                         (poly_mul c (poly_mul b d));
    (* lift: a·(b·(c·d)) ≈ a·(c·(b·d)) *)
    poly_mul_right_congruence a (poly_mul b (poly_mul c d))
                                (poly_mul c (poly_mul b d));
    (* a·(c·(b·d)) ≈ (a·c)·(b·d) *)
    poly_mul_associativity a c (poly_mul b d);
    poly_eq_symmetry (poly_mul (poly_mul a c) (poly_mul b d))
                     (poly_mul a (poly_mul c (poly_mul b d)));
    (* full chain: (a·b)·(c·d) ≈ a·(b·(c·d)) ≈ a·(c·(b·d)) ≈ (a·c)·(b·d) *)
    poly_eq_transitivity (poly_mul (poly_mul a b) (poly_mul c d))
                         (poly_mul a (poly_mul b (poly_mul c d)))
                         (poly_mul a (poly_mul c (poly_mul b d)));
    poly_eq_transitivity (poly_mul (poly_mul a b) (poly_mul c d))
                         (poly_mul a (poly_mul c (poly_mul b d)))
                         (poly_mul (poly_mul a c) (poly_mul b d))
#pop-options

(* Main PP shift: powered_product_aux xs (s+1) ≈ flat_product(xs) · powered_product_aux xs s *)
#push-options "--z3rlimit 60 --fuel 4 --ifuel 2"
let rec pp_shift (#t:Type) {| f: field t |}
  (xs: list (polynomial t)) (s: pos)
  : Lemma (ensures poly_eq (powered_product_aux xs (Prims.op_Addition s 1))
                           (poly_mul (flat_product xs) (powered_product_aux xs s)))
          (decreases xs)
  = let cr : commutative_ring t = TC.solve in
    match xs with
    | [] ->
        (* PP([], s+1) = poly_one. flat_product([]) · PP([], s) = poly_one · poly_one ≈ poly_one *)
        poly_mul_one (poly_one #t);
        poly_eq_symmetry (poly_mul (poly_one #t) (poly_one #t)) (poly_one #t)
    | x :: rest ->
        let s1 = Prims.op_Addition s 1 in
        let s2 = Prims.op_Addition s 2 in
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
                                  (poly_mul fp_rest pp_rest_s1);
        (* Now: PP(x::rest, s+1) ≈ poly_mul (poly_power x s1) (poly_mul fp_rest pp_rest_s1) *)
        (* Step 2: poly_power x (s+1) == poly_mul x (poly_power x s) [definitional] *)
        poly_eq_reflexivity (poly_mul x xps);
        poly_mul_left_congruence (poly_power x s1) (poly_mul x xps)
                                 (poly_mul fp_rest pp_rest_s1);
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
        let t1 = poly_mul (poly_power x s1) pp_rest_s2 in
        let t2 = poly_mul (poly_power x s1) (poly_mul fp_rest pp_rest_s1) in
        let t3 = poly_mul (poly_mul x xps) (poly_mul fp_rest pp_rest_s1) in
        let t4 = poly_mul (poly_mul x fp_rest) (poly_mul xps pp_rest_s1) in
        poly_eq_reflexivity t0;
        poly_eq_transitivity t0 t2 t3;
        poly_eq_transitivity t0 t3 t4
#pop-options

(* Corollary: PP(x :: rest, 1) ≈ flat_product(x :: rest) · PP(rest, 1)
   i.e., PP(factors, 1) ≈ flat_product(factors) · PP(tail, 1) *)
#push-options "--z3rlimit 60 --fuel 4 --ifuel 2"
let pp_split_head (#t:Type) {| f: field t |}
  (x: polynomial t) (rest: list (polynomial t))
  : Lemma (ensures poly_eq (powered_product_aux (x :: rest) 1)
                           (poly_mul (flat_product (x :: rest))
                                     (powered_product_aux rest 1)))
  = let cr : commutative_ring t = TC.solve in
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
    poly_mul_left_congruence (poly_mul x (poly_one #t)) x pp_rest_2;
    (* Step 4: substitute pp_shift: poly_mul x pp_rest_2 ≈ poly_mul x (poly_mul fp_rest pp_rest_1) *)
    poly_mul_right_congruence x pp_rest_2 (poly_mul fp_rest pp_rest_1);
    (* Step 5: associativity: poly_mul x (poly_mul fp_rest pp_rest_1) ≈ poly_mul (poly_mul x fp_rest) pp_rest_1 *)
    poly_mul_associativity x fp_rest pp_rest_1;
    poly_eq_symmetry (poly_mul (poly_mul x fp_rest) pp_rest_1)
                     (poly_mul x (poly_mul fp_rest pp_rest_1));
    (* Chain everything *)
    let t0 = powered_product_aux (x :: rest) 1 in
    let t1 = poly_mul (poly_mul x (poly_one #t)) pp_rest_2 in
    let t2 = poly_mul x pp_rest_2 in
    let t3 = poly_mul x (poly_mul fp_rest pp_rest_1) in
    let t4 = poly_mul (poly_mul x fp_rest) pp_rest_1 in
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
                    Some? (poly_deg d) /\ Some? (poly_deg p) /\
                    Some?.v (poly_deg d) == Some?.v (poly_deg p))
          (ensures  (let cr_p : commutative_ring (polynomial t) = TC.solve in
                     exists (c: polynomial t).
                       poly_eq p (poly_mul d c) /\
                       poly_deg c == Some 0))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let aux (c: polynomial t)
      : Lemma (requires poly_eq p (poly_mul d c))
              (ensures  poly_deg c == Some 0)
      = match poly_deg c with
        | None ->
            (* c ≈ zero → d·c ≈ zero → p ≈ zero. But Some?(deg p). Contradiction. *)
            assert (c == (poly_zero #t));
            H.x_mul_zero #(polynomial t) d;
            poly_eq_symmetry (poly_mul d c) (poly_zero #t);
            poly_eq_transitivity p (poly_mul d c) (poly_zero #t);
            degree_well_defined p (poly_zero #t)
        | Some dc ->
            (* deg(d·c) = deg(d) + deg(c). poly_eq p (d·c) → deg(p) = deg(d) + deg(c). *)
            degree_mul #t #(id_of_f t) d c;
            degree_well_defined p (poly_mul d c)
            (* Now: Some?.v (poly_deg p) == Some?.v (poly_deg d) + dc.
               But Some?.v (poly_deg p) == Some?.v (poly_deg d).
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
  : Lemma (requires (forall (k:nat). k < L.length xs ==> Some? (poly_deg (L.index xs k))))
          (ensures  Some? (poly_deg (powered_product_aux xs s)))
          (decreases xs)
  = match xs with
    | [] -> ()  (* poly_one has degree Some 0 *)
    | x :: rest ->
        assert (Some? (poly_deg x));
        assert (forall (k:nat). k < L.length rest ==>
                  L.index rest k == L.index (x :: rest) (Prims.op_Addition k 1));
        assert (forall (k:nat). k < L.length rest ==> Some? (poly_deg (L.index rest k)));
        poly_power_degree_exact x s;
        pp_has_degree rest (Prims.op_Addition s 1);
        degree_mul #t #(id_of_f t) (poly_power x s) (powered_product_aux rest (Prims.op_Addition s 1))
#pop-options

(* ================================================================ *)
(*  poly_div preserves Some? degree                                *)
(* ================================================================ *)

let poly_div_has_degree (#t:Type) {| f: field t |}
  (p d: polynomial t)
  : Lemma (requires Some? (poly_deg d) /\ Some? (poly_deg p) /\ divides d p)
          (ensures  Some? (poly_deg (poly_div p d)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    poly_div_correct p d;
    let q = poly_div p d in
    match poly_deg q with
    | Some _ -> ()
    | None ->
        degree_none_poly_eq_zero q;
        poly_eq_reflexivity d;
        poly_mul_congruence d q d (poly_zero #t);
        H.x_mul_zero #(polynomial t) d;
        poly_eq_transitivity (poly_mul d q) (poly_mul d (poly_zero #t)) (poly_zero #t);
        poly_eq_symmetry (poly_mul d q) p;
        poly_eq_transitivity (poly_zero #t) (poly_mul d q) p;
        poly_eq_symmetry (poly_zero #t) p;
        degree_well_defined p (poly_zero #t)

(* ================================================================ *)
(*  poly_div degree formula                                        *)
(* ================================================================ *)

let poly_div_degree (#t:Type) {| f: field t |}
  (p d: polynomial t)
  : Lemma (requires Some? (poly_deg d) /\ Some? (poly_deg p) /\ divides d p)
          (ensures  Some? (poly_deg (poly_div p d)) /\
                    Some?.v (poly_deg (poly_div p d)) ==
                    Some?.v (poly_deg p) - Some?.v (poly_deg d))
  = poly_div_has_degree p d;
    poly_div_correct p d;
    let q = poly_div p d in
    degree_mul #t #(id_of_f t) d q;
    poly_eq_symmetry (poly_mul d q) p;
    degree_well_defined p (poly_mul d q)

(* ================================================================ *)
(*  Irreducible ⟹ coprime or divides                               *)
(*                                                                  *)
(*  For an irreducible q: for any r with Some? degree, either       *)
(*  coprime(q, r) or q | r.                                         *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 4 --ifuel 3"
let irreducible_coprime_or_divides (#t:Type) {| f: field t |}
  (q r: polynomial t)
  : Lemma (requires poly_irreducible q /\ Some? (poly_deg r))
          (ensures  coprime q r \/ divides q r)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let g = poly_gcd #t #f q r in
    gcd_has_degree q r;
    gcd_divides_left q r;
    gcd_divides_right q r;
    coprime_reveal q r;
    if poly_deg g = Some 0 then ()
    else begin
      (* deg(g) ≥ 1. Show q | r via Euclid's lemma. *)
      let combined (h d: polynomial t)
        : Lemma (requires poly_eq q (poly_mul g h) /\ poly_eq r (poly_mul g d))
                (ensures  divides q r)
        = (* From irreducibility: deg(h) = 0 or None *)
          assert (poly_eq q (poly_mul g h) == true);
          assert (poly_deg g == Some 0 \/ poly_deg g == None \/
                  poly_deg h == Some 0 \/ poly_deg h == None);
          assert (poly_deg h == Some 0 \/ poly_deg h == None);
          (* Eliminate None: h ≈ 0 → q ≈ 0. Contradiction. *)
          (if None? (poly_deg h) then (
            degree_none_poly_eq_zero h;
            poly_eq_reflexivity g;
            poly_mul_congruence g h g (poly_zero #t);
            H.x_mul_zero #(polynomial t) g;
            poly_eq_transitivity (poly_mul g h) (poly_mul g (poly_zero #t)) (poly_zero #t);
            poly_eq_transitivity q (poly_mul g h) (poly_zero #t);
            degree_well_defined q (poly_zero #t)
          ) else ());
          assert (poly_deg h == Some 0);
          (* coprime(q, h): gcd(q,h) | h with deg(h) = 0,
             so deg(gcd(q,h)) ≤ 0 = Some 0. *)
          gcd_has_degree q h;
          gcd_divides_right q h;
          divides_degree_le (poly_gcd #t #f q h) h;
          coprime_reveal q h;
          assert (coprime q h);
          (* Show q | (r·h) via ring chain:
             r·h ≈ (g·d)·h ≈ g·(d·h) ≈ g·(h·d) ≈ (g·h)·d ≈ q·d *)
          poly_mul_left_congruence r (poly_mul g d) h;
          poly_mul_associativity g d h;
          poly_eq_symmetry (poly_mul (poly_mul g d) h)
                           (poly_mul g (poly_mul d h));
          poly_mul_commutativity d h;
          poly_mul_right_congruence g (poly_mul d h) (poly_mul h d);
          poly_mul_associativity g h d;
          poly_eq_symmetry q (poly_mul g h);
          poly_mul_left_congruence (poly_mul g h) q d;
          let rh = poly_mul r h in
          let gdh = poly_mul (poly_mul g d) h in
          let g_dh = poly_mul g (poly_mul d h) in
          let g_hd = poly_mul g (poly_mul h d) in
          let ghd = poly_mul (poly_mul g h) d in
          let qd = poly_mul q d in
          poly_eq_transitivity rh gdh g_dh;
          poly_eq_transitivity rh g_dh g_hd;
          poly_eq_transitivity rh g_hd ghd;
          poly_eq_transitivity rh ghd qd;
          poly_eq_symmetry rh qd;
          divides_intro #(polynomial t) #cr_p q rh d;
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
  : Lemma (requires poly_irreducible q /\ divides q p /\ Some? (poly_deg p))
          (ensures  exists (e: pos) (r: polynomial t).
            poly_eq p (poly_mul (poly_power q e) r) /\
            coprime q r /\
            Some? (poly_deg r))
          (decreases (if Some? (poly_deg p) then Some?.v (poly_deg p) else 0))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    poly_div_correct p q;
    poly_div_has_degree p q;
    poly_div_degree p q;
    let p1 = poly_div p q in
    poly_eq_symmetry (poly_mul q p1) p;
    assert (Some?.v (poly_deg p1) < Some?.v (poly_deg p));
    irreducible_coprime_or_divides q p1;
    if coprime q p1 then begin
      (* Base: e = 1, r = p1. poly_power q 1 = q. *)
      poly_mul_one q;
      poly_eq_symmetry (poly_mul q (poly_one #t)) q;
      assert (poly_eq (poly_power q 1) q);
      poly_mul_left_congruence q (poly_power q 1) p1;
      poly_eq_symmetry (poly_mul q p1) (poly_mul (poly_power q 1) p1);
      poly_eq_transitivity p (poly_mul q p1) (poly_mul (poly_power q 1) p1)
    end else begin
      (* Inductive: q | p1, recurse *)
      assert (divides q p1);
      factor_out_irreducible q p1;
      let chain (e': pos) (r': polynomial t)
        : Lemma (requires poly_eq p1 (poly_mul (poly_power q e') r') /\
                          coprime q r' /\ Some? (poly_deg r'))
                (ensures  exists (e: pos) (r: polynomial t).
                  poly_eq p (poly_mul (poly_power q e) r) /\
                  coprime q r /\ Some? (poly_deg r))
        = let e = Prims.op_Addition e' 1 in
          (* q · (q^e' · r') ≈ (q · q^e') · r' by associativity *)
          poly_mul_right_congruence q p1 (poly_mul (poly_power q e') r');
          poly_mul_associativity q (poly_power q e') r';
          poly_eq_symmetry (poly_mul (poly_mul q (poly_power q e')) r')
                           (poly_mul q (poly_mul (poly_power q e') r'));
          poly_eq_transitivity (poly_mul q p1)
                               (poly_mul q (poly_mul (poly_power q e') r'))
                               (poly_mul (poly_mul q (poly_power q e')) r');
          (* poly_power q e == poly_mul q (poly_power q e') *)
          poly_eq_reflexivity (poly_mul q (poly_power q e'));
          assert (poly_power q e == poly_mul q (poly_power q e'));
          poly_mul_left_congruence (poly_mul q (poly_power q e'))
                                  (poly_power q e) r';
          poly_eq_transitivity (poly_mul (poly_mul q (poly_power q e')) r')
                               (poly_mul (poly_power q e) r')
                               (poly_mul (poly_power q e) r');
          poly_eq_transitivity (poly_mul q p1)
                               (poly_mul (poly_mul q (poly_power q e')) r')
                               (poly_mul (poly_power q e) r');
          poly_eq_transitivity p (poly_mul q p1) (poly_mul (poly_power q e) r')
      in
      Classical.forall_intro_2 (Classical.move_requires_2 chain)
    end
#pop-options

(* ================================================================ *)
(*  Composition: irreducible q | p → q^(e-1) | gcd(p, D(p))        *)
(* ================================================================ *)

let irred_factor_gcd_valuation (#t:Type) {| f: field t |}
  (q p: polynomial t)
  : Lemma (requires poly_irreducible q /\ divides q p /\ Some? (poly_deg p))
          (ensures  exists (e: pos).
            divides (poly_power q (e - 1))
                    (poly_gcd #t #f p (poly_deriv p)))
  = factor_out_irreducible q p;
    let aux (e: pos) (r: polynomial t)
      : Lemma (requires poly_eq p (poly_mul (poly_power q e) r) /\
                        coprime q r /\ Some? (poly_deg r))
              (ensures  exists (e: pos).
                divides (poly_power q (e - 1))
                        (poly_gcd #t #f p (poly_deriv p)))
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
                    Some? (poly_deg r))
          (ensures  coprime q q2)
  = coprime_symmetric q r;
    coprime_divisor r q q2;
    coprime_symmetric q2 q
