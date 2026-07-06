module Core.Polynomial.Factorization

(*
   Yun's algorithm: factorization correctness.

   Main theorem: `yun_associates` — the powered product of Yun's square-free
   factorization output is associate to the input polynomial (mutual
   divisibility). Zero admits; fully verified.
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
open Core.Polynomial.Irreducible
open Core.Tactics.CanonRing

(* ===== merged from Core.Polynomial.PPInvariant - Yun PP-invariant (impl detail) ===== *)

(* poly_power_congruence (a ≈ b ⟹ a^n ≈ b^n) lives next to poly_power in
   Core.Polynomial.SquareFree — it is a general poly_power fact, not Yun-specific. *)

(* ================================================================ *)
(*  Ghost b-product: tracks product of intermediate b values        *)
(*                                                                  *)
(*  yun_loop_b_product(b, d, fuel) = b₁ · b₂ · ... · bₙ             *)
(*  where bₖ = bₖ₋₁ / gcd(bₖ₋₁, dₖ₋₁).                                *)
(* ================================================================ *)

private let rec yun_loop_b_product (#t:Type) {| f: field t |}
  (b d: polynomial t) (fuel: nat)
  : Tot (polynomial t) (decreases fuel)
  = if fuel = 0 then poly_one
    else if deg b < 0 then poly_one
    else if deg b = 0 then poly_one
    else
      let a = poly_gcd b d in
      let b' = poly_div b a in
      let c' = poly_div d a in
      let d' : polynomial t = (c' -- poly_deriv b') in
      b' * yun_loop_b_product b' d' (fuel - 1)

(* ================================================================ *)
(*  PP loop invariant:                                               *)
(*                                                                  *)
(*  PP(output) ≈ PP(acc) · b^(|acc|+1) · b_product(b, d, fuel)     *)
(*                                                                  *)
(*  At the top level (acc = []):                                    *)
(*  PP(yun(p)) ≈ 1 · b₀ · b_product = b₀ · b_product              *)
(*                                                                  *)
(*  Key algebraic step in the inductive case:                       *)
(*  We need: PP(acc) · b^n · (b' · R)                              *)
(*         ≈ PP(acc') · b'^(n+1) · R                               *)
(*  Using b ≈ a · b' and PP(acc') ≈ PP(acc) · a^n.                 *)
(* ================================================================ *)

(* Helper: five-factor rearrangement
   (P · (A · B)) · (b' · R) ≈ ((P · A) · (b' · B)) · R
   This swaps B and b' in a product of five factors. *)
(* Pure ring identity over t: (p*(a*b))*(b'*r) = ((p*a)*(b'*b))*r.
   Concrete commutative-ring rearrangement → canon_ring. *)
private let five_factor_rearrange (#t:Type) {| commutative_ring t |}
  (a b c x y: t)
  : Lemma ((a * (b * c)) * (x * y) = ((a * b) * (x * c)) * y)
  = assert ((a * (b * c)) * (x * y) = ((a * b) * (x * c)) * y)
      by canon_ring ()

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private let rec yun_loop_pp_invariant (#t:Type) {| f: field t |}
  (b d: polynomial t) (acc: list (polynomial t)) (fuel: nat)
  : Lemma (ensures
      (powered_product_aux (yun_loop b d acc fuel) 1)
      = (((powered_product_aux acc 1)
            * (poly_power b ((L.length acc) ++ 1)))
                * (yun_loop_b_product b d fuel)))
    (decreases fuel)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let n : pos = (L.length acc) ++ 1 in
    let pp_acc = powered_product_aux acc 1 in
    let bp = poly_power b n in
    if fuel = 0 || deg b < 0 || deg b = 0 then begin
      (* Base case: output = acc ++ [b], b_product = poly_one *)
      powered_product_aux_snoc acc b 1;
      let lhs = pp_acc * bp in
      H.x_mul_one lhs
    end
    else begin
      let a = poly_gcd b d in
      let b' = poly_div b a in
      let c' = poly_div d a in
      let d' : polynomial t = (c' -- (poly_deriv b')) in
      let acc' = L.append acc [a] in
      L.append_length acc [a];
      let n' : pos = (L.length acc) ++ 2 in
      assert (L.length acc' == (L.length acc) ++ 1);
      assert ((L.length acc') ++ 1 == n');

      (* IH *)
      yun_loop_pp_invariant b' d' acc' (fuel - 1);
      let pp_acc' = powered_product_aux acc' 1 in
      let bpn = poly_power b' n in   (* b'^n, NOT b'^n' *)
      let bp' = poly_power b' n' in  (* b'^n' *)
      let bp'_prod = yun_loop_b_product b' d' (fuel - 1) in
      let output = yun_loop b d acc fuel in

      (* From IH: PP(output) ≈ (pp_acc' · bp') · bp'_prod *)
      (* We want: PP(output) ≈ (pp_acc · bp) · (b' · bp'_prod) *)

      (* Fact 1: pp_acc' ≈ pp_acc · a^n *)
      powered_product_aux_snoc acc a 1;
      let apn = poly_power a n in

      (* Fact 2: b ≈ a · b' *)
      gcd_has_degree b d;
      gcd_divides_left b d;
      poly_div_correct b a;

      (* Fact 3: b^n ≈ a^n · b'^n *)
      poly_power_congruence b (a * b') n;
      poly_power_mul a b' n;

      (* Fact 4: bp' = b' · bpn  [definitional, since n' = n+1] *)
      assert (bp' == b' * (poly_power b' (n' - 1)));
      assert (n' - 1 == n);

      (* Now build the chain:
         (pp_acc · bp) · (b' · bp'_prod)
         ≈ (pp_acc · (apn · bpn)) · (b' · bp'_prod)  [Fact 3, congruence]
         ≈ ((pp_acc · apn) · (b' · bpn)) · bp'_prod  [five_factor_rearrange]
         ≈ (pp_acc' · bp') · bp'_prod                 [Fact 1 + Fact 4, congruence]
         ≈ PP(output)                                  [IH]
      *)

      (* Step A: lift Fact 3 into the product *)
      poly_mul_right_congruence pp_acc bp (apn * bpn);
      poly_mul_left_congruence (pp_acc * bp)
                               (pp_acc * (apn * bpn))
                               (b' * bp'_prod);

      (* Step B: five-factor rearrange *)
       
      five_factor_rearrange pp_acc apn bpn b' bp'_prod;

      (* Step C: substitute pp_acc' for pp_acc · apn *)
      poly_mul_left_congruence (pp_acc * apn) pp_acc' (b' * bpn);
      poly_mul_left_congruence ((pp_acc * apn) * (b' * bpn))
                               (pp_acc' * (b' * bpn))
                               bp'_prod
    end
#pop-options

(* ================================================================ *)
(*  Top-level corollary: PP(yun_loop b d [] fuel) ≈ b · b_product   *)
(*                                                                  *)
(*  Specializes the loop invariant to acc = []:                     *)
(*    PP_aux([] , 1) = poly_one                                     *)
(*    poly_power b 1 = b · poly_one ≈ b                            *)
(*  So: PP(output) ≈ poly_one · b^1 · b_product ≈ b · b_product   *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
private let yun_loop_pp_b_product (#t:Type) {| f: field t |}
  (b d: polynomial t) (fuel: nat)
  : Lemma (ensures
      (powered_product (yun_loop b d [] fuel))
      = (b * (yun_loop_b_product b d fuel)))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let bp = yun_loop_b_product b d fuel in
    let one_p : polynomial t = poly_one in
    (* Invoke the loop invariant with acc = [] *)
    yun_loop_pp_invariant b d [] fuel;
    (* PP(output) ≈ (poly_one · poly_power b 1) · bp, and poly_power b 1 == b · poly_one *)
    H.x_mul_one b;
    poly_mul_right_congruence one_p (b * one_p) b;
    H.one_mul_x b;
    poly_mul_left_congruence (one_p * (b * one_p)) b bp
#pop-options

(* ================================================================ *)
(*  1. Cancellation: a*p ≈ a*q and deg(a) >= 0  ==>  p ≈ q          *)
(* ================================================================ *)

(*
   Intended proof shape:

     a*p ≈ a*q
       ==> a*(p-q) ≈ 0

   Since deg a >= 0, the polynomial a is nonzero.  Over a field, the
   polynomial ring is an integral domain, so no-zero-divisors yields p-q ≈ 0,
   hence p ≈ q.  The original proof likely used either a direct integral-domain
   argument or an exact-division / Euclid-lemma style reduction.
*)
#push-options "--z3rlimit 30 --fuel 3 --ifuel 1 --split_queries on_failure"
let poly_mul_left_cancel (#t:Type) {| f: field t |}
  (a p q: polynomial t)
  : Lemma (requires deg a >= 0 /\ ((a * p) = (a * q)))
          (ensures  (p = q))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* Step 1: a * (p - q) ≈ (a*p) - (a*q) *)
    poly_mul_sub_distrib a p q;
    (* Step 2: (a*p) - (a*q) ≈ 0 since a*p ≈ a*q *)
    add_congruence (a * p) (- (a * q))
                   (a * q) (- (a * q));
    add_negation (a * q);
    (* Step 3: a * (p - q) ≈ 0, then domain_law gives a ≈ 0 or (p-q) ≈ 0 *)
    poly_domain_law a (p -- q);
    (* Step 5: a is not zero — if it were, degree_well_defined + poly_zero
       having None degree contradicts deg a >= 0 *)
    assert ((a = (poly_zero #t)) \/ ((p -- q) = (poly_zero #t)));
    (if (a = (poly_zero #t)) then begin
       degree_well_defined a (poly_zero #t);
       assert (deg a == deg (poly_zero #t))
     end);
    (* Step 6: so (p - q) ≈ 0, hence p ≈ q *)
    sub_zero_implies_eq p q
#pop-options

(* ================================================================ *)
(*  2. Ghost alpha tracker for the Yun loop                          *)
(* ================================================================ *)

private let rec yun_loop_alpha (#t:Type) {| f: field t |}
  (alpha b d: polynomial t) (fuel: nat)
  : Tot (polynomial t) (decreases fuel)
  = if fuel = 0 then alpha
    else if deg b < 0 then alpha
    else if deg b = 0 then alpha
    else
      let a = poly_gcd b d in
      let b' = poly_div b a in
      let c' = poly_div d a in
      let d' : polynomial t = (c' -- (poly_deriv b')) in
      let alpha' = poly_div alpha b' in
      yun_loop_alpha alpha' b' d' (fuel - 1)

(* ================================================================ *)
(*  3. coprime(b', d) at a Yun step                                  *)
(* ================================================================ *)

(*
   At a step with

     a  = gcd(b, d)
     b' = b / a

   the intended theorem is that b' is coprime to the old d.  The standard proof
   is: any irreducible q dividing both b' and d also divides b = a*b', hence q
   divides gcd(b,d) = a; now q divides both a and b', contradicting the square-
   free decomposition fact yun_step_coprime for b = a*b'.
*)
#push-options "--z3rlimit 40 --fuel 4 --ifuel 2 --split_queries on_failure"
private let coprime_b_prime_d (#t:Type) {| f: field t |}
  (b d: polynomial t)
  : Lemma (requires char_zero f /\ deg b >= 1 /\
                     square_free b)
          (ensures  (let a = poly_gcd b d in
                     let b' = poly_div b a in
                     coprime b' d))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let a = poly_gcd b d in
    let b' = poly_div b a in
    let c' = poly_div d a in
    (* Establish a has degree *)
    gcd_has_degree b d;
    (* a | b and a | d *)
    gcd_divides_left b d;
    gcd_divides_right b d;
    (* (a * b') ≈ b *)
    poly_div_correct b a;
    (* Establish deg b' >= 0 via contradiction:
       if b' is zero then a*b' ≈ 0, but (a * b') ≈ b and b has degree *)
    (if deg b' >= 0 then () else begin
         degree_none_poly_eq_zero b';
         H.x_mul_zero a;
         poly_eq_transitivity (a * b') (a * (poly_zero #t)) (poly_zero #t);
         poly_eq_transitivity (poly_zero #t) (a * b') b;
         degree_well_defined (poly_zero #t) b end);
    (* (a * c') ≈ d *)
    poly_div_correct d a;
    (* From yun_step_coprime: coprime(a, b') *)
    yun_step_coprime b d;
    (* coprime(b', a) by symmetry *)
    coprime_symmetric a b';
    (* From coprime_quotients: coprime(b', c') *)
    coprime_quotients b d;
    (* coprime_mul_right: coprime(b', a) ∧ coprime(b', c') → coprime(b', a*c') *)
    coprime_mul_right b' a c';
    (* Bridge: a*c' ≈ d, so gcd(b', a*c') ≈ gcd(b', d) *)
    gcd_congruence b' b' (a * c') d;
    (* Transfer coprime via degree_well_defined *)
    coprime_reveal b' (a * c');
    coprime_reveal b' d;
    degree_well_defined (poly_gcd b' (a * c')) (poly_gcd b' d)
#pop-options

(* ================================================================ *)
(*  4. Helper: (X + Y) - Y ≈ X                                        *)
(* ================================================================ *)

(* Pure additive-group identity over t: (x+y)-y = x. *)
private let add_sub_cancel (#t:Type) {| commutative_ring t |}
  (x y: t)
  : Lemma (((x + y) -- y) = x) = assert (((x + y) -- y) = x) by canon_ring ()

(* ================================================================ *)
(*  5. Base-case alpha invariant                                      *)
(* ================================================================ *)

(*
   For the initial Yun state

     a0 = gcd(p, D(p))
     b0 = p / a0
     c0 = D(p) / a0
     d0 = c0 - D(b0)

   the invariant is

     a0 * d0 ≈ D(a0) * b0.

   Starting from p ≈ a0*b0, differentiate and use the product rule:

     D(p) ≈ D(a0)*b0 + a0*D(b0).

   Since D(p) ≈ a0*c0, rearrangement gives

     a0*(c0 - D(b0)) ≈ D(a0)*b0,

   i.e. the desired a0*d0 identity.
*)
#push-options "--z3rlimit 40 --fuel 3 --ifuel 1 --split_queries on_failure"
private let alpha_base_case (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires char_zero f /\ deg p >= 1)
          (ensures  (let p' = poly_deriv p in
                     let a0 = poly_gcd p p' in
                     let b0 = poly_div p a0 in
                     let c0 = poly_div p' a0 in
                     let d0 : polynomial t = (c0 -- (poly_deriv b0)) in
                     ((a0 * d0) = ((poly_deriv a0) * b0))))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let p' = poly_deriv p in
    let a0 = poly_gcd p p' in
    let b0 = poly_div p a0 in
    let c0 = poly_div p' a0 in
    let d0 : polynomial t = (c0 -- (poly_deriv b0)) in
    (* Step 1: a0 has degree, divides p and p' *)
    gcd_has_degree p p';
    gcd_divides_left p p';
    gcd_divides_right p p';
    (* Step 2: a0*b0 ≈ p *)
    poly_div_correct p a0;
    (* Step 3: D(p) ≈ D(a0*b0) ≈ D(a0)*b0 + a0*D(b0) *)
    poly_deriv_congruence p (a0 * b0);
    poly_deriv_mul a0 b0;
    (* Step 4: a0*c0 ≈ p' *)
    poly_div_correct p' a0;
    (* Step 6: poly_add_sub_cancel gives (X + Y) - Y ≈ X *)
    add_sub_cancel (poly_deriv a0 * b0) (a0 * poly_deriv b0);
    (* Step 7: sub-congruence on LHS:
       (a0*c0) -- (a0*D(b0)) ≈ (D(a0)*b0 + a0*D(b0)) -- (a0*D(b0)) ≈ D(a0)*b0 *)
    add_congruence (a0 * c0) (- (a0 * (poly_deriv b0)))
                   (((poly_deriv a0) * b0) + (a0 * (poly_deriv b0)))
                   (- (a0 * (poly_deriv b0)));
    (* Step 8: a0*d0 ≈ a0*(c0 - D(b0)) ≈ a0*c0 - a0*D(b0) via poly_mul_sub_distrib *)
    poly_mul_sub_distrib a0 c0 (poly_deriv b0)
#pop-options

(* ================================================================ *)
(*  6. Inductive alpha step                                           *)
(* ================================================================ *)

(*
   This is the core algebraic step of the file.

   Given the loop invariant

     alpha * d ≈ D(alpha) * b

   with b square-free and deg(b) >= 1, define

     a      = gcd(b, d)
     b'     = b / a
     c'     = d / a
     d'     = c' - D(b')
     alpha' = alpha / b'.

   The intended conclusions are:

     1. b' divides alpha
     2. alpha' * d' ≈ D(alpha') * b'

   Standard proof outline:

     - prove coprime(b', d) using square-freeness of b;
     - from alpha*d ≈ D(alpha)*b = D(alpha)*(a*b'), commute to get b' | alpha*d;
     - apply Euclid's lemma with coprime(b', d) to deduce b' | alpha;
     - write alpha = b'*alpha';
     - expand D(alpha) by the product rule;
     - substitute d = a*c' and b = a*b';
     - cancel a and rearrange to obtain alpha'*d' ≈ D(alpha')*b'.
*)

(* Private helper: ring identity (b'*alpha')*(a*c') = (a*b')*(alpha'*c').
   Factored out because canon_ring needs operator syntax + correct instance binder. *)
private let swap_mid_poly (#t:Type) {| commutative_ring t |} (a b c d: t) 
  : Lemma ((b * c) * (a * d) = ((a* b) * (c * d)))
  = assert ((b * c) * (a * d) = ((a * b) * (c * d))) by canon_ring()

#push-options "--z3rlimit 60 --fuel 4 --ifuel 2 --split_queries always"
private let alpha_inductive_step (#t:Type) {| f: field t |}
  (alpha b d: polynomial t)
  : Lemma (requires char_zero f /\ deg alpha >= 0 /\ deg b >= 1 /\ square_free b /\
                   (((alpha * d)) = (((poly_deriv alpha) * b))))
          (ensures  (let a = poly_gcd b d in
                     let b' = poly_div b a in
                     let c' = poly_div d a in
                     let d' : polynomial t = (c' -- (poly_deriv b')) in
                     let alpha' = poly_div alpha b' in
                     divides b' alpha /\
                     (((alpha' * d')) = (((poly_deriv alpha') * b')))))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let a = poly_gcd b d in
    let b' = poly_div b a in
    let c' = poly_div d a in
    let d' : polynomial t = (c' -- (poly_deriv b')) in
    let alpha' = poly_div alpha b' in
    (* --- Setup --- *)
    gcd_has_degree b d;
    gcd_divides_left b d;
    gcd_divides_right b d;
    poly_div_correct b a;
    poly_div_correct d a;
    (if deg b' >= 0 then () else begin
       degree_none_poly_eq_zero b';
       poly_mul_congruence a b' a [];
       H.x_mul_zero a;
       degree_well_defined [] b end);
    (* --- Part A: b' | alpha via Euclid --- *)
    divides_refl b';
    divides_mul_right b' b' ((poly_deriv alpha) * a);
    mul_commutativity b' ((poly_deriv alpha) * a);
    mul_associativity (poly_deriv alpha) a b';
    mul_congruence (poly_deriv alpha) (a * b') (poly_deriv alpha) b;
    divides_congruence_right b'
      (b' * ((poly_deriv alpha) * a))
      (((poly_deriv alpha) * a) * b');
    divides_congruence_right b'
      (((poly_deriv alpha) * a) * b') (alpha * d);
    coprime_b_prime_d b d;
    euclid_lemma b' d alpha;
    (* --- Part B: new invariant via cancellation --- *)
    poly_div_correct alpha b';
    (* LHS chain: alpha*d ≈ (b'*alpha')*(a*c') ≈ (a*b')*(alpha'*c') *)
    mul_congruence alpha d (b' * alpha') d;
    mul_congruence (b' * alpha') d (b' * alpha') (a * c');
    (* Ring identity: (b'*alpha')*(a*c') = (a*b')*(alpha'*c') *)
    swap_mid_poly a b' alpha' c';
    (* RHS chain: D(alpha)*b ≈ (a*b')*(D(b')*alpha' + b'*D(alpha')) *)
    poly_deriv_congruence alpha (b' * alpha');
    poly_deriv_mul b' alpha';
    mul_congruence (poly_deriv alpha) b
                   (((poly_deriv b') * alpha') + (b' * (poly_deriv alpha'))) b;
    mul_congruence (((poly_deriv b') * alpha') + (b' * (poly_deriv alpha'))) b
                   (((poly_deriv b') * alpha') + (b' * (poly_deriv alpha'))) (a * b');
    mul_commutativity (((poly_deriv b') * alpha') + (b' * (poly_deriv alpha'))) (a * b');
    (* Cancel (a*b'): alpha*d ≈ (a*b')*X and D(alpha)*b ≈ (a*b')*Y; from alpha*d≈D(alpha)*b: X≈Y *)
    degree_well_defined (a * b') b;
    poly_mul_left_cancel (a * b') (alpha' * c')
                         (((poly_deriv b') * alpha') + (b' * (poly_deriv alpha')));
    (* --- Part C: alpha'*c' ≈ D(b')*alpha' + b'*D(alpha') → alpha'*d' ≈ D(alpha')*b' --- *)
    add_commutativity ((poly_deriv b') * alpha') (b' * (poly_deriv alpha'));
    add_sub_cancel (b' * (poly_deriv alpha')) ((poly_deriv b') * alpha');
    add_congruence (alpha' * c') (- ((poly_deriv b') * alpha'))
                   ((b' * (poly_deriv alpha')) + ((poly_deriv b') * alpha'))
                   (- ((poly_deriv b') * alpha'));
    poly_mul_sub_distrib alpha' c' (poly_deriv b');
    mul_commutativity alpha' (poly_deriv b');
    neg_congruence (alpha' * (poly_deriv b')) ((poly_deriv b') * alpha');
    add_congruence (alpha' * c') (- (alpha' * (poly_deriv b')))
                   (alpha' * c') (- ((poly_deriv b') * alpha'));
    mul_commutativity b' (poly_deriv alpha')
#pop-options

(* ================================================================ *)
(*  7. Alpha/product identity through the whole loop                  *)
(* ================================================================ *)

(* Shared per-step facts for both recursive loop lemmas
   (yun_loop_alpha_product, yun_loop_alpha_constant).  Bundles the
   degree bookkeeping and the inductive-step conclusions into one
   cheap-to-discharge helper, so the recursive proofs stay small. *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1 --split_queries on_failure"
private let yun_step_facts (#t:Type) {| f: field t |}
  (alpha b d: polynomial t)
  : Lemma (requires char_zero f /\ deg alpha >= 0 /\ deg b >= 1 /\ square_free b /\
                   ((alpha * d) = ((poly_deriv alpha) * b)))
          (ensures  (let a = poly_gcd b d in
                     let b' = poly_div b a in
                     let c' = poly_div d a in
                     let d' : polynomial t = (c' -- (poly_deriv b')) in
                     let alpha' = poly_div alpha b' in
                     deg b' >= 0 /\ deg alpha' >= 0 /\
                     deg alpha == deg b' + deg alpha' /\
                     divides b' alpha /\
                     (alpha = (b' * alpha')) /\
                     ((alpha' * d') = ((poly_deriv alpha') * b')) /\
                     square_free b'))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let a = poly_gcd b d in
    let b' = poly_div b a in
    let alpha' = poly_div alpha b' in
    (* divides b' alpha + new invariant *)
    alpha_inductive_step alpha b d;
    poly_div_correct alpha b';
    gcd_has_degree b d;
    gcd_divides_left b d;
    poly_div_correct b a;
    (* Establish deg b' >= 0 *)
    (if deg b' >= 0 then () else begin
       degree_none_poly_eq_zero b';
       poly_mul_congruence a b' a (poly_zero #t);
       H.x_mul_zero a;
       degree_well_defined (poly_zero #t) b end);
    (* Establish deg alpha' >= 0 *)
    (if deg alpha' >= 0 then () else begin
       degree_none_poly_eq_zero alpha';
       poly_mul_congruence b' alpha' b' (poly_zero #t);
       H.x_mul_zero b';
       degree_well_defined (poly_zero #t) alpha end);
    (* deg alpha = deg b' + deg alpha' *)
    degree_well_defined (b' * alpha') alpha;
    degree_mul b' alpha';
    (* square_free b' when deg b' >= 1 *)
    divides_refl b';
    divides_mul_right b' b' a;
    mul_commutativity b' a;
    divides_congruence_right b' (b' * a) (a * b');
    divides_congruence_right b' (a * b') b;
    divisor_of_square_free b' b
#pop-options

(*
   Ghost invariant tracked by this theorem:

     alpha0 ≈ b_product(b, d, fuel) * alpha_terminal

   where alpha_terminal is yun_loop_alpha alpha b d fuel and b_product is the
   ghost product of intermediate b-values from PPInvariant.fst.

   At each recursive step the inductive theorem alpha_inductive_step supplies
   alpha = b' * alpha', and the recursive call contributes the tail product.
   Chaining the factor b' onto that recursive identity yields the full product
   decomposition.
*)
#push-options "--z3rlimit 30 --fuel 2 --ifuel 1 --split_queries on_failure"
private let rec yun_loop_alpha_product (#t:Type) {| f: field t |}
  (alpha b d: polynomial t) (fuel: nat)
  : Lemma (requires char_zero f /\ deg alpha >= 0 /\ deg b >= 1 /\ square_free b /\
                   ((alpha * d) = ((poly_deriv alpha) * b)) /\
                   fuel >= deg alpha)
          (ensures  (alpha = ((yun_loop_b_product b d fuel) * (yun_loop_alpha alpha b d fuel))))
          (decreases fuel)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if fuel = 0 then
      (* yun_loop_alpha = alpha, yun_loop_b_product = poly_one *)
      H.one_mul_x alpha
    else begin
      (* fuel > 0 and deg b >= 1 *)
      let a = poly_gcd b d in
      let b' = poly_div b a in
      let c' = poly_div d a in
      let d' : polynomial t = (c' -- (poly_deriv b')) in
      let alpha' = poly_div alpha b' in
      yun_step_facts alpha b d;
      if deg b' = 0 then begin
        (* b' is a constant: the recursive functions return trivially,
           so yun_loop_b_product b d fuel == b' * poly_one and
           yun_loop_alpha alpha b d fuel == alpha'. *)
        H.x_mul_one b';
        poly_mul_congruence (b' * (poly_one #t)) alpha' b' alpha'
      end
      else begin
        (* deg b' >= 1: use the IH *)
        yun_loop_alpha_product alpha' b' d' (fuel - 1);
        (* IH: alpha' ≈ bp' * alpha_term *)
        let bp' = yun_loop_b_product b' d' (fuel - 1) in
        let at = yun_loop_alpha alpha' b' d' (fuel - 1) in
        (* Chain: alpha ≈ b' * alpha' ≈ b' * (bp' * at) ≈ (b' * bp') * at *)
        poly_mul_congruence b' alpha' b' (bp' * at);
        mul_associativity b' bp' at
      end
    end
#pop-options

(* ================================================================ *)
(*  8. If b is constant, then alpha is constant                       *)
(* ================================================================ *)

(*
   Heuristic degree argument intended here:

     alpha*d ≈ D(alpha)*b,
     deg(b) = 0,
     b square-free and therefore a nonzero unit.

   If deg(alpha) = n >= 1, then deg(D(alpha)) = n-1 in characteristic zero, so
   the right-hand side has degree (n-1) + 0 = n-1, while the left-hand side has
   degree at least n unless d is zero in a way incompatible with the invariant.
   The only consistent possibility is deg(alpha) = 0.
*)
#push-options "--z3rlimit 30 --fuel 3 --ifuel 1 --split_queries on_failure"
private let alpha_constant_from_invariant (#t:Type) {| f: field t |}
  (alpha b d: polynomial t)
  : Lemma (requires char_zero f /\ deg alpha >= 0 /\ deg b >= 0 /\
                   deg b = 0 /\ square_free b /\
                   ((alpha * d) = ((poly_deriv alpha) * b)))
          (ensures  deg alpha = 0)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let n = deg alpha in
    if n = 0 then ()
    else begin
      (* n >= 1, so D(alpha) has degree n-1 *)
      poly_deriv_degree_char0 alpha;
      (* D(alpha)*b has degree (n-1) + 0 = n-1 *)
      degree_mul (poly_deriv alpha) b;
      (* alpha*d ≈ D(alpha)*b, so they have the same degree *)
      degree_well_defined (alpha * d) ((poly_deriv alpha) * b);
      (* If d has degree: deg(alpha*d) = n + deg(d) >= n, but RHS has degree n-1. Contradiction. *)
      (* If d is zero: alpha*d ≈ 0, but (alpha * d) ≈ D(alpha)*b which has degree n-1 >= 0. *)
      (if deg d >= 0 then
           degree_mul alpha d
           (* deg(alpha*d) = n + dd, but deg(D(alpha)*b) = n-1. So n + dd = n - 1, impossible. *)
       else begin
           (* d ≈ 0, so alpha*d ≈ 0; but (alpha*d) ≈ D(alpha)*b has degree n-1 *)
           degree_none_poly_eq_zero d;
           poly_mul_congruence alpha d alpha (poly_zero #t);
           H.x_mul_zero alpha;
           degree_well_defined ((poly_deriv alpha) * b) (poly_zero #t) end)
    end
#pop-options

(* ================================================================ *)
(*  9. Recursive proof that alpha becomes constant                    *)
(* ================================================================ *)

#push-options "--z3rlimit 30 --fuel 2 --ifuel 1 --split_queries on_failure"
private let rec yun_loop_alpha_constant (#t:Type) {| f: field t |}
  (alpha b d: polynomial t) (fuel: nat)
  : Lemma (requires char_zero f /\ deg alpha >= 0 /\ deg b >= 1 /\ square_free b /\
                   ((alpha * d) = ((poly_deriv alpha) * b)) /\
                   fuel >= deg alpha)
          (ensures  deg (yun_loop_alpha alpha b d fuel) == 0)
          (decreases fuel)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if fuel = 0 then
      (* fuel = 0 means deg alpha = 0 from requires; yun_loop_alpha returns alpha *)
      ()
    else begin
      let a = poly_gcd b d in
      let b' = poly_div b a in
      let c' = poly_div d a in
      let d' : polynomial t = (c' -- (poly_deriv b')) in
      let alpha' = poly_div alpha b' in
      yun_step_facts alpha b d;
      if deg b' = 0 then
        alpha_constant_from_invariant alpha' b' d'
      else
        yun_loop_alpha_constant alpha' b' d' (fuel - 1)
    end
#pop-options

(* ================================================================ *)
(*  10. PP(yun(p)) divides p                                          *)
(* ================================================================ *)

(* Shared core for both associate directions: establishes the Yun
   bindings for p and proves (pp * at) = p together with the bridge
   pp == powered_product (yun p) and the per-step degree facts both
   callers need.  Factored out so each divisibility proof stays small. *)
#push-options "--z3rlimit 60 --fuel 4 --ifuel 2 --split_queries on_failure"
private let yun_pp_chain (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires char_zero f /\ deg p >= 1)
          (ensures  (let p' = poly_deriv p in
                     let a0 = poly_gcd p p' in
                     let b0 = poly_div p a0 in
                     let c0 = poly_div p' a0 in
                     let d0 : polynomial t = (c0 -- (poly_deriv b0)) in
                     let fuel = (if deg a0 < 0 then 0 else ((deg a0) ++ 1)) in
                     let at = yun_loop_alpha a0 b0 d0 fuel in
                     let pp = powered_product (yun_loop b0 d0 [] fuel) in
                     deg a0 >= 0 /\ deg at == 0 /\
                     ((pp * at) = p) /\
                     pp == powered_product (yun p)))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let p' = poly_deriv p in
    let a0 = poly_gcd p p' in
    let b0 = poly_div p a0 in
    let c0 = poly_div p' a0 in
    let d0 : polynomial t = (c0 -- (poly_deriv b0)) in
    let fuel = (if deg a0 < 0 then 0 else ((deg a0) ++ 1)) in
    (* Setup facts *)
    gcd_has_degree p p';
    gcd_divides_left p p';
    gcd_divides_right p p';
    poly_div_correct p a0;
    (* Establish deg b0 >= 0 via contradiction *)
    (if deg b0 >= 0 then () else begin
       degree_none_poly_eq_zero b0;
       poly_mul_congruence a0 b0 a0 (poly_zero #t);
       H.x_mul_zero a0;
       degree_well_defined (poly_zero #t) p end);
    (* Establish deg b0 >= 1: deg a0 <= deg p' = deg p - 1, so deg b0 >= 1 *)
    poly_deriv_degree_char0 p;
    divides_degree_le a0 p';
    degree_well_defined (a0 * b0) p;
    degree_mul a0 b0;
    b0_is_square_free p;
    (* alpha_base_case: a0*d0 ≈ D(a0)*b0 *)
    alpha_base_case p;
    (* PP(yun(p)) ≈ b0 * bp *)
    yun_loop_pp_b_product b0 d0 fuel;
    let bp = yun_loop_b_product b0 d0 fuel in
    let pp = powered_product (yun_loop b0 d0 [] fuel) in
    (* a0 ≈ bp * at *)
    yun_loop_alpha_product a0 b0 d0 fuel;
    let at = yun_loop_alpha a0 b0 d0 fuel in
    (* at has degree 0 *)
    yun_loop_alpha_constant a0 b0 d0 fuel;
    (* Chain: PP * at ≈ (b0 * bp) * at ≈ b0 * (bp * at) ≈ b0 * a0 ≈ a0 * b0 ≈ p *)
    mul_associativity b0 bp at;
    poly_mul_congruence pp at (b0 * bp) at;
    poly_mul_congruence b0 (bp * at) b0 a0;
    mul_commutativity b0 a0;
    (* Bridge: pp == powered_product (yun p) *)
    yun_unfold p

#pop-options

#push-options "--z3rlimit 30 --fuel 2 --ifuel 1 --split_queries on_failure"
let yun_pp_divides_p (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires char_zero f /\ deg p >= 1)
          (ensures  divides (powered_product (yun p)) p)
  = H.elim_equatable_laws (polynomial t) ();
    let p' = poly_deriv p in
    let a0 = poly_gcd p p' in
    let b0 = poly_div p a0 in
    let c0 = poly_div p' a0 in
    let d0 : polynomial t = (c0 -- (poly_deriv b0)) in
    let fuel = (if deg a0 < 0 then 0 else ((deg a0) ++ 1)) in
    let at = yun_loop_alpha a0 b0 d0 fuel in
    let pp = powered_product (yun_loop b0 d0 [] fuel) in
    yun_pp_chain p;
    (* (pp * at) = p, and divides pp (pp * at) by reflexivity *)
    divides_intro pp (pp * at) at;
    divides_congruence_right pp (pp * at) p
#pop-options

(* ================================================================ *)
(*  11. p divides PP(yun(p))                                          *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 4 --ifuel 2 --split_queries on_failure"
let yun_p_divides_pp (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires char_zero f /\ deg p >= 1)
          (ensures  divides p (powered_product (yun p)))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let p' = poly_deriv p in
    let a0 = poly_gcd p p' in
    let b0 = poly_div p a0 in
    let c0 = poly_div p' a0 in
    let d0 : polynomial t = (c0 -- (poly_deriv b0)) in
    let fuel = (if deg a0 < 0 then 0 else ((deg a0) ++ 1)) in
    let pp = powered_product (yun_loop b0 d0 [] fuel) in
    let at = yun_loop_alpha a0 b0 d0 fuel in
    (* (pp * at) = p, deg at == 0, and pp == powered_product (yun p) *)
    yun_pp_chain p;
    (* deg at == 0, so at == [c] with c = poly_lc at nonzero *)
    degree_zero_is_singleton at;
    let c = poly_lc at in
    let cinv = inv c in
    let cinv_p : polynomial t = [cinv] in
    let c_p : polynomial t = [c] in
    (* [cinv] * [c] ≈ poly_one *)
    singleton_inv_mul_singleton c;
    (* p * [cinv] ≈ (pp * at) * [cinv] ≈ pp * (at * [cinv]) *)
    poly_mul_congruence p cinv_p (pp * at) cinv_p;
    mul_associativity pp at cinv_p;
    (* at == [c], so at * [cinv] == [c] * [cinv] ≈ [cinv] * [c] ≈ poly_one *)
    mul_commutativity c_p cinv_p;
    assert (at == c_p);
    assert ((at * cinv_p) == (c_p * cinv_p));
    poly_mul_congruence pp (at * cinv_p) pp (poly_one #t);
    (* pp * poly_one ≈ pp, so p * [cinv] ≈ pp; hence divides p pp *)
    mul_one pp;
    divides_intro p (p * cinv_p) cinv_p;
    divides_congruence_right p (p * cinv_p) pp
#pop-options

(* ================================================================ *)
(*  THEOREM: p and PP(yun(p)) are associates (mutual divisibility)  *)
(* ================================================================ *)

let yun_associates (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires char_zero f /\ deg p >= 1)
          (ensures  divides (powered_product (yun p)) p /\
                   divides p (powered_product (yun p)))
  = yun_pp_divides_p p;
    yun_p_divides_pp p
