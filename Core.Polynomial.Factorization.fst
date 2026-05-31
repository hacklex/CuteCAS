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
open Core.Polynomial.PPInvariant

(* ================================================================ *)
(*  1. Cancellation: a*p ≈ a*q and deg(a) >= 0  ==>  p ≈ q          *)
(* ================================================================ *)

(*
   Intended proof shape:

     a*p ≈ a*q
       ==> a*(p-q) ≈ 0

   Since Some? (poly_deg a), the polynomial a is nonzero.  Over a field, the
   polynomial ring is an integral domain, so no-zero-divisors yields p-q ≈ 0,
   hence p ≈ q.  The original proof likely used either a direct integral-domain
   argument or an exact-division / Euclid-lemma style reduction.
*)
#push-options "--z3rlimit 80 --fuel 3 --ifuel 1 --split_queries on_failure"
let poly_mul_left_cancel (#t:Type) {| f: field t |}
  (a p q: polynomial t)
  : Lemma (requires Some? (poly_deg a) /\ poly_eq (poly_mul a p) (poly_mul a q))
          (ensures  poly_eq p q)
  = let id_t : integral_domain t = id_of_f t in
    let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* Step 1: a * (p - q) ≈ (a*p) - (a*q) *)
    poly_mul_sub_distrib a p q;
    (* Step 2: (a*p) - (a*q) ≈ 0 since a*p ≈ a*q *)
    poly_sub_reveal (poly_mul a p) (poly_mul a q);
    poly_eq_reflexivity (poly_neg (poly_mul a q));
    poly_add_congruence (poly_mul a p) (poly_neg (poly_mul a q))
                        (poly_mul a q) (poly_neg (poly_mul a q));
    poly_add_negation (poly_mul a q);
    poly_eq_transitivity (poly_sub (poly_mul a p) (poly_mul a q))
                         (poly_add (poly_mul a p) (poly_neg (poly_mul a q)))
                         (poly_add (poly_mul a q) (poly_neg (poly_mul a q)));
    poly_eq_transitivity (poly_sub (poly_mul a p) (poly_mul a q))
                         (poly_add (poly_mul a q) (poly_neg (poly_mul a q)))
                         (poly_zero #t);
    (* Step 3: a * (p - q) ≈ 0 *)
    poly_eq_transitivity (poly_mul a (poly_sub p q))
                         (poly_sub (poly_mul a p) (poly_mul a q))
                         (poly_zero #t);
    (* Step 4: by domain_law, a ≈ 0 or (p-q) ≈ 0 *)
    poly_domain_law a (poly_sub p q);
    (* Step 5: a is not zero — if it were, degree_well_defined + poly_zero
       having None degree contradicts Some? (poly_deg a) *)
    assert (poly_eq a (poly_zero #t) \/ poly_eq (poly_sub p q) (poly_zero #t));
    (if poly_eq a (poly_zero #t) then begin
       degree_well_defined a (poly_zero #t);
       assert (poly_deg a == poly_deg (poly_zero #t))
     end);
    (* Step 6: so (p - q) ≈ 0, hence p ≈ q *)
    sub_zero_implies_eq p q
#pop-options

(* ================================================================ *)
(*  2. Ghost alpha tracker for the Yun loop                          *)
(* ================================================================ *)

let rec yun_loop_alpha (#t:Type) {| f: field t |}
  (alpha b d: polynomial t) (fuel: nat)
  : Tot (polynomial t) (decreases fuel)
  = if fuel = 0 then alpha
    else if None? (poly_deg b) then alpha
    else if Some?.v (poly_deg b) = 0 then alpha
    else
      let a = poly_gcd #t #f b d in
      let b' = poly_div #t #f b a in
      let c' = poly_div #t #f d a in
      let d' = poly_sub c' (poly_deriv b') in
      let alpha' = poly_div #t #f alpha b' in
      yun_loop_alpha #t #f alpha' b' d' (fuel - 1)

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
#push-options "--z3rlimit 80 --fuel 4 --ifuel 2 --split_queries on_failure"
let coprime_b_prime_d (#t:Type) {| f: field t |}
  (b d: polynomial t)
  : Lemma (requires char_zero f /\ Some? (poly_deg b) /\ Some?.v (poly_deg b) >= 1 /\
                     square_free #t #f b)
          (ensures  (let a = poly_gcd #t #f b d in
                     let b' = poly_div #t #f b a in
                     coprime #t #f b' d))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let a = poly_gcd #t #f b d in
    let b' = poly_div #t #f b a in
    let c' = poly_div #t #f d a in
    (* Establish a has degree *)
    gcd_has_degree #t #f b d;
    (* a | b and a | d *)
    gcd_divides_left #t #f b d;
    gcd_divides_right #t #f b d;
    (* poly_mul a b' ≈ b *)
    poly_div_correct #t #f b a;
    (* Establish Some? (poly_deg b') via contradiction:
       if b' is zero then a*b' ≈ 0, but poly_mul a b' ≈ b and b has degree *)
    (match poly_deg b' with
     | Some _ -> ()
     | None ->
         degree_none_poly_eq_zero b';
         H.x_mul_zero #(polynomial t) a;
         poly_eq_transitivity (poly_mul a b') (poly_mul a (poly_zero #t)) (poly_zero #t);
         poly_eq_transitivity (poly_zero #t) (poly_mul a b') b;
         degree_well_defined (poly_zero #t) b);
    (* poly_mul a c' ≈ d *)
    poly_div_correct #t #f d a;
    (* From yun_step_coprime: coprime(a, b') *)
    yun_step_coprime #t #f b d;
    (* coprime(b', a) by symmetry *)
    coprime_symmetric #t #f a b';
    (* From coprime_quotients: coprime(b', c') *)
    coprime_quotients #t #f b d;
    (* coprime_mul_right: coprime(b', a) ∧ coprime(b', c') → coprime(b', a*c') *)
    coprime_mul_right #t #f b' a c';
    (* Bridge: a*c' ≈ d, so gcd(b', a*c') ≈ gcd(b', d) *)
    poly_eq_reflexivity b';
    gcd_congruence #t #f b' b' (poly_mul a c') d;
    (* Transfer coprime via degree_well_defined *)
    coprime_reveal #t #f b' (poly_mul a c');
    coprime_reveal #t #f b' d;
    degree_well_defined (poly_gcd #t #f b' (poly_mul a c')) (poly_gcd #t #f b' d)
#pop-options

(* ================================================================ *)
(*  4. Helper: (X + Y) - Y ≈ X                                        *)
(* ================================================================ *)

private let poly_add_sub_cancel (#t:Type) {| cr: commutative_ring t |}
  (x y: polynomial t)
  : Lemma (ensures poly_eq (poly_sub (poly_add x y) y) x)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let lhs = poly_sub (poly_add x y) y in
    let mid1 = poly_add (poly_add x y) (poly_neg y) in
    let mid2 = poly_add x (poly_add y (poly_neg y)) in
    let mid3 = poly_add x (poly_zero #t) in
    poly_sub_reveal (poly_add x y) y;
    poly_add_associativity x y (poly_neg y);
    poly_eq_symmetry (poly_add (poly_add x y) (poly_neg y))
                     (poly_add x (poly_add y (poly_neg y)));
    poly_add_negation y;
    poly_eq_reflexivity x;
    poly_add_congruence x (poly_add y (poly_neg y)) x (poly_zero #t);
    poly_eq_transitivity lhs mid1 mid2;
    poly_eq_transitivity lhs mid2 mid3;
    poly_add_zero x;
    poly_eq_transitivity lhs mid3 x

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
#push-options "--z3rlimit 100 --fuel 3 --ifuel 1 --split_queries on_failure"
let alpha_base_case (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires char_zero f /\ Some? (poly_deg p) /\ Some?.v (poly_deg p) >= 1)
          (ensures  (let p' = poly_deriv p in
                     let a0 = poly_gcd #t #f p p' in
                     let b0 = poly_div #t #f p a0 in
                     let c0 = poly_div #t #f p' a0 in
                     let d0 = poly_sub c0 (poly_deriv b0) in
                     poly_eq (poly_mul a0 d0) (poly_mul (poly_deriv a0) b0)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let p' = poly_deriv p in
    let a0 = poly_gcd #t #f p p' in
    let b0 = poly_div #t #f p a0 in
    let c0 = poly_div #t #f p' a0 in
    let d0 = poly_sub c0 (poly_deriv b0) in
    (* Step 1: a0 has degree, divides p and p' *)
    gcd_has_degree #t #f p p';
    gcd_divides_left #t #f p p';
    gcd_divides_right #t #f p p';
    (* Step 2: a0*b0 ≈ p *)
    poly_div_correct #t #f p a0;
    (* Step 3: D(p) ≈ D(a0*b0) ≈ D(a0)*b0 + a0*D(b0) *)
    poly_eq_symmetry (poly_mul a0 b0) p;
    poly_deriv_congruence p (poly_mul a0 b0);
    poly_deriv_mul a0 b0;
    poly_eq_transitivity (poly_deriv p) (poly_deriv (poly_mul a0 b0))
                         (poly_add (poly_mul (poly_deriv a0) b0) (poly_mul a0 (poly_deriv b0)));
    (* Step 4: a0*c0 ≈ p' *)
    poly_div_correct #t #f p' a0;
    (* Step 5: a0*c0 ≈ D(a0)*b0 + a0*D(b0) *)
    poly_eq_symmetry (poly_mul a0 c0) p';
    poly_eq_transitivity (poly_mul a0 c0) p'
                         (poly_add (poly_mul (poly_deriv a0) b0) (poly_mul a0 (poly_deriv b0)));
    (* Step 6: poly_add_sub_cancel gives (X + Y) - Y ≈ X *)
    poly_add_sub_cancel (poly_mul (poly_deriv a0) b0) (poly_mul a0 (poly_deriv b0));
    (* Step 7: by sub-congruence on LHS:
       poly_sub (a0*c0) (a0*D(b0)) ≈ poly_sub (D(a0)*b0 + a0*D(b0)) (a0*D(b0)) *)
    poly_neg_congruence (poly_mul a0 (poly_deriv b0)) (poly_mul a0 (poly_deriv b0));
    poly_add_congruence (poly_mul a0 c0) (poly_neg (poly_mul a0 (poly_deriv b0)))
                        (poly_add (poly_mul (poly_deriv a0) b0) (poly_mul a0 (poly_deriv b0)))
                        (poly_neg (poly_mul a0 (poly_deriv b0)));
    poly_sub_reveal (poly_mul a0 c0) (poly_mul a0 (poly_deriv b0));
    poly_sub_reveal (poly_add (poly_mul (poly_deriv a0) b0) (poly_mul a0 (poly_deriv b0)))
                    (poly_mul a0 (poly_deriv b0));
    (* Now: poly_sub (a0*c0) (a0*D(b0)) ≈ poly_sub (D(a0)*b0 + a0*D(b0)) (a0*D(b0)) ≈ D(a0)*b0 *)
    poly_eq_transitivity (poly_sub (poly_mul a0 c0) (poly_mul a0 (poly_deriv b0)))
                         (poly_sub (poly_add (poly_mul (poly_deriv a0) b0) (poly_mul a0 (poly_deriv b0)))
                                   (poly_mul a0 (poly_deriv b0)))
                         (poly_mul (poly_deriv a0) b0);
    (* Step 8: a0*d0 ≈ a0*(c0 - D(b0)) ≈ a0*c0 - a0*D(b0) via poly_mul_sub_distrib *)
    poly_mul_sub_distrib a0 c0 (poly_deriv b0);
    (* Chain: poly_mul a0 d0 ≈ poly_sub (a0*c0) (a0*D(b0)) ≈ D(a0)*b0 *)
    poly_eq_transitivity (poly_mul a0 (poly_sub c0 (poly_deriv b0)))
                         (poly_sub (poly_mul a0 c0) (poly_mul a0 (poly_deriv b0)))
                         (poly_mul (poly_deriv a0) b0)
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
private let swap_mid_poly (#t:Type) {| commutative_ring t |}
  (a b' alpha' c': polynomial t)
  : Lemma (poly_eq (poly_mul (poly_mul b' alpha') (poly_mul a c'))
                   (poly_mul (poly_mul a b') (poly_mul alpha' c')))
  = let pcrc : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    let _cr_p : commutative_ring (polynomial t) = TC.solve in
    assert (((b' * alpha') * (a * c')) = ((a * b') * (alpha' * c')))
      by Core.Tactics.CanonRing.canon_ring ()

#push-options "--z3rlimit 120 --fuel 4 --ifuel 2 --split_queries always"
let alpha_inductive_step (#t:Type) {| f: field t |}
  (alpha b d: polynomial t)
  : Lemma (requires char_zero f /\ Some? (poly_deg alpha) /\ Some? (poly_deg b) /\
                   Some?.v (poly_deg b) >= 1 /\ square_free #t #f b /\
                   poly_eq (poly_mul alpha d) (poly_mul (poly_deriv alpha) b))
          (ensures  (let a = poly_gcd #t #f b d in
                     let b' = poly_div #t #f b a in
                     let c' = poly_div #t #f d a in
                     let d' = poly_sub c' (poly_deriv b') in
                     let alpha' = poly_div #t #f alpha b' in
                     divides b' alpha /\
                     poly_eq (poly_mul alpha' d') (poly_mul (poly_deriv alpha') b')))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    let id_t : integral_domain t = id_of_f t in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let a = poly_gcd #t #f b d in
    let b' = poly_div #t #f b a in
    let c' = poly_div #t #f d a in
    let d' = poly_sub c' (poly_deriv b') in
    let alpha' = poly_div #t #f alpha b' in
    (* --- Setup --- *)
    gcd_has_degree #t #f b d;
    gcd_divides_left #t #f b d;
    gcd_divides_right #t #f b d;
    poly_div_correct #t #f b a;
    poly_div_correct #t #f d a;
    (match poly_deg b' with Some _ -> () | None ->
       degree_none_poly_eq_zero b';
       poly_eq_reflexivity a;
       poly_mul_congruence a b' a (poly_zero #t);
       H.x_mul_zero #(polynomial t) a;
       poly_eq_transitivity (poly_mul a b') (poly_mul a (poly_zero #t)) (poly_zero #t);
       poly_eq_transitivity (poly_zero #t) (poly_mul a b') b;
       degree_well_defined (poly_zero #t) b);
    (* --- Part A: b' | alpha via Euclid --- *)
    divides_refl #(polynomial t) #cr_p b';
    divides_mul_right #(polynomial t) #cr_p b' b' (poly_mul (poly_deriv alpha) a);
    poly_mul_commutativity b' (poly_mul (poly_deriv alpha) a);
    poly_mul_associativity (poly_deriv alpha) a b';
    poly_eq_symmetry (poly_mul (poly_mul (poly_deriv alpha) a) b')
                     (poly_mul (poly_deriv alpha) (poly_mul a b'));
    poly_mul_congruence (poly_deriv alpha) (poly_mul a b') (poly_deriv alpha) b;
    poly_eq_transitivity (poly_mul (poly_deriv alpha) (poly_mul a b'))
                         (poly_mul (poly_deriv alpha) b) (poly_mul (poly_deriv alpha) b);
    poly_eq_transitivity (poly_mul (poly_mul (poly_deriv alpha) a) b')
                         (poly_mul (poly_deriv alpha) (poly_mul a b'))
                         (poly_mul (poly_deriv alpha) b);
    poly_eq_symmetry (poly_mul alpha d) (poly_mul (poly_deriv alpha) b);
    poly_eq_transitivity (poly_mul (poly_mul (poly_deriv alpha) a) b')
                         (poly_mul (poly_deriv alpha) b) (poly_mul alpha d);
    divides_congruence_right #(polynomial t) #cr_p b'
      (poly_mul b' (poly_mul (poly_deriv alpha) a))
      (poly_mul (poly_mul (poly_deriv alpha) a) b');
    divides_congruence_right #(polynomial t) #cr_p b'
      (poly_mul (poly_mul (poly_deriv alpha) a) b') (poly_mul alpha d);
    coprime_b_prime_d b d;
    euclid_lemma #t #f b' d alpha;
    (* --- Part B: new invariant via cancellation --- *)
    poly_div_correct #t #f alpha b';
    (* LHS chain: alpha*d ≈ (b'*alpha')*(a*c') ≈ (a*b')*(alpha'*c') *)
    poly_eq_symmetry (poly_mul b' alpha') alpha;
    poly_mul_congruence alpha d (poly_mul b' alpha') d;
    poly_eq_symmetry (poly_mul a c') d;
    poly_eq_reflexivity (poly_mul b' alpha');
    poly_mul_congruence (poly_mul b' alpha') d (poly_mul b' alpha') (poly_mul a c');
    poly_eq_transitivity (poly_mul alpha d) (poly_mul (poly_mul b' alpha') d)
                         (poly_mul (poly_mul b' alpha') (poly_mul a c'));
    (* Ring identity: (b'*alpha')*(a*c') = (a*b')*(alpha'*c') *)
    swap_mid_poly a b' alpha' c';
    poly_eq_transitivity (poly_mul alpha d) (poly_mul (poly_mul b' alpha') (poly_mul a c'))
                         (poly_mul (poly_mul a b') (poly_mul alpha' c'));
    (* RHS chain: D(alpha)*b ≈ (a*b')*(D(b')*alpha' + b'*D(alpha')) *)
    poly_deriv_congruence alpha (poly_mul b' alpha');
    poly_deriv_mul b' alpha';
    poly_eq_transitivity (poly_deriv alpha) (poly_deriv (poly_mul b' alpha'))
                         (poly_add (poly_mul (poly_deriv b') alpha')
                                   (poly_mul b' (poly_deriv alpha')));
    poly_mul_congruence (poly_deriv alpha) b
                        (poly_add (poly_mul (poly_deriv b') alpha')
                                  (poly_mul b' (poly_deriv alpha'))) b;
    poly_eq_reflexivity (poly_add (poly_mul (poly_deriv b') alpha')
                                  (poly_mul b' (poly_deriv alpha')));
    poly_mul_congruence (poly_add (poly_mul (poly_deriv b') alpha')
                                  (poly_mul b' (poly_deriv alpha'))) b
                        (poly_add (poly_mul (poly_deriv b') alpha')
                                  (poly_mul b' (poly_deriv alpha'))) (poly_mul a b');
    poly_eq_transitivity (poly_mul (poly_deriv alpha) b)
                         (poly_mul (poly_add (poly_mul (poly_deriv b') alpha')
                                            (poly_mul b' (poly_deriv alpha'))) b)
                         (poly_mul (poly_add (poly_mul (poly_deriv b') alpha')
                                            (poly_mul b' (poly_deriv alpha'))) (poly_mul a b'));
    poly_mul_commutativity (poly_add (poly_mul (poly_deriv b') alpha')
                                     (poly_mul b' (poly_deriv alpha'))) (poly_mul a b');
    poly_eq_transitivity (poly_mul (poly_deriv alpha) b)
                         (poly_mul (poly_add (poly_mul (poly_deriv b') alpha')
                                            (poly_mul b' (poly_deriv alpha'))) (poly_mul a b'))
                         (poly_mul (poly_mul a b')
                                   (poly_add (poly_mul (poly_deriv b') alpha')
                                             (poly_mul b' (poly_deriv alpha'))));
    (* Cancel (a*b'): alpha*d ≈ (a*b')*X and D(alpha)*b ≈ (a*b')*Y; from alpha*d≈D(alpha)*b: X≈Y *)
    poly_eq_symmetry (poly_mul alpha d) (poly_mul (poly_deriv alpha) b);
    poly_eq_transitivity (poly_mul (poly_mul a b') (poly_mul alpha' c'))
                         (poly_mul alpha d) (poly_mul (poly_deriv alpha) b);
    poly_eq_transitivity (poly_mul (poly_mul a b') (poly_mul alpha' c'))
                         (poly_mul (poly_deriv alpha) b)
                         (poly_mul (poly_mul a b')
                                   (poly_add (poly_mul (poly_deriv b') alpha')
                                             (poly_mul b' (poly_deriv alpha'))));
    degree_well_defined (poly_mul a b') b;
    poly_mul_left_cancel (poly_mul a b') (poly_mul alpha' c')
                         (poly_add (poly_mul (poly_deriv b') alpha')
                                   (poly_mul b' (poly_deriv alpha')));
    (* --- Part C: alpha'*c' ≈ D(b')*alpha' + b'*D(alpha') → alpha'*d' ≈ D(alpha')*b' --- *)
    poly_add_commutativity (poly_mul (poly_deriv b') alpha') (poly_mul b' (poly_deriv alpha'));
    poly_eq_transitivity (poly_mul alpha' c')
                         (poly_add (poly_mul (poly_deriv b') alpha')
                                   (poly_mul b' (poly_deriv alpha')))
                         (poly_add (poly_mul b' (poly_deriv alpha'))
                                   (poly_mul (poly_deriv b') alpha'));
    poly_add_sub_cancel (poly_mul b' (poly_deriv alpha')) (poly_mul (poly_deriv b') alpha');
    poly_neg_congruence (poly_mul (poly_deriv b') alpha') (poly_mul (poly_deriv b') alpha');
    poly_add_congruence (poly_mul alpha' c') (poly_neg (poly_mul (poly_deriv b') alpha'))
                        (poly_add (poly_mul b' (poly_deriv alpha'))
                                  (poly_mul (poly_deriv b') alpha'))
                        (poly_neg (poly_mul (poly_deriv b') alpha'));
    poly_sub_reveal (poly_mul alpha' c') (poly_mul (poly_deriv b') alpha');
    poly_sub_reveal (poly_add (poly_mul b' (poly_deriv alpha'))
                              (poly_mul (poly_deriv b') alpha'))
                    (poly_mul (poly_deriv b') alpha');
    poly_eq_transitivity (poly_sub (poly_mul alpha' c') (poly_mul (poly_deriv b') alpha'))
                         (poly_sub (poly_add (poly_mul b' (poly_deriv alpha'))
                                            (poly_mul (poly_deriv b') alpha'))
                                   (poly_mul (poly_deriv b') alpha'))
                         (poly_mul b' (poly_deriv alpha'));
    poly_mul_sub_distrib alpha' c' (poly_deriv b');
    poly_mul_commutativity alpha' (poly_deriv b');
    poly_neg_congruence (poly_mul alpha' (poly_deriv b')) (poly_mul (poly_deriv b') alpha');
    poly_eq_reflexivity (poly_mul alpha' c');
    poly_add_congruence (poly_mul alpha' c') (poly_neg (poly_mul alpha' (poly_deriv b')))
                        (poly_mul alpha' c') (poly_neg (poly_mul (poly_deriv b') alpha'));
    poly_sub_reveal (poly_mul alpha' c') (poly_mul alpha' (poly_deriv b'));
    poly_sub_reveal (poly_mul alpha' c') (poly_mul (poly_deriv b') alpha');
    poly_eq_transitivity (poly_mul alpha' (poly_sub c' (poly_deriv b')))
                         (poly_sub (poly_mul alpha' c') (poly_mul alpha' (poly_deriv b')))
                         (poly_sub (poly_mul alpha' c') (poly_mul (poly_deriv b') alpha'));
    poly_eq_transitivity (poly_mul alpha' d')
                         (poly_sub (poly_mul alpha' c') (poly_mul (poly_deriv b') alpha'))
                         (poly_mul b' (poly_deriv alpha'));
    poly_mul_commutativity b' (poly_deriv alpha');
    poly_eq_transitivity (poly_mul alpha' d')
                         (poly_mul b' (poly_deriv alpha'))
                         (poly_mul (poly_deriv alpha') b')
#pop-options

(* ================================================================ *)
(*  7. Alpha/product identity through the whole loop                  *)
(* ================================================================ *)

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
#push-options "--z3rlimit 120 --fuel 4 --ifuel 2 --split_queries always"
let rec yun_loop_alpha_product (#t:Type) {| f: field t |}
  (alpha b d: polynomial t) (fuel: nat)
  : Lemma (requires char_zero f /\ Some? (poly_deg alpha) /\ Some? (poly_deg b) /\
                   Some?.v (poly_deg b) >= 1 /\ square_free #t #f b /\
                   poly_eq (poly_mul alpha d) (poly_mul (poly_deriv alpha) b) /\
                   fuel >= Some?.v (poly_deg alpha))
          (ensures  poly_eq alpha
                     (poly_mul (yun_loop_b_product #t #f b d fuel)
                               (yun_loop_alpha #t #f alpha b d fuel)))
          (decreases fuel)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    let id_t : integral_domain t = id_of_f t in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if fuel = 0 then begin
      (* yun_loop_alpha = alpha, yun_loop_b_product = poly_one *)
      H.one_mul_x #(polynomial t) alpha;
      poly_eq_symmetry (poly_mul (poly_one #t) alpha) alpha
    end else begin
      (* fuel > 0 and deg b >= 1 *)
      let a = poly_gcd #t #f b d in
      let b' = poly_div #t #f b a in
      let c' = poly_div #t #f d a in
      let d' = poly_sub c' (poly_deriv b') in
      let alpha' = poly_div #t #f alpha b' in
      (* From alpha_inductive_step: divides b' alpha + new invariant *)
      alpha_inductive_step alpha b d;
      poly_div_correct #t #f alpha b';
      (* Establish Some? (poly_deg b') *)
      gcd_has_degree #t #f b d;
      gcd_divides_left #t #f b d;
      poly_div_correct #t #f b a;
      (match poly_deg b' with Some _ -> () | None ->
         degree_none_poly_eq_zero b';
         poly_eq_reflexivity a;
         poly_mul_congruence a b' a (poly_zero #t);
         H.x_mul_zero #(polynomial t) a;
         poly_eq_transitivity (poly_mul a b') (poly_mul a (poly_zero #t)) (poly_zero #t);
         poly_eq_transitivity (poly_zero #t) (poly_mul a b') b;
         degree_well_defined (poly_zero #t) b);
      (* Establish Some? (poly_deg alpha') via contradiction *)
      (match poly_deg alpha' with Some _ -> () | None ->
         degree_none_poly_eq_zero alpha';
         poly_eq_reflexivity b';
         poly_mul_congruence b' alpha' b' (poly_zero #t);
         H.x_mul_zero #(polynomial t) b';
         poly_eq_transitivity (poly_mul b' alpha') (poly_mul b' (poly_zero #t)) (poly_zero #t);
         poly_eq_transitivity (poly_zero #t) (poly_mul b' alpha') alpha;
         degree_well_defined (poly_zero #t) alpha);
      (* deg alpha = deg b' + deg alpha' *)
      degree_well_defined (poly_mul b' alpha') alpha;
      degree_mul #t #id_t b' alpha';
      if Some?.v (poly_deg b') = 0 then begin
        (* b' is a constant: the recursive functions return trivially *)
        H.x_mul_one #(polynomial t) b';
        poly_mul_congruence (poly_mul b' (poly_one #t)) alpha'
                            b' alpha';
        poly_eq_symmetry alpha (poly_mul b' alpha');
        poly_eq_transitivity alpha (poly_mul b' alpha')
                             (poly_mul (poly_mul b' (poly_one #t)) alpha');
        poly_eq_symmetry (poly_mul (poly_mul b' (poly_one #t)) alpha')
                         alpha
      end else begin
        (* deg b' >= 1: use the IH *)
        divides_refl #(polynomial t) #cr_p b';
        divides_mul_right #(polynomial t) #cr_p b' b' a;
        poly_mul_commutativity b' a;
        divides_congruence_right #(polynomial t) #cr_p b' (poly_mul b' a) (poly_mul a b');
        divides_congruence_right #(polynomial t) #cr_p b' (poly_mul a b') b;
        divisor_of_square_free #t #f b' b;
        yun_loop_alpha_product #t #f alpha' b' d' (fuel - 1);
        (* IH: alpha' ≈ bp' * alpha_term *)
        let bp' = yun_loop_b_product #t #f b' d' (fuel - 1) in
        let at = yun_loop_alpha #t #f alpha' b' d' (fuel - 1) in
        (* Chain: alpha ≈ b' * alpha' ≈ b' * (bp' * at) ≈ (b' * bp') * at *)
        poly_eq_symmetry alpha (poly_mul b' alpha');
        poly_eq_reflexivity b';
        poly_mul_congruence b' alpha' b' (poly_mul bp' at);
        poly_eq_transitivity alpha (poly_mul b' alpha') (poly_mul b' (poly_mul bp' at));
        poly_mul_associativity b' bp' at;
        poly_eq_symmetry (poly_mul (poly_mul b' bp') at) (poly_mul b' (poly_mul bp' at));
        poly_eq_transitivity alpha (poly_mul b' (poly_mul bp' at))
                             (poly_mul (poly_mul b' bp') at)
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
#push-options "--z3rlimit 80 --fuel 3 --ifuel 1 --split_queries on_failure"
let alpha_constant_from_invariant (#t:Type) {| f: field t |}
  (alpha b d: polynomial t)
  : Lemma (requires char_zero f /\ Some? (poly_deg alpha) /\ Some? (poly_deg b) /\
                   Some?.v (poly_deg b) = 0 /\ square_free #t #f b /\
                   poly_eq (poly_mul alpha d) (poly_mul (poly_deriv alpha) b))
          (ensures  Some?.v (poly_deg alpha) = 0)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    let id_t : integral_domain t = id_of_f t in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let n = Some?.v (poly_deg alpha) in
    if n = 0 then ()
    else begin
      (* n >= 1, so D(alpha) has degree n-1 *)
      poly_deriv_degree_char0 alpha;
      (* D(alpha)*b has degree (n-1) + 0 = n-1 *)
      degree_mul #t #id_t (poly_deriv alpha) b;
      (* alpha*d ≈ D(alpha)*b, so they have the same degree *)
      degree_well_defined (poly_mul alpha d) (poly_mul (poly_deriv alpha) b);
      (* If d has degree: deg(alpha*d) = n + deg(d) >= n, but RHS has degree n-1. Contradiction. *)
      (* If d is zero: alpha*d ≈ 0, but poly_mul alpha d ≈ D(alpha)*b which has degree n-1 >= 0. *)
      (match poly_deg d with
       | Some dd ->
           degree_mul #t #id_t alpha d
           (* deg(alpha*d) = n + dd, but deg(D(alpha)*b) = n-1. So n + dd = n - 1, impossible. *)
       | None ->
           (* d ≈ 0, so alpha*d ≈ 0 *)
           degree_none_poly_eq_zero d;
           poly_eq_reflexivity alpha;
           poly_mul_congruence alpha d alpha (poly_zero #t);
           H.x_mul_zero #(polynomial t) alpha;
           poly_eq_transitivity (poly_mul alpha d) (poly_mul alpha (poly_zero #t)) (poly_zero #t);
           (* But poly_mul alpha d ≈ D(alpha)*b which has degree n-1 *)
           poly_eq_symmetry (poly_mul alpha d) (poly_mul (poly_deriv alpha) b);
           poly_eq_transitivity (poly_mul (poly_deriv alpha) b) (poly_mul alpha d) (poly_zero #t);
           degree_well_defined (poly_mul (poly_deriv alpha) b) (poly_zero #t))
    end
#pop-options

(* ================================================================ *)
(*  9. Recursive proof that alpha becomes constant                    *)
(* ================================================================ *)

#push-options "--z3rlimit 120 --fuel 4 --ifuel 2 --split_queries always"
let rec yun_loop_alpha_constant (#t:Type) {| f: field t |}
  (alpha b d: polynomial t) (fuel: nat)
  : Lemma (requires char_zero f /\ Some? (poly_deg alpha) /\ Some? (poly_deg b) /\
                   Some?.v (poly_deg b) >= 1 /\ square_free #t #f b /\
                   poly_eq (poly_mul alpha d) (poly_mul (poly_deriv alpha) b) /\
                   fuel >= Some?.v (poly_deg alpha))
          (ensures  poly_deg (yun_loop_alpha #t #f alpha b d fuel) == Some 0)
          (decreases fuel)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    let id_t : integral_domain t = id_of_f t in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if fuel = 0 then
      (* fuel = 0 means deg alpha = 0 from requires; yun_loop_alpha returns alpha *)
      ()
    else begin
      let a = poly_gcd #t #f b d in
      let b' = poly_div #t #f b a in
      let c' = poly_div #t #f d a in
      let d' = poly_sub c' (poly_deriv b') in
      let alpha' = poly_div #t #f alpha b' in
      (* Establish invariant for alpha' b' d' *)
      alpha_inductive_step alpha b d;
      poly_div_correct #t #f alpha b';
      gcd_has_degree #t #f b d;
      gcd_divides_left #t #f b d;
      poly_div_correct #t #f b a;
      (* Establish Some? (poly_deg b') *)
      (match poly_deg b' with Some _ -> () | None ->
         degree_none_poly_eq_zero b';
         poly_eq_reflexivity a;
         poly_mul_congruence a b' a (poly_zero #t);
         H.x_mul_zero #(polynomial t) a;
         poly_eq_transitivity (poly_mul a b') (poly_mul a (poly_zero #t)) (poly_zero #t);
         poly_eq_transitivity (poly_zero #t) (poly_mul a b') b;
         degree_well_defined (poly_zero #t) b);
      (* Establish Some? (poly_deg alpha') *)
      (match poly_deg alpha' with Some _ -> () | None ->
         degree_none_poly_eq_zero alpha';
         poly_eq_reflexivity b';
         poly_mul_congruence b' alpha' b' (poly_zero #t);
         H.x_mul_zero #(polynomial t) b';
         poly_eq_transitivity (poly_mul b' alpha') (poly_mul b' (poly_zero #t)) (poly_zero #t);
         poly_eq_transitivity (poly_zero #t) (poly_mul b' alpha') alpha;
         degree_well_defined (poly_zero #t) alpha);
      (* deg alpha = deg b' + deg alpha' *)
      degree_well_defined (poly_mul b' alpha') alpha;
      degree_mul #t #id_t b' alpha';
      (* square_free b' in all cases *)
      divides_refl #(polynomial t) #cr_p b';
      divides_mul_right #(polynomial t) #cr_p b' b' a;
      poly_mul_commutativity b' a;
      divides_congruence_right #(polynomial t) #cr_p b' (poly_mul b' a) (poly_mul a b');
      divides_congruence_right #(polynomial t) #cr_p b' (poly_mul a b') b;
      divisor_of_square_free #t #f b' b;
      if Some?.v (poly_deg b') = 0 then
        alpha_constant_from_invariant alpha' b' d'
      else
        yun_loop_alpha_constant #t #f alpha' b' d' (fuel - 1)
    end
#pop-options

(* ================================================================ *)
(*  10. PP(yun(p)) divides p                                          *)
(* ================================================================ *)

#push-options "--z3rlimit 200 --fuel 4 --ifuel 2"
let yun_pp_divides_p (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires char_zero f /\ Some? (poly_deg p) /\ Some?.v (poly_deg p) >= 1)
          (ensures  divides #(polynomial t) (powered_product (yun #t #f p)) p)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    let id_t : integral_domain t = id_of_f t in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let p' = poly_deriv p in
    let a0 = poly_gcd #t #f p p' in
    let b0 = poly_div #t #f p a0 in
    let c0 = poly_div #t #f p' a0 in
    let d0 = poly_sub c0 (poly_deriv b0) in
    let fuel = (match poly_deg a0 with | None -> 0 | Some n -> Prims.op_Addition n 1) in
    (* Setup facts *)
    gcd_has_degree #t #f p p';
    gcd_divides_left #t #f p p';
    gcd_divides_right #t #f p p';
    poly_div_correct #t #f p a0;
    (* Establish Some? (poly_deg b0) via contradiction *)
    (match poly_deg b0 with Some _ -> () | None ->
       degree_none_poly_eq_zero b0;
       poly_eq_reflexivity a0;
       poly_mul_congruence a0 b0 a0 (poly_zero #t);
       H.x_mul_zero #(polynomial t) a0;
       poly_eq_transitivity (poly_mul a0 b0) (poly_mul a0 (poly_zero #t)) (poly_zero #t);
       poly_eq_transitivity (poly_zero #t) (poly_mul a0 b0) p;
       degree_well_defined (poly_zero #t) p);
    (* Establish deg b0 >= 1: deg a0 <= deg p' = deg p - 1, so deg b0 = deg p - deg a0 >= 1 *)
    poly_deriv_degree_char0 p;
    divides_degree_le #t #f a0 p';
    degree_well_defined (poly_mul a0 b0) p;
    degree_mul #t #id_t a0 b0;
    b0_is_square_free #t #f p;
    (* alpha_base_case: a0*d0 ≈ D(a0)*b0 *)
    alpha_base_case p;
    (* PP(yun(p)) ≈ b0 * bp *)
    yun_loop_pp_b_product #t #f b0 d0 fuel;
    let bp = yun_loop_b_product #t #f b0 d0 fuel in
    let pp = powered_product (yun_loop #t #f b0 d0 [] fuel) in
    (* a0 ≈ bp * at *)
    yun_loop_alpha_product #t #f a0 b0 d0 fuel;
    let at = yun_loop_alpha #t #f a0 b0 d0 fuel in
    (* Chain: PP * at ≈ (b0 * bp) * at ≈ b0 * (bp * at) ≈ b0 * a0 ≈ a0 * b0 ≈ p *)
    poly_mul_associativity b0 bp at;
    poly_eq_symmetry (poly_mul (poly_mul b0 bp) at) (poly_mul b0 (poly_mul bp at));
    poly_mul_congruence pp at (poly_mul b0 bp) at;
    poly_eq_transitivity (poly_mul pp at) (poly_mul (poly_mul b0 bp) at)
                         (poly_mul b0 (poly_mul bp at));
    poly_eq_reflexivity b0;
    poly_mul_congruence b0 (poly_mul bp at) b0 a0;
    poly_eq_transitivity (poly_mul pp at) (poly_mul b0 (poly_mul bp at)) (poly_mul b0 a0);
    poly_mul_commutativity b0 a0;
    poly_eq_transitivity (poly_mul pp at) (poly_mul b0 a0) (poly_mul a0 b0);
    poly_eq_transitivity (poly_mul pp at) (poly_mul a0 b0) p;
    (* Chain: PP * at ≈ ... ≈ p *)
    (* Establish divides pp (poly_mul pp at) by reflexivity *)
    poly_eq_reflexivity (poly_mul pp at);
    divides_intro pp (poly_mul pp at) at;
    (* Transfer: poly_eq (poly_mul pp at) p gives divides pp p *)
    (* Note: divides_congruence_right needs `eq a b` from the CR's equatable.
       We bridge by asserting the eq fact explicitly using the same TC path. *)
    assert (eq #(polynomial t) (poly_mul pp at) p);
    assert (divides pp (poly_mul pp at));
    divides_congruence_right pp (poly_mul pp at) p;
    (* Bridge: pp == powered_product (yun p) *)
    yun_unfold #t #f p;
    assert (pp == powered_product (yun #t #f p))
#pop-options

(* ================================================================ *)
(*  11. p divides PP(yun(p))                                          *)
(* ================================================================ *)

#push-options "--z3rlimit 200 --fuel 4 --ifuel 2"
let yun_p_divides_pp (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires char_zero f /\ Some? (poly_deg p) /\ Some?.v (poly_deg p) >= 1)
          (ensures  divides #(polynomial t) p (powered_product (yun #t #f p)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    let id_t : integral_domain t = id_of_f t in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let p' = poly_deriv p in
    let a0 = poly_gcd #t #f p p' in
    let b0 = poly_div #t #f p a0 in
    let c0 = poly_div #t #f p' a0 in
    let d0 = poly_sub c0 (poly_deriv b0) in
    let fuel = (match poly_deg a0 with | None -> 0 | Some n -> Prims.op_Addition n 1) in
    (* Setup facts — same as yun_pp_divides_p *)
    gcd_has_degree #t #f p p';
    gcd_divides_left #t #f p p';
    gcd_divides_right #t #f p p';
    poly_div_correct #t #f p a0;
    (* Establish Some? (poly_deg b0) *)
    (match poly_deg b0 with Some _ -> () | None ->
       degree_none_poly_eq_zero b0;
       poly_eq_reflexivity a0;
       poly_mul_congruence a0 b0 a0 (poly_zero #t);
       H.x_mul_zero #(polynomial t) a0;
       poly_eq_transitivity (poly_mul a0 b0) (poly_mul a0 (poly_zero #t)) (poly_zero #t);
       poly_eq_transitivity (poly_zero #t) (poly_mul a0 b0) p;
       degree_well_defined (poly_zero #t) p);
    poly_deriv_degree_char0 p;
    divides_degree_le #t #f a0 p';
    degree_well_defined (poly_mul a0 b0) p;
    degree_mul #t #id_t a0 b0;
    b0_is_square_free #t #f p;
    (* alpha_base_case *)
    alpha_base_case p;
    (* PP(yun(p)) ≈ b0 * bp *)
    yun_loop_pp_b_product #t #f b0 d0 fuel;
    let bp = yun_loop_b_product #t #f b0 d0 fuel in
    let pp = powered_product (yun_loop #t #f b0 d0 [] fuel) in
    (* a0 ≈ bp * at *)
    yun_loop_alpha_product #t #f a0 b0 d0 fuel;
    let at = yun_loop_alpha #t #f a0 b0 d0 fuel in
    (* at has degree 0 *)
    yun_loop_alpha_constant #t #f a0 b0 d0 fuel;
    (* deg(at) == Some 0, so at == [poly_lc at] with poly_lc at ≠ zero *)
    degree_zero_is_singleton at;
    let c = poly_lc at in
    let cinv = f.f_sf.sf_mig.inv c in
    (* singleton_inv_mul_singleton: [cinv] * [c] ≈ poly_one *)
    singleton_inv_mul_singleton #t #f c;
    (* Since at == [c], we have [cinv] * at == [cinv] * [c] ≈ poly_one *)
    (* From yun_pp_divides_p logic: PP * at ≈ p *)
    (* Reproduce the chain: PP * at ≈ (b0*bp)*at ≈ b0*(bp*at) ≈ b0*a0 ≈ a0*b0 ≈ p *)
    poly_mul_associativity b0 bp at;
    poly_eq_symmetry (poly_mul (poly_mul b0 bp) at) (poly_mul b0 (poly_mul bp at));
    poly_mul_congruence pp at (poly_mul b0 bp) at;
    poly_eq_transitivity (poly_mul pp at) (poly_mul (poly_mul b0 bp) at)
                         (poly_mul b0 (poly_mul bp at));
    poly_eq_reflexivity b0;
    poly_mul_congruence b0 (poly_mul bp at) b0 a0;
    poly_eq_transitivity (poly_mul pp at) (poly_mul b0 (poly_mul bp at)) (poly_mul b0 a0);
    poly_mul_commutativity b0 a0;
    poly_eq_transitivity (poly_mul pp at) (poly_mul b0 a0) (poly_mul a0 b0);
    poly_eq_transitivity (poly_mul pp at) (poly_mul a0 b0) p;
    (* Now: poly_eq (poly_mul pp at) p *)
    (* Step 1: p * [cinv] ≈ (PP * at) * [cinv] *)
    let cinv_p : polynomial t = [cinv] in
    poly_eq_symmetry (poly_mul pp at) p;
    poly_eq_reflexivity cinv_p;
    poly_mul_congruence p cinv_p (poly_mul pp at) cinv_p;
    (* Step 2: (PP * at) * [cinv] ≈ PP * (at * [cinv]) *)
    poly_mul_associativity pp at cinv_p;
    poly_eq_transitivity (poly_mul p cinv_p)
                         (poly_mul (poly_mul pp at) cinv_p)
                         (poly_mul pp (poly_mul at cinv_p));
    (* Step 3: at * [cinv] ≈ poly_one *)
    (* at == [c], so poly_mul at cinv_p == poly_mul [c] [cinv] *)
    (* By commutativity: poly_mul [c] [cinv] ≈ poly_mul [cinv] [c] *)
    (* singleton_inv_mul_singleton gives: poly_mul [cinv] [c] ≈ poly_one *)
    let c_p : polynomial t = [c] in
    poly_mul_commutativity c_p cinv_p;
    (* poly_eq (poly_mul [c] [cinv]) (poly_mul [cinv] [c]) *)
    poly_eq_transitivity (poly_mul c_p cinv_p) (poly_mul cinv_p c_p) (poly_one #t);
    (* Now: poly_eq (poly_mul [c] [cinv]) (poly_one #t) *)
    (* Since at == [c], poly_mul at cinv_p == poly_mul c_p cinv_p *)
    assert (at == c_p);
    assert (poly_mul at cinv_p == poly_mul c_p cinv_p);
    (* Bridge: poly_eq (poly_mul at cinv_p) poly_one *)
    poly_eq_reflexivity pp;
    poly_mul_congruence pp (poly_mul at cinv_p) pp (poly_one #t);
    poly_eq_transitivity (poly_mul p cinv_p)
                         (poly_mul pp (poly_mul at cinv_p))
                         (poly_mul pp (poly_one #t));
    (* Step 4: PP * poly_one ≈ PP *)
    poly_mul_one pp;
    poly_eq_transitivity (poly_mul p cinv_p) (poly_mul pp (poly_one #t)) pp;
    (* poly_eq (poly_mul p cinv_p) pp *)
    poly_eq_symmetry (poly_mul p cinv_p) pp;
    (* poly_eq pp (poly_mul p cinv_p) *)
    (* Establish divides p pp *)
    poly_eq_reflexivity (poly_mul p cinv_p);
    divides_intro p (poly_mul p cinv_p) cinv_p;
    divides_congruence_right p (poly_mul p cinv_p) pp;
    (* Bridge: pp == powered_product (yun p) *)
    yun_unfold #t #f p;
    assert (pp == powered_product (yun #t #f p))
#pop-options

(* ================================================================ *)
(*  THEOREM: p and PP(yun(p)) are associates (mutual divisibility)  *)
(* ================================================================ *)

let yun_associates (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires char_zero f /\ Some? (poly_deg p) /\ Some?.v (poly_deg p) >= 1)
          (ensures  divides #(polynomial t) (powered_product (yun #t #f p)) p /\
                   divides #(polynomial t) p (powered_product (yun #t #f p)))
  = yun_pp_divides_p #t #f p;
    yun_p_divides_pp #t #f p
