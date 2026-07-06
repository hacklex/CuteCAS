module Core.Risch.HermiteFracLift

(*
   Rational-derivative power-quotient reduction.

   Reconciles the naive quotient rule applied to  nn / d^(n-1)  with the
   reduced Hermite denominator  d^n :

     D( nn / d^(n-1) )  =  ( nn'·d − (n-1)·nn·d' ) / d^n

   where the scalar (n-1) appears as the constant polynomial
   `scalar_poly (nat_scale (n-1) one)`.
*)

module H  = Core.Algebra.Helpers
module CR = Core.Tactics.CanonRing

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree
open Core.Polynomial.DerivPower
open Core.Polynomial.Irreducible
open Core.Fractions
open Core.Fractions.Derivative
open Core.Risch.Hermite
open Core.Risch.RTSoundness

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* ================================================================ *)
(*  Helper: nat_scale at poly level  =  scalar_poly multiplication   *)
(*                                                                   *)
(*    k·p  (repeated poly_add)  ≈  [k·1] · p                         *)
(* ================================================================ *)

#push-options "--z3rlimit 20 --fuel 2"
let rec nat_scale_poly_scalar (#t:Type) {| f: field t |} (k: nat) (p: polynomial t)
  : Lemma (ensures
             (nat_scale k p)
             = ((scalar_poly (nat_scale k (one #t))) * p))
          (decreases k)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if k = 0 then begin
      (* LHS: nat_scale 0 p == poly_zero (the acg zero). *)
      nat_scale_zero p;
      (* nat_scale 0 (one:t) == zero:t, so scalar_poly(...) == scalar_poly zero == poly_zero. *)
      nat_scale_zero (one #t);
      (* scalar_poly zero == poly_zero  definitionally (c = zero branch). *)
      (* poly_mul poly_zero p ≈ poly_zero. *)
      H.zero_mul_x p;
      (* Both sides ≈ poly_zero. *)
      poly_eq_symmetry
        ((scalar_poly (nat_scale 0 (one #t))) * p)
        (poly_zero #t);
      poly_eq_transitivity
        (nat_scale 0 p)
        (poly_zero #t)
        ((scalar_poly (nat_scale 0 (one #t))) * p)
    end
    else begin
      let k1 = k - 1 in
      (* LHS: nat_scale k p == p + nat_scale (k-1) p   (nat_scale_succ). *)
      nat_scale_succ k1 p;
      assert ((k1 ++ 1) == k);
      (* IH on k1. *)
      nat_scale_poly_scalar k1 p;
      (* nat_scale k1 p ≈ poly_mul (scalar_poly (nat_scale k1 one)) p *)
      let skm = scalar_poly (nat_scale k1 (one #t)) in
      let sk  = scalar_poly (nat_scale k  (one #t)) in
      (* LHS ≈ p + (skm · p)  via add congruence *)
      poly_add_congruence
        p (nat_scale k1 p)
        p (skm * p);
      (* p ≈ poly_mul poly_one p  (poly_one · p ≈ p, then symmetry) *)
      poly_mul_one p;
      poly_eq_symmetry ((poly_one #t) * p) p;
      poly_add_congruence
        p (skm * p)
        ((poly_one #t) * p) (skm * p);
      (* poly_mul poly_one p + poly_mul skm p ≈ poly_mul (poly_one + skm) p  (right distrib, reversed) *)
      poly_right_distributivity p (poly_one #t) skm;
      poly_eq_symmetry
        (((poly_one #t) + skm) * p)
        (((poly_one #t) * p) + (skm * p));
      (* scalar_poly_succ: sk ≈ poly_add skm poly_one ; we need poly_add poly_one skm.
         Build sk ≈ poly_add poly_one skm via commutativity. *)
      scalar_poly_succ #t k1;          (* sk ≈ poly_add skm poly_one *)
      poly_add_commutativity skm (poly_one #t);  (* poly_add skm one ≈ poly_add one skm *)
      poly_eq_transitivity sk (skm + (poly_one #t)) ((poly_one #t) + skm);
      (* poly_mul (poly_add one skm) p ≈ poly_mul sk p  via left congruence on the product. *)
      poly_eq_symmetry sk ((poly_one #t) + skm);
      poly_mul_congruence
        ((poly_one #t) + skm) p sk p;
      (* Now chain everything together by transitivity. *)
      poly_eq_transitivity
        (((poly_one #t) * p) + (skm * p))
        (((poly_one #t) + skm) * p)
        (sk * p);
      poly_eq_transitivity
        (p + (skm * p))
        (((poly_one #t) * p) + (skm * p))
        (sk * p);
      poly_eq_transitivity
        (p + (nat_scale k1 p))
        (p + (skm * p))
        (sk * p);
      poly_eq_transitivity
        (nat_scale k p)
        (p + (nat_scale k1 p))
        (sk * p)
    end
#pop-options

(* ================================================================ *)
(*  Nonzero bridges                                                  *)
(* ================================================================ *)

(* is_nonzero p  <==>  deg p >= 0  for polynomials. *)
private let nonzero_iff_some_deg (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (is_nonzero p <==> deg p >= 0)
  = poly_zero_is_unique p
    (* poly_eq p poly_zero <==> p == []; deg [] == -1; deg >= 0 iff length>0 *)

(* poly_power of a nonzero polynomial is nonzero. *)
private let poly_power_nonzero (#t:Type) {| f: field t |}
  (d: polynomial t) (k: nat)
  : Lemma (requires is_nonzero d)
          (ensures  is_nonzero (poly_power d k))
  = if k = 0 then
      (* poly_power d 0 == poly_one, which is nonzero in an integral domain. *)
      polynomial_one_ne_zero #t #_
    else begin
      nonzero_iff_some_deg d;                 (* deg d >= 0 *)
      poly_power_has_degree d k;               (* deg (poly_power d k) >= 0 *)
      nonzero_iff_some_deg (poly_power d k)
    end

(* SMT-patterned variant so that `Fraction nn (poly_power d k)` typechecks. *)
private let poly_power_nonzero_pat (#t:Type) {| f: field t |}
  (d: polynomial t) (k: nat)
  : Lemma (requires is_nonzero d)
          (ensures  is_nonzero (poly_power d k))
          [SMTPat (poly_power d k)]
  = poly_power_nonzero d k

(* ================================================================ *)
(*  MAIN: D( nn / d^(n-1) ) = ( nn'·d − (n-1)·nn·d' ) / d^n          *)
(* ================================================================ *)

(* The cross-multiplied polynomial identity (GOAL-X) behind the main
   reduction.  dm = d^(n-1), dn = d^n, dm' = D(dm).

     num_rd · dn  ≈  (dm·dm) · rhs_num

   where  num_rd = nn'·dm − nn·dm'  and  rhs_num = nn'·d − km1·(nn·d'). *)
(* Generic ring identity behind the n=1 case: with dm ≡ one and dn ≡ d·one,
     (a'·one)·(d·one)  =  (one·one)·(a'·d). *)
private let base_ring_id (#r:Type) {| cr: commutative_ring r |} (a' d: r)
  : Lemma ((a' * one) * (d * one) = (one * one) * (a' * d))
  = assert ((a' * one) * (d * one) = (one * one) * (a' * d))
      by (CR.canon_ring ())

(* Generic ring identity behind the n≥2 case.  Atoms:
     a = nn, a' = nn', k = km1, e = d, e' = d', w = d^(n-2).
   With dm ≡ e·w and dn ≡ e·(e·w),
     num_rd · dn  =  (dm·dm) · rhs_num
   becomes
     ((a'·(e·w)) − (a·(k·(w·e')))) · (e·(e·w))
       = (((e·w)·(e·w)) · ((a'·e) − (k·(a·e')))). *)
private let step_ring_id (#r:Type) {| cr: commutative_ring r |} (a a' k e e' w: r)
  : Lemma (
      (((a' * (e * w)) -- (a * (k * (w * e')))) * (e * (e * w)))
      = (((e * w) * (e * w)) * ((a' * e) -- (k * (a * e')))))
  = assert (
      (((a' * (e * w)) -- (a * (k * (w * e')))) * (e * (e * w)))
      = (((e * w) * (e * w)) * ((a' * e) -- (k * (a * e')))))
      by (CR.canon_ring ())

(* --- n = 1 case --- *)
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private let cross_goal_base (#t:Type) {| f: field t |}
  (nn d: polynomial t)
  : Lemma (requires is_nonzero d)
          (ensures
              (((poly_deriv nn * poly_power d 0)
                -- (nn * poly_deriv (poly_power d 0)))
               * poly_power d 1)
              = ((poly_power d 0 * poly_power d 0)
                 * ((poly_deriv nn * d)
                    -- (scalar_poly (nat_scale 0 (one #t))
                          * (nn * poly_deriv d)))))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let d'  = poly_deriv d in
    let nn' = poly_deriv nn in
    (* dm = poly_power d 0 == poly_one  (defeq) *)
    let dm  = poly_power d 0 in
    (* dn = poly_power d 1 == poly_mul d (poly_power d 0) == poly_mul d poly_one (defeq) *)
    let dn  = poly_power d 1 in
    let dm' = poly_deriv dm in
    let km1 : polynomial t = scalar_poly (nat_scale 0 (one #t)) in
    (* dm == poly_one, so length 1, so dm' == poly_zero *)
    polynomial_one_ne_zero #t #_;
    assert (dm == poly_one #t);
    poly_deriv_const dm;          (* dm' == poly_zero *)
    assert (dm' == poly_zero #t);
    (* km1 == scalar_poly zero == poly_zero (defeq via nat_scale 0 one == zero) *)
    nat_scale_zero (one #t);
    assert (km1 == poly_zero #t);
    let num_rd : polynomial t = (nn' * dm) -- (nn * dm') in
    let rhs_num : polynomial t = (nn' * d) -- (km1 * (nn * d')) in
    (* num_rd = (nn'·1) -- (nn·0).  poly_mul nn poly_zero ≈ poly_zero. *)
    H.x_mul_zero nn;     (* poly_mul nn poly_zero ≈ poly_zero *)
    (* rhs_num = (nn'·d) -- (poly_zero·(nn·d')).  poly_mul poly_zero X ≈ poly_zero. *)
    H.zero_mul_x (nn * d');
    (* Both subtracted terms ≈ poly_zero; the whole identity is then a ring
       identity in atoms nn', d (since dm ≡ 1, dn ≡ d·1, dm·dm ≡ 1·1). *)
    assert ((nn * dm') = (poly_zero #t));
    assert ((km1 * (nn * d')) = (poly_zero #t));
    (* num_rd ≈ poly_mul nn' poly_one ; rhs_num ≈ poly_mul nn' d *)
    poly_neg_congruence (nn * dm') (poly_zero #t);
    poly_neg_zero #t #_;
    poly_add_congruence
      (nn' * dm) (- (nn * dm'))
      (nn' * dm) (poly_zero #t);
    poly_add_zero (nn' * dm);
    poly_eq_transitivity num_rd ((nn' * dm) + (poly_zero #t)) (nn' * dm);
    (* num_rd ≈ poly_mul nn' dm , and dm ≡ poly_one *)
    poly_neg_congruence (km1 * (nn * d')) (poly_zero #t);
    poly_add_congruence
      (nn' * d) (- (km1 * (nn * d')))
      (nn' * d) (poly_zero #t);
    poly_add_zero (nn' * d);
    poly_eq_transitivity rhs_num ((nn' * d) + (poly_zero #t)) (nn' * d);
    (* Now: LHS = poly_mul num_rd dn ≈ poly_mul (poly_mul nn' dm) dn
       RHS = poly_mul (poly_mul dm dm) rhs_num ≈ poly_mul (poly_mul dm dm) (poly_mul nn' d).
       With dm ≡ poly_one, dn ≡ poly_mul d poly_one, this is a ring identity. *)
    poly_mul_congruence num_rd dn (nn' * dm) dn;
    poly_mul_congruence (dm * dm) rhs_num (dm * dm) (nn' * d);
    (* Ring identity:  (nn'·dm)·dn  ≈  (dm·dm)·(nn'·d)
       holds because dm ≡ poly_one and dn ≡ poly_mul d poly_one. *)
    base_ring_id nn' d;
    (* base_ring_id gives:
         (nn'·one)·(d·one) = (one·one)·(nn'·d)   in polynomial t.
       dm ≡ poly_one and dn ≡ poly_mul d poly_one defeq, so this is exactly
       the needed identity. *)
    assert (((nn' * dm) * dn)
            = ((dm * dm) * (nn' * d)));
    poly_eq_transitivity
      (num_rd * dn)
      ((nn' * dm) * dn)
      ((dm * dm) * (nn' * d));
    poly_eq_symmetry
      ((dm * dm) * rhs_num)
      ((dm * dm) * (nn' * d));
    poly_eq_transitivity
      (num_rd * dn)
      ((dm * dm) * (nn' * d))
      ((dm * dm) * rhs_num)
#pop-options

(* --- n >= 2 case --- *)
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private let cross_goal_step (#t:Type) {| f: field t |}
  (nn d: polynomial t) (n: nat{n >= 2})
  : Lemma (requires is_nonzero d)
          (ensures
              (((poly_deriv nn * poly_power d (n - 1))
                -- (nn * poly_deriv (poly_power d (n - 1))))
               * poly_power d n)
              = ((poly_power d (n - 1) * poly_power d (n - 1))
                 * ((poly_deriv nn * d)
                    -- (scalar_poly (nat_scale (n - 1) (one #t))
                          * (nn * poly_deriv d)))))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let d'  = poly_deriv d in
    let nn' = poly_deriv nn in
    let dm  = poly_power d (n - 1) in     (* d^(n-1) *)
    let dn  = poly_power d n in           (* d^n,  defeq poly_mul d dm *)
    let dn2 = poly_power d (n - 2) in     (* d^(n-2),  dm defeq poly_mul d dn2 *)
    let dm' = poly_deriv dm in
    let km1 : polynomial t = scalar_poly (nat_scale (n - 1) (one #t)) in
    let xX : polynomial t = dn2 * d' in   (* d^(n-2)·d' *)
    (* --- Step 1: dm' ≈ km1 · (dn2·d') --- *)
    poly_deriv_power d (n - 1);
    (* dm' ≈ nat_scale (n-1) (poly_mul (poly_power d (n-2)) d') = nat_scale (n-1) xX *)
    nat_scale_poly_scalar (n - 1) xX;
    (* nat_scale (n-1) xX ≈ poly_mul km1 xX *)
    poly_eq_transitivity
      dm'
      (nat_scale (n - 1) xX)
      (km1 * xX);
    (* dm' ≈ poly_mul km1 xX *)
    (* --- Step 2: num_rd ≈ (nn'·dm) -- (nn·(km1·xX)) --- *)
    let num_rd : polynomial t = (nn' * dm) -- (nn * dm') in
    let rhs_num : polynomial t = (nn' * d) -- (km1 * (nn * d')) in
    (* nn·dm' ≈ nn·(km1·xX) *)
    poly_mul_right_congruence nn dm' (km1 * xX);
    poly_neg_congruence (nn * dm') (nn * (km1 * xX));
    poly_add_congruence
      (nn' * dm) (- (nn * dm'))
      (nn' * dm) (- (nn * (km1 * xX)));
    let num_rd2 : polynomial t = (nn' * dm) -- (nn * (km1 * xX)) in
    (* num_rd ≈ num_rd2 *)
    poly_mul_congruence num_rd dn num_rd2 dn;
    (* poly_mul num_rd dn ≈ poly_mul num_rd2 dn *)
    (* --- Step 3: ring identity over explicit power products --- *)
    step_ring_id nn nn' km1 d d' dn2;
    (* step_ring_id gives, with e=d, w=dn2:
         ((nn'·(d·dn2)) -- (nn·(km1·(dn2·d')))) · (d·(d·dn2))
           = ((d·dn2)·(d·dn2)) · ((nn'·d) -- (km1·(nn·d')))
       Now: dm ≡ poly_mul d dn2,  dn ≡ poly_mul d dm ≡ poly_mul d (poly_mul d dn2),
       and dm·dm ≡ (d·dn2)·(d·dn2)  [defeq], so this is exactly
         poly_mul num_rd2 dn ≈ poly_mul (poly_mul dm dm) rhs_num. *)
    poly_eq_transitivity
      (num_rd * dn)
      (num_rd2 * dn)
      ((dm * dm) * rhs_num)
#pop-options

private let cross_goal (#t:Type) {| f: field t |}
  (nn d: polynomial t) (n: nat{n >= 1})
  : Lemma (requires is_nonzero d)
          (ensures
              (((poly_deriv nn * poly_power d (n - 1))
                -- (nn * poly_deriv (poly_power d (n - 1))))
               * poly_power d n)
              = ((poly_power d (n - 1) * poly_power d (n - 1))
                 * ((poly_deriv nn * d)
                    -- (scalar_poly (nat_scale (n - 1) (one #t))
                          * (nn * poly_deriv d)))))
  = if n = 1 then cross_goal_base nn d
    else cross_goal_step nn d n

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let rational_deriv_power_quotient (#t:Type) {| f: field t |}
  (nn d: polynomial t) (n: nat{n >= 1})
  : Lemma (requires is_nonzero d)
          (ensures
            rational_deriv (Fraction nn (poly_power d (n - 1)))
            = Fraction
                ((poly_deriv nn * d)
                 -- (scalar_poly (nat_scale (n - 1) (one #t))
                       * (nn * poly_deriv d)))
                (poly_power d n))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let d'  = poly_deriv d in
    let nn' = poly_deriv nn in
    let dm  = poly_power d (n - 1) in
    let dn  = poly_power d n in
    let dm' = poly_deriv dm in
    let km1 : polynomial t = scalar_poly (nat_scale (n - 1) (one #t)) in
    let rhs_num : polynomial t = (nn' * d) -- (km1 * (nn * d')) in
    let xfrac = Fraction nn dm in
    let yfrac = Fraction rhs_num dn in
    (* num/den of D(xfrac) *)
    rational_deriv_reveal xfrac;
    (* Fraction?.num (rational_deriv xfrac) == (nn'*dm) -- (nn*dm')
       Fraction?.den (rational_deriv xfrac) == poly_mul dm dm *)
    let rd = rational_deriv xfrac in
    let num_rd : polynomial t = (nn' * dm) -- (nn * dm') in
    (* Cross-multiplication identity. *)
    cross_goal nn d n;
    (* poly_eq (poly_mul num_rd dn) (poly_mul (poly_mul dm dm) rhs_num) *)
    (* fraction_eq_reveal: (rd = yfrac) <==> (num rd * den yfrac) = (den rd * num yfrac) *)
    fraction_eq_reveal rd yfrac
#pop-options

(* ================================================================ *)
(*  HERMITE FRACTION IDENTITY                                        *)
(*                                                                   *)
(*     D( nn / d^(n-1) )  +  final/d   =   rem / d^n                 *)
(*                                                                   *)
(*  Closes the Hermite part of the rational-integrator soundness.    *)
(* ================================================================ *)

(* Pure ring cross-product identity behind the fraction identity.

   With the power relation dn ≡ d·dm baked in as (d * dm), and
   rem ≡ hn + final·dm substituted on the RHS, the cross-multiplied
   goal
       (hn·d + dn·final)·dn  =  (dn·d)·rem
   becomes the closed ring identity
       (hn·d + (d·dm)·final)·(d·dm) = ((d·dm)·d)·(hn + final·dm).      *)
private let hermite_cross_id (#r:Type) {| cr: commutative_ring r |}
  (hn final d dm: r)
  : Lemma (((hn * d + (d * dm) * final) * (d * dm))
             = (((d * dm) * d) * (hn + final * dm)))
  = assert (((hn * d + (d * dm) * final) * (d * dm))
              = (((d * dm) * d) * (hn + final * dm)))
      by (CR.canon_ring ())

(* The same-denominator combine step, lifted to fractions:
     (HN / d^n)  +  (final / d)   =   rem / d^n
   given the polynomial identity  rem ≈ HN + final·d^(n-1). *)
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
private let hermite_combine_step (#t:Type) {| f: field t |}
  (rem final hn d: polynomial t) (n: nat{n >= 1})
  : Lemma (requires
            is_nonzero d /\
            rem
              = (hn + (final * (poly_power d (n - 1)))))
          (ensures
            (fraction_add
               (Fraction hn (poly_power d n))
               (Fraction final d))
            = Fraction rem (poly_power d n))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let dm = poly_power d (n - 1) in
    let dn = poly_power d n in
    (* dn == poly_mul d dm  definitionally (n >= 1). *)
    let lhs = fraction_add
                (Fraction hn dn)
                (Fraction final d) in
    let rhs = Fraction rem dn in
    (* num/den of the fraction sum. *)
    fraction_add_reveal
      (Fraction hn dn)
      (Fraction final d);
    (* Fraction?.num lhs == (hn * d) + (dn * final)
       Fraction?.den lhs == dn * d *)
    (* (lhs = rhs) <==> (num lhs * den rhs) = (den lhs * num rhs) *)
    fraction_eq_reveal lhs rhs;
    (* Goal reduces to:
         ((hn*d + dn*final) * dn) = ((dn*d) * rem)
       With dn == d*dm (defeq), the LHS matches the helper's LHS. *)
    let crem : polynomial t = hn + (final * dm) in
    (* RHS congruence: (dn*d)*rem  ≈  (dn*d)*crem   since rem ≈ crem. *)
    poly_mul_right_congruence (dn * d) rem crem;
    (* Helper ring identity (with dn ≡ d*dm baked in defeq):
         (hn*d + (d*dm)*final)*(d*dm) = ((d*dm)*d)*(hn + final*dm). *)
    hermite_cross_id hn final d dm;
    (* chain:  (hn*d + dn*final)*dn  ≈  (dn*d)*crem  ≈[sym]  (dn*d)*rem *)
    poly_eq_symmetry ((dn * d) * rem) ((dn * d) * crem);
    poly_eq_transitivity
      (((hn * d) + (dn * final)) * dn)
      ((dn * d) * crem)
      ((dn * d) * rem)
#pop-options

#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let hermite_fraction_identity (#t:Type) {| f: field t |}
  (rem d: polynomial t) (n: nat{n >= 1})
  : Lemma (requires deg d >= 0 /\ square_free d /\ char_zero f)
          (ensures
            (fraction_add
               (rational_deriv
                  (Fraction
                     (combined_num (fst (hermite_reduce_power rem d n)) d)
                     (poly_power d (n - 1))))
               (Fraction (snd (hermite_reduce_power rem d n)) d))
            = Fraction rem (poly_power d n))
  = let (parts, final) = hermite_reduce_power rem d n in
    let nn   = combined_num parts d in
    let d'   = poly_deriv d in
    let nn'  = poly_deriv nn in
    let km1 : polynomial t =
      scalar_poly (nat_scale (n - 1) (one #t)) in
    let hn : polynomial t = (nn' * d) -- (km1 * (nn * d')) in
    let dm = poly_power d (n - 1) in
    let dn = poly_power d n in
    (* (1) is_nonzero d. *)
    nonzero_iff_some_deg d;
    (* (2) rational_deriv (nn / d^(n-1)) = Fraction hn (d^n). *)
    rational_deriv_power_quotient nn d n;
    let rd = rational_deriv (Fraction nn dm) in
    let yfrac = Fraction hn dn in
    (* rd = yfrac. *)
    let ffinal = Fraction final d in
    (* (3) left congruence: fraction_add rd ffinal = fraction_add yfrac ffinal. *)
    frac_add_cong rd yfrac ffinal;
    (* (4) the same-denominator combine, using hermite_reduce_power_correct. *)
    hermite_reduce_power_correct rem d n;
    (* hermite_reduce_power_correct gives rem ≈ hn + final·dm  (same hn, km1 forms). *)
    hermite_combine_step rem final hn d n;
    (* (5) chain via transitivity over fraction id_p. *)
    transitivity
      (fraction_add rd ffinal)
      (fraction_add yfrac ffinal)
      (Fraction rem dn)
#pop-options
