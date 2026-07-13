module Core.Risch.RationalFull

(* ================================================================ *)
(*  M1 — the MULTI-FACTOR rational integrator (∫ p/q, q general).     *)
(*                                                                   *)
(*  Composes the single-factor pipeline over a squarefree            *)
(*  factorization  q ~ ∏ᵢ bᵢ^{eᵢ}  (Yun):                            *)
(*    (a) poly division   p = s·q + r                                *)
(*    (b) Yun factor q into (bᵢ, eᵢ)                                 *)
(*    (c) partial fraction  r/q = Σᵢ rᵢ/bᵢ^{eᵢ}   (list PF over      *)
(*        pairwise-coprime moduli, via partial_fraction_two)         *)
(*    (d) integrate_rational_single_factor on each rᵢ/bᵢ^{eᵢ}        *)
(*    (e) collect poly_part / hermite_rational / log_parts           *)
(*                                                                   *)
(*  Reusable core:                                                   *)
(*    pf_two_num_sound       — r = a1·d2 + a2·d1  (PF numerator id)   *)
(*    pf_two_frac_sound      — r/(d1·d2) = a1/d1 (+) a2/d2            *)
(*    pf_split               — executable n-ary PF numerators         *)
(*    pf_frac_sum(_sound)    — n-ary PF decomposition r/∏ms = Σ rᵢ/mᵢ *)
(*    integrate_rational_multi          — executable integrator       *)
(*    integrate_rational_multi_sound_split — D(answer) = p/(∏ms)      *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module PA = Core.Risch.PolyAntideriv
module CR = Core.Tactics.CanonRing

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.GCD
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree
open Core.Polynomial.Roots
open Core.Polynomial.Irreducible
open Core.Polynomial.PartialFraction
open Core.Polynomial.CRT
open Core.Polynomial.CRTMulti
open Core.Fractions
open Core.Fractions.Derivative
open Core.Fractions.DerivativeSum
open Core.Risch.RationalSound
open Core.Risch.RationalEuclid
open Core.Risch.RTSoundness
open Core.Risch.LRT
open Core.Risch.Rational
open Core.Risch.RationalSplitField

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ================================================================ *)
(*  deg >= 0  ==>  is_nonzero                                         *)
(* ================================================================ *)
let deg_nonneg_nonzero (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (requires deg p >= 0) (ensures is_nonzero p)
  = poly_zero_is_unique p

(* ================================================================ *)
(*  Pure ring identities (clean-env helpers; canon_ring is reliable   *)
(*  here but flaky in a large proof context).                        *)
(* ================================================================ *)
private let add_sub_cancel_l (#t:Type) {| cr: commutative_ring t |} (a b: t)
  : Lemma (((a + b) -- a) = b) = assert (((a + b) -- a) = b) by (CR.canon_ring ())

private let add_sub_cancel_r (#t:Type) {| cr: commutative_ring t |} (a b: t)
  : Lemma (((a + b) -- b) = a) = assert (((a + b) -- b) = a) by (CR.canon_ring ())

(* ((r·(s·d1 + t·d2)) -- (r·t)·d2)  =  d1·(r·s). *)
private let bez_term1 (#t:Type) {| cr: commutative_ring t |} (r s d1 tt d2: t)
  : Lemma (((r * ((s * d1) + (tt * d2))) -- ((r * tt) * d2)) = (d1 * (r * s)))
  = assert (((r * ((s * d1) + (tt * d2))) -- ((r * tt) * d2)) = (d1 * (r * s)))
      by (CR.canon_ring ())

(* (r -- (r·t)·d2) + ((r·t -- a1)·d2)  =  r -- a1·d2. *)
private let pf_decomp (#t:Type) {| cr: commutative_ring t |} (r tt d2 a1: t)
  : Lemma (((r -- ((r * tt) * d2)) + (((r * tt) -- a1) * d2)) = (r -- (a1 * d2)))
  = assert (((r -- ((r * tt) * d2)) + (((r * tt) -- a1) * d2)) = (r -- (a1 * d2)))
      by (CR.canon_ring ())

(* ================================================================ *)
(*  (Step 2)  Partial-fraction NUMERATOR soundness.                  *)
(*    For coprime d1 d2 (both nonconstant-or-constant, deg >= 0),     *)
(*    partial_fraction_two r d1 d2 = (a1, a2)  satisfies              *)
(*        r  =  a1·d2 + a2·d1.                                        *)
(* ================================================================ *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let pf_two_num_sound (#t:Type) {| f: field t |} (r d1 d2: polynomial t)
  : Lemma (requires deg d1 >= 0 /\ deg d2 >= 0 /\ coprime d1 d2)
          (ensures (let (a1, a2) = partial_fraction_two r d1 d2 in
                    r = ((a1 * d2) + (a2 * d1))))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let (s_norm, t_norm) = normalize_bezout d1 d2 in
    normalize_bezout_correct d1 d2;           (* EQ_bez: ((s_norm*d1)+(t_norm*d2)) = poly_one *)
    let sum : polynomial t = (s_norm * d1) + (t_norm * d2) in
    let qq1 : polynomial t = poly_div (r * t_norm) d1 in  (* r*t_norm = d1*qq1 + a1 *)
    let a1  : polynomial t = poly_rem (r * t_norm) d1 in
    let remainder : polynomial t = r -- (a1 * d2) in
    let a2  : polynomial t = poly_div remainder d1 in
    let rem2 : polynomial t = poly_rem remainder d1 in    (* remainder = d1*a2 + rem2 *)
    (* the pair from partial_fraction_two is (a1, a2) definitionally *)
    assert ((a1, a2) == partial_fraction_two r d1 d2);

    (* ---- term1 = r -- (r*t_norm)*d2 ;  divides d1 term1  (via bezout) ---- *)
    let term1 : polynomial t = r -- ((r * t_norm) * d2) in
    (* r = r * sum   (EQ_bez: sum = poly_one) *)
    mul_congruence r sum r (poly_one #t);     (* (r*sum) = (r*poly_one) *)
    mul_one r;                                (* (r*poly_one) = r *)
    transitivity (r * sum) (r * (poly_one #t)) r;
    symmetry (r * sum) r;                     (* r = (r*sum) *)
    (* rewrite the leading r of term1 to (r*sum) *)
    add_congruence r (- ((r * t_norm) * d2)) (r * sum) (- ((r * t_norm) * d2));
    bez_term1 r s_norm d1 t_norm d2;
    transitivity term1 ((r * sum) -- ((r * t_norm) * d2)) (d1 * (r * s_norm));
    divides_intro d1 term1 (r * s_norm);

    (* ---- term2 = ((r*t_norm) -- a1)*d2 ;  divides d1 term2 ---- *)
    (* poly_div ensures: (r*t_norm) = (d1*qq1) + a1, so d1 | ((r*t_norm) -- a1) *)
    add_congruence (r * t_norm) (- a1) ((d1 * qq1) + a1) (- a1);
    add_sub_cancel_r (d1 * qq1) a1;           (* ((d1*qq1)+a1) -- a1 = d1*qq1 *)
    transitivity ((r * t_norm) -- a1) (((d1 * qq1) + a1) -- a1) (d1 * qq1);
    divides_intro d1 ((r * t_norm) -- a1) qq1;
    let term2 : polynomial t = ((r * t_norm) -- a1) * d2 in
    divides_mul_right d1 ((r * t_norm) -- a1) d2;

    (* ---- divides d1 remainder  (= term1 + term2) ---- *)
    divides_add d1 term1 term2;
    pf_decomp r t_norm d2 a1;                 (* (term1 + term2) = remainder *)
    divides_congruence_right d1 (term1 + term2) remainder;

    (* ---- rem2 = 0 : d1 | rem2 and deg rem2 < deg d1 ---- *)
    divides_refl d1;
    divides_mul_right d1 d1 a2;               (* d1 | d1*a2 *)
    divides_sub d1 remainder (d1 * a2);       (* d1 | (remainder -- d1*a2) *)
    (* remainder = (d1*a2)+rem2, so (remainder -- d1*a2) = rem2 *)
    add_congruence remainder (- (d1 * a2)) ((d1 * a2) + rem2) (- (d1 * a2));
    add_sub_cancel_l (d1 * a2) rem2;          (* ((d1*a2)+rem2) -- (d1*a2) = rem2 *)
    transitivity (remainder -- (d1 * a2)) (((d1 * a2) + rem2) -- (d1 * a2)) rem2;
    divides_congruence_right d1 (remainder -- (d1 * a2)) rem2;
    if deg rem2 >= 0 then divides_degree_le d1 rem2;   (* forces deg d1 <= deg rem2 < deg d1 *)
    degree_none_poly_eq_zero rem2;            (* rem2 = poly_zero *)

    (* ---- remainder = d1*a2 ---- *)
    (* remainder = (d1*a2)+rem2 = (d1*a2)+0 = d1*a2 *)
    symmetry remainder ((d1 * a2) + rem2);    (* ((d1*a2)+rem2) = remainder *)
    add_congruence (d1 * a2) rem2 (d1 * a2) (poly_zero #t);
    H.x_plus_zero (d1 * a2);                  (* ((d1*a2)+0) = (d1*a2) *)
    transitivity ((d1 * a2) + rem2) ((d1 * a2) + (poly_zero #t)) (d1 * a2);
    symmetry ((d1 * a2) + rem2) (d1 * a2);    (* (d1*a2) = ((d1*a2)+rem2) *)
    transitivity remainder ((d1 * a2) + rem2) (d1 * a2);  (* remainder = d1*a2 *)

    (* ---- r = a1*d2 + a2*d1 ---- *)
    (* remainder = d1*a2 (proven) and remainder == (r -- a1*d2) (defeq) *)
    H.sub_to_add r (a1 * d2) (d1 * a2);        (* r = ((a1*d2)+(d1*a2)) *)
    mul_commutativity d1 a2;                   (* (d1*a2) = (a2*d1) *)
    add_congruence (a1 * d2) (d1 * a2) (a1 * d2) (a2 * d1);
    transitivity r ((a1 * d2) + (d1 * a2)) ((a1 * d2) + (a2 * d1))
#pop-options

(* ================================================================ *)
(*  Head / tail projections of the coprimality + degree predicates    *)
(*  (mirrors CRTMulti's private helpers, re-derived here).            *)
(* ================================================================ *)
let tail_pc (#t:Type) {| f: field t |} (m0: polynomial t) (rest: list (polynomial t))
  : Lemma (requires pairwise_coprime (m0 :: rest))
          (ensures  pairwise_coprime rest)
  = let cpf (i:nat{i < L.length rest}) (j:nat{j < L.length rest /\ j <> i})
      : Lemma (coprime (L.index rest i) (L.index rest j))
      = pairwise_coprime_elim (m0 :: rest);
        assert (L.index (m0 :: rest) (i ++ 1) == L.index rest i);
        assert (L.index (m0 :: rest) (j ++ 1) == L.index rest j)
    in
    pairwise_coprime_intro rest cpf

let tail_deg (#t:Type) {| f: field t |} (m0: polynomial t) (rest: list (polynomial t))
  : Lemma (requires all_deg_ge1 (m0 :: rest))
          (ensures  all_deg_ge1 rest)
  = let dpf (k:nat{k < L.length rest}) : Lemma (deg (L.index rest k) >= 1)
      = all_deg_ge1_elim (m0 :: rest);
        assert (L.index (m0 :: rest) (k ++ 1) == L.index rest k)
    in
    all_deg_ge1_intro rest dpf

let head_deg (#t:Type) {| f: field t |} (m0: polynomial t) (rest: list (polynomial t))
  : Lemma (requires all_deg_ge1 (m0 :: rest))
          (ensures  deg m0 >= 1)
  = all_deg_ge1_elim (m0 :: rest);
    assert (L.index (m0 :: rest) 0 == m0)

let head_coprime (#t:Type) {| f: field t |} (m0: polynomial t) (rest: list (polynomial t))
  : Lemma (requires pairwise_coprime (m0 :: rest) /\ deg m0 >= 0)
          (ensures  coprime m0 (poly_prod rest))
  = let cwa_pf (k:nat{k < L.length rest}) : Lemma (coprime m0 (L.index rest k))
      = pairwise_coprime_elim (m0 :: rest);
        assert (L.index (m0 :: rest) 0 == m0);
        assert (L.index (m0 :: rest) (k ++ 1) == L.index rest k)
    in
    coprime_with_all_intro m0 rest cwa_pf;
    coprime_to_prod m0 rest

(* ================================================================ *)
(*  (Step 3)  Executable  n-ary partial-fraction split.              *)
(*    pf_split r ms  =  [r_0; ...; r_{k-1}]  with  r/∏ms = Σ r_i/m_i. *)
(* ================================================================ *)
let rec pf_split (#t:Type) {| f: field t |}
  (r: polynomial t) (ms: list (polynomial t))
  : Pure (list (polynomial t))
         (requires pairwise_coprime ms /\ all_deg_ge1 ms)
         (ensures  fun ns -> L.length ns == L.length ms)
         (decreases ms)
  = match ms with
    | [] -> []
    | m0 :: rest ->
        (match rest with
         | [] -> [r]
         | _ ->
             head_deg m0 rest;                      (* deg m0 >= 1 *)
             head_coprime m0 rest;                  (* coprime m0 (poly_prod rest) *)
             tail_pc m0 rest;                       (* pairwise_coprime rest *)
             tail_deg m0 rest;                      (* all_deg_ge1 rest *)
             deg_prod_nonneg rest;                  (* deg (poly_prod rest) >= 0 *)
             let pr = poly_prod rest in
             let (a0, a2) = partial_fraction_two r m0 pr in
             a0 :: pf_split a2 rest)

(* ================================================================ *)
(*  (Step 3b)  The fraction-level n-ary partial-fraction sum.        *)
(*    pf_frac_sum r ms  =  Σᵢ rᵢ/mᵢ   (same rᵢ as pf_split).          *)
(* ================================================================ *)
#push-options "--z3rlimit 20 --fuel 2 --ifuel 1"
let rec pf_frac_sum (#t:Type) {| f: field t |}
  (r: polynomial t) (ms: list (polynomial t))
  : Pure (rational_function f)
         (requires pairwise_coprime ms /\ all_deg_ge1 ms /\ Cons? ms)
         (ensures  fun _ -> True)
         (decreases ms)
  = let id_p = polynomial_id #t #(id_of_f t) in
    match ms with
    | m0 :: rest ->
      (match rest with
       | [] ->
           head_deg m0 rest;
           deg_nonneg_nonzero m0;
           let e0 : (x:polynomial t{is_nonzero x}) = m0 in
           Fraction #(polynomial t) #id_p r e0
       | _ ->
           head_deg m0 rest;
           head_coprime m0 rest;
           tail_pc m0 rest;
           tail_deg m0 rest;
           deg_prod_nonneg rest;
           let pr = poly_prod rest in
           let (a0, a2) = partial_fraction_two r m0 pr in
           deg_nonneg_nonzero m0;
           let e0 : (x:polynomial t{is_nonzero x}) = m0 in
           fraction_add #(polynomial t) #id_p
             (Fraction #(polynomial t) #id_p a0 e0)
             (pf_frac_sum a2 rest))
#pop-options

(* ================================================================ *)
(*  (Step 2b)  Partial-fraction FRACTION soundness.                  *)
(*    r/(d1·d2)  =  a1/d1  (+)  a2/d2   as fractions.                 *)
(* ================================================================ *)
#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let pf_two_frac_sound (#t:Type) {| f: field t |} (r d1 d2: polynomial t)
  : Lemma (requires deg d1 >= 0 /\ deg d2 >= 0 /\ coprime d1 d2)
          (ensures (let id_p = polynomial_id #t #(id_of_f t) in
                    let prod : polynomial t = d1 * d2 in
                    is_nonzero d1 /\ is_nonzero d2 /\ is_nonzero prod /\
                    (let dd : (x:polynomial t{is_nonzero x}) = prod in
                     let e1 : (x:polynomial t{is_nonzero x}) = d1 in
                     let e2 : (x:polynomial t{is_nonzero x}) = d2 in
                     let (a1, a2) = partial_fraction_two r d1 d2 in
                     (Fraction #(polynomial t) #id_p r dd)
                       = fraction_add (Fraction #(polynomial t) #id_p a1 e1)
                                      (Fraction #(polynomial t) #id_p a2 e2))))
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    deg_nonneg_nonzero d1;
    deg_nonneg_nonzero d2;
    degree_mul d1 d2;
    let prod : polynomial t = d1 * d2 in
    deg_nonneg_nonzero prod;
    pf_two_num_sound r d1 d2;                  (* r = (a1*d2)+(a2*d1) *)
    let dd : (x:polynomial t{is_nonzero x}) = prod in
    let e1 : (x:polynomial t{is_nonzero x}) = d1 in
    let e2 : (x:polynomial t{is_nonzero x}) = d2 in
    let (a1, a2) = partial_fraction_two r d1 d2 in
    let lhs : fraction id_p = Fraction r dd in
    let x1  : fraction id_p = Fraction a1 e1 in
    let x2  : fraction id_p = Fraction a2 e2 in
    let rhs : fraction id_p = fraction_add x1 x2 in
    fraction_add_reveal x1 x2;    (* num rhs = a1*d2 + d1*a2, den rhs = d1*d2 *)
    (* r = num(rhs): (a1*d2)+(a2*d1) = (a1*d2)+(d1*a2) *)
    mul_commutativity a2 d1;                   (* (a2*d1) = (d1*a2) *)
    add_congruence (a1 * d2) (a2 * d1) (a1 * d2) (d1 * a2);
    transitivity r ((a1 * d2) + (a2 * d1)) ((a1 * d2) + (d1 * a2));
    (* cross product:  r*(d1*d2) = (d1*d2)*num(rhs) *)
    let nr : polynomial t = (a1 * d2) + (d1 * a2) in
    mul_congruence r (d1 * d2) nr (d1 * d2);   (* (r*(d1*d2)) = (nr*(d1*d2)) *)
    mul_commutativity nr (d1 * d2);            (* (nr*(d1*d2)) = ((d1*d2)*nr) *)
    transitivity (r * (d1 * d2)) (nr * (d1 * d2)) ((d1 * d2) * nr);
    fraction_eq_reveal lhs rhs
#pop-options

(* ================================================================ *)
(*  (Step 3c)  SOUNDNESS of the n-ary partial-fraction split:         *)
(*      r / (∏ ms)  =  pf_frac_sum r ms   as fractions.               *)
(* ================================================================ *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec pf_frac_sum_sound (#t:Type) {| f: field t |}
  (r: polynomial t) (ms: list (polynomial t))
  : Lemma (requires pairwise_coprime ms /\ all_deg_ge1 ms /\ Cons? ms)
          (ensures (let id_p = polynomial_id #t #(id_of_f t) in
                    is_nonzero (poly_prod ms) /\
                    (let q : (x:polynomial t{is_nonzero x}) = poly_prod ms in
                     (Fraction #(polynomial t) #id_p r q) = pf_frac_sum r ms)))
          (decreases ms)
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    deg_prod_nonneg ms;
    deg_nonneg_nonzero (poly_prod ms);
    match ms with
    | m0 :: rest ->
      (match rest with
       | [] ->
           (* poly_prod [m0] = m0 * poly_one ; pf_frac_sum = Fraction r m0 *)
           head_deg m0 rest;
           deg_nonneg_nonzero m0;
           let q : (x:polynomial t{is_nonzero x}) = poly_prod ms in
           let lhs : fraction id_p = Fraction r q in
           let rhs : fraction id_p = Fraction r m0 in
           (* cross:  r * m0  =  q * r,   q = m0 * poly_one *)
           mul_one m0;                                        (* (m0*poly_one) = m0 *)
           mul_congruence (m0 * (poly_one #t)) r m0 r;        (* ((m0*poly_one)*r) = (m0*r) *)
           mul_commutativity m0 r;                            (* (m0*r) = (r*m0) *)
           transitivity ((m0 * (poly_one #t)) * r) (m0 * r) (r * m0);
           symmetry ((m0 * (poly_one #t)) * r) (r * m0);      (* (r*m0) = ((m0*poly_one)*r) *)
           fraction_eq_reveal lhs rhs
       | _ ->
           head_deg m0 rest;
           head_coprime m0 rest;
           tail_pc m0 rest;
           tail_deg m0 rest;
           deg_prod_nonneg rest;
           deg_nonneg_nonzero m0;
           let pr = poly_prod rest in
           let (a0, a2) = partial_fraction_two r m0 pr in
           let e0 : (x:polynomial t{is_nonzero x}) = m0 in
           (* FACT1:  Fraction r (m0*pr) = (Fraction a0 m0) (+) (Fraction a2 pr) *)
           pf_two_frac_sound r m0 pr;
           (* FACT2 (IH):  Fraction a2 pr = pf_frac_sum a2 rest *)
           pf_frac_sum_sound a2 rest;
           let dpr : (x:polynomial t{is_nonzero x}) = pr in
           let x0  : fraction id_p = Fraction a0 e0 in
           let fa2 : fraction id_p = Fraction a2 dpr in
           let mprod : polynomial t = m0 * pr in
           let mpr : (x:polynomial t{is_nonzero x}) = mprod in
           let q   : (x:polynomial t{is_nonzero x}) = poly_prod ms in
           (* FACT3:  x0 (+) fa2 = x0 (+) pf_frac_sum a2 rest *)
           frac_add_cong_r x0 fa2 (pf_frac_sum a2 rest);
           (* chain:  Fraction r (m0*pr) = x0 (+) fa2 = x0 (+) pf_frac_sum a2 rest = pf_frac_sum r ms *)
           transitivity (Fraction #(polynomial t) #id_p r mpr)
                        (fraction_add x0 fa2)
                        (fraction_add x0 (pf_frac_sum a2 rest)))
#pop-options

(* ================================================================ *)
(*  (Step 4)  The MULTI-factor integration result + executable       *)
(*  integrator.  A squarefree factor with a proof carrier so the      *)
(*  per-factor integrate call's preconditions are discharged.         *)
(* ================================================================ *)

noeq type rational_multi_result (#t:Type) (f: field t) = {
  (* ∫ of the polynomial quotient + the per-factor polynomial parts *)
  poly_part_m        : polynomial t;
  (* concatenation of all per-factor Hermite rational triples *)
  hermite_rational_m : list (polynomial t & polynomial t & nat);
  (* the per-factor logarithmic parts *)
  log_parts_m        : list (root_sum f);
}

(* a squarefree denominator base carrying its own well-formedness. *)
let sf_factor (#t:Type) (f: field t) =
  (bp:(polynomial t & pos){deg (fst bp) >= 1 /\ square_free #t #f (fst bp)})

let moduli_of (#t:Type) {| f: field t |} (facs: list (sf_factor f)) : list (polynomial t) =
  L.map (fun (bp: sf_factor f) -> poly_power (fst bp) (snd bp)) facs

let rec map_length_moduli (#t:Type) {| f: field t |} (facs: list (sf_factor f))
  : Lemma (ensures L.length (moduli_of facs) == L.length facs) (decreases facs)
  = match facs with
    | []      -> ()
    | _ :: tl -> map_length_moduli tl

(* Integrate each proper numerator rᵢ against its factor (bᵢ, eᵢ). *)
let rec integrate_factors (#t:Type) {| f: field t |}
  (nums: list (polynomial t)) (facs: list (sf_factor f))
  : Pure (list (rational_integral_result f))
         (requires char_zero f /\ L.length nums == L.length facs)
         (ensures  fun rs -> L.length rs == L.length facs)
         (decreases facs)
  = match nums, facs with
    | n :: ntl, bp :: ftl ->
        integrate_rational_single_factor n (fst bp) (snd bp)
          :: integrate_factors ntl ftl
    | _, _ -> []

(* Collect the poly / hermite / log parts of the per-factor results. *)
let collect_parts (#t:Type) {| f: field t |}
  (s: polynomial t) (results: list (rational_integral_result f))
  : Pure (rational_multi_result f)
         (requires char_zero f) (ensures fun _ -> True)
  = { poly_part_m =
        L.fold_left (fun acc res -> acc + res.poly_part) (PA.antideriv s) results;
      hermite_rational_m =
        L.collect (fun res -> res.hermite_rational) results;
      log_parts_m =
        L.map (fun res -> res.log_part) results; }

(* Top-level executable multi-factor integrator.  The squarefree
   factorization `facs` of q is supplied (with q = poly_prod of the
   moduli, pairwise-coprime, each modulus deg >= 1). *)
let integrate_rational_multi (#t:Type) {| f: field t |}
  (p q: polynomial t) (facs: list (sf_factor f))
  : Pure (rational_multi_result f)
         (requires char_zero f /\
                   pairwise_coprime (moduli_of facs) /\
                   all_deg_ge1 (moduli_of facs))
         (ensures  fun _ -> True)
  = let (s, r) = poly_divmod p q in
    let ms = moduli_of facs in
    let nums = pf_split r ms in
    map_length_moduli facs;                  (* L.length ms == L.length facs *)
    let results = integrate_factors nums facs in
    collect_parts s results

(* ================================================================ *)
(*  (Step 5)  DERIVATION-SUM ASSEMBLY (the M1 soundness theorem).     *)
(*                                                                   *)
(*  Given                                                            *)
(*    - the Euclidean split  p = s·(∏ ms) + r,                        *)
(*    - the moduli ms pairwise-coprime, each deg >= 1,               *)
(*    - and `dsum`, the summed derivative of the per-factor answers,  *)
(*      equal to the fraction-level partial-fraction sum pf_frac_sum  *)
(*      (this last equality is exactly the per-factor certificates    *)
(*      `rational_single_factor_sound_split`, one per bᵢ^{eᵢ}),       *)
(*  the derivative of the WHOLE answer equals  p / (∏ ms):            *)
(*                                                                   *)
(*    D(∫s)  (+)  dsum   =   p / (∏ ms).                              *)
(* ================================================================ *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let integrate_rational_multi_sound_split (#t:Type) {| f: field t |}
  (p s r: polynomial t) (ms: list (polynomial t)) (dsum: rational_function f)
  : Lemma (requires char_zero f /\ pairwise_coprime ms /\ all_deg_ge1 ms /\ Cons? ms /\
                    p = ((s * (poly_prod ms)) + r) /\
                    dsum = pf_frac_sum r ms)
          (ensures (let id_p = polynomial_id #t #(id_of_f t) in
                    is_nonzero (poly_prod ms) /\
                    (let q : (x:polynomial t{is_nonzero x}) = poly_prod ms in
                     fraction_add
                       (rational_deriv (poly_to_rational (PA.antideriv s)))
                       dsum
                     = Fraction #(polynomial t) #id_p p q)))
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    deg_prod_nonneg ms;
    deg_nonneg_nonzero (poly_prod ms);
    let q : (x:polynomial t{is_nonzero x}) = poly_prod ms in
    (* dsum = Fraction r q :  dsum = pf_frac_sum r ms = Fraction r (poly_prod ms) *)
    pf_frac_sum_sound r ms;                          (* Fraction r q = pf_frac_sum r ms *)
    let pd : fraction id_p = Fraction r q in
    symmetry pd (pf_frac_sum r ms);                  (* pf_frac_sum r ms = pd *)
    transitivity dsum (pf_frac_sum r ms) pd;         (* dsum = pd *)
    (* Euclidean split soundness:  D(∫s) (+) pd = Fraction p q. *)
    split_sound_frac p q s r pd;
    (* rewrite pd back to dsum on the left summand. *)
    let da : fraction id_p =
      rational_deriv (poly_to_rational (PA.antideriv s)) in
    frac_add_cong_r da dsum pd;                       (* (da (+) dsum) = (da (+) pd) *)
    transitivity (fraction_add da dsum) (fraction_add da pd)
                 (Fraction #(polynomial t) #id_p p q)
#pop-options




