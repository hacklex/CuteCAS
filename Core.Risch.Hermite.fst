module Core.Risch.Hermite
(*
   Hermite reduction for rational integration.

   Given a rational function A/D^n where D is square-free and n ≥ 2,
   computes (G_num, C) such that:
     ∫ A/D^n dx = G_num / D^(n-1) + ∫ C / D^(n-1) dx

   Formula (from Bézout s·D + t·D' = 1 with D square-free):
     G_num = -[1/(n-1)] · A · t
     C     = A·s + [1/(n-1)] · (A·t)'

   Full Hermite reduction iterates this step for each Yun factor
   with multiplicity ≥ 2, reducing the integral to one with a
   completely square-free denominator.
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree
open Core.Polynomial.PartialFraction

(* ================================================================ *)
(*  Characteristic zero: every positive natural is nonzero          *)
(* ================================================================ *)

let char_zero (#t:Type) (f: field t) : prop
  = forall (n:pos). ~(nat_scale n (one #t) = (zero #t))

(* ================================================================ *)
(*  Field scalar: embed a coefficient as a constant polynomial      *)
(* ================================================================ *)

let scalar_poly (#t:Type) {| cr: commutative_ring t |} (c: t) : polynomial t
  = if c = zero then poly_zero #t else [c]

(* ================================================================ *)
(*  One Hermite step: reduce multiplicity by 1                      *)
(*                                                                  *)
(*  Input:  A (numerator), D (squarefree denom), n ≥ 2              *)
(*  Output: (G_num, C) where                                        *)
(*    ∫ A/D^n dx = G_num / D^(n-1) + ∫ C / D^(n-1) dx              *)
(*                                                                  *)
(*  Requires: char_zero (so (n-1) is invertible) and square_free D  *)
(* ================================================================ *)

let hermite_step (#t:Type) {| f: field t |}
  (a_num: polynomial t)
  (d: polynomial t)
  (n: nat{n >= 2})
  : Pure (polynomial t & polynomial t)
         (requires Some? (poly_deg d) /\ square_free #t #f d /\
                  char_zero f)
         (ensures fun _ -> True)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    (* D is squarefree => gcd(D, D') = 1 => coprime D D' *)
    let d' = poly_deriv #t #cr d in
    (* normalize_bezout gives (s, t) with s·D + t·D' ~ [1] *)
    let (s_coeff, t_coeff) = normalize_bezout #t #f d d' in
    (* Compute 1/(n-1) as a field element *)
    let nm1 : t = nat_scale #t #(cr.cr_r.r_add) (n - 1) (one #t) in
    let nm1_inv : t = (f.f_sf.sf_mig).inv nm1 in
    let inv_scale : polynomial t = scalar_poly nm1_inv in
    (* A·t *)
    let at_prod = poly_mul a_num t_coeff in
    (* G_num = -[1/(n-1)] · A · t *)
    let g_num = poly_neg (poly_mul inv_scale at_prod) in
    (* (A·t)' = derivative of A*t *)
    let at_deriv = poly_deriv #t #cr at_prod in
    (* C = A·s + [1/(n-1)] · (A·t)' *)
    let c_num = poly_add (poly_mul a_num s_coeff)
                         (poly_mul inv_scale at_deriv) in
    (g_num, c_num)

(* ================================================================ *)
(*  Soundness of hermite_step (polynomial-level identity)           *)
(*                                                                  *)
(*  The key correctness property:                                   *)
(*    A = G'·D - (n-1)·G·D' + C·D                                  *)
(*  where (G, C) = hermite_step A D n.                              *)
(*                                                                  *)
(*  This is equivalent to:                                          *)
(*    d/dx(G/D^(n-1)) + C/D^(n-1) = A/D^n                          *)
(*                                                                  *)
(*  Proof sketch:                                                   *)
(*    G = -[1/(n-1)]·A·t, C = A·s + [1/(n-1)]·(A·t)'              *)
(*    G' = -[1/(n-1)]·(A·t)'                                       *)
(*    G'·D - (n-1)·G·D' + C·D                                      *)
(*    = -[1/(n-1)]·(A·t)'·D + A·t·D' + (A·s + [1/(n-1)]·(A·t)')·D *)
(*    = A·t·D' + A·s·D                      (terms cancel)         *)
(*    = A·(s·D + t·D')                      (factor A)             *)
(*    = A·[1]                                (Bézout: s·D+t·D'~1)  *)
(*    = A                                    ✓                      *)
(* ================================================================ *)

(* ================================================================ *)
(*  Iterate Hermite step: reduce A/D^n all the way to A_final/D     *)
(*                                                                  *)
(*  Accumulates rational-part terms as a list of (numerator, power). *)
(*  Each term g_i / D^i contributes to the rational part.           *)
(* ================================================================ *)

let rec hermite_reduce_power (#t:Type) {| f: field t |}
  (a_num: polynomial t)
  (d: polynomial t)
  (n: nat{n >= 1})
  : Pure (list (polynomial t & nat) & polynomial t)
         (requires Some? (poly_deg d) /\ square_free #t #f d /\
                  char_zero f)
         (ensures fun _ -> True)
         (decreases n)
  = if n = 1 then
      (* Already at power 1: no reduction needed *)
      ([], a_num)
    else
      (* Apply one Hermite step: A/D^n → G/D^(n-1) + ∫C/D^(n-1) *)
      let (g_num, c_num) = hermite_step #t #f a_num d n in
      (* Recurse on C/D^(n-1) *)
      let (rest_rational, final_num) =
        hermite_reduce_power #t #f c_num d (n - 1) in
      (* The rational part: G/D^(n-1) plus whatever came from recursion *)
      ((g_num, n - 1) :: rest_rational, final_num)

(* ================================================================ *)
(*  Full Hermite reduction via Yun factorization                    *)
(*                                                                  *)
(*  Input: p/q (numerator p, denominator q with deg ≥ 1)            *)
(*  Output: (rational_parts, residual_num, residual_den)            *)
(*    where ∫ p/q = Σ(rational_parts) + ∫ residual_num/residual_den *)
(*    and residual_den is square-free.                               *)
(*                                                                  *)
(*  The rational_parts are concrete polynomial numerators over       *)
(*  explicit power-of-factor denominators.                          *)
(*                                                                  *)
(*  NOTE: This requires partial fraction decomposition to separate  *)
(*  p/q into parts for each Yun factor. For simplicity, we provide  *)
(*  the single-factor version (hermite_reduce_power) which is the   *)
(*  workhorse. The full integration pipeline orchestrates the calls. *)
(* ================================================================ *)

(* ================================================================ *)
(*  SOUNDNESS of one Hermite step                                    *)
(*                                                                   *)
(*    A ~ G'*D - (n-1)*G*D' + C*D    for (G,C) = hermite_step A D n  *)
(*                                                                   *)
(*  which is exactly  d/dx(G/D^(n-1)) + C/D^(n-1) = A/D^n  cleared    *)
(*  of denominators.  Proof outline:                                 *)
(*    - G = -(1/(n-1))*A*t,  C = A*s + (1/(n-1))*(A*t)'              *)
(*    - G' = -(1/(n-1))*(A*t)'                  (g_deriv_general)     *)
(*    - the RHS collapses via  (n-1)*(1/(n-1)) = 1  and the Bezout   *)
(*      identity  s*D + t*D' = 1                (hermite_algebra)     *)
(* ================================================================ *)

(* Derivative of a scalar-times-polynomial, negated:
   (neg ([c] * ap))' ~ neg ([c] * ap').  [c] is constant, so [c]'=0. *)
let g_deriv_general (#t:Type) {| cr: commutative_ring t |}
  (c: t) (ap: polynomial t)
  : Lemma (poly_eq (poly_deriv (poly_neg (poly_mul (c @ poly_zero) ap)))
                   (poly_neg (poly_mul (c @ poly_zero) (poly_deriv ap))))
  = let sc : polynomial t = c @ poly_zero in
    let x : polynomial t = poly_mul sc ap in
    poly_deriv_neg #t #cr x;
    poly_deriv_scalar_mul #t #cr c ap;
    poly_neg_congruence (poly_deriv x) (poly_mul sc (poly_deriv ap));
    poly_eq_transitivity (poly_deriv (poly_neg x))
                         (poly_neg (poly_deriv x))
                         (poly_neg (poly_mul sc (poly_deriv ap)))

(* Pure-ring identity 1: the Hermite RHS rearranges so the isc*u*d terms
   cancel, leaving  a*(s*d) + (n1*isc)*(a*(tw*dp)).  Standalone so that
   canon_ring reflects against clean atoms (no surrounding let-bindings). *)
let hermite_ring_id1 (#r:Type) {| cr: commutative_ring r |}
  (a d dp s tw u isc n1 : r)
  : Lemma ((((neg (isc * u)) * d)
              + neg (n1 * ((neg (isc * (a * tw))) * dp)))
             + (((a * s) + (isc * u)) * d)
           = ((a * (s * d)) + ((n1 * isc) * (a * (tw * dp)))))
  = assert ((((neg (isc * u)) * d)
              + neg (n1 * ((neg (isc * (a * tw))) * dp)))
             + (((a * s) + (isc * u)) * d)
           = ((a * (s * d)) + ((n1 * isc) * (a * (tw * dp)))))
      by Core.Tactics.CanonRing.canon_ring ()

(* Pure-ring identity 2: factor a out of the surviving two terms. *)
let hermite_ring_id2 (#r:Type) {| cr: commutative_ring r |}
  (a d dp s tw : r)
  : Lemma ((a * (s * d)) + (a * (tw * dp))
           = (a * ((s * d) + (tw * dp))))
  = assert ((a * (s * d)) + (a * (tw * dp))
            = (a * ((s * d) + (tw * dp))))
      by Core.Tactics.CanonRing.canon_ring ()

(* Abstract commutative-ring cancellation: with  n1*isc = 1  and
   s*d + tw*dp = 1, the Hermite RHS equals a. *)
let hermite_algebra (#r:Type) {| cr: commutative_ring r |}
  (a d dp s tw u isc n1 : r)
  : Lemma (requires (n1 * isc) = one /\ ((s * d) + (tw * dp)) = one)
          (ensures
            (let gnum = neg (isc * (a * tw)) in
             let gder = neg (isc * u) in
             let cnum = (a * s) + (isc * u) in
             a = (((gder * d) + neg (n1 * (gnum * dp))) + (cnum * d))))
  = H.elim_equatable_laws r ();
    H.trans_for_calc r ();
    hermite_ring_id1 a d dp s tw u isc n1;
    mul_congruence (n1 * isc) (a * (tw * dp)) one (a * (tw * dp));
    H.one_mul_x (a * (tw * dp));
    add_congruence (a * (s * d)) ((n1 * isc) * (a * (tw * dp)))
                   (a * (s * d)) (a * (tw * dp));
    hermite_ring_id2 a d dp s tw;
    mul_congruence a ((s * d) + (tw * dp)) a one;
    H.x_mul_one a

let hermite_step_correct (#t:Type) {| f: field t |}
  (a_num d: polynomial t) (n: nat{n >= 2})
  : Lemma (requires Some? (poly_deg d) /\ square_free #t #f d /\ char_zero f)
          (ensures (
            let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
            let (g_num, c_num) = hermite_step #t #f a_num d n in
            let d'  = poly_deriv #t #cr d in
            let g'  = poly_deriv #t #cr g_num in
            let nm1 = nat_scale #t #(cr.cr_r.r_add) (n - 1) (one #t) in
            let nm1_poly : polynomial t = scalar_poly nm1 in
            poly_eq a_num
              (poly_add (poly_sub (poly_mul g' d)
                                  (poly_mul nm1_poly (poly_mul g_num d')))
                        (poly_mul c_num d))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let d'  = poly_deriv #t #cr d in
    assert (coprime #t #f d d');                    (* square_free d = coprime d d' *)
    let (s_coeff, t_coeff) = normalize_bezout #t #f d d' in
    let nm1 = nat_scale #t #(cr.cr_r.r_add) (n - 1) (one #t) in
    let nm1_inv = (f.f_sf.sf_mig).inv nm1 in        (* requires is_nonzero nm1 (char_zero) *)
    let inv_scale : polynomial t = scalar_poly nm1_inv in
    let at_prod = poly_mul a_num t_coeff in
    let at_deriv = poly_deriv #t #cr at_prod in
    let g_num = poly_neg (poly_mul inv_scale at_prod) in
    let c_num = poly_add (poly_mul a_num s_coeff) (poly_mul inv_scale at_deriv) in
    let nm1_poly : polynomial t = scalar_poly nm1 in
    assert (hermite_step #t #f a_num d n == (g_num, c_num));
    assert (is_nonzero nm1_inv);
    assert (inv_scale == [nm1_inv]);
    assert (nm1_poly == [nm1]);
    normalize_bezout_correct #t #f d d';            (* H2: Bezout *)
    singleton_inv_mul_singleton #t #f nm1;          (* poly_eq (poly_mul [nm1_inv] [nm1]) poly_one *)
    poly_mul_commutativity nm1_poly inv_scale;
    poly_eq_transitivity (poly_mul nm1_poly inv_scale)
                         (poly_mul inv_scale nm1_poly)
                         (poly_one #t);              (* H1 *)
    g_deriv_general #t #cr nm1_inv at_prod;
    hermite_algebra #(polynomial t) a_num d d' s_coeff t_coeff at_deriv inv_scale nm1_poly;
    let g'        : polynomial t = poly_deriv #t #cr g_num in
    let gder      : polynomial t = poly_neg (poly_mul inv_scale at_deriv) in
    let yterm     : polynomial t = poly_neg (poly_mul nm1_poly (poly_mul g_num d')) in
    let ha_rhs    : polynomial t =
      poly_add (poly_add (poly_mul gder d) yterm) (poly_mul c_num d) in
    let tgt'      : polynomial t =
      poly_add (poly_add (poly_mul g' d) yterm) (poly_mul c_num d) in
    poly_eq_reflexivity d;
    poly_eq_reflexivity yterm;
    poly_eq_reflexivity (poly_mul c_num d);
    poly_mul_congruence g' d gder d;
    poly_add_congruence (poly_mul g' d) yterm (poly_mul gder d) yterm;
    poly_add_congruence (poly_add (poly_mul g' d) yterm) (poly_mul c_num d)
                        (poly_add (poly_mul gder d) yterm) (poly_mul c_num d);
    poly_eq_symmetry tgt' ha_rhs;
    poly_eq_transitivity a_num ha_rhs tgt';
    poly_sub_reveal (poly_mul g' d) (poly_mul nm1_poly (poly_mul g_num d'))

(* ================================================================ *)
(*  FULL-REDUCTION SOUNDNESS (lifting hermite_step_correct through    *)
(*  the hermite_reduce_power recursion).                              *)
(*                                                                    *)
(*  The rational parts (gᵢ, kᵢ) combine, over the common denominator  *)
(*  D^(n-1), into a single numerator N = combined_num parts D.  The   *)
(*  reduction soundness is the cleared-denominator identity           *)
(*    A ~ N'*D - (n-1)*N*D' + final*D^(n-1)                           *)
(*  (i.e. d/dx(N/D^(n-1)) + final/D = A/D^n), proved by induction on  *)
(*  n from hermite_step_correct.                                      *)
(* ================================================================ *)

(* combined_num: fold the rational parts into the numerator over D^(n-1).
     N([]) = 0,  N((g,_)::rest) = g + D * N(rest). *)
let rec combined_num (#t:Type) {| cr: commutative_ring t |}
  (parts: list (polynomial t & nat)) (d: polynomial t)
  : Tot (polynomial t) (decreases parts)
  = match parts with
    | [] -> poly_zero #t
    | (g, _) :: rest -> poly_add g (poly_mul d (combined_num rest d))

let coeff_scalar_poly_zero (#t:Type) {| cr: commutative_ring t |} (a: t)
  : Lemma (coeff (scalar_poly a) 0 = a)
  = H.elim_equatable_laws t ();
    if a = zero then reflexivity (zero <: t)
    else reflexivity a

let coeff_scalar_poly_high (#t:Type) {| cr: commutative_ring t |} (a: t) (i: nat)
  : Lemma (requires i >= 1) (ensures coeff (scalar_poly a) i = (zero <: t))
  = H.elim_equatable_laws t ();
    reflexivity (zero <: t)

let coeff_poly_one_zero (#t:Type) {| cr: commutative_ring t |} (_: unit)
  : Lemma (coeff (poly_one #t) 0 = (one <: t))
  = H.elim_equatable_laws t ();
    if (one <: t) = zero then reflexivity (one <: t) else reflexivity (one <: t)

let coeff_poly_one_high (#t:Type) {| cr: commutative_ring t |} (i: nat)
  : Lemma (requires i >= 1) (ensures coeff (poly_one #t) i = (zero <: t))
  = H.elim_equatable_laws t ();
    reflexivity (zero <: t)

(* scalar_poly (nat_scale (k+1) one) ~ scalar_poly (nat_scale k one) + 1 *)
let scalar_poly_succ (#t:Type) {| cr: commutative_ring t |} (k: nat)
  : Lemma (poly_eq (scalar_poly (nat_scale #t #(cr.cr_r.r_add) (Prims.op_Addition k 1) (one #t)))
                   (poly_add (scalar_poly (nat_scale #t #(cr.cr_r.r_add) k (one #t)))
                             (poly_one #t)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let a : t = nat_scale #t #(cr.cr_r.r_add) (Prims.op_Addition k 1) (one #t) in
    let b : t = nat_scale #t #(cr.cr_r.r_add) k (one #t) in
    let lhs : polynomial t = scalar_poly a in
    let rhs : polynomial t = poly_add (scalar_poly b) (poly_one #t) in
    nat_scale_succ #t #(cr.cr_r.r_add) k (one #t);
    add_commutativity (one <: t) b;
    let aux (i: nat) : Lemma (coeff lhs i = coeff rhs i) =
      if i = 0 then begin
        coeff_scalar_poly_zero a;
        poly_add_coeff (scalar_poly b) (poly_one #t) 0;
        coeff_scalar_poly_zero b;
        coeff_poly_one_zero #t ();
        add_congruence (coeff (scalar_poly b) 0) (coeff (poly_one #t) 0) b (one <: t);
        transitivity (coeff lhs 0) a (coeff rhs 0)
      end else begin
        coeff_scalar_poly_high a i;
        poly_add_coeff (scalar_poly b) (poly_one #t) i;
        coeff_scalar_poly_high b i;
        coeff_poly_one_high #t i;
        add_congruence (coeff (scalar_poly b) i) (coeff (poly_one #t) i) (zero <: t) (zero <: t);
        H.x_plus_zero (zero <: t);
        transitivity (coeff lhs i) (zero <: t) (coeff rhs i)
      end
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* Pure-ring identity behind the inductive step (cross-term vanishes
   because n1 is inlined as n2+one). *)
let reduce_pure (#r:Type) {| cr: commutative_ring r |}
  (gp d dp g nr nrp final dpow2 n2 : r)
  : Lemma (
      (((gp + ((dp * nr) + (d * nrp))) * d)
         + neg ((n2 + one) * ((g + (d * nr)) * dp)))
        + (final * (d * dpow2))
      =
      ((gp * d) + neg ((n2 + one) * (g * dp)))
        + ((((nrp * d) + neg (n2 * (nr * dp))) + (final * dpow2)) * d))
  = assert (
      (((gp + ((dp * nr) + (d * nrp))) * d)
         + neg ((n2 + one) * ((g + (d * nr)) * dp)))
        + (final * (d * dpow2))
      =
      ((gp * d) + neg ((n2 + one) * (g * dp)))
        + ((((nrp * d) + neg (n2 * (nr * dp))) + (final * dpow2)) * d))
      by Core.Tactics.CanonRing.canon_ring ()

let rec hermite_reduce_power_correct (#t:Type) {| f: field t |}
  (a_num d: polynomial t) (n: nat{n >= 1})
  : Lemma (requires Some? (poly_deg d) /\ square_free #t #f d /\ char_zero f)
          (ensures (
            let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
            let (parts, final) = hermite_reduce_power #t #f a_num d n in
            let nn = combined_num parts d in
            let d' = poly_deriv #t #cr d in
            poly_eq a_num
              (poly_add (poly_sub (poly_mul (poly_deriv #t #cr nn) d)
                                  (poly_mul (scalar_poly (nat_scale #t #(cr.cr_r.r_add) (n - 1) (one #t)))
                                            (poly_mul nn d')))
                        (poly_mul final (poly_power d (n - 1))))))
          (decreases n)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let d' = poly_deriv #t #cr d in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if n = 1 then begin
      let nn = poly_zero #t in
      let n1c = scalar_poly (nat_scale #t #(cr.cr_r.r_add) (n - 1) (one #t)) in
      let term1 = poly_mul (poly_deriv #t #cr nn) d in
      let term2 = poly_mul n1c (poly_mul nn d') in
      poly_deriv_zero #t #cr;
      H.zero_mul_x #(polynomial t) d;
      H.zero_mul_x #(polynomial t) d';
      poly_mul_congruence n1c (poly_mul nn d') n1c (poly_zero #t);
      H.x_mul_zero #(polynomial t) n1c;
      poly_neg_congruence term2 (poly_zero #t);
      poly_neg_zero #t #cr;
      poly_sub_reveal term1 term2;
      poly_add_congruence term1 (poly_neg term2) (poly_zero #t) (poly_zero #t);
      poly_add_zero #t #cr (poly_zero #t);
      poly_mul_one #t #cr a_num;
      poly_add_congruence (poly_sub term1 term2) (poly_mul a_num (poly_power d (n - 1)))
                          (poly_zero #t) a_num;
      poly_add_commutativity (poly_zero #t) a_num;
      poly_add_zero #t #cr a_num
    end else begin
      let (g_num, c_num) = hermite_step #t #f a_num d n in
      let (rest, final) = hermite_reduce_power #t #f c_num d (n - 1) in
      let nr = combined_num rest d in
      let nn = poly_add g_num (poly_mul d nr) in
      let gp = poly_deriv #t #cr g_num in
      let nrp = poly_deriv #t #cr nr in
      let n1 = scalar_poly (nat_scale #t #(cr.cr_r.r_add) (n - 1) (one #t)) in
      let n2 = scalar_poly (nat_scale #t #(cr.cr_r.r_add) (n - 2) (one #t)) in
      let n2p1 = poly_add n2 (poly_one #t) in
      let dpow2 = poly_power d (n - 2) in
      let np_exp = poly_add gp (poly_add (poly_mul d' nr) (poly_mul d nrp)) in
      let nnd' = poly_mul nn d' in
      let ggd' = poly_mul g_num d' in
      let ih_add = poly_add (poly_add (poly_mul nrp d) (poly_neg (poly_mul n2 (poly_mul nr d'))))
                            (poly_mul final dpow2) in
      hermite_step_correct #t #f a_num d n;
      hermite_reduce_power_correct #t #f c_num d (n - 1);
      scalar_poly_succ #t #cr (n - 2);
      reduce_pure #(polynomial t) gp d d' g_num nr nrp final dpow2 n2;
      poly_deriv_add #t #cr g_num (poly_mul d nr);
      poly_deriv_mul #t #cr d nr;
      poly_add_congruence gp (poly_deriv #t #cr (poly_mul d nr))
                          gp (poly_add (poly_mul d' nr) (poly_mul d nrp));
      poly_sub_reveal (poly_mul gp d) (poly_mul n1 ggd');
      poly_sub_reveal (poly_mul nrp d) (poly_mul n2 (poly_mul nr d'));
      poly_sub_reveal (poly_mul (poly_deriv #t #cr nn) d) (poly_mul n1 nnd');
      poly_mul_congruence n1 ggd' n2p1 ggd';
      poly_neg_congruence (poly_mul n1 ggd') (poly_mul n2p1 ggd');
      poly_mul_congruence c_num d ih_add d;
      poly_add_congruence (poly_mul gp d) (poly_neg (poly_mul n1 ggd'))
                          (poly_mul gp d) (poly_neg (poly_mul n2p1 ggd'));
      poly_add_congruence
        (poly_add (poly_mul gp d) (poly_neg (poly_mul n1 ggd'))) (poly_mul c_num d)
        (poly_add (poly_mul gp d) (poly_neg (poly_mul n2p1 ggd'))) (poly_mul ih_add d);
      poly_mul_congruence (poly_deriv #t #cr nn) d np_exp d;
      poly_mul_congruence n1 nnd' n2p1 nnd';
      poly_neg_congruence (poly_mul n1 nnd') (poly_mul n2p1 nnd');
      poly_add_congruence (poly_mul (poly_deriv #t #cr nn) d) (poly_neg (poly_mul n1 nnd'))
                          (poly_mul np_exp d) (poly_neg (poly_mul n2p1 nnd'));
      poly_add_congruence
        (poly_add (poly_mul (poly_deriv #t #cr nn) d) (poly_neg (poly_mul n1 nnd')))
        (poly_mul final (poly_power d (n - 1)))
        (poly_add (poly_mul np_exp d) (poly_neg (poly_mul n2p1 nnd')))
        (poly_mul final (poly_power d (n - 1)))
    end
