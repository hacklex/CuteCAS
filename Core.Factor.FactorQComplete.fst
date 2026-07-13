module Core.Factor.FactorQComplete

(* ================================================================ *)
(*  TOP-LEVEL factor_Q COMPLETENESS.                                 *)
(*                                                                   *)
(*  For a primitive, ℚ-squarefree integer polynomial b of degree     *)
(*  >= 1, the executable factorizer's candidate list (for a good     *)
(*  prime) CONTAINS a complete factorization: a list of integer      *)
(*  factors whose product is an associate of b, each of which is     *)
(*  reached (up to poly_eq, as its monic image) in the candidate     *)
(*  list monic_candidates (monicize_pos b) p.                        *)
(*                                                                   *)
(*  Built on:                                                        *)
(*   - Core.Polynomial.FactorizationExists (ℚ-factorization exists), *)
(*   - Core.Factor.Gauss / GaussIrred / Content (ℤ↔ℚ Gauss bridge),  *)
(*   - Core.Factor.NonMonicZass (each ℤ divides-factor is reached),  *)
(*   - Core.Factor.PrimeExists (a good prime exists).                *)
(*                                                                   *)
(*  Standalone (NOT on build-all).  NO admit / assume / sorry.       *)
(* ================================================================ *)

module L   = FStar.List.Tot
module E   = Core.NumberTheory
module R   = Core.Polynomial.Roots
module H   = Core.Algebra.Helpers
module NMZ = Core.Factor.NonMonicZass
module ZCplt = Core.Factor.ZassComplete
module PS  = Core.Factor.PrimeSelect
module PE  = Core.Factor.PrimeExists
module SF  = Core.Polynomial.SquareFree
module BIN = Core.Factor.BadIntNonzero
module IR  = Core.Polynomial.Irreducible
module FE  = Core.Polynomial.FactorizationExists
module F   = Core.Fractions
module EP  = Core.Polynomial.EmbedQProd

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Monic
open Core.Factor.Content
open Core.Factor.Gauss
open Core.Factor.GaussIrred
open Core.Polynomial.EmbedQ

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(* ================================================================ *)
(*  0.  Generic divisibility helpers over a commutative ring.        *)
(* ================================================================ *)

(* Every list member divides the list product. *)
let rec poly_prod_mem_divides (#t:Type) {| cr: commutative_ring t |}
  (l: list (polynomial t)) (g: polynomial t)
  : Lemma (requires L.memP g l)
          (ensures  divides g (R.poly_prod l))
          (decreases l)
  = match l with
    | x :: rest ->
      eliminate (g == x) \/ L.memP g rest
      returns divides g (R.poly_prod l)
      with _heq.
        begin
          divides_refl g;
          divides_mul_right g g (R.poly_prod rest)   (* divides g (g * prod rest) = prod (x::rest) *)
        end
      and _hin.
        begin
          poly_prod_mem_divides rest g;               (* divides g (prod rest) *)
          divides_mul_left g x (R.poly_prod rest)     (* divides g (x * prod rest) *)
        end

(* An associate (equal up to sign) yields mutual divisibility. *)
let mutual_divides_of_assoc (p q: polynomial int)
  : Lemma (requires poly_eq p q \/ poly_eq p (poly_neg q))
          (ensures  divides p q /\ divides q p)
  = H.elim_equatable_laws (polynomial int) ();
    eliminate (poly_eq p q) \/ (poly_eq p (poly_neg q))
    returns divides p q /\ divides q p
    with _hpos.
      begin
        divides_refl p;
        divides_congruence_right p p q;               (* divides p q *)
        poly_eq_symmetry p q;
        divides_refl q;
        divides_congruence_right q q p                (* divides q p *)
      end
    and _hneg.
      begin
        (* p = -q *)
        divides_refl p;
        divides_congruence_right p p (poly_neg q);    (* divides p (-q) *)
        divides_neg p (poly_neg q);                   (* divides p (-(-q)) *)
        H.neg_neg q;                                  (* -(-q) = q *)
        divides_congruence_right p (poly_neg (poly_neg q)) q;  (* divides p q *)
        poly_eq_symmetry p (poly_neg q);              (* -q = p *)
        divides_refl (poly_neg q);
        divides_congruence_right (poly_neg q) (poly_neg q) p;  (* divides (-q) p *)
        (* q divides -q divides p, and q = -(-q) *)
        divides_refl q;
        divides_neg q q;                              (* divides q (-q) *)
        divides_trans q (poly_neg q) p                (* divides q p *)
      end

(* ================================================================ *)
(*  1.  Per-ℚ-factor data and the descent to a primitive ℤ-factor.   *)
(* ================================================================ *)

(*  For a ℚ-polynomial qf, clear denominators to an integer polynomial
    a0 = snd (clear_denominators qf) with embed a0 = d · qf, then take
    its primitive part g_of qf.  d_of / ca_of are the two scalars. *)
let g_of  (qf: polynomial qq) : polynomial int = primitive_part (snd (clear_denominators qf))
let ca_of (qf: polynomial qq) : int = int_content (snd (clear_denominators qf))
let d_of  (qf: polynomial qq) : int = fst (clear_denominators qf)

(*  ca_of qf · embed (g_of qf)  =  d_of qf · qf   in ℚ[z],  with the
    primitive integer factor g_of qf of the SAME degree as qf. *)
let per_elem_bridge (qf: polynomial qq)
  : Lemma (requires deg qf >= 1)
          (ensures  is_primitive (g_of qf) /\ deg (g_of qf) == deg qf /\
                    ca_of qf > 0 /\ d_of qf <> 0 /\
                    poly_eq (R.poly_scale (embed_zq_const (ca_of qf)) (embed_zq (g_of qf)))
                            (R.poly_scale (embed_zq_const (d_of qf)) qf))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    H.elim_equatable_laws (polynomial int) ();
    let d  = fst (clear_denominators qf) in
    let a0 = snd (clear_denominators qf) in
    denom_prod_nonzero qf;                          (* d <> 0 *)
    clear_denominators_sound qf;                    (* embed a0 ~ scale(embed d) qf *)
    embed_zq_const_zero_iff d;                      (* embed d <> 0_qq *)
    deg_scale_nonzero (embed_zq_const d) qf;        (* deg(scale(embed d) qf) == deg qf *)
    poly_eq_length (embed_zq a0) (R.poly_scale (embed_zq_const d) qf);
    embed_zq_deg a0;                                (* deg(embed a0) == deg a0 *)
    assert (deg a0 >= 1);
    assert (~(a0 == []));
    let ca = int_content a0 in
    let g  = primitive_part a0 in
    content_pos a0;                                 (* ca > 0 *)
    primitive_part_is_primitive a0;                 (* is_primitive g *)
    primitive_part_deg a0;                          (* deg g == deg a0 == deg qf *)
    content_times_primitive a0;                     (* a0 ~ scale ca g *)
    poly_eq_int_eq a0 (R.poly_scale ca g);          (* a0 == scale ca g *)
    assert (embed_zq a0 == embed_zq (R.poly_scale ca g));
    embed_scale ca g;                               (* embed(scale ca g) ~ scale(embed ca)(embed g) *)
    poly_eq_symmetry (embed_zq (R.poly_scale ca g))
                     (R.poly_scale (embed_zq_const ca) (embed_zq g));
    (* scale(embed ca)(embed g) ~ embed(scale ca g) == embed a0 ~ scale(embed d) qf *)
    poly_eq_transitivity (R.poly_scale (embed_zq_const ca) (embed_zq g))
                         (embed_zq a0)
                         (R.poly_scale (embed_zq_const d) qf)

(*  Generic: multiply two scale-equalities coordinate-wise. *)
let scale_prod_step (#t:Type) {| cr: commutative_ring t |}
  (a1 b1 a2 b2: t) (x1 y1 x2 y2: polynomial t)
  : Lemma (requires poly_eq (R.poly_scale a1 x1) (R.poly_scale b1 y1) /\
                    poly_eq (R.poly_scale a2 x2) (R.poly_scale b2 y2))
          (ensures  poly_eq (R.poly_scale (a1 * a2) (x1 * x2))
                            (R.poly_scale (b1 * b2) (y1 * y2)))
  = H.elim_equatable_laws (polynomial t) ();
    scale_mul_combine a1 a2 x1 x2;                 (* scale a1 x1 * scale a2 x2 ~ scale(a1*a2)(x1*x2) *)
    poly_eq_symmetry (R.poly_scale a1 x1 * R.poly_scale a2 x2)
                     (R.poly_scale (a1 * a2) (x1 * x2));
    poly_mul_congruence (R.poly_scale a1 x1) (R.poly_scale a2 x2)
                        (R.poly_scale b1 y1) (R.poly_scale b2 y2);
    scale_mul_combine b1 b2 y1 y2;                 (* scale b1 y1 * scale b2 y2 ~ scale(b1*b2)(y1*y2) *)
    poly_eq_transitivity (R.poly_scale (a1 * a2) (x1 * x2))
                         (R.poly_scale a1 x1 * R.poly_scale a2 x2)
                         (R.poly_scale b1 y1 * R.poly_scale b2 y2);
    poly_eq_transitivity (R.poly_scale (a1 * a2) (x1 * x2))
                         (R.poly_scale b1 y1 * R.poly_scale b2 y2)
                         (R.poly_scale (b1 * b2) (y1 * y2))

(* ================================================================ *)
(*  2.  Products over the ℚ-factor list.                             *)
(* ================================================================ *)

let rec ca_prod (qfs: list (polynomial qq)) : int =
  match qfs with
  | []       -> 1
  | qf :: r  -> Prims.op_Star (ca_of qf) (ca_prod r)

let rec d_prod (qfs: list (polynomial qq)) : int =
  match qfs with
  | []       -> 1
  | qf :: r  -> Prims.op_Star (d_of qf) (d_prod r)

(*  embed_zq_const is multiplicative (as a ℚ ring hom). *)
let embed_const_mul_eq (m n: int)
  : Lemma (embed_zq_const (Prims.op_Star m n) = (embed_zq_const m) * (embed_zq_const n))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    embed_zq_const_mul m n;                          (* fraction_mul(em)(en) = embed(m*n) *)
    F.fraction_ring_mul_reveal (embed_zq_const m) (embed_zq_const n)  (* (em*en) == fraction_mul *)

(*  The empty integer product poly_one is primitive. *)
#push-options "--fuel 2 --ifuel 1"
let primitive_poly_one (_:unit)
  : Lemma (is_primitive (poly_one #int))
  = assert (poly_one #int == [1]);
    assert (int_content (poly_one #int) == gcd2 1 0);   (* content_list [1] = gcd2 1 0 *)
    E.is_gcd_0 1;                                       (* is_gcd 1 0 1 *)
    gcd2_is_gcd 1 0;                                    (* is_gcd 1 0 (gcd2 1 0) *)
    gcd2_nonneg 1 0;                                    (* gcd2 1 0 >= 0 *)
    E.is_gcd_unique 1 0 (gcd2 1 0) 1                    (* gcd2 1 0 = 1 (nonneg) *)
#pop-options

(*  The product of the primitive integer factors is primitive. *)
let rec prod_primitive (qfs: list (polynomial qq))
  : Lemma (requires (forall (qf: polynomial qq). L.memP qf qfs ==> deg qf >= 1))
          (ensures  is_primitive (R.poly_prod (L.map g_of qfs)))
          (decreases qfs)
  = match qfs with
    | []        -> primitive_poly_one ()
    | qf :: rest ->
        per_elem_bridge qf;                         (* is_primitive (g_of qf) *)
        prod_primitive rest;                        (* is_primitive (prod (map g_of rest)) *)
        primitive_mul_primitive (g_of qf) (R.poly_prod (L.map g_of rest))

(*  ca_prod · embed (∏ g_of)  =  d_prod · (∏ qf)   in ℚ[z]. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec prod_scalar (qfs: list (polynomial qq))
  : Lemma (requires (forall (qf: polynomial qq). L.memP qf qfs ==> deg qf >= 1))
          (ensures  ca_prod qfs > 0 /\ d_prod qfs <> 0 /\
                    poly_eq (R.poly_scale (embed_zq_const (ca_prod qfs))
                                          (embed_zq (R.poly_prod (L.map g_of qfs))))
                            (R.poly_scale (embed_zq_const (d_prod qfs))
                                          (R.poly_prod qfs)))
          (decreases qfs)
  = H.elim_equatable_laws qq ();
    match qfs with
    | [] ->
        EP.embed_zq_one ();                           (* embed poly_one_int = poly_one_qq *)
        scale_congr_poly (embed_zq_const 1)
                         (embed_zq (poly_one #int)) (poly_one #qq #crq)
    | qf :: rest ->
        let caq = ca_of qf in   let car = ca_prod rest in
        let dq  = d_of qf in    let dr  = d_prod rest in
        let gq  = g_of qf in
        let pr  = R.poly_prod (L.map g_of rest) in
        let qr  = R.poly_prod rest in
        per_elem_bridge qf;                           (* caq>0, dq<>0, E1 *)
        prod_scalar rest;                             (* car>0, dr<>0, E2 *)
        (* STEP : scale(embed caq * embed car)(embed gq * embed pr)
                    ~ scale(embed dq * embed dr)(qf * qr) *)
        scale_prod_step (embed_zq_const caq) (embed_zq_const dq)
                        (embed_zq_const car) (embed_zq_const dr)
                        (embed_zq gq) qf (embed_zq pr) qr;
        embed_const_mul_eq caq car;                   (* embed(caq*car) = embed caq * embed car *)
        embed_const_mul_eq dq dr;                     (* embed(dq*dr)   = embed dq * embed dr   *)
        embed_zq_mul gq pr;                           (* embed(gq*pr) ~ embed gq * embed pr *)
        let sca = embed_zq_const (Prims.op_Star caq car) in
        let scd = embed_zq_const (Prims.op_Star dq dr) in
        let gl  = R.poly_scale sca (embed_zq (gq * pr)) in
        let gla = R.poly_scale sca (poly_mul (embed_zq gq) (embed_zq pr)) in
        let sl  = R.poly_scale (embed_zq_const caq * embed_zq_const car)
                               (poly_mul (embed_zq gq) (embed_zq pr)) in
        let sr  = R.poly_scale (embed_zq_const dq * embed_zq_const dr) (qf * qr) in
        let gr  = R.poly_scale scd (qf * qr) in
        (* gl ~ gla : rewrite the scaled polynomial *)
        scale_congr_poly sca (embed_zq (gq * pr)) (poly_mul (embed_zq gq) (embed_zq pr));
        (* gla ~ sl : rewrite the scalar *)
        R.poly_scale_scalar_congr sca (embed_zq_const caq * embed_zq_const car)
                                (poly_mul (embed_zq gq) (embed_zq pr));
        (* gr ~ sr : rewrite the scalar *)
        R.poly_scale_scalar_congr scd (embed_zq_const dq * embed_zq_const dr) (qf * qr);
        poly_eq_transitivity gl gla sl;               (* gl ~ sl *)
        poly_eq_transitivity gl sl sr;                (* gl ~ sr  (STEP) *)
        poly_eq_symmetry gr sr;                        (* sr ~ gr *)
        poly_eq_transitivity gl sr gr                 (* gl ~ gr *)
#pop-options

(* ================================================================ *)
(*  3.  Assembling the integer factorization.                        *)
(* ================================================================ *)

(*  Every member of the mapped integer-factor list is a primitive
    polynomial of degree >= 1. *)
let rec map_g_of_props (qfacs: list (polynomial qq)) (g: polynomial int)
  : Lemma (requires (forall (qf: polynomial qq). L.memP qf qfacs ==> deg qf >= 1) /\
                    L.memP g (L.map g_of qfacs))
          (ensures  is_primitive g /\ deg g >= 1)
          (decreases qfacs)
  = match qfacs with
    | qf :: rest ->
      eliminate (g == g_of qf) \/ L.memP g (L.map g_of rest)
      returns is_primitive g /\ deg g >= 1
      with _h1. per_elem_bridge qf
      and  _h2. map_g_of_props rest g

(*  STEP 1 : the ℤ-factorization existence (the Gauss bridge).
    For a primitive b of degree >= 1, there is a non-empty list of
    primitive degree>=1 integer polynomials, each dividing b, whose
    product is an associate of b.  (ℚ-squarefreeness is NOT needed
    here — a ℚ-factorization exists for any degree>=1 polynomial; and
    ℤ-irreducibility of the factors is NOT claimed, only divisibility,
    which is what the reaching step downstream consumes.) *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let int_factorization_exists (b: polynomial int)
  : Lemma (requires is_primitive b /\ deg b >= 1)
          (ensures exists (facs: list (polynomial int)).
             Cons? facs /\
             (divides (R.poly_prod facs) b /\ divides b (R.poly_prod facs)) /\
             (forall (g: polynomial int). L.memP g facs ==>
                (is_primitive g /\ deg g >= 1 /\ divides g b)))
  = H.elim_equatable_laws (polynomial int) ();
    H.elim_equatable_laws qq ();
    embed_zq_deg b;                                   (* deg (embed b) == deg b >= 1 *)
    FE.poly_factorization_exists_aux #qq #BIN.ff (embed_zq b);
    eliminate exists (qfacs: list (polynomial qq)).
                Cons? qfacs /\ (R.poly_prod qfacs = embed_zq b) /\
                (forall (qf: polynomial qq). L.memP qf qfacs ==> IR.poly_irreducible #qq #BIN.ff qf)
    returns (exists (facs: list (polynomial int)).
               Cons? facs /\
               (divides (R.poly_prod facs) b /\ divides b (R.poly_prod facs)) /\
               (forall (g: polynomial int). L.memP g facs ==>
                  (is_primitive g /\ deg g >= 1 /\ divides g b)))
    with _hq.
    begin
      let facs = L.map g_of qfacs in
      let pP = R.poly_prod facs in
      let ca = ca_prod qfacs in
      let dd = d_prod qfacs in
      let pq = R.poly_prod qfacs in
      (* irreducible ==> deg >= 1 for each ℚ-factor *)
      assert (forall (qf: polynomial qq). L.memP qf qfacs ==> deg qf >= 1);
      prod_primitive qfacs;                           (* is_primitive pP *)
      prod_scalar qfacs;                              (* ca>0, dd<>0, scalar reln *)
      (* pull  scale(embed dd) pq  onto  scale(embed dd)(embed b) *)
      scale_congr_poly (embed_zq_const dd) pq (embed_zq b);
      poly_eq_transitivity (R.poly_scale (embed_zq_const ca) (embed_zq pP))
                           (R.poly_scale (embed_zq_const dd) pq)
                           (R.poly_scale (embed_zq_const dd) (embed_zq b));
      (* embed the integer scalings *)
      embed_scale ca pP;                              (* embed(scale ca pP) ~ scale(embed ca)(embed pP) *)
      embed_scale dd b;                               (* embed(scale dd b)  ~ scale(embed dd)(embed b)  *)
      poly_eq_symmetry (embed_zq (R.poly_scale dd b))
                       (R.poly_scale (embed_zq_const dd) (embed_zq b));
      poly_eq_transitivity (embed_zq (R.poly_scale ca pP))
                           (R.poly_scale (embed_zq_const ca) (embed_zq pP))
                           (R.poly_scale (embed_zq_const dd) (embed_zq b));
      poly_eq_transitivity (embed_zq (R.poly_scale ca pP))
                           (R.poly_scale (embed_zq_const dd) (embed_zq b))
                           (embed_zq (R.poly_scale dd b));
      embed_zq_injective (R.poly_scale ca pP) (R.poly_scale dd b);   (* poly_eq (scale ca pP)(scale dd b) *)
      primitive_qq_associate_implies_int_associate pP b ca dd;      (* pP ~ ±b *)
      mutual_divides_of_assoc pP b;                   (* divides pP b /\ divides b pP *)
      (* per-factor properties *)
      introduce forall (g: polynomial int). L.memP g facs ==>
                  (is_primitive g /\ deg g >= 1 /\ divides g b)
      with begin
        introduce L.memP g facs ==> (is_primitive g /\ deg g >= 1 /\ divides g b)
        with _hg.
        begin
          map_g_of_props qfacs g;                     (* is_primitive g /\ deg g >= 1 *)
          poly_prod_mem_divides facs g;               (* divides g pP *)
          divides_trans g pP b                        (* divides g b *)
        end
      end;
      introduce exists (facs2: list (polynomial int)).
                  Cons? facs2 /\
                  (divides (R.poly_prod facs2) b /\ divides b (R.poly_prod facs2)) /\
                  (forall (g: polynomial int). L.memP g facs2 ==>
                     (is_primitive g /\ deg g >= 1 /\ divides g b))
      with facs and ()
    end
#pop-options

(* ================================================================ *)
(*  4.  STEP 2 : factor_Q completeness (capstone).                   *)
(* ================================================================ *)

(*  For a primitive b of degree >= 1 whose monic-ization is ℚ-square-
    free, there is a good prime p and a non-empty integer factor list
    whose product is an associate of b, such that EVERY factor g is
    reached — as its monic image monic_factor_of b g — in the
    executable candidate list monic_candidates (monicize_pos b) p. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let factor_Q_complete (b: polynomial int)
  : Lemma (requires is_primitive b /\ deg b >= 1 /\
                    SF.square_free #qq #BIN.ff (embed_zq (NMZ.monicize_pos b)))
          (ensures exists (p:int{E.is_prime p}) (facs: list (polynomial int)).
             PS.is_good_prime p (NMZ.monicize_pos b) /\
             monic (PS.reduce_to_fp p (NMZ.monicize_pos b)) /\
             Cons? facs /\
             (divides (R.poly_prod facs) b /\ divides b (R.poly_prod facs)) /\
             (forall (g: polynomial int). L.memP g facs ==>
                (exists (d: polynomial int).
                   L.memP d (ZCplt.monic_candidates (NMZ.monicize_pos b) p) /\
                   poly_eq d (NMZ.monic_factor_of b g))))
  = H.elim_equatable_laws (polynomial int) ();
    let m = NMZ.monicize_pos b in
    NMZ.monicize_monic b;                    (* monic m *)
    NMZ.monicize_deg b;                      (* deg m == deg b *)
    int_factorization_exists b;              (* exists facs. product-assoc-b + per-g props *)
    PE.good_prime_exists_sqfree m;           (* exists p. is_good_prime p m *)
    eliminate exists (p:int{E.is_prime p}). PS.is_good_prime p m
    returns (exists (p:int{E.is_prime p}) (facs: list (polynomial int)).
               PS.is_good_prime p m /\
               monic (PS.reduce_to_fp p m) /\
               Cons? facs /\
               (divides (R.poly_prod facs) b /\ divides b (R.poly_prod facs)) /\
               (forall (g: polynomial int). L.memP g facs ==>
                  (exists (d: polynomial int).
                     L.memP d (ZCplt.monic_candidates m p) /\
                     poly_eq d (NMZ.monic_factor_of b g))))
    with hp.
    begin
      NMZ.good_prime_monic_reduction p m;    (* monic (reduce_to_fp p m) *)
      eliminate exists (facs: list (polynomial int)).
                  Cons? facs /\
                  (divides (R.poly_prod facs) b /\ divides b (R.poly_prod facs)) /\
                  (forall (g: polynomial int). L.memP g facs ==>
                     (is_primitive g /\ deg g >= 1 /\ divides g b))
      returns (exists (p:int{E.is_prime p}) (facs: list (polynomial int)).
                 PS.is_good_prime p m /\
                 monic (PS.reduce_to_fp p m) /\
                 Cons? facs /\
                 (divides (R.poly_prod facs) b /\ divides b (R.poly_prod facs)) /\
                 (forall (g: polynomial int). L.memP g facs ==>
                    (exists (d: polynomial int).
                       L.memP d (ZCplt.monic_candidates m p) /\
                       poly_eq d (NMZ.monic_factor_of b g))))
      with hf.
      begin
        introduce forall (g: polynomial int). L.memP g facs ==>
                    (exists (d: polynomial int).
                       L.memP d (ZCplt.monic_candidates m p) /\
                       poly_eq d (NMZ.monic_factor_of b g))
        with begin
          introduce L.memP g facs ==>
                      (exists (d: polynomial int).
                         L.memP d (ZCplt.monic_candidates m p) /\
                         poly_eq d (NMZ.monic_factor_of b g))
          with _hg.
            NMZ.nonmonic_factor_reached b g p    (* deg g>=1, divides g b from hf *)
        end;
        introduce exists (p2:int{E.is_prime p2}) (facs2: list (polynomial int)).
                    PS.is_good_prime p2 m /\
                    monic (PS.reduce_to_fp p2 m) /\
                    Cons? facs2 /\
                    (divides (R.poly_prod facs2) b /\ divides b (R.poly_prod facs2)) /\
                    (forall (g: polynomial int). L.memP g facs2 ==>
                       (exists (d: polynomial int).
                          L.memP d (ZCplt.monic_candidates m p2) /\
                          poly_eq d (NMZ.monic_factor_of b g)))
        with p facs and ()
      end
    end
#pop-options
