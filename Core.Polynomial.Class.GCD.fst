module Core.Polynomial.Class.GCD

(*
   Implementation of polynomial GCD via the Euclidean algorithm.
   See the .fsti for the exposed surface and the deferred-work notes.
*)

module TC = FStar.Tactics.Typeclasses
module L  = FStar.List.Tot

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial.Class
open Core.Polynomial.Class.Div
open Core.Polynomial.Class.Unique

(* ------------------------------------------------------------------ *)
(*  Termination measure                                               *)
(* ------------------------------------------------------------------ *)

let degree_measure (#t:Type) {| cr: commutative_ring t |}
                   (p: polynomial t) : nat
  = match poly_deg p with
    | None   -> 0
    | Some n -> Prims.op_Addition n 1

let degree_measure_zero_iff_zero
    (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (degree_measure p == 0 <==> None? (poly_deg p))
  = ()

(* Generic CR helper: from `c = a + b`, conclude `c + neg a = b`.
   Used to bridge `poly_divmod_correct` to a divisibility-of-remainder
   statement in the polynomial commutative ring. *)
private let cancel_helper
    (#t:Type) {| cr: commutative_ring t |} (a b c: t)
  : Lemma (requires eq c (add a b))
          (ensures  eq (add c (neg a)) b)
  = reflexivity (neg a);
    add_congruence c (neg a) (add a b) (neg a);
    assert (eq (add (add a b) (neg a)) b) by Core.Tactics.CanonRing.canon_ring ();
    transitivity (add c (neg a)) (add (add a b) (neg a)) b

(* Key termination lemma. *)
private let degree_measure_decreases
    (#t:Type) {| f: field t |}
    (p q: polynomial t)
  : Lemma (requires Some? (poly_deg q))
          (ensures  (let (_, r) = poly_divmod #t #f p q in
                     degree_measure r < degree_measure q))
  = poly_divmod_correct_degree #t #f p q

(* ------------------------------------------------------------------ *)
(*  Euclidean GCD                                                     *)
(* ------------------------------------------------------------------ *)

let rec poly_gcd (#t:Type) {| f: field t |} (p q: polynomial t)
  : Tot (polynomial t) (decreases (degree_measure q))
  = match poly_deg q with
    | None   -> p
    | Some _ ->
        let (_, r) = poly_divmod #t #f p q in
        degree_measure_decreases #t #f p q;
        poly_gcd q r

let poly_gcd_base
    (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires None? (poly_deg q))
          (ensures  poly_gcd #t #f p q == p)
  = ()

let poly_gcd_step
    (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires Some? (poly_deg q))
          (ensures  (let (_, r) = poly_divmod #t #f p q in
                     poly_gcd #t #f p q == poly_gcd #t #f q r))
  = ()

(* ------------------------------------------------------------------ *)
(*  GCD divisibility: gcd | p AND gcd | q                             *)
(*                                                                    *)
(*  Proven jointly via induction on `degree_measure q`.               *)
(* ------------------------------------------------------------------ *)

let rec gcd_divides_both
    (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (ensures  divides (poly_gcd #t #f p q) p /\
                    divides (poly_gcd #t #f p q) q)
          (decreases (degree_measure q))
  = let g = poly_gcd #t #f p q in
    match poly_deg q with
    | None ->
        divides_refl p;
        (* poly_deg q = None ⟹ q = []; poly_zero #t == ([] <: polynomial t) *)
        assert (q == (poly_zero #t));
        divides_zero p
    | Some _ ->
        let (qot, r) = poly_divmod #t #f p q in
        degree_measure_decreases #t #f p q;
        gcd_divides_both #t #f q r;
        (* IH: divides g q  AND  divides g r *)
        assert (g == poly_gcd #t #f q r);
        divides_mul_right g q qot;
        divides_add g (poly_mul q qot) r;
        poly_divmod_correct #t #f p q;
        let s = poly_add (poly_mul q qot) r in
        symmetry p s;
        divides_congruence_right g s p

let gcd_divides_left
    (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (divides (poly_gcd #t #f p q) p)
  = gcd_divides_both #t #f p q

let gcd_divides_right
    (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (divides (poly_gcd #t #f p q) q)
  = gcd_divides_both #t #f p q

(* ------------------------------------------------------------------ *)
(*  GCD maximality: d | p ∧ d | q ⟹ d | gcd p q                       *)
(* ------------------------------------------------------------------ *)

let rec gcd_is_maximal
    (#t:Type) {| f: field t |} (p q d: polynomial t)
  : Lemma (requires divides d p /\ divides d q)
          (ensures  divides d (poly_gcd #t #f p q))
          (decreases (degree_measure q))
  = match poly_deg q with
    | None -> ()
    | Some _ ->
        let (qot, r) = poly_divmod #t #f p q in
        degree_measure_decreases #t #f p q;
        poly_divmod_correct #t #f p q;
        divides_mul_right d q qot;
        divides_sub d p (poly_mul q qot);
        let pcrc : polynomial_commutative_ring t =
          polynomial_commutative_ring_instance #t #(cr_of_id t #(id_of_f t)) in
        let cr_p : commutative_ring (polynomial t) = TC.solve in
        cancel_helper #(polynomial t) #cr_p (poly_mul q qot) r p;
        divides_congruence_right #(polynomial t) #cr_p
          d (add p (neg (mul q qot))) r;
        gcd_is_maximal #t #f q r d

(* ------------------------------------------------------------------ *)
(*  Extended GCD (Bézout)                                             *)
(* ------------------------------------------------------------------ *)

(* CR helper: base-case identity 1*p + 0*q = p.  Single-CR scope so
   canon_ring picks the right instance. *)
private let bezout_base_helper
    (#t:Type) {| cr: commutative_ring t |} (p q: t)
  : Lemma (eq (add (mul one p) (mul zero q)) p)
  = assert (eq (add (mul one p) (mul zero q)) p)
      by Core.Tactics.CanonRing.canon_ring ()

(* CR helper: step-case Bézout rearrangement.

   Given:
     p ~ q*quot + rem                               (poly_divmod_correct)
     a'*q + b'*rem ~ gv                             (IH)
   Conclude:
     b'*p + (a' - b'*quot)*q ~ gv

   The intermediate identity
     b'*(q*quot + rem) + (a' - b'*quot)*q  ==  a'*q + b'*rem
   is pure CR algebra and is discharged by canon_ring.  We chain it
   together with mul_congruence (substituting p) and transitivity. *)
private let bezout_step_helper
    (#t:Type) {| cr: commutative_ring t |}
    (q quot rem b' a' p gv: t)
  : Lemma (requires eq p (add (mul q quot) rem) /\
                    eq (add (mul a' q) (mul b' rem)) gv)
          (ensures  eq (add (mul b' p)
                            (mul (add a' (neg (mul b' quot))) q))
                       gv)
  = let coeff_term = add a' (neg (mul b' quot)) in
    let lhs = add (mul b' p) (mul coeff_term q) in
    let mid = add (mul b' (add (mul q quot) rem)) (mul coeff_term q) in
    let rhs = add (mul a' q) (mul b' rem) in
    (* mul b' p ~ mul b' (q*quot + rem) *)
    reflexivity b';
    mul_congruence b' p b' (add (mul q quot) rem);
    (* lhs ~ mid by congruence of (+) on the left summand *)
    reflexivity (mul coeff_term q);
    add_congruence (mul b' p) (mul coeff_term q)
                   (mul b' (add (mul q quot) rem)) (mul coeff_term q);
    (* mid = rhs (pure CR identity).  Spell out both sides so that
       canon_ring doesn't see let-bound `mid`/`rhs` as opaque atoms. *)
    assert (eq (add (mul b' (add (mul q quot) rem))
                    (mul (add a' (neg (mul b' quot))) q))
               (add (mul a' q) (mul b' rem)))
      by Core.Tactics.CanonRing.canon_ring ();
    (* lhs ~ mid ~ rhs ~ gv *)
    transitivity lhs mid rhs;
    transitivity lhs rhs gv

let rec poly_ext_gcd (#t:Type) {| f: field t |} (p q: polynomial t)
  : Tot (polynomial t & polynomial t & polynomial t)
        (decreases (degree_measure q))
  = match poly_deg q with
    | None   -> (poly_one #t, poly_zero #t, p)
    | Some _ ->
        let (quot, r) = poly_divmod #t #f p q in
        degree_measure_decreases #t #f p q;
        let (a', b', gv) = poly_ext_gcd #t #f q r in
        (b', poly_add a' (poly_neg (poly_mul b' quot)), gv)

let rec ext_gcd_correct (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (ensures (let (a, b, g) = poly_ext_gcd #t #f p q in
                    poly_eq (add (mul a p) (mul b q)) g))
          (decreases (degree_measure q))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    match poly_deg q with
    | None ->
        bezout_base_helper #(polynomial t) #cr_p p q
    | Some _ ->
        let (quot, r) = poly_divmod #t #f p q in
        degree_measure_decreases #t #f p q;
        ext_gcd_correct #t #f q r;
        let (a', b', gv) = poly_ext_gcd #t #f q r in
        poly_divmod_correct #t #f p q;
        (* poly_divmod_correct: poly_eq p (poly_add (poly_mul q quot) r) *)
        bezout_step_helper #(polynomial t) #cr_p q quot r b' a' p gv

let rec ext_gcd_is_gcd (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (ensures (let (_, _, g) = poly_ext_gcd #t #f p q in
                    poly_eq g (poly_gcd #t #f p q)))
          (decreases (degree_measure q))
  = match poly_deg q with
    | None ->
        poly_eq_reflexivity p
    | Some _ ->
        let (_, r) = poly_divmod #t #f p q in
        degree_measure_decreases #t #f p q;
        ext_gcd_is_gcd #t #f q r


(* ================================================================== *)
(*  GCD congruence                                                    *)
(* ================================================================== *)

(* CR-level helper: from x1 ~ y1*a1 + r1, x2 ~ y2*a2 + r2, x1 ~ x2, y1 ~ y2,
   conclude y1*a1 + r1 ~ y1*a2 + r2.  Single-CR scope to dodge the
   canon_ring carrier-resolution bug. *)
private let gcd_chain_helper
    (#t:Type) {| cr: commutative_ring t |}
    (y1 y2 x1 x2 a1 a2 r1 r2: t)
  : Lemma (requires eq x1 (add (mul y1 a1) r1) /\
                    eq x2 (add (mul y2 a2) r2) /\
                    eq x1 x2 /\ eq y1 y2)
          (ensures  eq (add (mul y1 a1) r1)
                       (add (mul y1 a2) r2))
  = symmetry x1 (add (mul y1 a1) r1);
    transitivity (add (mul y1 a1) r1) x1 x2;
    transitivity (add (mul y1 a1) r1) x2 (add (mul y2 a2) r2);
    reflexivity a2;
    mul_congruence y1 a2 y2 a2;
    reflexivity r2;
    add_congruence (mul y1 a2) r2 (mul y2 a2) r2;
    symmetry (add (mul y1 a2) r2) (add (mul y2 a2) r2);
    transitivity (add (mul y1 a1) r1)
                 (add (mul y2 a2) r2)
                 (add (mul y1 a2) r2)

let rec gcd_congruence (#t:Type) {| f: field t |}
                       (x1 x2 y1 y2: polynomial t)
  : Lemma (requires poly_eq x1 x2 /\ poly_eq y1 y2)
          (ensures  poly_eq (poly_gcd #t #f x1 y1)
                            (poly_gcd #t #f x2 y2))
          (decreases (degree_measure y1))
  = degree_well_defined y1 y2;
    match poly_deg y1 with
    | None ->
        poly_gcd_base #t #f x1 y1;
        poly_gcd_base #t #f x2 y2
    | Some _ ->
        let (a1, r1) = poly_divmod #t #f x1 y1 in
        let (a2, r2) = poly_divmod #t #f x2 y2 in
        poly_divmod_correct #t #f x1 y1;
        poly_divmod_correct #t #f x2 y2;
        poly_divmod_correct_degree #t #f x1 y1;
        poly_divmod_correct_degree #t #f x2 y2;
        let cr_p : commutative_ring (polynomial t) = TC.solve in
        gcd_chain_helper #(polynomial t) #cr_p y1 y2 x1 x2 a1 a2 r1 r2;
        poly_divmod_unique #t #f y1 a1 a2 r1 r2;
        poly_gcd_step #t #f x1 y1;
        poly_gcd_step #t #f x2 y2;
        degree_measure_decreases #t #f x1 y1;
        gcd_congruence #t #f y1 y2 r1 r2


(* ================================================================== *)
(*  Chain instances: gcd_domain → ufd → euclidean_domain              *)
(* ================================================================== *)

instance polynomial_gcd_domain_instance
    (#t:Type) {| f: field t |}
  : gcd_domain (polynomial t)
  = {
    gcd_id            = (polynomial_integral_domain_instance #t #(id_of_f t)).pid;
    gcd               = poly_gcd #t #f;
    gcd_congruence    = (fun x1 x2 y1 y2 -> gcd_congruence #t #f x1 x2 y1 y2);
    gcd_divides_left  = (fun x y -> gcd_divides_left  #t #f x y);
    gcd_divides_right = (fun x y -> gcd_divides_right #t #f x y);
    gcd_is_maximal    = (fun x y d -> gcd_is_maximal #t #f x y d);
  }

instance polynomial_ufd_instance
    (#t:Type) {| f: field t |}
  : ufd (polynomial t)
  = { ufd_gd = polynomial_gcd_domain_instance #t #f }

private let poly_euclidean_norm
    (#t:Type) {| cr: commutative_ring t |} (p: polynomial t) : nat
  = match poly_deg p with
    | None   -> 0
    | Some n -> n

private let poly_ed_divmod
    (#t:Type) {| f: field t |} (p q: polynomial t)
  : Pure (polynomial t & polynomial t)
         (requires is_nonzero q)
         (ensures  fun _ -> True)
  = poly_zero_is_unique q;
    assert (not (q == poly_zero #t));
    poly_divmod #t #f p q

private let poly_ed_divmod_correct
    (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires is_nonzero q)
          (ensures  (let (a, r) = poly_ed_divmod #t #f p q in
                     poly_eq p (poly_add (poly_mul q a) r)))
  = poly_zero_is_unique q;
    poly_divmod_correct #t #f p q

private let poly_ed_divmod_decreasing
    (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires is_nonzero q)
          (ensures  (let (_, r) = poly_ed_divmod #t #f p q in
                     is_nonzero r ==>
                     poly_euclidean_norm r < poly_euclidean_norm q))
  = poly_zero_is_unique q;
    poly_divmod_correct_degree #t #f p q;
    let (_, r) = poly_ed_divmod #t #f p q in
    (match poly_deg r with
     | None   -> ()
     | Some _ ->
         poly_zero_is_unique r;
         ())

instance polynomial_euclidean_domain_chain_instance
    (#t:Type) {| f: field t |}
  : euclidean_domain (polynomial t)
  = {
    ed_ufd               = polynomial_ufd_instance #t #f;
    euclidean_norm       = poly_euclidean_norm;
    ed_divmod            = (fun p q -> poly_ed_divmod #t #f p q);
    ed_divmod_correct    = (fun p q -> poly_ed_divmod_correct #t #f p q);
    ed_divmod_decreasing = (fun p q -> poly_ed_divmod_decreasing #t #f p q);
  }

(* ================================================================== *)
(*  Coprimality and Euclid's lemma                                    *)
(* ================================================================== *)

let coprime (#t:Type) {| f: field t |} (p q: polynomial t) : bool
  = poly_deg (poly_gcd #t #f p q) = Some 0


(* ================================================================== *)
(*  Euclid's lemma: coprime(p, q) /\ p | a*q  ⟹  p | a                *)
(* ================================================================== *)

(* When poly_deg p = Some 0, the polynomial is a singleton list whose
   sole element is its leading coefficient and is nonzero. *)
private let degree_zero_is_singleton
    (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (requires poly_deg p == Some 0)
          (ensures  p == [poly_lc p] /\ not ((poly_lc p) = (zero <: t)))
  = leading_coeff_nonzero p;
    assert (L.length p == 1);
    match p with
    | [a] -> assert (poly_lc p == a)

(* For c <> zero, the singleton [inv c] times the singleton [c] equals
   poly_one (the polynomial-ring identity).  Proven via direct list
   inspection and the field inversion law. *)
private let singleton_inv_mul_singleton
    (#t:Type) {| f: field t |} (c: t)
  : Lemma (requires not (c = (zero <: t)))
          (ensures  (let cinv = f.f_sf.sf_mig.inv c in
                     let lhs : polynomial t = [cinv] in
                     let rhs : polynomial t = [c] in
                     poly_eq (poly_mul lhs rhs) (poly_one #t)))
  = let cinv = f.f_sf.sf_mig.inv c in
    let lhs : polynomial t = [cinv] in
    let rhs : polynomial t = [c] in
    (* monomial cinv 0 == [cinv] (since cinv <> zero) *)
    monomial_zero_n_reveal cinv;
    assert (monomial cinv 0 == lhs);
    (* coeff (poly_mul lhs rhs) 0 = cinv * coeff rhs 0 = cinv * c *)
    monomial_mul_coeff cinv 0 rhs 0;
    assert (coeff (poly_mul lhs rhs) 0 = ((cinv * c) <: t));
    (* By field inversion: cinv * c ~ one *)
    f.f_sf.sf_mig.inversion_lemma c;
    assert (((cinv * c) <: t) = (one <: t));
    transitivity (coeff (poly_mul lhs rhs) 0) ((cinv * c) <: t) (one <: t);
    (* For i >= 1: coeff above degree is zero on both sides.
       poly_deg lhs = Some 0, poly_deg rhs = Some 0,
       poly_deg (poly_mul lhs rhs) = either None or Some 0 (it's a
       product of two trimmed singletons; either result is [(cinv*c)]
       if nonzero, or [] if cinv*c = zero — but cinv*c = one ≠ zero,
       so product is [(cinv*c)], degree 0). *)
    let aux (i:nat) : Lemma (coeff (poly_mul lhs rhs) i = coeff (poly_one #t) i)
      = if i = 0 then ()
        else begin
          (* poly_mul lhs rhs has degree at most 0+0 = 0 by monomial product *)
          monomial_mul_coeff cinv 0 rhs i;
          assert (coeff (poly_mul lhs rhs) i = ((cinv * coeff rhs i) <: t));
          (* coeff rhs i = zero for i >= 1 *)
          coeff_above_degree rhs i;
          assert (coeff rhs i = (zero <: t));
          reflexivity cinv;
          mul_congruence cinv (coeff rhs i) cinv (zero <: t);
          assert (((cinv * (zero <: t)) <: t) = (zero <: t))
            by Core.Tactics.CanonRing.canon_ring ();
          transitivity ((cinv * coeff rhs i) <: t)
                       ((cinv * (zero <: t)) <: t) (zero <: t);
          transitivity (coeff (poly_mul lhs rhs) i)
                       ((cinv * coeff rhs i) <: t) (zero <: t);
          (* coeff poly_one i for i >= 1 = zero *)
          coeff_above_degree (poly_one #t) i;
          symmetry (coeff (poly_one #t) i) (zero <: t);
          transitivity (coeff (poly_mul lhs rhs) i)
                       (zero <: t) (coeff (poly_one #t) i)
        end
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (poly_mul lhs rhs) (poly_one #t)

(* CR helper: a + b ~ a*1 + b in polynomial CR — but we need the
   euclid_lemma-shaped algebraic identity.  This helper assembles
   p | a*s*p, p | (a*q)*t, into p | a*g where g ~ s*p + t*q. *)
private let euclid_bezout_helper
    (#t:Type) {| cr: commutative_ring t |}
    (p q a s tt g: t)
  : Lemma (requires eq (add (mul s p) (mul tt q)) g)
          (ensures  eq (add (mul a (mul s p))
                            (mul a (mul tt q)))
                       (mul a g))
  = reflexivity a;
    mul_congruence a (add (mul s p) (mul tt q)) a g;
    assert (eq (mul a (add (mul s p) (mul tt q)))
               (add (mul a (mul s p)) (mul a (mul tt q))))
      by Core.Tactics.CanonRing.canon_ring ();
    symmetry (mul a (add (mul s p) (mul tt q)))
             (add (mul a (mul s p)) (mul a (mul tt q)));
    transitivity (add (mul a (mul s p)) (mul a (mul tt q)))
                 (mul a (add (mul s p) (mul tt q)))
                 (mul a g)

(* Helper: p | x  /\  eq y x  ⟹  p | y  is just divides_congruence_right
   with a small twist of argument order.  Also pre-bundle: a*(s*p) = (a*s)*p
   so p | (a*s)*p follows from p | p*c via divides_mul_right. *)
private let divides_a_times_sp
    (#t:Type) {| cr: commutative_ring t |} (p a s: t)
  : Lemma (divides p (mul a (mul s p)))
  = divides_refl p;
    divides_mul_right p p (mul a s);
    assert (eq (mul p (mul a s)) (mul a (mul s p)))
      by Core.Tactics.CanonRing.canon_ring ();
    divides_congruence_right p (mul p (mul a s)) (mul a (mul s p))

private let divides_a_times_tq
    (#t:Type) {| cr: commutative_ring t |} (p a q tt: t)
  : Lemma (requires divides p (mul a q))
          (ensures  divides p (mul a (mul tt q)))
  = divides_mul_right p (mul a q) tt;
    assert (eq (mul (mul a q) tt) (mul a (mul tt q)))
      by Core.Tactics.CanonRing.canon_ring ();
    divides_congruence_right p (mul (mul a q) tt) (mul a (mul tt q))

(* CR helper: a*1 ~ a. *)
private let mul_one_right_helper
    (#t:Type) {| cr: commutative_ring t |} (a: t)
  : Lemma (eq (mul a one) a)
  = assert (eq (mul a one) a) by Core.Tactics.CanonRing.canon_ring ()

let euclid_lemma (#t:Type) {| f: field t |} (p q a: polynomial t)
  : Lemma (requires Some? (poly_deg p) /\
                    coprime p q /\
                    divides p (poly_mul a q))
          (ensures  divides p a)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    let g = poly_gcd #t #f p q in
    assert (poly_deg g == Some 0);
    ext_gcd_correct #t #f p q;
    ext_gcd_is_gcd  #t #f p q;
    let (s, tt, gv) = poly_ext_gcd #t #f p q in
    (* gv ~ g *)
    (* Step 1: p | a*s*p *)
    divides_a_times_sp #(polynomial t) #cr_p p a s;
    (* Step 2: p | a*tt*q (from p | a*q given) *)
    divides_a_times_tq #(polynomial t) #cr_p p a q tt;
    (* Step 3: p | a*s*p + a*tt*q *)
    divides_add #(polynomial t) #cr_p p (mul a (mul s p)) (mul a (mul tt q));
    (* Step 4: a*s*p + a*tt*q ~ a * (s*p + tt*q) ~ a * gv (via Bezout) *)
    euclid_bezout_helper #(polynomial t) #cr_p p q a s tt gv;
    divides_congruence_right #(polynomial t) #cr_p
      p (add (mul a (mul s p)) (mul a (mul tt q))) (mul a gv);
    (* Step 5: gv ~ g, so a*gv ~ a*g *)
    reflexivity a;
    mul_congruence a gv a g;
    divides_congruence_right #(polynomial t) #cr_p p (mul a gv) (mul a g);
    (* Step 6: g = [c] for some c ≠ zero (degree_zero_is_singleton) *)
    degree_zero_is_singleton g;
    let c : t = poly_lc g in
    assert (g == [c]);
    assert (not (c = (zero <: t)));
    let cinv : t = f.f_sf.sf_mig.inv c in
    let g_inv : polynomial t = [cinv] in
    (* Step 7: poly_mul g_inv g ~ poly_one *)
    singleton_inv_mul_singleton #t #f c;
    assert (poly_eq (poly_mul g_inv g) (poly_one #t));
    (* Step 8: p | (a*g) * g_inv = a * (g * g_inv) ~ a * (g_inv * g) ~ a*1 ~ a *)
    divides_mul_right #(polynomial t) #cr_p p (mul a g) g_inv;
    (* (a*g)*g_inv ~ a*(g*g_inv) ~ a*(g_inv*g) ~ a*poly_one ~ a *)
    let assoc_helper (#u:Type) {| cr: commutative_ring u |} (x y z: u)
      : Lemma (eq (mul (mul x y) z) (mul x (mul y z)))
      = assert (eq (mul (mul x y) z) (mul x (mul y z)))
          by Core.Tactics.CanonRing.canon_ring ()
    in
    let comm_helper (#u:Type) {| cr: commutative_ring u |} (x y: u)
      : Lemma (eq (mul x y) (mul y x))
      = assert (eq (mul x y) (mul y x)) by Core.Tactics.CanonRing.canon_ring ()
    in
    assoc_helper #(polynomial t) #cr_p a g g_inv;
    comm_helper #(polynomial t) #cr_p g g_inv;
    reflexivity a;
    mul_congruence a (mul g g_inv) a (mul g_inv g);
    transitivity (mul (mul a g) g_inv) (mul a (mul g g_inv)) (mul a (mul g_inv g));
    mul_congruence a (mul g_inv g) a (poly_one #t);
    transitivity (mul (mul a g) g_inv) (mul a (mul g_inv g)) (mul a (poly_one #t));
    mul_one_right_helper #(polynomial t) #cr_p a;
    transitivity (mul (mul a g) g_inv) (mul a (poly_one #t)) a;
    divides_congruence_right #(polynomial t) #cr_p p (mul (mul a g) g_inv) a
