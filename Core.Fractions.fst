module Core.Fractions

(*
   Field-of-fractions construction for the diamond-free tower.

   Given `integral_domain t`, build `field (fraction d)`. The single
   published instance is `fraction_field`; everything else (equatable,
   acg, ring, cr, domain, id, skewfield) is reached automatically
   through the foundation's projection chain.

   The file is structured top-down:
     §1  Ring/domain-level helpers (neg_unique, neg_mul_*, left_cancel,
         mul_middle_swap).
     §2  Equality on fractions (cross-multiplication) and the
         `equatable (fraction d)` content.
     §3  Constants (`fraction_zero`, `fraction_one`) and the basic
         smart constructor `( / )`.
     §4  Addition: `fraction_add`, congruences, identity, commutativity,
         associativity.
     §5  Negation, group law.
     §6  Multiplication: `fraction_mul`, congruences, identity, comm,
         assoc, distributivity, absorption.
     §7  Domain law and `one ≠ zero` on `fraction d`.
     §8  Inversion: `fraction_inv`, inversion lemmas.
     §9  Bundle assembly: the single `fraction_field` instance.
     §10 Convenience `( / )` published name.
*)

module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Helpers
open Core.Tactics.CanonRing

(* ================================================================ *)
(*  §1. Ring / domain helpers                                       *)
(* ================================================================ *)

private let neg_unique (#t:Type) {| d: commutative_ring t |} (p q: t)
  : Lemma (requires p + q = zero)
          (ensures  p = neg q) =
    assert (eq p (p + q + -q)) by canon_ring();
    reflexivity (-q);
    add_congruence (p + q) (-q) zero (-q);
    zero_plus_x (-q);
    transitivity (p + q + -q) (zero + -q) (-q);
    transitivity p (p + q + -q) (-q)

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let neg_mul_right (#t:Type) {| d: integral_domain t |} (x y: t)
  : Lemma (x * neg y = neg (x * y) /\ neg (x*y) = x * neg y)
  = assert (x * neg y = neg (x * y)) by canon_ring();
    assert (neg (x*y) = x * neg y) by canon_ring()

private let neg_mul_left (#t:Type) {| d: integral_domain t |} (x y: t)
  : Lemma (neg x * y = neg (x * y))
  = assert (neg x * y = neg (x * y)) by canon_ring()
#pop-options

(* Workhorse: in an integral domain, a*b = 0 ==> a=0 \/ b=0. The
   `domain_law` field gives the iff directly. *)
private let domain_zero_div (#t:Type) {| d: integral_domain t |} (a b: t)
  : Lemma (requires a * b = zero) (ensures a = zero \/ b = zero)
  = domain_law a b


let test left_cancel (#t:Type) {| d: integral_domain t |} (c a b: t)
  : Lemma (requires c * a = c * b /\ not (c = zero))
          (ensures  a = b) = 
  trans_for_calc t _;
  elim_equatable_laws t _;
  neg_mul_right c b;
  left_distributivity c a (-b);
  add_congruence (c*a) (c*(-b)) (c*b) (-(c*b));
  x_plus_neg_x (c*b);
  domain_law c (a + -b);    
  add_congruence (a -- b) b zero b;
  add_associativity a (-b) b;
  zero_plus_x b;
  neg_x_plus_x b;
  add_congruence a (-b + b) a zero;
  x_plus_zero a 

(* Left-cancellation over an integral domain: if c is nonzero, c*a = c*b
   forces a = b. *)
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let left_cancel (#t:Type) {| d: integral_domain t |} (c a b: t)
  : Lemma (requires c * a = c * b /\ not (c = zero))
          (ensures  a = b)
  = left_distributivity c a (neg b);
    neg_mul_right c b;
    reflexivity (c * a);
    add_congruence (c * a) (c * neg b) (c * a) (neg (c * b));
    transitivity (c * (a + neg b)) (c * a + c * neg b) (c * a + neg (c * b));
    reflexivity (neg (c * b));
    symmetry (c * a) (c * b);
    add_congruence (c * a) (neg (c * b)) (c * b) (neg (c * b));
    transitivity (c * (a + neg b)) (c * a + neg (c * b)) (c * b + neg (c * b));
    x_plus_neg_x (c * b);
    transitivity (c * (a + neg b)) (c * b + neg (c * b)) zero;
    domain_zero_div c (a + neg b);
    assert (a + neg b = zero);
    neg_unique a (neg b);
    x_plus_neg_x b;
    neg_unique b (neg b);
    symmetry b (neg (neg b));
    transitivity a (neg (neg b)) b
#pop-options

(* AC-juggling helper: (a*b)*(c*d) = (a*c)*(b*d). Used repeatedly in
   fraction multiplication / addition proofs. *)
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let mul_middle_swap (#t:Type) {| d: integral_domain t |} (a b c e: t)
  : Lemma ((a * b) * (c * e) = (a * c) * (b * e))
  = assert ((a * b) * (c * e) = (a * c) * (b * e)) by canon_ring()
#pop-options

(* ================================================================ *)
(*  §2. Equality on fractions                                       *)
(* ================================================================ *)

(* Cross-multiplication: a/b = c/d  iff  a*d = c*b in t. *)
let fraction_eq (#t:Type) {| d: integral_domain t |} (x y: fraction d) : bool =
  (x.num * y.den) = (x.den * y.num)

private let fraction_eq_from_num_den
  (#t:Type) {| d: integral_domain t |} (x y: fraction d)
  : Lemma (requires (x.den = y.den) /\ (x.num = y.num))
          (ensures fraction_eq x y)
  = let a, b, c, e : t & t & t & t = x.num, x.den, y.num, y.den in
    symmetry b e;
    mul_congruence a e c b;
    mul_commutativity c b;
    transitivity (a * e) (c * b) (b * c)

private let fraction_eq_refl
  (#t:Type) {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_eq x x)
  = mul_commutativity x.num x.den

private let fraction_eq_symm
  (#t:Type) {| d: integral_domain t |} (x y: fraction d)
  : Lemma (fraction_eq x y <==> fraction_eq y x)
  = let aux (p q: fraction d) : Lemma (fraction_eq p q ==> fraction_eq q p)
      = mul_commutativity q.num p.den;
        mul_commutativity p.num q.den;
        symmetry (p.den * q.num) (p.num * q.den);
        if fraction_eq p q then begin
          transitivity (q.num * p.den) (p.den * q.num) (p.num * q.den);
          transitivity (q.num * p.den) (p.num * q.den) (q.den * p.num)
        end
    in aux x y; aux y x

(* Routine wrapper: x = y implies x*z = y*z and z*x = z*y. *)
private let mul_cong_3 (#t:Type) {| d: integral_domain t |} (x y z: t)
  : Lemma (requires x = y) (ensures (x * z = y * z) /\ (z * x = z * y))
  = reflexivity z;
    mul_congruence x z y z;
    mul_congruence z x z y

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
private let fraction_eq_trans
  (#t:Type) {| dom: integral_domain t |} (x y z: fraction dom)
  : Lemma (requires fraction_eq x y /\ fraction_eq y z)
          (ensures fraction_eq x z)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let (a, b, c, dn, e, f) : (t & t & t & t & t & t)
      = (x.num, x.den, y.num, y.den, z.num, z.den) in
    (* b, dn, f are all nonzero by refinement on `den`. *)
    mul_cong_3 (c * f) (dn * e) (a * dn);
    mul_cong_3 (a * dn) (b * c) (dn * e);
    assert ((b * c) * (dn * e) = (a * dn) * (c * f));
    calc (=) {
      (b * c) * (dn * e);
      = { mul_associativity (b * c) dn e }
      ((b * c) * dn) * e;
      = { mul_associativity b c dn;
          mul_cong_3 ((b * c) * dn) (b * (c * dn)) e }
      (b * (c * dn)) * e;
      = { mul_commutativity b (c * dn);
          mul_cong_3 (b * (c * dn)) ((c * dn) * b) e;
          mul_associativity (c * dn) b e }
      (c * dn) * (b * e);
    };
    calc (=) {
      (a * dn) * (c * f);
      = { mul_associativity a dn (c * f);
          mul_associativity dn c f;
          mul_cong_3 (dn * (c * f)) ((dn * c) * f) a }
      a * ((dn * c) * f);
      = { mul_commutativity dn c;
          mul_cong_3 (dn * c) (c * dn) f;
          mul_cong_3 ((dn * c) * f) ((c * dn) * f) a;
          mul_commutativity a ((c * dn) * f);
          mul_associativity (c * dn) f a;
          mul_commutativity f a;
          mul_cong_3 (f * a) (a * f) (c * dn) }
      (c * dn) * (a * f);
    };
    transitivity ((c * dn) * (a * f)) ((a * dn) * (c * f)) ((b * c) * (dn * e));
    transitivity ((c * dn) * (a * f)) ((b * c) * (dn * e)) ((c * dn) * (b * e));
    assert ((c * dn) * (a * f) = (c * dn) * (b * e));
    if not (c * dn = zero) then
      left_cancel (c * dn) (a * f) (b * e)
    else begin
      (* c*dn = 0; dn ≠ 0 (refinement) ⇒ c = 0. *)
      domain_zero_div c dn;
      assert (c = zero);
      (* From a*dn = b*c and c = 0: a*dn = b*0 = 0, with dn ≠ 0 ⇒ a = 0. *)
      reflexivity b;
      mul_congruence b c b zero;
      x_mul_zero b;
      transitivity (b * c) (b * zero) zero;
      symmetry (b * c) (a * dn);
      transitivity (a * dn) (b * c) zero;
      domain_zero_div a dn;
      assert (a = zero);
      (* From c*f = dn*e and c = 0: 0*f = dn*e, with dn ≠ 0 ⇒ e = 0. *)
      reflexivity f;
      mul_congruence c f zero f;
      zero_mul_x f;
      transitivity (c * f) (zero * f) zero;
      symmetry (c * f) (dn * e);
      transitivity (dn * e) (c * f) zero;
      domain_zero_div dn e;
      assert (e = zero);
      (* Now a*f = 0*f = 0 = b*0 = b*e. *)
      reflexivity f;
      mul_congruence a f zero f;
      zero_mul_x f;
      transitivity (a * f) (zero * f) zero;
      reflexivity b;
      mul_congruence b e b zero;
      x_mul_zero b;
      transitivity (b * e) (b * zero) zero;
      symmetry (b * e) zero;
      transitivity (a * f) zero (b * e)
    end
#pop-options

let fraction_equatable (t:Type) (d: integral_domain t)
  : equatable (fraction d) = {
    eq           = (fun x y -> fraction_eq #t #d x y);
    reflexivity  = (fun x -> fraction_eq_refl #t #d x);
    symmetry     = (fun x y -> fraction_eq_symm #t #d x y);
    transitivity = (fun x y z -> fraction_eq_trans #t #d x y z);
  }

(* ================================================================ *)
(*  §3. Constants and the smart constructor                         *)
(* ================================================================ *)

let fraction_zero (t:Type) {| d: integral_domain t |} : fraction d =
  let _: squash (not ((one <: t) = (zero <: t))) = d.id_one_ne_zero in
  Fraction (zero <: t) (one <: t)

let fraction_one  (t:Type) {| d: integral_domain t |} : fraction d =
  let _: squash (not ((one <: t) = (zero <: t))) = d.id_one_ne_zero in
  Fraction (one <: t) (one <: t)

private let prod_den_nonzero
  (#t:Type) {| d: integral_domain t |} (x y: fraction d)
  : Lemma (is_nonzero (x.den * y.den))
  = domain_nonzero_mul_nonzero x.den y.den

(* ================================================================ *)
(*  §4. Addition                                                    *)
(* ================================================================ *)

let fraction_add (#t:Type) {| d: integral_domain t |} (x y: fraction d)
  : fraction d
  = let a, b, c, e : t & t & t & t = x.num, x.den, y.num, y.den in
    prod_den_nonzero x y;
    let num : t = a * e + b * c in
    let den : t = b * e in
    Fraction num den

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let fraction_add_is_commutative
  (#t:Type) {| d: integral_domain t |} (x y: fraction d)
  : Lemma (fraction_eq (fraction_add x y) (fraction_add y x))
  = let a, b, c, e : t & t & t & t = x.num, x.den, y.num, y.den in
    assert (a * e + b * c = c * b + e * a) by canon_ring();
    assert (b * e = e * b) by canon_ring();
    fraction_eq_from_num_den (fraction_add x y) (fraction_add y x)
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let fraction_add_is_associative
  (#t:Type) {| dom: integral_domain t |} (x y z: fraction dom)
  : Lemma (fraction_eq
             (fraction_add (fraction_add x y) z)
             (fraction_add x (fraction_add y z)))
  = let a, b, c, dd, e, f : t & t & t & t & t & t =
      x.num, x.den, y.num, y.den, z.num, z.den in
    prod_den_nonzero x y;
    prod_den_nonzero y z;
    prod_den_nonzero (fraction_add x y) z;
    prod_den_nonzero x (fraction_add y z);
    assert ((a * dd + b * c) * f + (b * dd) * e
          = a * (dd * f) + b * (c * f + dd * e)) by canon_ring();
    assert ((b * dd) * f = b * (dd * f)) by canon_ring();
    fraction_eq_from_num_den
      (fraction_add (fraction_add x y) z)
      (fraction_add x (fraction_add y z))
#pop-options

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let fraction_add_left_congruence
  (#t:Type) {| dom: integral_domain t |} (x1 x2 y: fraction dom)
  : Lemma (requires fraction_eq x1 x2)
          (ensures  fraction_eq (fraction_add x1 y) (fraction_add x2 y))
  = let a, b, e, f, c, dd : t & t & t & t & t & t =
      x1.num, x1.den, x2.num, x2.den, y.num, y.den in
    elim_equatable_laws t ();
    trans_for_calc t ();
    prod_den_nonzero x1 y;
    prod_den_nonzero x2 y;
    mul_middle_swap a dd f dd;
    mul_congruence (a * f) (dd * dd) (b * e) (dd * dd);
    mul_middle_swap b e dd dd;
    transitivity ((a * dd) * (f * dd)) ((a * f) * (dd * dd)) ((b * e) * (dd * dd));
    transitivity ((a * dd) * (f * dd)) ((b * e) * (dd * dd)) ((b * dd) * (e * dd));
    mul_middle_swap b c f dd;
    mul_middle_swap b dd f c;
    mul_commutativity c dd;
    mul_congruence (b * f) (c * dd) (b * f) (dd * c);
    symmetry ((b * dd) * (f * c)) ((b * f) * (dd * c));
    transitivity ((b * c) * (f * dd)) ((b * f) * (c * dd)) ((b * f) * (dd * c));
    transitivity ((b * c) * (f * dd)) ((b * f) * (dd * c)) ((b * dd) * (f * c));
    add_congruence ((a * dd) * (f * dd)) ((b * c) * (f * dd))
                   ((b * dd) * (e * dd)) ((b * dd) * (f * c));
    right_distributivity (f * dd) (a * dd) (b * c);
    left_distributivity  (b * dd) (e * dd) (f * c);
    transitivity ((a * dd + b * c) * (f * dd))
                 ((a * dd) * (f * dd) + (b * c) * (f * dd))
                 ((b * dd) * (e * dd) + (b * dd) * (f * c));
    symmetry ((b * dd) * (e * dd + f * c))
             ((b * dd) * (e * dd) + (b * dd) * (f * c));
    transitivity ((a * dd + b * c) * (f * dd))
                 ((b * dd) * (e * dd) + (b * dd) * (f * c))
                 ((b * dd) * (e * dd + f * c))
#pop-options

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
private let fraction_add_right_congruence
  (#t:Type) {| dom: integral_domain t |} (x y1 y2: fraction dom)
  : Lemma (requires fraction_eq y1 y2)
          (ensures  fraction_eq (fraction_add x y1) (fraction_add x y2))
  = fraction_add_is_commutative x y1;
    fraction_add_left_congruence y1 y2 x;
    fraction_add_is_commutative y2 x;
    fraction_eq_trans (fraction_add x y1) (fraction_add y1 x) (fraction_add y2 x);
    fraction_eq_trans (fraction_add x y1) (fraction_add y2 x) (fraction_add x y2)

private let fraction_add_congruence
  (#t:Type) {| dom: integral_domain t |} (x1 y1 x2 y2: fraction dom)
  : Lemma (requires fraction_eq x1 x2 /\ fraction_eq y1 y2)
          (ensures  fraction_eq (fraction_add x1 y1) (fraction_add x2 y2))
  = fraction_add_left_congruence  x1 x2 y1;
    fraction_add_right_congruence x2 y1 y2;
    fraction_eq_trans (fraction_add x1 y1) (fraction_add x2 y1) (fraction_add x2 y2)
#pop-options

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let fraction_add_left_identity
  (#t:Type) {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_eq (fraction_add (fraction_zero t) x) x)
  = let a, b : t & t = x.num, x.den in
    prod_den_nonzero (fraction_zero t #d) x;
    assert ((zero * b + one * a) * b = (one * b) * a) by canon_ring()

private let fraction_add_right_identity
  (#t:Type) {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_eq (fraction_add x (fraction_zero t)) x)
  = fraction_add_is_commutative x (fraction_zero t #d);
    fraction_add_left_identity x;
    fraction_eq_trans
      (fraction_add x (fraction_zero t #d))
      (fraction_add (fraction_zero t #d) x)
      x
#pop-options

(* ================================================================ *)
(*  §5. Negation and group law                                      *)
(* ================================================================ *)

let fraction_neg (#t:Type) {| d: integral_domain t |} (x: fraction d)
  : fraction d
  = Fraction (neg x.num) x.den

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let fraction_neg_congruence
  (#t:Type) {| d: integral_domain t |} (x y: fraction d)
  : Lemma (requires fraction_eq x y)
          (ensures  fraction_eq (fraction_neg x) (fraction_neg y))
  = let a, b, c, e : t & t & t & t = x.num, x.den, y.num, y.den in
    elim_equatable_laws t ();
    trans_for_calc t ();
    neg_mul_left a e;
    neg_congruence (a * e) (b * c);
    transitivity (neg a * e) (neg (a * e)) (neg (b * c));
    neg_mul_right b c;
    symmetry (b * neg c) (neg (b * c));
    transitivity (neg a * e) (neg (b * c)) (b * neg c)
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
private let fraction_negation_r
  (#t:Type) {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_eq (fraction_add x (fraction_neg x)) (fraction_zero t))
  = let a, b : t & t = x.num, x.den in
    prod_den_nonzero x (fraction_neg x);
    assert ((a * b + b * neg a) * one = (b * b) * zero) by canon_ring()

private let fraction_negation_l
  (#t:Type) {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_eq (fraction_add (fraction_neg x) x) (fraction_zero t))
  = fraction_add_is_commutative (fraction_neg x) x;
    fraction_negation_r x;
    fraction_eq_trans
      (fraction_add (fraction_neg x) x)
      (fraction_add x (fraction_neg x))
      (fraction_zero t #d)
#pop-options

(* ================================================================ *)
(*  §6. Multiplication                                              *)
(* ================================================================ *)

let fraction_mul (#t:Type) {| d: integral_domain t |} (x y: fraction d)
  : fraction d
  = let a, b, c, e : t & t & t & t = x.num, x.den, y.num, y.den in
    prod_den_nonzero x y;
    let num : t = a * c in
    let den : t = b * e in
    Fraction num den

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let fraction_mul_congruence
  (#t:Type) {| dom: integral_domain t |} (x1 y1 x2 y2: fraction dom)
  : Lemma (requires fraction_eq x1 x2 /\ fraction_eq y1 y2)
          (ensures  fraction_eq (fraction_mul x1 y1) (fraction_mul x2 y2))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let a, b, e, f : t & t & t & t = x1.num, x1.den, x2.num, x2.den in
    let c, dd, g, h : t & t & t & t = y1.num, y1.den, y2.num, y2.den in
    mul_middle_swap a c f h;
    mul_congruence (a * f) (c * h) (b * e) (dd * g);
    mul_middle_swap b e dd g;
    transitivity ((a * c) * (f * h)) ((a * f) * (c * h)) ((b * e) * (dd * g));
    transitivity ((a * c) * (f * h)) ((b * e) * (dd * g)) ((b * dd) * (e * g))

private let fraction_mul_is_associative
  (#t:Type) {| dom: integral_domain t |} (x y z: fraction dom)
  : Lemma (fraction_eq (fraction_mul (fraction_mul x y) z)
                       (fraction_mul x (fraction_mul y z)))
  = let a, b, c, dd, e, f : t & t & t & t & t & t =
      x.num, x.den, y.num, y.den, z.num, z.den in
    assert ((a * c) * e = a * (c * e)) by canon_ring();
    assert ((b * dd) * f = b * (dd * f)) by canon_ring();
    fraction_eq_from_num_den
      (fraction_mul (fraction_mul x y) z)
      (fraction_mul x (fraction_mul y z))

private let fraction_mul_is_commutative
  (#t:Type) {| dom: integral_domain t |} (x y: fraction dom)
  : Lemma (fraction_eq (fraction_mul x y) (fraction_mul y x))
  = assert (x.num * y.num = y.num * x.num) by canon_ring();
    assert (x.den * y.den = y.den * x.den) by canon_ring();
    fraction_eq_from_num_den (fraction_mul x y) (fraction_mul y x)
#pop-options

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let fraction_mul_left_identity
  (#t:Type) {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_eq (fraction_mul (fraction_one t) x) x)
  = let a, b : t & t = x.num, x.den in
    assert ((one * a) * b = (one * b) * a) by canon_ring()

private let fraction_mul_right_identity
  (#t:Type) {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_eq (fraction_mul x (fraction_one t)) x)
  = fraction_mul_is_commutative x (fraction_one t #d);
    fraction_mul_left_identity x;
    fraction_eq_trans
      (fraction_mul x (fraction_one t #d))
      (fraction_mul (fraction_one t #d) x)
      x

private let fraction_mul_left_absorption
  (#t:Type) {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_eq (fraction_mul (fraction_zero t) x) (fraction_zero t))
  = let a, b : t & t = x.num, x.den in
    assert ((zero * a) * one = (one * b) * zero) by canon_ring()

private let fraction_mul_right_absorption
  (#t:Type) {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_eq (fraction_mul x (fraction_zero t)) (fraction_zero t))
  = fraction_mul_is_commutative x (fraction_zero t #d);
    fraction_mul_left_absorption x;
    fraction_eq_trans
      (fraction_mul x (fraction_zero t #d))
      (fraction_mul (fraction_zero t #d) x)
      (fraction_zero t #d)
#pop-options

#push-options "--z3rlimit 80 --fuel 1 --ifuel 1"
private let fraction_left_distributivity
  (#t:Type) {| dom: integral_domain t |} (x y z: fraction dom)
  : Lemma (fraction_eq (fraction_mul x (fraction_add y z))
                       (fraction_add (fraction_mul x y) (fraction_mul x z)))
  = let a, b, c, dd, e, f : t & t & t & t & t & t =
      x.num, x.den, y.num, y.den, z.num, z.den in
    prod_den_nonzero y z;
    prod_den_nonzero x (fraction_add y z);
    prod_den_nonzero x y;
    prod_den_nonzero x z;
    prod_den_nonzero (fraction_mul x y) (fraction_mul x z);
    assert ((a * (c * f + dd * e)) * ((b * dd) * (b * f))
          = (b * (dd * f)) * ((a * c) * (b * f) + (b * dd) * (a * e)))
      by canon_ring()
#pop-options

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let fraction_right_distributivity
  (#t:Type) {| dom: integral_domain t |} (x y z: fraction dom)
  : Lemma (fraction_eq (fraction_mul (fraction_add x y) z)
                       (fraction_add (fraction_mul x z) (fraction_mul y z)))
  = fraction_mul_is_commutative (fraction_add x y) z;
    fraction_left_distributivity z x y;
    fraction_mul_is_commutative z x;
    fraction_mul_is_commutative z y;
    fraction_add_congruence (fraction_mul z x) (fraction_mul z y)
                            (fraction_mul x z) (fraction_mul y z);
    fraction_eq_trans
      (fraction_mul (fraction_add x y) z)
      (fraction_mul z (fraction_add x y))
      (fraction_add (fraction_mul z x) (fraction_mul z y));
    fraction_eq_trans
      (fraction_mul (fraction_add x y) z)
      (fraction_add (fraction_mul z x) (fraction_mul z y))
      (fraction_add (fraction_mul x z) (fraction_mul y z))
#pop-options

(* ================================================================ *)
(*  §7. Domain law and zero ≠ one on fractions                      *)
(* ================================================================ *)

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let fraction_zero_ne_one_lemma
  (#t:Type) {| dom: integral_domain t |}
  : Lemma (not (fraction_eq (fraction_zero t) (fraction_one t)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    zero_mul_x (one #t);
    one_mul_x  (one #t);
    let aux () : Lemma
        (requires fraction_eq (fraction_zero t #dom) (fraction_one t #dom))
        (ensures False)
      = symmetry (zero * one) (zero <: t);
        transitivity (zero #t) (zero * one) (one * one);
        transitivity (zero #t) (one * one) (one <: t);
        let _: squash (not ((one <: t) = (zero <: t))) = dom.id_one_ne_zero in
        symmetry (zero #t) (one <: t)
    in
    Classical.move_requires aux ()
#pop-options

(* Forward: if x*y ~ 0 then x ~ 0 or y ~ 0. *)
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let fraction_domain_law_fwd
  (#t:Type) {| dom: integral_domain t |} (x y: fraction dom)
  : Lemma (requires fraction_eq (fraction_mul x y) (fraction_zero t))
          (ensures  fraction_eq x (fraction_zero t) \/
                    fraction_eq y (fraction_zero t))
  = elim_equatable_laws t ();
    let a, b, c, e : t & t & t & t = x.num, x.den, y.num, y.den in
    assert ((a * c) * one = a * c) by canon_ring();
    assert ((b * e) * zero = zero) by canon_ring();
    symmetry ((a * c) * one) (a * c);
    transitivity (a * c) ((a * c) * one) ((b * e) * zero);
    transitivity (a * c) ((b * e) * zero) zero;
    domain_zero_div a c;
    let if_a () : Lemma (requires a = zero)
                        (ensures fraction_eq x (fraction_zero t #dom))
      = assert (a * one = a) by canon_ring();
        transitivity (a * one) a zero;
        assert (b * zero = zero) by canon_ring();
        symmetry (b * zero) zero;
        transitivity (a * one) zero (b * zero)
    in
    let if_c () : Lemma (requires c = zero)
                        (ensures fraction_eq y (fraction_zero t #dom))
      = assert (c * one = c) by canon_ring();
        transitivity (c * one) c zero;
        assert (e * zero = zero) by canon_ring();
        symmetry (e * zero) zero;
        transitivity (c * one) zero (e * zero)
    in
    Classical.move_requires if_a ();
    Classical.move_requires if_c ()
#pop-options

(* Backward (one side): if x ~ 0 then x*y ~ 0. *)
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let fraction_domain_law_bwd_left
  (#t:Type) {| dom: integral_domain t |} (x y: fraction dom)
  : Lemma (requires fraction_eq x (fraction_zero t))
          (ensures  fraction_eq (fraction_mul x y) (fraction_zero t))
  = elim_equatable_laws t ();
    let a, b, c, e : t & t & t & t = x.num, x.den, y.num, y.den in
    assert (a * one = a) by canon_ring();
    assert (b * zero = zero) by canon_ring();
    transitivity a (a * one) (b * zero);
    transitivity a (b * zero) zero;
    assert (a = zero);
    assert ((a * c) * one = a * c) by canon_ring();
    assert ((b * e) * zero = zero) by canon_ring();
    assert ((zero * c) = zero) by canon_ring();
    mul_congruence a c zero c;
    transitivity (a * c) (zero * c) zero;
    transitivity ((a * c) * one) (a * c) zero;
    symmetry ((b * e) * zero) zero;
    transitivity ((a * c) * one) zero ((b * e) * zero)
#pop-options

let fraction_eq_zero_iff_num_zero
  (#t:Type) {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_eq x (fraction_zero t) <==> (x.num = zero))
  = elim_equatable_laws t ();
    let a, b : t & t = x.num, x.den in
    assert (a * one = a) by canon_ring();
    assert (b * zero = zero) by canon_ring();
    let fwd () : Lemma (requires fraction_eq x (fraction_zero t #d))
                       (ensures  a = zero)
      = transitivity a (a * one) (b * zero);
        transitivity a (b * zero) zero
    in
    let bwd () : Lemma (requires a = zero)
                       (ensures  fraction_eq x (fraction_zero t #d))
      = symmetry (a * one) a;
        transitivity (a * one) a zero;
        symmetry (b * zero) zero;
        transitivity (a * one) zero (b * zero)
    in
    Classical.move_requires fwd ();
    Classical.move_requires bwd ()

(* ================================================================ *)
(*  §8. Inversion                                                   *)
(* ================================================================ *)

(* For a nonzero fraction a/b (so a ≠ 0 via fraction_eq_zero_iff_num_zero),
   the inverse is b/a. Stated directly via `fraction_eq` to avoid
   forward-referencing the not-yet-declared `fraction_field` TC instance
   (which `is_nonzero` would need). *)
let fraction_inv (#t:Type) {| d: integral_domain t |} (x: fraction d)
  : Pure (fraction d)
         (requires not (fraction_eq x (fraction_zero t)))
         (ensures fun y -> not (fraction_eq y (fraction_zero t)))
  = fraction_eq_zero_iff_num_zero x;
    let num : t = x.den in
    let den : t = x.num in
    let r : fraction d = Fraction num den in
    fraction_eq_zero_iff_num_zero r;
    r

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
private let fraction_inv_left
  (#t:Type) {| d: integral_domain t |} (x: fraction d)
  : Lemma (requires not (fraction_eq x (fraction_zero t)))
          (ensures  fraction_eq (fraction_mul (fraction_inv x) x) (fraction_one t))
  = let a, b : t & t = x.num, x.den in
    assert ((b * a) * one = (a * b) * one) by canon_ring()

private let fraction_inv_right
  (#t:Type) {| d: integral_domain t |} (x: fraction d)
  : Lemma (requires not (fraction_eq x (fraction_zero t)))
          (ensures  fraction_eq (fraction_mul x (fraction_inv x)) (fraction_one t))
  = fraction_mul_is_commutative x (fraction_inv x);
    fraction_inv_left x;
    fraction_eq_trans
      (fraction_mul x (fraction_inv x))
      (fraction_mul (fraction_inv x) x)
      (fraction_one t #d)

private let fraction_inv_congruence
  (#t:Type) {| d: integral_domain t |} (x y: fraction d)
  : Lemma (requires not (fraction_eq x (fraction_zero t)) /\
                    not (fraction_eq y (fraction_zero t)) /\
                    fraction_eq x y)
          (ensures  fraction_eq (fraction_inv x) (fraction_inv y))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let a, b : t & t = x.num, x.den in
    let c, e : t & t = y.num, y.den in
    symmetry (a * e) (b * c)
#pop-options

(* ================================================================ *)
(*  §9. Bundle assembly: the single `fraction_field` instance       *)
(* ================================================================ *)

(* The structure of the foundation's `field` requires us to build:
   field { f_sf: skewfield t; f_mic: mul_is_commutative; f_one_ne_zero }.
   skewfield needs { sf_d: domain t; sf_mig: mul_is_group }.
   domain needs   { d_r: ring t; domain_law }.
   ring needs     { r_add: add_comm_group t; one, mul, ...laws }.
   add_comm_group needs { acg_eq: equatable t; zero, add, neg, ...laws }.

   We construct each layer locally, then assemble the field on top. *)

private let fr_acg (t:Type) (d: integral_domain t)
  : add_comm_group (fraction d) = {
    acg_eq            = fraction_equatable t d;
    zero              = fraction_zero t #d;
    add               = (fun x y -> fraction_add x y);
    add_congruence    = (fun a b x y -> fraction_add_congruence a b x y);
    add_commutativity = (fun a b -> fraction_add_is_commutative a b);
    add_associativity = (fun a b c -> fraction_add_is_associative a b c);
    add_zero          = (fun x ->
                          fraction_add_left_identity x;
                          fraction_add_right_identity x);
    neg               = (fun x -> fraction_neg x);
    neg_congruence    = (fun a b -> fraction_neg_congruence a b);
    add_negation      = (fun x ->
                          fraction_negation_l x;
                          fraction_negation_r x);
  }

private let fr_ring (t:Type) (d: integral_domain t)
  : ring (fraction d) = {
    r_add                = fr_acg t d;
    one                  = fraction_one t #d;
    mul                  = (fun x y -> fraction_mul x y);
    mul_congruence       = (fun a b x y -> fraction_mul_congruence a b x y);
    mul_associativity    = (fun a b c -> fraction_mul_is_associative a b c);
    mul_one              = (fun x ->
                              fraction_mul_left_identity x;
                              fraction_mul_right_identity x);
    left_distributivity  = (fun x y z -> fraction_left_distributivity  x y z);
    right_distributivity = (fun x y z -> fraction_right_distributivity y z x);
  }

private let fr_domain (t:Type) (d: integral_domain t)
  : domain (fraction d) = {
    d_r        = fr_ring t d;
    domain_law = (fun x y ->
                    Classical.move_requires_2 (fraction_domain_law_fwd #t #d) x y;
                    Classical.move_requires_2 (fraction_domain_law_bwd_left #t #d) x y;
                    (* symmetric backward via commutativity *)
                    let bwd_right () : Lemma
                        (requires fraction_eq y (fraction_zero t #d))
                        (ensures  fraction_eq (fraction_mul x y) (fraction_zero t #d))
                      = fraction_mul_is_commutative x y;
                        fraction_domain_law_bwd_left y x;
                        fraction_eq_trans
                          (fraction_mul x y)
                          (fraction_mul y x)
                          (fraction_zero t #d)
                    in
                    Classical.move_requires bwd_right ());
  }

private let fr_mig (t:Type) (d: integral_domain t)
  : mul_is_group (fraction d) (fr_ring t d) = {
    inv             = (fun x -> fraction_inv x);
    inv_congr       = (fun a b -> fraction_inv_congruence a b);
    inversion_lemma = (fun x ->
                         fraction_inv_left x;
                         fraction_inv_right x);
  }

private let fr_mic (t:Type) (d: integral_domain t)
  : mul_is_commutative (fraction d) #(fr_ring t d) = {
    mul_commutativity = (fun a b -> fraction_mul_is_commutative a b);
  }

private let fr_skewfield (t:Type) (d: integral_domain t)
  : skewfield (fraction d) = {
    sf_r   = fr_ring t d;
    sf_mig = fr_mig t d;
  }

private let fraction_one_ne_zero_lemma
  (#t:Type) {| dom: integral_domain t |}
  : Lemma (not (fraction_eq (fraction_one t) (fraction_zero t)))
  = let aux () : Lemma
        (requires fraction_eq (fraction_one t #dom) (fraction_zero t #dom))
        (ensures False)
      = fraction_eq_symm (fraction_one t #dom) (fraction_zero t #dom);
        fraction_zero_ne_one_lemma #t #dom
    in
    Classical.move_requires aux ()

private let fr_one_ne_zero (t:Type) (d: integral_domain t)
  : Lemma (let _: ring (fraction d) = fr_ring t d in
           not ((one <: fraction d) = (zero <: fraction d)))
  = fraction_one_ne_zero_lemma #t #d

instance fraction_field (t:Type) (d: integral_domain t)
  : field (fraction d) = {
    f_sf           = fr_skewfield t d;
    f_mic          = fr_mic t d;
    f_one_ne_zero  = fr_one_ne_zero t d;
  }

(* ================================================================ *)
(*  §10. Published convenience: ( / )                               *)
(* ================================================================ *)

let ( / ) (#t:Type) {| d: integral_domain t |} (x y: t)
  : Pure (fraction d)
         (requires is_nonzero y)
         (ensures fun _ -> True)
  = Fraction x y
