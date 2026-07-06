module Core.AlgebraicConstant

(*
   Implementation of the quotient ring  polynomial t / (r).

   See the .fsti for the public surface.

   Strategy: `ac_eq a b := r | (a - b)` in `polynomial t`.  All ring
   operations are inherited verbatim from `polynomial t`; their
   congruence under `ac_eq` follows because (r) is an ideal.

   The polynomial `commutative_ring (polynomial t)` is reached via
   the registered `polynomial_cr` instance.
*)

module TC = FStar.Tactics.Typeclasses

module ID = FStar.IndefiniteDescription
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Algebra.CongruenceMod
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.GCD
open Core.Polynomial.PartialFraction
open Core.Polynomial.Irreducible

(* ---------------------------------------------------------------- *)
(*  Internal: a local CR helper for canon_ring identities over a    *)
(*  single-CR context (avoids the field/poly CR diamond).            *)
(* ---------------------------------------------------------------- *)

private let cr_neg_sub_swap
    (#u:Type) {| cr: commutative_ring u |} (x y: u)
  : Lemma (eq (- (x + (- y))) (y + (- x)))
  = assert (eq (- (x + (- y))) (y + (- x)))
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_sub_telescope
    (#u:Type) {| cr: commutative_ring u |} (a b c: u)
  : Lemma (eq ((a + (- b)) + (b + (- c)))
              (a + (- c)))
  = assert (eq ((a + (- b)) + (b + (- c)))
               (a + (- c)))
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_sub_distributes_add
    (#u:Type) {| cr: commutative_ring u |}
    (a1 b1 a2 b2: u)
  : Lemma (eq ((a1 + b1) + (- (a2 + b2)))
              ((a1 + (- a2)) + (b1 + (- b2))))
  = assert (eq ((a1 + b1) + (- (a2 + b2)))
               ((a1 + (- a2)) + (b1 + (- b2))))
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_neg_sub
    (#u:Type) {| cr: commutative_ring u |} (a1 a2: u)
  : Lemma (eq ((- a1) + (- (- a2)))
              (- (a1 + (- a2))))
  = assert (eq ((- a1) + (- (- a2)))
               (- (a1 + (- a2))))
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_mul_sub_split
    (#u:Type) {| cr: commutative_ring u |}
    (a1 b1 a2 b2: u)
  : Lemma (eq ((a1 * b1) + (- (a2 * b2)))
              (add (a1 * (b1 + (- b2)))
                   ((a1 + (- a2)) * b2)))
  = assert (eq ((a1 * b1) + (- (a2 * b2)))
               (add (a1 * (b1 + (- b2)))
                    ((a1 + (- a2)) * b2)))
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_sub_self
    (#u:Type) {| cr: commutative_ring u |} (a: u)
  : Lemma (eq (a + (- a)) (zero <: u))
  = assert (eq (a + (- a)) (zero <: u))
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_sub_zero_right
    (#u:Type) {| cr: commutative_ring u |} (a: u)
  : Lemma (eq (a + (- (zero <: u))) a)
  = assert (eq (a + (- (zero <: u))) a)
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_sub_zero_left
    (#u:Type) {| cr: commutative_ring u |} (a: u)
  : Lemma (eq ((zero <: u) + (- a)) (- a))
  = assert (eq ((zero <: u) + (- a)) (- a))
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_add_sub_cancel
    (#u:Type) {| cr: commutative_ring u |} (a m: u)
  : Lemma (eq (a + (m + (- a))) m)
  = assert (eq (a + (m + (- a))) m)
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_sub_sub_self
    (#u:Type) {| cr: commutative_ring u |} (m a: u)
  : Lemma (eq (m + (- (m + (- a)))) a)
  = assert (eq (m + (- (m + (- a)))) a)
      by Core.Tactics.CanonRing.canon_ring ()

(* From  p ~ s + rm  derive  (p -- rm) ~ s.  Used by class_of_mod (s = r*quot). *)
private let cr_sub_residue
    (#u:Type) {| cr: commutative_ring u |} (p s rm: u)
  : Lemma (requires eq p (s + rm))
          (ensures  eq (p + (- rm)) s)
  = H.elim_equatable_laws u ();

    add_congruence p (- rm) (s + rm) (- rm);   (* p + -rm ~ (s+rm) + -rm *)
    assert (eq ((s + rm) + (- rm)) s)
      by Core.Tactics.CanonRing.canon_ring ();
    transitivity (p + (- rm)) ((s + rm) + (- rm)) s

(* ---------------------------------------------------------------- *)
(*  Bridge: poly_eq x y  ⟹  poly_sub x y ~ poly_zero                *)
(* ---------------------------------------------------------------- *)

private let poly_eq_implies_sub_zero
    (#t:Type) {| cr: commutative_ring t |}
    (a b: polynomial t)
  : Lemma (requires a = b)
          (ensures  (a -- b) = poly_zero #t)
  =
    (* poly_sub a b = poly_add a (poly_neg b) *)
    reflexivity (- b);
    poly_add_congruence a (- b) b (- b);
    (* Now poly_add a (poly_neg b) ~ poly_add b (poly_neg b) *)
    cr_sub_self  b;
    (* poly_add b (poly_neg b) ~ poly_zero *)
    transitivity (a + (- b))
                 (b + (- b))
                 (poly_zero #t);
    (* And poly_sub a b == poly_add a (poly_neg b) (definitional via reveal) *)
    ()

(* ---------------------------------------------------------------- *)
(*  Operations + equality                                            *)
(* ---------------------------------------------------------------- *)

(* Decidable algebraic-constant equality: take the remainder of (a-b)
   on division by r and check it's zero.  Tot-pure. *)
let ac_eq #t #f (#r: polynomial t {proper_extension r})
          (a b: algebraic r) : bool
  = let rem = poly_rem (a -- b) r in
    rem = poly_zero #t

(* Bridge: ac_eq a b ⟺ r | (a.rep - b.rep)  in polynomial t.
   Equipped with an SMT pattern so users of `ac_eq` automatically get
   the divides interpretation when needed.  This bridge is the only
   way we use SMT patterns in this file — the lemma is a pure
   definitional equivalence. *)
private let ac_eq_iff_divides
    #t {| f: field t |} (#r: polynomial t {proper_extension r})
    (a b: algebraic r)
  : Lemma (
           b2t (ac_eq a b) <==>
             divides  r (a -- b))
    [SMTPat (ac_eq a b)]
  =
    let d = a -- b in
    let (q, rem) = poly_divmod d r in
    (* Forward: ac_eq ⟹ divides. rem ~ 0 + p_correct: d ~ r*q + rem ~ r*q + 0 ~ r*q. *)
    let fwd () : Lemma (requires b2t (ac_eq a b))
                       (ensures divides  r d)
      = (* rem ~ poly_zero, so d ~ r*q + 0 ~ r*q *)

        add_zero (r * q);
        (* poly_add (poly_mul r q) poly_zero ~ poly_mul r q *)
        poly_add_congruence (r * q) rem (r * q) (poly_zero #t);
        reflexivity (r * q);
        transitivity d ((r * q) + rem) ((r * q) + (poly_zero #t));
        transitivity d ((r * q) + (poly_zero #t)) (r * q);
        divides_intro  r d q
    in
    (* Backward: divides ⟹ rem ~ 0 via poly_divmod_unique. *)
    let bwd () : Lemma (requires divides  r d)
                       (ensures b2t (ac_eq a b))
      = 
        eliminate exists (k: polynomial t). d = r * k
        returns b2t (ac_eq a b)
        with hyp.
        begin
          (* Have: d ~ r*k.   Also d ~ r*q + rem.
             Convert to canonical shape: r*k + 0 ~ r*q + rem.
             Then poly_divmod_unique gives rem ~ 0.                    *)
          add_zero (r * k);
          (* poly_add (poly_mul r k) poly_zero ~ poly_mul r k *)
          symmetry
            ((r * k) + (poly_zero #t)) (r * k);
          transitivity d (r * k) ((r * k) + (poly_zero #t));
          (* d ~ poly_add (poly_mul r k) poly_zero
             d ~ poly_add (poly_mul r q) rem
             ⟹  poly_add (poly_mul r k) poly_zero ~ poly_add (poly_mul r q) rem *)
          symmetry d ((r * k) + (poly_zero #t));
          transitivity ((r * k) + (poly_zero #t))
                       d
                       ((r * q) + rem);
          deg_zero #t;
          poly_divmod_unique r k q (poly_zero #t) rem
        end
    in
    Classical.move_requires fwd ();
    Classical.move_requires bwd ()

(* deg poly_one == 0 over a field (one <> zero ⇒ poly_one = [one]); 0 < deg r
   since proper_extension gives deg r >= 2. *)
private let ac_poly_one_deg (#t:Type) {| f: field t |} ()
  : Lemma (deg (poly_one #t) == 0)
  = H.elim_equatable_laws t ();
    let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    poly_lc_reveal (poly_one #t)

(* ---------------------------------------------------------------- *)
(*  Smart constructor + keystone bridge                              *)
(* ---------------------------------------------------------------- *)

(* (class_of r p) : the canonical reduced representative of [p], i.e. the remainder of
   dividing p by r.  deg < deg r holds by poly_divmod_correct_degree (deg r>=2>0). *)
let class_of #t #f (r: polynomial t {proper_extension r}) (p: polynomial t) : algebraic r =
  let rm = poly_rem p r in
  rm

(* KEYSTONE: reducing p changes it only by a multiple of r, so r | ((class_of r p) -- p). *)
let class_of_mod #t #f (#r: polynomial t {proper_extension r}) (p: polynomial t)
  : Lemma (r `divides` ((class_of r p) -- p))
  = let (quot, rm) = poly_divmod p r in
    (* p -- rm ~ r*quot  ⇒  r | (p -- rm) *)
    cr_sub_residue p (r * quot) rm;
    (* (p -- rm) ~ r*quot, definitionally r*quot = mul r quot *)
    divides_intro r (p -- rm) quot;
    (* flip: r | (p -- rm) ⇒ r | (rm -- p) *)
    divides_neg r (p -- rm);
    cr_neg_sub_swap p rm;   (* neg (p -- rm) ~ rm -- p *)
    divides_congruence_right r
      (- (p -- rm)) (rm -- p)

(* ---------------------------------------------------------------- *)
(*  class_of-keystone bridges, restated at the generic `cong` level. *)
(*  The generic congruence-modulo toolkit (cong_trans / cong_mul /   *)
(*  cong_add / cong_of_eq) lives in Core.Algebra.CongruenceMod;       *)
(*  these two are the AlgebraicConstant-specific bridges built on the *)
(*  keystone class_of_mod (class_of p ~ p (mod r)).                         *)
(* ---------------------------------------------------------------- *)

(* (class_of r p) ~ p (mod r) — keystone restated at the cong level. *)
let class_of_cong (#t:Type) {| f: field t |} (r: polynomial t {proper_extension r})
  (p: polynomial t)
  : Lemma (cong r ((class_of r p)) p)
  = class_of_mod #_ #_ #r p

(* p ~ (class_of r p) (mod r) — symmetric form. *)
let class_of_cong_sym (#t:Type) {| f: field t |} (r: polynomial t {proper_extension r})
  (p: polynomial t)
  : Lemma (cong r p ((class_of r p)))
  = class_of_cong r p;
    cong_sym r ((class_of r p)) p

(* Conclude ac_eq from cong r for REDUCED reps (the result types of class_of/ac ops). *)
let ac_eq_of_cong (#t:Type) {| f: field t |} (r: polynomial t {proper_extension r})
  (lhs rhs: algebraic r)
  : Lemma (requires cong r lhs rhs)
          (ensures  ac_eq lhs rhs)
  = ac_eq_iff_divides lhs rhs

let ac_zero #t #f (#r: polynomial t {proper_extension r}) : algebraic r =
  (poly_zero #t <: algebraic r)             (* deg poly_zero = -1 < deg r *)
let ac_one  #t #f (#r: polynomial t {proper_extension r}) : algebraic r =
  ac_poly_one_deg #t ();                     (* deg poly_one = 0 < deg r (deg r >= 2) *)
  (poly_one #t <: algebraic r)

let ac_add #t #f (#r: polynomial t {proper_extension r}) (a b: algebraic r) : algebraic r =
  poly_add_degree_bound #t a b (deg r);      (* deg (a+b) < deg r *)
  (poly_add a b <: algebraic r)

let ac_neg #t #f (#r: polynomial t {proper_extension r}) (a: algebraic r) : algebraic r =
  poly_neg_degree #t a;                       (* deg (neg a) = deg a < deg r *)
  (poly_neg a <: algebraic r)

let ac_mul #t #f (#r: polynomial t {proper_extension r}) (a b: algebraic r) : algebraic r =
  (class_of r (a * b))

(* Clean characterization of nullity: [a] = 0 in the quotient iff r divides a.rep.
   This is the bridge the field construction (inverse via Bezout) consumes; it is
   proved here, where the divides<->ac_eq SMT pattern and the poly_eq/eq idiom are
   available, so external callers never need to fight `poly_sub a 0 ~ a`. *)
let ac_eq_zero_iff_divides #t #f (#r: polynomial t {proper_extension r}) (a: algebraic r)
  : Lemma (
           b2t (ac_eq a ac_zero) <==>
             r `divides` a)
  =
    let x = (a <: polynomial t) in
    let s = x -- (poly_zero #t) in
    (* SMTPat: ac_eq a 0 <==> divides r (x -- 0) = divides r s. *)
    ac_eq_iff_divides a ac_zero;
    (* s = x -- 0 ~ x. *)
    poly_neg_zero #t #_; (* poly_neg 0 == 0 *)
    add_zero x;                                                 (* poly_add x 0 ~ x *)
    reflexivity x;
    poly_add_congruence x (- (poly_zero #t)) x (poly_zero #t);
    transitivity s (x + (poly_zero #t)) x;               (* eq s x *)
    symmetry s x;     (* eq x s *)
    (* divides r s <==> divides r x. *)
    let fwd () : Lemma (requires divides  r s)
                       (ensures  divides  r x)
      = divides_congruence_right  r s x in
    let bwd () : Lemma (requires divides  r x)
                       (ensures  divides  r s)
      = divides_congruence_right  r x s in
    Classical.move_requires fwd ();
    Classical.move_requires bwd ()

(* General characterization (explicit, no SMT pattern): [a] = [b] iff r | (a.rep - b.rep).
   Re-exposes the internal definitional equivalence for external callers (e.g. the
   field inversion identity, which needs ac_eq _ ac_one). *)
let ac_eq_divides #t #f (#r: polynomial t {proper_extension r}) (a b: algebraic r)
  : Lemma (
           b2t (ac_eq a b) <==>
             r `divides` (a -- b))
  = ac_eq_iff_divides a b

(* Representation reveals (ops are abstract through the interface). *)
let ac_mul_rep #t #f (#r: polynomial t {proper_extension r}) (a b: algebraic r)
  : Lemma ((ac_mul a b) == (class_of r (a * b))) = ()

let ac_add_rep #t #f (#r: polynomial t {proper_extension r}) (a b: algebraic r)
  : Lemma ((ac_add a b <: polynomial t) == a + b) = poly_add_degree_bound #t a b (deg r)

let ac_one_rep #t #f (r: polynomial t {proper_extension r})
  : Lemma (((ac_one <: algebraic r) <: polynomial t) == poly_one) = ac_poly_one_deg #t ()

(* ---------------------------------------------------------------- *)
(*  Equivalence laws                                                 *)
(* ---------------------------------------------------------------- *)

let ac_eq_reflexivity #t #f (#r: polynomial t {proper_extension r}) (a: algebraic r)
  : Lemma (ac_eq a a)
  =
    let x = (a <: polynomial t) in
    (* x -- x ~ poly_zero, r | poly_zero, then divides_congruence_right. *)
    cr_sub_self  x;
    (* x -- x = poly_add x (poly_neg x); both directions of eq. *)
    divides_zero  r;
    symmetry
             (x + (- x)) (poly_zero #t);
    divides_congruence_right  r
                             (poly_zero #t) (x + (- x))

let ac_eq_symmetry #t #f (#r: polynomial t {proper_extension r}) (a b: algebraic r)
  : Lemma (ac_eq a b <==> ac_eq b a)
  =
    let x = (a <: polynomial t) in
    let y = (b <: polynomial t) in
    (* ac_eq a b <==> r | (x--y) and ac_eq b a <==> r | (y--x) (ac_eq_iff_divides
       SMTPat); the two divisibilities are equivalent since y--x ~ -(x--y). *)
    let fwd () : Lemma (requires divides r (x -- y)) (ensures divides r (y -- x))
      = divides_neg r (x -- y);
        cr_neg_sub_swap x y;
        divides_congruence_right r (- (x -- y)) (y -- x) in
    let bwd () : Lemma (requires divides r (y -- x)) (ensures divides r (x -- y))
      = divides_neg r (y -- x);
        cr_neg_sub_swap y x;
        divides_congruence_right r (- (y -- x)) (x -- y) in
    Classical.move_requires fwd ();
    Classical.move_requires bwd ()

let ac_eq_transitivity #t #f (#r: polynomial t {proper_extension r}) (a b c: algebraic r)
  : Lemma (requires ac_eq a b /\ ac_eq b c)
          (ensures  ac_eq a c)
  =
    let x = (a <: polynomial t) in
    let y = (b <: polynomial t) in
    let z = (c <: polynomial t) in
    divides_add  r (x -- y) (y -- z);
    cr_sub_telescope  x y z;
    divides_congruence_right  r
      ((x -- y) + (y -- z))
      (x -- z)

(* ---------------------------------------------------------------- *)
(*  Bridge: poly_eq → ac_eq                                          *)
(* ---------------------------------------------------------------- *)

private let poly_eq_implies_ac_eq
    #t {| f: field t |} (#r: polynomial t {proper_extension r}) (a b: algebraic r)
  : Lemma (requires poly_eq a b)
          (ensures  ac_eq a b)
  =
    let x = (a <: polynomial t) in
    let y = (b <: polynomial t) in
    poly_eq_implies_sub_zero x y;
    divides_zero  r;
    symmetry
             (x -- y) (poly_zero #t);
    divides_congruence_right  r
      (poly_zero #t) (x -- y)

(* ---------------------------------------------------------------- *)
(*  Add congruence + laws                                            *)
(* ---------------------------------------------------------------- *)

let ac_add_congruence #t #f (#r: polynomial t {proper_extension r}) (a1 b1 a2 b2: algebraic r)
  : Lemma (requires ac_eq a1 a2 /\ ac_eq b1 b2)
          (ensures  ac_eq (ac_add a1 b1) (ac_add a2 b2))
  =
    let x1 = (a1 <: polynomial t) in
    let y1 = (b1 <: polynomial t) in
    let x2 = (a2 <: polynomial t) in
    let y2 = (b2 <: polynomial t) in
    divides_add  r (x1 -- x2) (y1 -- y2);
    cr_sub_distributes_add  x1 y1 x2 y2;
    symmetry
      ((x1 + y1) -- (x2 + y2))
      ((x1 -- x2) + (y1 -- y2));
    divides_congruence_right  r
      ((x1 -- x2) + (y1 -- y2))
      ((x1 + y1) -- (x2 + y2))

let ac_add_associativity #t #f (#r: polynomial t {proper_extension r}) (a b c: algebraic r)
  : Lemma (ac_eq (ac_add (ac_add a b) c) (ac_add a (ac_add b c)))
  = poly_add_associativity a b c;
    poly_eq_implies_ac_eq (ac_add (ac_add a b) c) (ac_add a (ac_add b c))

let ac_add_commutativity #t #f (#r: polynomial t {proper_extension r}) (a b: algebraic r)
  : Lemma (ac_eq (ac_add a b) (ac_add b a))
  = poly_add_commutativity a b;
    poly_eq_implies_ac_eq (ac_add a b) (ac_add b a)

let ac_add_zero #t #f (#r: polynomial t {proper_extension r}) (a: algebraic r)
  : Lemma (ac_eq (ac_add a ac_zero) a /\ ac_eq (ac_add ac_zero a) a)
  = poly_add_zero a;
    poly_eq_implies_ac_eq (ac_add a ac_zero) a;
    poly_eq_implies_ac_eq (ac_add ac_zero a) a

(* ---------------------------------------------------------------- *)
(*  Neg congruence + add_negation                                    *)
(* ---------------------------------------------------------------- *)

let ac_neg_congruence #t #f (#r: polynomial t {proper_extension r}) (a1 a2: algebraic r)
  : Lemma (requires ac_eq a1 a2)
          (ensures  ac_eq (ac_neg a1) (ac_neg a2))
  =
    let x1 = (a1 <: polynomial t) in
    let x2 = (a2 <: polynomial t) in
    divides_neg  r (x1 -- x2);
    (* neg (x1 - x2) ~ -x1 + -(-x2) = -x1 - (-x2) *)
    cr_neg_sub  x1 x2;
    symmetry
      ((- x1) + (- (- x2)))
      (- (x1 -- x2));
    divides_congruence_right  r
      (- (x1 -- x2))
      ((- x1) + (- (- x2)))

let ac_add_negation #t #f (#r: polynomial t {proper_extension r}) (a: algebraic r)
  : Lemma (ac_eq (ac_add a (ac_neg a)) ac_zero /\
           ac_eq (ac_add (ac_neg a) a) ac_zero)
  = poly_add_negation a;
    poly_eq_implies_ac_eq (ac_add a (ac_neg a)) ac_zero;
    poly_eq_implies_ac_eq (ac_add (ac_neg a) a) ac_zero

(* ---------------------------------------------------------------- *)
(*  Mul congruence + laws                                            *)
(* ---------------------------------------------------------------- *)

let ac_mul_congruence #t #f (#r: polynomial t {proper_extension r}) (a1 b1 a2 b2: algebraic r)
  : Lemma (requires ac_eq a1 a2 /\ ac_eq b1 b2)
          (ensures  ac_eq (ac_mul a1 b1) (ac_mul a2 b2))
  = (* ac_mul ai bi = (class_of (ai*bi) <: algebraic r).  Chain:
       class_of(a1*b1) ~ a1*b1 ~ a2*b2 ~ class_of(a2*b2)  (mod r). *)
    ac_eq_iff_divides a1 a2;                          (* r | (a1--a2) = cong r a1 a2 *)
    ac_eq_iff_divides b1 b2;                          (* r | (b1--b2) = cong r b1 b2 *)
    class_of_cong r (a1 * b1);          (* class_of(a1*b1) ~ a1*b1 *)
    cong_mul r a1 a2 b1 b2;                    (* a1*b1 ~ a2*b2 *)
    cong_trans r ((class_of r (a1 * b1))) (a1 * b1) (a2 * b2);
    class_of_cong_sym r (a2 * b2);      (* a2*b2 ~ class_of(a2*b2) *)
    cong_trans r ((class_of r (a1 * b1))) (a2 * b2) ((class_of r (a2 * b2)));
    ac_eq_of_cong r (ac_mul a1 b1) (ac_mul a2 b2)

let ac_mul_associativity #t #f (#r: polynomial t {proper_extension r}) (a b c: algebraic r)
  : Lemma (ac_eq (ac_mul (ac_mul a b) c) (ac_mul a (ac_mul b c)))
  = (* lhs = class_of(class_of(a*b) * c),  rhs = class_of(a * class_of(b*c)).  Chain (mod r):
       class_of(class_of(a*b)*c) ~ class_of(a*b)*c ~ (a*b)*c = a*(b*c) ~ a*class_of(b*c) ~ class_of(a*class_of(b*c)). *)
    let ab  = a * b in
    let bc  = b * c in
    let mab = (class_of r ab) in
    let mbc = (class_of r bc) in
    (* step 1: class_of(mab*c) ~ mab*c *)
    class_of_cong r (mab * c);
    (* step 2: mab*c ~ (a*b)*c  (since mab ~ a*b) *)
    class_of_cong r ab;                        (* mab ~ ab *)
    cong_refl r c;
    cong_mul r mab ab c c;                     (* mab*c ~ ab*c *)
    cong_trans r ((class_of r (mab * c))) (mab * c) (ab * c);
    (* step 3: (a*b)*c = a*(b*c)  (exact) *)
    poly_mul_associativity a b c;                     (* poly_eq ((a*b)*c) (a*(b*c)) *)
    cong_of_eq r (ab * c) (a * bc);
    cong_trans r ((class_of r (mab * c))) (ab * c) (a * bc);
    (* step 4: a*(b*c) ~ a*class_of(b*c) *)
    class_of_cong_sym r bc;                     (* bc ~ mbc *)
    cong_refl r a;
    cong_mul r a a bc mbc;                      (* a*bc ~ a*mbc *)
    cong_trans r ((class_of r (mab * c))) (a * bc) (a * mbc);
    (* step 5: a*class_of(b*c) ~ class_of(a*class_of(b*c)) *)
    class_of_cong_sym r (a * mbc);
    cong_trans r ((class_of r (mab * c))) (a * mbc) ((class_of r (a * mbc)));
    ac_eq_of_cong r (ac_mul (ac_mul a b) c) (ac_mul a (ac_mul b c))

let ac_mul_one #t #f (#r: polynomial t {proper_extension r}) (a: algebraic r)
  : Lemma (ac_eq (ac_mul a ac_one) a /\ ac_eq (ac_mul ac_one a) a)
  = (* ac_mul a ac_one = class_of(a * poly_one) ~ a*poly_one = a (mod r).  a reduced. *)
    ac_one_rep r;                                      (* ac_one == poly_one *)
    (* class_of(a*one) ~ a*one *)
    class_of_cong r (a * (poly_one #t));
    poly_mul_one a;                                    (* poly_eq (a*one) a /\ poly_eq (one*a) a *)
    cong_of_eq r (a * (poly_one #t)) a;
    cong_trans r ((class_of r (a * (poly_one #t)))) (a * (poly_one #t)) a;
    ac_eq_of_cong r (ac_mul a ac_one) a;
    class_of_cong r ((poly_one #t) * a);
    cong_of_eq r ((poly_one #t) * a) a;
    cong_trans r ((class_of r ((poly_one #t) * a))) ((poly_one #t) * a) a;
    ac_eq_of_cong r (ac_mul ac_one a) a

let ac_mul_commutativity #t #f (#r: polynomial t {proper_extension r}) (a b: algebraic r)
  : Lemma (ac_eq (ac_mul a b) (ac_mul b a))
  = (* class_of(a*b) ~ a*b = b*a ~ class_of(b*a). *)
    let ab : polynomial t = a * b in
    let ba : polynomial t = b * a in
    class_of_cong r ab;
    poly_mul_commutativity a b;                        (* poly_eq (a*b) (b*a) *)
    cong_of_eq r ab ba;
    cong_trans r ((class_of r ab)) ab ba;
    class_of_cong_sym r ba;
    cong_trans r ((class_of r ab)) ba ((class_of r ba));
    ac_eq_of_cong r (ac_mul a b) (ac_mul b a)

let ac_left_distributivity #t #f (#r: polynomial t {proper_extension r}) (a b c: algebraic r)
  : Lemma (ac_eq (ac_mul a (ac_add b c))
                 (ac_add (ac_mul a b) (ac_mul a c)))
  = (* lhs = class_of(a*(b+c)),  rhs = class_of(a*b) + class_of(a*c)  (ac_add does NOT reduce).
       Chain: class_of(a*(b+c)) ~ a*(b+c) = a*b + a*c ~ class_of(a*b) + class_of(a*c). *)
    ac_add_rep b c;                                    (* ac_add b c == b + c *)
    ac_add_rep (ac_mul a b) (ac_mul a c);              (* rhs == class_of(a*b) + class_of(a*c) *)
    let bc  : polynomial t = b + c in
    let ab  : polynomial t = a * b in
    let ac' : polynomial t = a * c in
    let abc : polynomial t = a * bc in
    let mab : polynomial t = (class_of r ab) in
    let mac : polynomial t = (class_of r ac') in
    (* class_of(a*(b+c)) ~ a*(b+c) *)
    class_of_cong r abc;
    (* a*(b+c) = a*b + a*c *)
    poly_left_distributivity a b c;
    cong_of_eq r abc (ab + ac');
    cong_trans r ((class_of r abc)) abc (ab + ac');
    (* a*b + a*c ~ class_of(a*b) + class_of(a*c)  via add congruence of cong r *)
    class_of_cong_sym r ab;              (* a*b ~ mab *)
    class_of_cong_sym r ac';             (* a*c ~ mac *)
    cong_add r ab mab ac' mac;
    cong_trans r ((class_of r abc)) (ab + ac') (mab + mac);
    ac_eq_of_cong r (ac_mul a (ac_add b c)) (ac_add (ac_mul a b) (ac_mul a c))

let ac_right_distributivity #t #f (#r: polynomial t {proper_extension r}) (x y z: algebraic r)
  : Lemma (ac_eq (ac_mul (ac_add y z) x)
                 (ac_add (ac_mul y x) (ac_mul z x)))
  = ac_add_rep y z;                                    (* ac_add y z == y + z *)
    ac_add_rep (ac_mul y x) (ac_mul z x);              (* rhs == class_of(y*x) + class_of(z*x) *)
    let yz  : polynomial t = y + z in
    let yx  : polynomial t = y * x in
    let zx  : polynomial t = z * x in
    let yzx : polynomial t = yz * x in
    let myx : polynomial t = (class_of r yx) in
    let mzx : polynomial t = (class_of r zx) in
    class_of_cong r yzx;
    poly_right_distributivity x y z;                   (* poly_eq ((y+z)*x) (y*x + z*x) *)
    cong_of_eq r yzx (yx + zx);
    cong_trans r ((class_of r yzx)) yzx (yx + zx);
    class_of_cong_sym r yx;
    class_of_cong_sym r zx;
    cong_add r yx myx zx mzx;
    cong_trans r ((class_of r yzx)) (yx + zx) (myx + mzx);
    ac_eq_of_cong r (ac_mul (ac_add y z) x) (ac_add (ac_mul y x) (ac_mul z x))

(* ---------------------------------------------------------------- *)
(*  Typeclass instances                                              *)
(* ---------------------------------------------------------------- *)

(* algebraic_equatable is now defined TRANSPARENTLY in the interface (.fsti). *)

(* acr_impl is `unfold` in the .fsti, so `(acr_impl).cr_r.mul` etc. reduce to
   the ac_* ops directly in SMT — no reveal lemma needed (formerly
   acr_impl_reveal / algebraic_ring_reveal, now deleted). *)

(* ===== merged from Core.AlgebraicConstant.Field - field structure of k[x]/(r) for r irreducible (impl detail; not exposed) ===== *)

(* An irreducible r (deg >= 1) does not divide 1. *)
let r_not_divides_one (#t:Type) {| f: field t |} (r: polynomial t)
  : Lemma (requires poly_irreducible r)
          (ensures  ~(divides r poly_one))
  = let aux () : Lemma (requires divides r poly_one)
                       (ensures False)
      = divides_degree_le r poly_one (* deg r <= deg 1 = 0, but deg r >= 1 *)
    in Classical.move_requires aux ()

(* Not divisible by r  =>  a is a nonzero polynomial (Some degree). *)
let deg_some_of_not_div (#t:Type) {| f: field t |} (r a: polynomial t)
  : Lemma (requires (
                     ~(divides r a)))
          (ensures  deg a >= 0)
  =
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let aux () : Lemma (requires deg a < 0)
                       (ensures divides r a)
      = degree_none_poly_eq_zero a;                  (* a ~ poly_zero *)
        divides_zero r;        (* r | poly_zero *)
        poly_eq_symmetry (poly_zero) a;
        divides_congruence_right r (poly_zero) a
    in
    Classical.move_requires aux ()

(* Bridges between ac_eq-to-zero (= is_nonzero, once the ring is fixed) and
   ~(divides r rep).  Both follow directly from the public characterization
   ac_eq_zero_iff_divides. *)
let not_div_of_nonzero (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
  (x: algebraic r)
  : Lemma (requires not (ac_eq x ac_zero))
          (ensures (~(divides r x)))
  = ac_eq_zero_iff_divides x

(* (class_of r a) is divisible by r iff a is: (class_of r a) ~ a (mod r) via the keystone. *)
private let class_of_divides_iff (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
  (a: polynomial t)
  : Lemma (divides r ((class_of r a)) <==> divides r a)
  = let m = (class_of r a) in
    class_of_mod #_ #_ #r a;                                  (* r | (m -- a) *)
    (* divides r (m--a) and divides r a  ⇒  divides r m  (and conversely) *)
    let fwd () : Lemma (requires divides r a) (ensures divides r m)
      = divides_add r a (m -- a);                       (* r | (a + (m--a)) *)
        cr_add_sub_cancel a m;    (* a + (m--a) ~ m *)
        divides_congruence_right r (a + (m -- a)) m in
    let bwd () : Lemma (requires divides r m) (ensures divides r a)
      = divides_sub r m (m -- a);                        (* r | (m -- (m--a)) *)
        cr_sub_sub_self m a;        (* m -- (m--a) ~ a *)
        divides_congruence_right r (m -- (m -- a)) a in
    Classical.move_requires fwd ();
    Classical.move_requires bwd ()

let nonzero_of_not_div (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
  (a: polynomial t)
  : Lemma (requires (~(divides r a)))
          (ensures  not (ac_eq ((class_of r a)) ac_zero))
  = ac_eq_zero_iff_divides ((class_of r a));
    class_of_divides_iff #_ #_ #r a

(* ================================================================ *)
(*  Inverse in the algebraic field:  inv [a] = [bezout_right r a].  *)
(*  For coprime r a (a not divisible by irreducible r), Bezout gives *)
(*    bezout_left*r + bezout_right*a ~ 1,  so  a*bezout_right ~ 1 (mod r). *)
(* ================================================================ *)

let ac_inv (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
  (x: algebraic r)
  : Pure (algebraic r)
         (requires poly_irreducible r /\ not (ac_eq x ac_zero))
         (ensures  fun y -> not (ac_eq y ac_zero) /\
                         coprime r x /\
                         y == (class_of r (bezout_right r x)))
  = let a = x in
    not_div_of_nonzero #_ #_ #r x;                     (* ~(divides r a) *)
    deg_some_of_not_div r a;                  (* deg a >= 0 *)
    irreducible_coprime_or_divides r a;       (* coprime r a \/ divides r a => coprime r a *)
    let br = bezout_right r a in
    let bl = bezout_left  r a in
    let y : algebraic r = (class_of r br) in
    (* br is itself not divisible by r: else r | (bl*r + br*a) ~ 1. *)
    let aux () : Lemma (requires divides r br) (ensures False)
      = bezout_identity r a;                  (* bl * r + br * a ~ 1 *)
        divides_refl       r;                 (* r | r *)
        divides_mul_left   r bl r;            (* r | bl * r *)
        divides_mul_right  r br a;            (* r | br * a *)
        divides_add        r (bl * r) (br * a);
        divides_congruence_right r (bl * r + br * a) one;  (* r | 1 *)
        r_not_divides_one  r
    in
    Classical.move_requires aux ();                                 (* ~(divides r br) *)
    nonzero_of_not_div #_ #_ #r br;                                 (* not (ac_eq y ac_zero) *)
    y

(* ================================================================ *)
(*  Inversion identity:  [a] * [bezout_right r a] = [1]  in the     *)
(*  quotient (and symmetrically), for irreducible r and a not 0.    *)
(* ================================================================ *)

(* z - o  =  (-y) + ((y + z) - o)   *)
let residue_id (#u:Type) {| cr: commutative_ring u |} (y z o: u)
  : Lemma (z + -o = -y + (y + z + -o))
  = assert (z + -o = -y + (y + z + -o)) by Core.Tactics.CanonRing.canon_ring ()

let ac_inv_correct (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
  (x: algebraic r)
  : Lemma (requires poly_irreducible r /\ not (ac_eq x ac_zero))
          (ensures  ac_eq (ac_mul x (ac_inv x)) ac_one /\
                    ac_eq (ac_mul (ac_inv x) x) ac_one)
  =
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let a    = x in
    let inv  = ac_inv x in
    let brp  = bezout_right r a in                    (* the (possibly unreduced) Bezout cofactor *)
    let bl   = bezout_left r a in
    let yv   = bl * r in
    let zv   = brp * a in                             (* brp * a *)
    let onep : polynomial t = one in
    bezout_identity r a;                                     (* yv + zv ~ one *)
    (* r | yv  and  r | -yv *)
    divides_refl     r;
    divides_mul_left r bl r;
    divides_neg      r yv;
    (* (yv + zv) - one ~ zero,  hence r | ((yv + zv) - one) *)
    add_negation onep;                                       (* onep + -onep ~ zero *)
    add_congruence (yv + zv) (- onep) onep (- onep);
    transitivity ((yv + zv) + - onep) (onep + - onep) zero;
    divides_zero r;
    divides_congruence_right r zero ((yv + zv) + - onep);
    (* r | (-yv) + ((yv + zv) - one) *)
    divides_add r (- yv) ((yv + zv) + - onep);
    (* residue identity:  zv - one  ~  (-yv) + ((yv + zv) - one) *)
    residue_id yv zv onep;
    divides_congruence_right r
      ((- yv) + ((yv + zv) + - onep)) (zv + - onep);
    (* now r | (zv -- one), i.e.  cong r zv one.  Bridge through class_of:
       inv == (class_of r brp), ac_mul (ac_inv x) x == (class_of (inv*a) <: algebraic r), so we chain
         class_of(inv*a) ~ inv*a ~ brp*a = zv ~ one  (mod r). *)
    ac_mul_rep inv x;                                       (* ac_mul inv x == class_of(inv*a) *)
    ac_mul_rep x inv;                                       (* ac_mul x inv == class_of(a*inv) *)
    ac_one_rep r;                                            (* ac_one == poly_one == onep *)
    (* cong r zv one  is exactly what the divides chain above established *)
    (* SECOND form: ac_mul (ac_inv x) x == class_of(inv*a) ~ zv ~ one *)
    class_of_cong r (inv * a);               (* class_of(inv*a) ~ inv*a *)
    class_of_cong r brp;                             (* inv == (class_of r brp) ~ brp *)
    cong_refl r a;
    cong_mul r inv brp a a;                          (* inv*a ~ brp*a = zv *)
    cong_trans r ((class_of r (inv * a))) (inv * a) zv;
    cong_trans r ((class_of r (inv * a))) zv onep;     (* uses cong r zv one *)
    ac_eq_of_cong r (ac_mul (ac_inv x) x) ac_one;
    (* FIRST form: ac_mul x (ac_inv x) == class_of(a*inv) ~ a*brp ~ brp*a = zv ~ one *)
    class_of_cong r (a * inv);               (* class_of(a*inv) ~ a*inv *)
    cong_refl r a;
    cong_mul r a a inv brp;                          (* a*inv ~ a*brp *)
    mul_commutativity a brp;                               (* poly_eq (a*brp) (brp*a) *)
    cong_of_eq r (a * brp) zv;
    cong_trans r ((class_of r (a * inv))) (a * inv) (a * brp);
    cong_trans r ((class_of r (a * inv))) (a * brp) zv;
    cong_trans r ((class_of r (a * inv))) zv onep;
    ac_eq_of_cong r (ac_mul x (ac_inv x)) ac_one

(* ================================================================ *)
(*  Inverse respects the quotient equality (inverse is unique).      *)
(*  Standard argument: ia = ia*1 = ia*(b*ib) = (ia*b)*ib             *)
(*                        = (ia*a)*ib = 1*ib = ib.                    *)
(* ================================================================ *)

let ac_inv_congr (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
  (a b: algebraic r)
  : Lemma (requires poly_irreducible r /\
                    not (ac_eq a ac_zero) /\
                    not (ac_eq b ac_zero) /\
                    ac_eq a b)
          (ensures  ac_eq (ac_inv a) (ac_inv b))
  = let ia = ac_inv a in
    let ib = ac_inv b in
    let o  = ac_one in
    ac_elim_equatable_laws r;
    ac_inv_correct a;                         (* ac_eq (ac_mul ia a) o *)
    ac_inv_correct b;                         (* ac_eq (ac_mul b ib) o *)
    (* ia ~ ia*1 *)
    ac_mul_one ia;
    (* 1 ~ b*ib *)
    ac_mul_congruence ia o ia (ac_mul b ib);  (* ac_eq (ia*1) (ia*(b*ib)) *)
    (* ia*(b*ib) ~ (ia*b)*ib *)
    ac_mul_associativity ia b ib;             (* ac_eq ((ia*b)*ib) (ia*(b*ib)) *)
    (* (ia*b)*ib ~ (ia*a)*ib  (since b ~ a) *)
    ac_mul_congruence ia b ia a;              (* ac_eq (ia*b) (ia*a) *)
    ac_mul_congruence (ac_mul ia b) ib (ac_mul ia a) ib;
    (* (ia*a)*ib ~ 1*ib *)
    ac_mul_congruence (ac_mul ia a) ib o ib;  (* ac_eq ((ia*a)*ib) (o*ib) *)
    (* 1*ib ~ ib *)
    ac_mul_one ib                            (* ac_eq (ac_mul o ib) ib (second clause) *)    

(* ================================================================ *)
(*  Assembly:  algebraic r is a FIELD when r is irreducible.      *)
(* ================================================================ *)

(* 1 <> 0 in the quotient: else r | 1, contradicting irreducibility. *)
let ac_one_ne_zero (#t:Type) {| f: field t |}
  (r: polynomial t {proper_extension r})
  : Lemma (not (ac_eq (ac_one <: algebraic r) (ac_zero <: algebraic r)))
  = ac_eq_zero_iff_divides (ac_one <: algebraic r);
    ac_one_rep r;
    r_not_divides_one r

let algebraic_mig (#t:Type) {| f: field t |}
  (r: polynomial t {proper_extension r})
  : mul_is_group (algebraic r) #((acr_impl #_ #_ #r).cr_r)
  = {
      inv             = (fun x -> ac_inv x);
      inv_congr       = (fun aa bb -> ac_inv_congr aa bb);
      inversion_lemma = (fun x -> ac_inv_correct x);
    }

(* algebraic_field is now defined TRANSPARENTLY in the interface (.fsti),
   built directly on the (now public) acr_impl record. *)

(* The public commutative-ring `algebraic_commutative_ring` is now defined
   TRANSPARENTLY in the interface (cr_of_id (id_of_f (algebraic_field r))),
   so it is DEFEQ to the TC-resolved `commutative_ring (algebraic r)` and is
   NOT redefined here.  Its projection chain collapses cr.cr_r back to
   (acr_impl #_ #_ #r).cr_r definitionally, so the reveals below delegate to
   acr_impl_reveal. *)



let algebraic_eq_zero_pointwise (#t:Type) {| f: field t |}
  (r: polynomial t {proper_extension r})
  : Lemma ((forall (x y: algebraic r). eq x y == ac_eq x y) /\
           ((zero <: algebraic r) == (ac_zero <: algebraic r)))
  = ()
