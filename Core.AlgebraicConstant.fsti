module Core.AlgebraicConstant

(*
   Algebraic constants: the quotient ring  polynomial t / (r),
   where r is a fixed polynomial over a field t.

   Phase 1.75 scope: COMMUTATIVE RING ONLY.  No field structure,
   no irreducibility hypothesis, no inverse, no factorization.

   Design: quotient-by-equality.  Carrier is a wrapper around
   `polynomial t` (record with one field), and equality is

       AC a == AC b   iff   r divides (a - b)   in polynomial t.

   All ring operations are inherited verbatim from `polynomial t`;
   their congruence under our equality follows from (r) being an
   ideal of the polynomial ring.
*)

module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Algebra.CongruenceMod
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Irreducible

(* ---------------------------------------------------------------- *)
(*  Carrier                                                          *)
(* ---------------------------------------------------------------- *)

(* The carrier is the CANONICAL reduced representative: a polynomial of
   degree strictly below deg r.  The value *is* the polynomial (no record,
   no projector).  Reduction is performed by the smart constructor `class_of`
   in the .fst; arithmetic that cannot exceed deg r (add, neg) coerces
   directly, while multiplication reduces through `class_of`. *)
let algebraic (#t:Type) {| f: field t |}
              (r: polynomial t {proper_extension r}) =
  p: polynomial t { deg p < deg r }

(* ---------------------------------------------------------------- *)
(*  Operations                                                       *)
(* ---------------------------------------------------------------- *)

val ac_eq (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
          (a b: algebraic r) : bool

(* Smart constructor: reduce an arbitrary polynomial to its canonical
   representative of degree < deg r (the remainder of division by r). *)
val class_of (#t:Type) {| f: field t |} (r: polynomial t {proper_extension r})
    (p: polynomial t) : algebraic r

(* KEYSTONE bridge: reducing p changes it only by a multiple of r, so
   r | (class_of p -- p).  Exposed so downstream modules (Root/EmbedHom) can
   reason "class_of p ~ p (mod r)" — the only handle on class_of's behaviour. *)
val class_of_mod (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
    (p: polynomial t)
  : Lemma (r `divides` ((class_of r p) -- p))

(* class_of-keystone bridges at the generic `cong` (congruence-modulo) level.
   The generic cong toolkit (cong_trans / cong_mul / cong_add / cong_of_eq)
   lives in Core.Algebra.CongruenceMod; these two restate the keystone class_of_mod
   for downstream modules (Root) that push class_of through their recursions. *)
val class_of_cong (#t:Type) {| f: field t |} (r: polynomial t {proper_extension r})
    (p: polynomial t)
  : Lemma (cong r ((class_of r p)) p)

val class_of_cong_sym (#t:Type) {| f: field t |} (r: polynomial t {proper_extension r})
    (p: polynomial t)
  : Lemma (cong r p ((class_of r p)))

(* Conclude ac_eq from cong r for REDUCED reps (the result types of the ac_* ops). *)
val ac_eq_of_cong (#t:Type) {| f: field t |} (r: polynomial t {proper_extension r})
    (lhs rhs: algebraic r)
  : Lemma (requires cong r lhs rhs)
          (ensures  ac_eq lhs rhs)

val ac_zero (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
  : algebraic r

val ac_one (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
  : algebraic r

val ac_add (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
           (a b: algebraic r) : algebraic r

val ac_neg (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
           (a: algebraic r) : algebraic r

val ac_mul (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
           (a b: algebraic r) : algebraic r

(* Nullity in the quotient: [a] = 0  iff  r divides a.rep.  The bridge consumed
   by the field construction (inverse via Bezout). *)
val ac_eq_zero_iff_divides (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
    (a: algebraic r)
  : Lemma (b2t (ac_eq a ac_zero) <==> r `divides` a)

(* General: [a] = [b]  iff  r divides (a - b). *)
val ac_eq_divides (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
    (a b: algebraic r)
  : Lemma (b2t (ac_eq a b) <==> r `divides` (a -- b))

(* Representation reveals (the ring operations are abstract through this interface). *)
(* NOW ac_mul reduces: its rep is class_of of the exact polynomial product. *)
val ac_mul_rep (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
    (a b: algebraic r)
  : Lemma ((ac_mul a b) == class_of r (a * b))

(* ac_add does not reduce: its rep is exactly the polynomial sum (coerced). *)
val ac_add_rep (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
    (a b: algebraic r)
  : Lemma ((ac_add a b <: polynomial t) == a + b)

val ac_one_rep (#t:Type) {| f: field t |} (r: polynomial t {proper_extension r})
  : Lemma ((ac_one #t #f #r <: polynomial t) == poly_one)

(* ---------------------------------------------------------------- *)
(*  Equivalence + ring laws                                          *)
(* ---------------------------------------------------------------- *)

val ac_eq_reflexivity (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                      (a: algebraic r)
  : Lemma (ac_eq a a)

val ac_eq_symmetry (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                   (a b: algebraic r)
  : Lemma (ac_eq a b <==> ac_eq b a)

val ac_eq_transitivity (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                       (a b c: algebraic r)
  : Lemma (requires ac_eq a b /\ ac_eq b c)
          (ensures  ac_eq a c)

val ac_add_congruence (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                      (a1 b1 a2 b2: algebraic r)
  : Lemma (requires ac_eq a1 a2 /\ ac_eq b1 b2)
          (ensures  ac_eq (ac_add a1 b1) (ac_add a2 b2))

val ac_add_associativity (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                         (a b c: algebraic r)
  : Lemma (ac_eq (ac_add (ac_add a b) c) (ac_add a (ac_add b c)))

val ac_add_commutativity (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                         (a b: algebraic r)
  : Lemma (ac_eq (ac_add a b) (ac_add b a))

val ac_add_zero (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                (a: algebraic r)
  : Lemma (ac_eq (ac_add a ac_zero) a /\ ac_eq (ac_add ac_zero a) a)

val ac_neg_congruence (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                      (a1 a2: algebraic r)
  : Lemma (requires ac_eq a1 a2)
          (ensures  ac_eq (ac_neg a1) (ac_neg a2))

val ac_add_negation (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                    (a: algebraic r)
  : Lemma (ac_eq (ac_add a (ac_neg a)) ac_zero /\
           ac_eq (ac_add (ac_neg a) a) ac_zero)

val ac_mul_congruence (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                      (a1 b1 a2 b2: algebraic r)
  : Lemma (requires ac_eq a1 a2 /\ ac_eq b1 b2)
          (ensures  ac_eq (ac_mul a1 b1) (ac_mul a2 b2))

val ac_mul_associativity (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                         (a b c: algebraic r)
  : Lemma (ac_eq (ac_mul (ac_mul a b) c) (ac_mul a (ac_mul b c)))

val ac_mul_one (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
               (a: algebraic r)
  : Lemma (ac_eq (ac_mul a ac_one) a /\ ac_eq (ac_mul ac_one a) a)

val ac_mul_commutativity (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                         (a b: algebraic r)
  : Lemma (ac_eq (ac_mul a b) (ac_mul b a))

val ac_left_distributivity (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                           (a b c: algebraic r)
  : Lemma (ac_eq (ac_mul a (ac_add b c))
                 (ac_add (ac_mul a b) (ac_mul a c)))

(* Stated in the ring class's right_distributivity convention `(y+z)*x` so it
   assigns directly into acr_impl (no permuting lambda). *)
val ac_right_distributivity (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                            (x y z: algebraic r)
  : Lemma (ac_eq (ac_mul (ac_add y z) x)
                 (ac_add (ac_mul y x) (ac_mul z x)))

(* ---------------------------------------------------------------- *)
(*  Typeclass instance                                               *)
(* ---------------------------------------------------------------- *)

(* Transparent in the interface: acr_impl below needs its `.eq` field to
   reduce to ac_eq for the ring-law congruence fields to typecheck. *)
let algebraic_equatable
    (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
  : equatable (algebraic r)
  = {
    eq            = ac_eq;
    reflexivity   = ac_eq_reflexivity;
    symmetry      = ac_eq_symmetry;
    transitivity  = ac_eq_transitivity;
  }

let ac_elim_equatable_laws #t {| f: field t |} (r: polynomial t {proper_extension r})
  : Lemma ((forall (x:algebraic r). x `ac_eq` x) /\ (forall (x y:algebraic r). ac_eq x y <==> ac_eq y x)
          /\ (forall (x y z: algebraic r). ac_eq x y /\ ac_eq y z ==> ac_eq x z)) =
  Classical.forall_intro (ac_eq_reflexivity #t #f #r);
  Classical.forall_intro_2 (Classical.move_requires_2 (ac_eq_symmetry #t #f #r));
  Classical.forall_intro_3 (Classical.move_requires_3 (ac_eq_transitivity #t #f #r))

(* Directly-built commutative-ring record over the quotient, now PUBLIC and
   TRANSPARENT in the interface so that the field's `.cr_r.*` projections
   reduce through it (e.g. `(acr r).cr_r.one` reduces to `ac_one`).
   Kept general in `r` (no irreducibility): the base ring laws hold for any r. *)
unfold
let acr_impl
    (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
  : commutative_ring (algebraic r)
  = {
    cr_r = {
      r_add = {
        acg_eq           = algebraic_equatable;
        zero             = ac_zero;
        add              = ac_add;
        add_congruence   = ac_add_congruence;
        add_commutativity= ac_add_commutativity;
        add_associativity= ac_add_associativity;
        add_zero         = ac_add_zero;
        neg              = ac_neg;
        neg_congruence   = ac_neg_congruence;
        add_negation     = ac_add_negation;
      };
      one                  = ac_one;
      mul                  = ac_mul;
      mul_congruence       = ac_mul_congruence;
      mul_associativity    = ac_mul_associativity;
      mul_one              = ac_mul_one;
      left_distributivity  = ac_left_distributivity;
      right_distributivity = ac_right_distributivity;
    };
    cr_mic = {
      mul_commutativity = ac_mul_commutativity;
    };
  }

(* acr_impl is `unfold` (above), so its projections reduce to the ac_* ops
   directly in SMT — no reveal lemma is needed. *)

(* 1 <> 0 in the quotient: else r | 1, contradicting irreducibility.
   Body in the .fst. *)
val ac_one_ne_zero (#t:Type) {| f: field t |}
  (r: polynomial t {proper_extension r})
  : Lemma (not (ac_eq (ac_one #t #f #r) (ac_zero #t #f #r)))

(* The multiplicative-group structure on the quotient (inverse via Bezout).
   Body in the .fst. *)
val algebraic_mig (#t:Type) {| f: field t |}
  (r: polynomial t {proper_extension r})
  : mul_is_group (algebraic r) #((acr_impl #t #f #r).cr_r)

(* The single published instance: algebraic r is a FIELD when r is
   irreducible.  Defined TRANSPARENTLY here (built directly on acr_impl) so
   that its `.cr_r.*` projections reduce.  The commutative ring below is its
   projection. *)
instance algebraic_field (#t:Type) {| f: field t |}
  (r: polynomial t {proper_extension r})
  : field (algebraic r)
  = {
      f_sf          = { sf_r = acr_impl.cr_r;
                        sf_mig = algebraic_mig r };
      f_mic         = acr_impl.cr_mic;
      f_one_ne_zero = ac_one_ne_zero r;
    }

(* The public commutative-ring, recovered as the published field's
   projection (cr_of_id (id_of_f field)).  Requires irreducibility because
   the field does.  Defined TRANSPARENTLY in the interface (a plain `let`,
   not `unfold` — avoiding the record-inlining trap) so that it is DEFEQ to
   the TC-resolved `commutative_ring (algebraic r)` downstream: both are
   `cr_of_id (id_of_f (algebraic_field r))` (cr_of_id/id_of_f are unfold
   instances).  This is one record everywhere — no `coerce_eq` bridges. *)
let algebraic_commutative_ring (#t:Type) {| f: field t |}
  (r: polynomial t {proper_extension r})
  : commutative_ring (algebraic r)
  = cr_of_id (algebraic r)



(* Pointwise reveal: the commutative-ring's equality applied to any two
   elements is ac_eq applied to them, and its zero is ac_zero.  Stated
   pointwise so SMT can instantiate at the specific arguments it needs
   (the function-level == in algebraic_ring_reveal does not fire on
   applications). *)
val algebraic_eq_zero_pointwise (#t:Type) {| f: field t |}
  (r: polynomial t {proper_extension r})
  : Lemma ((forall (x y: algebraic r). eq x y == ac_eq x y) /\
           (zero == ac_zero #t #f #r))


