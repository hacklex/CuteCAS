module FStar.Algebra.Classes.Polynomial

(*
  Univariate polynomials over an integral domain.

  Representation: a list of coefficients, index 0 = constant term, last index =
  leading coefficient. There is NO canonical-form refinement: trailing zeros
  are allowed. Polynomial equality is defined coefficient-wise modulo trailing
  zeros, which makes representation hygiene a non-issue and keeps proofs short.

  Phase 1 deliverable. Built on the new typeclass tower (no AlgebraTypes).
*)

module TC = FStar.Tactics.Typeclasses
module L = FStar.List.Tot

open FStar.Algebra.Classes.Equatable
open FStar.Algebra.Classes.Grouplikes
open FStar.Algebra.Classes.Ringlikes

(* ------------------------------------------------------------------------ *)
(*  Representation                                                          *)
(* ------------------------------------------------------------------------ *)

let coeff (#t:Type) {| h: has_zero t |} (p: polynomial t) (i: nat) : t =
  if i < L.length p then L.index p i else zero

let poly_zero (#t:Type) : polynomial t = []

let poly_one (#t:Type) {| h: has_one t |} : polynomial t = [one]

(* ------------------------------------------------------------------------ *)
(*  Equality                                                                *)
(*                                                                          *)
(*  Coefficient-wise equality with trailing zeros ignored.                  *)
(*  poly_eq p q is "for every i, coeff p i =_t coeff q i".                  *)
(* ------------------------------------------------------------------------ *)

let rec all_zero (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Tot bool (decreases L.length p)
  = match p with
    | [] -> true
    | a :: p' -> (a = zero) && all_zero p'

let rec poly_eq (#t:Type) {| h: has_zero t |} (p q: polynomial t)
  : Tot bool (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _ -> all_zero q
    | _, [] -> all_zero p
    | a :: p', b :: q' -> (a = b) && poly_eq p' q'

let rec poly_eq_reflexivity (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (ensures poly_eq p p) (decreases L.length p)
  = match p with
    | [] -> ()
    | a :: p' -> h.eq.reflexivity a; poly_eq_reflexivity p'

let rec poly_eq_symmetry (#t:Type) {| h: has_zero t |} (p q: polynomial t)
  : Lemma (ensures poly_eq p q <==> poly_eq q p)
    (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _ -> ()
    | _ :: _, [] -> ()
    | a :: p', b :: q' ->
        h.eq.symmetry a b;
        poly_eq_symmetry p' q'

let rec poly_eq_trans_lhs_empty (#t:Type) {| h: has_zero t |} (q r: polynomial t)
  : Lemma (requires all_zero q /\ poly_eq q r) (ensures all_zero r)
    (decreases %[L.length q; L.length r])
  = match q, r with
    | [], _ -> ()
    | _ :: _, [] -> ()
    | b :: q', c :: r' ->
        h.eq.symmetry b c;
        h.eq.transitivity c b zero;
        poly_eq_trans_lhs_empty q' r'

let rec poly_eq_trans_rhs_empty (#t:Type) {| h: has_zero t |} (p q: polynomial t)
  : Lemma (requires poly_eq p q /\ all_zero q) (ensures all_zero p)
    (decreases %[L.length p; L.length q])
  = match p, q with
    | _, [] -> ()
    | [], _ -> ()
    | a :: p', b :: q' ->
        h.eq.transitivity a b zero;
        poly_eq_trans_rhs_empty p' q'

let rec poly_eq_trans_mid_empty (#t:Type) {| h: has_zero t |} (p r: polynomial t)
  : Lemma (requires all_zero p /\ all_zero r) (ensures poly_eq p r)
    (decreases %[L.length p; L.length r])
  = match p, r with
    | [], _ -> ()
    | _ :: _, [] -> ()
    | a :: p', c :: r' ->
        h.eq.symmetry c zero;
        h.eq.transitivity a zero c;
        poly_eq_trans_mid_empty p' r'

let rec poly_eq_transitivity (#t:Type) {| h: has_zero t |} (p q r: polynomial t)
  : Lemma (requires poly_eq p q /\ poly_eq q r) (ensures poly_eq p r)
    (decreases %[L.length p; L.length q; L.length r])
  = match p, q, r with
    | [], _, _ ->
        poly_eq_trans_lhs_empty q r
    | _ :: _, [], _ ->
        poly_eq_trans_rhs_empty p q;
        poly_eq_trans_mid_empty p r
    | _ :: _, _ :: _, [] ->
        poly_eq_trans_rhs_empty p q;
        poly_eq_trans_mid_empty p r
    | a :: p', b :: q', c :: r' ->
        h.eq.transitivity a b c;
        poly_eq_transitivity p' q' r'

(* ------------------------------------------------------------------------ *)
(*  Equatable instance                                                      *)
(* ------------------------------------------------------------------------ *)

instance polynomial_equatable (#t:Type) {| h: has_zero t |}
  : equatable (polynomial t) = {
    op_Equals = poly_eq;
    reflexivity = poly_eq_reflexivity;
    symmetry = poly_eq_symmetry;
    transitivity = poly_eq_transitivity;
  }

(* ------------------------------------------------------------------------ *)
(*  Addition                                                                *)
(* ------------------------------------------------------------------------ *)

let rec poly_add (#t:Type) {| m: add_monoid t |} (p q: polynomial t)
  : Tot (polynomial t) (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _ -> q
    | _, [] -> p
    | a :: p', b :: q' -> (a + b) :: poly_add p' q'

#push-options "--fuel 2 --ifuel 2 --z3rlimit 15"

let h_axb_eq_zero (#t:Type) {| m: add_monoid t |} (a b: t)
  : Lemma (requires (a = zero) /\ (b = zero)) (ensures (a + b = (zero <: t)))
  = let z : t = zero in
    assert (z == zero);
    left_add_identity z;
    add_congruence a b z z;
    transitivity (a + b) (z + z) z

let h_zero_plus_x_eq_x (#t:Type) {| m: add_monoid t |} (a b: t)
  : Lemma (requires a = zero) (ensures a + b = b)
  = m.has_zero.eq.reflexivity b;
    add_congruence a b zero b;
    left_add_identity b;
    transitivity (a + b) (zero + b) b

let h_x_plus_zero_eq_x (#t:Type) {| m: add_monoid t |} (a b: t)
  : Lemma (requires b = zero) (ensures a + b = a)
  = m.has_zero.eq.reflexivity a;
    add_congruence a b a zero;
    right_add_identity a;
    transitivity (a + b) (a + zero) a

#pop-options

let rec poly_add_left_all_zero (#t:Type) {| m: add_monoid t |} (p q: polynomial t)
  : Lemma (requires all_zero #t #m.has_zero p)
          (ensures poly_eq #t #m.has_zero (poly_add p q) q)
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _ ->
        poly_eq_reflexivity #t #m.has_zero q
    | _ :: _, [] -> ()
    | a :: p', b :: q' ->
        h_zero_plus_x_eq_x a b;
        poly_add_left_all_zero p' q'

let rec poly_add_right_all_zero (#t:Type) {| m: add_monoid t |} (p q: polynomial t)
  : Lemma (requires all_zero #t #m.has_zero q)
          (ensures poly_eq #t #m.has_zero (poly_add p q) p)
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _ -> ()
    | _ :: _, [] ->
        poly_eq_reflexivity #t #m.has_zero p
    | a :: p', b :: q' ->
        h_x_plus_zero_eq_x a b;
        poly_add_right_all_zero p' q'

#push-options "--fuel 3 --ifuel 3 --z3rlimit 30"
let poly_add_left_cong_case_zero_cons_cons
      (#t:Type) {| m: add_monoid t |}
      (b2: t) (p2' q': polynomial t) (c: t)
  : Lemma (requires b2 = zero /\ all_zero #t #m.has_zero p2')
          (ensures poly_eq #t #m.has_zero
                     (c :: q')
                     ((b2 + c) :: poly_add p2' q'))
  = h_zero_plus_x_eq_x b2 c;
    m.has_zero.eq.symmetry (b2 + c) c;
    poly_add_left_all_zero p2' q';
    poly_eq_symmetry #t #m.has_zero (poly_add p2' q') q'

let poly_add_left_cong_case_cons_zero_cons
      (#t:Type) {| m: add_monoid t |}
      (b1: t) (p1' q': polynomial t) (c: t)
  : Lemma (requires b1 = zero /\ all_zero #t #m.has_zero p1')
          (ensures poly_eq #t #m.has_zero
                     ((b1 + c) :: poly_add p1' q')
                     (c :: q'))
  = h_zero_plus_x_eq_x b1 c;
    poly_add_left_all_zero p1' q'

let poly_add_left_cong_case_cons_cons_cons
      (#t:Type) {| m: add_monoid t |}
      (a1: t) (p1': polynomial t) (a2: t) (p2': polynomial t)
      (c: t) (q': polynomial t)
  : Lemma (requires a1 = a2 /\
                    poly_eq #t #m.has_zero (poly_add p1' q') (poly_add p2' q'))
          (ensures poly_eq #t #m.has_zero
                     ((a1 + c) :: poly_add p1' q')
                     ((a2 + c) :: poly_add p2' q'))
  = m.has_zero.eq.reflexivity c;
    add_congruence a1 c a2 c

let poly_add_right_cong_case_cons_cons_empty
      (#t:Type) {| m: add_monoid t |}
      (a: t) (p': polynomial t) (c1: t) (q1': polynomial t)
  : Lemma (requires c1 = zero /\ all_zero #t #m.has_zero q1')
          (ensures poly_eq #t #m.has_zero
                     ((a + c1) :: poly_add p' q1')
                     (a :: p'))
  = h_x_plus_zero_eq_x a c1;
    poly_add_right_all_zero p' q1'

let poly_add_right_cong_case_cons_empty_cons
      (#t:Type) {| m: add_monoid t |}
      (a: t) (p': polynomial t) (c2: t) (q2': polynomial t)
  : Lemma (requires c2 = zero /\ all_zero #t #m.has_zero q2')
          (ensures poly_eq #t #m.has_zero
                     (a :: p')
                     ((a + c2) :: poly_add p' q2'))
  = h_x_plus_zero_eq_x a c2;
    m.has_zero.eq.symmetry (a + c2) a;
    poly_add_right_all_zero p' q2';
    poly_eq_symmetry #t #m.has_zero (poly_add p' q2') p'

let poly_add_right_cong_case_cons_cons_cons
      (#t:Type) {| m: add_monoid t |}
      (a: t) (p': polynomial t) (c1: t) (q1': polynomial t)
      (c2: t) (q2': polynomial t)
  : Lemma (requires c1 = c2 /\
                    poly_eq #t #m.has_zero (poly_add p' q1') (poly_add p' q2'))
          (ensures poly_eq #t #m.has_zero
                     ((a + c1) :: poly_add p' q1')
                     ((a + c2) :: poly_add p' q2'))
  = m.has_zero.eq.reflexivity a;
    add_congruence a c1 a c2
#pop-options

#push-options "--fuel 3 --ifuel 3 --z3rlimit 60"
let rec poly_add_left_congruence (#t:Type) {| m: add_monoid t |}
                                 (p1 p2 q: polynomial t)
  : Lemma (requires poly_eq #t #m.has_zero p1 p2)
          (ensures poly_eq #t #m.has_zero (poly_add p1 q) (poly_add p2 q))
          (decreases %[L.length p1; L.length p2; L.length q])
  = match p1, p2, q with
    | [], [], _ ->
        poly_eq_reflexivity #t #m.has_zero (poly_add p1 q)
    | [], _ :: _, [] ->
        ()
    | [], b2 :: p2', c :: q' ->
        poly_add_left_cong_case_zero_cons_cons #t #m b2 p2' q' c
    | _ :: _, [], [] ->
        ()
    | b1 :: p1', [], c :: q' ->
        poly_add_left_cong_case_cons_zero_cons #t #m b1 p1' q' c
    | _ :: _, _ :: _, [] ->
        ()
    | a1 :: p1', a2 :: p2', c :: q' ->
        poly_add_left_congruence p1' p2' q';
        poly_add_left_cong_case_cons_cons_cons #t #m a1 p1' a2 p2' c q'
#pop-options

#push-options "--fuel 3 --ifuel 3 --z3rlimit 60"
let rec poly_add_right_congruence (#t:Type) {| m: add_monoid t |}
                                  (p q1 q2: polynomial t)
  : Lemma (requires poly_eq #t #m.has_zero q1 q2)
          (ensures poly_eq #t #m.has_zero (poly_add p q1) (poly_add p q2))
          (decreases %[L.length p; L.length q1; L.length q2])
  = match p, q1, q2 with
    | _, [], [] ->
        poly_eq_reflexivity #t #m.has_zero (poly_add p q1)
    | [], _ :: _, _ :: _ ->
        ()
    | [], [], _ :: _ ->
        ()
    | [], _ :: _, [] ->
        ()
    | _ :: _, [], [] ->
        poly_eq_reflexivity #t #m.has_zero p
    | a :: p', [], c2 :: q2' ->
        poly_add_right_cong_case_cons_empty_cons #t #m a p' c2 q2'
    | a :: p', c1 :: q1', [] ->
        poly_add_right_cong_case_cons_cons_empty #t #m a p' c1 q1'
    | a :: p', c1 :: q1', c2 :: q2' ->
        poly_add_right_congruence p' q1' q2';
        poly_add_right_cong_case_cons_cons_cons #t #m a p' c1 q1' c2 q2'
#pop-options

let poly_add_congruence (#t:Type) {| m: add_monoid t |}
                        (p1 q1 p2 q2: polynomial t)
  : Lemma (requires poly_eq #t #m.has_zero p1 p2 /\ poly_eq #t #m.has_zero q1 q2)
          (ensures poly_eq #t #m.has_zero (poly_add p1 q1) (poly_add p2 q2))
  = poly_add_left_congruence p1 p2 q1;
    poly_add_right_congruence p2 q1 q2;
    poly_eq_transitivity #t #m.has_zero (poly_add p1 q1) (poly_add p2 q1) (poly_add p2 q2)

let poly_add_left_identity (#t:Type) {| m: add_monoid t |} (p: polynomial t)
  : Lemma (poly_eq #t #m.has_zero (poly_add (poly_zero #t) p) p)
  = poly_eq_reflexivity #t #m.has_zero p

let poly_add_right_identity (#t:Type) {| m: add_monoid t |} (p: polynomial t)
  : Lemma (poly_eq #t #m.has_zero (poly_add p (poly_zero #t)) p)
  = match p with
    | [] -> ()
    | _ :: _ -> poly_eq_reflexivity #t #m.has_zero p

#push-options "--fuel 3 --ifuel 3 --z3rlimit 30"
let rec poly_add_associative
  (#t:Type) {| m: add_monoid t |}
  (p q r: polynomial t)
  : Lemma (ensures poly_eq #t #m.has_zero
                     (poly_add (poly_add p q) r)
                     (poly_add p (poly_add q r)))
          (decreases %[L.length p; L.length q; L.length r])
  = match p, q, r with
    | [], _, _ -> poly_eq_reflexivity #t #m.has_zero (poly_add q r)
    | _ :: _, [], _ -> poly_eq_reflexivity #t #m.has_zero (poly_add p r)
    | _ :: _, _ :: _, [] -> poly_eq_reflexivity #t #m.has_zero (poly_add p q)
    | a :: p', b :: q', c :: r' ->
        add_associativity a b c;
        poly_add_associative p' q' r'
#pop-options

#push-options "--fuel 3 --ifuel 3 --z3rlimit 30"
let rec poly_add_commutative
  (#t:Type) {| m: add_comm_monoid t |}
  (p q: polynomial t)
  : Lemma (ensures poly_eq #t #m.add_monoid.has_zero (poly_add p q) (poly_add q p))
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], [] -> ()
    | [], _ :: _ -> poly_eq_reflexivity #t #m.add_monoid.has_zero q
    | _ :: _, [] -> poly_eq_reflexivity #t #m.add_monoid.has_zero p
    | a :: p', b :: q' ->
        add_commutativity a b;
        poly_add_commutative p' q'
#pop-options

(* ------------------------------------------------------------------------ *)
(*  Instances: has_zero, has_add, add_semigroup, add_monoid                 *)
(* ------------------------------------------------------------------------ *)

instance polynomial_has_zero (#t:Type) {| h: has_zero t |}
  : has_zero (polynomial t)
  = {
      eq = polynomial_equatable #t #h;
      zero = poly_zero;
    }

instance polynomial_has_add (#t:Type) {| m: add_monoid t |}
  : has_add (polynomial t)
  = {
      ( + ) = poly_add;
      eq = polynomial_equatable #t #m.has_zero;
      congruence = (fun p1 q1 p2 q2 -> poly_add_congruence p1 q1 p2 q2);
    }

instance polynomial_add_semigroup (#t:Type) {| m: add_monoid t |}
  : add_semigroup (polynomial t)
  = {
      has_add = polynomial_has_add #t #m;
      associativity = (fun p q r -> poly_add_associative p q r);
    }

instance polynomial_add_monoid (#t:Type) {| m: add_monoid t |}
  : add_monoid (polynomial t)
  = {
      has_zero = polynomial_has_zero #t #m.has_zero;
      add_semigroup = polynomial_add_semigroup #t #m;
      left_add_identity = (fun p -> poly_add_left_identity p);
      right_add_identity = (fun p -> poly_add_right_identity p);
    }

(* ------------------------------------------------------------------------ *)
(*  Commutative additive monoid instances                                   *)
(* ------------------------------------------------------------------------ *)

instance polynomial_add_comm_magma (#t:Type) {| m: add_comm_monoid t |}
  : add_comm_magma (polynomial t)
  = {
      has_add = polynomial_has_add #t #m.add_monoid;
      add_commutativity = (fun p q -> poly_add_commutative p q);
    }

instance polynomial_add_comm_semigroup (#t:Type) {| m: add_comm_monoid t |}
  : add_comm_semigroup (polynomial t)
  = {
      add_semigroup = polynomial_add_semigroup #t #m.add_monoid;
      add_comm_magma = polynomial_add_comm_magma #t #m;
    }

instance polynomial_add_comm_monoid (#t:Type) {| m: add_comm_monoid t |}
  : add_comm_monoid (polynomial t)
  = {
      add_monoid = polynomial_add_monoid #t #m.add_monoid;
      add_comm_semigroup = polynomial_add_comm_semigroup #t #m;
    }

(* ------------------------------------------------------------------------ *)
(*  Negation                                                                *)
(* ------------------------------------------------------------------------ *)

let rec poly_neg (#t:Type) {| g: add_comm_group t |} (p: polynomial t)
  : Tot (polynomial t) (decreases L.length p)
  = match p with
    | [] -> []
    | a :: p' -> (-a) :: poly_neg p'

let poly_sub (#t:Type) {| g: add_comm_group t |} (p q: polynomial t)
  : polynomial t
  = poly_add p (poly_neg q)

let rec poly_neg_all_zero (#t:Type) {| g: add_comm_group t |} (p: polynomial t)
  : Lemma (requires all_zero #t #g.add_group.add_monoid.has_zero p)
          (ensures all_zero #t #g.add_group.add_monoid.has_zero (poly_neg p))
          (decreases L.length p)
  = match p with
    | [] -> ()
    | a :: p' ->
        // a = zero -> -a = zero, by negation law: a + (-a) = 0 and a = 0 ==> 0 + (-a) = 0 ==> -a = 0
        g.add_group.negation a;
        // a + (-a) = zero
        h_zero_plus_x_eq_x a (-a);
        // a + (-a) = -a  (since a = zero)
        g.add_group.add_monoid.has_zero.eq.symmetry (a + (-a)) (-a);
        g.add_group.add_monoid.has_zero.eq.transitivity (-a) (a + (-a)) zero;
        poly_neg_all_zero p'

let rec poly_neg_congruence
  (#t:Type) {| g: add_comm_group t |} (p q: polynomial t)
  : Lemma (requires poly_eq #t #g.add_group.add_monoid.has_zero p q)
          (ensures poly_eq #t #g.add_group.add_monoid.has_zero (poly_neg p) (poly_neg q))
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _ -> poly_neg_all_zero q
    | _ :: _, [] -> poly_neg_all_zero p
    | a :: p', b :: q' ->
        // a = b -> -a = -b: use negation law on both, plus left/right cancellation
        // simpler: use negation_uniqueness via a+(-a) = 0 = b+(-b), and a = b
        // i.e., a + (-a) = b + (-b), with a=b, so by add_congruence and group properties (-a) = (-b)
        // Direct via the negation lemma applied to congruence_of_negation, which doesn't exist as a top-level.
        // Use: a + (-b) = b + (-b) = 0 (by congruence with a=b and reflexivity of -b, then negation b)
        //      Then a + (-b) = 0, and a + (-a) = 0, so by transitivity (-a) and (-b) play same role:
        //      Actually: (-b) = (-b) + 0 = (-b) + (a + (-a)) = ((-b) + a) + (-a)
        //                    = ((-b) + b) + (-a)  (using a = b)
        //                    = 0 + (-a) = -a. So -a = -b (symmetric).
        let ha = g.add_group.add_monoid.has_zero in
        let neg_a : t = -a in
        let neg_b : t = -b in
        ha.eq.reflexivity neg_b;
        add_congruence a neg_b b neg_b;          // a + (-b) = b + (-b)
        g.add_group.negation b;                    // b + (-b) = zero
        ha.eq.transitivity (a + neg_b) (b + neg_b) zero;
        // So a + (-b) = zero. Also a + (-a) = zero, so -a + a = 0 + ... actually use that -b is an inverse for a too
        // Now compute -b = (-b) + 0 = (-b) + (a + (-a)) = ((-b) + a) + (-a)
        //                = (a + (-b)) + (-a) (by commutativity)
        //                = 0 + (-a) = -a.
        add_commutativity neg_b a;                 // -b + a = a + -b = 0
        ha.eq.transitivity (neg_b + a) (a + neg_b) zero;
        // (-b + a) = 0
        g.add_group.negation a;                    // a + (-a) = 0  AND  (-a) + a = 0
        // Try: -a = (-b + a) + (-a)? We need an associativity argument:
        //   -b = -b + 0 = -b + (a + -a) = (-b + a) + -a = 0 + -a = -a
        ha.eq.reflexivity neg_a;
        add_congruence neg_b (a + (-a)) neg_b zero;
        // -b + (a + -a) = -b + 0
        ha.eq.symmetry (neg_b + (a + (-a))) (neg_b + zero);
        // -b + 0 = -b + (a + -a)
        right_add_identity neg_b;                  // -b + 0 = -b
        ha.eq.symmetry (neg_b + zero) neg_b;       // -b = -b + 0
        ha.eq.transitivity neg_b (neg_b + zero) (neg_b + (a + (-a)));
        // -b = -b + (a + -a)
        add_associativity neg_b a (-a);            // (-b + a) + -a = -b + (a + -a)
        ha.eq.symmetry ((neg_b + a) + (-a)) (neg_b + (a + (-a)));
        ha.eq.transitivity neg_b (neg_b + (a + (-a))) ((neg_b + a) + (-a));
        // -b = (-b + a) + -a
        add_congruence (neg_b + a) (-a) zero (-a); // (-b + a) + -a = 0 + -a
        ha.eq.transitivity neg_b ((neg_b + a) + (-a)) (zero + (-a));
        left_add_identity neg_a;                    // 0 + -a = -a
        ha.eq.transitivity neg_b (zero + neg_a) neg_a;
        // -b = -a. Need -a = -b.
        ha.eq.symmetry neg_b neg_a;
        poly_neg_congruence p' q'

let t_neg_congruence_helper (#t:Type) {| g: add_comm_group t |} (a b: t)
  : Lemma (requires a = b) (ensures (-a) = (-b))
  = let ha = g.add_group.add_monoid.has_zero in
    let neg_a : t = -a in
    let neg_b : t = -b in
    ha.eq.reflexivity neg_b;
    add_congruence a neg_b b neg_b;
    g.add_group.negation b;
    ha.eq.transitivity (a + neg_b) (b + neg_b) zero;
    add_commutativity neg_b a;
    ha.eq.transitivity (neg_b + a) (a + neg_b) zero;
    g.add_group.negation a;
    ha.eq.reflexivity neg_a;
    add_congruence neg_b (a + (-a)) neg_b zero;
    ha.eq.symmetry (neg_b + (a + (-a))) (neg_b + zero);
    right_add_identity neg_b;
    ha.eq.symmetry (neg_b + zero) neg_b;
    ha.eq.transitivity neg_b (neg_b + zero) (neg_b + (a + (-a)));
    add_associativity neg_b a (-a);
    ha.eq.symmetry ((neg_b + a) + (-a)) (neg_b + (a + (-a)));
    ha.eq.transitivity neg_b (neg_b + (a + (-a))) ((neg_b + a) + (-a));
    add_congruence (neg_b + a) (-a) zero (-a);
    ha.eq.transitivity neg_b ((neg_b + a) + (-a)) (zero + (-a));
    left_add_identity neg_a;
    ha.eq.transitivity neg_b (zero + neg_a) neg_a;
    ha.eq.symmetry neg_b neg_a

let rec poly_negation_law
  (#t:Type) {| g: add_comm_group t |} (p: polynomial t)
  : Lemma (ensures all_zero #t #g.add_group.add_monoid.has_zero (poly_add p (poly_neg p)))
          (decreases L.length p)
  = match p with
    | [] -> ()
    | a :: p' ->
        g.add_group.negation a;
        poly_negation_law p'

let rec poly_negation_law_left
  (#t:Type) {| g: add_comm_group t |} (p: polynomial t)
  : Lemma (ensures all_zero #t #g.add_group.add_monoid.has_zero (poly_add (poly_neg p) p))
          (decreases L.length p)
  = match p with
    | [] -> ()
    | a :: p' ->
        g.add_group.negation a;
        poly_negation_law_left p'

instance polynomial_has_neg (#t:Type) {| g: add_comm_group t |}
  : has_neg (polynomial t)
  = { op_Minus = poly_neg }

instance polynomial_has_sub (#t:Type) {| g: add_comm_group t |}
  : has_sub (polynomial t)
  = { op_Subtraction = poly_sub }

let poly_neg_inversion
  (#t:Type) {| g: add_comm_group t |} (p: polynomial t)
  : Lemma (poly_eq #t #g.add_group.add_monoid.has_zero (poly_add p (poly_neg p)) poly_zero
        /\ poly_eq #t #g.add_group.add_monoid.has_zero (poly_add (poly_neg p) p) poly_zero)
  = poly_negation_law p;
    poly_negation_law_left p

let poly_sub_def
  (#t:Type) {| g: add_comm_group t |} (p q: polynomial t)
  : Lemma (poly_eq #t #g.add_group.add_monoid.has_zero
            (poly_sub p q) (poly_add p (poly_neg q)))
  = poly_eq_reflexivity #t #g.add_group.add_monoid.has_zero (poly_add p (poly_neg q))

instance polynomial_add_group (#t:Type) {| g: add_comm_group t |}
  : add_group (polynomial t)
  = {
      add_monoid = polynomial_add_monoid #t #g.add_comm_monoid.add_monoid;
      has_neg = polynomial_has_neg #t #g;
      has_sub = polynomial_has_sub #t #g;
      subtraction_definition = (fun p q -> poly_sub_def p q);
      negation = (fun p -> poly_neg_inversion p);
    }

instance polynomial_add_comm_group (#t:Type) {| g: add_comm_group t |}
  : add_comm_group (polynomial t)
  = {
      add_group = polynomial_add_group #t #g;
      add_comm_monoid = polynomial_add_comm_monoid #t #g.add_comm_monoid;
    }

(* ========================================================================== *)
(*  Multiplication                                                            *)
(* ========================================================================== *)

let rec scalar_mul (#t:Type) {| r: semiring t |} (a: t) (q: polynomial t)
  : Tot (polynomial t) (decreases L.length q)
  = match q with
    | [] -> []
    | b :: q' -> (a * b) :: scalar_mul a q'

let rec poly_mul (#t:Type) {| r: semiring t |} (p q: polynomial t)
  : Tot (polynomial t) (decreases L.length p)
  = match p with
    | [] -> []
    | a :: p' -> poly_add (scalar_mul a q) (zero :: poly_mul p' q)

(* Hygiene helpers under the additive structure of the semiring. *)

let semiring_has_zero (#t:Type) (r: semiring t) : has_zero t
  = r.add_comm_monoid.add_monoid.has_zero

(* scalar_mul congruence in the polynomial argument. *)
let rec scalar_mul_right_congruence
  (#t:Type) {| r: semiring t |} (a: t) (q1 q2: polynomial t)
  : Lemma (requires poly_eq #t #(semiring_has_zero r) q1 q2)
          (ensures poly_eq #t #(semiring_has_zero r)
                     (scalar_mul a q1) (scalar_mul a q2))
          (decreases %[L.length q1; L.length q2])
  = let ha = semiring_has_zero r in
    match q1, q2 with
    | [], [] -> ()
    | [], b :: q2' ->
        // all_zero q2 -> b = zero -> a*b = zero, scalar_mul a q2' all_zero
        ha.eq.reflexivity a;
        mul_congruence a b a zero;
        right_absorption a;
        ha.eq.transitivity (a * b) (a * zero) zero;
        scalar_mul_right_congruence a [] q2'
    | b :: q1', [] ->
        ha.eq.reflexivity a;
        mul_congruence a b a zero;
        right_absorption a;
        ha.eq.transitivity (a * b) (a * zero) zero;
        scalar_mul_right_congruence a q1' []
    | b1 :: q1', b2 :: q2' ->
        ha.eq.reflexivity a;
        mul_congruence a b1 a b2;
        scalar_mul_right_congruence a q1' q2'

let rec scalar_mul_left_congruence
  (#t:Type) {| r: semiring t |} (a1 a2: t) (q: polynomial t)
  : Lemma (requires a1 = a2)
          (ensures poly_eq #t #(semiring_has_zero r)
                     (scalar_mul a1 q) (scalar_mul a2 q))
          (decreases L.length q)
  = let ha = semiring_has_zero r in
    match q with
    | [] -> ()
    | b :: q' ->
        ha.eq.reflexivity b;
        mul_congruence a1 b a2 b;
        scalar_mul_left_congruence a1 a2 q'

let rec scalar_mul_zero
  (#t:Type) {| r: semiring t |} (q: polynomial t)
  : Lemma (ensures all_zero #t #(semiring_has_zero r) (scalar_mul zero q))
          (decreases L.length q)
  = match q with
    | [] -> ()
    | b :: q' ->
        left_absorption b;
        scalar_mul_zero q'

let rec scalar_mul_distrib_add_right
  (#t:Type) {| r: semiring t |} (a: t) (q1 q2: polynomial t)
  : Lemma (ensures poly_eq #t #(semiring_has_zero r)
                     (scalar_mul a (poly_add q1 q2))
                     (poly_add (scalar_mul a q1) (scalar_mul a q2)))
          (decreases %[L.length q1; L.length q2])
  = let ha = semiring_has_zero r in
    match q1, q2 with
    | [], _ -> poly_eq_reflexivity #t #ha (scalar_mul a q2)
    | _ :: _, [] -> poly_eq_reflexivity #t #ha (scalar_mul a q1)
    | b1 :: q1', b2 :: q2' ->
        left_distributivity a b1 b2;
        scalar_mul_distrib_add_right a q1' q2'

let rec scalar_mul_distrib_add_left
  (#t:Type) {| r: semiring t |} (a1 a2: t) (q: polynomial t)
  : Lemma (ensures poly_eq #t #(semiring_has_zero r)
                     (scalar_mul (a1 + a2) q)
                     (poly_add (scalar_mul a1 q) (scalar_mul a2 q)))
          (decreases L.length q)
  = match q with
    | [] -> ()
    | b :: q' ->
        right_distributivity a1 a2 b;
        scalar_mul_distrib_add_left a1 a2 q'

let rec scalar_mul_assoc
  (#t:Type) {| r: semiring t |} (a b: t) (q: polynomial t)
  : Lemma (ensures poly_eq #t #(semiring_has_zero r)
                     (scalar_mul (a * b) q)
                     (scalar_mul a (scalar_mul b q)))
          (decreases L.length q)
  = match q with
    | [] -> ()
    | c :: q' ->
        mul_associativity a b c;
        scalar_mul_assoc a b q'

let rec scalar_mul_zero_coefficient
  (#t:Type) {| r: semiring t |} (a: t) (q: polynomial t)
  : Lemma (requires a = zero)
          (ensures all_zero #t #(semiring_has_zero r) (scalar_mul a q))
          (decreases L.length q)
  = let ha = semiring_has_zero r in
    match q with
    | [] -> ()
    | b :: q' ->
        ha.eq.reflexivity b;
        mul_congruence a b zero b;
        left_absorption b;
        ha.eq.transitivity (a * b) (zero * b) zero;
        scalar_mul_zero_coefficient a q'

let cons_all_zero (#t:Type) {| h: has_zero t |} (a: t) (p: polynomial t)
  : Lemma (requires a = zero /\ all_zero p) (ensures all_zero (a :: p))
  = ()

let rec poly_add_preserves_all_zero
  (#t:Type) {| m: add_monoid t |} (p q: polynomial t)
  : Lemma (requires all_zero #t #m.has_zero p /\ all_zero #t #m.has_zero q)
          (ensures all_zero #t #m.has_zero (poly_add p q))
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _ -> ()
    | _ :: _, [] -> ()
    | a :: p', b :: q' ->
        h_axb_eq_zero a b;
        poly_add_preserves_all_zero p' q'

let rec poly_mul_all_zero_left
  (#t:Type) {| r: semiring t |} (p q: polynomial t)
  : Lemma (requires all_zero #t #(semiring_has_zero r) p)
          (ensures all_zero #t #(semiring_has_zero r) (poly_mul p q))
          (decreases L.length p)
  = match p with
    | [] -> ()
    | a :: p' ->
        // a = zero, all_zero p'
        scalar_mul_zero_coefficient a q;
        poly_mul_all_zero_left p' q;
        // poly_mul (a::p') q = poly_add (scalar_mul a q) (zero :: poly_mul p' q)
        // both halves are all_zero, so poly_add is all_zero
        let ha = semiring_has_zero r in
        ha.eq.reflexivity zero;
        poly_add_preserves_all_zero #t #r.add_comm_monoid.add_monoid
          (scalar_mul a q) (zero :: poly_mul p' q)

let rec poly_mul_all_zero_right
  (#t:Type) {| r: semiring t |} (p q: polynomial t)
  : Lemma (requires all_zero #t #(semiring_has_zero r) q)
          (ensures all_zero #t #(semiring_has_zero r) (poly_mul p q))
          (decreases L.length p)
  = let ha = semiring_has_zero r in
    match p with
    | [] -> ()
    | a :: p' ->
        // scalar_mul a q has all_zero (since each coefficient b in q is zero -> a*b = zero by absorption-from-congruence)
        // We don't have a direct lemma; use scalar_mul_right_congruence with q ≡ [] giving scalar_mul a q ≡ []
        scalar_mul_right_congruence a q [];
        // poly_eq (scalar_mul a q) []  -> all_zero (scalar_mul a q)
        // poly_mul p' q by IH is all_zero
        poly_mul_all_zero_right p' q;
        // zero :: poly_mul p' q is all_zero
        ha.eq.reflexivity zero;
        // poly_add of two all_zero is all_zero
        poly_add_preserves_all_zero #t #r.add_comm_monoid.add_monoid
          (scalar_mul a q) (zero :: poly_mul p' q)

let rec poly_mul_left_congruence
  (#t:Type) {| r: semiring t |} (p1 p2 q: polynomial t)
  : Lemma (requires poly_eq #t #(semiring_has_zero r) p1 p2)
          (ensures poly_eq #t #(semiring_has_zero r)
                     (poly_mul p1 q) (poly_mul p2 q))
          (decreases %[L.length p1; L.length p2])
  = let ha = semiring_has_zero r in
    match p1, p2 with
    | [], [] -> ()
    | [], _ :: _ ->
        poly_mul_all_zero_left p2 q
    | _ :: _, [] ->
        poly_mul_all_zero_left p1 q
    | a1 :: p1', a2 :: p2' ->
        scalar_mul_left_congruence a1 a2 q;
        poly_mul_left_congruence p1' p2' q;
        ha.eq.reflexivity zero;
        // poly_eq (zero :: poly_mul p1' q) (zero :: poly_mul p2' q)
        // (zero = zero) && poly_eq (poly_mul p1' q) (poly_mul p2' q)  -- both true
        poly_add_congruence #t #r.add_comm_monoid.add_monoid
          (scalar_mul a1 q) (zero :: poly_mul p1' q)
          (scalar_mul a2 q) (zero :: poly_mul p2' q)

let rec poly_mul_right_congruence
  (#t:Type) {| r: semiring t |} (p q1 q2: polynomial t)
  : Lemma (requires poly_eq #t #(semiring_has_zero r) q1 q2)
          (ensures poly_eq #t #(semiring_has_zero r)
                     (poly_mul p q1) (poly_mul p q2))
          (decreases L.length p)
  = let ha = semiring_has_zero r in
    match p with
    | [] -> ()
    | a :: p' ->
        scalar_mul_right_congruence a q1 q2;
        poly_mul_right_congruence p' q1 q2;
        ha.eq.reflexivity zero;
        poly_add_congruence #t #r.add_comm_monoid.add_monoid
          (scalar_mul a q1) (zero :: poly_mul p' q1)
          (scalar_mul a q2) (zero :: poly_mul p' q2)

let poly_mul_congruence
  (#t:Type) {| r: semiring t |} (p1 q1 p2 q2: polynomial t)
  : Lemma (requires poly_eq #t #(semiring_has_zero r) p1 p2 /\
                    poly_eq #t #(semiring_has_zero r) q1 q2)
          (ensures poly_eq #t #(semiring_has_zero r)
                     (poly_mul p1 q1) (poly_mul p2 q2))
  = poly_mul_left_congruence p1 p2 q1;
    poly_mul_right_congruence p2 q1 q2;
    poly_eq_transitivity #t #(semiring_has_zero r)
      (poly_mul p1 q1) (poly_mul p2 q1) (poly_mul p2 q2)

let cons_zero_poly_add
  (#t:Type) {| m: add_monoid t |} (x y: polynomial t)
  : Lemma (poly_eq #t #m.has_zero
            (zero :: poly_add x y)
            (poly_add (zero :: x) (zero :: y)))
  = m.has_zero.eq.reflexivity zero;
    h_axb_eq_zero #t #m zero zero;
    m.has_zero.eq.symmetry (zero + zero) zero;
    poly_eq_reflexivity #t #m.has_zero (poly_add x y)

let poly_add_4_rearrange
  (#t:Type) {| m: add_comm_monoid t |} (a b c d: polynomial t)
  : Lemma (poly_eq #t #m.add_monoid.has_zero
            (poly_add (poly_add a b) (poly_add c d))
            (poly_add (poly_add a c) (poly_add b d)))
  = let ha = m.add_monoid.has_zero in
    poly_eq_reflexivity #t #ha a;
    poly_eq_reflexivity #t #ha d;
    let s  = poly_add (poly_add a b) (poly_add c d) in
    let t1 = poly_add a (poly_add b (poly_add c d)) in
    let t2 = poly_add a (poly_add (poly_add b c) d) in
    let t3 = poly_add a (poly_add (poly_add c b) d) in
    let t4 = poly_add a (poly_add c (poly_add b d)) in
    let e  = poly_add (poly_add a c) (poly_add b d) in
    // s = t1
    poly_add_associative #t #m.add_monoid a b (poly_add c d);
    // t1 = t2
    poly_add_associative #t #m.add_monoid b c d;
    poly_eq_symmetry #t #ha (poly_add (poly_add b c) d) (poly_add b (poly_add c d));
    poly_add_congruence #t #m.add_monoid
      a (poly_add b (poly_add c d)) a (poly_add (poly_add b c) d);
    // t2 = t3
    poly_add_commutative #t #m b c;
    poly_add_congruence #t #m.add_monoid (poly_add b c) d (poly_add c b) d;
    poly_add_congruence #t #m.add_monoid
      a (poly_add (poly_add b c) d) a (poly_add (poly_add c b) d);
    // t3 = t4
    poly_add_associative #t #m.add_monoid c b d;
    poly_add_congruence #t #m.add_monoid
      a (poly_add (poly_add c b) d) a (poly_add c (poly_add b d));
    // t4 = e   (reverse of associativity)
    poly_add_associative #t #m.add_monoid a c (poly_add b d);
    poly_eq_symmetry #t #ha e t4;
    // chain
    poly_eq_transitivity #t #ha s t1 t2;
    poly_eq_transitivity #t #ha s t2 t3;
    poly_eq_transitivity #t #ha s t3 t4;
    poly_eq_transitivity #t #ha s t4 e

let cons_congruence
  (#t:Type) {| h: has_zero t |} (a b: t) (p q: polynomial t)
  : Lemma (requires a = b /\ poly_eq p q) (ensures poly_eq (a :: p) (b :: q))
  = ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
let rec poly_mul_right_distrib
  (#t:Type) {| r: semiring t |} (p q1 q2: polynomial t)
  : Lemma (ensures poly_eq #t #(semiring_has_zero r)
                     (poly_mul p (poly_add q1 q2))
                     (poly_add (poly_mul p q1) (poly_mul p q2)))
          (decreases L.length p)
  = let ha = semiring_has_zero r in
    match p with
    | [] -> ()
    | a :: p' ->
        scalar_mul_distrib_add_right a q1 q2;
        // scalar_mul a (poly_add q1 q2) = poly_add (scalar_mul a q1) (scalar_mul a q2)
        poly_mul_right_distrib p' q1 q2;
        // poly_mul p' (poly_add q1 q2) = poly_add (poly_mul p' q1) (poly_mul p' q2)
        ha.eq.reflexivity zero;
        cons_congruence #t #ha zero zero (poly_mul p' (poly_add q1 q2))
                                          (poly_add (poly_mul p' q1) (poly_mul p' q2));
        // (zero :: poly_mul p' (poly_add q1 q2)) = (zero :: poly_add (poly_mul p' q1) (poly_mul p' q2))
        cons_zero_poly_add #t #r.add_comm_monoid.add_monoid (poly_mul p' q1) (poly_mul p' q2);
        // zero :: poly_add A B = poly_add (zero :: A) (zero :: B)
        poly_eq_transitivity #t #ha
          (zero :: poly_mul p' (poly_add q1 q2))
          (zero :: poly_add (poly_mul p' q1) (poly_mul p' q2))
          (poly_add (zero :: poly_mul p' q1) (zero :: poly_mul p' q2));
        // Now LHS expansion of poly_mul (a::p') (poly_add q1 q2):
        // = poly_add (scalar_mul a (poly_add q1 q2)) (zero :: poly_mul p' (poly_add q1 q2))
        // ≡ poly_add (poly_add (scalar_mul a q1) (scalar_mul a q2))
        //            (poly_add (zero :: poly_mul p' q1) (zero :: poly_mul p' q2))
        poly_add_congruence #t #r.add_comm_monoid.add_monoid
          (scalar_mul a (poly_add q1 q2))
          (zero :: poly_mul p' (poly_add q1 q2))
          (poly_add (scalar_mul a q1) (scalar_mul a q2))
          (poly_add (zero :: poly_mul p' q1) (zero :: poly_mul p' q2));
        // Now use 4-rearrange to bring to RHS shape.
        poly_add_4_rearrange #t #r.add_comm_monoid
          (scalar_mul a q1) (scalar_mul a q2)
          (zero :: poly_mul p' q1) (zero :: poly_mul p' q2);
        // (sa1 + sa2) + (zp1 + zp2) = (sa1 + zp1) + (sa2 + zp2) — wait we need
        // ((sa1+sa2)+(zp1+zp2)) = ((sa1+zp1)+(sa2+zp2))
        poly_eq_transitivity #t #ha
          (poly_mul (a :: p') (poly_add q1 q2))
          (poly_add (poly_add (scalar_mul a q1) (scalar_mul a q2))
                    (poly_add (zero :: poly_mul p' q1) (zero :: poly_mul p' q2)))
          (poly_add (poly_add (scalar_mul a q1) (zero :: poly_mul p' q1))
                    (poly_add (scalar_mul a q2) (zero :: poly_mul p' q2)))
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
let rec poly_mul_left_distrib
  (#t:Type) {| r: semiring t |} (p1 p2 q: polynomial t)
  : Lemma (ensures poly_eq #t #(semiring_has_zero r)
                     (poly_mul (poly_add p1 p2) q)
                     (poly_add (poly_mul p1 q) (poly_mul p2 q)))
          (decreases %[L.length p1; L.length p2])
  = let ha = semiring_has_zero r in
    match p1, p2 with
    | [], _ -> poly_eq_reflexivity #t #ha (poly_mul p2 q)
    | _ :: _, [] -> poly_eq_reflexivity #t #ha (poly_mul p1 q)
    | a :: p1', b :: p2' ->
        scalar_mul_distrib_add_left a b q;
        poly_mul_left_distrib p1' p2' q;
        ha.eq.reflexivity zero;
        cons_congruence #t #ha zero zero
          (poly_mul (poly_add p1' p2') q)
          (poly_add (poly_mul p1' q) (poly_mul p2' q));
        cons_zero_poly_add #t #r.add_comm_monoid.add_monoid (poly_mul p1' q) (poly_mul p2' q);
        poly_eq_transitivity #t #ha
          (zero :: poly_mul (poly_add p1' p2') q)
          (zero :: poly_add (poly_mul p1' q) (poly_mul p2' q))
          (poly_add (zero :: poly_mul p1' q) (zero :: poly_mul p2' q));
        poly_add_congruence #t #r.add_comm_monoid.add_monoid
          (scalar_mul (a + b) q)
          (zero :: poly_mul (poly_add p1' p2') q)
          (poly_add (scalar_mul a q) (scalar_mul b q))
          (poly_add (zero :: poly_mul p1' q) (zero :: poly_mul p2' q));
        poly_add_4_rearrange #t #r.add_comm_monoid
          (scalar_mul a q) (scalar_mul b q)
          (zero :: poly_mul p1' q) (zero :: poly_mul p2' q);
        poly_eq_transitivity #t #ha
          (poly_mul (poly_add p1 p2) q)
          (poly_add (poly_add (scalar_mul a q) (scalar_mul b q))
                    (poly_add (zero :: poly_mul p1' q) (zero :: poly_mul p2' q)))
          (poly_add (poly_add (scalar_mul a q) (zero :: poly_mul p1' q))
                    (poly_add (scalar_mul b q) (zero :: poly_mul p2' q)))
#pop-options

let rec scalar_mul_one
  (#t:Type) {| r: semiring t |} (q: polynomial t)
  : Lemma (ensures poly_eq #t #(semiring_has_zero r) (scalar_mul one q) q)
          (decreases L.length q)
  = match q with
    | [] -> ()
    | b :: q' ->
        left_mul_identity b;
        scalar_mul_one q'

let scalar_mul_zero_left_const
  (#t:Type) {| r: semiring t |} (q: polynomial t)
  : Lemma (all_zero #t #(semiring_has_zero r) (scalar_mul zero q))
  = (semiring_has_zero r).eq.reflexivity zero;
    scalar_mul_zero_coefficient zero q

let poly_mul_one_left
  (#t:Type) {| r: semiring t |} (q: polynomial t)
  : Lemma (poly_eq #t #(semiring_has_zero r) (poly_mul [one] q) q)
  = let ha = semiring_has_zero r in
    scalar_mul_one q;
    // poly_mul [one] q = poly_add (scalar_mul one q) (zero :: [])
    // [zero] is all_zero, so poly_add X [zero] ≡ X
    ha.eq.reflexivity zero;
    poly_add_right_all_zero #t #r.add_comm_monoid.add_monoid (scalar_mul one q) [zero];
    // poly_add (scalar_mul one q) [zero] ≡ scalar_mul one q
    poly_eq_transitivity #t #ha
      (poly_mul [one] q)
      (scalar_mul one q)
      q

let rec poly_mul_one_right
  (#t:Type) {| r: semiring t |} (q: polynomial t)
  : Lemma (ensures poly_eq #t #(semiring_has_zero r) (poly_mul q [one]) q)
          (decreases L.length q)
  = let ha = semiring_has_zero r in
    match q with
    | [] -> ()
    | a :: q' ->
        // poly_mul (a::q') [one] = poly_add [a*one] (zero :: poly_mul q' [one])
        //                        = (a*one + zero) :: poly_mul q' [one]
        right_mul_identity a;
        // a*one = a
        ha.eq.reflexivity zero;
        h_x_plus_zero_eq_x (a * one) zero;
        // (a*one) + zero = (a*one)
        ha.eq.transitivity ((a * one) + zero) (a * one) a;
        poly_mul_one_right q'

let scalar_mul_cons_zero
  (#t:Type) {| r: semiring t |} (a: t) (p: polynomial t)
  : Lemma (poly_eq #t #(semiring_has_zero r)
            (scalar_mul a (zero :: p))
            (zero :: scalar_mul a p))
  = let ha = semiring_has_zero r in
    right_absorption a;
    // a * zero = zero
    poly_eq_reflexivity #t #ha (scalar_mul a p)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
let rec scalar_mul_poly_mul
  (#t:Type) {| r: semiring t |} (a: t) (q s: polynomial t)
  : Lemma (ensures poly_eq #t #(semiring_has_zero r)
                     (poly_mul (scalar_mul a q) s)
                     (scalar_mul a (poly_mul q s)))
          (decreases L.length q)
  = let ha = semiring_has_zero r in
    match q with
    | [] -> ()
    | b :: q' ->
        // LHS  = poly_mul ((a*b) :: scalar_mul a q') s
        //      = poly_add (scalar_mul (a*b) s) (zero :: poly_mul (scalar_mul a q') s)
        // RHS  = scalar_mul a (poly_mul (b::q') s)
        //      = scalar_mul a (poly_add (scalar_mul b s) (zero :: poly_mul q' s))
        scalar_mul_distrib_add_right a (scalar_mul b s) (zero :: poly_mul q' s);
        // RHS ≡ poly_add (scalar_mul a (scalar_mul b s)) (scalar_mul a (zero :: poly_mul q' s))
        scalar_mul_assoc a b s;
        // scalar_mul (a*b) s ≡ scalar_mul a (scalar_mul b s)
        scalar_mul_poly_mul a q' s;
        // poly_mul (scalar_mul a q') s ≡ scalar_mul a (poly_mul q' s)
        ha.eq.reflexivity zero;
        cons_congruence #t #ha zero zero
          (poly_mul (scalar_mul a q') s) (scalar_mul a (poly_mul q' s));
        // zero :: poly_mul (scalar_mul a q') s ≡ zero :: scalar_mul a (poly_mul q' s)
        scalar_mul_cons_zero a (poly_mul q' s);
        // scalar_mul a (zero :: poly_mul q' s) ≡ zero :: scalar_mul a (poly_mul q' s)
        poly_eq_symmetry #t #ha
          (scalar_mul a (zero :: poly_mul q' s))
          (zero :: scalar_mul a (poly_mul q' s));
        poly_eq_transitivity #t #ha
          (zero :: poly_mul (scalar_mul a q') s)
          (zero :: scalar_mul a (poly_mul q' s))
          (scalar_mul a (zero :: poly_mul q' s));
        // (zero :: poly_mul (scalar_mul a q') s) ≡ scalar_mul a (zero :: poly_mul q' s)
        poly_add_congruence #t #r.add_comm_monoid.add_monoid
          (scalar_mul (a * b) s) (zero :: poly_mul (scalar_mul a q') s)
          (scalar_mul a (scalar_mul b s)) (scalar_mul a (zero :: poly_mul q' s));
        // LHS ≡ poly_add (scalar_mul a (scalar_mul b s)) (scalar_mul a (zero :: poly_mul q' s))
        poly_eq_symmetry #t #ha
          (scalar_mul a (poly_add (scalar_mul b s) (zero :: poly_mul q' s)))
          (poly_add (scalar_mul a (scalar_mul b s)) (scalar_mul a (zero :: poly_mul q' s)));
        poly_eq_transitivity #t #ha
          (poly_mul (scalar_mul a q) s)
          (poly_add (scalar_mul a (scalar_mul b s)) (scalar_mul a (zero :: poly_mul q' s)))
          (scalar_mul a (poly_add (scalar_mul b s) (zero :: poly_mul q' s)))
#pop-options

let poly_mul_cons_zero
  (#t:Type) {| r: semiring t |} (x s: polynomial t)
  : Lemma (poly_eq #t #(semiring_has_zero r)
            (poly_mul (zero :: x) s)
            (zero :: poly_mul x s))
  = scalar_mul_zero_left_const s;
    (semiring_has_zero r).eq.reflexivity zero;
    poly_add_left_all_zero #t #r.add_comm_monoid.add_monoid
      (scalar_mul zero s) (zero :: poly_mul x s)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
let rec poly_mul_associative
  (#t:Type) {| r: semiring t |} (p q s: polynomial t)
  : Lemma (ensures poly_eq #t #(semiring_has_zero r)
                     (poly_mul (poly_mul p q) s)
                     (poly_mul p (poly_mul q s)))
          (decreases L.length p)
  = let ha = semiring_has_zero r in
    match p with
    | [] -> ()
    | a :: p' ->
        // LHS = poly_mul (poly_add (scalar_mul a q) (zero :: poly_mul p' q)) s
        poly_mul_left_distrib (scalar_mul a q) (zero :: poly_mul p' q) s;
        // LHS ≡ poly_add (poly_mul (scalar_mul a q) s) (poly_mul (zero :: poly_mul p' q) s)
        scalar_mul_poly_mul a q s;
        // poly_mul (scalar_mul a q) s ≡ scalar_mul a (poly_mul q s)
        poly_mul_cons_zero (poly_mul p' q) s;
        // poly_mul (zero :: poly_mul p' q) s ≡ zero :: poly_mul (poly_mul p' q) s
        poly_mul_associative p' q s;
        // poly_mul (poly_mul p' q) s ≡ poly_mul p' (poly_mul q s)
        ha.eq.reflexivity zero;
        cons_congruence #t #ha zero zero
          (poly_mul (poly_mul p' q) s) (poly_mul p' (poly_mul q s));
        // zero :: poly_mul (poly_mul p' q) s ≡ zero :: poly_mul p' (poly_mul q s)
        poly_eq_transitivity #t #ha
          (poly_mul (zero :: poly_mul p' q) s)
          (zero :: poly_mul (poly_mul p' q) s)
          (zero :: poly_mul p' (poly_mul q s));
        // poly_mul (zero :: poly_mul p' q) s ≡ zero :: poly_mul p' (poly_mul q s)
        poly_add_congruence #t #r.add_comm_monoid.add_monoid
          (poly_mul (scalar_mul a q) s) (poly_mul (zero :: poly_mul p' q) s)
          (scalar_mul a (poly_mul q s)) (zero :: poly_mul p' (poly_mul q s));
        // intermediate ≡ poly_add (scalar_mul a (poly_mul q s)) (zero :: poly_mul p' (poly_mul q s))
        // That's exactly poly_mul (a::p') (poly_mul q s) = RHS
        poly_eq_transitivity #t #ha
          (poly_mul (poly_mul p q) s)
          (poly_add (poly_mul (scalar_mul a q) s) (poly_mul (zero :: poly_mul p' q) s))
          (poly_add (scalar_mul a (poly_mul q s)) (zero :: poly_mul p' (poly_mul q s)))
#pop-options

let poly_mul_zero_left
  (#t:Type) {| r: semiring t |} (q: polynomial t)
  : Lemma (poly_eq #t #(semiring_has_zero r) (poly_mul (poly_zero #t) q) (poly_zero #t))
  = poly_eq_reflexivity #t #(semiring_has_zero r) []

let poly_mul_zero_right
  (#t:Type) {| r: semiring t |} (q: polynomial t)
  : Lemma (poly_eq #t #(semiring_has_zero r) (poly_mul q (poly_zero #t)) (poly_zero #t))
  = poly_mul_all_zero_right q []

(* ------------------------------------------------------------------------ *)
(*  Multiplicative + semiring/ring instances                                *)
(* ------------------------------------------------------------------------ *)

instance polynomial_has_one (#t:Type) {| r: semiring t |}
  : has_one (polynomial t)
  = {
      eq = polynomial_equatable #t #(semiring_has_zero r);
      one = poly_one;
    }

instance polynomial_has_mul (#t:Type) {| r: semiring t |}
  : has_mul (polynomial t)
  = {
      ( * ) = poly_mul;
      eq = polynomial_equatable #t #(semiring_has_zero r);
      congruence = (fun p1 q1 p2 q2 -> poly_mul_congruence p1 q1 p2 q2);
    }

instance polynomial_mul_semigroup (#t:Type) {| r: semiring t |}
  : mul_semigroup (polynomial t)
  = {
      has_mul = polynomial_has_mul #t #r;
      associativity = (fun p q s -> poly_mul_associative p q s);
    }

instance polynomial_mul_monoid (#t:Type) {| r: semiring t |}
  : mul_monoid (polynomial t)
  = {
      has_one = polynomial_has_one #t #r;
      mul_semigroup = polynomial_mul_semigroup #t #r;
      left_mul_identity  = (fun q -> poly_mul_one_left q);
      right_mul_identity = (fun q -> poly_mul_one_right q);
    }

instance polynomial_semiring (#t:Type) {| r: semiring t |}
  : semiring (polynomial t)
  = {
      add_comm_monoid = polynomial_add_comm_monoid #t #r.add_comm_monoid;
      mul_monoid = polynomial_mul_monoid #t #r;
      left_absorption  = (fun q -> poly_mul_zero_left q);
      right_absorption = (fun q -> poly_mul_zero_right q);
      left_distributivity  = (fun p q1 q2 -> poly_mul_right_distrib p q1 q2);
      right_distributivity = (fun p1 p2 q -> poly_mul_left_distrib p1 p2 q);
    }

instance polynomial_ring (#t:Type) {| r: ring t |}
  : ring (polynomial t)
  = {
      semiring = polynomial_semiring #t #r.semiring;
      add_comm_group = polynomial_add_comm_group #t #r.add_comm_group;
    }
