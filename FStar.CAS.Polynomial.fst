module FStar.CAS.Polynomial

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

open FStar.CAS.Equatable
open FStar.CAS.Grouplikes
open FStar.CAS.Ringlikes

(* ------------------------------------------------------------------------ *)
(*  Representation                                                          *)
(* ------------------------------------------------------------------------ *)

let coeff (#t:Type) {| h: has_zero t |} (p: polynomial t) (i: nat) : t =
  if i < L.length p then L.index p i else zero

let poly_zero (#t:Type) : polynomial t = []

let poly_one (#t:Type) {| h: has_one t |} : polynomial t = [one]

let poly_one_def (#t:Type) {| h: has_one t |} (u: unit)
  : Lemma (poly_one #t == [one]) = ()

let poly_zero_def (#t:Type) (u: unit)
  : Lemma (poly_zero #t == ([] <: polynomial t)) = ()

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

let poly_add_sub_cancel
  (#t:Type) {| g: add_comm_group t |} (t_poly p: polynomial t)
  : Lemma (poly_eq #t #g.add_group.add_monoid.has_zero
             (poly_add t_poly (poly_sub p t_poly)) p)
  = let hz = g.add_group.add_monoid.has_zero in
    let m = g.add_group.add_monoid in
    let cm = g.add_comm_monoid in
    poly_add_commutative #t #cm p (poly_neg t_poly);
    poly_eq_reflexivity #t #hz t_poly;
    poly_add_congruence #t #m t_poly (poly_add p (poly_neg t_poly))
                                     t_poly (poly_add (poly_neg t_poly) p);
    poly_add_associative #t #m t_poly (poly_neg t_poly) p;
    poly_eq_symmetry #t #hz
      (poly_add (poly_add t_poly (poly_neg t_poly)) p)
      (poly_add t_poly (poly_add (poly_neg t_poly) p));
    poly_neg_inversion t_poly;
    poly_eq_reflexivity #t #hz p;
    poly_add_congruence #t #m (poly_add t_poly (poly_neg t_poly)) p poly_zero p;
    poly_add_left_identity #t #m p;
    poly_eq_transitivity #t #hz
      (poly_add t_poly (poly_sub p t_poly))
      (poly_add t_poly (poly_add (poly_neg t_poly) p))
      (poly_add (poly_add t_poly (poly_neg t_poly)) p);
    poly_eq_transitivity #t #hz
      (poly_add t_poly (poly_sub p t_poly))
      (poly_add (poly_add t_poly (poly_neg t_poly)) p)
      (poly_add poly_zero p);
    poly_eq_transitivity #t #hz
      (poly_add t_poly (poly_sub p t_poly))
      (poly_add poly_zero p)
      p

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

let semiring_has_zero_unfold (#t:Type) (r: semiring t)
  : Lemma (ensures semiring_has_zero r == r.add_comm_monoid.add_monoid.has_zero)
  = ()

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

let poly_mul_singleton
  (#t:Type) {| r: semiring t |} (c: t) (q: polynomial t)
  : Lemma (poly_eq #t #(semiring_has_zero r) (poly_mul [c] q) (scalar_mul c q))
  = let ha = semiring_has_zero r in
    ha.eq.reflexivity zero;
    poly_add_right_all_zero #t #r.add_comm_monoid.add_monoid (scalar_mul c q) [zero]

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

(* ------------------------------------------------------------------------ *)
(*  Canonical form (poly_normalize), degree, leading coefficient            *)
(* ------------------------------------------------------------------------ *)

let rec drop_leading_zeros (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Tot (polynomial t) (decreases L.length p)
  = match p with
    | [] -> []
    | a :: tl -> if a = zero then drop_leading_zeros tl else p

let poly_normalize (#t:Type) {| h: has_zero t |} (p: polynomial t) : polynomial t
  = L.rev (drop_leading_zeros (L.rev p))

let rec drop_leading_zeros_no_lead_zero
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (ensures (let q = drop_leading_zeros p in
                    L.length q = 0 \/ ~ (L.index q 0 = zero)))
          (decreases L.length p)
  = match p with
    | [] -> ()
    | a :: tl ->
      if a = zero then drop_leading_zeros_no_lead_zero tl
      else ()

let rec index_append_lemma (#a:Type) (l1 l2: list a) (i: nat)
  : Lemma (requires i < L.length l1 + L.length l2)
          (ensures (L.append_length l1 l2;
                    (if i < L.length l1
                     then L.index (L.append l1 l2) i == L.index l1 i
                     else L.index (L.append l1 l2) i == L.index l2 (Prims.op_Subtraction i (L.length l1)))))
          (decreases l1)
  = L.append_length l1 l2;
    match l1 with
    | [] -> ()
    | _ :: tl ->
      L.append_length tl l2;
      if i = 0 then ()
      else index_append_lemma tl l2 (Prims.op_Subtraction i 1)

let rev_index_last (#a:Type) (l: list a)
  : Lemma (requires Cons? l)
          (ensures (L.rev_length l;
                    L.index (L.rev l) (Prims.op_Subtraction (L.length l) 1) == L.hd l))
  = L.rev_length l;
    match l with
    | hd :: tl ->
      L.rev_rev' l;
      L.rev_rev' tl;
      let rtl = L.rev tl in
      L.rev_length tl;
      L.append_length rtl [hd];
      index_append_lemma rtl [hd] (L.length tl)

let poly_normalize_no_trailing_zero
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (ensures (let np = poly_normalize p in
                    L.length np = 0 \/
                    ~ (L.index np (Prims.op_Subtraction (L.length np) 1) = zero)))
  = let pr = L.rev p in
    let q = drop_leading_zeros pr in
    drop_leading_zeros_no_lead_zero pr;
    let np = L.rev q in
    L.rev_length q;
    if L.length q = 0 then ()
    else rev_index_last q

let rec drop_leading_zeros_all_zero_is_empty
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (requires all_zero p)
          (ensures L.length (drop_leading_zeros p) = 0)
          (decreases L.length p)
  = match p with
    | [] -> ()
    | a :: tl -> drop_leading_zeros_all_zero_is_empty tl

let rec all_zero_append
  (#t:Type) {| h: has_zero t |} (p q: polynomial t)
  : Lemma (ensures all_zero (L.append p q) <==> (all_zero p /\ all_zero q))
          (decreases L.length p)
  = match p with
    | [] -> ()
    | _ :: tl -> all_zero_append tl q

let rec rev_all_zero
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (requires all_zero p)
          (ensures all_zero (L.rev p))
          (decreases L.length p)
  = match p with
    | [] -> ()
    | a :: tl ->
      rev_all_zero tl;
      L.rev_rev' p;
      // L.rev (a :: tl) = L.append (L.rev tl) [a]
      L.rev_append [a] tl;
      // Need: all_zero (L.rev tl @ [a])
      all_zero_append (L.rev tl) [a]

let poly_normalize_all_zero_is_empty
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (requires all_zero p)
          (ensures L.length (poly_normalize p) = 0)
  = rev_all_zero p;
    drop_leading_zeros_all_zero_is_empty (L.rev p);
    L.rev_length (drop_leading_zeros (L.rev p))

let rec leading_zeros_prefix (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Tot (polynomial t) (decreases L.length p)
  = match p with
    | [] -> []
    | a :: tl -> if a = zero then a :: leading_zeros_prefix tl else []

let rec leading_zeros_prefix_lemma
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (ensures all_zero (leading_zeros_prefix p) /\
                   p == L.append (leading_zeros_prefix p) (drop_leading_zeros p))
          (decreases L.length p)
  = match p with
    | [] -> ()
    | a :: tl ->
      if a = zero then leading_zeros_prefix_lemma tl
      else ()

let rec poly_eq_append_all_zero_right
  (#t:Type) {| h: has_zero t |} (p z: polynomial t)
  : Lemma (requires all_zero z)
          (ensures poly_eq (L.append p z) p)
          (decreases L.length p)
  = match p with
    | [] -> ()
    | a :: tl ->
      h.eq.reflexivity a;
      poly_eq_append_all_zero_right tl z

let poly_eq_self_normalize
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (ensures poly_eq p (poly_normalize p))
  = let pr = L.rev p in
    let zs = leading_zeros_prefix pr in
    let q = drop_leading_zeros pr in
    leading_zeros_prefix_lemma pr;
    // pr == zs @ q
    L.rev_append zs q;
    // L.rev pr == L.rev q @ L.rev zs
    L.rev_involutive p;
    // p == L.rev pr
    rev_all_zero zs;
    // all_zero (L.rev zs)
    poly_eq_append_all_zero_right (L.rev q) (L.rev zs)
    // poly_eq (L.rev q @ L.rev zs) (L.rev q)  i.e. poly_eq p (poly_normalize p)

let degree (#t:Type) {| h: has_zero t |} (p: polynomial t) : option nat
  = let np = poly_normalize p in
    if L.length np = 0 then None
    else Some (Prims.op_Subtraction (L.length np) 1)

let leading_coefficient (#t:Type) {| h: has_zero t |} (p: polynomial t) : t
  = let np = poly_normalize p in
    if L.length np = 0 then zero
    else L.index np (Prims.op_Subtraction (L.length np) 1)

(* ------------------------------------------------------------------------ *)
(*  Evaluation                                                              *)
(* ------------------------------------------------------------------------ *)

let rec eval (#t:Type) {| r: semiring t |} (p: polynomial t) (x: t)
  : Tot t (decreases L.length p)
  = match p with
    | [] -> zero
    | a :: p' -> a + x * eval p' x

let rec eval_all_zero (#t:Type) {| r: semiring t |} (p: polynomial t) (x: t)
  : Lemma (requires all_zero #t #(semiring_has_zero r) p)
          (ensures eval p x = zero)
          (decreases L.length p)
  = let ha = semiring_has_zero r in
    match p with
    | [] -> ha.eq.reflexivity zero
    | a :: p' ->
      eval_all_zero p' x;
      // eval p x = a + x * eval p' x; want = zero
      // From IH: eval p' x = zero. Then x * eval p' x = x * zero = zero (right_absorption).
      r.right_absorption x;
      ha.eq.reflexivity x;
      r.mul_monoid.mul_semigroup.has_mul.congruence x (eval p' x) x zero;
      // now x * eval p' x = x * zero = zero
      ha.eq.transitivity (x * eval p' x) (x * zero) zero;
      // a = zero (from all_zero) and x * eval p' x = zero, so a + (x * eval p' x) = zero + zero = zero
      ha.eq.reflexivity zero;
      r.add_comm_monoid.add_monoid.add_semigroup.has_add.congruence a (x * eval p' x) zero zero;
      r.add_comm_monoid.add_monoid.left_add_identity zero;
      ha.eq.transitivity (a + x * eval p' x) (zero + zero) zero

let rec eval_well_defined (#t:Type) {| r: semiring t |} (p q: polynomial t) (x: t)
  : Lemma (requires poly_eq #t #(semiring_has_zero r) p q)
          (ensures eval p x = eval q x)
          (decreases %[L.length p; L.length q])
  = let ha = semiring_has_zero r in
    match p, q with
    | [], [] -> ha.eq.reflexivity zero
    | [], b :: q' ->
      // all_zero (b :: q'), so b = zero and all_zero q'
      eval_all_zero q x;
      // eval q x = zero, eval p x = zero
      ha.eq.symmetry (eval q x) zero
    | _ :: _, [] ->
      eval_all_zero p x;
      ha.eq.reflexivity zero;
      // eval p x = zero, eval q x = zero
      ()
    | a :: p', b :: q' ->
      eval_well_defined p' q' x;
      // a = b and eval p' x = eval q' x
      ha.eq.reflexivity x;
      r.mul_monoid.mul_semigroup.has_mul.congruence x (eval p' x) x (eval q' x);
      // x * eval p' x = x * eval q' x
      r.add_comm_monoid.add_monoid.add_semigroup.has_add.congruence
        a (x * eval p' x) b (x * eval q' x)
      // (a + x * eval p' x) = (b + x * eval q' x)

let eval_poly_zero (#t:Type) {| r: semiring t |} (x: t)
  : Lemma (eval #t #r poly_zero x = zero)
  = (semiring_has_zero r).eq.reflexivity zero

let eval_poly_one (#t:Type) {| r: semiring t |} (x: t)
  : Lemma (eval #t #r poly_one x = one)
  = let ha = semiring_has_zero r in
    // eval [one] x = one + x * eval [] x = one + x * zero
    // x * zero = zero (right_absorption); one + zero = one (right_add_identity)
    r.right_absorption x;
    ha.eq.reflexivity one;
    r.add_comm_monoid.add_monoid.add_semigroup.has_add.congruence one (x * zero) one zero;
    r.add_comm_monoid.add_monoid.right_add_identity one;
    ha.eq.transitivity (one + x * zero) (one + zero) one

(* ------------------------------------------------------------------------ *)
(*  Commutative ring instances (stubs)                                      *)
(* ------------------------------------------------------------------------ *)

(* Add-comm-monoid helper: rearrange X + (Y + W) = Y + (X + W). *)
let poly_add_swap_middle
  (#t:Type) {| m: add_comm_monoid t |} (x y w: polynomial t)
  : Lemma (poly_eq #t #m.add_monoid.has_zero
            (poly_add x (poly_add y w)) (poly_add y (poly_add x w)))
  = let ha : has_zero t = m.add_monoid.has_zero in
    // X + (Y + W) ≈ (X + Y) + W                  (assoc reversed)
    poly_add_associative x y w;
    poly_eq_symmetry (poly_add x (poly_add y w)) (poly_add (poly_add x y) w);
    // X + Y ≈ Y + X
    poly_add_commutative x y;
    // (X + Y) + W ≈ (Y + X) + W   by congruence
    poly_eq_reflexivity w;
    poly_add_congruence (poly_add x y) w (poly_add y x) w;
    // (Y + X) + W ≈ Y + (X + W)
    poly_add_associative y x w;
    // Chain: X + (Y + W) ≈ (X+Y)+W ≈ (Y+X)+W ≈ Y + (X+W)
    poly_eq_transitivity
      (poly_add x (poly_add y w))
      (poly_add (poly_add x y) w)
      (poly_add (poly_add y x) w);
    poly_eq_transitivity
      (poly_add x (poly_add y w))
      (poly_add (poly_add y x) w)
      (poly_add y (poly_add x w))

(* Right-recursive decomposition of poly_mul over a commutative_ring.
   poly_mul p (a :: q') = scalar_mul a p + (zero :: poly_mul p q')  modulo poly_eq. *)
let rec poly_mul_right_decomp
  (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t) (a: t) (q': polynomial t)
  : Lemma (ensures poly_eq #t #(semiring_has_zero cr.ring.semiring)
            (poly_mul p (a :: q'))
            (poly_add (scalar_mul a p) (zero :: poly_mul p q')))
          (decreases L.length p)
  = let r : semiring t = cr.ring.semiring in
    let ha : has_zero t = semiring_has_zero r in
    let ham : add_comm_monoid t = r.add_comm_monoid in
    match p with
    | [] ->
      // LHS = []; RHS = poly_add [] [zero] = [zero]; all_zero [zero] => poly_eq.
      ha.eq.reflexivity zero
    | c :: p' ->
      poly_mul_right_decomp p' a q';
      // IH: poly_eq (poly_mul p' (a::q')) (poly_add (scalar_mul a p') (zero :: poly_mul p' q'))
      let x  : polynomial t = scalar_mul c q' in
      let y  : polynomial t = scalar_mul a p' in
      let z  : polynomial t = poly_mul p' q' in
      let w  : polynomial t = zero :: z in
      let m1 : polynomial t = poly_mul p' (a :: q') in
      let m2 : polynomial t = poly_add y w in
      // LHS = poly_add (scalar_mul c (a::q')) (zero :: poly_mul p' (a::q'))
      //     = poly_add ((c*a) :: x) (zero :: m1)
      // Lift IH into LHS: replace m1 by m2 inside (zero :: _).
      poly_eq_reflexivity #t #ha (zero :: m1);
      // poly_eq (zero :: m1) (zero :: m2) — via cons of reflexive zero
      ha.eq.reflexivity zero;
      // we use that poly_eq (a::p) (b::q) = (a=b) && poly_eq p q
      assert (poly_eq #t #ha (zero :: m1) (zero :: m2));
      poly_eq_reflexivity #t #ha ((c * a) :: x);
      poly_add_congruence ((c * a) :: x) (zero :: m1) ((c * a) :: x) (zero :: m2);
      // LHS ≈ poly_add ((c*a) :: x) (zero :: m2)
      //     = (c*a + zero) :: poly_add x m2   by def
      // poly_add_swap_middle on x, y, w: x + (y + w) ≈ y + (x + w)
      poly_add_swap_middle #t #ham x y w;
      // poly_eq (poly_add x m2) (poly_add y (poly_add x w))
      // Now use commutativity at the head: c*a = a*c
      cr.mul_comm_monoid.mul_comm_semigroup.mul_comm_magma.mul_commutativity c a;
      ha.eq.reflexivity zero;
      r.add_comm_monoid.add_monoid.add_semigroup.has_add.congruence (c * a) zero (a * c) zero;
      // (c*a + zero) = (a*c + zero)
      // Combined cons-cons: (c*a + zero) :: poly_add x m2 ≈ (a*c + zero) :: poly_add y (poly_add x w)
      let lhs_tail = poly_add x m2 in
      let rhs_tail = poly_add y (poly_add x w) in
      assert (poly_eq #t #ha lhs_tail rhs_tail);
      // Now: poly_add ((c*a) :: x) (zero :: m2) computationally = (c*a + zero) :: poly_add x m2
      // and RHS = poly_add ((a*c) :: y) (zero :: poly_add x w)
      //        = (a*c + zero) :: poly_add y (poly_add x w)
      // Chain LHS ≈ that intermediate ≈ RHS.
      // Stitch via transitivity:
      poly_eq_transitivity #t #ha
        (poly_mul (c :: p') (a :: q'))
        (poly_add ((c * a) :: x) (zero :: m2))
        (poly_add ((a * c) :: y) (zero :: poly_add x w))

let rec poly_mul_commutative
  (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma (ensures poly_eq #t #(semiring_has_zero cr.ring.semiring) (poly_mul p q) (poly_mul q p))
          (decreases L.length p)
  = let r : semiring t = cr.ring.semiring in
    let ha : has_zero t = semiring_has_zero r in
    match p with
    | [] ->
      // poly_mul [] q = []; poly_mul q [] is all_zero by poly_mul_all_zero_right.
      poly_mul_all_zero_right #t #r q []
    | a :: p' ->
      poly_mul_commutative p' q;
      // IH: poly_eq (poly_mul p' q) (poly_mul q p')
      // LHS = poly_mul (a :: p') q = poly_add (scalar_mul a q) (zero :: poly_mul p' q)
      // RHS expanded via poly_mul_right_decomp: poly_mul q (a :: p') ≈ poly_add (scalar_mul a q) (zero :: poly_mul q p')
      poly_mul_right_decomp #t #cr q a p';
      poly_eq_symmetry (poly_mul q (a :: p'))
                       (poly_add (scalar_mul a q) (zero :: poly_mul q p'));
      // Now connect LHS to that:
      // (zero :: poly_mul p' q) ≈ (zero :: poly_mul q p') by IH + cons-zero
      ha.eq.reflexivity zero;
      let lhs_tail = poly_mul p' q in
      let rhs_tail = poly_mul q p' in
      assert (poly_eq #t #ha (zero :: lhs_tail) (zero :: rhs_tail));
      poly_eq_reflexivity #t #ha (scalar_mul a q);
      poly_add_congruence (scalar_mul a q) (zero :: lhs_tail)
                          (scalar_mul a q) (zero :: rhs_tail);
      // poly_mul (a::p') q ≈ poly_add (scalar_mul a q) (zero :: poly_mul q p')
      poly_eq_transitivity #t #ha
        (poly_mul (a :: p') q)
        (poly_add (scalar_mul a q) (zero :: rhs_tail))
        (poly_mul q (a :: p'))

instance polynomial_mul_comm_magma (#t:Type) {| cr: commutative_ring t |}
  : mul_comm_magma (polynomial t)
  = {
      has_mul = polynomial_has_mul #t #cr.ring.semiring;
      mul_commutativity = (fun p q -> poly_mul_commutative #t #cr p q);
    }

instance polynomial_mul_comm_semigroup (#t:Type) {| cr: commutative_ring t |}
  : mul_comm_semigroup (polynomial t)
  = {
      mul_semigroup = polynomial_mul_semigroup #t #cr.ring.semiring;
      mul_comm_magma = polynomial_mul_comm_magma #t #cr;
    }

instance polynomial_mul_comm_monoid (#t:Type) {| cr: commutative_ring t |}
  : mul_comm_monoid (polynomial t)
  = {
      mul_monoid = polynomial_mul_monoid #t #cr.ring.semiring;
      mul_comm_semigroup = polynomial_mul_comm_semigroup #t #cr;
    }

instance polynomial_commutative_ring (#t:Type) {| cr: commutative_ring t |}
  : commutative_ring (polynomial t)
  = {
      ring = polynomial_ring #t #cr.ring;
      mul_comm_monoid = polynomial_mul_comm_monoid #t #cr;
    }

(* ------------------------------------------------------------------------ *)
(*  Zero ≠ one, domain, integral domain instances (stubs)                   *)
(* ------------------------------------------------------------------------ *)

let poly_zero_ne_poly_one (#t:Type) {| z: zero_ne_one_semiring t |}
  : Lemma (~ (poly_eq #t #(semiring_has_zero z.semiring) poly_zero (poly_one #t #z.semiring.mul_monoid.has_one)))
  = let r : semiring t = z.semiring in
    let ha : has_zero t = semiring_has_zero r in
    let one_t : t = r.mul_monoid.has_one.one in
    let zero_t : t = ha.zero in
    // From z refinement: zero_t <> one_t (typeclass <> reduces to not (x=y) over equatable t).
    assert (zero_t <> one_t);
    // poly_eq [] [one_t] = all_zero #t #ha [one_t] = (one_t =_ha zero_t) && true
    // The two equatables (one inside ha, one used by <>) coincide per semiring's coherence axiom.
    ha.eq.symmetry one_t zero_t;
    assert (~ (one_t = zero_t));
    assert (~ (all_zero #t #ha [one_t]));
    assert (~ (poly_eq #t #ha [] [one_t]))

instance polynomial_zero_ne_one_semiring (#t:Type) {| z: zero_ne_one_semiring t |}
  : zero_ne_one_semiring (polynomial t)
  = {
      semiring = (poly_zero_ne_poly_one #t #z; polynomial_semiring #t #z.semiring);
    }

(* ------------------------------------------------------------------------ *)
(*  Length and index helpers for poly_mul_top_coef                          *)
(* ------------------------------------------------------------------------ *)

let rec scalar_mul_length
  (#t:Type) {| r: semiring t |} (a: t) (q: polynomial t)
  : Lemma (ensures L.length (scalar_mul a q) = L.length q)
          (decreases L.length q)
  = match q with
    | [] -> ()
    | _ :: q' -> scalar_mul_length a q'

let rec poly_add_length
  (#t:Type) {| m: add_monoid t |} (p q: polynomial t)
  : Lemma (ensures L.length (poly_add p q) = (if L.length p >= L.length q then L.length p else L.length q))
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _ -> ()
    | _, [] -> ()
    | _ :: p', _ :: q' -> poly_add_length p' q'

let rec poly_mul_length
  (#t:Type) {| r: semiring t |} (p q: polynomial t)
  : Lemma (requires Cons? p /\ Cons? q)
          (ensures L.length (poly_mul p q) = Prims.op_Subtraction (L.length p + L.length q) 1)
          (decreases L.length p)
  = match p with
    | [a] ->
      // poly_mul [a] q = poly_add (scalar_mul a q) [zero]
      scalar_mul_length a q;
      poly_add_length #t #r.add_comm_monoid.add_monoid (scalar_mul a q) [zero]
    | a :: p' ->
      // p' is Cons since L.length p >= 2
      poly_mul_length p' q;
      scalar_mul_length a q;
      // (zero :: poly_mul p' q) has length 1 + (|p'|+|q|-1) = |p'|+|q| = |p|+|q|-1
      poly_add_length #t #r.add_comm_monoid.add_monoid (scalar_mul a q) (zero :: poly_mul p' q)

let rec index_scalar_mul
  (#t:Type) {| r: semiring t |} (a: t) (q: polynomial t) (i: nat)
  : Lemma (requires i < L.length q)
          (ensures (scalar_mul_length a q;
                    L.index (scalar_mul a q) i == a * L.index q i))
          (decreases L.length q)
  = scalar_mul_length a q;
    match q with
    | hd :: tl ->
      if i = 0 then ()
      else index_scalar_mul a tl (Prims.op_Subtraction i 1)

let rec index_poly_add_left_longer
  (#t:Type) {| m: add_monoid t |} (p q: polynomial t) (i: nat)
  : Lemma (requires i < L.length p /\ L.length q <= i)
          (ensures (poly_add_length p q;
                    L.index (poly_add p q) i == L.index p i))
          (decreases %[L.length p; L.length q])
  = poly_add_length p q;
    match p, q with
    | _ :: _, [] -> ()
    | hd_p :: tl_p, hd_q :: tl_q ->
      if i = 0 then () // impossible since L.length q <= i = 0 means q = [], handled above
      else index_poly_add_left_longer tl_p tl_q (Prims.op_Subtraction i 1)

let rec index_poly_add_right_longer
  (#t:Type) {| m: add_monoid t |} (p q: polynomial t) (i: nat)
  : Lemma (requires i < L.length q /\ L.length p <= i)
          (ensures (poly_add_length p q;
                    L.index (poly_add p q) i == L.index q i))
          (decreases %[L.length q; L.length p])
  = poly_add_length p q;
    match p, q with
    | [], _ :: _ -> ()
    | hd_p :: tl_p, hd_q :: tl_q ->
      if i = 0 then ()
      else index_poly_add_right_longer tl_p tl_q (Prims.op_Subtraction i 1)

(* The key lemma: the top coefficient of a product is the product of the top coefficients
   (under the additive identity, when one of the lists has trailing structure). *)
let rec poly_mul_top_coef
  (#t:Type) {| r: semiring t |} (p q: polynomial t)
  : Lemma (requires Cons? p /\ Cons? q)
          (ensures (poly_mul_length p q;
                    L.index (poly_mul p q) (Prims.op_Subtraction (L.length p + L.length q) 2) =
                    (L.index p (Prims.op_Subtraction (L.length p) 1)) *
                    (L.index q (Prims.op_Subtraction (L.length q) 1))))
          (decreases L.length p)
  = let ha : has_zero t = semiring_has_zero r in
    let am : add_comm_monoid t = r.add_comm_monoid in
    poly_mul_length p q;
    match p with
    | [a] ->
      // poly_mul [a] q = poly_add (scalar_mul a q) [zero]
      let lhs : polynomial t = poly_add (scalar_mul a q) [zero] in
      scalar_mul_length a q;
      poly_add_length #t #am.add_monoid (scalar_mul a q) [zero];
      let lq = L.length q in
      let target = Prims.op_Subtraction lq 1 in
      let qhd = L.index q target in
      // Compute the value at `target` index of lhs and compare against a * qhd.
      if lq = 1 then begin
        // both sides are length 1; the head value is a*qhd + zero
        // Compute: poly_add (scalar_mul a [qhd]) [zero] = (a*qhd + zero) :: []
        // We need: a*qhd + zero =_ha a * qhd
        ha.eq.reflexivity (a * qhd);
        am.add_monoid.right_add_identity (a * qhd)
      end else begin
        // scalar_mul a q is longer than [zero]; index target uses left side.
        index_poly_add_left_longer #t #am.add_monoid (scalar_mul a q) [zero] target;
        index_scalar_mul a q target;
        // L.index lhs target == L.index (scalar_mul a q) target == a * qhd
        ha.eq.reflexivity (a * qhd)
      end
    | a :: p' ->
      // p' nonempty (since |p| >= 2)
      let lp = L.length p in
      let lq = L.length q in
      poly_mul_top_coef p' q;
      poly_mul_length p' q;
      scalar_mul_length a q;
      let m : polynomial t = zero :: poly_mul p' q in
      poly_add_length #t #am.add_monoid (scalar_mul a q) m;
      // length m = 1 + (|p'|+|q|-1) = |p'|+|q| = |p|+|q|-1 > |q| = length (scalar_mul a q)
      let target = Prims.op_Subtraction (lp + lq) 2 in
      // target < length m, target >= length (scalar_mul a q)
      assert (target < L.length m);
      assert (L.length (scalar_mul a q) <= target);
      index_poly_add_right_longer #t #am.add_monoid (scalar_mul a q) m target;
      // L.index (poly_add ...) target == L.index m target == L.index (poly_mul p' q) (target-1)
      // target - 1 = |p'|+|q|-2
      let inner_target = Prims.op_Subtraction target 1 in
      assert (inner_target = Prims.op_Subtraction (L.length p' + lq) 2);
      // By IH:
      assert (L.index (poly_mul p' q) inner_target =
              L.index p' (Prims.op_Subtraction (L.length p') 1) *
              L.index q (Prims.op_Subtraction lq 1));
      // L.index p' (|p'|-1) = L.index p (|p|-1) since p = a :: p' and |p|-1 = |p'|
      assert (L.index p' (Prims.op_Subtraction (L.length p') 1) ==
              L.index p (Prims.op_Subtraction lp 1));
      ha.eq.reflexivity (L.index p (Prims.op_Subtraction lp 1) *
                         L.index q (Prims.op_Subtraction lq 1))

let rec all_zero_implies_index_zero
  (#t:Type) {| h: has_zero t |} (p: polynomial t) (i: nat)
  : Lemma (requires all_zero p /\ i < L.length p)
          (ensures L.index p i = zero)
          (decreases L.length p)
  = match p with
    | _ :: tl ->
      if i = 0 then h.eq.reflexivity zero
      else all_zero_implies_index_zero tl (Prims.op_Subtraction i 1)

let polynomial_domain_law (#t:Type) {| d: domain t |} (p q: polynomial t)
  : Lemma (requires poly_eq #t #(semiring_has_zero d.ring.semiring) (poly_mul p q) poly_zero)
          (ensures poly_eq #t #(semiring_has_zero d.ring.semiring) p poly_zero \/
                   poly_eq #t #(semiring_has_zero d.ring.semiring) q poly_zero)
  = let r : semiring t = d.ring.semiring in
    let ha : has_zero t = semiring_has_zero r in
    // poly_eq (poly_mul p q) [] = all_zero (poly_mul p q)
    // We argue by contraposition: assume neither all_zero p nor all_zero q,
    // derive a contradiction via poly_mul_top_coef.
    if all_zero #t #ha p then ()
    else if all_zero #t #ha q then ()
    else begin
      // Both p and q have a nonzero coefficient => poly_normalize is non-empty for each.
      let np = poly_normalize #t #ha p in
      let nq = poly_normalize #t #ha q in
      poly_eq_self_normalize #t #ha p;
      poly_eq_self_normalize #t #ha q;
      poly_normalize_no_trailing_zero #t #ha p;
      poly_normalize_no_trailing_zero #t #ha q;
      // np non-empty (else all_zero p), similarly nq:
      // If poly_normalize p = [], then all_zero p (the reverse direction of poly_normalize_all_zero_is_empty
      // doesn't hold directly; but poly_eq p [] = all_zero p, and poly_eq p np with np = [] gives all_zero p).
      if L.length np = 0 then poly_eq_symmetry p np
      else if L.length nq = 0 then poly_eq_symmetry q nq
      else begin
        // np and nq nonempty; their last entries are nonzero.
        let kp = Prims.op_Subtraction (L.length np) 1 in
        let kq = Prims.op_Subtraction (L.length nq) 1 in
        let lp = L.index np kp in
        let lq_coef = L.index nq kq in
        // lp <> zero, lq_coef <> zero, so by domain lp*lq_coef <> zero.
        domain_nonzero_factors_means_nonzero_product #t #d lp lq_coef;
        assert (~ (lp * lq_coef = zero));
        // poly_mul_top_coef on np, nq:
        poly_mul_top_coef #t #r np nq;
        poly_mul_length #t #r np nq;
        let target = Prims.op_Subtraction (L.length np + L.length nq) 2 in
        let prod = poly_mul np nq in
        assert (L.index prod target = lp * lq_coef);
        // poly_eq (poly_mul p q) (poly_mul np nq) via congruence
        poly_mul_congruence #t #r p q np nq;
        // We are given poly_eq (poly_mul p q) []. Combined via transitivity:
        poly_eq_symmetry (poly_mul p q) prod;
        poly_eq_transitivity prod (poly_mul p q) poly_zero;
        // poly_eq prod [] => all_zero prod (by def of poly_eq when q = [])
        assert (poly_eq #t #ha prod poly_zero);
        assert (Cons? prod);
        assert (all_zero #t #ha prod);
        // Hence L.index prod target = zero by all_zero_implies_index_zero.
        all_zero_implies_index_zero prod target;
        assert (L.index prod target = zero);
        // Combine: lp*lq_coef = L.index prod target = zero. Contradiction with ~(lp*lq_coef = zero).
        ha.eq.symmetry (L.index prod target) (lp * lq_coef);
        ha.eq.transitivity (lp * lq_coef) (L.index prod target) zero;
        assert (False)
      end
    end

instance polynomial_domain (#t:Type) {| d: domain t |}
  : domain (polynomial t)
  = {
      ring = polynomial_ring #t #d.ring;
      zero_ne_one_semiring = polynomial_zero_ne_one_semiring #t #d.zero_ne_one_semiring;
      domain_law = (fun p q -> polynomial_domain_law #t #d p q);
    }

instance polynomial_integral_domain (#t:Type) {| id: integral_domain t |}
  : integral_domain (polynomial t)
  = {
      commutative_ring = polynomial_commutative_ring #t #id.commutative_ring;
      domain = polynomial_domain #t #id.domain;
    }


(* ====================================================================== *)
(*  Evaluation homomorphism                                                *)
(*                                                                         *)
(*  eval is a ring homomorphism from polynomial t into t:                *)
(*     eval (p + q) x = eval p x + eval q x                                *)
(*     eval (a * q   :as scalar)    x = a * eval q x                       *)
(*     eval (p * q)  x = eval p x * eval q x                               *)
(*     eval (-p)     x = -(eval p x)                                       *)
(* ====================================================================== *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
(* Helper: 4-term shuffle in a commutative monoid. *)
private let add_swap4 (#t:Type) {| acm: add_comm_monoid t |} (a b u v: t)
  : Lemma ((a + b) + (u + v) = (a + u) + (b + v))
  = let am = acm.add_monoid in
    let sg = am.add_semigroup in
    let cm = acm.add_comm_semigroup.add_comm_magma in
    let ha = am.has_zero in
    elim_equatable_laws t;
    (* (a+b) + (u+v) *)
    sg.associativity a b (u + v);
    (* = a + (b + (u+v)) *)
    sg.associativity b u v;
    (* b + (u+v) = (b+u) + v ; but assoc gives (b+u)+v = b + (u+v), so use symmetry *)
    ha.eq.symmetry ((b + u) + v) (b + (u + v));
    cm.add_commutativity b u;
    ha.eq.reflexivity v;
    sg.has_add.congruence (b + u) v (u + b) v;
    sg.associativity u b v;
    (* (u+b) + v = u + (b+v) *)
    ha.eq.transitivity ((b + u) + v) ((u + b) + v) (u + (b + v));
    ha.eq.transitivity (b + (u + v)) ((b + u) + v) (u + (b + v));
    ha.eq.reflexivity a;
    sg.has_add.congruence a (b + (u + v)) a (u + (b + v));
    sg.associativity a u (b + v);
    (* a + (u + (b+v)) = (a+u) + (b+v) *)
    ha.eq.symmetry ((a + u) + (b + v)) (a + (u + (b + v)));
    ha.eq.transitivity (a + (b + (u + v))) (a + (u + (b + v))) ((a + u) + (b + v));
    ha.eq.symmetry (a + (b + (u + v))) ((a + b) + (u + v));
    ha.eq.transitivity ((a + b) + (u + v)) (a + (b + (u + v))) ((a + u) + (b + v))

let rec eval_add (#t:Type) {| r: semiring t |} (p q: polynomial t) (x: t)
  : Lemma (ensures eval (poly_add #t #r.add_comm_monoid.add_monoid p q) x
                   = eval p x + eval q x)
          (decreases %[L.length p; L.length q])
  = let ha = semiring_has_zero r in
    let acm = r.add_comm_monoid in
    let am = acm.add_monoid in
    elim_equatable_laws t;
    match p, q with
    | [], _ ->
      ha.eq.reflexivity (eval q x);
      am.left_add_identity (eval q x);
      ha.eq.symmetry (zero + eval q x) (eval q x)
    | _ :: _, [] ->
      ha.eq.reflexivity (eval p x);
      am.right_add_identity (eval p x);
      ha.eq.symmetry (eval p x + zero) (eval p x)
    | a :: p', b :: q' ->
      eval_add p' q' x;
      (* IH: eval (poly_add p' q') x = eval p' x + eval q' x *)
      ha.eq.reflexivity x;
      r.mul_monoid.mul_semigroup.has_mul.congruence
        x (eval (poly_add p' q') x) x (eval p' x + eval q' x);
      r.left_distributivity x (eval p' x) (eval q' x);
      ha.eq.transitivity (x * eval (poly_add p' q') x)
                         (x * (eval p' x + eval q' x))
                         (x * eval p' x + x * eval q' x);
      ha.eq.reflexivity (a + b);
      am.add_semigroup.has_add.congruence
        (a + b) (x * eval (poly_add p' q') x)
        (a + b) (x * eval p' x + x * eval q' x);
      (* (a+b) + x*eval(poly_add p' q') = (a+b) + (x*ep + x*eq) *)
      add_swap4 #t #acm a b (x * eval p' x) (x * eval q' x);
      (* (a+b) + (x*ep + x*eq) = (a + x*ep) + (b + x*eq) *)
      ha.eq.transitivity ((a + b) + x * eval (poly_add p' q') x)
                         ((a + b) + (x * eval p' x + x * eval q' x))
                         ((a + x * eval p' x) + (b + x * eval q' x))
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
let eval_cons_zero (#t:Type) {| r: semiring t |} (p: polynomial t) (x: t)
  : Lemma (eval ((zero #t) :: p) x = x * eval p x)
  = let ha = semiring_has_zero r in
    let am = r.add_comm_monoid.add_monoid in
    elim_equatable_laws t;
    am.left_add_identity (x * eval p x);
    ha.eq.reflexivity (x * eval p x)
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let rec eval_scalar_mul (#t:Type) {| cr: commutative_ring t |} (a: t) (q: polynomial t) (x: t)
  : Lemma (ensures eval #t #cr.ring.semiring (scalar_mul a q) x = a * eval q x)
          (decreases L.length q)
  = let r : ring t = cr.ring in
    let sr : semiring t = r.semiring in
    let ha = semiring_has_zero sr in
    let am = sr.add_comm_monoid.add_monoid in
    let mcm = cr.mul_comm_monoid in
    elim_equatable_laws t;
    match q with
    | [] ->
      sr.right_absorption a;
      ha.eq.symmetry (a * zero) zero
    | b :: q' ->
      eval_scalar_mul a q' x;
      (* IH: eval (scalar_mul a q') x = a * eval q' x *)
      ha.eq.reflexivity x;
      sr.mul_monoid.mul_semigroup.has_mul.congruence
        x (eval (scalar_mul a q') x) x (a * eval q' x);
      (* x * eval(scalar_mul a q') = x * (a * eval q') *)
      mcm.mul_comm_semigroup.mul_comm_magma.mul_commutativity x a;
      (* x * a = a * x *)
      ha.eq.reflexivity (eval q' x);
      sr.mul_monoid.mul_semigroup.has_mul.congruence (x * a) (eval q' x) (a * x) (eval q' x);
      sr.mul_monoid.mul_semigroup.associativity x a (eval q' x);
      ha.eq.symmetry ((x * a) * eval q' x) (x * (a * eval q' x));
      sr.mul_monoid.mul_semigroup.associativity a x (eval q' x);
      ha.eq.transitivity ((x * a) * eval q' x) ((a * x) * eval q' x) (a * (x * eval q' x));
      ha.eq.transitivity (x * (a * eval q' x)) ((x * a) * eval q' x) (a * (x * eval q' x));
      ha.eq.transitivity (x * eval (scalar_mul a q') x) (x * (a * eval q' x)) (a * (x * eval q' x));
      (* eval (scalar_mul a (b::q')) x = (a*b) + x * eval (scalar_mul a q') x
                                       = (a*b) + a * (x * eval q' x)
                                       = a * (b + x * eval q' x)   by left_distrib
                                       = a * eval (b::q') x *)
      ha.eq.reflexivity (a * b);
      am.add_semigroup.has_add.congruence
        (a * b) (x * eval (scalar_mul a q') x)
        (a * b) (a * (x * eval q' x));
      sr.left_distributivity a b (x * eval q' x);
      (* a * (b + x*eval q' x) = a*b + a*(x*eval q' x) *)
      ha.eq.symmetry (a * (b + x * eval q' x)) (a * b + a * (x * eval q' x));
      ha.eq.transitivity ((a * b) + x * eval (scalar_mul a q') x)
                         ((a * b) + a * (x * eval q' x))
                         (a * (b + x * eval q' x))
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let rec eval_mul (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) (x: t)
  : Lemma (ensures eval #t #cr.ring.semiring (poly_mul p q) x = eval p x * eval q x)
          (decreases L.length p)
  = let r : ring t = cr.ring in
    let sr : semiring t = r.semiring in
    let ha = semiring_has_zero sr in
    let am = sr.add_comm_monoid.add_monoid in
    elim_equatable_laws t;
    match p with
    | [] ->
      (* poly_mul [] q = []; eval [] x = zero; zero * eval q x = zero *)
      sr.left_absorption (eval q x);
      ha.eq.symmetry (zero * eval q x) zero
    | a :: p' ->
      eval_mul p' q x;
      (* IH: eval (poly_mul p' q) x = eval p' x * eval q x *)
      let pa = scalar_mul a q in
      let pm = poly_mul p' q in
      let cz = (zero #t) :: pm in
      (* eval (poly_mul (a::p') q) x = eval (poly_add pa cz) x *)
      eval_add #t #sr pa cz x;
      (* = eval pa x + eval cz x *)
      eval_scalar_mul #t #cr a q x;
      (* eval pa x = a * eval q x *)
      eval_cons_zero #t #sr pm x;
      (* eval cz x = x * eval pm x *)
      ha.eq.reflexivity x;
      sr.mul_monoid.mul_semigroup.has_mul.congruence
        x (eval pm x) x (eval p' x * eval q x);
      (* x * eval pm x = x * (eval p' x * eval q x) *)
      ha.eq.transitivity (eval cz x) (x * eval pm x) (x * (eval p' x * eval q x));
      am.add_semigroup.has_add.congruence
        (eval pa x) (eval cz x)
        (a * eval q x) (x * (eval p' x * eval q x));
      (* eval pa x + eval cz x = a*eval q x + x*(eval p' x * eval q x) *)
      ha.eq.transitivity (eval (poly_add pa cz) x)
                         (eval pa x + eval cz x)
                         (a * eval q x + x * (eval p' x * eval q x));
      (* Now eval (a::p') x * eval q x = (a + x * eval p' x) * eval q x *)
      sr.right_distributivity a (x * eval p' x) (eval q x);
      (* (a + x*eval p' x) * eval q x = a*eval q x + (x*eval p' x)*eval q x *)
      sr.mul_monoid.mul_semigroup.associativity x (eval p' x) (eval q x);
      (* (x * eval p' x) * eval q x = x * (eval p' x * eval q x) *)
      ha.eq.reflexivity (a * eval q x);
      am.add_semigroup.has_add.congruence
        (a * eval q x) ((x * eval p' x) * eval q x)
        (a * eval q x) (x * (eval p' x * eval q x));
      ha.eq.transitivity ((a + x * eval p' x) * eval q x)
                         (a * eval q x + (x * eval p' x) * eval q x)
                         (a * eval q x + x * (eval p' x * eval q x));
      ha.eq.symmetry ((a + x * eval p' x) * eval q x)
                     (a * eval q x + x * (eval p' x * eval q x));
      ha.eq.transitivity (eval (poly_add pa cz) x)
                         (a * eval q x + x * (eval p' x * eval q x))
                         ((a + x * eval p' x) * eval q x)
#pop-options

(* ====================================================================== *)
(*  degree(p*q) over an integral domain                                    *)
(* ====================================================================== *)

(* drop_leading_zeros leaves a list with non-zero head unchanged. *)
let drop_leading_zeros_head_nonzero
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (requires Cons? p /\ ~ (L.index p 0 = zero))
          (ensures drop_leading_zeros p == p)
  = match p with
    | a :: _ -> ()

(* Equivalent forward characterization of normalize length: position of last
   non-zero coefficient + 1, or 0 if no such position. *)
let rec forward_norm_length
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Tot nat (decreases L.length p)
  = match p with
    | [] -> 0
    | a :: tl ->
      let r = forward_norm_length tl in
      if r > 0 then Prims.op_Addition r 1
      else if a = zero then 0
      else 1

(* forward_norm_length = 0 iff all_zero. *)
let rec forward_norm_length_zero_iff_all_zero
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (ensures forward_norm_length p = 0 <==> all_zero p)
          (decreases L.length p)
  = match p with
    | [] -> ()
    | _ :: tl -> forward_norm_length_zero_iff_all_zero tl

(* drop_leading_zeros append when prefix-after-drop is nonempty. *)
let rec drop_lead_append_when_drop_nonempty
  (#t:Type) {| h: has_zero t |} (p s: polynomial t)
  : Lemma (requires Cons? (drop_leading_zeros p))
          (ensures L.length (drop_leading_zeros (L.append p s)) =
                   Prims.op_Addition (L.length (drop_leading_zeros p)) (L.length s))
          (decreases L.length p)
  = match p with
    | a :: tl ->
      if a = zero then drop_lead_append_when_drop_nonempty tl s
      else (L.append_length p s)

(* drop_leading_zeros of (all_zero ++ s) collapses to drop_leading_zeros s. *)
let rec drop_lead_all_zero_prefix_then_head
  (#t:Type) {| h: has_zero t |} (p s: polynomial t)
  : Lemma (requires all_zero p)
          (ensures drop_leading_zeros (L.append p s) == drop_leading_zeros s)
          (decreases L.length p)
  = match p with
    | [] -> ()
    | a :: tl ->
      drop_lead_all_zero_prefix_then_head tl s

(* forward_norm_length matches L.length of poly_normalize. *)
let rec forward_norm_length_eq_normalize_length
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (ensures L.length (poly_normalize p) = forward_norm_length p)
          (decreases L.length p)
  = match p with
    | [] -> ()
    | a :: tl ->
      forward_norm_length_eq_normalize_length tl;
      let rtl = L.rev tl in
      let r = forward_norm_length tl in
      L.rev_length tl;
      L.rev_rev' p;
      L.rev_append [a] tl;
      L.append_length rtl [a];
      assert (L.rev p == L.append rtl [a]);
      assert (L.length (poly_normalize tl) = r);
      L.rev_length (drop_leading_zeros rtl);
      assert (L.length (drop_leading_zeros rtl) = r);
      if r > 0 then begin
        assert (Cons? (drop_leading_zeros rtl));
        drop_lead_append_when_drop_nonempty rtl [a];
        L.rev_length (drop_leading_zeros (L.append rtl [a]))
      end else begin
        forward_norm_length_zero_iff_all_zero tl;
        rev_all_zero tl;
        drop_lead_all_zero_prefix_then_head rtl [a];
        L.rev_length (drop_leading_zeros [a])
      end

(* poly_eq congruence for forward_norm_length. *)
let rec poly_eq_forward_norm_length
  (#t:Type) {| h: has_zero t |} (p q: polynomial t)
  : Lemma (requires poly_eq p q)
          (ensures forward_norm_length p = forward_norm_length q)
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _ -> forward_norm_length_zero_iff_all_zero q
    | _ :: _, [] -> forward_norm_length_zero_iff_all_zero p
    | a :: p', b :: q' ->
      poly_eq_forward_norm_length p' q';
      let r = forward_norm_length p' in
      if r > 0 then ()
      else begin
        h.eq.symmetry a b;
        if a = zero then h.eq.transitivity b a zero
        else if b = zero then h.eq.transitivity a b zero
      end

(* poly_eq implies same normalize length. *)
let poly_eq_normalize_length
  (#t:Type) {| h: has_zero t |} (p q: polynomial t)
  : Lemma (requires poly_eq p q)
          (ensures L.length (poly_normalize p) = L.length (poly_normalize q))
  = poly_eq_forward_norm_length p q;
    forward_norm_length_eq_normalize_length p;
    forward_norm_length_eq_normalize_length q

(* degree is well-defined under poly_eq. *)
let degree_poly_zero (#t:Type) {| h: has_zero t |} (u: unit)
  : Lemma (degree #t #h (poly_zero #t) == None)
  = ()

let degree_well_defined
  (#t:Type) {| h: has_zero t |} (p q: polynomial t)
  : Lemma (requires poly_eq p q)
          (ensures degree p == degree q)
  = poly_eq_normalize_length p q

(* poly_normalize is identity when last element is non-zero. *)
let poly_normalize_idempotent_when_last_nonzero
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (requires Cons? p /\
                    ~ (L.index p (Prims.op_Subtraction (L.length p) 1) = zero))
          (ensures poly_normalize p == p)
  = let rp = L.rev p in
    L.rev_length p;
    L.rev_involutive p;
    rev_index_last rp;
    drop_leading_zeros_head_nonzero rp

(* degree(p*q) = deg p + deg q over an integral domain. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let degree_mul
  (#t:Type) {| id: integral_domain t |} (p q: polynomial t)
  : Lemma (requires Some? (degree #t #(semiring_has_zero id.commutative_ring.ring.semiring) p) /\
                    Some? (degree #t #(semiring_has_zero id.commutative_ring.ring.semiring) q))
          (ensures (let ha = semiring_has_zero id.commutative_ring.ring.semiring in
                    degree #t #ha (poly_mul p q) ==
                    Some (Prims.op_Addition
                            (Some?.v (degree #t #ha p))
                            (Some?.v (degree #t #ha q)))))
  = let r : semiring t = id.commutative_ring.ring.semiring in
    let ha : has_zero t = semiring_has_zero r in
    let np : polynomial t = poly_normalize #t #ha p in
    let nq : polynomial t = poly_normalize #t #ha q in
    let n : nat = Some?.v (degree #t #ha p) in
    let m : nat = Some?.v (degree #t #ha q) in
    (* By definition of degree: |np| = n+1, |nq| = m+1. *)
    assert (L.length np = Prims.op_Addition n 1);
    assert (L.length nq = Prims.op_Addition m 1);
    poly_normalize_no_trailing_zero #t #ha p;
    poly_normalize_no_trailing_zero #t #ha q;
    assert (~ (L.index np n = zero));
    assert (~ (L.index nq m = zero));
    (* Compute degree of poly_mul np nq directly. *)
    poly_mul_length #t #r np nq;
    let prod : polynomial t = poly_mul #t #r np nq in
    assert (L.length prod = Prims.op_Addition (Prims.op_Addition n m) 1);
    poly_mul_top_coef #t #r np nq;
    let target : nat = Prims.op_Addition n m in
    assert (target = Prims.op_Subtraction (L.length prod) 1);
    let topp : t = L.index np n in
    let topq : t = L.index nq m in
    assert (L.index prod target = topp * topq);
    domain_nonzero_factors_means_nonzero_product #t #id.domain topp topq;
    assert (~ (topp * topq = zero));
    (* Hence ~ (L.index prod (|prod|-1) = zero) via equatable transitivity. *)
    ha.eq.symmetry (L.index prod target) (topp * topq);
    (* If L.index prod target = zero, by symmetry zero = L.index prod target,
       trans gives topp*topq = zero, contradiction. *)
    if L.index prod target = zero then begin
      ha.eq.transitivity (topp * topq) (L.index prod target) zero
    end;
    assert (~ (L.index prod target = zero));
    poly_normalize_idempotent_when_last_nonzero #t #ha prod;
    assert (poly_normalize prod == prod);
    assert (degree #t #ha prod == Some target);
    (* Lift to poly_mul p q via congruence + degree_well_defined. *)
    poly_eq_self_normalize #t #ha p;
    poly_eq_self_normalize #t #ha q;
    poly_mul_congruence #t #r p q np nq;
    degree_well_defined #t #ha (poly_mul p q) prod
#pop-options

(* poly_normalize is a prefix of the original list. *)
let poly_normalize_prefix
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (ensures (let np = poly_normalize p in
                    let zs = L.rev (leading_zeros_prefix (L.rev p)) in
                    p == L.append np zs /\ all_zero zs))
  = let rp = L.rev p in
    leading_zeros_prefix_lemma rp;
    let zs_rev = leading_zeros_prefix rp in
    let dr = drop_leading_zeros rp in
    (* rp == L.append zs_rev dr *)
    L.rev_involutive p;
    L.rev_append zs_rev dr;
    (* L.rev rp == L.append (L.rev dr) (L.rev zs_rev) *)
    rev_all_zero zs_rev

let poly_normalize_length_le
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (ensures L.length (poly_normalize p) <= L.length p)
  = poly_normalize_prefix p;
    let np = poly_normalize p in
    let zs : polynomial t = L.rev (leading_zeros_prefix (L.rev p)) in
    L.append_length np zs

let poly_normalize_index_eq_index
  (#t:Type) {| h: has_zero t |} (p: polynomial t) (i: nat)
  : Lemma (requires i < L.length (poly_normalize p))
          (ensures L.length (poly_normalize p) <= L.length p /\
                   L.index (poly_normalize p) i == L.index p i)
  = poly_normalize_prefix p;
    poly_normalize_length_le p;
    let np = poly_normalize p in
    let zs : polynomial t = L.rev (leading_zeros_prefix (L.rev p)) in
    L.append_length np zs;
    index_append_lemma np zs i

(* coeff_at: zero-padded coefficient access. *)
let coeff_at (#t:Type) {| h: has_zero t |} (p: polynomial t) (i: nat) : t
  = if i < L.length p then L.index p i else zero

let rec poly_eq_coeff_at
  (#t:Type) {| h: has_zero t |} (p q: polynomial t) (i: nat)
  : Lemma (requires poly_eq p q)
          (ensures coeff_at p i = coeff_at q i)
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _ ->
      if i < L.length q then begin
        all_zero_implies_index_zero q i;
        h.eq.symmetry (L.index q i) zero
      end else h.eq.reflexivity zero
    | _ :: _, [] ->
      if i < L.length p then begin
        all_zero_implies_index_zero p i;
        h.eq.reflexivity zero  (* coeff_at p i = L.index p i = zero, coeff_at q i = zero *)
      end else h.eq.reflexivity zero
    | a :: p', b :: q' ->
      if i = 0 then ()
      else poly_eq_coeff_at p' q' (Prims.op_Subtraction i 1)

let lc_well_defined
  (#t:Type) {| h: has_zero t |} (p q: polynomial t)
  : Lemma (requires poly_eq p q)
          (ensures leading_coefficient p = leading_coefficient q)
  = poly_eq_normalize_length p q;
    let np = poly_normalize p in
    let nq = poly_normalize q in
    let k = L.length np in
    if k = 0 then h.eq.reflexivity zero
    else begin
      let i = Prims.op_Subtraction k 1 in
      poly_normalize_length_le p;
      poly_normalize_length_le q;
      poly_normalize_index_eq_index p i;
      poly_normalize_index_eq_index q i;
      poly_eq_coeff_at p q i
    end

(* leading_coefficient(p*q) = lc(p) * lc(q) over an integral domain. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lc_mul
  (#t:Type) {| id: integral_domain t |} (p q: polynomial t)
  : Lemma (requires Some? (degree #t #(semiring_has_zero id.commutative_ring.ring.semiring) p) /\
                    Some? (degree #t #(semiring_has_zero id.commutative_ring.ring.semiring) q))
          (ensures (let ha = semiring_has_zero id.commutative_ring.ring.semiring in
                    leading_coefficient #t #ha (poly_mul p q) =
                    leading_coefficient #t #ha p * leading_coefficient #t #ha q))
  = let r : semiring t = id.commutative_ring.ring.semiring in
    let ha : has_zero t = semiring_has_zero r in
    let np : polynomial t = poly_normalize #t #ha p in
    let nq : polynomial t = poly_normalize #t #ha q in
    let n : nat = Some?.v (degree #t #ha p) in
    let m : nat = Some?.v (degree #t #ha q) in
    assert (L.length np = Prims.op_Addition n 1);
    assert (L.length nq = Prims.op_Addition m 1);
    poly_normalize_no_trailing_zero #t #ha p;
    poly_normalize_no_trailing_zero #t #ha q;
    poly_mul_length #t #r np nq;
    let prod : polynomial t = poly_mul #t #r np nq in
    poly_mul_top_coef #t #r np nq;
    let target : nat = Prims.op_Addition n m in
    let topp : t = L.index np n in
    let topq : t = L.index nq m in
    assert (L.index prod target = topp * topq);
    domain_nonzero_factors_means_nonzero_product #t #id.domain topp topq;
    ha.eq.symmetry (L.index prod target) (topp * topq);
    if L.index prod target = zero then
      ha.eq.transitivity (topp * topq) (L.index prod target) zero;
    assert (~ (L.index prod target = zero));
    poly_normalize_idempotent_when_last_nonzero #t #ha prod;
    assert (poly_normalize prod == prod);
    (* lc (poly_mul np nq) = L.index prod target = topp * topq *)
    assert (leading_coefficient #t #ha prod == L.index prod target);
    (* lc p = topp, lc q = topq (by definition; np = poly_normalize p is structurally
       equal to itself, and L.index np n is the lc by definition). *)
    assert (leading_coefficient #t #ha p == topp);
    assert (leading_coefficient #t #ha q == topq);
    (* Lift via poly_eq + lc_well_defined. *)
    poly_eq_self_normalize #t #ha p;
    poly_eq_self_normalize #t #ha q;
    poly_mul_congruence #t #r p q np nq;
    lc_well_defined #t #ha (poly_mul p q) prod;
    ha.eq.reflexivity (L.index prod target);
    (* lc prod == L.index prod target propositionally, plus reflexivity gives
       lc prod = L.index prod target as equatable. *)
    ha.eq.transitivity (leading_coefficient #t #ha (poly_mul p q))
                       (leading_coefficient #t #ha prod)
                       (L.index prod target);
    ha.eq.transitivity (leading_coefficient #t #ha (poly_mul p q))
                       (L.index prod target)
                       (topp * topq)
#pop-options

let coeff_at_unfold
  (#t:Type) {| h: has_zero t |} (p: polynomial t) (i: nat)
  : Lemma (ensures coeff_at p i ==
                   (if i < L.length p then L.index p i else zero))
  = ()

let poly_add_nil_left (#t:Type) {| m: add_monoid t |} (q: polynomial t)
  : Lemma (ensures poly_add #t #m [] q == q)
  = ()

let poly_add_nil_right (#t:Type) {| m: add_monoid t |} (p: polynomial t)
  : Lemma (ensures poly_add #t #m p [] == p)
  = ()

let poly_add_cons_cons (#t:Type) {| m: add_monoid t |}
                       (a: t) (p': polynomial t) (b: t) (q': polynomial t)
  : Lemma (ensures poly_add #t #m (a :: p') (b :: q') == (a + b) :: poly_add p' q')
  = ()

let scalar_mul_nil (#t:Type) {| r: semiring t |} (a: t)
  : Lemma (ensures scalar_mul a ([] <: polynomial t) == [])
  = ()

let scalar_mul_cons (#t:Type) {| r: semiring t |} (a: t) (b: t) (q': polynomial t)
  : Lemma (ensures scalar_mul a (b :: q') == (a * b) :: scalar_mul a q')
  = ()

let poly_neg_nil (#t:Type) {| g: add_comm_group t |} (u: unit)
  : Lemma (ensures poly_neg #t #g [] == [])
  = ()

let poly_neg_cons (#t:Type) {| g: add_comm_group t |} (a: t) (p': polynomial t)
  : Lemma (ensures poly_neg (a :: p') == (-a) :: poly_neg p')
  = ()

let all_zero_nil (#t:Type) {| h: has_zero t |} (u: unit)
  : Lemma (ensures all_zero #t #h [] == true)
  = ()

let all_zero_cons (#t:Type) {| h: has_zero t |} (a: t) (p': polynomial t)
  : Lemma (ensures all_zero (a :: p') == ((a = zero) && all_zero p'))
  = ()

let poly_eq_nil_left (#t:Type) {| h: has_zero t |} (q: polynomial t)
  : Lemma (ensures poly_eq ([] <: polynomial t) q == all_zero q)
  = ()

let poly_eq_nil_right (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (ensures poly_eq p ([] <: polynomial t) == all_zero p)
  = match p with | [] -> () | _ :: _ -> ()

let poly_eq_cons_cons (#t:Type) {| h: has_zero t |}
                      (a: t) (p': polynomial t) (b: t) (q': polynomial t)
  : Lemma (ensures poly_eq (a :: p') (b :: q') == ((a = b) && poly_eq p' q'))
  = ()

let poly_sub_unfold (#t:Type) {| g: add_comm_group t |} (p q: polynomial t)
  : Lemma (ensures poly_sub p q == poly_add p (poly_neg q))
  = ()
(* ====================================================================== *)
(*  Extensionality: coeff-wise equality implies poly_eq                   *)
(* ====================================================================== *)

let rec all_zero_of_coeff_zero (#t:Type) {| h: has_zero t |} (q: polynomial t)
  : Lemma (requires forall (i: nat). coeff_at q i = zero)
          (ensures all_zero q)
          (decreases L.length q)
  = match q with
    | [] -> ()
    | b :: q' ->
      coeff_at_unfold q 0;
      assert (coeff_at q 0 == b);
      let aux (i: nat) : Lemma (coeff_at q' i = zero) =
        coeff_at_unfold q' i;
        coeff_at_unfold (b :: q') (Prims.op_Addition i 1)
      in
      Classical.forall_intro aux;
      all_zero_of_coeff_zero q'

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec coeff_at_to_poly_eq (#t:Type) {| h: has_zero t |} (p q: polynomial t)
  : Lemma (requires forall (i: nat). coeff_at p i = coeff_at q i)
          (ensures poly_eq p q)
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _ ->
      let aux (i: nat) : Lemma (coeff_at q i = zero) =
        coeff_at_unfold ([] <: polynomial t) i;
        h.eq.symmetry (coeff_at p i) (coeff_at q i)
      in
      Classical.forall_intro aux;
      all_zero_of_coeff_zero q
    | a :: p', [] ->
      let aux (i: nat) : Lemma (coeff_at p i = zero) =
        coeff_at_unfold ([] <: polynomial t) i
      in
      Classical.forall_intro aux;
      all_zero_of_coeff_zero p
    | a :: p', b :: q' ->
      coeff_at_unfold p 0;
      coeff_at_unfold q 0;
      assert (coeff_at p 0 == a);
      assert (coeff_at q 0 == b);
      let aux (i: nat) : Lemma (coeff_at p' i = coeff_at q' i) =
        coeff_at_unfold p' i;
        coeff_at_unfold q' i;
        coeff_at_unfold (a :: p') (Prims.op_Addition i 1);
        coeff_at_unfold (b :: q') (Prims.op_Addition i 1)
      in
      Classical.forall_intro aux;
      coeff_at_to_poly_eq p' q'
#pop-options

(* Euclidean-division helpers *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let lc_nonzero_of_degree_some
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (requires Some? (degree p))
          (ensures ~(leading_coefficient p = zero))
  = let np = poly_normalize p in
    let k = Some?.v (degree p) in
    poly_normalize_no_trailing_zero p
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let coeff_at_degree_eq_lc
  (#t:Type) {| h: has_zero t |} (p: polynomial t)
  : Lemma (requires Some? (degree p))
          (ensures coeff_at p (Some?.v (degree p)) = leading_coefficient p)
  = let k = Some?.v (degree p) in
    let np = poly_normalize p in
    poly_eq_self_normalize p;
    poly_eq_coeff_at p (poly_normalize p) k;
    poly_normalize_index_eq_index p k;
    h.eq.reflexivity (leading_coefficient p)
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
private let degree_above_means_past_normalize (#t:Type) {| h: has_zero t |} (p: polynomial t) (i: nat)
  : Lemma (requires (degree #t #h p == None \/ (Some? (degree #t #h p) /\ i > Some?.v (degree #t #h p))) /\
                    L.length (poly_normalize #t #h p) > 0)
          (ensures i >= L.length (poly_normalize #t #h p))
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let coeff_above_degree_is_zero
  (#t:Type) {| h: has_zero t |} (p: polynomial t) (i: nat)
  : Lemma (requires (degree p == None \/ (Some? (degree p) /\ i > Some?.v (degree p))))
          (ensures coeff_at p i = zero)
  = let np = poly_normalize p in
    poly_eq_self_normalize p;
    poly_eq_coeff_at p np i;
    coeff_at_unfold np i;
    if L.length np = 0 then
      h.eq.reflexivity zero
    else begin
      degree_above_means_past_normalize p i;
      h.eq.reflexivity zero
    end
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let degree_lt_from_coeff_zero
  (#t:Type) {| h: has_zero t |} (p: polynomial t) (n: nat)
  : Lemma (requires (forall (i:nat). i >= n ==> coeff_at p i = zero))
          (ensures (degree p == None \/ (Some? (degree p) /\ Some?.v (degree p) < n)))
  = match degree p with
    | None -> ()
    | Some k ->
      if k >= n then begin
        coeff_at_degree_eq_lc p;
        lc_nonzero_of_degree_some p;
        h.eq.symmetry (coeff_at p k) (leading_coefficient p);
        h.eq.transitivity (leading_coefficient p) (coeff_at p k) zero
      end else ()
#pop-options