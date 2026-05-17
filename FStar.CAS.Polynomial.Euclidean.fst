module FStar.CAS.Polynomial.Euclidean

open FStar.CAS.Equatable
open FStar.CAS.Grouplikes
open FStar.CAS.Ringlikes
open FStar.CAS.Polynomial

module L = FStar.List.Tot.Base

(* ====================================================================== *)
(*  poly_shift: prepend k zeros (i.e., multiply by x^k)                    *)
(* ====================================================================== *)

let rec poly_shift (#t:Type) {| h: has_zero t |} (p: polynomial t) (k: nat)
  : Tot (polynomial t) (decreases k)
  = if k = 0 then p else zero :: poly_shift p (Prims.op_Subtraction k 1)

let rec poly_shift_length
  (#t:Type) {| h: has_zero t |} (p: polynomial t) (k: nat)
  : Lemma (ensures L.length (poly_shift p k) = Prims.op_Addition (L.length p) k)
          (decreases k)
  = if k = 0 then ()
    else poly_shift_length p (Prims.op_Subtraction k 1)

let rec poly_shift_index
  (#t:Type) {| h: has_zero t |} (p: polynomial t) (k: nat) (i: nat)
  : Lemma (requires i < Prims.op_Addition (L.length p) k)
          (ensures (poly_shift_length p k;
                    (if i < k then L.index (poly_shift p k) i == zero
                     else L.index (poly_shift p k) i ==
                          L.index p (Prims.op_Subtraction i k))))
          (decreases k)
  = poly_shift_length p k;
    if k = 0 then ()
    else if i = 0 then ()
    else poly_shift_index p (Prims.op_Subtraction k 1) (Prims.op_Subtraction i 1)


(* ====================================================================== *)
(*  coeff_at lemmas for poly_add, scalar_mul, poly_shift, poly_neg         *)
(* ====================================================================== *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec coeff_at_poly_add
  (#t:Type) {| m: add_monoid t |} (p q: polynomial t) (i: nat)
  : Lemma (ensures coeff_at (poly_add p q) i =
                   coeff_at p i + coeff_at q i)
          (decreases %[L.length p; L.length q])
  = let lhs = coeff_at (poly_add p q) i in
    let cp = coeff_at p i in
    let cq = coeff_at q i in
    coeff_at_unfold (poly_add p q) i;
    coeff_at_unfold p i;
    coeff_at_unfold q i;
    match p, q with
    | [], _ ->
      poly_add_nil_left q;
      m.left_add_identity cq;
      m.has_zero.eq.symmetry (zero + cq) cq
    | _ :: _, [] ->
      poly_add_nil_right p;
      m.right_add_identity cp;
      m.has_zero.eq.symmetry (cp + zero) cp
    | a :: p', b :: q' ->
      poly_add_cons_cons a p' b q';
      if i = 0 then begin
        m.has_zero.eq.reflexivity (a + b)
      end else begin
        let i' = Prims.op_Subtraction i 1 in
        coeff_at_unfold (poly_add p' q') i';
        coeff_at_unfold p' i';
        coeff_at_unfold q' i';
        coeff_at_poly_add p' q' i'
      end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec coeff_at_scalar_mul
  (#t:Type) {| r: semiring t |} (a: t) (q: polynomial t) (i: nat)
  : Lemma (ensures coeff_at (scalar_mul a q) i = a * coeff_at q i)
          (decreases L.length q)
  = coeff_at_unfold (scalar_mul a q) i;
    coeff_at_unfold q i;
    match q with
    | [] ->
      scalar_mul_nil #t #r a;
      (he_r r).reflexivity zero;
      absorption zero a;
      (he_r r).symmetry (a * zero) zero
    | b :: q' ->
      scalar_mul_cons a b q';
      if i = 0 then (he_r r).reflexivity (a * b)
      else begin
        let i' = Prims.op_Subtraction i 1 in
        coeff_at_unfold (scalar_mul a q') i';
        coeff_at_unfold q' i';
        coeff_at_scalar_mul a q' i'
      end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec coeff_at_poly_neg
  (#t:Type) {| g: add_comm_group t |} (p: polynomial t) (i: nat)
  : Lemma (ensures coeff_at (poly_neg p) i = -(coeff_at p i))
          (decreases L.length p)
  = let ha = g.add_comm_monoid.add_monoid.add_semigroup.has_add in
    coeff_at_unfold (poly_neg p) i;
    coeff_at_unfold p i;
    match p with
    | [] ->
      poly_neg_nil #t #g ();
      zero_equals_minus_zero #t #g.add_group;
      ha.eq.symmetry zero (-zero)
    | a :: p' ->
      poly_neg_cons a p';
      if i = 0 then ha.eq.reflexivity (-a)
      else begin
        let i' = Prims.op_Subtraction i 1 in
        coeff_at_unfold (poly_neg p') i';
        coeff_at_unfold p' i';
        coeff_at_poly_neg p' i'
      end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let coeff_at_poly_shift
  (#t:Type) {| h: has_zero t |} (p: polynomial t) (k: nat) (i: nat)
  : Lemma (ensures coeff_at (poly_shift p k) i ==
                   (if i < k then zero
                    else coeff_at p (Prims.op_Subtraction i k)))
          (decreases k)
  = coeff_at_unfold (poly_shift p k) i;
    poly_shift_length p k;
    coeff_at_unfold p (if i < k then 0 else Prims.op_Subtraction i k);
    if k = 0 then ()
    else if i = 0 then ()
    else if i < Prims.op_Addition (L.length p) k then begin
      poly_shift_index p k i
    end else ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let coeff_at_poly_sub
  (#t:Type) {| g: add_comm_group t |} (p q: polynomial t) (i: nat)
  : Lemma (ensures coeff_at (poly_sub p q) i = coeff_at p i - coeff_at q i)
  = let ha = g.add_comm_monoid.add_monoid.add_semigroup.has_add in
    let cp = coeff_at p i in
    let cq = coeff_at q i in
    coeff_at_poly_add p (poly_neg q) i;
    coeff_at_poly_neg q i;
    poly_sub_unfold p q;
    assert (coeff_at (poly_sub p q) i = cp + coeff_at (poly_neg q) i);
    ha.eq.reflexivity cp;
    let lhs_neg = coeff_at (poly_neg q) i in
    ha.congruence cp lhs_neg cp (-cq);
    assert (cp + lhs_neg = cp + (-cq));
    ha.eq.transitivity (coeff_at (poly_sub p q) i) (cp + lhs_neg) (cp + (-cq));
    g.add_group.subtraction_definition cp cq;
    ha.eq.symmetry (cp - cq) (cp + (-cq));
    ha.eq.transitivity (coeff_at (poly_sub p q) i) (cp + (-cq)) (cp - cq)
#pop-options

(* ====================================================================== *)
(*  Euclidean polynomial division over a field                              *)
(*                                                                          *)
(*  Given p, q with q ≠ 0 (degree q = Some _), compute (quot, rem) s.t.:   *)
(*    poly_eq p (poly_add (poly_mul q quot) rem)                            *)
(*    degree rem < degree q  (or rem ≈ 0)                                   *)
(* ====================================================================== *)

(* Shorthand for the has_zero from a field. *)
let field_has_zero (#t:Type) (f: field t) : has_zero t =
  semiring_has_zero f.division_ring.domain.ring.semiring

(* Recursive Euclidean division with explicit fuel.
   fuel should be >= degree(p) + 1 for a complete division. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let rec poly_divmod_aux (#t:Type) {|f: field t|}
  (p q: polynomial t) (fuel: nat)
  : Tot (polynomial t & polynomial t) (decreases fuel)
  = if fuel = 0 then (poly_zero, p)
    else
      match degree p, degree q with
      | None, _ -> (poly_zero, p)
      | _, None -> (poly_zero, p)
      | Some dp, Some dq ->
        if dp < dq then (poly_zero, p)
        else begin
          lc_nonzero_of_degree_some q;
          let lc_p = leading_coefficient p in
          let lc_q = leading_coefficient q in
          let inv_lc_q : t = f.division_ring.inv lc_q in
          let c : t = lc_p * inv_lc_q in
          let shift : nat = Prims.op_Subtraction dp dq in
          let t_poly = scalar_mul c (poly_shift q shift) in
          let p' = poly_sub p t_poly in
          let (q', r) = poly_divmod_aux p' q (Prims.op_Subtraction fuel 1) in
          (poly_add (poly_shift [c] shift) q', r)
        end
#pop-options

(* Top-level Euclidean division: supplies the initial fuel. *)
let poly_divmod (#t:Type) {|f: field t|}
  (p q: polynomial t)
  : Pure (polynomial t & polynomial t)
    (requires Some? (degree q))
    (ensures fun _ -> True)
  = let fuel : nat =
      match degree p with
      | None -> 1
      | Some dp -> Prims.op_Addition dp 1
    in
    poly_divmod_aux p q fuel

(* Projections for convenience. *)
let poly_div (#t:Type) {|f: field t|} (p q: polynomial t)
  : Pure (polynomial t)
    (requires Some? (degree q))
    (ensures fun _ -> True)
  = fst (poly_divmod p q)

let poly_mod (#t:Type) {|f: field t|} (p q: polynomial t)
  : Pure (polynomial t)
    (requires Some? (degree q))
    (ensures fun _ -> True)
  = snd (poly_divmod p q)

(* ====================================================================== *)
(*  Degree-reduction proof for Euclidean division                           *)
(* ====================================================================== *)

(* Helper: x - x = zero for any add_group *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let sub_self (#t:Type) {|g: add_group t|} (x: t)
  : Lemma (x - x = zero) =
  g.subtraction_definition x x;
  g.negation x;
  let eq : equatable t = g.add_monoid.add_semigroup.has_add.eq in
  eq.transitivity (x - x) (x + (-x)) zero
#pop-options

// Proves x - x = zero in a clean SMT context (no accumulated TC bridges)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let sub_self_via_field (#t:Type) {|f: field t|} (x: t)
  : Lemma (let r = f.division_ring.domain.ring in
           let ag = r.add_comm_group.add_group in
           let ag_eq = ag.add_monoid.add_semigroup.has_add.eq in
           let hz = ag.add_monoid.has_zero in
           ag_eq.op_Equals (x - x) hz.zero = true) =
  let r = f.division_ring.domain.ring in
  let ag = r.add_comm_group.add_group in
  let ag_eq = ag.add_monoid.add_semigroup.has_add.eq in
  ag.subtraction_definition x x;
  ag.negation x;
  ag_eq.transitivity (x - x) (x + (-x)) ag.add_monoid.has_zero.zero
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let sub_congruence (#t:Type) {|g: add_group t|} (a b c d: t)
  : Lemma (requires a = c /\ b = d)
          (ensures a - b = c - d) =
  g.subtraction_definition a b;
  g.subtraction_definition c d;
  equal_elements_have_equal_inverses b d;
  let ha = g.add_monoid.add_semigroup.has_add in
  ha.congruence a (-b) c (-d);
  let eq : equatable t = ha.eq in
  eq.transitivity (a - b) (a + (-b)) (c + (-d));
  eq.symmetry (c - d) (c + (-d));
  eq.transitivity (a - b) (c + (-d)) (c - d)
#pop-options

// Congruence of subtraction in a field context, clean SMT context
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let sub_congruence_field (#t:Type) {|f: field t|} (a b c d: t)
  : Lemma (requires f.division_ring.domain.ring.add_comm_group.add_group
                     .add_monoid.add_semigroup.has_add.eq.op_Equals a c = true /\
                    f.division_ring.domain.ring.add_comm_group.add_group
                     .add_monoid.add_semigroup.has_add.eq.op_Equals b d = true)
          (ensures f.division_ring.domain.ring.add_comm_group.add_group
                    .add_monoid.add_semigroup.has_add.eq.op_Equals (a - b) (c - d) = true) =
  let r = f.division_ring.domain.ring in
  let ag = r.add_comm_group.add_group in
  sub_congruence #t #ag a b c d
#pop-options

// Transitivity in a field context, clean SMT context  
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let eq_transitivity_field (#t:Type) {|f: field t|} (a b c: t)
  : Lemma (requires f.division_ring.domain.ring.add_comm_group.add_group
                     .add_monoid.add_semigroup.has_add.eq.op_Equals a b = true /\
                    f.division_ring.domain.ring.add_comm_group.add_group
                     .add_monoid.add_semigroup.has_add.eq.op_Equals b c = true)
          (ensures f.division_ring.domain.ring.add_comm_group.add_group
                    .add_monoid.add_semigroup.has_add.eq.op_Equals a c = true) =
  let r = f.division_ring.domain.ring in
  let ag_eq = r.add_comm_group.add_group.add_monoid.add_semigroup.has_add.eq in
  ag_eq.transitivity a b c
#pop-options

// Multiplication congruence in a field context, clean SMT context
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let mul_congruence_field (#t:Type) {|f: field t|} (a b c d: t)
  : Lemma (requires f.division_ring.domain.ring.add_comm_group.add_group
                     .add_monoid.add_semigroup.has_add.eq.op_Equals a c = true /\
                    f.division_ring.domain.ring.add_comm_group.add_group
                     .add_monoid.add_semigroup.has_add.eq.op_Equals b d = true)
          (ensures f.division_ring.domain.ring.add_comm_group.add_group
                    .add_monoid.add_semigroup.has_add.eq.op_Equals (a * b) (c * d) = true) =
  let r = f.division_ring.domain.ring in
  let hm = r.semiring.mul_monoid.mul_semigroup.has_mul in
  hm.congruence a b c d
#pop-options

// Right absorption (c * 0 = 0) in a field context, clean SMT context
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let right_absorption_field (#t:Type) {|f: field t|} (c: t)
  : Lemma (f.division_ring.domain.ring.add_comm_group.add_group
            .add_monoid.add_semigroup.has_add.eq.op_Equals
            (c * f.division_ring.domain.ring.add_comm_group.add_group.add_monoid.has_zero.zero)
            f.division_ring.domain.ring.add_comm_group.add_group.add_monoid.has_zero.zero = true) =
  let r = f.division_ring.domain.ring in
  r.semiring.right_absorption c
#pop-options

// Reflexivity in a field context, clean SMT context
#push-options "--fuel 1 --ifuel 1 --z3rlimit 30"
let reflexivity_field (#t:Type) {|f: field t|} (x: t)
  : Lemma (f.division_ring.domain.ring.add_comm_group.add_group
            .add_monoid.add_semigroup.has_add.eq.op_Equals x x = true) =
  let r = f.division_ring.domain.ring in
  r.add_comm_group.add_group.add_monoid.add_semigroup.has_add.eq.reflexivity x
#pop-options

// Wrap coeff_at_scalar_mul to produce postcondition in ag_eq terms
#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
let coeff_at_scalar_mul_field (#t:Type) {|f: field t|} (c: t) (p: polynomial t) (i: nat)
  : Lemma (ensures f.division_ring.domain.ring.add_comm_group.add_group
                    .add_monoid.add_semigroup.has_add.eq.op_Equals
                    (coeff_at #t #(f.division_ring.domain.ring.add_comm_group.add_group.add_monoid.has_zero)
                      (scalar_mul c p) i)
                    (c * coeff_at #t #(f.division_ring.domain.ring.add_comm_group.add_group.add_monoid.has_zero)
                      p i) = true) =
  let sr = f.division_ring.domain.ring.semiring in
  coeff_at_scalar_mul #t #sr c p i
#pop-options

// Wrap coeff_at_poly_sub to produce postcondition in ag_eq terms
#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
let coeff_at_poly_sub_field (#t:Type) {|f: field t|} (p q: polynomial t) (i: nat)
  : Lemma (ensures f.division_ring.domain.ring.add_comm_group.add_group
                    .add_monoid.add_semigroup.has_add.eq.op_Equals
                    (coeff_at #t #(f.division_ring.domain.ring.add_comm_group.add_group.add_monoid.has_zero)
                      (poly_sub p q) i)
                    (coeff_at #t #(f.division_ring.domain.ring.add_comm_group.add_group.add_monoid.has_zero)
                      p i -
                     coeff_at #t #(f.division_ring.domain.ring.add_comm_group.add_group.add_monoid.has_zero)
                      q i) = true) =
  let g = f.division_ring.domain.ring.add_comm_group in
  coeff_at_poly_sub #t #g p q i
#pop-options

// Wrap coeff_above_degree_is_zero to produce postcondition in ag_eq terms
#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
let coeff_above_degree_field (#t:Type) {|f: field t|} (p: polynomial t) (i: nat)
  : Lemma (requires degree p == None \/ (Some? (degree p) /\ i > Some?.v (degree p)))
          (ensures f.division_ring.domain.ring.add_comm_group.add_group
                    .add_monoid.add_semigroup.has_add.eq.op_Equals
                    (coeff_at #t #(f.division_ring.domain.ring.add_comm_group.add_group.add_monoid.has_zero)
                      p i)
                    f.division_ring.domain.ring.add_comm_group.add_group.add_monoid.has_zero.zero = true) =
  let hz = f.division_ring.domain.ring.add_comm_group.add_group.add_monoid.has_zero in
  coeff_above_degree_is_zero #t #hz p i
#pop-options

(* Key helper: subtracting the leading term reduces the degree. *)

// Separate lemma for the i=dp case, to get a clean SMT context
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let leading_term_coeff_at_dp (#t:Type) {|f: field t|}
  (p q: polynomial t) (dp dq: nat)
  : Lemma (requires degree p == Some dp /\ degree q == Some dq /\ dp >= dq)
          (ensures (let r = f.division_ring.domain.ring in
                    let ag = r.add_comm_group.add_group in
                    let hz : has_zero t = ag.add_monoid.has_zero in
                    let eq : equatable t = hz.eq in
                    let shift : nat = Prims.op_Subtraction dp dq in
                    lc_nonzero_of_degree_some q;
                    let c = leading_coefficient p * f.division_ring.inv (leading_coefficient q) in
                    let p' = poly_sub p (scalar_mul c (poly_shift q shift)) in
                    eq.op_Equals (coeff_at #t #hz p' dp) hz.zero = true))
  = let r  = f.division_ring.domain.ring in
    let sr = r.semiring in
    let g  = r.add_comm_group in
    let ag = g.add_group in
    let hz : has_zero t = ag.add_monoid.has_zero in
    let eq : equatable t = hz.eq in
    let hm = sr.mul_monoid.mul_semigroup.has_mul in
    let shift : nat = Prims.op_Subtraction dp dq in
    lc_nonzero_of_degree_some q;
    let lc_p = leading_coefficient p in
    let lc_q = leading_coefficient q in
    let inv_lc_q = f.division_ring.inv lc_q in
    let c = lc_p * inv_lc_q in
    let sq = scalar_mul c (poly_shift q shift) in
    let p' = poly_sub p sq in
    // Coefficient extraction
    coeff_at_poly_sub #t #g p sq dp;
    coeff_at_scalar_mul #t #sr c (poly_shift q shift) dp;
    coeff_at_poly_shift #t #hz q shift dp;
    coeff_at_degree_eq_lc #t #hz p;
    coeff_at_degree_eq_lc #t #hz q;
    // Show c * lc_q = lc_p
    sr.mul_monoid.mul_semigroup.associativity lc_p inv_lc_q lc_q;
    eq.reflexivity lc_p;
    hm.congruence lc_p (inv_lc_q * lc_q) lc_p one;
    eq.transitivity (c * lc_q) (lc_p * (inv_lc_q * lc_q)) (lc_p * one);
    sr.mul_monoid.right_mul_identity lc_p;
    eq.transitivity (c * lc_q) (lc_p * one) lc_p;
    // Show c * coeff_at q dq = lc_p
    eq.reflexivity c;
    hm.congruence c (coeff_at #t #hz q dq) c lc_q;
    eq.transitivity (c * coeff_at #t #hz q dq) (c * lc_q) lc_p;
    // Chain: coeff_at sq dp = lc_p
    eq_transitivity_field #t #f (coeff_at #t #hz sq dp) (c * coeff_at #t #hz q dq) lc_p;
    // Congruence: (coeff p dp) - (coeff sq dp) = lc_p - lc_p
    sub_congruence_field #t #f (coeff_at #t #hz p dp) (coeff_at #t #hz sq dp) lc_p lc_p;
    // lc_p - lc_p = zero
    sub_self_via_field #t #f lc_p;
    // Chain: sub(coeff p, coeff sq) = lc_p - lc_p = zero
    eq_transitivity_field #t #f (coeff_at #t #hz p dp - coeff_at #t #hz sq dp) (lc_p - lc_p) hz.zero;
    // Chain: coeff_at p' dp = sub(coeff p, coeff sq) = zero
    eq.symmetry (coeff_at #t #hz p' dp) (coeff_at #t #hz p dp - coeff_at #t #hz sq dp);
    eq_transitivity_field #t #f (coeff_at #t #hz p' dp) (coeff_at #t #hz p dp - coeff_at #t #hz sq dp) hz.zero
#pop-options

// Separate lemma for the i>dp case  
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let leading_term_coeff_above_dp (#t:Type) {|f: field t|}
  (p q: polynomial t) (dp dq: nat) (i: nat)
   : Lemma (requires degree p == Some dp /\ degree q == Some dq /\ dp >= dq /\ i > dp)
          (ensures (let r = f.division_ring.domain.ring in
                    let ag = r.add_comm_group.add_group in
                    let hz : has_zero t = ag.add_monoid.has_zero in
                    let eq : equatable t = hz.eq in
                    let shift : nat = Prims.op_Subtraction dp dq in
                    lc_nonzero_of_degree_some q;
                    let c = leading_coefficient p * f.division_ring.inv (leading_coefficient q) in
                    let p' = poly_sub p (scalar_mul c (poly_shift q shift)) in
                    eq.op_Equals (coeff_at #t #hz p' i) hz.zero = true))
  = let r  = f.division_ring.domain.ring in
    let sr = r.semiring in
    let g  = r.add_comm_group in
    let ag = g.add_group in
    let hz : has_zero t = ag.add_monoid.has_zero in
    let eq : equatable t = hz.eq in
    let shift : nat = Prims.op_Subtraction dp dq in
    lc_nonzero_of_degree_some q;
    let c = leading_coefficient p * f.division_ring.inv (leading_coefficient q) in
    let sq = scalar_mul c (poly_shift q shift) in
    let p' = poly_sub p sq in
    let j : nat = Prims.op_Subtraction i shift in
    // All lemma calls use field-wrapped versions (same ag_eq in postconditions)
    coeff_at_poly_shift #t #hz q shift i;
    coeff_at_poly_sub_field #t #f p sq i;
    coeff_at_scalar_mul_field #t #f c (poly_shift q shift) i;
    coeff_above_degree_field #t #f p i;
    coeff_above_degree_field #t #f q j;
    // Chain: coeff sq i = c * coeff(poly_shift q shift, i) = c * coeff(q,j) = c*0 = 0
    reflexivity_field #t #f c;
    reflexivity_field #t #f (coeff_at #t #hz q j);
    mul_congruence_field #t #f c (coeff_at #t #hz (poly_shift q shift) i) c (coeff_at #t #hz q j);
    eq_transitivity_field #t #f (coeff_at #t #hz sq i) (c * coeff_at #t #hz (poly_shift q shift) i) (c * coeff_at #t #hz q j);
    mul_congruence_field #t #f c (coeff_at #t #hz q j) c hz.zero;
    eq_transitivity_field #t #f (coeff_at #t #hz sq i) (c * coeff_at #t #hz q j) (c * hz.zero);
    right_absorption_field #t #f c;
    eq_transitivity_field #t #f (coeff_at #t #hz sq i) (c * hz.zero) hz.zero;
    // Congruence: (coeff p i) - (coeff sq i) = zero - zero
    sub_congruence_field #t #f (coeff_at #t #hz p i) (coeff_at #t #hz sq i) hz.zero hz.zero;
    sub_self_via_field #t #f hz.zero;
    eq_transitivity_field #t #f (coeff_at #t #hz p i - coeff_at #t #hz sq i) (hz.zero - hz.zero) hz.zero;
    eq.symmetry (coeff_at #t #hz p' i) (coeff_at #t #hz p i - coeff_at #t #hz sq i);
    eq_transitivity_field #t #f (coeff_at #t #hz p' i) (coeff_at #t #hz p i - coeff_at #t #hz sq i) hz.zero
#pop-options

(* Main lemma: subtracting the scaled leading term reduces degree *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let leading_term_sub_degree_lt (#t:Type) {|f: field t|}
  (p q: polynomial t) (dp dq: nat)
  : Lemma (requires (degree p == Some dp /\
                     degree q == Some dq /\
                     dp >= dq))
          (ensures (let shift : nat = Prims.op_Subtraction dp dq in
                    lc_nonzero_of_degree_some q;
                    let c = leading_coefficient p * f.division_ring.inv (leading_coefficient q) in
                    let p' = poly_sub p (scalar_mul c (poly_shift q shift)) in
                    (degree p' == None \/
                     (Some? (degree p') /\ Some?.v (degree p') < dp))))
  = let r  = f.division_ring.domain.ring in
    let ag = r.add_comm_group.add_group in
    let hz : has_zero t = ag.add_monoid.has_zero in
    let eq : equatable t = hz.eq in
    let shift : nat = Prims.op_Subtraction dp dq in
    lc_nonzero_of_degree_some q;
    let c = leading_coefficient p * f.division_ring.inv (leading_coefficient q) in
    let p' = poly_sub p (scalar_mul c (poly_shift q shift)) in
    let aux (i: nat{i >= dp})
      : Lemma (coeff_at #t #hz p' i `eq.op_Equals` hz.zero)
      = if i > dp then
          leading_term_coeff_above_dp #t #f p q dp dq i
        else
          leading_term_coeff_at_dp #t #f p q dp dq
    in
    Classical.forall_intro (Classical.move_requires aux);
    degree_lt_from_coeff_zero #t #hz p' dp
#pop-options

(* ====================================================================== *)
(*  Correctness proof for Euclidean division                                *)
(* ====================================================================== *)

(* poly_mul (poly_shift [c] k) q ≡ poly_shift (scalar_mul c q) k *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec poly_mul_shift_singleton (#t:Type) {| f: field t |}
  (c: t) (q: polynomial t) (k: nat)
  : Lemma (ensures (let sr = f.division_ring.domain.ring.semiring in
                    let hz = semiring_has_zero sr in
                    poly_eq #t #hz
                      (poly_mul #t #sr (poly_shift #t #hz [c] k) q)
                      (poly_shift #t #hz (scalar_mul #t #sr c q) k)))
          (decreases k)
  = let sr = f.division_ring.domain.ring.semiring in
    let hz = semiring_has_zero sr in
    semiring_has_zero_unfold sr;
    if k = 0 then
      poly_mul_singleton #t #sr c q
    else begin
      let k' = Prims.op_Subtraction k 1 in
      poly_mul_cons_zero #t #sr (poly_shift #t #hz [c] k') q;
      poly_mul_shift_singleton c q k';
      hz.eq.reflexivity zero;
      cons_congruence #t #hz zero zero
        (poly_mul #t #sr (poly_shift #t #hz [c] k') q)
        (poly_shift #t #hz (scalar_mul #t #sr c q) k');
      poly_eq_transitivity #t #hz
        (poly_mul #t #sr (poly_shift #t #hz [c] k) q)
        (zero :: poly_mul #t #sr (poly_shift #t #hz [c] k') q)
        (poly_shift #t #hz (scalar_mul #t #sr c q) k)
    end
#pop-options

(* scalar_mul c (poly_shift q k) ≡ poly_shift (scalar_mul c q) k *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 50"
let rec scalar_mul_shift_comm (#t:Type) {| f: field t |}
  (c: t) (q: polynomial t) (k: nat)
  : Lemma (ensures (let sr = f.division_ring.domain.ring.semiring in
                    let hz = semiring_has_zero sr in
                    poly_eq #t #hz
                      (scalar_mul #t #sr c (poly_shift #t #hz q k))
                      (poly_shift #t #hz (scalar_mul #t #sr c q) k)))
          (decreases k)
  = let sr = f.division_ring.domain.ring.semiring in
    let hz = semiring_has_zero sr in
    semiring_has_zero_unfold sr;
    if k = 0 then
      poly_eq_reflexivity #t #hz (scalar_mul #t #sr c q)
    else begin
      let k' = Prims.op_Subtraction k 1 in
      scalar_mul_cons_zero #t #sr c (poly_shift #t #hz q k');
      scalar_mul_shift_comm c q k';
      hz.eq.reflexivity zero;
      cons_congruence #t #hz zero zero
        (scalar_mul #t #sr c (poly_shift #t #hz q k'))
        (poly_shift #t #hz (scalar_mul #t #sr c q) k');
      poly_eq_transitivity #t #hz
        (scalar_mul #t #sr c (poly_shift #t #hz q k))
        (zero :: scalar_mul #t #sr c (poly_shift #t #hz q k'))
        (poly_shift #t #hz (scalar_mul #t #sr c q) k)
    end
#pop-options

(* scalar_mul c (poly_shift q k) ≡ poly_mul q (poly_shift [c] k)
   — via shift_singleton + commutativity *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let scalar_mul_as_poly_mul (#t:Type) {| f: field t |}
  (c: t) (q: polynomial t) (k: nat)
  : Lemma (ensures (let sr = f.division_ring.domain.ring.semiring in
                    let hz = semiring_has_zero sr in
                    poly_eq #t #hz
                      (scalar_mul #t #sr c (poly_shift #t #hz q k))
                      (poly_mul #t #sr q (poly_shift #t #hz [c] k))))
  = let sr = f.division_ring.domain.ring.semiring in
    let hz = semiring_has_zero sr in
    let cr = f.commutative_ring in
    semiring_has_zero_unfold sr;
    scalar_mul_shift_comm c q k;
    poly_mul_shift_singleton c q k;
    poly_eq_symmetry #t #hz
      (poly_mul #t #sr (poly_shift #t #hz [c] k) q)
      (poly_shift #t #hz (scalar_mul #t #sr c q) k);
    poly_mul_commutative #t #cr (poly_shift #t #hz [c] k) q;
    poly_eq_transitivity #t #hz
      (scalar_mul #t #sr c (poly_shift #t #hz q k))
      (poly_shift #t #hz (scalar_mul #t #sr c q) k)
      (poly_mul #t #sr (poly_shift #t #hz [c] k) q);
    poly_eq_transitivity #t #hz
      (scalar_mul #t #sr c (poly_shift #t #hz q k))
      (poly_mul #t #sr (poly_shift #t #hz [c] k) q)
      (poly_mul #t #sr q (poly_shift #t #hz [c] k))
#pop-options

(* Base case helper for correctness proof *)
let base_case (#t:Type) {| f: field t |} (q p: polynomial t)
  (sr: semiring t) (hz: has_zero t)
  : Lemma (requires sr == f.division_ring.domain.ring.semiring /\
                    hz == semiring_has_zero sr)
          (ensures poly_eq #t #hz (poly_add (poly_mul q poly_zero) p) p)
  = semiring_has_zero_unfold sr;
    poly_mul_zero_right #t #sr q;
    poly_eq_reflexivity #t #hz p;
    poly_add_congruence (poly_mul q poly_zero) p (poly_zero #t) p;
    poly_add_left_identity p;
    poly_eq_transitivity #t #hz
      (poly_add (poly_mul q poly_zero) p) (poly_add (poly_zero #t) p) p

(* Correctness of poly_divmod_aux: q * quot + rem ≡ p *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let rec poly_divmod_aux_correct (#t:Type) {| f: field t |}
  (p q: polynomial t) (fuel: nat)
  : Lemma (requires Some? (degree q))
          (ensures (let sr = f.division_ring.domain.ring.semiring in
                    let hz = semiring_has_zero sr in
                    let (quot, rem) = poly_divmod_aux p q fuel in
                    poly_eq #t #hz (poly_add (poly_mul q quot) rem) p))
          (decreases fuel)
  = let sr = f.division_ring.domain.ring.semiring in
    let hz = semiring_has_zero sr in
    semiring_has_zero_unfold sr;
    if fuel = 0 then base_case q p sr hz
    else
      match degree p, degree q with
      | None, _ -> base_case q p sr hz
      | _, None -> base_case q p sr hz
      | Some dp, Some dq ->
        if dp < dq then base_case q p sr hz
        else begin
          lc_nonzero_of_degree_some q;
          let lc_p = leading_coefficient p in
          let lc_q = leading_coefficient q in
          let inv_lc_q : t = f.division_ring.inv lc_q in
          let c : t = lc_p * inv_lc_q in
          let shift : nat = Prims.op_Subtraction dp dq in
          let t_poly = scalar_mul c (poly_shift q shift) in
          let p' = poly_sub p t_poly in
          let (q', r) = poly_divmod_aux p' q (Prims.op_Subtraction fuel 1) in
          let sh_c = poly_shift #t #hz [c] shift in
          let quot = poly_add sh_c q' in
          poly_divmod_aux_correct p' q (Prims.op_Subtraction fuel 1);
          scalar_mul_as_poly_mul c q shift;
          poly_add_sub_cancel t_poly p;
          poly_mul_right_distrib #t #sr q sh_c q';
          poly_eq_reflexivity #t #hz r;
          poly_add_congruence
            (poly_mul q (poly_add sh_c q')) r
            (poly_add (poly_mul q sh_c) (poly_mul q q')) r;
          poly_add_associative (poly_mul q sh_c) (poly_mul q q') r;
          poly_eq_transitivity #t #hz
            (poly_add (poly_mul q quot) r)
            (poly_add (poly_add (poly_mul q sh_c) (poly_mul q q')) r)
            (poly_add (poly_mul q sh_c) (poly_add (poly_mul q q') r));
          poly_eq_reflexivity #t #hz (poly_mul q sh_c);
          poly_add_congruence
            (poly_mul q sh_c) (poly_add (poly_mul q q') r) (poly_mul q sh_c) p';
          poly_eq_transitivity #t #hz
            (poly_add (poly_mul q quot) r)
            (poly_add (poly_mul q sh_c) (poly_add (poly_mul q q') r))
            (poly_add (poly_mul q sh_c) p');
          poly_eq_symmetry #t #hz t_poly (poly_mul q sh_c);
          poly_eq_reflexivity #t #hz p';
          poly_add_congruence (poly_mul q sh_c) p' t_poly p';
          poly_eq_transitivity #t #hz
            (poly_add (poly_mul q quot) r) (poly_add (poly_mul q sh_c) p') (poly_add t_poly p');
          poly_eq_transitivity #t #hz
            (poly_add (poly_mul q quot) r) (poly_add t_poly p') p
        end
#pop-options

(* Top-level correctness: q * div(p,q) + mod(p,q) ≡ p *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let poly_divmod_correct (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires Some? (degree q))
          (ensures (let sr = f.division_ring.domain.ring.semiring in
                    let hz = semiring_has_zero sr in
                    poly_eq #t #hz
                      (poly_add (poly_mul q (poly_div p q)) (poly_mod p q)) p))
  = let sr = f.division_ring.domain.ring.semiring in
    semiring_has_zero_unfold sr;
    let fuel : nat =
      match degree p with
      | None -> 1
      | Some dp -> Prims.op_Addition dp 1
    in
    poly_divmod_aux_correct p q fuel
#pop-options

(* Degree bound for poly_divmod_aux remainder *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let rec poly_divmod_aux_degree (#t:Type) {| f: field t |}
  (p q: polynomial t) (fuel: nat)
  : Lemma (requires (let hz = semiring_has_zero f.division_ring.domain.ring.semiring in
                     Some? (degree #t #hz q) /\
                     (degree #t #hz p == None \/
                      Some?.v (degree #t #hz p) < Some?.v (degree #t #hz q) \/
                      fuel > Prims.op_Subtraction (Some?.v (degree #t #hz p)) (Some?.v (degree #t #hz q)))))
          (ensures (let hz = semiring_has_zero f.division_ring.domain.ring.semiring in
                    let dq = Some?.v (degree #t #hz q) in
                    let (_, rem) = poly_divmod_aux p q fuel in
                    degree #t #hz rem == None \/
                    (Some? (degree #t #hz rem) /\ Some?.v (degree #t #hz rem) < dq)))
          (decreases fuel)
  = let sr = f.division_ring.domain.ring.semiring in
    let hz = semiring_has_zero sr in
    semiring_has_zero_unfold sr;
    if fuel = 0 then ()
    else
      match degree #t #hz p, degree #t #hz q with
      | None, _ -> ()
      | _, None -> ()
      | Some dp, Some dq ->
        if dp < dq then ()
        else begin
          lc_nonzero_of_degree_some q;
          let lc_p = leading_coefficient p in
          let lc_q = leading_coefficient q in
          let inv_lc_q : t = f.division_ring.inv lc_q in
          let c : t = lc_p * inv_lc_q in
          let shift : nat = Prims.op_Subtraction dp dq in
          let t_poly = scalar_mul c (poly_shift q shift) in
          let p' = poly_sub p t_poly in
          leading_term_sub_degree_lt p q dp dq;
          poly_divmod_aux_degree p' q (Prims.op_Subtraction fuel 1)
        end
#pop-options

(* Top-level degree bound: degree(mod(p,q)) < degree(q) *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let poly_divmod_degree (#t:Type) {| f: field t |} (p q: polynomial t)
  : Lemma (requires Some? (degree q))
          (ensures (let rem = poly_mod p q in
                    degree rem == None \/
                    (Some? (degree rem) /\ Some?.v (degree rem) < Some?.v (degree q))))
  = let sr = f.division_ring.domain.ring.semiring in
    semiring_has_zero_unfold sr;
    let fuel : nat =
      match degree p with
      | None -> 1
      | Some dp -> Prims.op_Addition dp 1
    in
    poly_divmod_aux_degree p q fuel
#pop-options

(* ====================================================================== *)
(*  Uniqueness of Euclidean division and poly_mod congruence              *)
(* ====================================================================== *)

(* poly_add_neg_cancel_right: (a + b) + (-b) ≡ a *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let poly_add_neg_cancel_right (#t:Type) {| g: add_comm_group t |} (a b: polynomial t)
  : Lemma (ensures (let hz = g.add_group.add_monoid.has_zero in
                    poly_eq #t #hz (poly_add (poly_add a b) (poly_neg b)) a))
  = let am = g.add_group.add_monoid in
    let hz = am.has_zero in
    poly_neg_inversion #t #g b;
    poly_add_associative #t #am a b (poly_neg b);
    poly_eq_reflexivity #t #hz a;
    poly_add_congruence #t #am a (poly_add b (poly_neg b)) a (poly_zero #t);
    poly_add_right_identity #t #am a;
    poly_eq_transitivity #t #hz (poly_add (poly_add a b) (poly_neg b))
      (poly_add a (poly_add b (poly_neg b))) (poly_add a (poly_zero #t));
    poly_eq_transitivity #t #hz (poly_add (poly_add a b) (poly_neg b))
      (poly_add a (poly_zero #t)) a
#pop-options

(* poly_inverse_unique: a+b≡0 ∧ a+c≡0 → b≡c *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let poly_inverse_unique (#t:Type) {| g: add_comm_group t |} (a b c: polynomial t)
  : Lemma (requires (let hz = g.add_group.add_monoid.has_zero in
                     poly_eq #t #hz (poly_add a b) (poly_zero #t) /\
                     poly_eq #t #hz (poly_add a c) (poly_zero #t)))
          (ensures (let hz = g.add_group.add_monoid.has_zero in
                    poly_eq #t #hz b c))
  = let am = g.add_group.add_monoid in
    let hz = am.has_zero in
    poly_add_left_identity #t #am b;
    poly_neg_inversion #t #g a;
    poly_add_commutative #t #g.add_comm_monoid a (poly_neg a);
    poly_eq_symmetry #t #hz (poly_add a (poly_neg a)) (poly_add (poly_neg a) a);
    poly_eq_transitivity #t #hz (poly_add (poly_neg a) a) (poly_add a (poly_neg a)) (poly_zero #t);
    poly_eq_symmetry #t #hz (poly_add (poly_neg a) a) (poly_zero #t);
    poly_eq_reflexivity #t #hz b;
    poly_add_congruence #t #am (poly_zero #t) b (poly_add (poly_neg a) a) b;
    poly_add_associative #t #am (poly_neg a) a b;
    poly_eq_reflexivity #t #hz (poly_neg a);
    poly_add_congruence #t #am (poly_neg a) (poly_add a b) (poly_neg a) (poly_zero #t);
    poly_add_right_identity #t #am (poly_neg a);
    poly_eq_symmetry #t #hz (poly_add (poly_zero #t) b) b;
    poly_eq_transitivity #t #hz b (poly_add (poly_zero #t) b)
      (poly_add (poly_add (poly_neg a) a) b);
    poly_eq_transitivity #t #hz b (poly_add (poly_add (poly_neg a) a) b)
      (poly_add (poly_neg a) (poly_add a b));
    poly_eq_transitivity #t #hz b (poly_add (poly_neg a) (poly_add a b))
      (poly_add (poly_neg a) (poly_zero #t));
    poly_eq_transitivity #t #hz b (poly_add (poly_neg a) (poly_zero #t)) (poly_neg a);
    poly_add_congruence #t #am (poly_neg a) (poly_add a c) (poly_neg a) (poly_zero #t);
    poly_add_left_identity #t #am c;
    poly_eq_symmetry #t #hz (poly_add (poly_zero #t) c) c;
    poly_eq_reflexivity #t #hz c;
    poly_add_congruence #t #am (poly_zero #t) c (poly_add (poly_neg a) a) c;
    poly_eq_transitivity #t #hz c (poly_add (poly_zero #t) c)
      (poly_add (poly_add (poly_neg a) a) c);
    poly_add_associative #t #am (poly_neg a) a c;
    poly_eq_transitivity #t #hz c (poly_add (poly_add (poly_neg a) a) c)
      (poly_add (poly_neg a) (poly_add a c));
    poly_eq_transitivity #t #hz c (poly_add (poly_neg a) (poly_add a c))
      (poly_add (poly_neg a) (poly_zero #t));
    poly_eq_transitivity #t #hz c (poly_add (poly_neg a) (poly_zero #t)) (poly_neg a);
    poly_eq_symmetry #t #hz c (poly_neg a);
    poly_eq_transitivity #t #hz b (poly_neg a) c
#pop-options

(* poly_mul_neg: q * (-a) ≡ -(q * a) in ring context *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let poly_mul_neg (#t:Type) {| rng: ring t |} (q a: polynomial t)
  : Lemma (let sr = rng.semiring in
           let hz = semiring_has_zero sr in
           poly_eq #t #hz (poly_mul q (poly_neg a)) (poly_neg (poly_mul q a)))
  = let sr = rng.semiring in
    let hz = semiring_has_zero sr in
    let g = rng.add_comm_group in
    let ag = g.add_group in
    semiring_has_zero_unfold sr;
    poly_neg_inversion #t #g a;
    poly_eq_reflexivity #t #hz q;
    poly_mul_right_distrib #t #sr q a (poly_neg a);
    poly_eq_symmetry #t #hz (poly_mul q (poly_add a (poly_neg a)))
      (poly_add (poly_mul q a) (poly_mul q (poly_neg a)));
    poly_mul_zero_right #t #sr q;
    poly_mul_congruence #t #sr q (poly_add a (poly_neg a)) q (poly_zero #t);
    poly_eq_transitivity #t #hz (poly_add (poly_mul q a) (poly_mul q (poly_neg a)))
      (poly_mul q (poly_add a (poly_neg a))) (poly_mul q (poly_zero #t));
    poly_eq_transitivity #t #hz (poly_add (poly_mul q a) (poly_mul q (poly_neg a)))
      (poly_mul q (poly_zero #t)) (poly_zero #t);
    poly_neg_inversion #t #g (poly_mul q a);
    poly_inverse_unique #t #g (poly_mul q a) (poly_mul q (poly_neg a)) (poly_neg (poly_mul q a))
#pop-options

(* add_rearrange: x+r1 ≡ y+r2 → (x-y) ≡ (r2-r1) *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let add_rearrange (#t:Type) {| g: add_comm_group t |} (x y r1 r2: polynomial t)
  : Lemma (requires (let hz = g.add_group.add_monoid.has_zero in
                     poly_eq #t #hz (poly_add x r1) (poly_add y r2)))
          (ensures (let hz = g.add_group.add_monoid.has_zero in
                    poly_eq #t #hz (poly_sub x y) (poly_sub r2 r1)))
  = let ag = g.add_group in
    let am = ag.add_monoid in
    let hz = am.has_zero in
    // Step 1: add (-r1) to both sides on the right
    // (x+r1)+(-r1) ≡ (y+r2)+(-r1)
    poly_eq_reflexivity #t #hz (poly_neg r1);
    poly_add_congruence #t #am (poly_add x r1) (poly_neg r1) (poly_add y r2) (poly_neg r1);
    // LHS: (x+r1)+(-r1) ≡ x [cancel_right]
    poly_add_neg_cancel_right #t #g x r1;
    // RHS: (y+r2)+(-r1)
    // = y + (r2 + (-r1)) [assoc]
    poly_add_associative #t #am y r2 (poly_neg r1);
    // = y + sub(r2, r1) [sub_def]
    poly_sub_def #t #g r2 r1;
    poly_eq_symmetry #t #hz (poly_sub r2 r1) (poly_add r2 (poly_neg r1));
    poly_eq_reflexivity #t #hz y;
    poly_add_congruence #t #am y (poly_add r2 (poly_neg r1)) y (poly_sub r2 r1);
    poly_eq_transitivity #t #hz (poly_add (poly_add y r2) (poly_neg r1))
      (poly_add y (poly_add r2 (poly_neg r1))) (poly_add y (poly_sub r2 r1));
    // So: x ≡ (x+r1)+(-r1) ≡ (y+r2)+(-r1) ≡ y + sub(r2,r1)
    poly_eq_symmetry #t #hz (poly_add (poly_add x r1) (poly_neg r1)) x;
    poly_eq_transitivity #t #hz x (poly_add (poly_add x r1) (poly_neg r1))
      (poly_add (poly_add y r2) (poly_neg r1));
    poly_eq_transitivity #t #hz x (poly_add (poly_add y r2) (poly_neg r1))
      (poly_add y (poly_sub r2 r1));
    // Step 2: add (-y) to both sides on the right
    // x + (-y) ≡ (y + sub(r2,r1)) + (-y)
    poly_eq_reflexivity #t #hz (poly_neg y);
    poly_add_congruence #t #am x (poly_neg y) (poly_add y (poly_sub r2 r1)) (poly_neg y);
    // LHS: x + (-y) = sub(x,y)
    poly_sub_def #t #g x y;
    poly_eq_symmetry #t #hz (poly_sub x y) (poly_add x (poly_neg y));
    // RHS: (y + sub(r2,r1)) + (-y) ≡ sub(r2,r1)
    // Use commutativity: y + s ≡ s + y, then cancel_right
    poly_add_commutative #t #g.add_comm_monoid y (poly_sub r2 r1);
    poly_eq_reflexivity #t #hz (poly_neg y);
    poly_add_congruence #t #am (poly_add y (poly_sub r2 r1)) (poly_neg y)
      (poly_add (poly_sub r2 r1) y) (poly_neg y);
    poly_add_neg_cancel_right #t #g (poly_sub r2 r1) y;
    // (y+s)+(-y) ≡ (s+y)+(-y) ≡ s
    // Chain: sub(x,y) ≡ x+(-y) ≡ (y+sub(r2,r1))+(-y) ≡ (sub(r2,r1)+y)+(-y) ≡ sub(r2,r1)
    poly_eq_transitivity #t #hz (poly_sub x y) (poly_add x (poly_neg y))
      (poly_add (poly_add y (poly_sub r2 r1)) (poly_neg y));
    poly_eq_transitivity #t #hz (poly_sub x y)
      (poly_add (poly_add y (poly_sub r2 r1)) (poly_neg y))
      (poly_add (poly_add (poly_sub r2 r1) y) (poly_neg y));
    poly_eq_transitivity #t #hz (poly_sub x y)
      (poly_add (poly_add (poly_sub r2 r1) y) (poly_neg y)) (poly_sub r2 r1)
#pop-options

(* poly_mul_sub_distrib: q*(a-b) ≡ q*a - q*b *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let poly_mul_sub_distrib (#t:Type) {| rng: ring t |} (q a b: polynomial t)
  : Lemma (let sr = rng.semiring in let hz = semiring_has_zero sr in
           poly_eq #t #hz (poly_mul q (poly_sub a b)) (poly_sub (poly_mul q a) (poly_mul q b)))
  = let sr = rng.semiring in
    let hz = semiring_has_zero sr in
    let g = rng.add_comm_group in
    let ag = g.add_group in
    semiring_has_zero_unfold sr;
    // sub(a,b) = a + (-b)
    poly_sub_def #t #g a b;
    // q * sub(a,b) ≡ q * (a + (-b)) [congruence]
    poly_eq_reflexivity #t #hz q;
    poly_mul_congruence #t #sr q (poly_sub a b) q (poly_add a (poly_neg b));
    // q * (a + (-b)) ≡ q*a + q*(-b) [distrib]
    poly_mul_right_distrib #t #sr q a (poly_neg b);
    // q*(-b) ≡ -(q*b) [mul_neg]
    poly_mul_neg #t #rng q b;
    // q*a + q*(-b) ≡ q*a + (-(q*b)) [congruence]
    poly_eq_reflexivity #t #hz (poly_mul q a);
    poly_add_congruence #t #g.add_group.add_monoid (poly_mul q a) (poly_mul q (poly_neg b))
      (poly_mul q a) (poly_neg (poly_mul q b));
    poly_sub_def #t #g (poly_mul q a) (poly_mul q b);
    poly_eq_symmetry #t #hz (poly_sub (poly_mul q a) (poly_mul q b))
      (poly_add (poly_mul q a) (poly_neg (poly_mul q b)));
    // Chain
    poly_eq_transitivity #t #hz (poly_mul q (poly_sub a b))
      (poly_mul q (poly_add a (poly_neg b)))
      (poly_add (poly_mul q a) (poly_mul q (poly_neg b)));
    poly_eq_transitivity #t #hz (poly_mul q (poly_sub a b))
      (poly_add (poly_mul q a) (poly_mul q (poly_neg b)))
      (poly_add (poly_mul q a) (poly_neg (poly_mul q b)));
    poly_eq_transitivity #t #hz (poly_mul q (poly_sub a b))
      (poly_add (poly_mul q a) (poly_neg (poly_mul q b)))
      (poly_sub (poly_mul q a) (poly_mul q b))
#pop-options

(* zero_minus_zero_is_zero: a=0 ∧ b=0 → a-b=0 (element level, ring) *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
let zero_minus_zero_is_zero (#t:Type) {| f: field t |} (a b: t)
  : Lemma (requires (let ag = f.division_ring.domain.ring.add_comm_group.add_group in
                     let ha = ag.add_monoid.add_semigroup.has_add in
                     let z = ag.add_monoid.has_zero.zero in
                     ha.eq.op_Equals a z /\ ha.eq.op_Equals b z))
          (ensures (let ag = f.division_ring.domain.ring.add_comm_group.add_group in
                    let ha = ag.add_monoid.add_semigroup.has_add in
                    let z = ag.add_monoid.has_zero.zero in
                    ha.eq.op_Equals (a - b) z))
  = let rng = f.division_ring.domain.ring in
    let g = rng.add_comm_group.add_group in
    let am = g.add_monoid in
    let ha = am.add_semigroup.has_add in
    let eq = ha.eq in
    let z = am.has_zero.zero in
    // a - b = a + (-b)
    g.subtraction_definition a b;
    // b + (-b) = z (group inverse)
    g.negation b;
    // b = z, so z + (-b) = b + (-b) via congruence
    eq.reflexivity (-b);
    eq.symmetry b z;
    ha.congruence z (-b) b (-b);
    eq.transitivity (z + (-b)) (b + (-b)) z;
    // a = z, so a + (-b) = z + (-b) via congruence
    ha.congruence a (-b) z (-b);
    eq.transitivity (a + (-b)) (z + (-b)) z;
    // a - b = a + (-b) = z
    eq.symmetry (a - b) (a + (-b));
    eq.transitivity (a - b) (a + (-b)) z
#pop-options

(* poly_sub_coeff_zero_upper_bound: for any i >= n, coeff_at(sub r2 r1, i) = 0 *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 120"
let poly_sub_coeff_zero_upper_bound (#t:Type) {| f: field t |} (r1 r2: polynomial t) (n: nat) (i: nat)
  : Lemma (requires (let sr = f.division_ring.domain.ring.semiring in
                     let hz = semiring_has_zero sr in
                     i >= n /\
                     (degree #t #hz r1 == None \/ (Some? (degree #t #hz r1) /\ Some?.v (degree #t #hz r1) < n)) /\
                     (degree #t #hz r2 == None \/ (Some? (degree #t #hz r2) /\ Some?.v (degree #t #hz r2) < n))))
          (ensures (let ag = f.division_ring.domain.ring.add_comm_group.add_group in
                    let ag_hz = ag.add_monoid.has_zero in
                    ag_hz.eq.op_Equals (coeff_at #t #ag_hz (poly_sub r2 r1) i) ag_hz.zero = true))
  = let sr = f.division_ring.domain.ring.semiring in
    let hz = semiring_has_zero sr in
    semiring_has_zero_unfold sr;
    let ag = f.division_ring.domain.ring.add_comm_group.add_group in
    let am = ag.add_monoid in
    let ag_hz = am.has_zero in
    let ha = am.add_semigroup.has_add in
    let eq = ha.eq in
    assert (hz == ag_hz);
    assert (ag_hz.eq == eq);
    coeff_above_degree_is_zero #t #ag_hz r1 i;
    coeff_above_degree_is_zero #t #ag_hz r2 i;
    coeff_at_poly_sub_field #t #f r2 r1 i;
    zero_minus_zero_is_zero #t #f
      (coeff_at #t #ag_hz r2 i) (coeff_at #t #ag_hz r1 i);
    eq.transitivity (coeff_at #t #ag_hz (poly_sub r2 r1) i)
      (coeff_at #t #ag_hz r2 i - coeff_at #t #ag_hz r1 i) ag_hz.zero
#pop-options

(* degree_sub_bound: deg(r1)<n ∧ deg(r2)<n → deg(sub r2 r1)<n *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 120"
let degree_sub_bound (#t:Type) {| f: field t |} (r1 r2: polynomial t) (n: nat)
  : Lemma (requires (let hz = semiring_has_zero f.division_ring.domain.ring.semiring in
                     (degree #t #hz r1 == None \/ (Some? (degree #t #hz r1) /\ Some?.v (degree #t #hz r1) < n)) /\
                     (degree #t #hz r2 == None \/ (Some? (degree #t #hz r2) /\ Some?.v (degree #t #hz r2) < n))))
          (ensures (let hz = semiring_has_zero f.division_ring.domain.ring.semiring in
                    degree #t #hz (poly_sub r2 r1) == None \/
                    (Some? (degree #t #hz (poly_sub r2 r1)) /\ Some?.v (degree #t #hz (poly_sub r2 r1)) < n)))
  = let sr = f.division_ring.domain.ring.semiring in
    let hz = semiring_has_zero sr in
    semiring_has_zero_unfold sr;
    let ag = f.division_ring.domain.ring.add_comm_group.add_group in
    let ag_hz = ag.add_monoid.has_zero in
    assert (hz == ag_hz);
    let aux (i:nat) : Lemma (requires i >= n)
                             (ensures ag_hz.eq.op_Equals (coeff_at #t #ag_hz (poly_sub r2 r1) i) ag_hz.zero = true)
      = poly_sub_coeff_zero_upper_bound #t #f r1 r2 n i
    in
    Classical.forall_intro (Classical.move_requires aux);
    degree_lt_from_coeff_zero #t #ag_hz (poly_sub r2 r1) n
#pop-options

(* only_mul_zero_decreases_poly_degree: q*d ≡ s ∧ deg(s) < deg(q) → deg(d) = None *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let only_mul_zero_decreases_poly_degree (#t:Type) {| f: field t |} (q d s: polynomial t)
  : Lemma (requires (let hz = semiring_has_zero f.division_ring.domain.ring.semiring in
                     Some? (degree #t #hz q) /\
                     poly_eq #t #hz (poly_mul q d) s /\
                     (degree #t #hz s == None \/
                      (Some? (degree #t #hz s) /\ Some?.v (degree #t #hz s) < Some?.v (degree #t #hz q)))))
          (ensures (let hz = semiring_has_zero f.division_ring.domain.ring.semiring in
                    degree #t #hz d == None))
  = let sr = f.division_ring.domain.ring.semiring in
    let hz = semiring_has_zero sr in
    semiring_has_zero_unfold sr;
    let id : integral_domain t = {
      commutative_ring = f.commutative_ring;
      domain = f.division_ring.domain
    } in
    match degree #t #hz d with
    | None -> ()
    | Some dd ->
      degree_mul #t #id q d;
      degree_well_defined #t #hz (poly_mul q d) s
#pop-options

(* degree_none_poly_eq_zero: degree p == None → poly_eq p poly_zero *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let degree_none_poly_eq_zero (#t:Type) {| f: field t |} (p: polynomial t)
  : Lemma (requires (let hz = semiring_has_zero f.division_ring.domain.ring.semiring in
                     degree #t #hz p == None))
          (ensures (let hz = semiring_has_zero f.division_ring.domain.ring.semiring in
                    poly_eq #t #hz p (poly_zero #t)))
  = let sr = f.division_ring.domain.ring.semiring in
    let hz = semiring_has_zero sr in
    let am = sr.add_comm_monoid.add_monoid in
    semiring_has_zero_unfold sr;
    // degree None means all coefficients are zero
    let aux (i:nat) : Lemma (hz.eq.op_Equals (coeff_at p i) hz.zero) =
      coeff_above_degree_is_zero #t #hz p i
    in
    Classical.forall_intro aux;
    all_zero_of_coeff_zero #t #hz p;
    // p is all_zero. We need poly_eq p poly_zero.
    // poly_add_right_all_zero: poly_eq (add z p) z when all_zero p
    poly_add_right_all_zero #t #am (poly_zero #t) p;
    // poly_add_left_identity: poly_eq (add z p) p
    poly_add_left_identity #t #am p;
    // z+p ≡ z and z+p ≡ p, so p ≡ z+p ≡ z
    poly_eq_symmetry #t #hz (poly_add (poly_zero #t) p) p;
    poly_eq_transitivity #t #hz p (poly_add (poly_zero #t) p) (poly_zero #t)
#pop-options

(* sub_zero_implies_eq: poly_sub a b ≡ 0 → a ≡ b *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let sub_zero_implies_eq (#t:Type) {| g: add_comm_group t |} (a b: polynomial t)
  : Lemma (requires (let hz = g.add_group.add_monoid.has_zero in
                     poly_eq #t #hz (poly_sub a b) (poly_zero #t)))
          (ensures (let hz = g.add_group.add_monoid.has_zero in
                    poly_eq #t #hz a b))
  = let hz = g.add_group.add_monoid.has_zero in
    let am = g.add_group.add_monoid in
    poly_add_sub_cancel #t #g b a;
    poly_add_right_identity #t #am b;
    poly_eq_reflexivity #t #hz b;
    poly_add_congruence #t #am b (poly_sub a b) b (poly_zero #t);
    poly_eq_symmetry #t #hz (poly_add b (poly_sub a b)) a;
    poly_eq_transitivity #t #hz a (poly_add b (poly_sub a b)) (poly_add b (poly_zero #t));
    poly_eq_transitivity #t #hz a (poly_add b (poly_zero #t)) b
#pop-options

(* ===== UNIQUENESS OF EUCLIDEAN DIVISION ===== *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let poly_divmod_unique (#t:Type) {| f: field t |} (q a1 a2 r1 r2: polynomial t)
  : Lemma (requires (let sr = f.division_ring.domain.ring.semiring in
                     let hz = semiring_has_zero sr in
                     Some? (degree #t #hz q) /\
                     poly_eq #t #hz (poly_add (poly_mul q a1) r1) (poly_add (poly_mul q a2) r2) /\
                     (degree #t #hz r1 == None \/ (Some? (degree #t #hz r1) /\ Some?.v (degree #t #hz r1) < Some?.v (degree #t #hz q))) /\
                     (degree #t #hz r2 == None \/ (Some? (degree #t #hz r2) /\ Some?.v (degree #t #hz r2) < Some?.v (degree #t #hz q)))))
          (ensures (let sr = f.division_ring.domain.ring.semiring in
                    let hz = semiring_has_zero sr in
                    poly_eq #t #hz a1 a2 /\ poly_eq #t #hz r1 r2))
  = let sr = f.division_ring.domain.ring.semiring in
    let rng = f.division_ring.domain.ring in
    let g = rng.add_comm_group in
    let hz = semiring_has_zero sr in
    let am = g.add_group.add_monoid in
    semiring_has_zero_unfold sr;
    let dq = Some?.v (degree #t #hz q) in
    // Part A: a1 ≡ a2
    add_rearrange #t #g (poly_mul q a1) (poly_mul q a2) r1 r2;
    poly_mul_sub_distrib #t #rng q a1 a2;
    poly_eq_transitivity #t #hz (poly_mul q (poly_sub a1 a2))
      (poly_sub (poly_mul q a1) (poly_mul q a2)) (poly_sub r2 r1);
    degree_sub_bound #t #f r1 r2 dq;
    degree_well_defined #t #hz (poly_mul q (poly_sub a1 a2)) (poly_sub r2 r1);
    only_mul_zero_decreases_poly_degree #t #f q (poly_sub a1 a2) (poly_sub r2 r1);
    degree_none_poly_eq_zero #t #f (poly_sub a1 a2);
    sub_zero_implies_eq #t #g a1 a2;
    // Part B: r1 ≡ r2
    poly_eq_reflexivity #t #hz q;
    poly_mul_congruence #t #sr q a1 q a2;
    poly_eq_reflexivity #t #hz r1;
    poly_add_congruence #t #am (poly_mul q a1) r1 (poly_mul q a2) r1;
    poly_eq_symmetry #t #hz (poly_add (poly_mul q a1) r1) (poly_add (poly_mul q a2) r1);
    poly_eq_transitivity #t #hz
      (poly_add (poly_mul q a2) r1) (poly_add (poly_mul q a1) r1) (poly_add (poly_mul q a2) r2);
    poly_add_neg_cancel_right #t #g r1 (poly_mul q a2);
    poly_add_neg_cancel_right #t #g r2 (poly_mul q a2);
    poly_add_commutative #t #g.add_comm_monoid (poly_mul q a2) r1;
    poly_add_commutative #t #g.add_comm_monoid (poly_mul q a2) r2;
    poly_eq_reflexivity #t #hz (poly_neg (poly_mul q a2));
    poly_add_congruence #t #am (poly_add (poly_mul q a2) r1) (poly_neg (poly_mul q a2))
                               (poly_add r1 (poly_mul q a2)) (poly_neg (poly_mul q a2));
    poly_eq_transitivity #t #hz
      (poly_add (poly_add (poly_mul q a2) r1) (poly_neg (poly_mul q a2)))
      (poly_add (poly_add r1 (poly_mul q a2)) (poly_neg (poly_mul q a2))) r1;
    poly_add_congruence #t #am (poly_add (poly_mul q a2) r2) (poly_neg (poly_mul q a2))
                               (poly_add r2 (poly_mul q a2)) (poly_neg (poly_mul q a2));
    poly_eq_transitivity #t #hz
      (poly_add (poly_add (poly_mul q a2) r2) (poly_neg (poly_mul q a2)))
      (poly_add (poly_add r2 (poly_mul q a2)) (poly_neg (poly_mul q a2))) r2;
    poly_add_congruence #t #am
      (poly_add (poly_mul q a2) r1) (poly_neg (poly_mul q a2))
      (poly_add (poly_mul q a2) r2) (poly_neg (poly_mul q a2));
    poly_eq_symmetry #t #hz
      (poly_add (poly_add (poly_mul q a2) r1) (poly_neg (poly_mul q a2))) r1;
    poly_eq_transitivity #t #hz r1
      (poly_add (poly_add (poly_mul q a2) r1) (poly_neg (poly_mul q a2)))
      (poly_add (poly_add (poly_mul q a2) r2) (poly_neg (poly_mul q a2)));
    poly_eq_transitivity #t #hz r1
      (poly_add (poly_add (poly_mul q a2) r2) (poly_neg (poly_mul q a2))) r2
#pop-options

(* ===== POLY_MOD CONGRUENCE ===== *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"
let poly_mod_congruence (#t:Type) {| f: field t |} (p1 p2 q: polynomial t)
  : Lemma (requires Some? (degree q) /\
                     (let hz = semiring_has_zero f.division_ring.domain.ring.semiring in
                      poly_eq #t #hz p1 p2))
          (ensures (let hz = semiring_has_zero f.division_ring.domain.ring.semiring in
                    poly_eq #t #hz (poly_mod #t #f p1 q) (poly_mod #t #f p2 q)))
  = let sr = f.division_ring.domain.ring.semiring in
    let hz = semiring_has_zero sr in
    semiring_has_zero_unfold sr;
    poly_divmod_correct #t #f p1 q;
    poly_divmod_correct #t #f p2 q;
    poly_eq_symmetry #t #hz
      (poly_add (poly_mul q (poly_div p1 q)) (poly_mod p1 q)) p1;
    poly_eq_symmetry #t #hz
      (poly_add (poly_mul q (poly_div p2 q)) (poly_mod p2 q)) p2;
    poly_eq_transitivity #t #hz
      (poly_add (poly_mul q (poly_div p1 q)) (poly_mod p1 q)) p1 p2;
    poly_eq_transitivity #t #hz
      (poly_add (poly_mul q (poly_div p1 q)) (poly_mod p1 q)) p2
      (poly_add (poly_mul q (poly_div p2 q)) (poly_mod p2 q));
    poly_divmod_degree #t #f p1 q;
    poly_divmod_degree #t #f p2 q;
    poly_divmod_unique #t #f q (poly_div p1 q) (poly_div p2 q) (poly_mod p1 q) (poly_mod p2 q)
#pop-options