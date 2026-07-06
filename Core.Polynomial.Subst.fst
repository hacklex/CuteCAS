module Core.Polynomial.Subst

(* ================================================================ *)
(*  The substitution homomorphism  phi_h : t[X] -> t[X],  X |-> h.   *)
(*                                                                   *)
(*  Defined as the coefficient sum  phi_h(g) = Sum_i [coeff g i]*h^i  *)
(*  over the polynomial ring (mirroring Core.Polynomial.Eval, which   *)
(*  evaluates at a point IN the coefficient ring).  The coefficient   *)
(*  embedding  poly_const : t -> t[X],  c |-> [c],  is shown to be a ring  *)
(*  homomorphism; phi_h then inherits the ring-hom laws.              *)
(*                                                                   *)
(*  Unlocks the Berlekamp reverse splitting  f | prod_c (h - c)  by   *)
(*  substituting X |-> h in  X^p - X = prod_c (X - c).                *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module E  = Core.Polynomial.Eval
module CC = Core.Polynomial.Coeff
module CV = Core.FinSum

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Polynomial
open Core.Polynomial.Div
open Core.FinSum

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"


(* ================================================================ *)
(*  The substitution map  phi_h(g) = Sum_i [coeff g i] * h^i.        *)
(*  Everything lives in the polynomial ring t[X]; the polynomial     *)
(*  commutative_ring / add_comm_group instance (polynomial_cr) is    *)
(*  resolved by typeclass search, so sum_range, cpow and the         *)
(*  convolution lemmas all line up.                                  *)
(* ================================================================ *)

(* poly_const commutes with finite sums (named form: the polynomial-valued summand
   g is passed explicitly with a pointwise hypothesis g i ~ poly_const (f i),
   sidestepping lambda-unification against an internal `fun i -> poly_const (f i)`). *)
let rec poly_const_sum_range (#t:Type) {| cr: commutative_ring t |}
  (f: nat -> t) (g: nat -> polynomial t) (lo hi: nat)
  (hyp: (i:nat) -> Lemma (g i = poly_const (f i)))
  : Lemma (ensures poly_const (sum_range f lo hi) = sum_range g lo hi)
          (decreases (hi - lo))
  = H.elim_equatable_laws t ();
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if lo >= hi then begin
      sum_range_empty f lo hi;                                 (* sum f lo hi == zero(t) *)
      poly_const_zero #t #cr ();                                    (* poly_const zero ~ poly_zero *)
      sum_range_empty g lo hi        (* sum g == poly_zero *)
    end else begin
      sum_range_unfold_left f lo hi;                            (* sum f lo hi == f lo + sum f (lo+1) hi *)
      sum_range_unfold_left g lo hi; (* sum g lo hi == g lo + sum g (lo+1) hi *)
      poly_const_add (f lo) (sum_range f (lo ++ 1) hi);         (* poly_const(flo+S) ~ poly_add (poly_const flo)(poly_const S) *)
      poly_const_sum_range f g (lo ++ 1) hi hyp;               (* IH: poly_const S ~ sum g (lo+1) hi *)
      hyp lo;                                                    (* g lo ~ poly_const (f lo) *)

      add_congruence
        (poly_const (f lo)) (poly_const (sum_range f (lo ++ 1) hi))
        (g lo) (sum_range g (lo ++ 1) hi)
    end

(* the i-th substitution term  [coeff g i] * h^i  (in t[X]). *)
let subst_term (#t:Type) {| cr: commutative_ring t |} (h g: polynomial t) (i: nat) : polynomial t
  = (poly_const (coeff g i)) * (E.cpow h i)

(* the substitution  phi_h(g) = Sum_{i<len g} [coeff g i] * h^i. *)
let poly_subst (#t:Type) {| cr: commutative_ring t |} (h g: polynomial t) : polynomial t
  = sum_range (subst_term h g) 0 (L.length g)

(* terms beyond the length vanish (coeff = 0 there). *)
let subst_term_high (#t:Type) {| cr: commutative_ring t |} (h g: polynomial t) (i: nat)
  : Lemma (requires i >= L.length g) (ensures subst_term h g i = poly_zero)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let ck = E.cpow h i in
    assert (coeff g i == (zero <: t));                 (* from coeff's refinement *)
    poly_const_zero #t #cr ();                              (* poly_const zero ~ poly_zero *)
    (* poly_const (coeff g i) == poly_const zero ~ poly_zero *)
    H.zero_mul_x ck;   (* poly_zero * ck ~ poly_zero *)
    mul_congruence
      (poly_const (coeff g i)) ck (poly_zero) ck

(* summing past the length doesn't change the value. *)
let subst_extend (#t:Type) {| cr: commutative_ring t |} (h g: polynomial t) (n: nat)
  : Lemma (requires n >= L.length g)
          (ensures sum_range (subst_term h g) 0 n = poly_subst h g)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let f = subst_term h g in
    let lg = L.length g in
    sum_range_split f 0 lg n;
    sum_range_all_zero f lg n
      (fun (k: nat{lg <= k /\ k < n}) -> subst_term_high h g k);
    H.x_plus_zero (sum_range f 0 lg);
    add_congruence
      (sum_range f 0 lg) (sum_range f lg n)
      (sum_range f 0 lg) (poly_zero)

(* phi_h respects poly_eq in its polynomial argument. *)
let subst_congr (#t:Type) {| cr: commutative_ring t |} (h g1 g2: polynomial t)
  : Lemma (requires g1 = g2) (ensures poly_subst h g1 = poly_subst h g2)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    poly_eq_length g1 g2;
    let f1 = subst_term h g1 in
    let f2 = subst_term h g2 in
    let step (i: nat{0 <= i /\ i < L.length g1}) : Lemma (f1 i = f2 i) =
      let ck = E.cpow h i in
      poly_eq_means_equal_coeffs g1 g2 i;                 (* coeff g1 i = coeff g2 i *)
      poly_const_congr (coeff g1 i) (coeff g2 i);             (* poly_const (coeff g1 i) ~ poly_const (coeff g2 i) *)

      mul_congruence
        (poly_const (coeff g1 i)) ck (poly_const (coeff g2 i)) ck
    in
    sum_range_congruence f1 f2 0 (L.length g1) step

(* phi_h(1) = 1. *)
#push-options "--fuel 4 --ifuel 2"
let subst_one (#t:Type) {| cr: commutative_ring t |} (h: polynomial t)
  : Lemma (poly_subst h (poly_one) = poly_one)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let f1 = subst_term h (poly_one) in
    if (one <: t) = (zero <: t) then
      (* poly_one == [] ; poly_subst h [] = empty sum = poly_zero == poly_one *)
      sum_range_empty f1 0 0
    else begin
      (* poly_one == [one] : the single term is  poly_const one * h^0 = poly_const one * 1 ~ poly_one *)
      sum_range_unfold_left f1 0 1;
      sum_range_empty f1 1 1;
      H.x_plus_zero (f1 0);
      add_congruence (f1 0) (sum_range f1 1 1)
                     (f1 0) (poly_zero);
      (* f1 0 = poly_const (coeff poly_one 0) * (cpow h 0 = poly_one) = poly_const one * poly_one ~ poly_const one ~ poly_one *)
      poly_const_coeff0 (one <: t);                            (* coeff poly_one 0 = one : but here coeff (poly_one) 0 = one directly *)
      H.x_mul_one (poly_const (one <: t));   (* poly_const one * one ~ poly_const one *)
      poly_const_one #t #cr ();                                 (* poly_const one ~ poly_one *)
      mul_congruence
        (poly_const (coeff (poly_one) 0)) (E.cpow h 0)
        (poly_const (one <: t)) (E.cpow h 0)
    end
#pop-options

(* additivity:  phi_h(a + b) = phi_h(a) + phi_h(b). *)
let subst_add (#t:Type) {| cr: commutative_ring t |} (h a b: polynomial t)
  : Lemma (poly_subst h (a + b) = (poly_subst h a) + (poly_subst h b))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let s : polynomial t = a + b in
    let n = L.length a + L.length b + L.length s + 1 in
    let fa = subst_term h a in
    let fb = subst_term h b in
    let fs = subst_term h s in
    subst_extend h a n; subst_extend h b n; subst_extend h s n;
    let step (i: nat{0 <= i /\ i < n}) : Lemma (fs i = pointwise_add fa fb i) =
      let ck = E.cpow h i in
      let cai : t = coeff a i in
      let cbi : t = coeff b i in
      poly_add_coeff a b i;                              (* coeff s i = cai + cbi *)
      poly_const_add cai cbi;                                 (* poly_const (cai+cbi) ~ poly_add (poly_const cai)(poly_const cbi) *)
      poly_const_congr (coeff s i) (cai + cbi);               (* poly_const (coeff s i) ~ poly_const (cai+cbi) *)
      mul_congruence
        (poly_const (coeff s i)) ck ((poly_const cai) + (poly_const cbi)) ck;
      right_distributivity ck (poly_const cai) (poly_const cbi)
    in
    sum_range_congruence fs (pointwise_add fa fb) 0 n step;
    sum_range_add fa fb 0 n;
    add_congruence
      (sum_range fa 0 n) (sum_range fb 0 n)
      (poly_subst h a) (poly_subst h b)

(* negation:  phi_h(neg a) = neg (phi_h a). *)
let subst_neg (#t:Type) {| cr: commutative_ring t |} (h a: polynomial t)
  : Lemma (poly_subst h (- a) = - (poly_subst h a))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let na : polynomial t = - a in
    let n = L.length a + L.length na + 1 in
    let fa = subst_term h a in
    let fna = subst_term h na in
    subst_extend h a n; subst_extend h na n;
    let step (i: nat{0 <= i /\ i < n}) : Lemma (fna i = pointwise_neg fa i) =
      let ck = E.cpow h i in
      let cai : t = coeff a i in
      pointwise_neg_unfold fa i;
      poly_neg_coeff a i;                                 (* coeff na i = neg cai *)
      poly_const_neg cai;                                      (* poly_const (neg cai) ~ poly_neg (poly_const cai) *)
      poly_const_congr (coeff na i) (- cai);                 (* poly_const (coeff na i) ~ poly_const (neg cai) *)
      mul_congruence
        (poly_const (coeff na i)) ck (- (poly_const cai)) ck;
      H.neg_mul_l (poly_const cai) ck
    in
    sum_range_congruence fna (pointwise_neg fa) 0 n step;
    sum_range_neg fa 0 n;
    neg_congruence
      (sum_range fa 0 n) (poly_subst h a)

(* ================================================================ *)
(*  Multiplicativity of phi_h (the heart).                           *)
(* ================================================================ *)

(* t-level: the convolution sum over [0,k+1) is the k-th product coeff. *)
let conv_coeff_t (#t:Type) {| cr: commutative_ring t |} (a b: polynomial t) (k: nat)
  : Lemma (sum_range (fun (i:nat) -> coeff a i * coeff b (k - i)) 0 ((k ++ 1))
           = coeff (a * b) k)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cc : nat -> t = fun (i:nat) -> coeff a i * coeff b (k - i) in
    let kk1 : nat = (k ++ 1) in
    let lp : nat = L.length a in
    let mm : nat = (kk1 ++ lp) in
    (* sum cc 0 kk1 = sum cc 0 lp  (both extend to mm with zero tails) *)
    sum_range_split cc 0 kk1 mm;
    sum_range_all_zero cc kk1 mm (fun (i:nat{kk1 <= i /\ i < mm}) -> H.x_mul_zero (coeff a i));
    H.x_plus_zero (sum_range cc 0 kk1);
    add_congruence (sum_range cc 0 kk1) (sum_range cc kk1 mm) (sum_range cc 0 kk1) (zero <: t);
    sum_range_split cc 0 lp mm;
    sum_range_all_zero cc lp mm (fun (i:nat{lp <= i /\ i < mm}) -> H.zero_mul_x (coeff b (k - i)));
    H.x_plus_zero (sum_range cc 0 lp);
    add_congruence (sum_range cc 0 lp) (sum_range cc lp mm) (sum_range cc 0 lp) (zero <: t);
    CC.coeff_poly_mul_named a b k cc H.obvious
    (* chain: sum cc 0 kk1 = sum cc 0 mm = sum cc 0 lp = coeff(ab)k *)

(* abstract ring rearrangement (canon_ring works on an abstract instance var). *)
let mul4_swap (#p:Type) {| pr: commutative_ring p |} (a u b v: p)
  : Lemma ((a * u) * (b * v) = (a * b) * (u * v))
  = assert ((a * u) * (b * v) = (a * b) * (u * v)) by (Core.Tactics.CanonRing.canon_ring ())

(* per-k bridge:  conv_sum (subst_term h a) (subst_term h b) k ~ subst_term h (a*b) k. *)
let subst_conv (#t:Type) {| cr: commutative_ring t |} (h a b: polynomial t) (k: nat)
  : Lemma (CV.conv_sum (subst_term h a) (subst_term h b) k
           = subst_term h (a * b) k)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let fa = subst_term h a in
    let fb = subst_term h b in
    let ck = E.cpow h k in
    let cc : nat -> t = fun (i:nat) -> coeff a i * coeff b (k - i) in
    let cc0 : nat -> polynomial t = fun (i:nat) -> poly_const (cc i) in
    let kk1 : nat = (k ++ 1) in
    let term_cb (i:nat{0 <= i /\ i < kk1})
      : Lemma (poly_eq (CV.conv_term fa fb k i) (pointwise_mul cc0 (const ck) i)) =
      let cai0 = poly_const (coeff a i) in
      let cbi0 = poly_const (coeff b (k - i)) in
      let pi  = E.cpow h i in
      let pki = E.cpow h (k - i) in
      CV.conv_term_reveal fa fb k i;
      mul4_swap cai0 pi cbi0 pki;     (* (cai0*pi)*(cbi0*pki) = (cai0*cbi0)*(pi*pki) *)
      E.cpow_add h i (k - i);          (* ck = pi*pki *)
      poly_const_mul (coeff a i) (coeff b (k - i));                  (* cc0 i ~ cai0*cbi0 *)
      mul_congruence
        (cai0 * cbi0) (pi * pki) (cc0 i) ck
    in
    sum_range_congruence
      (CV.conv_term fa fb k) (pointwise_mul cc0 (const ck)) 0 kk1 term_cb;
    sum_range_mul_right cc0 ck 0 kk1;
    (* sum cc0 0 kk1 ~ poly_const (coeff (a*b) k) *)
    poly_const_sum_range cc cc0 0 kk1 H.obvious;
    conv_coeff_t a b k;                                           (* sum cc 0 kk1 = coeff(ab)k *)
    poly_const_congr (sum_range cc 0 kk1) (coeff (a * b) k);   (* poly_const(sum cc) ~ poly_const(coeff(ab)k) *)

    mul_congruence
      (sum_range cc0 0 kk1) ck (poly_const (coeff (a * b) k)) ck;
    (* assemble:  conv_sum = (sum cc0)*ck ~ poly_const(coeff(ab)k)*ck = subst_term h (ab) k *)
    CV.conv_sum_reveal fa fb k

(* coeff (a*b) k vanishes (hence subst_term) for k >= len a + len b. *)
let subst_pq_high (#t:Type) {| cr: commutative_ring t |} (h a b: polynomial t) (k: nat)
  : Lemma (requires k >= L.length a + L.length b)
          (ensures subst_term h (a * b) k = poly_zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cc : nat -> t = fun (i:nat) -> coeff a i * coeff b (k - i) in
    CC.coeff_poly_mul_named a b k cc H.obvious;
    sum_range_all_zero cc 0 (L.length a)
      (fun (i:nat{0 <= i /\ i < L.length a}) -> H.x_mul_zero (coeff a i));
    (* coeff (a*b) k = 0, so poly_const (coeff (a*b) k) ~ poly_zero, times ck ~ poly_zero *)
    poly_const_congr (coeff (a * b) k) (zero <: t);
    poly_const_zero #t #cr ();
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let ck = E.cpow h k in
    H.zero_mul_x ck;
    mul_congruence
      (poly_const (coeff (a * b) k)) ck (poly_zero) ck

(* MULTIPLICATIVITY:  phi_h(a * b) = phi_h(a) * phi_h(b). *)
let subst_mul (#t:Type) {| cr: commutative_ring t |} (h a b: polynomial t)
  : Lemma (poly_subst h (a * b) = (poly_subst h a) * (poly_subst h b))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let fa = subst_term h a in
    let fb = subst_term h b in
    let ab : polynomial t = a * b in
    let bnd : nat = (L.length a ++ L.length b) in
    let mm : nat = (L.length ab ++ bnd) in
    let etab : nat -> polynomial t = subst_term h ab in
    CV.sum_range_convolution fa fb (L.length a) (L.length b)
      (fun (i:nat{i >= L.length a}) -> subst_term_high h a i)
      (fun (j:nat{j >= L.length b}) -> subst_term_high h b j);
    sum_range_congruence
      (CV.conv_sum fa fb) etab 0 bnd
      (fun (k:nat{0 <= k /\ k < bnd}) -> subst_conv h a b k);
    subst_extend h ab mm;
    sum_range_split etab 0 bnd mm;
    sum_range_all_zero etab bnd mm
      (fun (k:nat{bnd <= k /\ k < mm}) -> subst_pq_high h a b k);
    H.x_plus_zero (sum_range etab 0 bnd);
    add_congruence
      (sum_range etab 0 bnd) (sum_range etab bnd mm)
      (sum_range etab 0 bnd) (poly_zero)

(* subtraction:  phi_h(a - b) = phi_h(a) - phi_h(b). *)
let subst_sub (#t:Type) {| cr: commutative_ring t |} (h a b: polynomial t)
  : Lemma (poly_subst h (a -- b) = (poly_subst h a) -- (poly_subst h b))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    subst_add h a (- b);                          (* phi(a + neg b) ~ phi a + phi(neg b) *)
    subst_neg h b;                                       (* phi(neg b) ~ neg (phi b) *)

    add_congruence
      (poly_subst h a) (poly_subst h (- b)) (poly_subst h a) (- (poly_subst h b))
