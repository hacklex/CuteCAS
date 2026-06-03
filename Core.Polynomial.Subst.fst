module Core.Polynomial.Subst

(* ================================================================ *)
(*  The substitution homomorphism  phi_h : t[X] -> t[X],  X |-> h.   *)
(*                                                                   *)
(*  Defined as the coefficient sum  phi_h(g) = Sum_i [coeff g i]*h^i  *)
(*  over the polynomial ring (mirroring Core.Polynomial.Eval, which   *)
(*  evaluates at a point IN the coefficient ring).  The coefficient   *)
(*  embedding  const0 : t -> t[X],  c |-> [c],  is shown to be a ring  *)
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
module CV = Core.FinSum.Convolution

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Polynomial
open Core.Polynomial.Div
open Core.FinSum

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  const0 c = the constant polynomial [c] = monomial c 0.           *)
(*  Shown to be a ring homomorphism  t -> t[X].                      *)
(* ================================================================ *)

let const0 (#t:Type) {| cr: commutative_ring t |} (c: t) : polynomial t
  = monomial #t #cr c 0

(* equatable equality on t, routed so it resolves the equatable instance
   (a bare `x = y` in a `requires` defaults to Prims.op_Equality / eqtype). *)
unfold let eq_t (#t:Type) {| cr: commutative_ring t |} (x y: t) : bool = x = y

(* poly_eq from coefficient agreement on nat indices (negatives are zero). *)
let poly_eq_by_coeff (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  (h: (j:nat) -> Lemma (coeff p j = coeff q j))
  : Lemma (poly_eq p q)
  = H.elim_equatable_laws t ();
    let aux (j:int) : Lemma (coeff p j = coeff q j) =
      if j < 0 then reflexivity (zero <: t) else h j
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq p q

let const0_coeff0 (#t:Type) {| cr: commutative_ring t |} (c: t)
  : Lemma (coeff (const0 c) 0 = c)
  = H.elim_equatable_laws t ();
    monomial_coeff #t #cr c 0 0

let const0_coeff_high (#t:Type) {| cr: commutative_ring t |} (c: t) (i:nat)
  : Lemma (requires i >= 1) (ensures coeff (const0 c) i = (zero <: t))
  = H.elim_equatable_laws t ();
    monomial_coeff #t #cr c 0 i

(* const0 zero ~ poly_zero *)
let const0_zero (#t:Type) {| cr: commutative_ring t |} ()
  : Lemma (poly_eq (const0 (zero <: t)) (poly_zero #t))
  = H.elim_equatable_laws t ();
    poly_eq_by_coeff (const0 (zero <: t)) (poly_zero #t)
      (fun (j:nat) -> if j = 0 then const0_coeff0 (zero <: t)
                      else const0_coeff_high (zero <: t) j)

(* const0 respects = *)
let const0_congr (#t:Type) {| cr: commutative_ring t |} (x y: t)
  : Lemma (requires (eq_t x y)) (ensures poly_eq (const0 x) (const0 y))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    poly_eq_by_coeff (const0 x) (const0 y)
      (fun (j:nat) ->
        if j = 0 then (const0_coeff0 x; const0_coeff0 y)
        else (const0_coeff_high x j; const0_coeff_high y j))

(* additivity:  const0 (x + y) ~ const0 x + const0 y *)
let const0_add (#t:Type) {| cr: commutative_ring t |} (x y: t)
  : Lemma (poly_eq (const0 (x + y)) (poly_add (const0 x) (const0 y)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    poly_eq_by_coeff (const0 (x + y)) (poly_add (const0 x) (const0 y))
      (fun (j:nat) ->
        if j = 0 then begin
          const0_coeff0 (x + y); const0_coeff0 x; const0_coeff0 y;
          (* coeff (poly_add ..) 0 = coeff (const0 x) 0 + coeff (const0 y) 0  [SMTPat poly_add_coeff] *)
          add_congruence (coeff (const0 x) 0) (coeff (const0 y) 0) x y
        end else begin
          const0_coeff_high (x + y) j; const0_coeff_high x j; const0_coeff_high y j;
          add_congruence (coeff (const0 x) j) (coeff (const0 y) j) (zero <: t) (zero <: t);
          H.x_plus_zero (zero <: t)
        end)

(* negation:  const0 (neg x) ~ poly_neg (const0 x) *)
let const0_neg (#t:Type) {| cr: commutative_ring t |} (x: t)
  : Lemma (poly_eq (const0 (neg x)) (poly_neg (const0 x)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    poly_eq_by_coeff (const0 (neg x)) (poly_neg (const0 x))
      (fun (j:nat) ->
        if j = 0 then begin
          const0_coeff0 (neg x); const0_coeff0 x;
          poly_neg_coeff (const0 x) 0;                   (* coeff(poly_neg)0 = neg(coeff(const0 x)0) *)
          neg_congruence (coeff (const0 x) 0) x           (* neg(coeff(const0 x)0) = neg x *)
        end else begin
          const0_coeff_high (neg x) j; const0_coeff_high x j;
          poly_neg_coeff (const0 x) j;
          neg_congruence (coeff (const0 x) j) (zero <: t);
          H.neg_zero #t ()                                (* neg zero = zero *)
        end)

(* multiplicativity:  const0 (x * y) ~ const0 x * const0 y *)
let const0_mul (#t:Type) {| cr: commutative_ring t |} (x y: t)
  : Lemma (poly_eq (const0 (x * y)) (poly_mul (const0 x) (const0 y)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    poly_eq_by_coeff (const0 (x * y)) (poly_mul (const0 x) (const0 y))
      (fun (j:nat) ->
        if j = 0 then begin
          const0_coeff0 (x * y); const0_coeff0 y;
          (* const0 x = monomial x 0 ; monomial_mul_coeff x 0 (const0 y) 0 :
             coeff (monomial x 0 * const0 y) (0+0) = x * coeff (const0 y) 0 = x * y *)
          monomial_mul_coeff #t #cr x 0 (const0 y) 0;
          mul_congruence x (coeff (const0 y) 0) x y        (* x * coeff(const0 y)0 = x*y *)
        end else begin
          const0_coeff_high (x * y) j;
          const0_coeff_high y j;
          (* coeff(monomial x 0 * const0 y)(0+j) = x * coeff(const0 y) j = x*zero = zero *)
          monomial_mul_coeff #t #cr x 0 (const0 y) j;
          mul_congruence x (coeff (const0 y) j) x (zero <: t);
          H.x_mul_zero x                                   (* x * zero = zero *)
        end)

(* unit:  const0 one ~ poly_one *)
#push-options "--fuel 4 --ifuel 2"
let const0_one (#t:Type) {| cr: commutative_ring t |} ()
  : Lemma (poly_eq (const0 (one <: t)) (poly_one #t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if (one <: t) = (zero <: t) then begin
      (* poly_one == [] ; const0 one ~ const0 zero ~ poly_zero == poly_one *)
      const0_congr (one <: t) (zero <: t);          (* const0 one ~ const0 zero *)
      const0_zero #t #cr ();                          (* const0 zero ~ poly_zero *)
      H.elim_equatable_laws (polynomial t) #((polynomial_acg cr).acg_eq) ();
      H.trans_for_calc (polynomial t) #((polynomial_acg cr).acg_eq) ();
      transitivity #(polynomial t) #((polynomial_acg cr).acg_eq)
        (const0 (one <: t)) (const0 (zero <: t)) (poly_zero #t)
    end else
      (* poly_one == [one] : coeff 0 = one, coeff (>=1) = zero *)
      poly_eq_by_coeff (const0 (one <: t)) (poly_one #t)
        (fun (j:nat) ->
          if j = 0 then const0_coeff0 (one <: t)
          else const0_coeff_high (one <: t) j)
#pop-options

(* ================================================================ *)
(*  The substitution map  phi_h(g) = Sum_i [coeff g i] * h^i.        *)
(*  Everything lives in the polynomial ring t[X]; we fix ONE         *)
(*  add_comm_group / commutative_ring instance for it (the one       *)
(*  carried by polynomial_commutative_ring_instance) so sum_range,   *)
(*  cpow and the convolution lemmas all line up.                     *)
(* ================================================================ *)

let pcr (#t:Type) (cr: commutative_ring t) : commutative_ring (polynomial t)
  = (polynomial_commutative_ring_instance #t #cr).pcr

let pacg (#t:Type) (cr: commutative_ring t) : add_comm_group (polynomial t)
  = (pcr cr).cr_r.r_add

(* const0 commutes with finite sums (named form: the polynomial-valued summand
   g is passed explicitly with a pointwise hypothesis g i ~ const0 (f i),
   sidestepping lambda-unification against an internal `fun i -> const0 (f i)`). *)
let rec const0_sum_range (#t:Type) {| cr: commutative_ring t |}
  (f: nat -> t) (g: nat -> polynomial t) (lo hi: nat)
  (hyp: (i:nat) -> Lemma (poly_eq (g i) (const0 (f i))))
  : Lemma (ensures poly_eq (const0 (sum_range f lo hi)) (sum_range #(polynomial t) #(pacg cr) g lo hi))
          (decreases (hi - lo))
  = H.elim_equatable_laws t ();
    H.elim_equatable_laws (polynomial t) #((pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial t) #((pacg cr).acg_eq) ();
    if lo >= hi then begin
      sum_range_empty f lo hi;                                 (* sum f lo hi == zero(t) *)
      const0_zero #t #cr ();                                    (* const0 zero ~ poly_zero *)
      sum_range_empty #(polynomial t) #(pacg cr) g lo hi        (* sum g == poly_zero *)
    end else begin
      sum_range_unfold_left f lo hi;                            (* sum f lo hi == f lo + sum f (lo+1) hi *)
      sum_range_unfold_left #(polynomial t) #(pacg cr) g lo hi; (* sum g lo hi == g lo + sum g (lo+1) hi *)
      const0_add (f lo) (sum_range f (nat_succ lo) hi);         (* const0(flo+S) ~ poly_add (const0 flo)(const0 S) *)
      const0_sum_range f g (nat_succ lo) hi hyp;               (* IH: const0 S ~ sum g (lo+1) hi *)
      hyp lo;                                                    (* g lo ~ const0 (f lo) *)
      symmetry #(polynomial t) #((pacg cr).acg_eq) (g lo) (const0 (f lo));   (* const0 (f lo) ~ g lo *)
      add_congruence #(polynomial t) #(pacg cr)
        (const0 (f lo)) (const0 (sum_range f (nat_succ lo) hi))
        (g lo) (sum_range #(polynomial t) #(pacg cr) g (nat_succ lo) hi);
      transitivity #(polynomial t) #((pacg cr).acg_eq)
        (const0 (sum_range f lo hi))
        (poly_add (const0 (f lo)) (const0 (sum_range f (nat_succ lo) hi)))
        (poly_add (g lo) (sum_range #(polynomial t) #(pacg cr) g (nat_succ lo) hi))
    end

(* the i-th substitution term  [coeff g i] * h^i  (in t[X]). *)
let subst_term (#t:Type) {| cr: commutative_ring t |} (h g: polynomial t) (i: nat) : polynomial t
  = poly_mul (const0 (coeff g i)) (E.cpow #(polynomial t) #(pcr cr) h i)

(* the substitution  phi_h(g) = Sum_{i<len g} [coeff g i] * h^i. *)
let poly_subst (#t:Type) {| cr: commutative_ring t |} (h g: polynomial t) : polynomial t
  = sum_range #(polynomial t) #(pacg cr) (subst_term h g) 0 (L.length g)

(* terms beyond the length vanish (coeff = 0 there). *)
let subst_term_high (#t:Type) {| cr: commutative_ring t |} (h g: polynomial t) (i: nat)
  : Lemma (requires i >= L.length g) (ensures poly_eq (subst_term h g i) (poly_zero #t))
  = H.elim_equatable_laws (polynomial t) #((pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial t) #((pacg cr).acg_eq) ();
    let ck = E.cpow #(polynomial t) #(pcr cr) h i in
    assert (coeff g i == (zero <: t));                 (* from coeff's refinement *)
    const0_zero #t #cr ();                              (* const0 zero ~ poly_zero *)
    (* const0 (coeff g i) == const0 zero ~ poly_zero *)
    H.zero_mul_x #(polynomial t) #((pcr cr).cr_r) ck;   (* poly_mul poly_zero ck ~ poly_zero *)
    mul_congruence #(polynomial t) #((pcr cr).cr_r)
      (const0 (coeff g i)) ck (poly_zero #t) ck;
    transitivity #(polynomial t) #((pacg cr).acg_eq)
      (subst_term h g i) (poly_mul (poly_zero #t) ck) (poly_zero #t)

(* summing past the length doesn't change the value. *)
let subst_extend (#t:Type) {| cr: commutative_ring t |} (h g: polynomial t) (n: nat)
  : Lemma (requires n >= L.length g)
          (ensures poly_eq (sum_range #(polynomial t) #(pacg cr) (subst_term h g) 0 n) (poly_subst h g))
  = H.elim_equatable_laws (polynomial t) #((pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial t) #((pacg cr).acg_eq) ();
    let f = subst_term h g in
    let lg = L.length g in
    sum_range_split #(polynomial t) #(pacg cr) f 0 lg n;
    sum_range_all_zero #(polynomial t) #(pacg cr) f lg n
      (fun (k: nat{lg <= k /\ k < n}) -> subst_term_high h g k);
    H.x_plus_zero #(polynomial t) #(pacg cr) (sum_range #(polynomial t) #(pacg cr) f 0 lg);
    add_congruence #(polynomial t) #(pacg cr)
      (sum_range #(polynomial t) #(pacg cr) f 0 lg) (sum_range #(polynomial t) #(pacg cr) f lg n)
      (sum_range #(polynomial t) #(pacg cr) f 0 lg) (poly_zero #t);
    transitivity #(polynomial t) #((pacg cr).acg_eq)
      (sum_range #(polynomial t) #(pacg cr) f 0 n)
      (poly_add (sum_range #(polynomial t) #(pacg cr) f 0 lg) (sum_range #(polynomial t) #(pacg cr) f lg n))
      (poly_add (sum_range #(polynomial t) #(pacg cr) f 0 lg) (poly_zero #t));
    transitivity #(polynomial t) #((pacg cr).acg_eq)
      (sum_range #(polynomial t) #(pacg cr) f 0 n)
      (poly_add (sum_range #(polynomial t) #(pacg cr) f 0 lg) (poly_zero #t))
      (sum_range #(polynomial t) #(pacg cr) f 0 lg)

(* phi_h respects poly_eq in its polynomial argument. *)
let subst_congr (#t:Type) {| cr: commutative_ring t |} (h g1 g2: polynomial t)
  : Lemma (requires poly_eq g1 g2) (ensures poly_eq (poly_subst h g1) (poly_subst h g2))
  = H.elim_equatable_laws (polynomial t) #((pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial t) #((pacg cr).acg_eq) ();
    poly_eq_length g1 g2;
    let f1 = subst_term h g1 in
    let f2 = subst_term h g2 in
    let step (i: nat{0 <= i /\ i < L.length g1}) : Lemma (poly_eq (f1 i) (f2 i)) =
      let ck = E.cpow #(polynomial t) #(pcr cr) h i in
      poly_eq_means_equal_coeffs g1 g2 i;                 (* coeff g1 i = coeff g2 i *)
      const0_congr (coeff g1 i) (coeff g2 i);             (* const0 (coeff g1 i) ~ const0 (coeff g2 i) *)
      reflexivity #(polynomial t) #((pacg cr).acg_eq) ck;
      mul_congruence #(polynomial t) #((pcr cr).cr_r)
        (const0 (coeff g1 i)) ck (const0 (coeff g2 i)) ck
    in
    sum_range_congruence #(polynomial t) #(pacg cr) f1 f2 0 (L.length g1) step

(* phi_h(1) = 1. *)
#push-options "--fuel 4 --ifuel 2"
let subst_one (#t:Type) {| cr: commutative_ring t |} (h: polynomial t)
  : Lemma (poly_eq (poly_subst h (poly_one #t)) (poly_one #t))
  = H.elim_equatable_laws (polynomial t) #((pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial t) #((pacg cr).acg_eq) ();
    let f1 = subst_term h (poly_one #t) in
    if (one <: t) = (zero <: t) then
      (* poly_one == [] ; poly_subst h [] = empty sum = poly_zero == poly_one *)
      sum_range_empty #(polynomial t) #(pacg cr) f1 0 0
    else begin
      (* poly_one == [one] : the single term is  const0 one * h^0 = const0 one * 1 ~ poly_one *)
      sum_range_unfold_left #(polynomial t) #(pacg cr) f1 0 1;
      sum_range_empty #(polynomial t) #(pacg cr) f1 1 1;
      H.x_plus_zero #(polynomial t) #(pacg cr) (f1 0);
      add_congruence #(polynomial t) #(pacg cr) (f1 0) (sum_range #(polynomial t) #(pacg cr) f1 1 1)
                     (f1 0) (poly_zero #t);
      (* f1 0 = const0 (coeff poly_one 0) * (cpow h 0 = poly_one) = const0 one * poly_one ~ const0 one ~ poly_one *)
      const0_coeff0 (one <: t);                            (* coeff poly_one 0 = one : but here coeff (poly_one) 0 = one directly *)
      H.x_mul_one #(polynomial t) #((pcr cr).cr_r) (const0 (one <: t));   (* const0 one * one ~ const0 one *)
      const0_one #t #cr ();                                 (* const0 one ~ poly_one *)
      mul_congruence #(polynomial t) #((pcr cr).cr_r)
        (const0 (coeff (poly_one #t) 0)) (E.cpow #(polynomial t) #(pcr cr) h 0)
        (const0 (one <: t)) (E.cpow #(polynomial t) #(pcr cr) h 0);
      transitivity #(polynomial t) #((pacg cr).acg_eq)
        (f1 0) (poly_mul (const0 (one <: t)) (E.cpow #(polynomial t) #(pcr cr) h 0)) (const0 (one <: t));
      transitivity #(polynomial t) #((pacg cr).acg_eq)
        (f1 0) (const0 (one <: t)) (poly_one #t);
      transitivity #(polynomial t) #((pacg cr).acg_eq)
        (poly_subst h (poly_one #t)) (f1 0) (poly_one #t)
    end
#pop-options

(* additivity:  phi_h(a + b) = phi_h(a) + phi_h(b). *)
let subst_add (#t:Type) {| cr: commutative_ring t |} (h a b: polynomial t)
  : Lemma (poly_eq (poly_subst h (poly_add a b)) (poly_add (poly_subst h a) (poly_subst h b)))
  = H.elim_equatable_laws (polynomial t) #((pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial t) #((pacg cr).acg_eq) ();
    let s = poly_add a b in
    let n = L.length a + L.length b + L.length s + 1 in
    let fa = subst_term h a in
    let fb = subst_term h b in
    let fs = subst_term h s in
    subst_extend h a n; subst_extend h b n; subst_extend h s n;
    let step (i: nat{0 <= i /\ i < n}) : Lemma (poly_eq (fs i) (pointwise_add fa fb i)) =
      let ck = E.cpow #(polynomial t) #(pcr cr) h i in
      let cai : t = coeff a i in
      let cbi : t = coeff b i in
      poly_add_coeff a b i;                              (* coeff s i = cai + cbi *)
      const0_add cai cbi;                                 (* const0 (cai+cbi) ~ poly_add (const0 cai)(const0 cbi) *)
      const0_congr (coeff s i) (cai + cbi);               (* const0 (coeff s i) ~ const0 (cai+cbi) *)
      transitivity #(polynomial t) #((pacg cr).acg_eq)
        (const0 (coeff s i)) (const0 (cai + cbi)) (poly_add (const0 cai) (const0 cbi));
      mul_congruence #(polynomial t) #((pcr cr).cr_r)
        (const0 (coeff s i)) ck (poly_add (const0 cai) (const0 cbi)) ck;
      right_distributivity #(polynomial t) #((pcr cr).cr_r) ck (const0 cai) (const0 cbi);
      transitivity #(polynomial t) #((pacg cr).acg_eq)
        (fs i) (poly_mul (poly_add (const0 cai) (const0 cbi)) ck)
        (poly_add (poly_mul (const0 cai) ck) (poly_mul (const0 cbi) ck))
    in
    sum_range_congruence #(polynomial t) #(pacg cr) fs (pointwise_add fa fb) 0 n step;
    sum_range_add #(polynomial t) #(pacg cr) fa fb 0 n;
    add_congruence #(polynomial t) #(pacg cr)
      (sum_range #(polynomial t) #(pacg cr) fa 0 n) (sum_range #(polynomial t) #(pacg cr) fb 0 n)
      (poly_subst h a) (poly_subst h b);
    transitivity #(polynomial t) #((pacg cr).acg_eq)
      (poly_subst h s) (sum_range #(polynomial t) #(pacg cr) (pointwise_add fa fb) 0 n)
      (poly_add (sum_range #(polynomial t) #(pacg cr) fa 0 n) (sum_range #(polynomial t) #(pacg cr) fb 0 n));
    transitivity #(polynomial t) #((pacg cr).acg_eq)
      (poly_subst h s)
      (poly_add (sum_range #(polynomial t) #(pacg cr) fa 0 n) (sum_range #(polynomial t) #(pacg cr) fb 0 n))
      (poly_add (poly_subst h a) (poly_subst h b))

(* negation:  phi_h(neg a) = neg (phi_h a). *)
let subst_neg (#t:Type) {| cr: commutative_ring t |} (h a: polynomial t)
  : Lemma (poly_eq (poly_subst h (poly_neg a)) (poly_neg (poly_subst h a)))
  = H.elim_equatable_laws (polynomial t) #((pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial t) #((pacg cr).acg_eq) ();
    let na = poly_neg a in
    let n = L.length a + L.length na + 1 in
    let fa = subst_term h a in
    let fna = subst_term h na in
    subst_extend h a n; subst_extend h na n;
    let step (i: nat{0 <= i /\ i < n}) : Lemma (poly_eq (fna i) (neg #(polynomial t) #(pacg cr) (fa i))) =
      let ck = E.cpow #(polynomial t) #(pcr cr) h i in
      let cai : t = coeff a i in
      poly_neg_coeff a i;                                 (* coeff na i = neg cai *)
      const0_neg cai;                                      (* const0 (neg cai) ~ poly_neg (const0 cai) *)
      const0_congr (coeff na i) (neg cai);                 (* const0 (coeff na i) ~ const0 (neg cai) *)
      transitivity #(polynomial t) #((pacg cr).acg_eq)
        (const0 (coeff na i)) (const0 (neg cai)) (poly_neg (const0 cai));
      mul_congruence #(polynomial t) #((pcr cr).cr_r)
        (const0 (coeff na i)) ck (poly_neg (const0 cai)) ck;
      H.neg_mul_l #(polynomial t) #((pcr cr).cr_r) (const0 cai) ck;
      transitivity #(polynomial t) #((pacg cr).acg_eq)
        (fna i) (poly_mul (poly_neg (const0 cai)) ck) (poly_neg (poly_mul (const0 cai) ck))
    in
    sum_range_congruence #(polynomial t) #(pacg cr) fna (fun (k:nat) -> neg #(polynomial t) #(pacg cr) (fa k)) 0 n step;
    sum_range_neg #(polynomial t) #(pacg cr) fa 0 n;
    neg_congruence #(polynomial t) #(pacg cr)
      (sum_range #(polynomial t) #(pacg cr) fa 0 n) (poly_subst h a);
    transitivity #(polynomial t) #((pacg cr).acg_eq)
      (poly_subst h na) (neg #(polynomial t) #(pacg cr) (sum_range #(polynomial t) #(pacg cr) fa 0 n))
      (neg #(polynomial t) #(pacg cr) (poly_subst h a))

(* ================================================================ *)
(*  Multiplicativity of phi_h (the heart).                           *)
(* ================================================================ *)

(* t-level: the convolution sum over [0,k+1) is the k-th product coeff. *)
let conv_coeff_t (#t:Type) {| cr: commutative_ring t |} (a b: polynomial t) (k: nat)
  : Lemma (sum_range (fun (i:nat) -> coeff a i * coeff b (k - i)) 0 (Prims.op_Addition k 1)
           = coeff (poly_mul a b) k)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cc : nat -> t = fun (i:nat) -> coeff a i * coeff b (k - i) in
    let kk1 : nat = Prims.op_Addition k 1 in
    let lp : nat = L.length a in
    let mm : nat = Prims.op_Addition kk1 lp in
    (* sum cc 0 kk1 = sum cc 0 lp  (both extend to mm with zero tails) *)
    sum_range_split cc 0 kk1 mm;
    sum_range_all_zero cc kk1 mm (fun (i:nat{kk1 <= i /\ i < mm}) -> H.x_mul_zero (coeff a i));
    H.x_plus_zero (sum_range cc 0 kk1);
    add_congruence (sum_range cc 0 kk1) (sum_range cc kk1 mm) (sum_range cc 0 kk1) (zero <: t);
    sum_range_split cc 0 lp mm;
    sum_range_all_zero cc lp mm (fun (i:nat{lp <= i /\ i < mm}) -> H.zero_mul_x (coeff b (k - i)));
    H.x_plus_zero (sum_range cc 0 lp);
    add_congruence (sum_range cc 0 lp) (sum_range cc lp mm) (sum_range cc 0 lp) (zero <: t);
    CC.coeff_poly_mul_named a b k cc (fun (i:nat) -> reflexivity (coeff a i * coeff b (k - i)));
    (* chain: sum cc 0 kk1 = sum cc 0 mm = sum cc 0 lp = coeff(ab)k *)
    transitivity (sum_range cc 0 kk1) (sum_range cc 0 kk1 + sum_range cc kk1 mm) (sum_range cc 0 kk1 + (zero <: t));
    transitivity (sum_range cc 0 lp) (sum_range cc 0 lp + sum_range cc lp mm) (sum_range cc 0 lp + (zero <: t));
    symmetry (sum_range cc 0 lp) (sum_range cc 0 mm);
    transitivity (sum_range cc 0 kk1) (sum_range cc 0 mm) (sum_range cc 0 lp);
    transitivity (sum_range cc 0 kk1) (sum_range cc 0 lp) (coeff (poly_mul a b) k)

(* abstract ring rearrangement (canon_ring works on an abstract instance var). *)
let mul4_swap (#p:Type) {| pr: commutative_ring p |} (a u b v: p)
  : Lemma ((a * u) * (b * v) = (a * b) * (u * v))
  = assert ((a * u) * (b * v) = (a * b) * (u * v)) by (Core.Tactics.CanonRing.canon_ring ())

(* per-k bridge:  conv_sum (subst_term h a) (subst_term h b) k ~ subst_term h (a*b) k. *)
let subst_conv (#t:Type) {| cr: commutative_ring t |} (h a b: polynomial t) (k: nat)
  : Lemma (poly_eq (CV.conv_sum #(polynomial t) #(pcr cr) (subst_term h a) (subst_term h b) k)
                   (subst_term h (poly_mul a b) k))
  = H.elim_equatable_laws (polynomial t) #((pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial t) #((pacg cr).acg_eq) ();
    let fa = subst_term h a in
    let fb = subst_term h b in
    let ck = E.cpow #(polynomial t) #(pcr cr) h k in
    let cc : nat -> t = fun (i:nat) -> coeff a i * coeff b (k - i) in
    let cc0 : nat -> polynomial t = fun (i:nat) -> const0 (cc i) in
    let kk1 : nat = Prims.op_Addition k 1 in
    let term_cb (i:nat{0 <= i /\ i < kk1})
      : Lemma (poly_eq (CV.conv_term fa fb k i) (pointwise_mul cc0 (const ck) i)) =
      let cai0 = const0 (coeff a i) in
      let cbi0 = const0 (coeff b (k - i)) in
      let pi  = E.cpow #(polynomial t) #(pcr cr) h i in
      let pki = E.cpow #(polynomial t) #(pcr cr) h (k - i) in
      mul4_swap #(polynomial t) #(pcr cr) cai0 pi cbi0 pki;     (* (cai0*pi)*(cbi0*pki) = (cai0*cbi0)*(pi*pki) *)
      E.cpow_add #(polynomial t) #(pcr cr) h i (k - i);          (* ck = pi*pki *)
      const0_mul (coeff a i) (coeff b (k - i));                  (* cc0 i ~ cai0*cbi0 *)
      mul_congruence #(polynomial t) #((pcr cr).cr_r)
        (poly_mul cai0 cbi0) (poly_mul pi pki) (cc0 i) ck;
      transitivity #(polynomial t) #((pacg cr).acg_eq)
        (CV.conv_term fa fb k i)
        (poly_mul (poly_mul cai0 cbi0) (poly_mul pi pki))
        (poly_mul (cc0 i) ck)
    in
    sum_range_congruence #(polynomial t) #(pacg cr)
      (CV.conv_term fa fb k) (pointwise_mul cc0 (const ck)) 0 kk1 term_cb;
    sum_range_mul_right #(polynomial t) #((pcr cr).cr_r) cc0 ck 0 kk1;
    (* sum cc0 0 kk1 ~ const0 (coeff (a*b) k) *)
    const0_sum_range cc cc0 0 kk1 (fun (i:nat) -> reflexivity #(polynomial t) #((pacg cr).acg_eq) (cc0 i));
    conv_coeff_t a b k;                                           (* sum cc 0 kk1 = coeff(ab)k *)
    const0_congr (sum_range cc 0 kk1) (coeff (poly_mul a b) k);   (* const0(sum cc) ~ const0(coeff(ab)k) *)
    symmetry #(polynomial t) #((pacg cr).acg_eq)
      (const0 (sum_range cc 0 kk1)) (sum_range #(polynomial t) #(pacg cr) cc0 0 kk1);
    transitivity #(polynomial t) #((pacg cr).acg_eq)
      (sum_range #(polynomial t) #(pacg cr) cc0 0 kk1)
      (const0 (sum_range cc 0 kk1)) (const0 (coeff (poly_mul a b) k));
    reflexivity #(polynomial t) #((pacg cr).acg_eq) ck;
    mul_congruence #(polynomial t) #((pcr cr).cr_r)
      (sum_range #(polynomial t) #(pacg cr) cc0 0 kk1) ck (const0 (coeff (poly_mul a b) k)) ck;
    (* assemble:  conv_sum = (sum cc0)*ck ~ const0(coeff(ab)k)*ck = subst_term h (ab) k *)
    transitivity #(polynomial t) #((pacg cr).acg_eq)
      (CV.conv_sum #(polynomial t) #(pcr cr) fa fb k)
      (poly_mul (sum_range #(polynomial t) #(pacg cr) cc0 0 kk1) ck)
      (poly_mul (const0 (coeff (poly_mul a b) k)) ck)

(* coeff (a*b) k vanishes (hence subst_term) for k >= len a + len b. *)
let subst_pq_high (#t:Type) {| cr: commutative_ring t |} (h a b: polynomial t) (k: nat)
  : Lemma (requires k >= L.length a + L.length b)
          (ensures poly_eq (subst_term h (poly_mul a b) k) (poly_zero #t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cc : nat -> t = fun (i:nat) -> coeff a i * coeff b (k - i) in
    CC.coeff_poly_mul_named a b k cc (fun (i:nat) -> reflexivity (coeff a i * coeff b (k - i)));
    sum_range_all_zero cc 0 (L.length a)
      (fun (i:nat{0 <= i /\ i < L.length a}) -> H.x_mul_zero (coeff a i));
    (* coeff (a*b) k = 0, so const0 (coeff (a*b) k) ~ poly_zero, times ck ~ poly_zero *)
    const0_congr (coeff (poly_mul a b) k) (zero <: t);
    const0_zero #t #cr ();
    H.elim_equatable_laws (polynomial t) #((pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial t) #((pacg cr).acg_eq) ();
    let ck = E.cpow #(polynomial t) #(pcr cr) h k in
    transitivity #(polynomial t) #((pacg cr).acg_eq)
      (const0 (coeff (poly_mul a b) k)) (const0 (zero <: t)) (poly_zero #t);
    H.zero_mul_x #(polynomial t) #((pcr cr).cr_r) ck;
    mul_congruence #(polynomial t) #((pcr cr).cr_r)
      (const0 (coeff (poly_mul a b) k)) ck (poly_zero #t) ck;
    transitivity #(polynomial t) #((pacg cr).acg_eq)
      (subst_term h (poly_mul a b) k) (poly_mul (poly_zero #t) ck) (poly_zero #t)

(* MULTIPLICATIVITY:  phi_h(a * b) = phi_h(a) * phi_h(b). *)
let subst_mul (#t:Type) {| cr: commutative_ring t |} (h a b: polynomial t)
  : Lemma (poly_eq (poly_subst h (poly_mul a b)) (poly_mul (poly_subst h a) (poly_subst h b)))
  = H.elim_equatable_laws (polynomial t) #((pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial t) #((pacg cr).acg_eq) ();
    let fa = subst_term h a in
    let fb = subst_term h b in
    let bnd : nat = Prims.op_Addition (L.length a) (L.length b) in
    let mm : nat = Prims.op_Addition (L.length (poly_mul a b)) bnd in
    let etab : nat -> polynomial t = subst_term h (poly_mul a b) in
    CV.sum_range_convolution #(polynomial t) #(pcr cr) fa fb (L.length a) (L.length b)
      (fun (i:nat{i >= L.length a}) -> subst_term_high h a i)
      (fun (j:nat{j >= L.length b}) -> subst_term_high h b j);
    sum_range_congruence #(polynomial t) #(pacg cr)
      (CV.conv_sum #(polynomial t) #(pcr cr) fa fb) etab 0 bnd
      (fun (k:nat{0 <= k /\ k < bnd}) -> subst_conv h a b k);
    subst_extend h (poly_mul a b) mm;
    sum_range_split #(polynomial t) #(pacg cr) etab 0 bnd mm;
    sum_range_all_zero #(polynomial t) #(pacg cr) etab bnd mm
      (fun (k:nat{bnd <= k /\ k < mm}) -> subst_pq_high h a b k);
    H.x_plus_zero #(polynomial t) #(pacg cr) (sum_range #(polynomial t) #(pacg cr) etab 0 bnd);
    add_congruence #(polynomial t) #(pacg cr)
      (sum_range #(polynomial t) #(pacg cr) etab 0 bnd) (sum_range #(polynomial t) #(pacg cr) etab bnd mm)
      (sum_range #(polynomial t) #(pacg cr) etab 0 bnd) (poly_zero #t);
    transitivity #(polynomial t) #((pacg cr).acg_eq)
      (poly_subst h (poly_mul a b)) (sum_range #(polynomial t) #(pacg cr) etab 0 mm)
      (poly_add (sum_range #(polynomial t) #(pacg cr) etab 0 bnd) (sum_range #(polynomial t) #(pacg cr) etab bnd mm));
    transitivity #(polynomial t) #((pacg cr).acg_eq)
      (poly_subst h (poly_mul a b))
      (poly_add (sum_range #(polynomial t) #(pacg cr) etab 0 bnd) (sum_range #(polynomial t) #(pacg cr) etab bnd mm))
      (poly_add (sum_range #(polynomial t) #(pacg cr) etab 0 bnd) (poly_zero #t));
    transitivity #(polynomial t) #((pacg cr).acg_eq)
      (poly_subst h (poly_mul a b))
      (poly_add (sum_range #(polynomial t) #(pacg cr) etab 0 bnd) (poly_zero #t))
      (sum_range #(polynomial t) #(pacg cr) etab 0 bnd);
    transitivity #(polynomial t) #((pacg cr).acg_eq)
      (poly_subst h (poly_mul a b))
      (sum_range #(polynomial t) #(pacg cr) (CV.conv_sum #(polynomial t) #(pcr cr) fa fb) 0 bnd)
      (poly_mul (poly_subst h a) (poly_subst h b))

(* subtraction:  phi_h(a - b) = phi_h(a) - phi_h(b). *)
let subst_sub (#t:Type) {| cr: commutative_ring t |} (h a b: polynomial t)
  : Lemma (poly_eq (poly_subst h (poly_sub a b)) (poly_sub (poly_subst h a) (poly_subst h b)))
  = H.elim_equatable_laws (polynomial t) #((pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial t) #((pacg cr).acg_eq) ();
    poly_sub_reveal a b;                                 (* poly_sub a b == poly_add a (poly_neg b) *)
    subst_add h a (poly_neg b);                          (* phi(a + neg b) ~ phi a + phi(neg b) *)
    subst_neg h b;                                       (* phi(neg b) ~ neg (phi b) *)
    reflexivity #(polynomial t) #((pacg cr).acg_eq) (poly_subst h a);
    add_congruence #(polynomial t) #(pacg cr)
      (poly_subst h a) (poly_subst h (poly_neg b)) (poly_subst h a) (poly_neg (poly_subst h b));
    poly_sub_reveal (poly_subst h a) (poly_subst h b);   (* poly_sub (phi a)(phi b) == poly_add (phi a)(poly_neg (phi b)) *)
    transitivity #(polynomial t) #((pacg cr).acg_eq)
      (poly_subst h (poly_sub a b))
      (poly_add (poly_subst h a) (poly_subst h (poly_neg b)))
      (poly_add (poly_subst h a) (poly_neg (poly_subst h b)))
