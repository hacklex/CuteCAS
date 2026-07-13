module Core.Factor.BerlekampRepr

(* ================================================================ *)
(*  C5e — the matrix <-> Frobenius REPRESENTATION and the discharge  *)
(*  of  kernel_span_cover_t,  making  berlekamp_factor_all_irreducible*)
(*  UNCONDITIONAL.                                                    *)
(*                                                                   *)
(*  B.1  berlekamp_matrix_represents  : the transposed Berlekamp      *)
(*       matrix computes  h |-> (h^p mod fbar) - h  under mat_vec_mul.*)
(*  B.2  in_kernel_iff_berlekamp      : its null space = B(fbar).     *)
(*  B.3  span-lift + const_mod closure.                              *)
(*  B.4  CRT lift + discharge kernel_span_cover_t.                   *)
(*  B.5  berlekamp_factor_all_irreducible UNCONDITIONAL.             *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L   = FStar.List.Tot
module NS  = Core.LinearAlgebra.FpNullSpace
module BF  = Core.Factor.BerlekampFactor
module FM  = Core.Factor.FrobeniusMatrix
module BC3 = Core.Factor.BerlekampComplete3
module CM  = Core.Algebra.CongruenceMod
module CS  = Core.Polynomial.Coeff
module IR  = Core.Polynomial.Irreducible
module H   = Core.Algebra.Helpers
module EU  = Core.NumberTheory

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.FinSum
open Core.Algebra.Combinators
open Core.Modular.PrimeField
open Core.Tactics.CanonRing

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ================================================================ *)
(*  0.  generic ring / congruence helpers.                          *)
(* ================================================================ *)

(* additive 2x2 subtraction regroup, in any commutative ring. *)
let ring_2x2_sub (#t:Type) {| cr: commutative_ring t |} (a b c d: t)
  : Lemma (((a + (- b)) + (c + (- d))) = ((a + c) + (- (b + d))))
  = H.elim_equatable_laws t ();
    assert (((a + (- b)) + (c + (- d))) `eq` ((a + c) + (- (b + d))))
      by (canon_ring ())

(* (b + r) - b = r, in any commutative ring. *)
let add_sub_cancel (#t:Type) {| cr: commutative_ring t |} (b r: t)
  : Lemma (((b + r) -- b) = r)
  = H.elim_equatable_laws t ();
    assert (((b + r) + (- b)) `eq` r) by (canon_ring ())

(* (a - b) + (b - c) = a - c, in any commutative ring. *)
let sub_chain (#t:Type) {| cr: commutative_ring t |} (a b c: t)
  : Lemma (((a -- b) + (b -- c)) = (a -- c))
  = H.elim_equatable_laws t ();
    assert (((a + (- b)) + (b + (- c))) `eq` (a + (- c))) by (canon_ring ())

(* congruence of negation. *)
let cong_neg (#t:Type) {| cr: commutative_ring t |} (m x y: t)
  : Lemma (requires CM.cong m x y) (ensures CM.cong m (- x) (- y))
  = H.elim_equatable_laws t ();
    CM.cong_reveal m x y;                       (* m | (x + (- y)) *)
    divides_neg m (x + (- y));                  (* m | (- (x + (- y))) *)
    H.neg_of_sum x (- y);                        (* - (x + (- y)) = (- (- y)) + (- x) *)
    divides_congruence_right m (- (x + (- y))) ((- (- y)) + (- x));
    add_commutativity (- (- y)) (- x);           (* = (- x) + (- (- y)) *)
    divides_congruence_right m ((- (- y)) + (- x)) ((- x) + (- (- y)));
    CM.cong_reveal m (- x) (- y)

(* congruence of subtraction. *)
let cong_sub (#t:Type) {| cr: commutative_ring t |} (m a b c d: t)
  : Lemma (requires CM.cong m a c /\ CM.cong m b d)
          (ensures  CM.cong m (a -- b) (c -- d))
  = cong_neg m b d;
    CM.cong_add m a c (- b) (- d)

(* ================================================================ *)
(*  1.  sum_range : pointwise congruence -> congruence of the sums.  *)
(* ================================================================ *)

let rec cong_sum_range (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  (f g: nat -> polynomial (fp p)) (lo hi: nat)
  (pf: (i:nat{lo <= i /\ i < hi}) ->
       Lemma (CM.cong #(polynomial (fp p)) fbar (f i) (g i)))
  : Lemma (ensures CM.cong #(polynomial (fp p)) fbar
                     (sum_range f lo hi) (sum_range g lo hi))
          (decreases (hi - lo))
  = if lo >= hi then begin
      sum_range_empty f lo hi;
      sum_range_empty g lo hi;
      CM.cong_of_eq #(polynomial (fp p)) fbar (sum_range f lo hi) (sum_range g lo hi)
    end
    else begin
      sum_range_unfold_right f lo hi;
      sum_range_unfold_right g lo hi;
      cong_sum_range p fbar f g lo (hi - 1) pf;
      pf (hi - 1);
      let sfh : polynomial (fp p) = (sum_range f lo (hi - 1)) + (f (hi - 1)) in
      let sgh : polynomial (fp p) = (sum_range g lo (hi - 1)) + (g (hi - 1)) in
      CM.cong_add #(polynomial (fp p)) fbar
        (sum_range f lo (hi - 1)) (sum_range g lo (hi - 1))
        (f (hi - 1)) (g (hi - 1));                              (* cong sfh sgh *)
      CM.cong_of_eq #(polynomial (fp p)) fbar (sum_range f lo hi) sfh;
      CM.cong_trans #(polynomial (fp p)) fbar (sum_range f lo hi) sfh sgh;
      CM.cong_of_eq #(polynomial (fp p)) fbar (sum_range g lo hi) sgh;
      CM.cong_sym #(polynomial (fp p)) fbar (sum_range g lo hi) sgh;
      CM.cong_trans #(polynomial (fp p)) fbar
        (sum_range f lo hi) sgh (sum_range g lo hi)
    end

(* ================================================================ *)
(*  2.  sum_range of a pointwise difference splits.                  *)
(* ================================================================ *)

let sub_congruence (#t:Type) {| cr: commutative_ring t |} (a b a' b': t)
  : Lemma (requires a = a' /\ b = b') (ensures (a -- b) = (a' -- b'))
  = H.elim_equatable_laws t ();
    neg_congruence b b';
    add_congruence a (- b) a' (- b')

(* pure poly_eq chaining for sum_range_sub, isolated in a fuel-0 VC over
   abstract atoms to avoid poly_eq unfolding blowup. *)
private
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let sum_sub_glue (#p:int{EU.is_prime p}) (sfun sa sf sng sg : polynomial (fp p))
  : Lemma (requires sfun = sa /\ sa = (sf + sng) /\ sng = (- sg))
          (ensures  sfun = (sf -- sg))
  = poly_eq_reflexivity sf;
    add_congruence sf sng sf (- sg);
    poly_eq_transitivity sfun sa (sf + sng);
    poly_eq_transitivity sfun (sf + sng) (sf -- sg)
#pop-options

(* sum_range of a pointwise difference splits — via the proven library
   lemmas sum_range_add / sum_range_neg (offloads the 2x2 regroup). *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let sum_range_sub (p:int{EU.is_prime p})
  (f g: nat -> polynomial (fp p)) (lo hi: nat)
  : Lemma (ensures (sum_range (fun (i:nat) -> (f i) -- (g i)) lo hi)
                   = ((sum_range f lo hi) -- (sum_range g lo hi)))
  = let ng : nat -> polynomial (fp p) = pointwise_neg g in
    sum_range_congruence #(polynomial (fp p)) (fun (i:nat) -> (f i) -- (g i))
      (pointwise_add f ng) lo hi
      (fun (k:nat{lo <= k /\ k < hi}) -> poly_eq_reflexivity ((f k) -- (g k)));
    sum_range_add #(polynomial (fp p)) f ng lo hi;      (* sa = sf + sng *)
    sum_range_neg #(polynomial (fp p)) g lo hi;         (* sng = - sg *)
    sum_sub_glue #p (sum_range (fun (i:nat) -> (f i) -- (g i)) lo hi)
                    (sum_range (pointwise_add f ng) lo hi)
                    (sum_range f lo hi) (sum_range ng lo hi) (sum_range g lo hi)
#pop-options

(* ================================================================ *)
(*  3.  degrees + the FROBENIUS-LINEARITY identity  (B.1a).         *)
(* ================================================================ *)

let pdeg_eq (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  : Lemma (BF.pdeg fbar == deg fbar) = ()

(* a polynomial whose coefficients vanish from index k on has deg < k. *)
let deg_bound_of_coeffs (#t:Type) {| cr: commutative_ring t |}
  (q: polynomial t) (k:nat)
  (pf: (i:nat{i >= k}) -> Lemma (coeff q i = (zero <: t)))
  : Lemma (deg q < k)
  = if deg q >= 0 then begin
      let d : nat = deg q in
      if d < k then ()
      else (pf d; leading_coeff_nonzero q)
    end

(* congruent mod fbar + both below deg fbar  ==>  equal. *)
let cong_deg_eq (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (a b: polynomial (fp p))
  : Lemma (requires CM.cong #(polynomial (fp p)) fbar a b /\
                    deg a < BF.pdeg fbar /\ deg b < BF.pdeg fbar)
          (ensures  a = b)
  = let n : nat = BF.pdeg fbar in
    CM.cong_reveal #(polynomial (fp p)) fbar a b;   (* fbar | (a + (- b)) = (a -- b) *)
    poly_sub_degree_bound a b n;                    (* deg (a -- b) < n = deg fbar *)
    if deg (a -- b) >= 0 then IR.divides_degree_le #(fp p) fbar (a -- b);
    Core.Polynomial.Unique.degree_none_poly_eq_zero #(fp p) (a -- b);
    Core.Polynomial.Unique.sub_zero_implies_eq #(fp p) a b

(* left multiplication distributes over subtraction. *)
let mul_sub_left (#t:Type) {| cr: commutative_ring t |} (a b c: t)
  : Lemma ((a * (b -- c)) = ((a * b) -- (a * c)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    left_distributivity a b (- c);                  (* a*(b + (-c)) = a*b + a*(-c) *)
    H.neg_mul_r a c;                                 (* a*(-c) = -(a*c) *)
    add_congruence (a * b) (a * (- c)) (a * b) (- (a * c))

(* the per-monomial Frobenius image stays below deg fbar. *)
let deg_frob_x (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (i:nat{i < BF.pdeg fbar})
  : Lemma (deg (FM.frob_x p fbar i) < BF.pdeg fbar)
  = let n : nat = BF.pdeg fbar in
    let xi = BF.mono_x p i in
    let qi = poly_rem (poly_power xi (p <: nat)) fbar in
    (* deg qi < deg fbar = n *)
    let _ = poly_rem (poly_power xi (p <: nat)) fbar in
    monomial_deg #(fp p) (fp_one p) i;              (* deg xi = i (fp_one <> 0) *)
    fp_one_ne_zero p;
    assert (deg xi == i);
    poly_sub_degree_bound qi xi n


(* the k-th coefficient of the i-th linear-combination term. *)
let pterm (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  (h: polynomial (fp p)) (i:nat) : polynomial (fp p)
  = (poly_const #(fp p) (coeff h i)) * (FM.frob_x p fbar i)

let gk (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  (h: polynomial (fp p)) (k:nat) (i:nat) : fp p
  = (coeff h i) * (coeff (FM.frob_x p fbar i) k)

let term_coeff (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  (h: polynomial (fp p)) (i k:nat)
  : Lemma (coeff (pterm p fbar h i) k = gk p fbar h k i)
  = H.elim_equatable_laws (fp p) ();
    monomial_mul_coeff #(fp p) (coeff h i) 0 (FM.frob_x p fbar i) k

(* coeff of the whole linear combination = the pointwise sum. *)
let coeff_S (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  (h: polynomial (fp p)) (k n:nat)
  : Lemma (coeff (sum_range (pterm p fbar h) 0 n) k
           = sum_range (gk p fbar h k) 0 n)
  = H.elim_equatable_laws (fp p) ();
    CS.coeff_sum_range #(fp p) (pterm p fbar h) 0 n k;
    let lhs_fn (i:nat) : fp p = coeff (pterm p fbar h i) k in
    sum_range_congruence #(fp p) lhs_fn (gk p fbar h k) 0 n
      (fun (i:nat{0 <= i /\ i < n}) -> term_coeff p fbar h i k);
    transitivity (coeff (sum_range (pterm p fbar h) 0 n) k)
                 (sum_range lhs_fn 0 n)
                 (sum_range (gk p fbar h k) 0 n)

(* the linear combination stays below deg fbar. *)
let deg_S (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (h: polynomial (fp p)) (n:nat)
  : Lemma (requires n == BF.pdeg fbar)
          (ensures  deg (sum_range (pterm p fbar h) 0 n) < n)
  = H.elim_equatable_laws (fp p) ();
    let kpf (k:nat{k >= n}) : Lemma (coeff (sum_range (pterm p fbar h) 0 n) k = (zero <: fp p))
      = coeff_S p fbar h k n;
        let ipf (i:nat{0 <= i /\ i < n}) : Lemma (gk p fbar h k i = (zero <: fp p))
          = deg_frob_x p fbar i;                              (* deg frob_x i < n <= k *)
            coeff_above_degree #(fp p) (FM.frob_x p fbar i) k; (* coeff (frob_x i) k = zero *)
            mul_congruence (coeff h i) (coeff (FM.frob_x p fbar i) k)
                           (coeff h i) (zero <: fp p);
            H.x_mul_zero #(fp p) (coeff h i);
            transitivity (gk p fbar h k i)
                         ((coeff h i) * (zero <: fp p)) (zero <: fp p)
        in
        sum_range_all_zero #(fp p) (gk p fbar h k) 0 n ipf;
        transitivity (coeff (sum_range (pterm p fbar h) 0 n) k)
                     (sum_range (gk p fbar h k) 0 n) (zero <: fp p)
    in
    deg_bound_of_coeffs #(fp p) (sum_range (pterm p fbar h) 0 n) n kpf

(* per-index CONGRUENCE:  term_i  ≡  (monomial c_i i)^p - (monomial c_i i). *)
(* pure poly_eq bridge  c0*(hp--xi) = pwmi -- mi , isolated at fuel 0. *)
private
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let mul_sub_bridge (#p:int{EU.is_prime p}) (c0 hp xi pwmi mi : polynomial (fp p))
  : Lemma (requires (c0 * hp) = pwmi /\ (c0 * xi) = mi)
          (ensures  (c0 * (hp -- xi)) = (pwmi -- mi))
  = mul_sub_left #(polynomial (fp p)) c0 hp xi;              (* c0*(hp--xi) = (c0*hp)--(c0*xi) *)
    sub_congruence #(polynomial (fp p)) (c0 * hp) (c0 * xi) pwmi mi;
    poly_eq_transitivity (c0 * (hp -- xi)) ((c0 * hp) -- (c0 * xi)) (pwmi -- mi)
#pop-options

let term_cong (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  (h: polynomial (fp p)) (i:nat)
  : Lemma (CM.cong #(polynomial (fp p)) fbar
             (pterm p fbar h i)
             ((BC3.pw p (monomial #(fp p) (coeff h i) i)) -- (monomial #(fp p) (coeff h i) i)))
  = let c  : fp p = coeff h i in
    let xi : polynomial (fp p) = BF.mono_x p i in
    let hp : polynomial (fp p) = poly_power #(fp p) xi (p <: nat) in
    let qi : polynomial (fp p) = poly_rem hp fbar in
    let mi : polynomial (fp p) = monomial #(fp p) c i in
    let c0 : polynomial (fp p) = poly_const #(fp p) c in
    (* frob_x i = qi -- xi *)
    assert (FM.frob_x p fbar i == (qi -- xi));
    (* cong fbar qi hp *)
    let dv : polynomial (fp p) = fst (poly_divmod #(fp p) hp fbar) in
    CM.cong_of_divmod #(polynomial (fp p)) hp fbar dv qi;   (* cong fbar hp qi *)
    CM.cong_sym #(polynomial (fp p)) fbar hp qi;            (* cong fbar qi hp *)
    (* cong fbar (frob_x i) (hp -- xi) *)
    CM.cong_refl #(polynomial (fp p)) fbar xi;
    cong_sub #(polynomial (fp p)) fbar qi xi hp xi;         (* cong (qi -- xi) (hp -- xi) *)
    (* cong fbar (pterm i) (c0 * (hp -- xi)) *)
    CM.cong_refl #(polynomial (fp p)) fbar c0;
    CM.cong_mul #(polynomial (fp p)) fbar c0 c0 (qi -- xi) (hp -- xi);
    (* c0 * (hp -- xi) = (c0*hp) -- (c0*xi) = (pw mi) -- mi *)
    BC3.pw_monomial p c i;                                  (* pw mi = c0 * pw xi = c0 * hp *)
    poly_eq_symmetry (BC3.pw p mi) (c0 * hp);               (* c0*hp = pw mi *)
    BC3.mono_const_eq p c i;                                (* mi = c0 * xi *)
    poly_eq_symmetry mi (c0 * xi);                          (* c0*xi = mi *)
    mul_sub_bridge #p c0 hp xi (BC3.pw p mi) mi;            (* c0*(hp--xi) = (pw mi)--mi *)
    CM.cong_eq_right #(polynomial (fp p)) fbar
      (pterm p fbar h i) (c0 * (hp -- xi)) ((BC3.pw p mi) -- mi)

(* the monomial component functions (named, to keep sums lambda-stable). *)
let mm (p:int{EU.is_prime p}) (h: polynomial (fp p)) (i:nat) : polynomial (fp p)
  = monomial #(fp p) (coeff h i) i

let pwm (p:int{EU.is_prime p}) (h: polynomial (fp p)) (i:nat) : polynomial (fp p)
  = BC3.pw p (mm p h i)

(* B.1a — the Frobenius(-id) endomorphism as an explicit linear combination.
   SPLIT into three small VCs (each << 10s) to avoid the monolithic 60s query. *)

(* step 1+2 : cong fbar s (bigP -- bigM). *)
private
let frob_step_s_cong (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (h: polynomial (fp p)) (n:nat)
  : Lemma (requires n == BF.pdeg fbar /\ deg h < n)
          (ensures  CM.cong #(polynomial (fp p)) fbar
                      (sum_range (pterm p fbar h) 0 n)
                      ((sum_range (pwm p h) 0 n) -- (sum_range (mm p h) 0 n)))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let s    : polynomial (fp p) = sum_range (pterm p fbar h) 0 n in
    let bigM : polynomial (fp p) = sum_range (mm p h) 0 n in
    let bigP : polynomial (fp p) = sum_range (pwm p h) 0 n in
    cong_sum_range p fbar (pterm p fbar h)
      (fun (i:nat) -> (pwm p h i) -- (mm p h i)) 0 n
      (fun (i:nat{0 <= i /\ i < n}) -> term_cong p fbar h i);
    sum_range_sub p (pwm p h) (mm p h) 0 n;
    CM.cong_eq_right #(polynomial (fp p)) fbar s
      (sum_range (fun (i:nat) -> (pwm p h i) -- (mm p h i)) 0 n) (bigP -- bigM)

(* step 3 : bigM = h. *)
private
let frob_step_bigM_eq (p:int{EU.is_prime p})
  (h: polynomial (fp p)) (n:nat)
  : Lemma (requires deg h < n)
          (ensures (sum_range (mm p h) 0 n) = h)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    H.trans_for_calc (polynomial (fp p)) ();
    let bigM : polynomial (fp p) = sum_range (mm p h) 0 n in
    CS.monomial_decomposition #(fp p) h n;
    sum_range_congruence #(polynomial (fp p)) (mm p h)
      (fun (i:nat) -> monomial #(fp p) (coeff h i) i) 0 n
      (fun (k:nat{0 <= k /\ k < n}) -> reflexivity (mm p h k));
    transitivity bigM (sum_range (fun (i:nat) -> monomial #(fp p) (coeff h i) i) 0 n) h

(* step 4 : cong fbar (h^p) bigP. *)
private
let frob_step_hph_cong (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (h: polynomial (fp p)) (n:nat)
  : Lemma (requires deg h < n)
          (ensures CM.cong #(polynomial (fp p)) fbar
                     (poly_power #(fp p) h (p <: nat)) (sum_range (pwm p h) 0 n))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let bigM : polynomial (fp p) = sum_range (mm p h) 0 n in
    let bigP : polynomial (fp p) = sum_range (pwm p h) 0 n in
    let hph  : polynomial (fp p) = poly_power #(fp p) h (p <: nat) in
    frob_step_bigM_eq p h n;                               (* bigM = h *)
    BC3.frob_sum_mod p fbar (mm p h) 0 n;
    sum_range_congruence #(polynomial (fp p)) (fun (i:nat) -> BC3.pw p (mm p h i)) (pwm p h) 0 n
      (fun (k:nat{0 <= k /\ k < n}) -> reflexivity (pwm p h k));
    poly_power_congruence #(fp p) bigM h (p <: nat);       (* pw bigM = hph *)
    poly_eq_symmetry hph (BC3.pw p bigM);
    CM.cong_of_eq #(polynomial (fp p)) fbar hph (BC3.pw p bigM);
    CM.cong_trans #(polynomial (fp p)) fbar hph (BC3.pw p bigM)
      (sum_range (fun (i:nat) -> BC3.pw p (mm p h i)) 0 n);
    CM.cong_eq_right #(polynomial (fp p)) fbar hph
      (sum_range (fun (i:nat) -> BC3.pw p (mm p h i)) 0 n) bigP

(* step 5+6 : cong fbar (bigP -- bigM) (h^p -- h)  and  cong fbar (frob h) (h^p -- h). *)
private
let frob_step_diff_cong (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (h: polynomial (fp p)) (n:nat)
  : Lemma (requires n == BF.pdeg fbar /\ deg h < n)
          (ensures  CM.cong #(polynomial (fp p)) fbar
                       ((sum_range (pwm p h) 0 n) -- (sum_range (mm p h) 0 n))
                       ((poly_power #(fp p) h (p <: nat)) -- h) /\
                    CM.cong #(polynomial (fp p)) fbar
                       (FM.frob p fbar h)
                       ((poly_power #(fp p) h (p <: nat)) -- h))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let bigM : polynomial (fp p) = sum_range (mm p h) 0 n in
    let bigP : polynomial (fp p) = sum_range (pwm p h) 0 n in
    let hph  : polynomial (fp p) = poly_power #(fp p) h (p <: nat) in
    (* step 6 : bigP -- bigM  ~  hph -- h *)
    frob_step_hph_cong p fbar h n;                         (* cong hph bigP *)
    frob_step_bigM_eq p h n;                               (* bigM = h *)
    CM.cong_sym #(polynomial (fp p)) fbar hph bigP;        (* cong bigP hph *)
    CM.cong_of_eq #(polynomial (fp p)) fbar bigM h;        (* cong bigM h *)
    cong_sub #(polynomial (fp p)) fbar bigP bigM hph h;
    (* step 5 : frob h  ~  hph -- h *)
    let qi : polynomial (fp p) = poly_rem hph fbar in
    let dv : polynomial (fp p) = fst (poly_divmod #(fp p) hph fbar) in
    assert (FM.frob p fbar h == (qi -- h));
    CM.cong_of_divmod #(polynomial (fp p)) hph fbar dv qi;
    CM.cong_sym #(polynomial (fp p)) fbar hph qi;
    CM.cong_refl #(polynomial (fp p)) fbar h;
    cong_sub #(polynomial (fp p)) fbar qi h hph h

let frob_eq_sum (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (h: polynomial (fp p)) (n:nat)
  : Lemma (requires n == BF.pdeg fbar /\ deg h < n)
          (ensures  FM.frob p fbar h = sum_range (pterm p fbar h) 0 n)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let s    : polynomial (fp p) = sum_range (pterm p fbar h) 0 n in
    let bigM : polynomial (fp p) = sum_range (mm p h) 0 n in
    let bigP : polynomial (fp p) = sum_range (pwm p h) 0 n in
    let hph  : polynomial (fp p) = poly_power #(fp p) h (p <: nat) in
    frob_step_s_cong p fbar h n;                           (* cong s (bigP -- bigM) *)
    frob_step_diff_cong p fbar h n;                        (* cong (bigP--bigM)(hph--h); cong (frob h)(hph--h) *)
    CM.cong_trans #(polynomial (fp p)) fbar s (bigP -- bigM) (hph -- h);   (* cong s (hph--h) *)
    CM.cong_sym #(polynomial (fp p)) fbar s (hph -- h);
    CM.cong_trans #(polynomial (fp p)) fbar (FM.frob p fbar h) (hph -- h) s;
    (* degree bounds + upgrade *)
    let qi : polynomial (fp p) = poly_rem hph fbar in
    poly_sub_degree_bound qi h n;
    deg_S p fbar h n;
    cong_deg_eq p fbar (FM.frob p fbar h) s

(* ================================================================ *)
(*  4.  the dot <-> sum_range bridge, and B.1 / B.2.               *)
(* ================================================================ *)

(* the transpose entry is the coefficient of the per-monomial image. *)
let mT_entry_is_coeff (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (i:nat) (k:nat{k < BF.pdeg fbar})
  : Lemma (BF.mT_entry p fbar i k == coeff (FM.frob_x p fbar i) k)
  = FM.berlekamp_row_is_frob_x p fbar i;                 (* berlekamp_row = vec_of (frob_x i) 0 n *)
    FM.vec_of_poly_get #p (BF.pdeg fbar) (FM.frob_x p fbar i) k

(* dot of a transpose row with the coordinate vector = the pointwise product sum. *)
let rec dot_mT_vec (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (h: polynomial (fp p)) (k:nat) (i0 cnt:nat)
  : Lemma (ensures NS.dot (BF.mT_row p fbar k i0 cnt) (BF.vec_of h i0 cnt)
                   = sum_range (fun (i:nat) -> (BF.mT_entry p fbar i k) * (coeff h i))
                               i0 (i0 ++ cnt))
          (decreases cnt)
  = H.elim_equatable_laws (fp p) ();
    let f (i:nat) : fp p = (BF.mT_entry p fbar i k) * (coeff h i) in
    if cnt = 0 then begin
      (* dot [] [] = fp_zero = zero ; sum empty = zero *)
      sum_range_empty f i0 (i0 ++ cnt)
    end
    else begin
      dot_mT_vec p fbar h k (i0 ++ 1) (cnt - 1);           (* IH *)
      sum_range_unfold_left f i0 (i0 ++ cnt);              (* sum = f i0 + sum (i0+1) .. *)
      reflexivity (f i0)
    end

(* ---- B.1  berlekamp_matrix_represents ---- *)

(* index of a matrix-vector product is the dot of the indexed row. *)
let rec mvm_get (p:int{EU.is_prime p}) (m: list (NS.vector p)) (v: NS.vector p) (k:nat)
  : Lemma (requires k < L.length m)
          (ensures  NS.get (NS.mat_vec_mul m v) k == NS.dot (L.index m k) v)
          (decreases m)
  = NS.mat_vec_mul_length m v;
    match m with
    | row :: m' -> if k = 0 then () else mvm_get p m' v (k - 1)

(* the k-th entry of  mat_vec_mul (T) (vec_of_poly n h)  equals  coeff (frob h) k. *)
let mvm_entry_eq (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (h: polynomial (fp p)) (k:nat)
  : Lemma (requires deg h < BF.pdeg fbar /\ k < BF.pdeg fbar)
          (ensures  NS.get (NS.mat_vec_mul (BF.berlekamp_matrix_T p fbar)
                              (FM.vec_of_poly (BF.pdeg fbar) h)) k
                    == coeff (FM.frob p fbar h) k)
  = H.elim_equatable_laws (fp p) ();
    let n : nat = BF.pdeg fbar in
    BF.berlekamp_matrix_T_length p fbar;
    mvm_get p (BF.berlekamp_matrix_T p fbar) (FM.vec_of_poly n h) k;
    BF.mT_rows_length p fbar 0 n;
    BF.mT_rows_index p fbar 0 n k;                 (* index T k = mT_row k 0 n *)
    dot_mT_vec p fbar h k 0 n;                     (* dot = sum (mT_entry . coeff) 0 (0++n) *)
    frob_eq_sum p fbar h n;                        (* frob h = S *)
    coeff_S p fbar h k n;                          (* coeff S k = sum gk 0 n *)
    poly_eq_means_equal_coeffs #(fp p) (FM.frob p fbar h) (sum_range (pterm p fbar h) 0 n) k;
    sum_range_congruence #(fp p)
      (fun (i:nat) -> (BF.mT_entry p fbar i k) * (coeff h i)) (gk p fbar h k) 0 n
      (fun (i:nat{0 <= i /\ i < n}) ->
        H.elim_equatable_laws (fp p) ();
        mT_entry_is_coeff p fbar i k;
        fp_mul_commutativity (BF.mT_entry p fbar i k) (coeff h i))

(* B.1 — the transposed Berlekamp matrix represents  h |-> frob h. *)
let berlekamp_matrix_represents (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (h: polynomial (fp p))
  : Lemma (requires deg h < BF.pdeg fbar)
          (ensures  NS.mat_vec_mul (BF.berlekamp_matrix_T p fbar) (FM.vec_of_poly (BF.pdeg fbar) h)
                    == FM.vec_of_poly (BF.pdeg fbar) (FM.frob p fbar h))
  = let n : nat = BF.pdeg fbar in
    let lhs = NS.mat_vec_mul (BF.berlekamp_matrix_T p fbar) (FM.vec_of_poly n h) in
    let rhs = FM.vec_of_poly n (FM.frob p fbar h) in
    NS.mat_vec_mul_length (BF.berlekamp_matrix_T p fbar) (FM.vec_of_poly n h);
    BF.berlekamp_matrix_T_length p fbar;
    FM.vec_of_poly_length #p n (FM.frob p fbar h);
    introduce forall (j:nat). j < L.length lhs ==> NS.get lhs j == NS.get rhs j
    with (introduce _ ==> _ with _hj.
      (mvm_entry_eq p fbar h j;
       FM.vec_of_poly_get #p n (FM.frob p fbar h) j));
    NS.vec_ext lhs rhs

(* ---- B.2 building blocks ---- *)

let berlekamp_implies_frob_zero (p:int{EU.is_prime p})
  (fbar: polynomial (fp p){deg fbar >= 1}) (h: polynomial (fp p))
  : Lemma (requires deg h < BF.pdeg fbar /\
                    CM.cong #(polynomial (fp p)) fbar (poly_power #(fp p) h (p <: nat)) h)
          (ensures  FM.frob p fbar h = (poly_zero #(fp p)))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let hph = poly_power #(fp p) h (p <: nat) in
    let r   = poly_rem hph fbar in
    let dv  = fst (poly_divmod #(fp p) hph fbar) in
    assert (FM.frob p fbar h == (r -- h));
    CM.cong_of_divmod #(polynomial (fp p)) hph fbar dv r;   (* cong fbar hph r *)
    CM.cong_sym #(polynomial (fp p)) fbar hph r;            (* cong fbar r hph *)
    CM.cong_trans #(polynomial (fp p)) fbar r hph h;        (* cong fbar r h *)
    cong_deg_eq p fbar r h;                                 (* r = h *)
    H.sub_self_zero r h                                     (* r -- h = zero *)

let frob_zero_implies_berlekamp (p:int{EU.is_prime p})
  (fbar: polynomial (fp p){deg fbar >= 1}) (h: polynomial (fp p))
  : Lemma (requires deg h < BF.pdeg fbar /\ FM.frob p fbar h = (poly_zero #(fp p)))
          (ensures  CM.cong #(polynomial (fp p)) fbar (poly_power #(fp p) h (p <: nat)) h)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let hph = poly_power #(fp p) h (p <: nat) in
    let r   = poly_rem hph fbar in
    let dv  = fst (poly_divmod #(fp p) hph fbar) in
    assert (FM.frob p fbar h == (r -- h));
    Core.Polynomial.Unique.sub_zero_implies_eq #(fp p) r h;  (* r = h *)
    CM.cong_of_divmod #(polynomial (fp p)) hph fbar dv r;    (* cong fbar hph r *)
    CM.cong_eq_right #(polynomial (fp p)) fbar hph r h       (* cong fbar hph h *)

let vec_of_poly_of_zero (p:int{EU.is_prime p}) (q: polynomial (fp p)) (n:nat)
  : Lemma (requires q = (poly_zero #(fp p)))
          (ensures  FM.vec_of_poly n q == NS.zeros n)
  = NS.zeros_length #p n;
    FM.vec_of_poly_length #p n q;
    introduce forall (j:nat). j < L.length (FM.vec_of_poly n q) ==>
                NS.get (FM.vec_of_poly n q) j == NS.get (NS.zeros n) j
    with (introduce _ ==> _ with _hj.
      (FM.vec_of_poly_get #p n q j;
       poly_eq_means_equal_coeffs #(fp p) q (poly_zero #(fp p)) j;
       NS.get_zeros #p n j));
    NS.vec_ext (FM.vec_of_poly n q) (NS.zeros n)

let vec_zeros_gives_poly_zero (p:int{EU.is_prime p}) (q: polynomial (fp p)) (n:nat)
  : Lemma (requires FM.vec_of_poly n q == NS.zeros n /\ deg q < n)
          (ensures  q = (poly_zero #(fp p)))
  = H.elim_equatable_laws (fp p) ();
    NS.zeros_length #p n;
    FM.vec_of_poly_length #p n q;
    poly_eq_by_coeff #(fp p) q (poly_zero #(fp p))
      (fun (j:nat) ->
        if j < n then begin
          FM.vec_of_poly_get #p n q j;         (* get(vec) j == coeff q j *)
          NS.get_zeros #p n j;                 (* get(zeros) j == fp_zero *)
          poly_eq_means_equal_coeffs #(fp p) (poly_zero #(fp p)) (poly_zero #(fp p)) j
        end
        else coeff_above_degree #(fp p) q j)

(* B.2 — the null space of the transposed matrix = the Berlekamp subalgebra. *)
let in_kernel_iff_berlekamp (p:int{EU.is_prime p})
  (fbar: polynomial (fp p){deg fbar >= 1}) (h: polynomial (fp p))
  : Lemma (requires deg h < BF.pdeg fbar)
          (ensures  (NS.mat_vec_mul (BF.berlekamp_matrix_T p fbar) (FM.vec_of_poly (BF.pdeg fbar) h)
                       == NS.zeros (BF.pdeg fbar))
                    <==> CM.cong #(polynomial (fp p)) fbar (poly_power #(fp p) h (p <: nat)) h)
  = let n : nat = BF.pdeg fbar in
    berlekamp_matrix_represents p fbar h;        (* mvm == vec_of_poly n (frob h) *)
    let hph = poly_power #(fp p) h (p <: nat) in
    introduce CM.cong #(polynomial (fp p)) fbar hph h ==>
              (NS.mat_vec_mul (BF.berlekamp_matrix_T p fbar) (FM.vec_of_poly n h) == NS.zeros n)
    with _.
      (berlekamp_implies_frob_zero p fbar h;
       vec_of_poly_of_zero p (FM.frob p fbar h) n);
    introduce (NS.mat_vec_mul (BF.berlekamp_matrix_T p fbar) (FM.vec_of_poly n h) == NS.zeros n) ==>
              CM.cong #(polynomial (fp p)) fbar hph h
    with _.
      (let r = poly_rem hph fbar in
       poly_sub_degree_bound r h n;              (* deg (frob h) < n *)
       vec_zeros_gives_poly_zero p (FM.frob p fbar h) n;
       frob_zero_implies_berlekamp p fbar h)
