module Core.Polynomial.Split

(* Distinct-roots factorization:

     a polynomial p over a field, with Some?(poly_deg p) = n, having
     n pairwise-distinct roots, equals  lc(p) * (x-c1)*...*(x-cn).

   This is the W2-wall lemma `poly_split_distinct_roots`; with it,
     X^p - X  ~  prod_{c in fp p} (X - c)
   follows (both monic, degree p, agreeing on all p elements). *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Tactics.CanonRing
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Root
open Core.Polynomial.Product
open Core.Polynomial.Unique
open Core.Polynomial.Coeff
open Core.Polynomial.GCD
open Core.Polynomial.Div
open Core.FinSum

(* ================================================================ *)
(*  poly_scale a p = [a] * p  (a * p coefficient-wise via mul).      *)
(* ================================================================ *)

let poly_scale (#t:Type) {| cr: commutative_ring t |} (a: t) (p: polynomial t) : polynomial t =
  poly_mul (a @ poly_zero) p

(* ================================================================ *)
(*  poly_eq preserves the leading coefficient.                       *)
(* ================================================================ *)

let poly_eq_lc (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma (requires poly_eq p q) (ensures poly_lc p = poly_lc q)
  = H.elim_equatable_laws t ();
    poly_eq_length p q;
    if L.length p > 0 then begin
      let i = L.length p - 1 in
      poly_eq_means_equal_coeffs p q i;        (* coeff p i = coeff q i *)
      last_eq_index p i;                        (* L.last p = L.index p i *)
      last_eq_index q i;                        (* L.last q = L.index q i *)
      poly_lc_reveal p; poly_lc_reveal q
    end else begin
      poly_lc_reveal p; poly_lc_reveal q;
      reflexivity (zero <: t)
    end

(* ================================================================ *)
(*  coeff of  (x - a) * A  :  coeff A (k-1) + (-a) * coeff A k.       *)
(* ================================================================ *)

let comm_helper (#t:Type) {| cr: commutative_ring t |} (x v w: t)
  : Lemma (x * v + w = w + x * v)
  = assert (x * v + w = w + x * v) by canon_ring ()

let coeff_linear_mul (#t:Type) {| f: field t |} (a: t) (bigA: polynomial t) (k: nat)
  : Lemma (coeff (poly_mul (poly_linear #t #f a) bigA) k
         = coeff bigA (Prims.op_Subtraction k 1) + (neg a) * coeff bigA k)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    let pl = poly_linear #t #f a in
    assert (L.length pl == 2);
    let g (i:nat) : t = coeff pl i * coeff bigA (Prims.op_Subtraction k i) in
    coeff_poly_mul_named pl bigA k g (fun (i:nat) -> reflexivity (g i));
    sum_range_unfold_left g 0 2;
    sum_range_unfold_left g 1 2;
    sum_range_empty g 2 2;
    H.x_plus_zero (g 1);
    add_congruence (g 1) (sum_range g 2 2) (g 1) (zero <: t);
    transitivity (sum_range g 1 2) (g 1 + sum_range g 2 2) (g 1 + (zero <: t));
    transitivity (sum_range g 1 2) (g 1 + (zero <: t)) (g 1);
    add_congruence (g 0) (sum_range g 1 2) (g 0) (g 1);
    transitivity (sum_range g 0 2) (g 0 + sum_range g 1 2) (g 0 + g 1);
    assert (coeff pl 0 == (neg a <: t));
    reflexivity (coeff bigA k);
    mul_congruence (coeff pl 0) (coeff bigA k) (neg a) (coeff bigA k);
    assert (g 0 == coeff pl 0 * coeff bigA (Prims.op_Subtraction k 0));
    assert (Prims.op_Subtraction k 0 == k);
    transitivity (g 0) (coeff pl 0 * coeff bigA k) ((neg a) * coeff bigA k);
    assert (coeff pl 1 == (one <: t));
    reflexivity (coeff bigA (Prims.op_Subtraction k 1));
    mul_congruence (coeff pl 1) (coeff bigA (Prims.op_Subtraction k 1))
                   (one <: t) (coeff bigA (Prims.op_Subtraction k 1));
    H.one_mul_x (coeff bigA (Prims.op_Subtraction k 1));
    transitivity (g 1) (coeff pl 1 * coeff bigA (Prims.op_Subtraction k 1))
                 ((one <: t) * coeff bigA (Prims.op_Subtraction k 1));
    transitivity (g 1) ((one <: t) * coeff bigA (Prims.op_Subtraction k 1))
                 (coeff bigA (Prims.op_Subtraction k 1));
    add_congruence (g 0) (g 1) ((neg a) * coeff bigA k) (coeff bigA (Prims.op_Subtraction k 1));
    transitivity (sum_range g 0 2) (g 0 + g 1)
                 ((neg a) * coeff bigA k + coeff bigA (Prims.op_Subtraction k 1));
    comm_helper (neg a) (coeff bigA k) (coeff bigA (Prims.op_Subtraction k 1));
    transitivity (sum_range g 0 2)
                 ((neg a) * coeff bigA k + coeff bigA (Prims.op_Subtraction k 1))
                 (coeff bigA (Prims.op_Subtraction k 1) + (neg a) * coeff bigA k);
    symmetry (coeff (poly_mul pl bigA) k) (sum_range g 0 2);
    transitivity (coeff (poly_mul pl bigA) k) (sum_range g 0 2)
                 (coeff bigA (Prims.op_Subtraction k 1) + (neg a) * coeff bigA k)

(* ================================================================ *)
(*  Leading coefficient of  (x - a) * q  equals  lc q.               *)
(* ================================================================ *)

let poly_lc_mul_linear (#t:Type) {| f: field t |} (a: t) (q: polynomial t)
  : Lemma (requires Some? (poly_deg q))
          (ensures  poly_lc (poly_mul (poly_linear #t #f a) q) = poly_lc q)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    let la = poly_linear #t #f a in
    poly_linear_deg #t #f a;                              (* deg la = Some 1 *)
    poly_deg_mul la q;                                    (* deg (la*q) = 1 + deg q *)
    let m = poly_mul la q in
    (* length q >= 1, length m = length q + 1 *)
    let lq = L.length q in
    assert (lq >= 1);
    assert (L.length m == Prims.op_Addition lq 1);
    let k = lq in
    (* coeff m k = coeff q (k-1) + (neg a) * coeff q k *)
    coeff_linear_mul #t #f a q k;
    (* coeff q k = coeff q lq = zero (past the end) *)
    assert (coeff q k == (zero <: t));
    reflexivity (neg a <: t);
    mul_congruence (neg a) (coeff q k) (neg a) (zero <: t);   (* (neg a)*coeff q k = (neg a)*zero *)
    H.x_mul_zero (neg a);                                     (* (neg a)*zero = zero *)
    transitivity ((neg a) * coeff q k) ((neg a) * (zero <: t)) (zero <: t);
    (* coeff q (k-1) = coeff q (lq-1) = L.index q (lq-1) = L.last q = poly_lc q *)
    last_eq_index q (Prims.op_Subtraction lq 1);
    poly_lc_reveal q;
    assert (coeff q (Prims.op_Subtraction k 1) == poly_lc q);
    (* coeff m k = poly_lc q + zero = poly_lc q *)
    reflexivity (coeff q (Prims.op_Subtraction k 1));
    add_congruence (coeff q (Prims.op_Subtraction k 1)) ((neg a) * coeff q k)
                   (poly_lc q) (zero <: t);
    transitivity (coeff m k)
                 (coeff q (Prims.op_Subtraction k 1) + (neg a) * coeff q k)
                 (poly_lc q + (zero <: t));
    H.x_plus_zero (poly_lc q);
    transitivity (coeff m k) (poly_lc q + (zero <: t)) (poly_lc q);
    (* poly_lc m = coeff m (length m - 1) = coeff m k *)
    last_eq_index m k;
    poly_lc_reveal m;
    assert (poly_lc m == coeff m k);
    transitivity (poly_lc m) (coeff m k) (poly_lc q)

(* ================================================================ *)
(*  General leading coefficient of a product:                        *)
(*    lc (p * q) = lc p * lc q   (p, q both nonzero).                 *)
(*  Convolution at index deg p + deg q: only the i = deg p term       *)
(*  survives (others have one factor past its degree).               *)
(* ================================================================ *)

#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let poly_lc_mul (#t:Type) {| id: integral_domain t |} (p q: polynomial t)
  : Lemma (requires Some? (poly_deg p) /\ Some? (poly_deg q))
          (ensures  poly_lc (poly_mul p q) = poly_lc p * poly_lc q)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let dp = Some?.v (poly_deg p) in
    let dq = Some?.v (poly_deg q) in
    poly_deg_mul p q;                                    (* deg(p*q) = dp + dq *)
    let m = poly_mul p q in
    let k : nat = Prims.op_Addition dp dq in
    (* coeff m k = sum_{i<length p} coeff p i * coeff q (k-i) *)
    let g (i:nat) : t = coeff p i * coeff q (Prims.op_Subtraction k i) in
    coeff_poly_mul_named p q k g (fun (i:nat) -> reflexivity (g i));
    (* length p = dp + 1, so the sum is over [0, dp+1) = [0, dp] U {dp}. *)
    assert (L.length p == Prims.op_Addition dp 1);
    (* split: sum_range g 0 (dp+1) = sum_range g 0 dp + sum_range g dp (dp+1) *)
    sum_range_split g 0 dp (Prims.op_Addition dp 1);
    (* sum_range g dp (dp+1) = g dp  (singleton) *)
    sum_range_singleton g dp;
    (* lower part is all zero: for i<dp, k-i > dq, so coeff q (k-i) = 0 *)
    let hz (i:nat{0 <= i /\ i < dp}) : Lemma (g i = (zero <: t)) =
      (* k - i = dp + dq - i > dq  *)
      coeff_above_degree q (Prims.op_Subtraction k i);   (* coeff q (k-i) = 0 *)
      reflexivity (coeff p i);
      mul_congruence (coeff p i) (coeff q (Prims.op_Subtraction k i)) (coeff p i) (zero <: t);
      H.x_mul_zero (coeff p i);
      transitivity (g i) (coeff p i * (zero <: t)) (zero <: t)
    in
    sum_range_all_zero g 0 dp hz;                        (* sum_range g 0 dp = 0 *)
    (* sum_range g 0 (dp+1) = 0 + g dp = g dp *)
    reflexivity (sum_range g dp (Prims.op_Addition dp 1));
    add_congruence (sum_range g 0 dp) (sum_range g dp (Prims.op_Addition dp 1))
                   (zero <: t) (sum_range g dp (Prims.op_Addition dp 1));
    transitivity (sum_range g 0 (Prims.op_Addition dp 1))
                 (sum_range g 0 dp + sum_range g dp (Prims.op_Addition dp 1))
                 ((zero <: t) + sum_range g dp (Prims.op_Addition dp 1));
    H.zero_plus_x (sum_range g dp (Prims.op_Addition dp 1));
    transitivity (sum_range g 0 (Prims.op_Addition dp 1))
                 ((zero <: t) + sum_range g dp (Prims.op_Addition dp 1))
                 (sum_range g dp (Prims.op_Addition dp 1));
    (* sum_range g dp (dp+1) = g dp = coeff p dp * coeff q dq *)
    transitivity (sum_range g 0 (Prims.op_Addition dp 1))
                 (sum_range g dp (Prims.op_Addition dp 1)) (g dp);
    (* coeff m k = g dp *)
    transitivity (coeff m k) (sum_range g 0 (Prims.op_Addition dp 1)) (g dp);
    (* coeff p dp = lc p, coeff q dq = lc q *)
    last_eq_index p dp; poly_lc_reveal p;
    last_eq_index q dq; poly_lc_reveal q;
    assert (coeff p dp == poly_lc p);
    assert (coeff q (Prims.op_Subtraction k dp) == poly_lc q);   (* k - dp = dq *)
    assert (g dp == poly_lc p * poly_lc q);
    transitivity (coeff m k) (g dp) (poly_lc p * poly_lc q);
    (* poly_lc m = coeff m (length m - 1) = coeff m k *)
    last_eq_index m k; poly_lc_reveal m;
    assert (poly_lc m == coeff m k);
    transitivity (poly_lc m) (coeff m k) (poly_lc p * poly_lc q)
#pop-options

(* ================================================================ *)
(*  Dominant-degree addition:  if deg a = n, lc a <> 0, and          *)
(*  deg b < n (or b = 0), then deg(a+b) = n and lc(a+b) = lc a.      *)
(* ================================================================ *)

#push-options "--z3rlimit 100"
let poly_add_deg_dominant (#t:Type) {| cr: commutative_ring t |} (a b: polynomial t) (n: nat)
  : Lemma (requires Some? (poly_deg a) /\ Some?.v (poly_deg a) == n /\
                    (None? (poly_deg b) \/ Some?.v (poly_deg b) < n))
          (ensures  Some? (poly_deg (poly_add a b)) /\
                    Some?.v (poly_deg (poly_add a b)) == n /\
                    poly_lc (poly_add a b) = poly_lc a)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let s = poly_add a b in
    (* coeff s n = coeff a n + coeff b n = lc a + 0 = lc a *)
    poly_add_coeff a b n;
    last_eq_index a n; poly_lc_reveal a;
    assert (coeff a n == poly_lc a);
    coeff_above_degree b n;                              (* coeff b n = 0 (deg b < n) *)
    reflexivity (coeff a n);
    add_congruence (coeff a n) (coeff b n) (coeff a n) (zero <: t);
    H.x_plus_zero (coeff a n);
    transitivity (coeff s n) (coeff a n + coeff b n) (coeff a n + (zero <: t));
    transitivity (coeff s n) (coeff a n + (zero <: t)) (coeff a n);
    (* coeff s n = coeff a n <> 0  ==>  deg s >= n *)
    leading_coeff_nonzero a;                             (* coeff a n <> 0 *)
    assert (not (coeff a n = (zero <: t)));
    (* coeff s n = coeff a n, so coeff s n <> 0 *)
    assert (not (coeff s n = (zero <: t)));
    Classical.move_requires (coeff_above_degree s) n;    (* contrapositive: deg s >= n *)
    (* deg s <= n via poly_add_degree_bound with k = n+1 *)
    poly_add_degree_bound a b (Prims.op_Addition n 1);
    (* so deg s = Some n; lc s = coeff s n = lc a *)
    last_eq_index s n; poly_lc_reveal s;
    transitivity (poly_lc s) (coeff s n) (poly_lc a)
#pop-options

(* ================================================================ *)
(*  Field fact: distinct points have nonzero difference.             *)
(*    cj <> c0  ==>  neg c0 + cj <> 0.                                *)
(* ================================================================ *)

let sub_nonzero_of_distinct (#t:Type) {| f: field t |} (c0 cj: t)
  : Lemma (requires not (cj = c0))
          (ensures  not ((neg c0 + cj) = (zero <: t)))
  = H.elim_equatable_laws t ();
    if (neg c0 + cj) = (zero <: t) then begin
      H.neg_x_plus_x c0;                          (* neg c0 + c0 = zero *)
      symmetry (neg c0 + c0) (zero <: t);         (* zero = neg c0 + c0 *)
      transitivity (neg c0 + cj) (zero <: t) (neg c0 + c0);   (* neg c0 + cj = neg c0 + c0 *)
      H.group_cancel_left (neg c0) cj c0          (* cj = c0, contradiction *)
    end

(* ================================================================ *)
(*  Roots survive division by a coprime linear factor.               *)
(*    p ~ (x-c0)*q,  p(cj)=0,  cj<>c0   ==>   q(cj)=0.                *)
(* ================================================================ *)

let root_survives_division (#t:Type) {| f: field t |}
  (c0 cj: t) (p q: polynomial t)
  : Lemma (requires poly_eq p (poly_mul (poly_linear #t #f c0) q) /\
                    poly_eval p cj = (zero <: t) /\
                    not (cj = c0))
          (ensures  poly_eval q cj = (zero <: t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let la = poly_linear #t #f c0 in
    (* eval p cj = eval (la*q) cj = eval la cj * eval q cj *)
    eval_congruence p (poly_mul la q) cj;
    eval_mul la q cj;
    eval_linear #t #f c0 cj;                      (* eval la cj = neg c0 + cj *)
    transitivity (poly_eval p cj) (poly_eval (poly_mul la q) cj)
                 (poly_eval la cj * poly_eval q cj);
    (* eval la cj * eval q cj = (neg c0 + cj) * eval q cj *)
    reflexivity (poly_eval q cj);
    mul_congruence (poly_eval la cj) (poly_eval q cj) (neg c0 + cj) (poly_eval q cj);
    symmetry (poly_eval p cj) (poly_eval la cj * poly_eval q cj);
    transitivity ((neg c0 + cj) * poly_eval q cj) (poly_eval la cj * poly_eval q cj)
                 (poly_eval p cj);                (* (neg c0+cj)*eval q cj = eval p cj = 0 *)
    transitivity ((neg c0 + cj) * poly_eval q cj) (poly_eval p cj) (zero <: t);
    (* (neg c0 + cj) <> 0 and product = 0 ==> eval q cj = 0 (domain law) *)
    sub_nonzero_of_distinct #t #f c0 cj;
    let id : integral_domain t = id_of_f t in
    id.id_d.domain_law (neg c0 + cj) (poly_eval q cj)

(* ================================================================ *)
(*  poly_scale respects equality of the scalar (coefficient-wise).   *)
(* ================================================================ *)

let poly_scale_scalar_congr (#t:Type) {| cr: commutative_ring t |}
  (a b: t) (p: polynomial t)
  : Lemma (requires a = b)
          (ensures  poly_eq (poly_scale a p) (poly_scale b p))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let aux (i:nat) : Lemma (coeff (poly_scale a p) i = coeff (poly_scale b p) i) =
      poly_mul_singleton_coeff a p i;            (* coeff (scale a p) i = a * coeff p i *)
      poly_mul_singleton_coeff b p i;            (* coeff (scale b p) i = b * coeff p i *)
      reflexivity (coeff p i);
      mul_congruence a (coeff p i) b (coeff p i); (* a*coeff = b*coeff *)
      symmetry (coeff (poly_scale b p) i) (b * coeff p i);
      transitivity (coeff (poly_scale a p) i) (a * coeff p i) (b * coeff p i);
      transitivity (coeff (poly_scale a p) i) (b * coeff p i) (coeff (poly_scale b p) i)
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (poly_scale a p) (poly_scale b p)

(* ================================================================ *)
(*  Polynomial ring rearrangement:  x * (y * z) ~ y * (x * z).       *)
(* ================================================================ *)

let poly_mul_swap_mid (#t:Type) {| cr: commutative_ring t |} (x y z: polynomial t)
  : Lemma (poly_eq (poly_mul x (poly_mul y z)) (poly_mul y (poly_mul x z)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    assert (mul #(polynomial t) #cr_p.cr_r x (mul #(polynomial t) #cr_p.cr_r y z)
            = mul #(polynomial t) #cr_p.cr_r y (mul #(polynomial t) #cr_p.cr_r x z))
      by canon_ring ()

(* ================================================================ *)
(*  Pairwise distinctness under the FIELD equality `=`.              *)
(*  (no_repeats_p uses propositional ==, but `root_survives_division`*)
(*  needs cj <> c0 under the field's `=`; over an arbitrary field    *)
(*  these differ.  Over fp p, where `=` is ==, the two coincide.)    *)
(* ================================================================ *)

let rec all_distinct (#t:Type) {| cr: commutative_ring t |} (roots: list t)
  : Tot prop (decreases roots)
  = match roots with
    | []      -> True
    | c :: cs -> (forall (d:t). L.memP d cs ==> not (c = d)) /\ all_distinct cs

(* ================================================================ *)
(*  If  p ~ (x-c0)*q  and p has a degree, then q has a degree.        *)
(* ================================================================ *)

let mul_linear_nonzero_quotient (#t:Type) {| f: field t |}
  (c0: t) (p q: polynomial t)
  : Lemma (requires Some? (poly_deg p) /\
                    poly_eq p (poly_mul (poly_linear #t #f c0) q))
          (ensures  Some? (poly_deg q))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws t ();
    let la = poly_linear #t #f c0 in
    degree_well_defined p (poly_mul la q);              (* poly_deg (la*q) = Some n *)
    if None? (poly_deg q) then begin
      degree_none_poly_eq_zero q;                        (* q ~ 0 *)
      reflexivity #(polynomial t) #(cr_p.cr_r.r_add.acg_eq) la;
      poly_mul_congruence la q la (poly_zero #t);         (* la*q ~ la*0 *)
      H.x_mul_zero #(polynomial t) #(cr_p.cr_r) la;       (* la*0 ~ 0 *)
      degree_well_defined (poly_mul la q) (poly_mul la (poly_zero #t));
      degree_well_defined (poly_mul la (poly_zero #t)) (poly_zero #t);
      assert (None? (poly_deg (poly_mul la q)));          (* contradiction with Some *)
      assert False
    end

(* ================================================================ *)
(*  THE DISTINCT-ROOTS FACTORIZATION THEOREM.                        *)
(*                                                                   *)
(*    p over a field, Some?(poly_deg p) = n,  n distinct roots       *)
(*    ==>  p ~ lc(p) * (x-c1) * ... * (x-cn).                        *)
(* ================================================================ *)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 2"
let rec poly_split_distinct_roots (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t)
  : Lemma (requires Some? (poly_deg p) /\
                    L.length roots == Some?.v (poly_deg p) /\
                    all_distinct #t roots /\
                    (forall (c:t). L.memP c roots ==> poly_eval p c = (zero <: t)))
          (ensures  poly_eq p (poly_scale (poly_lc p) (poly_prod_linears #t #f roots)))
          (decreases roots)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cr_p : commutative_ring (polynomial t) = TC.solve in
    let lcp = poly_lc p in
    match roots with
    | [] ->
        (* deg p = 0, so p == [lc p], and poly_scale (lc p) poly_one ~ [lc p]. *)
        degree_zero_is_singleton p;                       (* p == [poly_lc p], lcp <> 0 *)
        (* poly_prod_linears [] = poly_one; poly_scale lcp poly_one = (lcp@0)*poly_one *)
        poly_mul_one (lcp @ poly_zero);                   (* (lcp@0)*poly_one ~ (lcp@0) *)
        (* lcp@0 == [lcp] since lcp <> 0 *)
        assert ((lcp @ poly_zero) == ([lcp] <: polynomial t));
        assert (p == ([lcp] <: polynomial t));
        (* so poly_scale lcp poly_one ~ [lcp] == p *)
        poly_eq_symmetry (poly_scale lcp (poly_prod_linears #t #f roots)) (lcp @ poly_zero);
        reflexivity #(polynomial t) #(cr_p.cr_r.r_add.acg_eq) p
    | c0 :: rest ->
        (* c0 is a root: (x-c0) | p, so p ~ (x-c0)*q. *)
        let _ : squash (L.memP c0 roots) = () in
        assert (poly_eval p c0 = (zero <: t));
        factor_forward #t #f p c0;                        (* divides (x-c0) p *)
        let la = poly_linear #t #f c0 in
        eliminate exists (q: polynomial t). poly_eq p (poly_mul la q)
        returns poly_eq p (poly_scale lcp (poly_prod_linears #t #f roots))
        with _hq.
        begin
          (* p nonempty ==> la*q nonempty ==> q nonempty (Some? poly_deg q). *)
          degree_well_defined p (poly_mul la q);          (* poly_deg p = poly_deg (la*q) *)
          poly_linear_deg #t #f c0;                        (* deg la = Some 1 *)
          mul_linear_nonzero_quotient #t #f c0 p q;        (* Some? (poly_deg q) *)
          poly_deg_mul #(t) #(id_of_f t) la q;             (* deg(la*q) = 1 + deg q *)
          (* length rest = deg q *)
          assert (L.length roots == Prims.op_Addition (L.length rest) 1);
          assert (Some?.v (poly_deg q) == L.length rest);
          (* the remaining roots survive in q *)
          (* all_distinct (c0::rest) = (forall d. memP d rest ==> c0<>d) /\ all_distinct rest *)
          assert ((forall (d:t). L.memP d rest ==> not (c0 = d)) /\ all_distinct #t rest);
          let surv (c:t) : Lemma (requires L.memP c rest)
                                 (ensures poly_eval q c = (zero <: t)) =
            assert (L.memP c roots);                       (* c in rest ==> c in roots *)
            assert (poly_eval p c = (zero <: t));
            assert (not (c0 = c));                          (* from all_distinct head *)
            H.elim_equatable_laws t ();
            symmetry c0 c;                                  (* c0=c <==> c=c0 *)
            assert (not (c = c0));
            root_survives_division #t #f c0 c p q
          in
          let surv_all (c:t) : Lemma (L.memP c rest ==> poly_eval q c = (zero <: t)) =
            Classical.move_requires surv c
          in
          Classical.forall_intro surv_all;
          (* IH on q *)
          poly_split_distinct_roots #t #f q rest;
          let lcq = poly_lc q in
          let prest = poly_prod_linears #t #f rest in
          (* q ~ poly_scale lcq prest = (lcq@0)*prest *)
          assert (poly_eq q (poly_scale lcq prest));
          (* lc p = lc q *)
          poly_lc_mul_linear #t #f c0 q;                   (* lc(la*q) = lc q *)
          poly_eq_lc p (poly_mul la q);                    (* lc p = lc(la*q) *)
          transitivity lcp (poly_lc (poly_mul la q)) lcq;  (* lcp = lcq *)
          (* Build the chain.
             p ~ la*q ~ la*((lcq@0)*prest) ~ la*((lcp@0)*prest) ~ (lcp@0)*(la*prest). *)
          reflexivity #(polynomial t) #(cr_p.cr_r.r_add.acg_eq) la;
          poly_mul_congruence la q la (poly_scale lcq prest);  (* la*q ~ la*(scale lcq prest) *)
          transitivity p (poly_mul la q) (poly_mul la (poly_scale lcq prest));
          (* (lcq@0) ~ (lcp@0) via scalar congr (lcq = lcp) *)
          symmetry lcp lcq;                                 (* lcq = lcp *)
          poly_scale_scalar_congr lcq lcp prest;            (* scale lcq prest ~ scale lcp prest *)
          poly_mul_congruence la (poly_scale lcq prest) la (poly_scale lcp prest);
          transitivity p (poly_mul la (poly_scale lcq prest)) (poly_mul la (poly_scale lcp prest));
          (* la*((lcp@0)*prest) ~ (lcp@0)*(la*prest) *)
          poly_mul_swap_mid la (lcp @ poly_zero) prest;
          (* note poly_scale lcp prest == poly_mul (lcp@0) prest by definition *)
          transitivity p (poly_mul la (poly_scale lcp prest))
                         (poly_mul (lcp @ poly_zero) (poly_mul la prest));
          (* RHS goal: poly_scale lcp (poly_prod_linears (c0::rest))
             = poly_mul (lcp@0) (poly_mul la prest) by definitional unfolding. *)
          assert (poly_prod_linears #t #f roots == poly_mul la prest);
          assert (poly_scale lcp (poly_prod_linears #t #f roots)
                  == poly_mul (lcp @ poly_zero) (poly_mul la prest))
        end
#pop-options
