module Core.Polynomial.Roots

(*
   Roots & splitting over a field (merged module).
   Consolidates the former Core.Polynomial.Root + .Product + .Split:
   factor theorem / poly_linear, products of linear factors (poly_prod),
   and splitting into distinct linear factors.
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Tactics.CanonRing
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Unique
open Core.Polynomial.Irreducible
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree
open Core.Polynomial.Coeff
open Core.FinSum
open Core.Polynomial.Eval

(* ===== from Core.Polynomial.Root ===== *)

(* ================================================================ *)
(*  The linear polynomial  x - a  =  [neg a; one].                   *)
(*  (trimmed because the leading coeff `one` <> zero in a field).    *)
(* ================================================================ *)

let poly_linear (#t:Type) {| f: field t |} (a: t) : polynomial t =
  let _ : squash (not (one #t = zero)) = f.f_one_ne_zero in
  [(- a); one]

let poly_linear_deg (#t:Type) {| f: field t |} (a: t)
  : Lemma (deg (poly_linear a) == 1)
  = let _ : squash (not (one #t = zero)) = f.f_one_ne_zero in
    ()

(* leading coefficient of x - a is one (monic). *)
let poly_linear_lc (#t:Type) {| f: field t |} (a: t)
  : Lemma (poly_lc (poly_linear a) = one)
  = H.elim_equatable_laws t ();
    poly_linear_deg a;
    poly_lc_reveal (poly_linear a)     (* lc = L.last [neg a; one] = one *)

(* ================================================================ *)
(*  Evaluation of small polynomials.                                 *)
(* ================================================================ *)

(* poly_eval [c0] c = c0   (for c0 <> 0 so [c0] is a valid polynomial) *)
let eval_singleton (#t:Type) {| f: field t |} (c0 c: t)
  : Lemma (requires not (c0 = zero))
          (ensures  poly_eval ([c0]) c = c0)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let p : polynomial t = [c0] in
    let g = eval_term p c in
    sum_range_unfold_left g 0 1;                 (* sum01 = g0 + sum11 *)
    sum_range_empty g 1 1;                        (* sum11 = zero *)
    H.x_mul_one c0;                               (* c0 * one = c0 ; g0 == c0 * one *)
    H.x_plus_zero (g 0);
    add_congruence (g 0) (sum_range g 1 1) (g 0) zero

(* poly_eval (x - a) c = c - a   (here written  neg a + c). *)
let eval_linear (#t:Type) {| f: field t |} (a c: t)
  : Lemma (poly_eval (poly_linear a) c = ((- a) + c))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let _ : squash (not (one #t = zero)) = f.f_one_ne_zero in
    let la = poly_linear a in
    let g = eval_term la c in
    sum_range_unfold_left g 0 2;                 (* sum02 = g0 + sum12 *)
    sum_range_unfold_left g 1 2;                 (* sum12 = g1 + sum22 *)
    sum_range_empty g 2 2;                        (* sum22 = zero *)
    (* g 0 == neg a * one == neg a *)
    H.x_mul_one (- a);
    (* g 1 == one * (c * one) == one * c == c *)
    H.x_mul_one c;
    mul_congruence one (c * one) one c;    (* one*(c*one) = one*c *)
    H.one_mul_x c;                                       (* one*c = c *)
    (* sum12 = g1 + zero = g1 = c *)
    H.x_plus_zero (g 1);
    add_congruence (g 1) (sum_range g 2 2) (g 1) zero;
    (* sum02 = g0 + sum12 = neg a + c *)
    add_congruence (g 0) (sum_range g 1 2) (- a) c

(* poly_eval (x - a) a = 0  : a is a root of x - a. *)
let eval_linear_root (#t:Type) {| f: field t |} (a: t)
  : Lemma (poly_eval (poly_linear a) a = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    eval_linear a a;                               (* eval = neg a + a *)
    H.neg_x_plus_x a                               (* neg a + a = zero *)

(* ================================================================ *)
(*  Factor theorem.                                                  *)
(* ================================================================ *)

(* If (x - a) | p, then a is a root of p. *)
let factor_backward (#t:Type) {| f: field t |} (p: polynomial t) (a: t)
  : Lemma (requires divides (poly_linear a) p)
          (ensures  poly_eval p a = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let la = poly_linear a in
    eliminate exists (c: polynomial t). (p = (la * c))
    returns poly_eval p a = zero
    with _.
      begin
        eval_congruence p (la * c) a;             (* eval p a = eval (la*c) a *)
        eval_mul la c a;                                 (* eval (la*c) a = eval la a * eval c a *)
        eval_linear_root a;                              (* eval la a = zero *)
        mul_congruence (poly_eval la a) (poly_eval c a) zero (poly_eval c a);
        H.zero_mul_x (poly_eval c a)                     (* zero * eval c a = zero *)
      end

(* A constant remainder (deg <= 0) vanishing at one point is the zero polynomial. *)
let small_eval_zero_is_zero (#t:Type) {| f: field t |} (rem: polynomial t) (a: t)
  : Lemma (requires (deg rem < 0 \/ deg rem == 0) /\
                    poly_eval rem a = zero)
          (ensures  (rem = (poly_zero #t)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if deg rem < 0 then degree_none_poly_eq_zero rem
    else begin
      degree_zero_is_singleton rem;                     (* rem == [poly_lc rem], lc <> zero *)
      let c0 : t = poly_lc rem in
      eval_singleton c0 a                               (* poly_eval [c0] a = c0 *)
      (* rem == [c0] ==> poly_eval rem a = c0; with eval rem a = zero gives c0 = zero (contra) *)
    end

(* If a is a root of p, then (x - a) | p. *)
let factor_forward (#t:Type) {| f: field t |} (p: polynomial t) (a: t)
  : Lemma (requires poly_eval p a = zero)
          (ensures  divides (poly_linear a) p)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let la = poly_linear a in
    poly_linear_deg a;                                  (* poly_deg la = Some 1 *)
    let q  = poly_div p la in
    let rm = poly_rem p la in
    (* poly_div/poly_rem ensures auto-adjoin: poly_eq p (add (mul la q) rm)
       and deg rm < deg la (= 1) since deg la >= 0 *)
    (* eval at a: eval p a = eval (mul la q) a + eval rm a ; first summand = 0 *)
    eval_congruence p ((la * q) + rm) a;
    eval_add (la * q) rm a;
    eval_mul la q a;
    eval_linear_root a;
    mul_congruence (poly_eval la a) (poly_eval q a) zero (poly_eval q a);
    H.zero_mul_x (poly_eval q a);
    (* eval (add (mul la q) rm) a = zero + eval rm a = eval rm a *)
    add_congruence (poly_eval (la * q) a) (poly_eval rm a) zero (poly_eval rm a);
    H.zero_plus_x (poly_eval rm a);
    (* rm is constant and vanishes => rm ~ 0 => p ~ la*q => (x-a) | p *)
    small_eval_zero_is_zero rm a;                       (* poly_eq rm poly_zero *)
    add_zero (la * q);                           (* (la*q) + 0 ~ (la*q) *)
    add_congruence (la * q) rm (la * q) (poly_zero #t);
    divides_intro la p q

let factor_theorem (#t:Type) {| f: field t |} (p: polynomial t) (a: t)
  : Lemma ((poly_eval p a = zero) <==>
           divides (poly_linear a) p)
  = Classical.move_requires (factor_forward p) a;
    Classical.move_requires (factor_backward p) a

(* ================================================================ *)
(*  Square-free  ==>  simple roots:  q(a)=0 ==> q'(a) <> 0.           *)
(*  If both vanished, (x-a) would divide gcd(q,q'), forcing          *)
(*  deg(gcd) >= 1, contradicting coprime q q' (= square_free q).      *)
(* ================================================================ *)

let squarefree_root_deriv_nonzero (#t:Type) {| f: field t |} (q: polynomial t) (a: t)
  : Lemma (requires square_free q /\ poly_eval q a = zero)
          (ensures  not (poly_eval (poly_deriv q) a = zero))
  = let la = poly_linear a in
    poly_linear_deg a;                                  (* deg la = Some 1 *)
    factor_forward q a;                                  (* la | q *)
    let aux () : Lemma (requires poly_eval (poly_deriv q) a = zero)
                       (ensures False)
      = factor_forward (poly_deriv q) a;                 (* la | q' *)
        gcd_is_maximal q (poly_deriv q) la;              (* la | gcd q q' *)
        coprime_reveal q (poly_deriv q);                 (* deg (gcd q q') = Some 0 *)
        (* la | gcd, deg la = 1, deg gcd = 0  ==>  1 <= 0 *)
        divides_degree_le la (poly_gcd q (poly_deriv q))
    in
    Classical.move_requires aux ()

(* ===== from Core.Polynomial.Product ===== *)

(* ================================================================ *)
(*  Product of a list of polynomials, and the matching scalar fold.  *)
(* ================================================================ *)

let rec poly_prod (#t:Type) {| cr: commutative_ring t |} (ps: list (polynomial t))
  : Tot (polynomial t) (decreases ps)
  = match ps with
    | []        -> poly_one #t
    | p :: rest -> p * (poly_prod rest)

let rec eval_prod (#t:Type) {| cr: commutative_ring t |} (ps: list (polynomial t)) (c: t)
  : Tot t (decreases ps)
  = match ps with
    | []        -> one #t
    | p :: rest -> poly_eval p c * eval_prod rest c

(* poly_eval is a ring homomorphism over the product. *)
let rec eval_poly_prod (#t:Type) {| cr: commutative_ring t |} (ps: list (polynomial t)) (c: t)
  : Lemma (ensures poly_eval (poly_prod ps) c = eval_prod ps c) (decreases ps)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match ps with
    | []        -> eval_one c
    | p :: rest ->
      eval_mul p (poly_prod rest) c;             (* eval (p * prod rest) = eval p * eval (prod rest) *)
      eval_poly_prod rest c;                      (* IH: eval (prod rest) = eval_prod rest *)
      mul_congruence (poly_eval p c) (poly_eval (poly_prod rest) c)
                     (poly_eval p c) (eval_prod rest c)

(* ================================================================ *)
(*  Products of linear factors  (x - a1) * ... * (x - an).           *)
(* ================================================================ *)

let rec poly_prod_linears (#t:Type) {| f: field t |} (roots: list t)
  : Tot (polynomial t) (decreases roots)
  = match roots with
    | []        -> poly_one #t
    | a :: rest -> (poly_linear a) * (poly_prod_linears rest)

let rec eval_prod_sub (#t:Type) {| f: field t |} (roots: list t) (c: t)
  : Tot t (decreases roots)
  = match roots with
    | []        -> one #t
    | a :: rest -> ((- a) + c) * eval_prod_sub rest c

(* poly_eval of a product of linear factors = prod (c - a). *)
let rec eval_poly_prod_linears (#t:Type) {| f: field t |} (roots: list t) (c: t)
  : Lemma (ensures poly_eval (poly_prod_linears roots) c = eval_prod_sub roots c)
          (decreases roots)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match roots with
    | []        -> eval_one c
    | a :: rest ->
      eval_mul (poly_linear a) (poly_prod_linears rest) c;
      eval_linear a c;                            (* eval (x-a) c = neg a + c *)
      eval_poly_prod_linears rest c;              (* IH *)
      mul_congruence (poly_eval (poly_linear a) c)
                     (poly_eval (poly_prod_linears rest) c)
                     ((- a) + c) (eval_prod_sub rest c)

(* Every listed root is genuinely a root of the factored polynomial. *)
let rec prod_linears_vanishes (#t:Type) {| f: field t |} (roots: list t) (a: t)
  : Lemma (requires L.memP a roots)
          (ensures  poly_eval (poly_prod_linears roots) a = zero)
          (decreases roots)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match roots with
    | []        -> ()                             (* memP a [] is False *)
    | b :: rest ->
      eval_mul (poly_linear b) (poly_prod_linears rest) a;
      let lhs = poly_eval (poly_linear b) a in
      let rhs = poly_eval (poly_prod_linears rest) a in
      eliminate (b == a) \/ (L.memP a rest)
      returns poly_eval (poly_prod_linears (b :: rest)) a = zero
      with _h.
        begin                                     (* a is this factor's root: lhs = 0 *)
          eval_linear_root b;                     (* eval (x-b) b = 0 ; b == a *)
          mul_congruence lhs rhs zero rhs;
          H.zero_mul_x rhs                         (* zero * rhs = zero *)
        end
      and _h.
        begin                                     (* a is a root of the rest: rhs = 0 *)
          prod_linears_vanishes rest a;
          mul_congruence lhs rhs lhs zero;
          H.x_mul_zero lhs                         (* lhs * zero = zero *)
        end

(* ===== from Core.Polynomial.Split ===== *)

(* ================================================================ *)
(*  poly_scale a p = [a] * p  (a * p coefficient-wise via mul).      *)
(* ================================================================ *)

let poly_scale (#t:Type) {| cr: commutative_ring t |} (a: t) (p: polynomial t) : polynomial t =
  (a @ poly_zero) * p

(* ================================================================ *)
(*  poly_eq preserves the leading coefficient.                       *)
(* ================================================================ *)

let poly_eq_lc (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma (requires (p = q)) (ensures poly_lc p = poly_lc q)
  = H.elim_equatable_laws t ();
    poly_eq_length p q;
    if L.length p > 0 then begin
      let i = L.length p - 1 in
      poly_eq_means_equal_coeffs p q i;        (* coeff p i = coeff q i *)
      last_eq_index p i;                        (* L.last p = L.index p i *)
      last_eq_index q i;                        (* L.last q = L.index q i *)
      poly_lc_reveal p; poly_lc_reveal q
    end else begin
      poly_lc_reveal p; poly_lc_reveal q
    end

(* ================================================================ *)
(*  coeff of  (x - a) * A  :  coeff A (k-1) + (-a) * coeff A k.       *)
(* ================================================================ *)

let comm_helper (#t:Type) {| cr: commutative_ring t |} (x v w: t)
  : Lemma (x * v + w = w + x * v)
  = assert (x * v + w = w + x * v) by canon_ring ()

let coeff_linear_mul (#t:Type) {| f: field t |} (a: t) (bigA: polynomial t) (k: nat)
  : Lemma (coeff ((poly_linear a) * bigA) k
         = coeff bigA ((k - 1)) + (- a) * coeff bigA k)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let _ : squash (not (one #t = zero)) = f.f_one_ne_zero in
    let pl = poly_linear a in
    assert (L.length pl == 2);
    let g (i:nat) : t = coeff pl i * coeff bigA ((k - i)) in
    coeff_poly_mul_named pl bigA k g H.obvious;
    sum_range_unfold_left g 0 2;
    sum_range_unfold_left g 1 2;
    sum_range_empty g 2 2;
    H.x_plus_zero (g 1);
    add_congruence (g 1) (sum_range g 2 2) (g 1) zero;
    add_congruence (g 0) (sum_range g 1 2) (g 0) (g 1);
    assert (coeff pl 0 == ((- a) <: t));
    mul_congruence (coeff pl 0) (coeff bigA k) (- a) (coeff bigA k);
    assert (g 0 == coeff pl 0 * coeff bigA ((k - 0)));
    assert ((k - 0) == k);
    assert (coeff pl 1 == (one <: t));
    mul_congruence (coeff pl 1) (coeff bigA ((k - 1)))
                   one (coeff bigA ((k - 1)));
    H.one_mul_x (coeff bigA ((k - 1)));
    add_congruence (g 0) (g 1) ((- a) * coeff bigA k) (coeff bigA ((k - 1)));
    comm_helper (- a) (coeff bigA k) (coeff bigA ((k - 1)))

(* ================================================================ *)
(*  Leading coefficient of  (x - a) * q  equals  lc q.               *)
(* ================================================================ *)

let poly_lc_mul_linear (#t:Type) {| f: field t |} (a: t) (q: polynomial t)
  : Lemma (requires deg q >= 0)
          (ensures  poly_lc ((poly_linear a) * q) = poly_lc q)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let _ : squash (not (one #t = zero)) = f.f_one_ne_zero in
    let la = poly_linear a in
    poly_linear_deg a;                                   (* deg la = 1 *)
    deg_mul la q;                                        (* deg (la*q) = 1 + deg q *)
    let m = poly_mul la q in
    (* length q >= 1, length m = length q + 1 *)
    let lq = L.length q in
    assert (lq >= 1);
    assert (L.length m == (lq ++ 1));
    let k = lq in
    (* coeff m k = coeff q (k-1) + (neg a) * coeff q k *)
    coeff_linear_mul a q k;
    (* coeff q k = coeff q lq = zero (past the end) *)
    assert (coeff q k == (zero <: t));
    mul_congruence (- a) (coeff q k) (- a) zero;   (* (neg a)*coeff q k = (neg a)*zero *)
    H.x_mul_zero (- a);                                     (* (neg a)*zero = zero *)
    (* coeff q (k-1) = coeff q (lq-1) = L.index q (lq-1) = L.last q = poly_lc q *)
    last_eq_index q ((lq - 1));
    poly_lc_reveal q;
    assert (coeff q ((k - 1)) == poly_lc q);
    (* coeff m k = poly_lc q + zero = poly_lc q *)
    add_congruence (coeff q ((k - 1))) ((- a) * coeff q k)
                   (poly_lc q) zero;
    H.x_plus_zero (poly_lc q);
    (* poly_lc m = coeff m (length m - 1) = coeff m k *)
    last_eq_index m k;
    poly_lc_reveal m;
    assert (poly_lc m == coeff m k)

(* ================================================================ *)
(*  General leading coefficient of a product:                        *)
(*    lc (p * q) = lc p * lc q   (p, q both nonzero).                 *)
(*  Convolution at index deg p + deg q: only the i = deg p term       *)
(*  survives (others have one factor past its degree).               *)
(* ================================================================ *)

#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let poly_lc_mul (#t:Type) {| id: integral_domain t |} (p q: polynomial t)
  : Lemma (requires deg p >= 0 /\ deg q >= 0)
          (ensures  poly_lc (p * q) = poly_lc p * poly_lc q)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let dp = deg p in
    let dq = deg q in
    deg_mul p q;                                        (* deg(p*q) = dp + dq *)
    let m = poly_mul p q in
    let k : nat = (dp ++ dq) in
    (* coeff m k = sum_{i<length p} coeff p i * coeff q (k-i) *)
    let g (i:nat) : t = coeff p i * coeff q ((k - i)) in
    coeff_poly_mul_named p q k g H.obvious;
    (* length p = dp + 1, so the sum is over [0, dp+1) = [0, dp] U {dp}. *)
    assert (L.length p == (dp ++ 1));
    (* split: sum_range g 0 (dp+1) = sum_range g 0 dp + sum_range g dp (dp+1) *)
    sum_range_split g 0 dp ((dp ++ 1));
    (* sum_range g dp (dp+1) = g dp  (singleton) *)
    sum_range_singleton g dp;
    (* lower part is all zero: for i<dp, k-i > dq, so coeff q (k-i) = 0 *)
    let hz (i:nat{0 <= i /\ i < dp}) : Lemma (g i = zero) =
      (* k - i = dp + dq - i > dq  *)
      coeff_above_degree q ((k - i));   (* coeff q (k-i) = 0 *)
      mul_congruence (coeff p i) (coeff q ((k - i))) (coeff p i) zero;
      H.x_mul_zero (coeff p i)
    in
    sum_range_all_zero g 0 dp hz;                        (* sum_range g 0 dp = 0 *)
    (* sum_range g 0 (dp+1) = 0 + g dp = g dp *)
    add_congruence (sum_range g 0 dp) (sum_range g dp ((dp ++ 1)))
                   zero (sum_range g dp ((dp ++ 1)));
    H.zero_plus_x (sum_range g dp ((dp ++ 1)));
    (* coeff p dp = lc p, coeff q dq = lc q *)
    last_eq_index p dp; poly_lc_reveal p;
    last_eq_index q dq; poly_lc_reveal q;
    assert (coeff p dp == poly_lc p);
    assert (coeff q ((k - dp)) == poly_lc q);   (* k - dp = dq *)
    assert (g dp == poly_lc p * poly_lc q);
    (* poly_lc m = coeff m (length m - 1) = coeff m k *)
    last_eq_index m k; poly_lc_reveal m;
    assert (poly_lc m == coeff m k)
#pop-options

(* ================================================================ *)
(*  Dominant-degree addition:  if deg a = n, lc a <> 0, and          *)
(*  deg b < n (or b = 0), then deg(a+b) = n and lc(a+b) = lc a.      *)
(* ================================================================ *)

#push-options "--z3rlimit 100"
let poly_add_deg_dominant (#t:Type) {| cr: commutative_ring t |} (a b: polynomial t) (n: nat)
  : Lemma (requires deg a == n /\ deg b < n)
          (ensures  deg (a + b) == n /\
                    poly_lc (a + b) = poly_lc a)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let s = a + b in
    (* coeff s n = coeff a n + coeff b n = lc a + 0 = lc a *)
    poly_add_coeff a b n;
    last_eq_index a n; poly_lc_reveal a;
    assert (coeff a n == poly_lc a);
    coeff_above_degree b n;                              (* coeff b n = 0 (deg b < n) *)
    add_congruence (coeff a n) (coeff b n) (coeff a n) zero;
    H.x_plus_zero (coeff a n);
    (* coeff s n = coeff a n <> 0  ==>  deg s >= n *)
    leading_coeff_nonzero a;                             (* coeff a n <> 0 *)
    assert (not (coeff a n = zero));
    (* coeff s n = coeff a n, so coeff s n <> 0 *)
    assert (not (coeff s n = zero));
    Classical.move_requires (coeff_above_degree s) n;    (* contrapositive: deg s >= n *)
    (* deg s <= n via poly_add_degree_bound with k = n+1 *)
    poly_add_degree_bound a b ((n ++ 1));
    (* so deg s = Some n; lc s = coeff s n = lc a *)
    last_eq_index s n; poly_lc_reveal s
#pop-options

(* ================================================================ *)
(*  Field fact: distinct points have nonzero difference.             *)
(*    cj <> c0  ==>  neg c0 + cj <> 0.                                *)
(* ================================================================ *)

let sub_nonzero_of_distinct (#t:Type) {| f: field t |} (c0 cj: t)
  : Lemma (requires not (cj = c0))
          (ensures  not (((- c0) + cj) = zero))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if ((- c0) + cj) = zero then begin
      H.neg_x_plus_x c0;                          (* neg c0 + c0 = zero *)
      H.group_cancel_left (- c0) cj c0          (* cj = c0, contradiction *)
    end

(* ================================================================ *)
(*  Roots survive division by a coprime linear factor.               *)
(*    p ~ (x-c0)*q,  p(cj)=0,  cj<>c0   ==>   q(cj)=0.                *)
(* ================================================================ *)

let root_survives_division (#t:Type) {| f: field t |}
  (c0 cj: t) (p q: polynomial t)
  : Lemma (requires (p = (poly_linear c0 * q)) /\
                    poly_eval p cj = zero /\
                    not (cj = c0))
          (ensures  poly_eval q cj = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let la = poly_linear c0 in
    (* eval p cj = eval (la*q) cj = eval la cj * eval q cj *)
    eval_congruence p (la * q) cj;
    eval_mul la q cj;
    eval_linear c0 cj;                            (* eval la cj = neg c0 + cj *)
    (* eval la cj * eval q cj = (neg c0 + cj) * eval q cj *)
    mul_congruence (poly_eval la cj) (poly_eval q cj) ((- c0) + cj) (poly_eval q cj);
    (* (neg c0 + cj) <> 0 and product = 0 ==> eval q cj = 0 (domain law) *)
    sub_nonzero_of_distinct c0 cj;
    domain_law ((- c0) + cj) (poly_eval q cj)

(* ================================================================ *)
(*  poly_scale respects equality of the scalar (coefficient-wise).   *)
(* ================================================================ *)

let poly_scale_scalar_congr (#t:Type) {| cr: commutative_ring t |}
  (a b: t) (p: polynomial t)
  : Lemma (requires a = b)
          (ensures  (poly_scale a p = poly_scale b p))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let aux (i:nat) : Lemma (coeff (poly_scale a p) i = coeff (poly_scale b p) i) =
      poly_mul_singleton_coeff a p i;            (* coeff (scale a p) i = a * coeff p i *)
      poly_mul_singleton_coeff b p i;            (* coeff (scale b p) i = b * coeff p i *)
      mul_congruence a (coeff p i) b (coeff p i) (* a*coeff = b*coeff *)
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (poly_scale a p) (poly_scale b p)

(* ================================================================ *)
(*  Polynomial ring rearrangement:  x * (y * z) ~ y * (x * z).       *)
(* ================================================================ *)

let poly_mul_swap_mid (#t:Type) {| cr: commutative_ring t |} (x y z: t)
  : Lemma ((x * (y * z)) = (y * (x * z)))
  = assert ((x * (y * z)) = (y * (x * z))) by canon_ring ()

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
  : Lemma (requires deg p >= 0 /\
                    (p = (poly_linear c0 * q)))
          (ensures  deg q >= 0)
  = H.elim_equatable_laws (polynomial t) ();
    let la = poly_linear c0 in
    degree_well_defined p (la * q);              (* deg (la*q) = deg p >= 0 *)
    if deg q < 0 then begin
      degree_none_poly_eq_zero q;                        (* q ~ 0 *)
      mul_congruence la q la (poly_zero #t);              (* la*q ~ la*0 *)
      H.x_mul_zero la;                                    (* la*0 ~ 0 *)
      degree_well_defined (la * q) (la * (poly_zero #t));
      degree_well_defined (la * (poly_zero #t)) (poly_zero #t);
      assert (deg (la * q) < 0);                  (* contradiction with deg >= 0 *)
      assert False
    end

(* ================================================================ *)
(*  THE DISTINCT-ROOTS FACTORIZATION THEOREM.                        *)
(*                                                                   *)
(*    p over a field, Some?(poly_deg p) = n,  n distinct roots       *)
(*    ==>  p ~ lc(p) * (x-c1) * ... * (x-cn).                        *)
(* ================================================================ *)

(* "every listed root is a root of p" as an OPAQUE proposition, with
   elim / proof-as-argument / intro (Q1: hides the `forall` so it never
   lands raw in a consumer's SMT context).  Template: CRT.coprime_with_all. *)
[@@"opaque_to_smt"]
let all_roots_vanish (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  : prop = forall (c:t). L.memP c roots ==> poly_eval p c = zero

let all_roots_vanish_elim (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t{all_roots_vanish p roots})
  : Lemma (forall (c:t). L.memP c roots ==> poly_eval p c = zero)
  = reveal_opaque (`%all_roots_vanish) (all_roots_vanish p roots)

let all_roots_vanish_proof (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  = (c:t{L.memP c roots}) -> Lemma (poly_eval p c = zero)

let all_roots_vanish_intro (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t) (proof: all_roots_vanish_proof p roots)
  : Lemma (all_roots_vanish p roots)
  = reveal_opaque (`%all_roots_vanish) (all_roots_vanish p roots);
    let aux (c:t) : Lemma (L.memP c roots ==> poly_eval p c = zero)
      = if L.memP c roots then proof c else ()
    in
    Classical.forall_intro aux

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let rec poly_split_distinct_roots (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t)
  : Lemma (requires deg p >= 0 /\
                    L.length roots == deg p /\
                    all_distinct roots /\
                    all_roots_vanish p roots)
          (ensures  (p = poly_scale (poly_lc p) (poly_prod_linears roots)))
          (decreases roots)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    all_roots_vanish_elim p roots;                        (* expose the forall to SMT *)
    let lcp = poly_lc p in
    match roots with
    | [] ->
        (* deg p = 0, so p == [lc p], and poly_scale (lc p) poly_one ~ [lc p]. *)
        degree_zero_is_singleton p;                       (* p == [poly_lc p], lcp <> 0 *)
        (* poly_prod_linears [] = poly_one; poly_scale lcp poly_one = (lcp@0)*poly_one *)
        mul_one (lcp @ poly_zero);                        (* (lcp@0)*poly_one ~ (lcp@0) *)
        (* lcp@0 == [lcp] since lcp <> 0 *)
        assert ((lcp @ poly_zero) == ([lcp]));
        assert (p == ([lcp]))
        (* so poly_scale lcp poly_one ~ [lcp] == p; the symmetric direction of
           poly_mul_one is supplied by the equatable laws in scope. *)
    | c0 :: rest ->
        (* c0 is a root: (x-c0) | p, so p ~ (x-c0)*q. *)
        let _ : squash (L.memP c0 roots) = () in
        assert (poly_eval p c0 = zero);
        factor_forward p c0;                              (* divides (x-c0) p *)
        let la = poly_linear c0 in
        eliminate exists (q: polynomial t). (p = (la * q))
        returns (p = poly_scale lcp (poly_prod_linears roots))
        with _hq.
        begin
          (* p nonempty ==> la*q nonempty ==> q nonempty (Some? poly_deg q). *)
          degree_well_defined p (la * q);          (* deg p = deg (la*q) *)
          poly_linear_deg c0;                              (* deg la = 1 *)
          mul_linear_nonzero_quotient c0 p q;              (* deg q >= 0 *)
          deg_mul la q;                  (* deg(la*q) = 1 + deg q *)
          (* length rest = deg q *)
          assert (L.length roots == (L.length rest ++ 1));
          assert (deg q == L.length rest);
          (* the remaining roots survive in q *)
          (* all_distinct (c0::rest) = (forall d. memP d rest ==> c0<>d) /\ all_distinct rest *)
          assert ((forall (d:t). L.memP d rest ==> not (c0 = d)) /\ all_distinct rest);
          let surv (c:t{L.memP c rest}) : Lemma (poly_eval q c = zero) =
            assert (L.memP c roots);                       (* c in rest ==> c in roots *)
            assert (poly_eval p c = zero);
            assert (not (c0 = c));                          (* from all_distinct head *)
            H.elim_equatable_laws t ();
            assert (not (c = c0));
            root_survives_division c0 c p q
          in
          all_roots_vanish_intro q rest surv;
          (* IH on q *)
          poly_split_distinct_roots q rest;
          let lcq = poly_lc q in
          let prest = poly_prod_linears rest in
          (* q ~ poly_scale lcq prest = (lcq@0)*prest *)
          assert (q = poly_scale lcq prest);
          (* lc p = lc q *)
          poly_lc_mul_linear c0 q;                         (* lc(la*q) = lc q *)
          poly_eq_lc p (la * q);                    (* lc p = lc(la*q) *)
          (* Build the chain.
             p ~ la*q ~ la*((lcq@0)*prest) ~ la*((lcp@0)*prest) ~ (lcp@0)*(la*prest). *)
          mul_congruence la q la (poly_scale lcq prest);  (* la*q ~ la*(scale lcq prest) *)
          (* (lcq@0) ~ (lcp@0) via scalar congr (lcq = lcp) *)
          poly_scale_scalar_congr lcq lcp prest;            (* scale lcq prest ~ scale lcp prest *)
          mul_congruence la (poly_scale lcq prest) la (poly_scale lcp prest);
          (* la*((lcp@0)*prest) ~ (lcp@0)*(la*prest) *)
          poly_mul_swap_mid la (lcp @ poly_zero) prest;
          (* note poly_scale lcp prest == poly_mul (lcp@0) prest by definition *)
          (* RHS goal: poly_scale lcp (poly_prod_linears (c0::rest))
             = poly_mul (lcp@0) (poly_mul la prest) by definitional unfolding. *)
          assert (poly_prod_linears roots == (la * prest));
          assert (poly_scale lcp (poly_prod_linears roots)
                  == ((lcp @ poly_zero) * (la * prest)))
        end
#pop-options
