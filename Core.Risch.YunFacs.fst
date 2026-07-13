module Core.Risch.YunFacs

(* ================================================================ *)
(*  Bridge: Yun square-free factorization  ->  the `sf_factor` list  *)
(*  consumed by `integrate_rational_multi`.  Makes the multi-factor  *)
(*  rational integrator callable on ANY nonzero polynomial.          *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.GCD
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree
open Core.Polynomial.Irreducible
open Core.Polynomial.Roots
open Core.Polynomial.CRTMulti
open Core.Risch.RationalFull

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ---------------------------------------------------------------- *)
(*  Build sf_factor list from a suffix of `yun q` starting at k.      *)
(*  Position k in `yun q` carries multiplicity (k+1) (powers start    *)
(*  at 1 for position 0).  Constant/unit factors (deg < 1) dropped.   *)
(* ---------------------------------------------------------------- *)
let rec yun_facs_from (#t:Type) {| f: field t |} (q: polynomial t) (k: nat)
  : Pure (list (sf_factor f))
         (requires char_zero f /\ deg q >= 1 /\ k <= L.length (yun q))
         (ensures  fun _ -> True)
         (decreases (L.length (yun q) - k))
  = if k >= L.length (yun q) then []
    else begin
      let a = L.index (yun q) k in
      let rest = yun_facs_from q (k ++ 1) in
      if deg a >= 1 then begin
        yun_factors_square_free q k;
        let bp : sf_factor f = (a, k ++ 1) in
        bp :: rest
      end else rest
    end

let yun_facs (#t:Type) {| f: field t |} (q: polynomial t)
  : Pure (list (sf_factor f))
         (requires char_zero f /\ deg q >= 1)
         (ensures  fun _ -> True)
  = yun_facs_from q 0

(* ---------------------------------------------------------------- *)
(*  Generic list map-index lemma.                                    *)
(* ---------------------------------------------------------------- *)
private let rec index_map_lemma (#a #b:Type) (g: a -> b)
  (l: list a) (i: nat{i < L.length l})
  : Lemma (ensures L.index (L.map g l) i == g (L.index l i)) (decreases l)
  = if i = 0 then () else index_map_lemma g (L.tl l) (i - 1)

(* ---------------------------------------------------------------- *)
(*  (Deliverable 3)  Every modulus has degree >= 1.  Holds for ANY   *)
(*  sf_factor list: each base has deg >= 1 and multiplicity >= 1.     *)
(* ---------------------------------------------------------------- *)
private let moduli_all_deg_ge1 (#t:Type) {| f: field t |} (facs: list (sf_factor f))
  : Lemma (all_deg_ge1 (moduli_of facs))
  = let ms = moduli_of facs in
    map_length_moduli facs;                        (* L.length ms == L.length facs *)
    let pf (k: nat{k < L.length ms}) : Lemma (deg (L.index ms k) >= 1)
      = index_map_lemma (fun (bp: sf_factor f) -> poly_power (fst bp) (snd bp)) facs k;
        let bp = L.index facs k in
        poly_power_degree_exact (fst bp) (snd bp)    (* deg = (snd)*(deg fst) >= 1 *)
    in
    all_deg_ge1_intro ms pf

let yun_facs_deg (#t:Type) {| f: field t |} (q: polynomial t)
  : Lemma (requires char_zero f /\ deg q >= 1)
          (ensures  all_deg_ge1 (moduli_of (yun_facs q)))
  = moduli_all_deg_ge1 (yun_facs q)

(* ---------------------------------------------------------------- *)
(*  Structural invariant of `yun_facs_from q k`: the element at       *)
(*  result-position i has multiplicity  p+1  and base  (yun q)[p]     *)
(*  for a yun-index p with  k <= p < |yun q|.                         *)
(* ---------------------------------------------------------------- *)
private let rec yun_facs_from_recover (#t:Type) {| f: field t |}
  (q: polynomial t) (k: nat) (i: nat)
  : Lemma (requires char_zero f /\ deg q >= 1 /\ k <= L.length (yun q) /\
                    i < L.length (yun_facs_from q k))
          (ensures (let bp = L.index (yun_facs_from q k) i in
                    let p = snd bp - 1 in
                    k <= p /\ p < L.length (yun q) /\ fst bp == L.index (yun q) p))
          (decreases (L.length (yun q) - k))
  = if k >= L.length (yun q) then ()
    else begin
      let a = L.index (yun q) k in
      if deg a >= 1 then begin
        if i = 0 then ()
        else yun_facs_from_recover q (k ++ 1) (i - 1)
      end else
        yun_facs_from_recover q (k ++ 1) i
    end

(* Multiplicities are strictly increasing across result positions.     *)
private let rec yun_facs_from_snd_mono (#t:Type) {| f: field t |}
  (q: polynomial t) (k: nat) (i j: nat)
  : Lemma (requires char_zero f /\ deg q >= 1 /\ k <= L.length (yun q) /\
                    i < j /\ j < L.length (yun_facs_from q k))
          (ensures snd (L.index (yun_facs_from q k) i) <
                   snd (L.index (yun_facs_from q k) j))
          (decreases (L.length (yun q) - k))
  = let a = L.index (yun q) k in
    if deg a >= 1 then begin
      if i = 0 then
        (* head has multiplicity k+1; every tail element has mult >= k+2 *)
        yun_facs_from_recover q (k ++ 1) (j - 1)
      else
        yun_facs_from_snd_mono q (k ++ 1) (i - 1) (j - 1)
    end else
      yun_facs_from_snd_mono q (k ++ 1) i j

(* ---------------------------------------------------------------- *)
(*  (Deliverable 2)  The moduli are pairwise coprime.                *)
(* ---------------------------------------------------------------- *)
let yun_facs_coprime (#t:Type) {| f: field t |} (q: polynomial t)
  : Lemma (requires char_zero f /\ deg q >= 1)
          (ensures  pairwise_coprime (moduli_of (yun_facs q)))
  = let facs = yun_facs q in
    let ms = moduli_of facs in
    map_length_moduli facs;
    let g = (fun (bp: sf_factor f) -> poly_power (fst bp) (snd bp)) in
    let pf (i:nat{i < L.length ms}) (j:nat{j < L.length ms /\ j <> i})
      : Lemma (coprime (L.index ms i) (L.index ms j))
      = index_map_lemma g facs i;
        index_map_lemma g facs j;
        yun_facs_from_recover q 0 i;
        yun_facs_from_recover q 0 j;
        let bi = L.index facs i in
        let bj = L.index facs j in
        let pi = snd bi - 1 in
        let pj = snd bj - 1 in
        poly_power_degree_exact (fst bi) (snd bi);   (* deg ms_i >= 0 *)
        poly_power_degree_exact (fst bj) (snd bj);   (* deg ms_j >= 0 *)
        if i < j then begin
          yun_facs_from_snd_mono q 0 i j;            (* pi < pj *)
          yun_factors_coprime q pi pj;               (* coprime (fst bi)(fst bj) *)
          coprime_powers (fst bi) (fst bj) (snd bi) (snd bj)
        end else begin
          yun_facs_from_snd_mono q 0 j i;            (* pj < pi *)
          yun_factors_coprime q pj pi;               (* coprime (fst bj)(fst bi) *)
          coprime_powers (fst bj) (fst bi) (snd bj) (snd bi);
          coprime_symmetric (L.index ms j) (L.index ms i)
        end
    in
    pairwise_coprime_intro ms pf

(* ================================================================ *)
(*  (Deliverable 4)  Associate lemma.  Building blocks.               *)
(* ================================================================ *)

(* A square-free polynomial is nonzero (deg >= 0). *)
let square_free_deg_ge0 (#t:Type) {| f: field t |} (a: polynomial t)
  : Lemma (requires square_free a) (ensures deg a >= 0)
  = if deg a >= 0 then ()
    else begin
      Core.Polynomial.Unique.degree_none_poly_eq_zero a;   (* a == poly_zero *)
      poly_deriv_zero #t #_;                     (* poly_deriv poly_zero == poly_zero *)
      assert (poly_deriv a == (poly_zero #t));
      poly_gcd_base a (poly_deriv a);            (* poly_gcd a (poly_deriv a) == a *)
      coprime_reveal a (poly_deriv a)            (* square_free a = (deg gcd = 0), but = deg a < 0 *)
    end

(* A degree-zero (nonzero constant) polynomial is a unit: it divides 1. *)
let deg_zero_divides_one (#t:Type) {| f: field t |} (c: polynomial t)
  : Lemma (requires deg c == 0) (ensures divides c (poly_one #t))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    degree_zero_is_singleton c;                  (* c == [poly_lc c], lc <> 0 *)
    let lc = poly_lc c in
    let lcinv_p : polynomial t = [inv lc] in
    let lc_p : polynomial t = [lc] in
    singleton_inv_mul_singleton lc;              (* lcinv_p * lc_p = poly_one *)
    mul_congruence lcinv_p c lcinv_p lc_p;       (* lcinv_p*c = lcinv_p*lc_p *)
    mul_commutativity lcinv_p c;                 (* lcinv_p*c = c*lcinv_p *)
    divides_intro c (poly_one #t) lcinv_p

(* Multiply both sides of a divisibility by a common factor. *)
let divides_mul_both (#t:Type) {| f: field t |} (c x y: polynomial t)
  : Lemma (requires divides x y) (ensures divides (c * x) (c * y))
  = H.elim_equatable_laws (polynomial t) ();
    eliminate exists (w: polynomial t). y = (x * w)
    returns divides (c * x) (c * y)
    with _hyp.
    begin
      mul_congruence c y c (x * w);
      mul_associativity c x w;
      transitivity (c * y) (c * (x * w)) ((c * x) * w);
      divides_intro (c * x) (c * y) w
    end

(* If c is a unit (c | 1), then (c*x) | x. *)
let unit_mul_divides (#t:Type) {| f: field t |} (c x: polynomial t)
  : Lemma (requires divides c (poly_one #t)) (ensures divides (c * x) x)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    eliminate exists (u: polynomial t). (poly_one #t) = (c * u)
    returns divides (c * x) x
    with _hyp.
    begin
      mul_one x;                                 (* x * poly_one = x *)
      mul_congruence x (poly_one #t) x (c * u);  (* x*poly_one = x*(c*u) *)
      mul_associativity x c u;                   (* (x*c)*u = x*(c*u) *)
      mul_commutativity x c;                     (* x*c = c*x *)
      mul_congruence (x * c) u (c * x) u;        (* (x*c)*u = (c*x)*u *)
      divides_intro (c * x) x u
    end

(* ---------------------------------------------------------------- *)
(*  List suffix (drop first k) and its two structural facts, used to  *)
(*  align the index-recursion of `yun_facs_from` with the structural  *)
(*  recursion of `powered_product_aux`.                              *)
(* ---------------------------------------------------------------- *)
let rec ldrop (#a:Type) (k: nat) (l: list a) : Tot (list a) (decreases k)
  = if k = 0 then l else (match l with | [] -> [] | _ :: tl -> ldrop (k - 1) tl)

private let rec ldrop_nil (#a:Type) (k: nat) (l: list a)
  : Lemma (requires k >= L.length l) (ensures ldrop k l == []) (decreases l)
  = match l with
    | []      -> ()
    | _ :: tl -> ldrop_nil (k - 1) tl

#push-options "--fuel 2 --ifuel 1"
private let rec ldrop_cons (#a:Type) (k: nat) (l: list a)
  : Lemma (requires k < L.length l)
          (ensures ldrop k l == (L.index l k) :: (ldrop (k ++ 1) l))
          (decreases k)
  = match l with
    | []      -> ()
    | _ :: tl -> if k = 0 then () else ldrop_cons (k - 1) tl
#pop-options

(* ---------------------------------------------------------------- *)
(*  Core associate induction:  poly_prod of the kept moduli from      *)
(*  position k  is associate to  powered_product_aux (suffix k) (k+1). *)
(* ---------------------------------------------------------------- *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
private let rec yun_facs_assoc_aux (#t:Type) {| f: field t |} (q: polynomial t) (k: nat)
  : Lemma (requires char_zero f /\ deg q >= 1 /\ k <= L.length (yun q))
          (ensures (let a = poly_prod (moduli_of (yun_facs_from q k)) in
                    let p = powered_product_aux (ldrop k (yun q)) (k ++ 1) in
                    divides a p /\ divides p a))
          (decreases (L.length (yun q) - k))
  = H.elim_equatable_laws (polynomial t) ();
    if k >= L.length (yun q) then begin
      ldrop_nil k (yun q);
      divides_refl (poly_one #t)
    end else begin
      let a = L.index (yun q) k in
      let m : pos = k ++ 1 in
      let c = poly_power a m in
      let tail_l = ldrop (k ++ 1) (yun q) in
      let ak1 = poly_prod (moduli_of (yun_facs_from q (k ++ 1))) in
      let fk1 = powered_product_aux tail_l ((k ++ 1) ++ 1) in
      ldrop_cons k (yun q);
      assert (powered_product_aux (ldrop k (yun q)) (k ++ 1) ==
              powered_product_aux (a :: tail_l) (k ++ 1));
      assert (powered_product_aux (a :: tail_l) (k ++ 1) == c * fk1);
      yun_facs_assoc_aux q (k ++ 1);                (* IH: ak1 ~ fk1 *)
      if deg a >= 1 then begin
        assert (poly_prod (moduli_of (yun_facs_from q k)) == c * ak1);
        divides_mul_both c ak1 fk1;
        divides_mul_both c fk1 ak1
      end else begin
        assert (poly_prod (moduli_of (yun_facs_from q k)) == ak1);
        yun_factors_square_free q k;
        square_free_deg_ge0 a;
        assert (deg a == 0);
        poly_power_degree_exact a m;
        assert (deg c == 0);
        deg_zero_divides_one c;
        divides_mul_left ak1 c fk1;                  (* divides ak1 (c*fk1) *)
        unit_mul_divides c fk1;                      (* divides (c*fk1) fk1 *)
        divides_trans (c * fk1) fk1 ak1              (* divides (c*fk1) ak1 *)
      end
    end
#pop-options

(* ---------------------------------------------------------------- *)
(*  (Deliverable 4)  poly_prod (moduli_of (yun_facs q))  is associate  *)
(*  to q  (both directions of divisibility).                         *)
(* ---------------------------------------------------------------- *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let yun_facs_associates (#t:Type) {| f: field t |} (q: polynomial t)
  : Lemma (requires char_zero f /\ deg q >= 1)
          (ensures divides (poly_prod (moduli_of (yun_facs q))) q /\
                   divides q (poly_prod (moduli_of (yun_facs q))))
  = let a = poly_prod (moduli_of (yun_facs q)) in
    let pp = powered_product (yun q) in
    yun_facs_assoc_aux q 0;
    assert (ldrop 0 (yun q) == yun q);
    assert (powered_product_aux (ldrop 0 (yun q)) (0 ++ 1) == pp);
    assert (divides a pp);
    assert (divides pp a);
    Core.Polynomial.Factorization.yun_associates q; (* pp ~ q *)
    divides_trans a pp q;
    divides_trans q pp a
#pop-options

(* ================================================================ *)
(*  (Capstone)  Push-button multi-factor rational integrator.         *)
(*  Runs Yun square-free factorization internally, so it is callable  *)
(*  on ANY denominator q with deg q >= 1 — the caller need not supply  *)
(*  (nor prove well-formed) a square-free factorization.  The two      *)
(*  Yun deliverables discharge `integrate_rational_multi`'s coprime /  *)
(*  degree preconditions on `moduli_of (yun_facs q)`.                  *)
(* ================================================================ *)
(* `yun_facs q` returns a square-free factorization whose modulus product
   `qq = poly_prod (moduli_of (yun_facs q))` is an ASSOCIATE of q (proven by
   yun_facs_associates: q | qq and qq | q), so qq = u*q for a nonzero constant
   unit u.  integrate_rational_multi's soundness gives D(answer) = numerator /
   qq, so to obtain exactly p/q we integrate (u*p)/qq = (u*p)/(u*q) = p/q,
   with u = qq / q (exact, since q | qq). *)
let integrate_rational (#t:Type) {| f: field t |} (p q: polynomial t)
  : Pure (rational_multi_result f)
         (requires char_zero f /\ deg q >= 1)
         (ensures  fun _ -> True)
  = yun_facs_coprime q;                    (* pairwise_coprime (moduli_of (yun_facs q)) *)
    yun_facs_deg q;                        (* all_deg_ge1     (moduli_of (yun_facs q)) *)
    let facs = yun_facs q in
    let qq = poly_prod (moduli_of facs) in
    let u  = fst (Core.Polynomial.Div.poly_divmod qq q) in
    integrate_rational_multi (u * p) qq facs
