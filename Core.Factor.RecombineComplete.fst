module Core.Factor.RecombineComplete

(* ================================================================ *)
(*  M2 · S7 — COMPLETENESS of the recombination divisibility test.   *)
(*                                                                   *)
(*  Converse of `Core.Factor.Recombine.divides_test_sound`: if a     *)
(*  monic `d` (deg >= 1) genuinely divides `bigF` over ℤ, then the   *)
(*  executable `divides_test bigF d` returns `true`. Hence a true    *)
(*  ℤ-factor SURVIVES the recombination filter (`recomb_keep`).      *)
(*                                                                   *)
(*  ROUTE:                                                           *)
(*    1. `ediv_correct`      : bigF = d·quot + rem.                  *)
(*    2. `monic_divmod_fuel_degree` (the KEY missing bound): for a   *)
(*       MONIC divisor the leading term cancels at each step, so the *)
(*       fuelled Euclidean division terminates with deg rem < deg d. *)
(*       (Port of Core.Polynomial.Div.poly_divmod_fuel_degree, with  *)
(*       the field-inverse pivot replaced by the monic lc = one.)    *)
(*    3. From bigF = d·k (divides) and bigF = d·quot + rem we get    *)
(*       d·(k − quot) = rem with deg rem < deg d; over the integral  *)
(*       domain ℤ (deg_mul) k − quot must be zero, hence rem = 0.    *)
(*                                                                   *)
(*  Standalone (NOT on build-all).  NO admit / assume / sorry.       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Int
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Monic
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Factor.Recombine

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  §1 — leading-term cancellation for a MONIC divisor.              *)
(*                                                                   *)
(*  The coefficient-level machinery is a port of the (unexported)    *)
(*  helpers in Core.Polynomial.Div; all four lemmas are ring-generic.*)
(* ================================================================ *)

(* For monic q the leading coefficient is `one`, so scaling by the   *)
(* pivot `coeff p m` leaves it unchanged: (coeff p m)·(coeff q n) =   *)
(* coeff p m.  This is the monic replacement for `lc_cancel_field`.   *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let lc_cancel_monic (#t:Type) {| cr: commutative_ring t |}
                    (p q: polynomial t) (m n: nat)
  : Lemma (requires monic q /\ n = deg q)
          (ensures  ((coeff p m * coeff q n) = coeff p m))
  = H.elim_equatable_laws t ();
    last_eq_index q n;                             (* L.last q == L.index q (len-1) *)
    poly_lc_reveal q;                              (* deg q >= 0 ⇒ poly_lc q == L.last q *)
    (* coeff q n == poly_lc q, and monic q ⇒ poly_lc q = one ⇒ coeff q n = one *)
    let x : t = coeff p m in
    mul_congruence x (coeff q n) x (one <: t);     (* x·(coeff q n) = x·one *)
    H.x_mul_one x;                                 (* x·one = x *)
    transitivity (x * coeff q n) (x * (one <: t)) x
#pop-options

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
(* Leading-term cancellation: (c·coeff q n = coeff p m) and m >= n ⇒
   coeff (p − monomial c (m−n)·q) m = zero. *)
let cancellation_at (#t:Type) {| cr: commutative_ring t |}
                    (p q: polynomial t) (m n: nat) (c: t)
  : Lemma (requires m >= n /\ (c * (coeff q n)) = coeff p m)
          (ensures  coeff (p -- ((monomial c (m - n)) * q)) m = zero)
  = let k = m - n in
    H.elim_equatable_laws t ();
    let mono : polynomial t = monomial c k in
    let prod : polynomial t = mono * q in
    poly_sub_coeff p prod m;
    monomial_mul_coeff c k q n;
    let cp_m  : t = coeff p m in
    let cq_n  : t = coeff q n in
    let prod_m: t = coeff prod m in
    let c_qn  : t = c * cq_n in
    transitivity prod_m c_qn cp_m;
    neg_congruence prod_m cp_m;
    add_congruence cp_m (- prod_m) cp_m (- cp_m);
    H.x_plus_neg_x cp_m;
    let lhs0 : t = coeff (p -- prod) m in
    let s1   : t = cp_m + (- prod_m) in
    let s2   : t = cp_m + (- cp_m) in
    transitivity lhs0 s1 s2;
    transitivity lhs0 s2 zero
#pop-options

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
(* Above the leading position the monomial-product vanishes. *)
let monomial_mul_coeff_above (#t:Type) {| cr: commutative_ring t |}
                             (c: t) (m n: nat) (q: polynomial t) (i: nat)
  : Lemma (requires deg q = n /\ m >= n /\ i > m)
          (ensures coeff ((monomial c (m - n)) * q) i = zero)
  = let k = m - n in
    H.elim_equatable_laws t ();
    let j = i - k in
    monomial_mul_coeff c k q j;
    coeff_above_degree q j;
    mul_congruence c (coeff q j) c zero;
    H.x_mul_zero c;
    let prod_i : t = coeff ((monomial c k) * q) i in
    let cqj    : t = c * (coeff q j) in
    let cz     : t = c * zero in
    transitivity prod_i cqj cz;
    transitivity prod_i cz zero
#pop-options

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
(* Above the leading position, p − (mono·q) also vanishes. *)
let residue_zero_above (#t:Type) {| cr: commutative_ring t |}
                       (p q: polynomial t) (m n: nat) (c: t) (i: nat)
  : Lemma (requires deg p = m /\ deg q = n /\ m >= n /\ i > m)
          (ensures coeff (p -- ((monomial c (m - n)) * q)) i = zero)
  = let k = m - n in
    H.elim_equatable_laws t ();
    let prod : polynomial t = (monomial c k) * q in
    poly_sub_coeff p prod i;
    coeff_above_degree p i;
    monomial_mul_coeff_above c m n q i;
    let cp_i  : t = coeff p i in
    let prod_i: t = coeff prod i in
    neg_congruence prod_i zero;
    H.neg_zero #t ();
    transitivity (- prod_i) (- zero) zero;
    add_congruence cp_i (- prod_i) zero zero;
    H.zero_plus_x (zero <: t);
    let lhs_i : t = coeff (p -- prod) i in
    let s1   : t = cp_i + (- prod_i) in
    let s2   : t = zero + zero in
    transitivity lhs_i s1 s2;
    transitivity lhs_i s2 zero
#pop-options

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
(* One monic division step strictly drops the degree. *)
let divmod_step_degree_decreases (#t:Type) {| cr: commutative_ring t |}
    (p q: polynomial t) (m n: nat) (c: t)
  : Lemma (requires deg p = m /\ deg q = n /\ m >= n /\
                    (c * (coeff q n)) = coeff p m)
          (ensures
             (let mono = monomial c (m - n) in
              let r = p -- (mono * q) in
              deg r < m))
  = let mono : polynomial t = monomial c (m - n) in
    let r : polynomial t = p -- (mono * q) in
    if deg r >= 0 then begin
      let d = deg r in
      if d >= m then begin
        if d = m then cancellation_at p q m n c
        else residue_zero_above p q m n c d;
        leading_coeff_nonzero r
      end
    end
#pop-options

(* ================================================================ *)
(*  §2 — the KEY missing lemma: remainder-degree bound for the       *)
(*        MONIC fuelled Euclidean division.                          *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let rec monic_divmod_fuel_degree (#t:Type) {| cr: commutative_ring t |}
    (p q: polynomial t) (fuel: nat)
  : Lemma (requires monic q /\ fuel > deg p)
          (ensures  (let (_, rem) = monic_divmod_fuel p q fuel in
                     deg rem < deg q))
          (decreases fuel)
  = if fuel = 0 then ()
    else
      let m = deg p in
      let n = deg q in
      if m < 0 || n < 0 then ()
      else if m < n then ()
      else begin
        let c = coeff p m in
        lc_cancel_monic p q m n;
        divmod_step_degree_decreases p q m n c;
        let mono : polynomial t = monomial c (m - n) in
        let sub_term = mono * q in
        let p' = p -- sub_term in
        monic_divmod_fuel_degree p' q (fuel - 1)
      end
#pop-options

(* ================================================================ *)
(*  §3 — small group identity: ((a + b) − a) = b.                    *)
(* ================================================================ *)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let add_sub_cancel_left (#t:Type) {| cr: commutative_ring t |}
                        (a b: polynomial t)
  : Lemma (((a + b) -- a) = b)
  = H.elim_equatable_laws (polynomial t) ();
    let na : polynomial t = - a in
    let lhs : polynomial t = (a + b) + na in
    add_commutativity a b;                              (* a+b = b+a *)
    add_congruence (a + b) na (b + a) na;               (* lhs = (b+a)+na *)
    let s1 : polynomial t = (b + a) + na in
    add_associativity b a na;                           (* (b+a)+na = b+(a+na) *)
    let s2 : polynomial t = b + (a + na) in
    add_negation a;                                     (* a+na = zero *)
    add_congruence b (a + na) b (zero <: polynomial t); (* s2 = b+zero *)
    let s3 : polynomial t = b + (zero <: polynomial t) in
    add_zero b;                                         (* b+zero = b *)
    transitivity lhs s1 s2;
    transitivity lhs s2 s3;
    transitivity lhs s3 b
#pop-options

(* ================================================================ *)
(*  §4 — COMPLETENESS of the test.                                   *)
(* ================================================================ *)

(* The algebra below is kept ABSTRACT over the coefficient ring: with the
   instance a variable, the polynomial ring instance always resolves.  At the
   concrete type `polynomial int` the operator `( * )` (needing `ring
   (polynomial int)`) fails to resolve when spelled out in an under-determined
   position (e.g. an intermediate `transitivity` argument), so the concrete
   theorem only ever applies these lemmas — it never re-derives the identities. *)

(* From  d·k = d·quot + rem  conclude  d·(k − quot) = rem. *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let mul_sub_eq_rem (#t:Type) {| cr: commutative_ring t |}
                   (d k quot rem: polynomial t)
  : Lemma (requires (d * k) = ((d * quot) + rem))
          (ensures  (d * (k -- quot)) = rem)
  = H.elim_equatable_laws (polynomial t) ();
    let kq : polynomial t = k -- quot in
    poly_mul_sub_distrib d k quot;                     (* d·kq = (d·k) -- (d·quot) *)
    add_congruence (d * k) (- (d * quot))
                   ((d * quot) + rem) (- (d * quot));  (* (d·k)--(d·quot) = ((d·quot)+rem)--(d·quot) *)
    add_sub_cancel_left (d * quot) rem;                (* ((d·quot)+rem)--(d·quot) = rem *)
    transitivity (d * kq) ((d * k) -- (d * quot))
                 (((d * quot) + rem) -- (d * quot));
    transitivity (d * kq) (((d * quot) + rem) -- (d * quot)) rem
#pop-options

(* Over an integral domain, if d·kq = rem with deg rem < deg d (deg d >= 0)
   then rem is the zero polynomial (kq must vanish, else deg(d·kq) >= deg d). *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let rem_is_zero (#t:Type) {| id: integral_domain t |}
                (d kq rem: polynomial t)
  : Lemma (requires (d * kq) = rem /\ deg d >= 0 /\ deg rem < deg d)
          (ensures  rem = (poly_zero #t))
  = H.elim_equatable_laws (polynomial t) ();
    (if deg kq >= 0 then begin
       degree_mul d kq;                   (* deg (d·kq) = deg d + deg kq >= deg d *)
       degree_well_defined (d * kq) rem   (* deg (d·kq) = deg rem  — contradicts deg rem < deg d *)
     end);
    degree_none_poly_eq_zero kq;          (* deg kq < 0 ⇒ kq = poly_zero *)
    let znil : polynomial t = [] in
    symmetry (d * kq) rem;                 (* rem = d·kq *)
    poly_mul_congruence d kq d znil;       (* d·kq = d·[] *)
    poly_mul_nil_right d;                   (* d·[] = [] *)
    transitivity rem (d * kq) (d * znil);
    transitivity rem (d * znil) znil
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let divides_test_complete (bigF d: polynomial int)
  : Lemma (requires monic d /\ deg d >= 1 /\ divides d bigF)
          (ensures  divides_test bigF d = true)
  = H.elim_equatable_laws (polynomial int) ();
    ediv_correct bigF d;
    let (quot, rem) = ediv bigF d in
    (* A : bigF = (d*quot) + rem *)
    monic_divmod_fuel_degree bigF d (L.length bigF ++ 1);
    assert (deg rem < deg d);
    eliminate exists (k: polynomial int). eq bigF (d * k)
    returns divides_test bigF d = true
    with _pf.
    begin
      (* Pin the concrete products so `ring (polynomial int)` resolves. *)
      let dk  : polynomial int = d * k in
      let rhs : polynomial int = (d * quot) + rem in
      (* C : (d*k) = (d*quot) + rem *)
      symmetry bigF dk;
      transitivity dk bigF rhs;
      mul_sub_eq_rem d k quot rem;         (* d·(k−quot) = rem *)
      rem_is_zero d (k -- quot) rem        (* rem = poly_zero ⇒ divides_test = true *)
    end
#pop-options
