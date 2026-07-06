module Core.Polynomial.Div

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial

module H = Core.Algebra.Helpers

(* ================================================================ *)
(*  Polynomial subtraction                                          *)
(* ================================================================ *)

(* `poly_sub` is an `unfold let` in Core.Polynomial.Div.fsti: subtraction is
   `poly_add p (poly_neg q)` = `p -- q`, fully transparent (no opaque wrapper).
   Downstream code uses the `( -- )` operator directly; the `poly_sub` alias
   survives only in a few explicit-coefficient-ring-instance Berlekamp lambdas. *)

(* `add_sub_cancel` (the group-cancellation identity p ~ (p - s) + s) lives
   below as `add_sub_cancel_pub`; the former private duplicate with the same
   body was removed (W1 dedup). *)

(* ================================================================ *)
(*  Coefficient helpers                                             *)
(* ================================================================ *)

(* ================================================================ *)
(*  Leading coefficient is nonzero                                  *)
(* ================================================================ *)

(* In Class.fst, is_trimmed enforces L.last p <> zero whenever p is
   nonempty. poly_deg p = Some (L.length p - 1) on nonempty p, and
   coeff p (L.length p - 1) = L.last p. *)
let leading_coeff_nonzero #t #cr (p: polynomial t)
  : Lemma (requires deg p >= 0)
          (ensures  not ((coeff p (deg p)) = zero))
  = let d = deg p in
    L.lemma_unsnoc_is_last p;
    assert (L.last p == L.index p (L.length p - 1));
    assert (d = L.length p - 1);
    assert (coeff p d == L.index p d)

(* ================================================================ *)
(*  Coefficient helpers                                             *)
(* ================================================================ *)

let poly_sub_coeff #t #cr (p q: polynomial t) (i: nat)
  : Lemma (coeff (p -- q) i = ((coeff p i) + (- (coeff q i))))
  = poly_add_coeff p (- q) i;
    H.elim_equatable_laws t ();
    poly_neg_coeff q i;
    add_congruence (coeff p i) (coeff (- q) i)
                   (coeff p i) (- (coeff q i));
    transitivity (coeff (p -- q) i)
                 ((coeff p i) + (coeff (- q) i))
                 ((coeff p i) + (- (coeff q i)))

(* (monomial_deg / monomial_coeff / zero_shift_coeff / monomial_mul_coeff
   relocated to Core.Polynomial — basic monomial/coeff facts, no division.) *)

(* ================================================================ *)
(*  Degree bounds                                                   *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let rec poly_neg_degree #t #cr (p: polynomial t)
  : Lemma (ensures deg (- p) == deg p)
          (decreases L.length p)
  = match p with
    | []      -> poly_neg_zero #t #cr
    | a :: p' ->
        poly_neg_reveal a p';
        poly_neg_degree p';
        if a = zero then begin
          H.neg_of_zero a;
          ()
        end
        else begin
          if (- a) = zero then begin
            H.zero_of_neg a
          end
          else ()
        end
#pop-options

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let coeff_zero_above_k_of_add (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) (k: nat) (i: nat)
  : Lemma (requires i >= k /\ deg p < k /\ deg q < k)
          (ensures  coeff (p + q) i = zero)
  = let zp : t = coeff p i in
    let zq : t = coeff q i in
    coeff_above_degree p i;
    coeff_above_degree q i;
    poly_add_coeff p q i;
    let s : t = zp + zq in
    let z : t = zero in
    let zz : t = z + z in
    add_congruence zp zq z z;
    H.x_plus_zero z;
    transitivity s zz z;
    transitivity (coeff (p + q) i) s z
#pop-options

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let poly_add_degree_bound #t #cr (p q: polynomial t) (k: nat)
  : Lemma (requires deg p < k /\ deg q < k)
          (ensures  deg (p + q) < k)
  = if deg (p + q) >= 0 then begin
      let d = deg (p + q) in
      if d < k then ()
      else begin
        coeff_zero_above_k_of_add p q k d;
        leading_coeff_nonzero (p + q)
      end
    end

let poly_sub_degree_bound #t #cr (p q: polynomial t) (k: nat)
  : Lemma (requires deg p < k /\ deg q < k)
          (ensures  deg (p -- q) < k)
  = poly_neg_degree q;
    poly_add_degree_bound p (- q) k
#pop-options

(* ================================================================ *)
(*  Euclidean division: poly_divmod                                 *)
(* ================================================================ *)

module H' = Core.Algebra.Helpers

(* ----- poly_mul nil right via commutativity ----- *)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let poly_mul_nil_right (#t:Type) {| cr: commutative_ring t |}
                       (q: polynomial t)
  : Lemma ((q * ([] <: polynomial t)) = ([] <: polynomial t))
  = H.elim_equatable_laws (polynomial t) ();
    mul_commutativity q ([] <: polynomial t);
    transitivity (q * ([] <: polynomial t))
                 (([] <: polynomial t) * q)
                 ([] <: polynomial t)
#pop-options

(* ----- divmod base case ----- *)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let divmod_base_case (#t:Type) {| cr: commutative_ring t |}
                     (p q: polynomial t)
  : Lemma (p = ((q * ([] <: polynomial t)) + p))
  = H.elim_equatable_laws (polynomial t) ();
    poly_mul_nil_right q;
    add_congruence ((q * ([] <: polynomial t))) p
                   ([] <: polynomial t) p;
    assert (([] <: polynomial t) + p = p);
    symmetry ((q * ([] <: polynomial t)) + p)
             (([] <: polynomial t) + p);
    transitivity p (([] <: polynomial t) + p)
                 ((q * ([] <: polynomial t)) + p)
#pop-options

(* ----- group cancellation: p = (p - s) + s ----- *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let add_sub_cancel_pub (#t:Type) {| cr: commutative_ring t |}
                       (p s: polynomial t)
  : Lemma (p = ((p -- s) + s))
  = H.elim_equatable_laws (polynomial t) ();
    let ns : polynomial t = - s in
    let ps : polynomial t = p + ns in
    let z : polynomial t = [] in
    add_associativity p ns s;
    add_negation s;
    add_congruence p (ns + s) p z;
    add_zero p;
    transitivity (ps + s) (p + (ns + s)) (p + z);
    transitivity (ps + s) (p + z) p;
    symmetry (ps + s) p
#pop-options

(* ----- inductive step using polynomial CR algebra ----- *)

#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let inductive_step (#t:Type) {| cr: commutative_ring t |}
                   (p q mono quot rem: polynomial t)
  : Lemma
      (requires
        ((p -- (mono * q))
                = ((q * quot) + rem)))
      (ensures
        (p
                = ((q * (quot + mono)) + rem)))
  = H.elim_equatable_laws (polynomial t) ();
    let sub_term = mono * q in
    let p2 = p -- sub_term in
    let qm = q * mono in
    let qq = q * quot in
    let lhs_main = (q * (quot + mono)) + rem in

    left_distributivity q quot mono;
    let step1 = qq + qm in
    add_congruence (q * (quot + mono)) rem step1 rem;
    let a1 = step1 + rem in
    add_associativity qq qm rem;
    let a2 = qq + (qm + rem) in
    add_commutativity qm rem;
    add_congruence qq (qm + rem) qq (rem + qm);
    let a3 = qq + (rem + qm) in
    add_associativity qq rem qm;
    symmetry ((qq + rem) + qm) (qq + (rem + qm));
    let a4 = (qq + rem) + qm in
    symmetry p2 (qq + rem);
    add_congruence (qq + rem) qm p2 qm;
    let a5 = p2 + qm in
    mul_commutativity q mono;
    add_congruence p2 qm p2 sub_term;
    let a6 = p2 + sub_term in
    add_sub_cancel_pub p sub_term;
    symmetry p a6;

    transitivity a1 a2 a3;
    transitivity a1 a3 a4;
    transitivity a1 a4 a5;
    transitivity a1 a5 a6;
    transitivity a1 a6 p;
    transitivity lhs_main a1 p;
    symmetry lhs_main p
#pop-options

(* ----- poly_divmod_fuel (computes), using field for leading-coeff inverse ----- *)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let rec poly_divmod_fuel
    (#t:Type) {| f: field t |}
    (p q: polynomial t)
    (fuel: nat)
  : Tot (polynomial t & polynomial t)
        (decreases fuel)
  = if fuel = 0 then ([], p)
    else
      let m = deg p in
      let n = deg q in
      if m < 0 || n < 0 then ([], p)
      else if m < n then ([], p)
      else begin
        leading_coeff_nonzero q;
        let lc_p = coeff p m in
        let lc_q = coeff q n in
        let inv_lc_q = inv lc_q in
        let c = lc_p * inv_lc_q in
        let mono : polynomial t = monomial c (m - n) in
        let sub_term = mono * q in
        let p' = p -- sub_term in
        let (quot, rem) = poly_divmod_fuel p' q (fuel - 1) in
        (quot + mono, rem)
      end
#pop-options

(* ----- poly_divmod_fuel correctness ----- *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let rec poly_divmod_fuel_correct
    (#t:Type) {| f: field t |}
    (p q: polynomial t)
    (fuel: nat)
  : Lemma
      (ensures (let (quot, rem) = poly_divmod_fuel p q fuel in
                (p = ((q * quot) + rem))))
      (decreases fuel)
  = if fuel = 0 then
      divmod_base_case p q
    else
      let m = deg p in
      let n = deg q in
      if m < 0 || n < 0 then divmod_base_case p q
      else if m < n then divmod_base_case p q
      else begin
        leading_coeff_nonzero q;
        let lc_p = coeff p m in
        let lc_q = coeff q n in
        let inv_lc_q = inv lc_q in
        let c = lc_p * inv_lc_q in
        let mono : polynomial t = monomial c (m - n) in
        let sub_term = mono * q in
        let p2 = p -- sub_term in
        poly_divmod_fuel_correct p2 q (fuel - 1);
        let (quot2, rem) = poly_divmod_fuel p2 q (fuel - 1) in
        inductive_step p q mono quot2 rem
      end
#pop-options

(* ================================================================ *)
(*  Degree decrease for the divmod inductive step                   *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"

(* Leading-term cancellation:
   If c * coeff q n = coeff p m and m >= n, then
   coeff (poly_sub p (poly_mul (monomial c (m-n)) q)) m = zero. *)
let cancellation_at (#t:Type) {| cr: commutative_ring t |}
                    (p q: polynomial t) (m n: nat) (c: t)
  : Lemma (requires m >= n /\
                    (c * (coeff q n)) = coeff p m)
          (ensures
             coeff (p -- ((monomial c (m - n)) * q))
                   m
             = zero)
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
    H'.x_plus_neg_x cp_m;
    let lhs0 : t = coeff (p -- prod) m in
    let s1   : t = cp_m + (- prod_m) in
    let s2   : t = cp_m + (- cp_m) in
    transitivity lhs0 s1 s2;
    transitivity lhs0 s2 zero

#pop-options

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"

(* Above the leading position the monomial-product also vanishes. *)
let monomial_mul_coeff_above (#t:Type) {| cr: commutative_ring t |}
                             (c: t) (m n: nat) (q: polynomial t) (i: nat)
  : Lemma (requires deg q = n /\
                    m >= n /\
                    i > m)
          (ensures coeff ((monomial c (m - n)) * q) i
                   = zero)
  = let k = m - n in
    H.elim_equatable_laws t ();
    let j = i - k in
    monomial_mul_coeff c k q j;
    coeff_above_degree q j;
    mul_congruence c (coeff q j) c zero;
    H'.x_mul_zero c;
    let prod_i : t = coeff ((monomial c k) * q) i in
    let cqj    : t = c * (coeff q j) in
    let cz     : t = c * zero in
    transitivity prod_i cqj cz;
    transitivity prod_i cz zero

#pop-options

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"

(* Above the leading position, p - (mono * q) also vanishes. *)
let residue_zero_above (#t:Type) {| cr: commutative_ring t |}
                       (p q: polynomial t) (m n: nat) (c: t) (i: nat)
  : Lemma (requires deg p = m /\ deg q = n /\
                    m >= n /\ i > m)
          (ensures
             coeff (p -- ((monomial c (m - n)) * q))
                   i
             = zero)
  = let k = m - n in
    H.elim_equatable_laws t ();
    let prod : polynomial t = (monomial c k) * q in
    poly_sub_coeff p prod i;
    coeff_above_degree p i;
    monomial_mul_coeff_above c m n q i;
    let cp_i  : t = coeff p i in
    let prod_i: t = coeff prod i in
    neg_congruence prod_i zero;
    H'.neg_zero #t ();
    transitivity (- prod_i) (- zero) zero;
    add_congruence cp_i (- prod_i) zero zero;
    H'.zero_plus_x (zero <: t);
    let lhs_i : t = coeff (p -- prod) i in
    let s1   : t = cp_i + (- prod_i) in
    let s2   : t = zero + zero in
    transitivity lhs_i s1 s2;
    transitivity lhs_i s2 zero

#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"

(* Pointwise "coeff vanishes from index k upward" hypothesis as a per-index
   proof-fn argument (Q1: no raw `forall` in the lemma's requires). *)
let degree_decreases (#t:Type) {| cr: commutative_ring t |}
                     (p: polynomial t) (k: nat)
                     (pf: (i:nat{i >= k}) -> Lemma (coeff p i = zero))
  : Lemma (ensures deg p < k)
  = if deg p >= 0 then begin
      leading_coeff_nonzero p;
      if deg p >= k then pf (deg p)
    end

let divmod_step_degree_decreases (#t:Type) {| cr: commutative_ring t |}
    (p q: polynomial t) (m n: nat) (c: t)
  : Lemma (requires deg p = m /\ deg q = n /\
                    m >= n /\
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

(* ----- field-level: (x * inv y) * y = x ----- *)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"

let lc_cancel_field (#t:Type) {| f: field t |} (x y: t)
  : Lemma (requires is_nonzero y)
          (ensures  (((x * inv y) * y) = x))
  = let inv_y = inv y in
    H.elim_equatable_laws t ();
    inversion_lemma y;
    mul_associativity x inv_y y;
    mul_congruence x (inv_y * y) x (one <: t);
    H'.x_mul_one x;
    let lhs : t = (x * inv_y) * y in
    let m1  : t = x * (inv_y * y) in
    let m2  : t = x * (one <: t) in
    transitivity lhs m1 m2;
    transitivity lhs m2 x

#pop-options

(* ----- fuel-degree correctness ----- *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"

let rec poly_divmod_fuel_degree
    (#t:Type) {| f: field t |}
    (p q: polynomial t)
    (fuel: nat)
  : Lemma (requires deg q >= 0 /\ fuel > deg p)
          (ensures  (let (_, rem) = poly_divmod_fuel p q fuel in
                     deg rem < deg q))
          (decreases fuel)
  = if fuel = 0 then ()
    else
      let m = deg p in
      let n = deg q in
      if m < 0 || n < 0 then ()
      else if m < n then ()
      else begin
        leading_coeff_nonzero q;
        let lc_p = coeff p m in
        let lc_q = coeff q n in
        let inv_lc_q = inv lc_q in
        let c = lc_p * inv_lc_q in
        lc_cancel_field lc_p lc_q;
        divmod_step_degree_decreases p q m n c;
        let mono : polynomial t = monomial c (m - n) in
        let sub_term = mono * q in
        let p' = p -- sub_term in
        poly_divmod_fuel_degree p' q (fuel - 1)
      end

#pop-options

(* ================================================================ *)
(*  Public divmod entry points + euclidean-domain instance          *)
(* ================================================================ *)

let poly_divmod (#t:Type) {| f: field t |} (p q: polynomial t)
  : Pure (polynomial t & polynomial t)
         (requires True)
         (ensures fun (quot, rem) -> p = ((q * quot) + rem) /\
                                     (deg q >= 0 ==> deg rem < deg q))
  = poly_divmod_fuel_correct p q (L.length p ++ 1);
    (if deg q >= 0 then poly_divmod_fuel_degree p q (L.length p ++ 1));
    poly_divmod_fuel p q (L.length p ++ 1)

let poly_div (#t:Type) {| f: field t |} (p q: polynomial t)
  : Pure (polynomial t)
         (requires True)
         (ensures fun quot -> quot == fst (poly_divmod p q) /\
                              p = ((q * quot) + (snd (poly_divmod p q))) /\
                              (deg q >= 0 ==> deg (snd (poly_divmod p q)) < deg q))
  = fst (poly_divmod p q)

let poly_rem (#t:Type) {| f: field t |} (p q: polynomial t)
  : Pure (polynomial t)
         (requires True)
         (ensures fun rem -> rem == snd (poly_divmod p q) /\
                             p = ((q * (fst (poly_divmod p q))) + rem) /\
                             (deg q >= 0 ==> deg rem < deg q))
  = snd (poly_divmod p q)

(* ================================================================ *)
(*  polynomial_euclidean_domain_instance                            *)
(* ================================================================ *)

let _zero_eq_nil (#t:Type) {| cr: commutative_ring t |}
  : Lemma (poly_zero #t == ([] <: polynomial t))
  = ()


(* polynomial_euclidean_domain_instance removed: the wrapper euclidean class is gone;
   the canonical euclidean_domain (polynomial t) is the generic chain in Core.Polynomial.GCD. *)
