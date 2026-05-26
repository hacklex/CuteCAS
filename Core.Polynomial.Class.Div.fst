module Core.Polynomial.Class.Div

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial.Class

module H = Core.Algebra.Helpers

(* ================================================================ *)
(*  Monomial                                                        *)
(* ================================================================ *)

(* Inner recursive helper returning a raw list with explicit non-emptiness
   and "last = c" invariants when c <> zero. *)
let rec monomial_nonzero_aux #t {| cr: commutative_ring t |}
                             (c: t{not (c = zero)}) (n: nat)
  : Tot (l: list t {Cons? l /\ L.last l == c}) (decreases n)
  = if n = 0 then [c]
    else (zero <: t) :: monomial_nonzero_aux c (Prims.op_Subtraction n 1)

let monomial #t #cr (c: t) (n: nat) : polynomial t
  = if c = zero then [] else monomial_nonzero_aux c n

let monomial_zero_n_reveal #t #cr c
  = ()

let monomial_succ_n_reveal #t #cr c n
  = ()

(* ================================================================ *)
(*  Polynomial subtraction                                          *)
(* ================================================================ *)

let poly_sub #t #cr p q = poly_add p (poly_neg q)

let poly_sub_reveal #t #cr p q = ()

(* p ~ (p - s) + s.  Group cancellation. Private; users should derive this
   directly from the commutative_ring axioms once a polynomial CR instance
   is in scope. *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
private let add_sub_cancel (#t:Type) {| cr: commutative_ring t |} (p s: polynomial t)
  : Lemma (poly_eq p (poly_add (poly_sub p s) s))
  = let ns = poly_neg s in
    let ps : polynomial t = poly_add p ns in
    let z : polynomial t = [] in
    poly_add_associativity p ns s;
    poly_add_negation s;
    poly_eq_reflexivity p;
    poly_add_congruence p (poly_add ns s) p z;
    poly_add_zero p;
    poly_eq_transitivity (poly_add ps s) (poly_add p (poly_add ns s))
                         (poly_add p z);
    poly_eq_transitivity (poly_add ps s) (poly_add p z) p;
    poly_eq_symmetry (poly_add ps s) p
#pop-options

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
  : Lemma (requires Some? (poly_deg p))
          (ensures  not ((coeff p (Some?.v (poly_deg p))) = (zero <: t)))
  = let d = Some?.v (poly_deg p) in
    L.lemma_unsnoc_is_last p;
    assert (L.last p == L.index p (L.length p - 1));
    assert (d = L.length p - 1);
    assert (coeff p d == L.index p d)

(* ================================================================ *)
(*  Coefficient helpers                                             *)
(* ================================================================ *)

(* Any index strictly above the polynomial degree yields a zero coefficient. *)
let coeff_above_degree #t #cr (p: polynomial t) (i: nat)
  : Lemma (requires None? (poly_deg p) \/ Some?.v (poly_deg p) < i)
          (ensures  coeff p i = (zero <: t))
  = reflexivity (zero <: t)

let poly_sub_coeff #t #cr (p q: polynomial t) (i: nat)
  : Lemma (coeff (poly_sub p q) i = ((coeff p i) + (- (coeff q i))))
  = poly_add_coeff p (poly_neg q) i;
    poly_neg_coeff q i;
    reflexivity (coeff p i);
    add_congruence (coeff p i) (coeff (poly_neg q) i)
                   (coeff p i) (- (coeff q i));
    transitivity (coeff (poly_sub p q) i)
                 ((coeff p i) + (coeff (poly_neg q) i))
                 ((coeff p i) + (- (coeff q i)))

(* ================================================================ *)
(*  Monomial coefficient + degree                                   *)
(* ================================================================ *)

let rec monomial_deg #t #cr (c: t) (n: nat)
  : Lemma (ensures (if c = (zero <: t)
                    then poly_deg #t #cr (monomial c n) == None
                    else poly_deg #t #cr (monomial c n) == Some n))
          (decreases n)
  = if n = 0 then ()
    else monomial_deg #t #cr c (Prims.op_Subtraction n 1)

#push-options "--z3rlimit 80 --fuel 3 --ifuel 3"
let rec monomial_coeff #t #cr (c: t) (n: nat) (i: nat)
  : Lemma (ensures (if i = n then coeff #t #cr (monomial c n) i = c
                    else coeff #t #cr (monomial c n) i = (zero <: t)))
          (decreases n)
  = if n = 0 then begin
      if i = 0 then begin
        if c = (zero <: t) then begin
          (* monomial c 0 = []; coeff [] 0 = zero; want coeff = c.
             From c = zero we have eq c zero; want eq (coeff = zero) c.
             coeff p 0 = zero by refined return type; symmetry of eq. *)
          symmetry c (zero <: t);
          reflexivity (zero <: t);
          transitivity (zero <: t) (zero <: t) c
        end
        else reflexivity c
      end
      else begin
        (* i > 0, n = 0; whether c = zero or not, the monomial has length <= 1,
           so coeff at i >= 1 is zero. *)
        reflexivity (zero <: t)
      end
    end
    else begin
      let n' = Prims.op_Subtraction n 1 in
      if i = 0 then
        (* monomial c n = zero :: monomial c n'; coeff at 0 is zero. *)
        reflexivity (zero <: t)
      else begin
        let i' = Prims.op_Subtraction i 1 in
        monomial_coeff #t #cr c n' i'
      end
    end
#pop-options

(* ================================================================ *)
(*  Coefficient identity for poly_mul of a monomial                 *)
(* ================================================================ *)

(* coeff ((zero :: p)-like) (i+1) = coeff p i, including the smart-cons
   collapse case (zero @ [] == []). *)
let zero_shift_coeff (#t:Type) {| cr: commutative_ring t |} (p: polynomial t) (i: nat)
  : Lemma (coeff ((zero <: t) @ p) (Prims.op_Addition i 1) = coeff p i)
  = match p with
    | []     -> reflexivity (zero <: t)
    | _ :: _ -> reflexivity (coeff p i)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let rec monomial_mul_coeff (#t:Type) {| cr: commutative_ring t |} (c: t) (k: nat) (q: polynomial t) (j: nat)
  : Lemma (ensures coeff (poly_mul (monomial c k) q) (Prims.op_Addition k j)
                   = c * (coeff q j))
          (decreases k)
  = if c = (zero <: t) then begin
      (* monomial c k = []; poly_mul [] q = []; coeff = zero = c * coeff q j *)
      reflexivity (coeff q j);
      mul_congruence c (coeff q j) (zero <: t) (coeff q j);
      H.zero_mul_x (coeff q j);
      transitivity (c * coeff q j) ((zero <: t) * coeff q j) (zero <: t);
      symmetry (c * coeff q j) (zero <: t);
      reflexivity (zero <: t)
    end
    else if k = 0 then begin
      (* monomial c 0 = c @ poly_zero; use the singleton coeff lemma *)
      poly_mul_singleton_coeff c q j
    end
    else begin
      let k' = Prims.op_Subtraction k 1 in
      (* monomial c k = zero @ monomial c k'  (since monomial c k' nonempty) *)
      let m  : polynomial t = monomial c k  in
      let m' : polynomial t = monomial c k' in
      assert (m == ((zero <: t) @ m'));
      (* poly_mul_reveal applied to a=zero, p=m', q *)
      let s1 : polynomial t = poly_mul ((zero <: t) @ poly_zero) q in
      let s2 : polynomial t = (zero <: t) @ (poly_mul m' q)        in
      let rhs : polynomial t = poly_add s1 s2 in
      poly_mul_reveal (zero <: t) m' q;
      poly_eq_means_equal_coeffs (poly_mul m q) rhs (Prims.op_Addition k j);
      poly_add_coeff s1 s2 (Prims.op_Addition k j);
      (* coeff s1 _ = zero * coeff q _ = zero *)
      poly_mul_singleton_coeff (zero <: t) q (Prims.op_Addition k j);
      H.zero_mul_x (coeff q (Prims.op_Addition k j));
      transitivity (coeff s1 (Prims.op_Addition k j))
                   ((zero <: t) * coeff q (Prims.op_Addition k j))
                   (zero <: t);
      (* coeff s2 (k+j) = coeff (poly_mul m' q) (k'+j) by zero_shift_coeff *)
      zero_shift_coeff (poly_mul m' q) (Prims.op_Addition k' j);
      monomial_mul_coeff c k' q j;
      (* assemble: coeff (poly_mul m q) (k+j)
         = coeff s1 (k+j) + coeff s2 (k+j)
         = zero + coeff (poly_mul m' q) (k'+j)
         = zero + c * coeff q j
         = c * coeff q j *)
      let r1 : t = coeff s1 (Prims.op_Addition k j) in
      let r2 : t = coeff s2 (Prims.op_Addition k j) in
      let r2' : t = coeff (poly_mul m' q) (Prims.op_Addition k' j) in
      reflexivity r2;
      add_congruence r1 r2 (zero <: t) r2';
      H.zero_plus_x r2';
      transitivity (r1 + r2) ((zero <: t) + r2') r2';
      transitivity (coeff (poly_mul m q) (Prims.op_Addition k j))
                   (coeff rhs (Prims.op_Addition k j))
                   (r1 + r2);
      transitivity (coeff (poly_mul m q) (Prims.op_Addition k j))
                   (r1 + r2) r2';
      transitivity (coeff (poly_mul m q) (Prims.op_Addition k j))
                   r2' (c * coeff q j)
    end
#pop-options
(* ================================================================ *)
(*  Degree bounds                                                   *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let rec poly_neg_degree #t #cr (p: polynomial t)
  : Lemma (ensures poly_deg (poly_neg p) == poly_deg p)
          (decreases L.length p)
  = match p with
    | []      -> poly_neg_zero #t #cr
    | a :: p' ->
        poly_neg_reveal a p';
        poly_neg_degree p';
        if a = (zero <: t) then begin
          H.neg_of_zero a;
          ()
        end
        else begin
          if (cr.cr_r.r_add.neg a) = (zero <: t) then begin
            H.zero_of_neg a
          end
          else ()
        end
#pop-options

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let coeff_zero_above_k_of_add #t #cr (p q: polynomial t) (k: nat) (i: nat)
  : Lemma (requires i >= k /\
                    (None? (poly_deg p) \/ Some?.v (poly_deg p) < k) /\
                    (None? (poly_deg q) \/ Some?.v (poly_deg q) < k))
          (ensures  coeff (poly_add p q) i = (zero <: t))
  = let zp : t = coeff p i in
    let zq : t = coeff q i in
    coeff_above_degree p i;
    coeff_above_degree q i;
    poly_add_coeff p q i;
    let s : t = cr.cr_r.r_add.add zp zq in
    let z : t = (zero <: t) in
    let zz : t = cr.cr_r.r_add.add z z in
    cr.cr_r.r_add.add_congruence zp zq z z;
    H.x_plus_zero z;
    transitivity s zz z;
    transitivity (coeff (poly_add p q) i) s z
#pop-options

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let poly_add_degree_bound #t #cr (p q: polynomial t) (k: nat)
  : Lemma (requires (None? (poly_deg p) \/ Some?.v (poly_deg p) < k) /\
                    (None? (poly_deg q) \/ Some?.v (poly_deg q) < k))
          (ensures  None? (poly_deg (poly_add p q)) \/
                    Some?.v (poly_deg (poly_add p q)) < k)
  = match poly_deg (poly_add p q) with
    | None   -> ()
    | Some d ->
        if d < k then ()
        else begin
          coeff_zero_above_k_of_add p q k d;
          leading_coeff_nonzero (poly_add p q);
          ()
        end

let poly_sub_degree_bound #t #cr (p q: polynomial t) (k: nat)
  : Lemma (requires (None? (poly_deg p) \/ Some?.v (poly_deg p) < k) /\
                    (None? (poly_deg q) \/ Some?.v (poly_deg q) < k))
          (ensures  None? (poly_deg (poly_sub p q)) \/
                    Some?.v (poly_deg (poly_sub p q)) < k)
  = poly_neg_degree q;
    poly_add_degree_bound p (poly_neg q) k
#pop-options

(* ================================================================ *)
(*  Euclidean division: poly_divmod                                 *)
(* ================================================================ *)

module H' = Core.Algebra.Helpers

(* ----- poly_mul nil right via commutativity ----- *)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let poly_mul_nil_right (#t:Type) {| cr: commutative_ring t |}
                       (q: polynomial t)
  : Lemma (poly_eq (poly_mul q ([] <: polynomial t)) ([] <: polynomial t))
  = poly_mul_commutativity q ([] <: polynomial t);
    poly_eq_reflexivity ([] <: polynomial t);
    poly_eq_transitivity (poly_mul q ([] <: polynomial t))
                         (poly_mul ([] <: polynomial t) q)
                         ([] <: polynomial t)
#pop-options

(* ----- divmod base case ----- *)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let divmod_base_case (#t:Type) {| cr: commutative_ring t |}
                     (p q: polynomial t)
  : Lemma (poly_eq p (poly_add (poly_mul q ([] <: polynomial t)) p))
  = poly_mul_nil_right q;
    poly_eq_reflexivity p;
    poly_add_congruence (poly_mul q ([] <: polynomial t)) p
                        ([] <: polynomial t) p;
    let pcrc : polynomial_commutative_ring t = polynomial_commutative_ring_instance in
    let cr_p : commutative_ring (polynomial t) = TC.solve in
    assert (poly_eq (poly_add ([] <: polynomial t) p) p);
    poly_eq_symmetry (poly_add (poly_mul q ([] <: polynomial t)) p)
                     (poly_add ([] <: polynomial t) p);
    poly_eq_transitivity p (poly_add ([] <: polynomial t) p)
                         (poly_add (poly_mul q ([] <: polynomial t)) p)
#pop-options

(* ----- group cancellation: p = (p - s) + s ----- *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let add_sub_cancel_pub (#t:Type) {| cr: commutative_ring t |}
                       (p s: polynomial t)
  : Lemma (poly_eq p (poly_add (poly_sub p s) s))
  = let ns = poly_neg s in
    let ps : polynomial t = poly_add p ns in
    let z : polynomial t = [] in
    poly_add_associativity p ns s;
    poly_add_negation s;
    poly_eq_reflexivity p;
    poly_add_congruence p (poly_add ns s) p z;
    poly_add_zero p;
    poly_eq_transitivity (poly_add ps s) (poly_add p (poly_add ns s))
                         (poly_add p z);
    poly_eq_transitivity (poly_add ps s) (poly_add p z) p;
    poly_eq_symmetry (poly_add ps s) p
#pop-options

(* ----- inductive step using polynomial CR algebra ----- *)

#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let inductive_step (#t:Type) {| cr: commutative_ring t |}
                   (p q mono quot rem: polynomial t)
  : Lemma
      (requires
        poly_eq (poly_sub p (poly_mul mono q))
                (poly_add (poly_mul q quot) rem))
      (ensures
        poly_eq p
                (poly_add (poly_mul q (poly_add quot mono)) rem))
  = let sub_term = poly_mul mono q in
    let p2 = poly_sub p sub_term in
    let qm = poly_mul q mono in
    let qq = poly_mul q quot in
    let lhs_main = poly_add (poly_mul q (poly_add quot mono)) rem in

    poly_left_distributivity q quot mono;
    let step1 = poly_add qq qm in
    poly_eq_reflexivity rem;
    poly_add_congruence (poly_mul q (poly_add quot mono)) rem step1 rem;
    let a1 = poly_add step1 rem in
    poly_add_associativity qq qm rem;
    let a2 = poly_add qq (poly_add qm rem) in
    poly_add_commutativity qm rem;
    poly_eq_reflexivity qq;
    poly_add_congruence qq (poly_add qm rem) qq (poly_add rem qm);
    let a3 = poly_add qq (poly_add rem qm) in
    poly_add_associativity qq rem qm;
    poly_eq_symmetry (poly_add (poly_add qq rem) qm)
                     (poly_add qq (poly_add rem qm));
    let a4 = poly_add (poly_add qq rem) qm in
    poly_eq_symmetry p2 (poly_add qq rem);
    poly_eq_reflexivity qm;
    poly_add_congruence (poly_add qq rem) qm p2 qm;
    let a5 = poly_add p2 qm in
    poly_mul_commutativity q mono;
    poly_eq_reflexivity p2;
    poly_add_congruence p2 qm p2 sub_term;
    let a6 = poly_add p2 sub_term in
    add_sub_cancel_pub p sub_term;
    poly_eq_symmetry p a6;

    poly_eq_transitivity a1 a2 a3;
    poly_eq_transitivity a1 a3 a4;
    poly_eq_transitivity a1 a4 a5;
    poly_eq_transitivity a1 a5 a6;
    poly_eq_transitivity a1 a6 p;
    poly_eq_transitivity lhs_main a1 p;
    poly_eq_symmetry lhs_main p
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
      match poly_deg p, poly_deg q with
      | None, _ | _, None -> ([], p)
      | Some m, Some n ->
          if m < n then ([], p)
          else begin
            leading_coeff_nonzero q;
            let lc_p = coeff p m in
            let lc_q = coeff q n in
            let inv_lc_q = f.f_sf.sf_mig.inv lc_q in
            let c = lc_p * inv_lc_q in
            let mono : polynomial t = monomial c (Prims.op_Subtraction m n) in
            let sub_term = poly_mul mono q in
            let p' = poly_sub p sub_term in
            let (quot, rem) = poly_divmod_fuel #t #f p' q (Prims.op_Subtraction fuel 1) in
            (poly_add quot mono, rem)
          end
#pop-options

(* ----- poly_divmod_fuel correctness ----- *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let rec poly_divmod_fuel_correct
    (#t:Type) {| f: field t |}
    (p q: polynomial t)
    (fuel: nat)
  : Lemma
      (ensures (let (quot, rem) = poly_divmod_fuel #t #f p q fuel in
                poly_eq p (poly_add (poly_mul q quot) rem)))
      (decreases fuel)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    if fuel = 0 then
      divmod_base_case #t #cr p q
    else
      match poly_deg p, poly_deg q with
      | None, _ -> divmod_base_case #t #cr p q
      | _, None -> divmod_base_case #t #cr p q
      | Some m, Some n ->
          if m < n then divmod_base_case #t #cr p q
          else begin
            leading_coeff_nonzero q;
            let lc_p = coeff p m in
            let lc_q = coeff q n in
            let inv_lc_q = f.f_sf.sf_mig.inv lc_q in
            let c = lc_p * inv_lc_q in
            let mono : polynomial t = monomial c (Prims.op_Subtraction m n) in
            let sub_term = poly_mul mono q in
            let p2 = poly_sub p sub_term in
            poly_divmod_fuel_correct #t #f p2 q (Prims.op_Subtraction fuel 1);
            let (quot2, rem) = poly_divmod_fuel #t #f p2 q (Prims.op_Subtraction fuel 1) in
            inductive_step #t #cr p q mono quot2 rem
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
                    (cr.cr_r.mul c (coeff q n)) = coeff p m)
          (ensures
             coeff (poly_sub p
                     (poly_mul (monomial c (Prims.op_Subtraction m n)) q))
                   m
             = (zero <: t))
  = let k = Prims.op_Subtraction m n in
    let mono : polynomial t = monomial c k in
    let prod : polynomial t = poly_mul mono q in
    poly_sub_coeff p prod m;
    monomial_mul_coeff c k q n;
    let cp_m  : t = coeff p m in
    let cq_n  : t = coeff q n in
    let prod_m: t = coeff prod m in
    let c_qn  : t = cr.cr_r.mul c cq_n in
    transitivity prod_m c_qn cp_m;
    let neg_fn = cr.cr_r.r_add.neg in
    cr.cr_r.r_add.neg_congruence prod_m cp_m;
    reflexivity cp_m;
    cr.cr_r.r_add.add_congruence cp_m (neg_fn prod_m) cp_m (neg_fn cp_m);
    H'.x_plus_neg_x cp_m;
    let lhs0 : t = coeff (poly_sub p prod) m in
    let s1   : t = cr.cr_r.r_add.add cp_m (neg_fn prod_m) in
    let s2   : t = cr.cr_r.r_add.add cp_m (neg_fn cp_m) in
    transitivity lhs0 s1 s2;
    transitivity lhs0 s2 (zero <: t)

#pop-options

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"

(* Above the leading position the monomial-product also vanishes. *)
let monomial_mul_coeff_above (#t:Type) {| cr: commutative_ring t |}
                             (c: t) (m n: nat) (q: polynomial t) (i: nat)
  : Lemma (requires Some? (poly_deg q) /\
                    Some?.v (poly_deg q) = n /\
                    m >= n /\
                    i > m)
          (ensures coeff (poly_mul (monomial c (Prims.op_Subtraction m n)) q) i
                   = (zero <: t))
  = let k = Prims.op_Subtraction m n in
    let j = Prims.op_Subtraction i k in
    monomial_mul_coeff c k q j;
    coeff_above_degree q j;
    reflexivity c;
    cr.cr_r.mul_congruence c (coeff q j) c (zero <: t);
    H'.x_mul_zero c;
    let prod_i : t = coeff (poly_mul (monomial #t #cr c k) q) i in
    let cqj    : t = cr.cr_r.mul c (coeff q j) in
    let cz     : t = cr.cr_r.mul c (zero <: t) in
    transitivity prod_i cqj cz;
    transitivity prod_i cz (zero <: t)

#pop-options

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"

(* Above the leading position, p - (mono * q) also vanishes. *)
let residue_zero_above (#t:Type) {| cr: commutative_ring t |}
                       (p q: polynomial t) (m n: nat) (c: t) (i: nat)
  : Lemma (requires Some? (poly_deg p) /\ Some?.v (poly_deg p) = m /\
                    Some? (poly_deg q) /\ Some?.v (poly_deg q) = n /\
                    m >= n /\ i > m)
          (ensures
             coeff (poly_sub p
                     (poly_mul (monomial c (Prims.op_Subtraction m n)) q))
                   i
             = (zero <: t))
  = let k = Prims.op_Subtraction m n in
    let prod : polynomial t = poly_mul (monomial c k) q in
    poly_sub_coeff p prod i;
    coeff_above_degree p i;
    monomial_mul_coeff_above c m n q i;
    let cp_i  : t = coeff p i in
    let prod_i: t = coeff prod i in
    let neg_fn = cr.cr_r.r_add.neg in
    cr.cr_r.r_add.neg_congruence prod_i (zero <: t);
    H'.neg_zero #t ();
    symmetry (zero <: t) (neg_fn (zero <: t));
    transitivity (neg_fn prod_i) (neg_fn (zero <: t)) (zero <: t);
    cr.cr_r.r_add.add_congruence cp_i (neg_fn prod_i)
                                  (zero <: t) (zero <: t);
    H'.zero_plus_x (zero <: t);
    let lhs_i : t = coeff (poly_sub p prod) i in
    let s1   : t = cr.cr_r.r_add.add cp_i (neg_fn prod_i) in
    let s2   : t = cr.cr_r.r_add.add (zero <: t) (zero <: t) in
    transitivity lhs_i s1 s2;
    transitivity lhs_i s2 (zero <: t)

#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"

let degree_decreases (#t:Type) {| cr: commutative_ring t |}
                     (p: polynomial t) (k: nat)
  : Lemma (requires (forall (i:nat). i >= k ==> coeff p i = (zero <: t)))
          (ensures  (None? (poly_deg p) \/ Some?.v (poly_deg p) < k))
  = match poly_deg p with
    | None   -> ()
    | Some d ->
        leading_coeff_nonzero p;
        assert (d >= k ==> coeff p d = (zero <: t))

let divmod_step_degree_decreases (#t:Type) {| cr: commutative_ring t |}
    (p q: polynomial t) (m n: nat) (c: t)
  : Lemma (requires Some? (poly_deg p) /\ Some?.v (poly_deg p) = m /\
                    Some? (poly_deg q) /\ Some?.v (poly_deg q) = n /\
                    m >= n /\
                    (cr.cr_r.mul c (coeff q n)) = coeff p m)
          (ensures
             (let mono = monomial c (Prims.op_Subtraction m n) in
              let r = poly_sub p (poly_mul mono q) in
              None? (poly_deg r) \/ Some?.v (poly_deg r) < m))
  = let mono : polynomial t = monomial c (Prims.op_Subtraction m n) in
    let r : polynomial t = poly_sub p (poly_mul mono q) in
    match poly_deg r with
    | None   -> ()
    | Some d ->
        if d >= m then begin
          if d = m then cancellation_at p q m n c
          else residue_zero_above p q m n c d;
          leading_coeff_nonzero r
        end

#pop-options

(* ----- field-level: (x * inv y) * y = x ----- *)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"

let lc_cancel_field (#t:Type) {| f: field t |} (x y: t)
  : Lemma (requires is_nonzero y)
          (ensures  (let inv_y = f.f_sf.sf_mig.inv y in
                     ((x * inv_y) * y) = x))
  = let inv_y = f.f_sf.sf_mig.inv y in
    f.f_sf.sf_mig.inversion_lemma y;
    mul_associativity x inv_y y;
    reflexivity x;
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
  : Lemma (requires Some? (poly_deg q) /\
                    (None? (poly_deg p) \/ fuel > Some?.v (poly_deg p)))
          (ensures  (let (_, rem) = poly_divmod_fuel #t #f p q fuel in
                     None? (poly_deg rem) \/
                     Some?.v (poly_deg rem) < Some?.v (poly_deg q)))
          (decreases fuel)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    if fuel = 0 then ()
    else
      match poly_deg p, poly_deg q with
      | None, _ -> ()
      | _, None -> ()
      | Some m, Some n ->
          if m < n then ()
          else begin
            leading_coeff_nonzero q;
            let lc_p = coeff p m in
            let lc_q = coeff q n in
            let inv_lc_q = f.f_sf.sf_mig.inv lc_q in
            let c = lc_p * inv_lc_q in
            lc_cancel_field #t #f lc_p lc_q;
            divmod_step_degree_decreases #t #cr p q m n c;
            let mono : polynomial t = monomial c (Prims.op_Subtraction m n) in
            let sub_term = poly_mul mono q in
            let p' = poly_sub p sub_term in
            poly_divmod_fuel_degree #t #f p' q (Prims.op_Subtraction fuel 1)
          end

#pop-options

(* ================================================================ *)
(*  Public divmod entry points + euclidean-domain instance          *)
(* ================================================================ *)

let poly_divmod (#t:Type) {| f: field t |} (p q: polynomial t)
  : polynomial t & polynomial t
  = poly_divmod_fuel #t #f p q (Prims.op_Addition (L.length p) 1)

let poly_divmod_correct (#t:Type) {| f: field t |}
                        (p q: polynomial t)
  : Lemma (let (quot, rem) = poly_divmod #t #f p q in
           poly_eq p (poly_add (poly_mul q quot) rem))
  = poly_divmod_fuel_correct #t #f p q (Prims.op_Addition (L.length p) 1)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let degree_lt_length (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (requires Some? (poly_deg p))
          (ensures  Some?.v (poly_deg p) < L.length p)
  = ()
#pop-options

let poly_divmod_correct_degree (#t:Type) {| f: field t |}
                               (p q: polynomial t)
  : Lemma (requires Some? (poly_deg q))
          (ensures (let (_, rem) = poly_divmod #t #f p q in
                    None? (poly_deg rem) \/
                    Some?.v (poly_deg rem) < Some?.v (poly_deg q)))
  = (match poly_deg p with
     | None   -> ()
     | Some _ -> degree_lt_length p);
    poly_divmod_fuel_degree #t #f p q (Prims.op_Addition (L.length p) 1)

(* ================================================================ *)
(*  polynomial_euclidean_domain_instance                            *)
(* ================================================================ *)

let _zero_eq_nil (#t:Type) {| cr: commutative_ring t |}
  : Lemma (poly_zero #t == ([] <: polynomial t))
  = ()

instance polynomial_euclidean_domain_instance
    (#t:Type) {| f: field t |}
  : polynomial_euclidean_domain t
       #f
       #(polynomial_commutative_ring_instance #t #(cr_of_id t #(id_of_f t)))
       #(polynomial_integral_domain_instance  #t #(id_of_f t))
  =
  let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
  let pcrc : polynomial_commutative_ring t = polynomial_commutative_ring_instance #t #cr in
  let divmod_fn (p: polynomial t) (d: polynomial t { not (d = poly_zero #t) })
    : polynomial t & polynomial t
    = poly_divmod #t #f p d
  in
  let divmod_lemma_fn (p: polynomial t) (d: polynomial t { not (d = poly_zero #t) })
    : Lemma (let q, r = divmod_fn p d in
             poly_eq p (poly_add (poly_mul d q) r))
    = poly_divmod_correct #t #f p d
  in
  let d_has_deg (d: polynomial t { not (d = poly_zero #t) })
    : Lemma (Some? (poly_deg d))
    = match d with
      | []    -> ()
      | _ :: _ -> ()
  in
  let divmod_degree_fn (p: polynomial t) (d: polynomial t { not (d = poly_zero #t) })
    : Lemma (let _, r = divmod_fn p d in
             poly_eq r (poly_zero #t) \/
             (Some? (poly_deg r) /\ Some? (poly_deg d) /\
              Some?.v (poly_deg r) < Some?.v (poly_deg d)))
    = d_has_deg d;
      poly_divmod_correct_degree #t #f p d;
      let (_, r) = divmod_fn p d in
      match poly_deg r with
      | None   -> poly_eq_reflexivity ([] <: polynomial t)
      | Some _ -> ()
  in
  { divmod = divmod_fn;
    divmod_lemma = divmod_lemma_fn;
    divmod_degree = divmod_degree_fn;
  }
