module FStar.CAS.Matrix.Determinant
(*   Determinant of a square matrix via the Leibniz formula:       det(M) = Σ_{σ ∈ S_n}  sign(σ) · ∏_{i=0..n-1} M(i, σ(i))   Built on top of:     - FStar.CAS.Permutation             (permutation, parity, identity)     - FStar.CAS.Permutation.Enum        (all_permutations)     - FStar.CAS.Permutation.Sum         (sum_over_perms, reindexing)     - FStar.CAS.Matrix                  (square_matrix)     - FStar.CAS.FinSum                  (prod_range)   Coefficient ring: any [commutative_ring t] (we need + and -).   This file currently provides the bare definition and the identity-matrix   case [det (identity_matrix n) = one].  Multilinearity, alternating,   row-swap antisymmetry, transpose-invariance, and det(M·N) = det(M)·det(N)   follow in subsequent modules / sections.   Author: A. Rozanov (CuteCAS).*)
module L = FStar.List.Tot
open FStar.CAS.Equatable
open FStar.CAS.Grouplikes
open FStar.CAS.Ringlikes
open FStar.CAS.FinSum
open FStar.CAS.Permutation
open FStar.CAS.Permutation.Enum
open FStar.CAS.Permutation.Sum
open FStar.CAS.Matrix

(* Private aliases for removed Permutation API. *)
private let perm_eq_sym (#n: nat) (p q: permutation n)
  : Lemma (requires perm_eq p q) (ensures perm_eq q p)
  = reveal_opaque (`%perm_eq) (perm_eq p q);
    reveal_opaque (`%perm_eq) (perm_eq q p);
    perm_eq_bool_from_sym p q 0

(* -------------------------------------------------------------------- *)
(*  Product along a permutation: ∏_{i=0..n-1} M(i, p.fwd i).            *)
(* -------------------------------------------------------------------- *)
let perm_product  (#t: Type) {| r: ring t |} (#n: nat)  (m: square_matrix t n) (p: permutation n) : t  = prod_range      (fun (i: nat) -> if i < n then m (i <: fin n) (p.fwd (i <: fin n)) else one)      0 n

let perm_product_unfold (#t: Type) {| r: ring t |} (#n: nat)
  (m: square_matrix t n) (p: permutation n)
  : Lemma (perm_product m p ==
           prod_range (fun (k: nat) -> if k < n then m (k <: fin n) (p.fwd (k <: fin n)) else one) 0 n)
  = ()
(* -------------------------------------------------------------------- *)
(*  Signed Leibniz summand.                                             *)
(* -------------------------------------------------------------------- *)
let leibniz_term  (#t: Type) {| r: ring t |} (#n: nat)  (m: square_matrix t n) (p: permutation n) : t  = if parity p    then perm_product m p    else (-(perm_product m p))
(* -------------------------------------------------------------------- *)
(*  Determinant.                                                         *)
(* -------------------------------------------------------------------- *)
let det  (#t: Type) {| r: ring t |} (#n: nat) (m: square_matrix t n) : t  = sum_over_perms n (leibniz_term m)
let det_unfold (#t: Type) {| r: ring t |} (#n: nat) (m: square_matrix t n)  : Lemma (det m == sum_over_perms n (leibniz_term m))  = ()
(* -------------------------------------------------------------------- *)
(*  Helpers on prod_range needed by det_identity.                       *)
(* -------------------------------------------------------------------- *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"let rec prod_range_const_one  (#t: Type) {| r: ring t |} (lo hi: nat)  : Lemma (ensures prod_range #t (fun _ -> one) lo hi = one)          (decreases (if hi > lo then nat_minus hi lo else 0))  = if lo >= hi then reflexivity (one #t)    else begin      prod_range_unfold_left #t (fun _ -> one) lo hi;      prod_range_const_one #t #r (nat_succ lo) hi;      reflexivity (one #t);      reflexivity (one #t * prod_range #t (fun _ -> one) (nat_succ lo) hi);      mul_congruence (one #t) (prod_range #t (fun _ -> one) (nat_succ lo) hi)                     (one #t) (one #t);      left_mul_identity (one #t);      trans_lemma [ prod_range #t (fun _ -> one) lo hi;                    one #t * prod_range #t (fun _ -> one) (nat_succ lo) hi;                    one #t * one #t;                    one #t ]    end
#pop-options
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"let rec prod_range_zero_factor  (#t: Type) {| r: ring t |} (f: nat -> t) (lo hi: nat) (k: nat)  : Lemma (requires lo <= k /\ k < hi /\ f k = zero)          (ensures  prod_range f lo hi = zero)          (decreases (if hi > lo then nat_minus hi lo else 0))  = prod_range_unfold_left f lo hi;    if k = lo then begin      reflexivity (prod_range f (nat_succ lo) hi);      reflexivity (f lo * prod_range f (nat_succ lo) hi);      mul_congruence (f lo) (prod_range f (nat_succ lo) hi)                     zero (prod_range f (nat_succ lo) hi);      ring_zero_is_left_absorber (prod_range f (nat_succ lo) hi);      trans_lemma [ prod_range f lo hi;                    f lo * prod_range f (nat_succ lo) hi;                    zero * prod_range f (nat_succ lo) hi;                    zero #t ]    end else begin      prod_range_zero_factor f (nat_succ lo) hi k;      reflexivity (f lo);      reflexivity (f lo * prod_range f (nat_succ lo) hi);      mul_congruence (f lo) (prod_range f (nat_succ lo) hi)                     (f lo) zero;      ring_zero_is_right_absorber (f lo);      trans_lemma [ prod_range f lo hi;                    f lo * prod_range f (nat_succ lo) hi;                    f lo * zero;                    zero #t ]    end
#pop-options
(* -------------------------------------------------------------------- *)
(*  det (identity matrix) = one                                          *)
(* -------------------------------------------------------------------- *)
module TC = FStar.Tactics.Typeclasses
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"private let neg_congruence_lem (#t:Type) {| g: add_comm_group t |} (a b: t)  : Lemma (requires a = b) (ensures (-a) = (-b))  = let ha = g.add_group.add_monoid.has_zero in    let neg_a : t = -a in    let neg_b : t = -b in    ha.eq.reflexivity neg_b;    add_congruence a neg_b b neg_b;    g.add_group.negation b;    ha.eq.transitivity (a + neg_b) (b + neg_b) zero;    add_commutativity neg_b a;    ha.eq.transitivity (neg_b + a) (a + neg_b) zero;    g.add_group.negation a;    ha.eq.reflexivity neg_a;    add_congruence neg_b (a + (-a)) neg_b zero;    ha.eq.symmetry (neg_b + (a + (-a))) (neg_b + zero);    right_add_identity neg_b;    ha.eq.symmetry (neg_b + zero) neg_b;    ha.eq.transitivity neg_b (neg_b + zero) (neg_b + (a + (-a)));    add_associativity neg_b a (-a);    ha.eq.symmetry ((neg_b + a) + (-a)) (neg_b + (a + (-a)));    ha.eq.transitivity neg_b (neg_b + (a + (-a))) ((neg_b + a) + (-a));    add_congruence (neg_b + a) (-a) zero (-a);    ha.eq.transitivity neg_b ((neg_b + a) + (-a)) (zero + (-a));    left_add_identity neg_a;    ha.eq.transitivity neg_b (zero + neg_a) neg_a;    ha.eq.symmetry neg_b neg_a
#pop-options
private let neg_zero_lem (#t:Type) {| g: add_comm_group t |}  : Lemma ((-(zero #t)) = zero)  = let ha = g.add_group.add_monoid.has_zero in    g.add_group.negation (zero #t);    left_add_identity (-(zero #t));    ha.eq.symmetry (zero + (-(zero #t))) (-(zero #t));    ha.eq.transitivity (-(zero #t)) (zero + (-(zero #t))) (zero #t)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"let perm_product_id_identity (#t: Type) {| r: ring t |} (n: nat)  : Lemma (perm_product (id_matrix #t n) (identity n) = one)  = let body : nat -> t      = fun (i: nat) ->          if i < n          then id_matrix #t n (i <: fin n) ((identity n).fwd (i <: fin n))          else one in    let const_one : nat -> t = fun _ -> one in    let aux (k: nat) : Lemma (0 <= k /\ k < n ==> body k = const_one k)      = if k < n then begin          let i : fin n = k in          identity_fwd n i;          id_matrix_diag #t n i;          reflexivity (one #t);          reflexivity (body k)        end    in    Classical.forall_intro aux;    prod_range_congruence #t body const_one 0 n;    prod_range_const_one #t #r 0 n;    assert_norm (perm_product (id_matrix #t n) (identity n) ==                 prod_range #t body 0 n);    let eq : equatable t = TC.solve in    eq.transitivity (prod_range body 0 n)                    (prod_range const_one 0 n)                    (one #t);    reflexivity (perm_product (id_matrix #t n) (identity n));    eq.transitivity (perm_product (id_matrix #t n) (identity n))                    (prod_range body 0 n)                    (one #t)
#pop-options
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"let perm_product_id_nonidentity (#t: Type) {| r: ring t |} (#n: nat)  (p: permutation n)  : Lemma (requires ~(perm_eq p (identity n)))          (ensures  perm_product (id_matrix #t n) p = zero)  = let phi (i: fin n) : prop = ~(p.fwd i == i) in    let helper (assume_not : (i: fin n -> Lemma (~(phi i)))) : Lemma False
      = Classical.forall_intro assume_not;
        assert (forall (i: fin n). p.fwd i == i);
        perm_eq_intro p (identity n);
        assert False    in    Classical.exists_intro_not_all_not #(fin n) #phi helper;    eliminate exists (i: fin n). phi i      returns perm_product (id_matrix #t n) p = zero with _.      begin        let body : nat -> t          = fun (j: nat) ->              if j < n              then id_matrix #t n (j <: fin n) (p.fwd (j <: fin n))              else one in        let k : nat = i in        id_matrix_off #t n i (p.fwd i);        assert (body k == zero #t);        reflexivity (zero #t);        prod_range_zero_factor #t body 0 n k;        assert_norm (perm_product (id_matrix #t n) p == prod_range #t body 0 n);        reflexivity (perm_product (id_matrix #t n) p);        let eq : equatable t = TC.solve in        eq.transitivity (perm_product (id_matrix #t n) p)                        (prod_range body 0 n)                        (zero #t)      end
#pop-options
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"let perm_product_id_respects_perm_eq (#t: Type) {| r: ring t |} (n: nat)  (p q: permutation n)  : Lemma (requires perm_eq p q)          (ensures  perm_product (id_matrix #t n) p = perm_product (id_matrix #t n) q)  = let f : nat -> t = fun (i: nat) ->      if i < n then id_matrix #t n (i <: fin n) (p.fwd (i <: fin n)) else one in    let g : nat -> t = fun (i: nat) ->      if i < n then id_matrix #t n (i <: fin n) (q.fwd (i <: fin n)) else one in    let aux (k: nat) : Lemma (0 <= k /\ k < n ==> f k = g k)      = if k < n then begin          let i : fin n = k in          perm_eq_elim p q i;          reflexivity (f k)        end    in    Classical.forall_intro aux;    prod_range_congruence #t f g 0 n;    assert_norm (perm_product (id_matrix #t n) p == prod_range #t f 0 n);    assert_norm (perm_product (id_matrix #t n) q == prod_range #t g 0 n);    reflexivity (perm_product (id_matrix #t n) p);    reflexivity (perm_product (id_matrix #t n) q);    let eq : equatable t = TC.solve in    eq.transitivity (perm_product (id_matrix #t n) p) (prod_range f 0 n) (prod_range g 0 n);    eq.transitivity (perm_product (id_matrix #t n) p) (prod_range g 0 n) (perm_product (id_matrix #t n) q)
#pop-options
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"let leibniz_term_id_respects_perm_eq (#t: Type) {| r: ring t |} (n: nat)  : Lemma (respects_perm_eq #t (leibniz_term (id_matrix #t n)))  = let f = leibniz_term (id_matrix #t #_ #_ n) in    let aux (p q: permutation n) : Lemma (perm_eq p q ==> f p = f q)      = if FStar.IndefiniteDescription.strong_excluded_middle (perm_eq p q) then begin          parity_perm_eq_invariant p q;          perm_product_id_respects_perm_eq #t #r n p q;          if parity p then reflexivity (f p)          else begin            let pp = perm_product (id_matrix #t n) p in            let qq = perm_product (id_matrix #t n) q in            assert (pp = qq);            neg_congruence_lem #t #(add_comm_group_of_ring t r) pp qq;            reflexivity (f p)          end        end    in    Classical.forall_intro_2 aux;    respects_perm_eq_intro f
#pop-options
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"let det_identity (#t: Type) {| r: ring t |} (n: nat)  : Lemma (det (id_matrix #t n) = one)  = let f = leibniz_term (id_matrix #t #_ #_ n) in    let p0 = identity n in    leibniz_term_id_respects_perm_eq #t #r n;    let vanish (q: permutation n) : Lemma (~(perm_eq p0 q) ==> f q = zero)      = if FStar.IndefiniteDescription.strong_excluded_middle (~(perm_eq p0 q)) then begin          let not_q_p0 () : Lemma (requires perm_eq q p0) (ensures False)
            = perm_eq_sym q p0;
              assert (perm_eq p0 q)
          in
          Classical.move_requires not_q_p0 ();
          perm_product_id_nonidentity #t #r #n q;          parity_identity n;          if parity q then reflexivity (f q)          else begin            let pp = perm_product (id_matrix #t n) q in            assert (pp = zero #t);            neg_zero_lem #t #(add_comm_group_of_ring t r);            neg_congruence_lem #t #(add_comm_group_of_ring t r) pp (zero #t);            let eq : equatable t = TC.solve in            reflexivity (f q);            eq.transitivity (f q) (-pp) ((-(zero #t)));            eq.transitivity (f q) (-(zero #t)) (zero #t)          end        end    in    Classical.forall_intro vanish;    sum_over_perms_single n f p0;    parity_identity n;    perm_product_id_identity #t #r n;    det_unfold (id_matrix #t n);    assert (parity p0 == true);    assert (f p0 == perm_product (id_matrix #t n) p0);    reflexivity (det (id_matrix #t n));    reflexivity (f p0);    let eq : equatable t = TC.solve in    eq.transitivity (det (id_matrix #t n)) (sum_over_perms n f) (f p0);    eq.transitivity (det (id_matrix #t n)) (f p0) (perm_product (id_matrix #t n) p0);    eq.transitivity (det (id_matrix #t n)) (perm_product (id_matrix #t n) p0) (one #t)
#pop-options
(* -------------------------------------------------------------------- *)
(*  det of a matrix with a zero row is zero.                            *)
(*                                                                      *)
(*  Every Leibniz summand contains the factor M(k, p.fwd k) = zero, so  *)
(*  perm_product m p = zero for every p, hence leibniz_term m p = zero. *)
(* -------------------------------------------------------------------- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"let perm_product_zero_row  (#t: Type) {| r: ring t |} (#n: nat)  (m: square_matrix t n) (k: fin n)  (zrow: squash (forall (j: fin n). m k j = zero))  (p: permutation n)  : Lemma (perm_product m p = zero)  = let body : nat -> t =      fun (i: nat) -> if i < n then m (i <: fin n) (p.fwd (i <: fin n)) else one in    assert (body k == m k (p.fwd k));    assert (m k (p.fwd k) = zero);    reflexivity (m k (p.fwd k));    let eq : equatable t = TC.solve in    eq.transitivity (body k) (m k (p.fwd k)) (zero #t);    prod_range_zero_factor body 0 n k;    reflexivity (perm_product m p)
#pop-options
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"let det_zero_row  (#t: Type) {| r: ring t |} (#n: nat)  (m: square_matrix t n) (k: fin n)  : Lemma (requires forall (j: fin n). m k j = zero)          (ensures  det m = zero)  = let zrow : squash (forall (j: fin n). m k j = zero) = () in    let f = leibniz_term m in    let term_zero (p: permutation n) : Lemma (f p = zero)      = perm_product_zero_row #t #r #n m k zrow p;        if parity p then reflexivity (f p)        else begin          let pp = perm_product m p in          assert (f p == (-pp));          reflexivity (f p);          assert (pp = zero #t);          neg_zero_lem #t #(add_comm_group_of_ring t r);          neg_congruence_lem #t #(add_comm_group_of_ring t r) pp (zero #t);          let eq : equatable t = TC.solve in          eq.transitivity (f p) (-pp) ((-(zero #t)));          eq.transitivity (f p) (-(zero #t)) (zero #t)        end    in    Classical.forall_intro term_zero;    assert (forall (p: permutation n). f p = zero);    sum_over_perms_all_zero n f;    det_unfold m;    reflexivity (det m);    reflexivity (sum_over_perms n f);    let eq : equatable t = TC.solve in    eq.transitivity (det m) (sum_over_perms n f) (zero #t)
#pop-options
(* -------------------------------------------------------------------- *)
(*  det(M^T) = det(M).                                                  *)
(*                                                                      *)
(*  Strategy:                                                           *)
(*    det(M^T) = sum_p sign(p) * perm_product(M^T, p)                  *)
(*             = sum_p sign(p^{-1}) * perm_product(M^T, p^{-1})         *)
(*               [reindexing p -> p^{-1}]                              *)
(*             = sum_p sign(p) * perm_product(M, p)                    *)
(*               [parity_inverse and prod_range_perm_invariance]       *)
(*             = det(M).                                                *)
(* -------------------------------------------------------------------- *)
(* perm_product respects perm_eq in its permutation argument. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"let perm_product_respects_perm_eq  (#t: Type) {| r: ring t |} (#n: nat)  (m: square_matrix t n) (p q: permutation n)  : Lemma (requires perm_eq p q)          (ensures  perm_product m p = perm_product m q)  = let bp : nat -> t =      fun i -> if i < n then m (i <: fin n) (p.fwd (i <: fin n)) else one in    let bq : nat -> t =      fun i -> if i < n then m (i <: fin n) (q.fwd (i <: fin n)) else one in    let h (k: nat) : Lemma (requires 0 <= k /\ k < n) (ensures bp k = bq k)      = perm_eq_elim p q (k <: fin n);        reflexivity (m (k <: fin n) (p.fwd (k <: fin n)))    in    Classical.forall_intro (Classical.move_requires h);    prod_range_congruence bp bq 0 n;    reflexivity (perm_product m p);    reflexivity (perm_product m q);    let eq : equatable t = TC.solve in    eq.transitivity (perm_product m p) (prod_range bp 0 n) (prod_range bq 0 n);    eq.transitivity (perm_product m p) (prod_range bq 0 n) (perm_product m q)
#pop-options
(* leibniz_term respects perm_eq in its permutation argument. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"let leibniz_term_respects_perm_eq  (#t: Type) {| r: ring t |} (#n: nat)  (m: square_matrix t n)  : Lemma (respects_perm_eq #t (leibniz_term m))  = let f = leibniz_term m in    let aux (p q: permutation n) : Lemma (requires perm_eq p q) (ensures f p = f q)      = perm_product_respects_perm_eq m p q;        parity_perm_eq_invariant p q;        if parity p        then begin          reflexivity (f p);          reflexivity (f q);          let eq : equatable t = TC.solve in          eq.transitivity (f p) (perm_product m p) (perm_product m q);          eq.transitivity (f p) (perm_product m q) (f q)        end else begin          let pp = perm_product m p in          let qq = perm_product m q in          neg_congruence_lem #t #(add_comm_group_of_ring t r) pp qq;          reflexivity (f p);          reflexivity (f q);          let eq : equatable t = TC.solve in          eq.transitivity (f p) (-pp) (-qq);          eq.transitivity (f p) (-qq) (f q)        end    in    Classical.forall_intro_2 (fun p q -> Classical.move_requires (aux p) q);    respects_perm_eq_intro f
#pop-options
(* perm_product (transpose m) (inverse p) = perm_product m p, in any comm_ring. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"let perm_product_transpose_inverse  (#t: Type) {| cr: commutative_ring t |} (#n: nat)  (m: square_matrix t n) (p: permutation n)  : Lemma (perm_product (transpose m) (inverse p) = perm_product m p)  = let mcm : mul_comm_monoid t = mul_comm_monoid_of_comm_ring t cr in  elim_equatable_laws t #(mcm.mul_monoid.mul_semigroup.has_mul.eq);  transitivity_for_calc_proofs t #(mcm.mul_monoid.mul_semigroup.has_mul.eq);  let bigF : nat -> t =    fun (k: nat) -> if k < n then m (k <: fin n) (p.fwd (k <: fin n)) else one in  let bigG : nat -> t =    fun (k: nat) -> if k < n             then (transpose m) (k <: fin n) ((inverse p).fwd (k <: fin n))             else one in  let body_p : nat -> t =    fun (k: nat) -> if k < n then bigF ((inverse p).fwd (k <: fin n)) else one in  (* Pointwise bigG = body_p on [0, n). *)  let hGH (k: nat) : Lemma (requires 0 <= k /\ k < n) (ensures bigG k = body_p k)    = let kf : fin n = k <: fin n in      inverse_fwd p kf;      let j : fin n = (inverse p).fwd kf in      p.fwd_bwd_id kf;      reflexivity (m j (p.fwd j))  in  Classical.forall_intro (Classical.move_requires hGH);  prod_range_congruence bigG body_p 0 n;  (* prod_range body_p 0 n = prod_range bigF 0 n via perm_invariance wrapper. *)  let bp_hyp (k: nat) : Lemma    (0 <= k /\ k < n ==> body_p k = bigF ((inverse p).fwd (k <: fin n)))    = if 0 <= k && k < n then        reflexivity (bigF ((inverse p).fwd (k <: fin n))) in  Classical.forall_intro bp_hyp;  let bi_hyp (k: nat) : Lemma    (0 <= k /\ k < n ==> bigF k = bigF k)    = if 0 <= k && k < n then reflexivity (bigF k) in  Classical.forall_intro bi_hyp;  prod_range_perm_invariance_fn #t #mcm #n bigF body_p bigF (inverse p);  perm_product_unfold (transpose m) (inverse p);  perm_product_unfold m p;  reflexivity (perm_product (transpose m) (inverse p));  reflexivity (perm_product m p);  trans_lemma #t #(mcm.mul_monoid.mul_semigroup.has_mul.eq)              [ perm_product (transpose m) (inverse p);                prod_range bigG 0 n;                prod_range body_p 0 n;                prod_range bigF 0 n;                perm_product m p ]
#pop-options
(* leibniz_term (transpose m) (inverse p) = leibniz_term m p.                  *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"let leibniz_transpose_inverse_eq  (#t: Type) {| cr: commutative_ring t |} (#n: nat)  (m: square_matrix t n) (p: permutation n)  : Lemma (leibniz_term (transpose m) (inverse p) = leibniz_term m p)  = let r : ring t = cr.ring in    parity_inverse p;    perm_product_transpose_inverse #t #cr #n m p;    let lhs = leibniz_term (transpose m) (inverse p) in    let rhs = leibniz_term m p in    if parity p    then begin      (* lhs = perm_product (transpose m) (inverse p); rhs = perm_product m p *)      reflexivity lhs;      reflexivity rhs;      let eq : equatable t = TC.solve in      eq.transitivity lhs (perm_product (transpose m) (inverse p)) (perm_product m p);      eq.transitivity lhs (perm_product m p) rhs    end else begin      let lp = perm_product (transpose m) (inverse p) in      let rp = perm_product m p in      neg_congruence_lem #t #(add_comm_group_of_ring t r) lp rp;      reflexivity lhs;      reflexivity rhs;      let eq : equatable t = TC.solve in      eq.transitivity lhs (-lp) (-rp);      eq.transitivity lhs (-rp) rhs    end
#pop-options
(* Headline: det(M^T) = det(M) over any commutative ring. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"let det_transpose  (#t: Type) {| cr: commutative_ring t |} (#n: nat)  (m: square_matrix t n)  : Lemma (det (transpose m) = det m)  = let r : ring t = cr.ring in    let f = leibniz_term (transpose m) in    let g = leibniz_term m in    leibniz_term_respects_perm_eq #t #r #n (transpose m);    leibniz_term_respects_perm_eq #t #r #n m;    (* sum_over_perms n f = sum_over_perms n (fun s -> f (inverse s)) *)    sum_over_perms_reindex_inverse n f;    (* fun s -> f (inverse s) is pointwise equal to g *)    let pointwise (s: permutation n) : Lemma (f (inverse s) = g s)      = leibniz_transpose_inverse_eq #t #cr #n m s in    Classical.forall_intro pointwise;    sum_over_perms_congruence n (fun s -> f (inverse s)) g;    det_unfold (transpose m);    det_unfold m;    reflexivity (det (transpose m));    reflexivity (det m);    let eq : equatable t = TC.solve in    (* det (transpose m) = sum_over_perms n f *)    eq.transitivity (det (transpose m)) (sum_over_perms n f)                    (sum_over_perms n (fun s -> f (inverse s)));    eq.transitivity (det (transpose m))                    (sum_over_perms n (fun s -> f (inverse s)))                    (sum_over_perms n g);    eq.transitivity (det (transpose m)) (sum_over_perms n g) (det m)
#pop-options
(* -------------------------------------------------------------------- *)
(*  Row swap and alternating property.                                  *)
(*                                                                      *)
(*  row_swap m i j is m with rows i and j swapped.                      *)
(*  Headline: det(row_swap m i j) = -det(m) when i <> j.                 *)
(* -------------------------------------------------------------------- *)
let row_swap (#t: Type) (#n: nat) (m: square_matrix t n) (i j: fin n)  : square_matrix t n  = fun (k: fin n) (l: fin n) -> m ((transposition n i j).fwd k) l
(* Key calculation: perm_product (row_swap m i j) p = perm_product m (compose p σ),   where σ = transposition n i j. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"let perm_product_row_swap  (#t: Type) {| cr: commutative_ring t |} (#n: nat)  (m: square_matrix t n) (i j: fin n) (p: permutation n)  : Lemma (perm_product (row_swap m i j) p =           perm_product m (compose p (transposition n i j)))  = let mcm : mul_comm_monoid t = mul_comm_monoid_of_comm_ring t cr in    elim_equatable_laws t #(mcm.mul_monoid.mul_semigroup.has_mul.eq);    transitivity_for_calc_proofs t #(mcm.mul_monoid.mul_semigroup.has_mul.eq);    let sigma = transposition n i j in    let q = compose p sigma in    let lhs_body : nat -> t =      fun (k: nat) -> if k < n                  then (row_swap m i j) (k <: fin n) (p.fwd (k <: fin n))                  else one in    let rhs_body : nat -> t =      fun (k: nat) -> if k < n                  then m (k <: fin n) (q.fwd (k <: fin n))                  else one in    (* The "f" we feed perm_invariance: f(k) = if k<n then m (σ.fwd k) (p.fwd (σ.fwd k)) else one,       but cleaner: f(k) = m(k, p.fwd(σ.fwd k)) for k<n. We use a slightly different bridge:       reindex Π_k m(σ.fwd k, p.fwd k) via σ to get Π_k m(k, p.fwd(σ.fwd k)). *)    let f_via_sigma : nat -> t =      fun (k: nat) -> if k < n                  then m ((sigma.fwd (k <: fin n)) <: fin n)                           (p.fwd ((sigma.fwd (k <: fin n)) <: fin n))                  else one in    (* lhs_body k = f_via_sigma applied at σ.fwd k? No.       Reindex direction: prod_range_perm_invariance with f and permutation σ gives:         Π_k (if k<n then f(σ.fwd k) else one) = Π_k (if k<n then f(k) else one).       Set f(k) = if k<n then m k (p.fwd(σ.fwd k)) else one.       Then f(σ.fwd k) for k<n = m(σ.fwd k, p.fwd(σ.fwd(σ.fwd k))) = m(σ.fwd k, p.fwd k)       (since σ.fwd∘σ.fwd = id by transposition_self_inverse).       So Π_k m(σ.fwd k, p.fwd k) = Π_k m(k, p.fwd(σ.fwd k)). *)    let f : nat -> t =      fun (k: nat) -> if k < n                  then m (k <: fin n) (p.fwd ((sigma.fwd (k <: fin n)) <: fin n))                  else one in    transposition_self_inverse n i j;    let body_p_hyp (k: nat) : Lemma      (0 <= k /\ k < n ==>       lhs_body k = f (sigma.fwd (k <: fin n)))      = if 0 <= k && k < n then begin          let kf : fin n = k <: fin n in          let sk : fin n = sigma.fwd kf in          compose_fwd sigma sigma kf;          perm_eq_elim (compose sigma sigma) (identity n) kf;          identity_fwd n kf;          (* (compose sigma sigma).fwd kf = sigma.fwd (sigma.fwd kf) = identity.fwd kf = kf *)          reflexivity (m kf (p.fwd kf))        end in    Classical.forall_intro body_p_hyp;    let body_id_hyp (k: nat) : Lemma      (0 <= k /\ k < n ==> rhs_body k = f k)      = if 0 <= k && k < n then begin          let kf : fin n = k <: fin n in          compose_fwd p sigma kf;          (* q.fwd kf = (compose p sigma).fwd kf = p.fwd (sigma.fwd kf) *)          reflexivity (m kf (p.fwd (sigma.fwd kf)))        end in    Classical.forall_intro body_id_hyp;    prod_range_perm_invariance_fn #t #mcm #n f lhs_body rhs_body sigma;    perm_product_unfold (row_swap m i j) p;    perm_product_unfold m q;    reflexivity (perm_product (row_swap m i j) p);    reflexivity (perm_product m q);    trans_lemma #t #(mcm.mul_monoid.mul_semigroup.has_mul.eq)                [ perm_product (row_swap m i j) p;                  prod_range lhs_body 0 n;                  prod_range rhs_body 0 n;                  perm_product m q ]
#pop-options
(* leibniz_term (row_swap m i j) p = -(leibniz_term m (compose p σ)) when i <> j,   where σ = transposition n i j. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"let leibniz_term_row_swap  (#t: Type) {| cr: commutative_ring t |} (#n: nat)  (m: square_matrix t n) (i j: fin n) (p: permutation n)  : Lemma (requires ~(i == j))          (ensures  leibniz_term (row_swap m i j) p =                    -(leibniz_term m (compose p (transposition n i j))))  = let r : ring t = cr.ring in    let sigma = transposition n i j in    let q = compose p sigma in    perm_product_row_swap #t #cr #n m i j p;    (* perm_product (row_swap m i j) p = perm_product m q *)    parity_transposition n i j;    (* parity sigma == (i = j) == false *)    sign_homomorphism p sigma;    (* parity q == (parity p = parity sigma) == (parity p = false) == not (parity p) *)    let lhs = leibniz_term (row_swap m i j) p in    let rhs = -(leibniz_term m q) in    let pp1 = perm_product (row_swap m i j) p in    let pp2 = perm_product m q in    if parity p    then begin      assert (leibniz_term (row_swap m i j) p == pp1);      assert (leibniz_term m q == -pp2);      assert (rhs == -(-pp2));      reflexivity pp1;      reflexivity pp2;      double_negation_lemma #t #(add_comm_group_of_ring t r).add_group pp2;      symmetry (-(-pp2)) pp2;      trans_lemma [ pp1; pp2; -(-pp2) ];      assert (pp1 = -(-pp2));      assert (lhs = rhs)    end else begin      assert (leibniz_term (row_swap m i j) p == -pp1);      assert (leibniz_term m q == pp2);      assert (rhs == -pp2);      neg_congruence_lem #t #(add_comm_group_of_ring t r) pp1 pp2;      assert ((-pp1) = (-pp2));      assert (lhs = rhs)    end
#pop-options
(* Headline: det(row_swap m i j) = -det(m) when i <> j.  *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 80"let det_row_swap  (#t: Type) {| cr: commutative_ring t |} (#n: nat)  (m: square_matrix t n) (i j: fin n)  : Lemma (requires ~(i == j))          (ensures  det (row_swap m i j) = -(det m))  = let r : ring t = cr.ring in    let sigma = transposition n i j in    let f = leibniz_term (row_swap m i j) in    let g = leibniz_term m in    leibniz_term_respects_perm_eq #t #r #n m;    (* By reindexing: sum_over_perms n g = sum_over_perms n (fun s -> g (compose s sigma)). *)    sum_over_perms_reindex n g sigma;    (* By leibniz_term_row_swap: f s = -(g (compose s sigma)) for every s. *)    let pointwise (s: permutation n) : Lemma (f s = -(g (compose s sigma)))      = leibniz_term_row_swap #t #cr #n m i j s in    Classical.forall_intro pointwise;    sum_over_perms_congruence n f (fun s -> -(g (compose s sigma)));    (* sum_over_perms n (fun s -> -(g (compose s sigma))) = -(sum_over_perms n (fun s -> g (compose s sigma))) *)    sum_over_perms_neg #t #(add_comm_group_of_ring t r) n (fun s -> g (compose s sigma));    (* sum_over_perms_reindex gives: sum n g = sum n (fun s -> g (compose s sigma)). Flip it. *)    symmetry (sum_over_perms n g) (sum_over_perms n (fun s -> g (compose s sigma)));    (* Chain together. *)    det_unfold (row_swap m i j);    det_unfold m;    reflexivity (sum_over_perms n g);    reflexivity (sum_over_perms n f);    symmetry (det m) (sum_over_perms n g);    neg_congruence_lem #t #(add_comm_group_of_ring t r)                   (sum_over_perms n (fun s -> g (compose s sigma)))                   (sum_over_perms n g);    neg_congruence_lem #t #(add_comm_group_of_ring t r)                   (sum_over_perms n g)                   (det m);    trans_lemma [ det (row_swap m i j);                  sum_over_perms n f;                  sum_over_perms n (fun s -> -(g (compose s sigma)));                  -(sum_over_perms n (fun s -> g (compose s sigma)));                  -(sum_over_perms n g);                  -(det m) ]
#pop-options
(* ==================================================================== *)
(*  ELEMENTARY MATRICES                                                  *)
(*                                                                      *)
(*  Three flavours, each an n x n matrix:                                *)
(*    E_swap n i j     = identity with rows i, j swapped                 *)
(*    E_scale n i c    = identity with the (i,i) entry replaced by c     *)
(*    E_add n i j c    = identity plus c at off-diagonal slot (i,j)      *)
(*                       (i <> j ; preserves triangularity)              *)
(*                                                                      *)
(*  Their determinants are computed below.  Left-multiplication by an    *)
(*  elementary corresponds to the same operation on the rows of the     *)
(*  multiplicand; right-multiplication, to the operation on columns.     *)
(* ==================================================================== *)
let e_swap_mat (#t: Type) {| h0: has_zero t |} {| h1: has_one t |}               (n: nat) (i j: fin n) : square_matrix t n  = row_swap (id_matrix #t n) i j
let e_scale_mat (#t: Type) {| h0: has_zero t |} {| h1: has_one t |}                (n: nat) (i: fin n) (c: t) : square_matrix t n  = fun a b -> if a = i && b = i then c              else if a = b then one              else zero
let e_add_mat (#t: Type) {| h0: has_zero t |} {| h1: has_one t |} {| ha: has_add t |}              (n: nat) (i j: fin n) (c: t) : square_matrix t n  = fun a b -> if a = b then one              else if a = i && b = j then c              else zero
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"let det_e_swap (#t: Type) {| cr: commutative_ring t |} (n: nat) (i j: fin n)  : Lemma (requires ~(i == j))          (ensures  det (e_swap_mat #t #_ #_ n i j) = -(one #t))  = let r : ring t = cr.ring in    let m0 = id_matrix #t n in    det_row_swap #t #cr #n m0 i j;    assert (det (row_swap m0 i j) = -(det m0));    det_identity #t #r n;    assert (det m0 = one #t);    neg_congruence_lem #t #(add_comm_group_of_ring t r)                       (det m0) (one #t);    assert ((-(det m0)) = (-(one #t)));    assert (det (e_swap_mat #t #_ #_ n i j) == det (row_swap m0 i j));    let lhs = det (e_swap_mat #t #_ #_ n i j) in    reflexivity lhs;    assert (lhs = det (row_swap m0 i j));    trans_lemma [ lhs;                  det (row_swap m0 i j);                  -(det m0);                  -(one #t) ]
#pop-options
(* perm_product is zero whenever one of its factors vanishes. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"let perm_product_has_zero_factor  (#t: Type) {| r: ring t |} (#n: nat)  (m: square_matrix t n) (p: permutation n) (k: fin n)  : Lemma (requires m k (p.fwd k) = zero)          (ensures  perm_product m p = zero)  = let body : nat -> t      = fun (j: nat) ->          if j < n then m (j <: fin n) (p.fwd (j <: fin n)) else one in    let kk : nat = k in    assert (body kk == m k (p.fwd k));    reflexivity (m k (p.fwd k));    let eq : equatable t = TC.solve in    eq.transitivity (body kk) (m k (p.fwd k)) (zero #t);    prod_range_zero_factor #t body 0 n kk;    assert_norm (perm_product m p == prod_range #t body 0 n);    reflexivity (perm_product m p);    eq.transitivity (perm_product m p) (prod_range body 0 n) (zero #t)
#pop-options
(* prod_range with all-ones except at one position equals the value at that   position.  Useful for diagonal-like matrices. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"let prod_range_one_except_at  (#t: Type) {| r: ring t |} (f: nat -> t) (lo hi: nat) (i: nat)  : Lemma (requires lo <= i /\ i < hi /\                    (forall (k: nat). lo <= k /\ k < hi /\ k <> i ==> f k = one))          (ensures  prod_range f lo hi = f i)  = let eq : equatable t = TC.solve in    elim_equatable_laws t #eq;    transitivity_for_calc_proofs t #eq;    let const_one : nat -> t = fun _ -> one in    let aux_left (k: nat) : Lemma (lo <= k /\ k < i ==> f k = const_one k)      = if lo <= k && k < i then begin          assert (f k = one);          reflexivity (one #t)        end    in    let aux_right (k: nat) : Lemma (nat_succ i <= k /\ k < hi ==> f k = const_one k)      = if nat_succ i <= k && k < hi then begin          assert (f k = one);          reflexivity (one #t)        end    in    Classical.forall_intro aux_left;    Classical.forall_intro aux_right;    prod_range_split f lo i hi;    prod_range_unfold_left f i hi;    prod_range_congruence #t f const_one lo i;    prod_range_congruence #t f const_one (nat_succ i) hi;    prod_range_const_one #t #r lo i;    prod_range_const_one #t #r (nat_succ i) hi;    let p_left = prod_range f lo i in    let p_right_tail = prod_range f (nat_succ i) hi in    let p_right = prod_range f i hi in    assert (p_left = prod_range const_one lo i);    assert (prod_range const_one lo i = one);    trans_lemma [ p_left; prod_range const_one lo i; one #t ];    assert (p_left = one);    assert (p_right_tail = prod_range const_one (nat_succ i) hi);    assert (prod_range const_one (nat_succ i) hi = one);    trans_lemma [ p_right_tail; prod_range const_one (nat_succ i) hi; one #t ];    assert (p_right_tail = one);    reflexivity (f i);    mul_congruence (f i) p_right_tail (f i) (one #t);    assert (f i * p_right_tail = f i * one);    right_mul_identity (f i);    assert (f i * one = f i);    prod_range_unfold_left f i hi;    assert (p_right = f i * p_right_tail);    trans_lemma [ p_right; f i * p_right_tail; f i * one; f i ];    assert (p_right = f i);    mul_congruence p_left p_right (one #t) (f i);    assert (p_left * p_right = one * f i);    left_mul_identity (f i);    assert (one * f i = f i);    assert (prod_range f lo hi = p_left * p_right);    trans_lemma [ prod_range f lo hi; p_left * p_right; one * f i; f i ]
#pop-options
(* det (E_scale n i c) = c. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"let det_e_scale (#t: Type) {| cr: commutative_ring t |} (n: nat) (i: fin n) (c: t)  : Lemma (det (e_scale_mat #t #_ #_ n i c) = c)  = let r : ring t = cr.ring in    let eq : equatable t = TC.solve in    elim_equatable_laws t #eq;    transitivity_for_calc_proofs t #eq;    let m = e_scale_mat #t #_ #_ n i c in    let f = leibniz_term #t #r #n m in    let p0 = identity n in    (* leibniz_term respects perm_eq for this matrix.  We replay det_identity-style:       sum over perms collapses to f p0; show f p0 = c. *)    let respects (p q: permutation n) : Lemma (requires perm_eq p q)                                              (ensures f p = f q)      = (* perm_product m p = perm_product m q via congruence on body *)        let body_p : nat -> t          = fun (j: nat) -> if j < n then m (j <: fin n) (p.fwd (j <: fin n)) else one in        let body_q : nat -> t          = fun (j: nat) -> if j < n then m (j <: fin n) (q.fwd (j <: fin n)) else one in        let aux (k: nat) : Lemma (0 <= k /\ k < n ==> body_p k = body_q k)          = if k < n then begin              let kk : fin n = k in              perm_eq_elim p q kk;              reflexivity (body_p k)            end        in        Classical.forall_intro aux;        prod_range_congruence #t body_p body_q 0 n;        assert_norm (perm_product m p == prod_range #t body_p 0 n);        assert_norm (perm_product m q == prod_range #t body_q 0 n);        reflexivity (perm_product m p);        reflexivity (perm_product m q);        eq.transitivity (perm_product m p) (prod_range body_p 0 n) (prod_range body_q 0 n);        eq.transitivity (perm_product m p) (prod_range body_q 0 n) (perm_product m q);        parity_perm_eq_invariant p q;        if parity p then begin          reflexivity (f p);          reflexivity (f q)        end else begin          neg_congruence_lem #t #(add_comm_group_of_ring t r)                             (perm_product m p) (perm_product m q);          reflexivity (f p);          reflexivity (f q)        end    in    Classical.forall_intro_2 (Classical.move_requires_2 respects);    respects_perm_eq_intro f;    (* For non-identity p: m(k, p.fwd k) = 0 for any k with p.fwd k <> k. *)    let vanish (q: permutation n) : Lemma (~(perm_eq p0 q) ==> f q = zero)      = if FStar.IndefiniteDescription.strong_excluded_middle (~(perm_eq p0 q)) then begin          let phi (k: fin n) : prop = ~(q.fwd k == k) in          let helper (assume_not : (k: fin n -> Lemma (~(phi k)))) : Lemma False            = Classical.forall_intro assume_not;              assert (forall (k: fin n). q.fwd k == k);              assert (forall (k: fin n). p0.fwd k == k);              perm_eq_intro p0 q          in          Classical.exists_intro_not_all_not #(fin n) #phi helper;          eliminate exists (k: fin n). phi k            returns f q = zero with _.            begin              (* m(k, q.fwd k) = zero since k <> q.fwd k *)              assert (~(k == q.fwd k));              assert (m k (q.fwd k) == zero #t);              reflexivity (zero #t);              perm_product_has_zero_factor #t #r #n m q k;              let pp = perm_product m q in              if parity q then begin                reflexivity (f q);                eq.transitivity (f q) pp (zero #t)              end else begin                neg_zero_lem #t #(add_comm_group_of_ring t r);                neg_congruence_lem #t #(add_comm_group_of_ring t r) pp (zero #t);                reflexivity (f q);                eq.transitivity (f q) (-pp) ((-(zero #t)));                eq.transitivity (f q) (-(zero #t)) (zero #t)              end            end        end    in    Classical.forall_intro vanish;    sum_over_perms_single n f p0;    parity_identity n;    (* f p0 = perm_product m p0; compute that with prod_range_one_except_at on body(k) = m(k,k). *)    let body : nat -> t      = fun (j: nat) -> if j < n then m (j <: fin n) (p0.fwd (j <: fin n)) else one in    let aux_diag (k: nat) : Lemma (0 <= k /\ k < n /\ k <> (i <: nat) ==> body k = one)      = if k < n && k <> (i <: nat) then begin          let kk : fin n = k in          identity_fwd n kk;          assert (p0.fwd kk == kk);          assert (m kk kk == one #t);          reflexivity (one #t)        end    in    Classical.forall_intro aux_diag;    let aux_at_i : unit -> Lemma (body (i <: nat) = c) = fun () ->      identity_fwd n i;      assert (p0.fwd i == i);      assert (m i i == c);      reflexivity c    in    aux_at_i ();    prod_range_one_except_at #t #r body 0 n (i <: nat);    assert_norm (perm_product m p0 == prod_range #t body 0 n);    reflexivity (perm_product m p0);    eq.transitivity (perm_product m p0) (prod_range body 0 n) (body (i <: nat));    eq.transitivity (perm_product m p0) (body (i <: nat)) c;    assert (parity p0 == true);    assert (f p0 == perm_product m p0);    reflexivity (f p0);    eq.transitivity (f p0) (perm_product m p0) c;    det_unfold m;    reflexivity (det m);    eq.transitivity (det m) (sum_over_perms n f) (f p0);    eq.transitivity (det m) (f p0) c
#pop-options
(* det (E_add n i j c) = one,  i <> j. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 120"let det_e_add (#t: Type) {| cr: commutative_ring t |} (n: nat) (i j: fin n) (c: t)  : Lemma (requires ~(i == j))          (ensures  det (e_add_mat #t #_ #_ #_ n i j c) = one)  = let r : ring t = cr.ring in    let eq : equatable t = TC.solve in    elim_equatable_laws t #eq;    transitivity_for_calc_proofs t #eq;    let m = e_add_mat #t #_ #_ #_ n i j c in    let f = leibniz_term #t #r #n m in    let p0 = identity n in    (* leibniz_term respects perm_eq for m.  Same proof as in det_e_scale. *)    let respects (p q: permutation n) : Lemma (requires perm_eq p q)                                              (ensures f p = f q)      = let body_p : nat -> t          = fun (jj: nat) -> if jj < n then m (jj <: fin n) (p.fwd (jj <: fin n)) else one in        let body_q : nat -> t          = fun (jj: nat) -> if jj < n then m (jj <: fin n) (q.fwd (jj <: fin n)) else one in        let aux (k: nat) : Lemma (0 <= k /\ k < n ==> body_p k = body_q k)          = if k < n then begin              let kk : fin n = k in              perm_eq_elim p q kk;              reflexivity (body_p k)            end        in        Classical.forall_intro aux;        prod_range_congruence #t body_p body_q 0 n;        assert_norm (perm_product m p == prod_range #t body_p 0 n);        assert_norm (perm_product m q == prod_range #t body_q 0 n);        reflexivity (perm_product m p);        reflexivity (perm_product m q);        eq.transitivity (perm_product m p) (prod_range body_p 0 n) (prod_range body_q 0 n);        eq.transitivity (perm_product m p) (prod_range body_q 0 n) (perm_product m q);        parity_perm_eq_invariant p q;        if parity p then begin          reflexivity (f p);          reflexivity (f q)        end else begin          neg_congruence_lem #t #(add_comm_group_of_ring t r)                             (perm_product m p) (perm_product m q);          reflexivity (f p);          reflexivity (f q)        end    in    Classical.forall_intro_2 (Classical.move_requires_2 respects);    respects_perm_eq_intro f;    let vanish (q: permutation n) : Lemma (~(perm_eq p0 q) ==> f q = zero)      = if FStar.IndefiniteDescription.strong_excluded_middle (~(perm_eq p0 q)) then begin          (* Show: exists k:fin n. m k (q.fwd k) = zero. *)          let phi (k: fin n) : prop = m k (q.fwd k) = zero in          let helper (assume_not : (k: fin n -> Lemma (~(phi k)))) : Lemma False            = Classical.forall_intro assume_not;              (* Now: forall k. m k (q.fwd k) <> zero. By cases on the matrix definition,                 that forces forall k. q.fwd k == k OR (k == i AND q.fwd k == j). *)              let cls (k: fin n) : Lemma (q.fwd k == k \/ ((k <: nat) == (i <: nat) /\ q.fwd k == j))                = if (k = q.fwd k) then ()                  else if (k = i && q.fwd k = j) then ()                  else begin                    assert (m k (q.fwd k) == zero #t);                    reflexivity (zero #t);                    assert (~(m k (q.fwd k) = zero));                    ()                  end              in              Classical.forall_intro cls;              (* Apply at j: q.fwd j == j OR (j == i AND q.fwd j == j). Since i <> j, both yield q.fwd j == j. *)              assert (q.fwd j == j \/ ((j <: nat) == (i <: nat) /\ q.fwd j == j));              assert (q.fwd j == j);              (* Apply at i: q.fwd i == i OR (i == i AND q.fwd i == j). *)              assert (q.fwd i == i \/ q.fwd i == j);              (* Case 1: q.fwd i == i. Then forall k <> i, by cls, q.fwd k == k (since k <> i so k = i can't hold).                 So q.fwd k == k for all k, i.e. perm_eq p0 q.  Contradicts ~(perm_eq p0 q). *)              (* Case 2: q.fwd i == j. Combined with q.fwd j == j, injectivity gives i == j. *)              if q.fwd i = j then begin                fwd_injective q i j;                assert (i == j);                ()              end else begin                assert (q.fwd i == i);                let cls2 (k: fin n) : Lemma (q.fwd k == k)                  = if (k <: nat) = (i <: nat) then ()                    else begin                      let _ = cls k in                      assert (q.fwd k == k \/ ((k <: nat) == (i <: nat) /\ q.fwd k == j));                      ()                    end                in                Classical.forall_intro cls2;                assert (forall (k: fin n). q.fwd k == k);                assert (forall (k: fin n). p0.fwd k == k);                perm_eq_intro p0 q;                ()              end          in          Classical.exists_intro_not_all_not #(fin n) #phi helper;          eliminate exists (k: fin n). phi k            returns f q = zero with _.            begin              perm_product_has_zero_factor #t #r #n m q k;              let pp = perm_product m q in              if parity q then begin                reflexivity (f q);                eq.transitivity (f q) pp (zero #t)              end else begin                neg_zero_lem #t #(add_comm_group_of_ring t r);                neg_congruence_lem #t #(add_comm_group_of_ring t r) pp (zero #t);                reflexivity (f q);                eq.transitivity (f q) (-pp) ((-(zero #t)));                eq.transitivity (f q) (-(zero #t)) (zero #t)              end            end        end    in    Classical.forall_intro vanish;    sum_over_perms_single n f p0;    parity_identity n;    (* f p0 = perm_product m p0 = prod_range body 0 n with body k = m(k, k) = one for all k. *)    let body : nat -> t      = fun (jj: nat) -> if jj < n then m (jj <: fin n) (p0.fwd (jj <: fin n)) else one in    let const_one : nat -> t = fun _ -> one in    let aux_one (k: nat) : Lemma (0 <= k /\ k < n ==> body k = const_one k)      = if k < n then begin          let kk : fin n = k in          identity_fwd n kk;          assert (p0.fwd kk == kk);          assert (m kk kk == one #t);          reflexivity (one #t);          reflexivity (body k)        end    in    Classical.forall_intro aux_one;    prod_range_congruence #t body const_one 0 n;    prod_range_const_one #t #r 0 n;    assert_norm (perm_product m p0 == prod_range #t body 0 n);    reflexivity (perm_product m p0);    eq.transitivity (perm_product m p0) (prod_range body 0 n) (prod_range const_one 0 n);    eq.transitivity (perm_product m p0) (prod_range const_one 0 n) (one #t);    assert (parity p0 == true);    assert (f p0 == perm_product m p0);    reflexivity (f p0);    eq.transitivity (f p0) (perm_product m p0) (one #t);    det_unfold m;    reflexivity (det m);    eq.transitivity (det m) (sum_over_perms n f) (f p0);    eq.transitivity (det m) (f p0) (one #t)
#pop-options
(* ==================================================================== *)
(*  Row operations as data                                              *)
(* ==================================================================== *)
(* Multiply row i by scalar c. *)
let row_scale (#t: Type) {| h: has_mul t |} (#n: nat)              (m: square_matrix t n) (i: fin n) (c: t) : square_matrix t n  = fun a b -> if a = i then c * m a b else m a b
(* Add c times row j to row i (i <> j). *)
let row_add (#t: Type) {| sr: semiring t |} (#n: nat)            (m: square_matrix t n) (i j: fin n) (c: t) : square_matrix t n  = fun a b -> if a = i then m a b + c * m j b else m a b
(* ==================================================================== *)
(*  Connection lemmas: left-mult by elementary = row operation          *)
(* ==================================================================== *)
(* A scalar generalization of fin_sum_kronecker:     fin_sum (k. (if i0 = k then scal else zero) * g k) = scal * g i0*)
#push-options "--fuel 4 --ifuel 4 --z3rlimit 120"let fin_sum_scaled_kronecker  (#t: Type) {| sr: semiring t |} (#n: nat)  (i0: fin n) (scal: t) (g: fin n -> t)  : Lemma (fin_sum (fun (k: fin n) ->             (if (i0 <: nat) = (k <: nat) then scal else zero #t) * g k)        = scal * g i0)  = elim_equatable_laws t;    transitivity_for_calc_proofs t;    let pf (k: fin n) : Lemma        ((if (i0 <: nat) = (k <: nat) then scal else zero #t) * g k         = scal * ((if (i0 <: nat) = (k <: nat) then one #t else zero #t) * g k))      = reflexivity scal;        if (i0 <: nat) = (k <: nat) then begin          left_mul_identity (g k);          mul_congruence scal (one #t * g k) scal (g k);          symmetry (scal * (one #t * g k)) (scal * g k);          reflexivity (scal * g k);          (* scal * g k = scal * (one * g k) *)          reflexivity ((if (i0 <: nat) = (k <: nat) then scal else zero #t) * g k)          (* LHS reduces to scal * g k by the true branch *)        end else begin          left_absorption (g k);          mul_congruence scal (zero #t * g k) scal (zero #t);          right_absorption scal;          (* zero * g k = zero; scal * (zero * g k) = scal * zero = zero;             LHS = zero * g k = zero; both sides = zero. *)          reflexivity (zero #t * g k);          symmetry (scal * (zero #t * g k)) (scal * zero #t);          symmetry (scal * zero #t) (zero #t);          transitivity (zero #t * g k) (zero #t) (scal * zero #t);          transitivity (zero #t * g k) (scal * zero #t) (scal * (zero #t * g k))        end    in    Classical.forall_intro pf;    fin_sum_congruence      (fun (k: fin n) ->        (if (i0 <: nat) = (k <: nat) then scal else zero #t) * g k)      (fun (k: fin n) ->        scal * ((if (i0 <: nat) = (k <: nat) then one #t else zero #t) * g k));    fin_sum_mul_left scal      (fun (k: fin n) ->        (if (i0 <: nat) = (k <: nat) then one #t else zero #t) * g k);    fin_sum_kronecker i0 g;    reflexivity scal;    mul_congruence scal      (fin_sum (fun (k: fin n) ->        (if (i0 <: nat) = (k <: nat) then one #t else zero #t) * g k))      scal (g i0);    (* Chain:       fin_sum (body) = fin_sum (scal * kr)  [by congruence]       fin_sum (scal * kr) = scal * fin_sum kr  [by fin_sum_mul_left, symmetric]       scal * fin_sum kr = scal * g i0  [by mul_congruence + kronecker] *)    symmetry      (scal * fin_sum (fun (k: fin n) ->        (if (i0 <: nat) = (k <: nat) then one #t else zero #t) * g k))      (fin_sum (fun (k: fin n) ->        scal * ((if (i0 <: nat) = (k <: nat) then one #t else zero #t) * g k)));    transitivity      (fin_sum (fun (k: fin n) ->        scal * ((if (i0 <: nat) = (k <: nat) then one #t else zero #t) * g k)))      (scal * fin_sum (fun (k: fin n) ->        (if (i0 <: nat) = (k <: nat) then one #t else zero #t) * g k))      (scal * g i0);    transitivity      (fin_sum (fun (k: fin n) ->        (if (i0 <: nat) = (k <: nat) then scal else zero #t) * g k))      (fin_sum (fun (k: fin n) ->        scal * ((if (i0 <: nat) = (k <: nat) then one #t else zero #t) * g k)))      (scal * g i0)
#pop-options
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"let e_swap_left_mul  (#t: Type) {| sr: semiring t |} (#n: nat)  (m: square_matrix t n) (i j: fin n) (a b: fin n)  : Lemma (matrix_mul (e_swap_mat #t n i j) m a b = swap_rows m i j a b)  = elim_equatable_laws t;    let sigma = transposition n i j in    let sa : fin n = sigma.fwd a in    let es = e_swap_mat #t n i j in    let pf (k: fin n) : Lemma        (es a k * m k b         = (if (sa <: nat) = (k <: nat) then one else zero #t) * m k b)      = if (sa <: nat) = (k <: nat) then begin          assert (es a k == one #t);          reflexivity (es a k * m k b)        end else begin          id_matrix_off #t n sa k;          assert (es a k == zero #t);          reflexivity (es a k * m k b)        end    in    Classical.forall_intro pf;    fin_sum_congruence      (fun (k: fin n) -> es a k * m k b)      (fun (k: fin n) ->         (if (sa <: nat) = (k <: nat) then one else zero #t) * m k b);    fin_sum_kronecker sa (fun (k: fin n) -> m k b);    transitivity      (fin_sum (fun (k: fin n) -> es a k * m k b))      (fin_sum (fun (k: fin n) ->         (if (sa <: nat) = (k <: nat) then one else zero #t) * m k b))      (m sa b);    matrix_mul_eq_at es m a b;    assert (swap_rows m i j a b == m sa b);    reflexivity (swap_rows m i j a b)
#pop-options
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"let e_scale_left_mul  (#t: Type) {| sr: semiring t |} (#n: nat)  (m: square_matrix t n) (i: fin n) (c: t) (a b: fin n)  : Lemma (matrix_mul (e_scale_mat #t n i c) m a b = row_scale m i c a b)  = elim_equatable_laws t;    let es = e_scale_mat #t n i c in    if a = i then begin      (* row_scale m i c i b = c * m i b *)      let pf (k: fin n) : Lemma          (es i k * m k b           = (if (i <: nat) = (k <: nat) then c else zero #t) * m k b)        = if (i <: nat) = (k <: nat) then begin            assert (es i k == c);            reflexivity (es i k * m k b)          end else begin            assert (es i k == zero #t);            reflexivity (es i k * m k b)          end      in      Classical.forall_intro pf;      fin_sum_congruence        (fun (k: fin n) -> es i k * m k b)        (fun (k: fin n) ->           (if (i <: nat) = (k <: nat) then c else zero #t) * m k b);      fin_sum_scaled_kronecker i c (fun (k: fin n) -> m k b);      transitivity        (fin_sum (fun (k: fin n) -> es i k * m k b))        (fin_sum (fun (k: fin n) ->           (if (i <: nat) = (k <: nat) then c else zero #t) * m k b))        (c * m i b);      matrix_mul_eq_at es m i b;      assert (row_scale m i c i b == c * m i b);      assert (a == i);      reflexivity (row_scale m i c i b)    end else begin      (* a <> i ⇒ row_scale m i c a b = m a b *)      let pf (k: fin n) : Lemma          (es a k * m k b           = (if (a <: nat) = (k <: nat) then one #t else zero #t) * m k b)        = if (a <: nat) = (k <: nat) then begin            assert (es a k == one #t);            reflexivity (es a k * m k b)          end else begin            assert (es a k == zero #t);            reflexivity (es a k * m k b)          end      in      Classical.forall_intro pf;      fin_sum_congruence        (fun (k: fin n) -> es a k * m k b)        (fun (k: fin n) ->           (if (a <: nat) = (k <: nat) then one #t else zero #t) * m k b);      fin_sum_kronecker a (fun (k: fin n) -> m k b);      transitivity        (fin_sum (fun (k: fin n) -> es a k * m k b))        (fin_sum (fun (k: fin n) ->           (if (a <: nat) = (k <: nat) then one #t else zero #t) * m k b))        (m a b);      matrix_mul_eq_at es m a b;      assert (row_scale m i c a b == m a b);      reflexivity (row_scale m i c a b)    end
#pop-options
#push-options "--fuel 2 --ifuel 2 --z3rlimit 120"let e_add_left_mul  (#t: Type) {| sr: semiring t |} (#n: nat)  (m: square_matrix t n) (i j: fin n) (c: t) (a b: fin n)  : Lemma (requires i <> j)          (ensures matrix_mul (e_add_mat #t n i j c) m a b                   = row_add m i j c a b)  = elim_equatable_laws t;    let es = e_add_mat #t n i j c in    if a = i then begin      (* row_add m i j c i b = m i b + c * m j b *)      let pf (k: fin n) : Lemma          (es i k * m k b           = (if (i <: nat) = (k <: nat) then one else zero #t) * m k b           + (if (j <: nat) = (k <: nat) then c else zero #t) * m k b)        = reflexivity (m k b);          if (i <: nat) = (k <: nat) then begin            (* k = i, so k <> j *)            assert (es i k == one #t);            left_mul_identity (m k b);            left_absorption (m k b);            (* LHS: one * m i b = m i b               RHS: one * m i b + zero * m i b = m i b + zero = m i b *)            right_add_identity (one #t * m k b);            (* (one * m k b) + zero = one * m k b *)            add_congruence              (one #t * m k b) (zero #t * m k b)              (one #t * m k b) (zero #t);            (* one * m k b + zero * m k b = one * m k b + zero *)            symmetry              ((one #t * m k b) + (zero #t * m k b))              ((one #t * m k b) + (zero #t));            transitivity              ((one #t * m k b) + (zero #t))              ((one #t * m k b) + (zero #t * m k b))              ((one #t * m k b) + (zero #t * m k b));            (* err — let me simplify *)            transitivity              (one #t * m k b)              ((one #t * m k b) + (zero #t))              ((one #t * m k b) + (zero #t * m k b));            (* one * m k b = (one * m k b) + (zero * m k b) *)            reflexivity (es i k * m k b);            assert (es i k * m k b == one #t * m k b);            transitivity              (es i k * m k b)              (one #t * m k b)              ((one #t * m k b) + (zero #t * m k b))          end else if (j <: nat) = (k <: nat) then begin            (* k = j, k <> i *)            assert (es i k == c);            left_absorption (m k b);            left_add_identity (c * m k b);            (* zero + c * m k b = c * m k b *)            add_congruence              (zero #t * m k b) (c * m k b)              (zero #t) (c * m k b);            symmetry              ((zero #t * m k b) + (c * m k b))              ((zero #t) + (c * m k b));            transitivity              (c * m k b)              ((zero #t) + (c * m k b))              ((zero #t * m k b) + (c * m k b));            reflexivity (es i k * m k b);            assert (es i k * m k b == c * m k b);            transitivity              (es i k * m k b)              (c * m k b)              ((zero #t * m k b) + (c * m k b))          end else begin            (* k <> i, k <> j *)            assert (es i k == zero #t);            left_absorption (m k b);            (* zero * m k b = zero *)            left_add_identity (zero #t * m k b);            (* zero + zero * m k b = zero * m k b *)            add_congruence              (zero #t * m k b) (zero #t * m k b)              (zero #t)         (zero #t * m k b);            (* zero * m k b + zero * m k b = zero + zero * m k b *)            symmetry              ((zero #t * m k b) + (zero #t * m k b))              ((zero #t) + (zero #t * m k b));            transitivity              (zero #t * m k b)              ((zero #t) + (zero #t * m k b))              ((zero #t * m k b) + (zero #t * m k b));            (* zero * m k b = (zero * m k b) + (zero * m k b) *)            reflexivity (es i k * m k b);            assert (es i k * m k b == zero #t * m k b);            transitivity              (es i k * m k b)              (zero #t * m k b)              ((zero #t * m k b) + (zero #t * m k b))          end      in      Classical.forall_intro pf;      fin_sum_add_ext        (fun (k: fin n) ->           (if (i <: nat) = (k <: nat) then one else zero #t) * m k b)        (fun (k: fin n) ->           (if (j <: nat) = (k <: nat) then c else zero #t) * m k b)        (fun (k: fin n) -> es i k * m k b);      fin_sum_kronecker i (fun (k: fin n) -> m k b);      fin_sum_scaled_kronecker j c (fun (k: fin n) -> m k b);      (* Now: fin_sum (es i k * m k b) = fin_sum f + fin_sum g = m i b + c * m j b *)      add_congruence        (fin_sum (fun (k: fin n) ->           (if (i <: nat) = (k <: nat) then one else zero #t) * m k b))        (fin_sum (fun (k: fin n) ->           (if (j <: nat) = (k <: nat) then c else zero #t) * m k b))        (m i b) (c * m j b);      transitivity        (fin_sum (fun (k: fin n) -> es i k * m k b))        ((fin_sum (fun (k: fin n) ->           (if (i <: nat) = (k <: nat) then one else zero #t) * m k b))         + (fin_sum (fun (k: fin n) ->           (if (j <: nat) = (k <: nat) then c else zero #t) * m k b)))        ((m i b) + (c * m j b));      matrix_mul_eq_at es m i b;      assert (row_add m i j c i b == (m i b) + (c * m j b));      assert (a == i);      reflexivity (row_add m i j c i b)    end else begin      (* a <> i: row_add m i j c a b = m a b *)      let pf (k: fin n) : Lemma          (es a k * m k b           = (if (a <: nat) = (k <: nat) then one #t else zero #t) * m k b)        = if (a <: nat) = (k <: nat) then begin            assert (es a k == one #t);            reflexivity (es a k * m k b)          end else begin            (* a <> k. Also a <> i so the c-clause is dead: es a k = zero *)            assert (es a k == zero #t);            reflexivity (es a k * m k b)          end      in      Classical.forall_intro pf;      fin_sum_congruence        (fun (k: fin n) -> es a k * m k b)        (fun (k: fin n) ->           (if (a <: nat) = (k <: nat) then one #t else zero #t) * m k b);      fin_sum_kronecker a (fun (k: fin n) -> m k b);      transitivity        (fin_sum (fun (k: fin n) -> es a k * m k b))        (fin_sum (fun (k: fin n) ->           (if (a <: nat) = (k <: nat) then one #t else zero #t) * m k b))        (m a b);      matrix_mul_eq_at es m a b;      assert (row_add m i j c a b == m a b);      reflexivity (row_add m i j c a b)    end
#pop-options
(* ==================================================================== *)
(*  Column operations and right-multiplication connection lemmas        *)
(* ==================================================================== *)
let col_swap (#t: Type) (#n: nat)             (m: square_matrix t n) (i j: fin n) : square_matrix t n  = permute_cols m (transposition n i j)
(* Multiply column i by scalar c (scalar applied on the right; equivalent   to c * m a b under commutativity). *)
let col_scale (#t: Type) {| h: has_mul t |} (#n: nat)              (m: square_matrix t n) (i: fin n) (c: t) : square_matrix t n  = fun a b -> if b = i then m a b * c else m a b
(* col_add m i j c: add c times column j to column i (scalar on the right). *)
let col_add (#t: Type) {| sr: semiring t |} (#n: nat)            (m: square_matrix t n) (i j: fin n) (c: t) : square_matrix t n  = fun a b -> if b = i then m a b + m a j * c else m a b
(* Right-side scaled kronecker:     fin_sum (fun k -> g k * (if i0 = k then scal else zero)) = g i0 * scal   Proven by case-splitting the body into a (left) kronecker pattern, then   reusing fin_sum_kronecker. No commutativity required. *)
#push-options "--fuel 4 --ifuel 4 --z3rlimit 120"let fin_sum_kronecker_right_scaled  (#t: Type) {| sr: semiring t |} (#n: nat)  (i0: fin n) (g: fin n -> t) (scal: t)  : Lemma (fin_sum (fun (k: fin n) ->              g k * (if (i0 <: nat) = (k <: nat) then scal else zero #t))        = g i0 * scal)  = elim_equatable_laws t;    transitivity_for_calc_proofs t;    let v : t = g i0 * scal in    let pf (k: fin n) : Lemma        (g k * (if (i0 <: nat) = (k <: nat) then scal else zero #t)         = (if (i0 <: nat) = (k <: nat) then one else zero #t) * v)      = if (i0 <: nat) = (k <: nat) then begin          left_mul_identity v;          symmetry (one #t * v) v;          reflexivity (g k * scal);          assert (g k * scal == v);          transitivity (g k * scal) v (one #t * v)        end else begin          right_absorption (g k);          left_absorption v;          symmetry (zero #t * v) (zero #t);          transitivity (g k * zero #t) (zero #t) (zero #t * v)        end    in    Classical.forall_intro pf;    fin_sum_congruence      (fun (k: fin n) -> g k * (if (i0 <: nat) = (k <: nat) then scal else zero #t))      (fun (k: fin n) -> (if (i0 <: nat) = (k <: nat) then one else zero #t) * v);    fin_sum_kronecker i0 (fun (_: fin n) -> v);    transitivity      (fin_sum (fun (k: fin n) ->         g k * (if (i0 <: nat) = (k <: nat) then scal else zero #t)))      (fin_sum (fun (k: fin n) ->         (if (i0 <: nat) = (k <: nat) then one else zero #t) * v))      v
#pop-options
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"let e_swap_right_mul  (#t: Type) {| sr: semiring t |} (#n: nat)  (m: square_matrix t n) (i j: fin n) (a b: fin n)  : Lemma (matrix_mul m (e_swap_mat #t n i j) a b = col_swap m i j a b)  = elim_equatable_laws t;    let sigma = transposition n i j in    let sb : fin n = sigma.fwd b in    let es = e_swap_mat #t n i j in    let pf (k: fin n) : Lemma        (m a k * es k b         = (if (sb <: nat) = (k <: nat) then one else zero #t) * m a k)      = transposition_self_inverse n i j;        compose_fwd sigma sigma b;        perm_eq_elim (compose sigma sigma) (identity n) b;        identity_fwd n b;        if (sb <: nat) = (k <: nat) then begin          assert (sigma.fwd k == b);          assert (es k b == one #t);          right_mul_identity (m a k);          left_mul_identity (m a k);          symmetry (one * m a k) (m a k);          transitivity (m a k * es k b) (m a k) (one * m a k)        end else begin          compose_fwd sigma sigma k;          perm_eq_elim (compose sigma sigma) (identity n) k;          identity_fwd n k;          assert ((sigma.fwd k <: nat) <> (b <: nat));          id_matrix_off #t n (sigma.fwd k) b;          assert (es k b == zero #t);          right_absorption (m a k);          left_absorption (m a k);          symmetry (zero * m a k) (zero #t);          transitivity (m a k * es k b) (zero #t) (zero * m a k)        end    in    Classical.forall_intro pf;    fin_sum_congruence      (fun (k: fin n) -> m a k * es k b)      (fun (k: fin n) ->         (if (sb <: nat) = (k <: nat) then one else zero #t) * m a k);    fin_sum_kronecker sb (fun (k: fin n) -> m a k);    transitivity      (fin_sum (fun (k: fin n) -> m a k * es k b))      (fin_sum (fun (k: fin n) ->         (if (sb <: nat) = (k <: nat) then one else zero #t) * m a k))      (m a sb);    matrix_mul_eq_at m es a b;    assert (col_swap m i j a b == m a sb);    reflexivity (col_swap m i j a b)
#pop-options
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"let e_scale_right_mul  (#t: Type) {| sr: semiring t |} (#n: nat)  (m: square_matrix t n) (i: fin n) (c: t) (a b: fin n)  : Lemma (matrix_mul m (e_scale_mat #t n i c) a b = col_scale m i c a b)  = elim_equatable_laws t;    let es = e_scale_mat #t n i c in    if b = i then begin      let pf (k: fin n) : Lemma          (m a k * es k i           = m a k * (if (i <: nat) = (k <: nat) then c else zero #t))        = if (i <: nat) = (k <: nat) then begin            assert (es k i == c);            reflexivity (m a k * c)          end else begin            assert (es k i == zero #t);            reflexivity (m a k * zero #t)          end      in      Classical.forall_intro pf;      fin_sum_congruence        (fun (k: fin n) -> m a k * es k i)        (fun (k: fin n) ->           m a k * (if (i <: nat) = (k <: nat) then c else zero #t));      fin_sum_kronecker_right_scaled i (fun (k: fin n) -> m a k) c;      transitivity        (fin_sum (fun (k: fin n) -> m a k * es k i))        (fin_sum (fun (k: fin n) ->           m a k * (if (i <: nat) = (k <: nat) then c else zero #t)))        (m a i * c);      matrix_mul_eq_at m es a i;      assert (col_scale m i c a i == m a i * c);      reflexivity (col_scale m i c a i)    end else begin      let pf (k: fin n) : Lemma          (m a k * es k b           = (if (b <: nat) = (k <: nat) then one else zero #t) * m a k)        = if (b <: nat) = (k <: nat) then begin            assert (es k b == one #t);            right_mul_identity (m a k);            left_mul_identity (m a k);            symmetry (one * m a k) (m a k);            transitivity (m a k * es k b) (m a k) (one * m a k)          end else begin            assert (es k b == zero #t);            right_absorption (m a k);            left_absorption (m a k);            symmetry (zero * m a k) (zero #t);            transitivity (m a k * es k b) (zero #t) (zero * m a k)          end      in      Classical.forall_intro pf;      fin_sum_congruence        (fun (k: fin n) -> m a k * es k b)        (fun (k: fin n) ->           (if (b <: nat) = (k <: nat) then one else zero #t) * m a k);      fin_sum_kronecker b (fun (k: fin n) -> m a k);      transitivity        (fin_sum (fun (k: fin n) -> m a k * es k b))        (fin_sum (fun (k: fin n) ->           (if (b <: nat) = (k <: nat) then one else zero #t) * m a k))        (m a b);      matrix_mul_eq_at m es a b;      assert (col_scale m i c a b == m a b);      reflexivity (col_scale m i c a b)    end
#pop-options
(*  e_add_right_mul:    matrix_mul m (e_add_mat n i j c) = col_add m j i c  i.e., right-multiplication by the (i,j)-add elementary matrix adds c times  column i to column j (note the index swap relative to the row version).*)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 240"let e_add_right_mul  (#t: Type) {| sr: semiring t |} (#n: nat)  (m: square_matrix t n) (i j: fin n) (c: t) (a b: fin n)  : Lemma (requires i <> j)          (ensures matrix_mul m (e_add_mat #t n i j c) a b                   = col_add m j i c a b)  = elim_equatable_laws t;    let es = e_add_mat #t n i j c in    if b = j then begin      (* col_add m j i c a j = m a j + m a i * c *)      let pf (k: fin n) : Lemma          (m a k * es k j           = (if (j <: nat) = (k <: nat) then one else zero #t) * m a k           + m a k * (if (i <: nat) = (k <: nat) then c else zero #t))        = if (j <: nat) = (k <: nat) then begin            assert (es k j == one #t);            right_mul_identity (m a k);            (* m a k * 1 = m a k *)            left_mul_identity (m a k);            symmetry (one * m a k) (m a k);            transitivity (m a k * es k j) (m a k) (one * m a k);            (* now have: m a k * es k j = one * m a k *)            (* need: ... + m a k * 0 = ... *)            right_absorption (m a k);            right_add_identity (one #t * m a k);            (* one * m a k + 0 = one * m a k *)            add_congruence (one #t * m a k) (m a k * zero #t)                           (one #t * m a k) (zero #t);            symmetry ((one #t * m a k) + (m a k * zero #t))                     ((one #t * m a k) + zero #t);            transitivity (one #t * m a k)                         ((one #t * m a k) + zero #t)                         ((one #t * m a k) + (m a k * zero #t));            transitivity (m a k * es k j)                         (one #t * m a k)                         ((one #t * m a k) + (m a k * zero #t))          end else if (i <: nat) = (k <: nat) then begin            assert (es k j == c);            (* m a k * es k j = m a k * c.               RHS = 0 * m a k + m a k * c. *)            reflexivity (m a k * c);            assert (m a k * es k j = m a k * c);            left_absorption (m a k);            (* zero * m a k = zero *)            symmetry (zero #t * m a k) (zero #t);            (* zero = zero * m a k *)            reflexivity (m a k * c);            add_congruence (zero #t) (m a k * c) (zero #t * m a k) (m a k * c);            (* (zero + m a k * c) = (zero * m a k + m a k * c) *)            left_add_identity (m a k * c);            (* zero + m a k * c = m a k * c *)            symmetry ((zero #t) + (m a k * c)) (m a k * c);            (* m a k * c = zero + m a k * c *)            transitivity (m a k * c)                         ((zero #t) + (m a k * c))                         ((zero #t * m a k) + (m a k * c));            transitivity (m a k * es k j) (m a k * c)                         ((zero #t * m a k) + (m a k * c))          end else begin            assert (es k j == zero #t);            right_absorption (m a k);            (* m a k * 0 = 0 *)            assert (m a k * es k j = m a k * zero #t);            left_absorption (m a k);            (* 0 * m a k = 0 *)            left_add_identity (m a k * zero #t);            add_congruence (zero #t) (m a k * zero #t)                           (zero #t * m a k) (m a k * zero #t);            symmetry ((zero #t) + (m a k * zero #t))                     ((zero #t * m a k) + (m a k * zero #t));            transitivity (m a k * zero #t)                         ((zero #t) + (m a k * zero #t))                         ((zero #t * m a k) + (m a k * zero #t));            transitivity (m a k * es k j)                         (m a k * zero #t)                         ((zero #t * m a k) + (m a k * zero #t))          end      in      Classical.forall_intro pf;      fin_sum_add_ext        (fun (k: fin n) ->           (if (j <: nat) = (k <: nat) then one else zero #t) * m a k)        (fun (k: fin n) ->           m a k * (if (i <: nat) = (k <: nat) then c else zero #t))        (fun (k: fin n) -> m a k * es k j);      fin_sum_kronecker j (fun (k: fin n) -> m a k);      fin_sum_kronecker_right_scaled i (fun (k: fin n) -> m a k) c;      add_congruence        (fin_sum (fun (k: fin n) ->           (if (j <: nat) = (k <: nat) then one else zero #t) * m a k))        (fin_sum (fun (k: fin n) ->           m a k * (if (i <: nat) = (k <: nat) then c else zero #t)))        (m a j) (m a i * c);      transitivity        (fin_sum (fun (k: fin n) -> m a k * es k j))        ((fin_sum (fun (k: fin n) ->           (if (j <: nat) = (k <: nat) then one else zero #t) * m a k))         + (fin_sum (fun (k: fin n) ->           m a k * (if (i <: nat) = (k <: nat) then c else zero #t))))        ((m a j) + (m a i * c));      matrix_mul_eq_at m es a j;      assert (col_add m j i c a j == (m a j) + (m a i * c));      reflexivity (col_add m j i c a j)    end else begin      let pf (k: fin n) : Lemma          (m a k * es k b           = (if (b <: nat) = (k <: nat) then one else zero #t) * m a k)        = if (b <: nat) = (k <: nat) then begin            assert (es k b == one #t);            right_mul_identity (m a k);            left_mul_identity (m a k);            symmetry (one * m a k) (m a k);            transitivity (m a k * es k b) (m a k) (one * m a k)          end else begin            (* b <> k. Also b <> j so the c-clause requires k=i AND b=j, dead. *)            assert (es k b == zero #t);            right_absorption (m a k);            left_absorption (m a k);            symmetry (zero * m a k) (zero #t);            transitivity (m a k * es k b) (zero #t) (zero * m a k)          end      in      Classical.forall_intro pf;      fin_sum_congruence        (fun (k: fin n) -> m a k * es k b)        (fun (k: fin n) ->           (if (b <: nat) = (k <: nat) then one else zero #t) * m a k);      fin_sum_kronecker b (fun (k: fin n) -> m a k);      transitivity        (fin_sum (fun (k: fin n) -> m a k * es k b))        (fin_sum (fun (k: fin n) ->           (if (b <: nat) = (k <: nat) then one else zero #t) * m a k))        (m a b);      matrix_mul_eq_at m es a b;      assert (col_add m j i c a b == m a b);      reflexivity (col_add m j i c a b)    end
#pop-options
(* ==================================================================== *)
(*  MULTILINEARITY: det(row_scale m i c) = c * det m                     *)
(* ==================================================================== *)
(* Factor a scalar out of one index of a finite product over a       *)
(* commutative-ring range.  body and body' agree everywhere except    *)
(* at index i, where body' i = c * body i.                            *)
(* Helper: shape lemma for prod_range built from split + unfold_left. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"private let prod_range_shape_at  (#t: Type) {| m: mul_monoid t |}  (f: nat -> t) (lo hi: nat) (i: nat)  : Lemma (requires lo <= i /\ i < hi)          (ensures prod_range f lo hi =                   prod_range f lo i * (f i * prod_range f (nat_succ i) hi))  = elim_equatable_laws t;    transitivity_for_calc_proofs t;    prod_range_split f lo i hi;    prod_range_unfold_left f i hi;    assert (prod_range f i hi == f i * prod_range f (nat_succ i) hi);    reflexivity (prod_range f lo i);    reflexivity (f i * prod_range f (nat_succ i) hi);    mul_congruence (prod_range f lo i) (prod_range f i hi)                   (prod_range f lo i) (f i * prod_range f (nat_succ i) hi);    assert (prod_range f lo i * prod_range f i hi            = prod_range f lo i * (f i * prod_range f (nat_succ i) hi));    assert (prod_range f lo hi            = prod_range f lo i * prod_range f i hi);    trans_lemma [ prod_range f lo hi;                  prod_range f lo i * prod_range f i hi;                  prod_range f lo i * (f i * prod_range f (nat_succ i) hi) ]
#pop-options
#push-options "--fuel 4 --ifuel 2 --z3rlimit 160"let prod_range_extract_scalar_left  (#t: Type) {| cr: commutative_ring t |}  (body body': nat -> t) (lo hi: nat) (i: nat) (c: t)  : Lemma (requires lo <= i /\ i < hi /\                    body' i = c * body i /\                    (forall (k: nat). lo <= k /\ k < hi /\ k <> i ==> body' k = body k))          (ensures prod_range body' lo hi = c * prod_range body lo hi)  = let r : ring t = cr.ring in    let mcm = cr.mul_comm_monoid in    elim_equatable_laws t;    transitivity_for_calc_proofs t;    prod_range_shape_at body  lo hi i;    prod_range_shape_at body' lo hi i;    prod_range_congruence #t body' body lo i;    prod_range_congruence #t body' body (nat_succ i) hi;    let l   = prod_range body lo i in    let r0  = prod_range body (nat_succ i) hi in    let bi  = body i in    let bi' = body' i in    let p   = bi * r0 in    assert (prod_range body' lo i = l);    assert (prod_range body' (nat_succ i) hi = r0);    assert (bi' = c * bi);    assert (prod_range body  lo hi = l * (bi * r0));    assert (prod_range body' lo hi            = prod_range body' lo i * (bi' * prod_range body' (nat_succ i) hi));    (* Bridge prod_range body' lo hi = l * (bi' * r0) using congruence. *)    reflexivity bi';    mul_congruence bi' (prod_range body' (nat_succ i) hi) bi' r0;    assert (bi' * prod_range body' (nat_succ i) hi = bi' * r0);    reflexivity (prod_range body' lo i);    mul_congruence (prod_range body' lo i) (bi' * prod_range body' (nat_succ i) hi)                   l (bi' * r0);    trans_lemma [ prod_range body' lo hi;                  prod_range body' lo i * (bi' * prod_range body' (nat_succ i) hi);                  l * (bi' * r0) ];    assert (prod_range body' lo hi = l * (bi' * r0));    (* Now: l * (bi' * r0) = l * ((c * bi) * r0) = l * (c * (bi * r0)) = l * (c * p). *)    reflexivity r0;    mul_congruence bi' r0 (c * bi) r0;    assert (bi' * r0 = (c * bi) * r0);    mul_associativity c bi r0;    assert ((c * bi) * r0 = c * (bi * r0));    trans_lemma [ bi' * r0; (c * bi) * r0; c * p ];    reflexivity l;    mul_congruence l (bi' * r0) l (c * p);    assert (l * (bi' * r0) = l * (c * p));    (* l * (c * p) = (l * c) * p = (c * l) * p = c * (l * p). *)    mul_associativity l c p;    assert ((l * c) * p = l * (c * p));    symmetry ((l * c) * p) (l * (c * p));    mcm.mul_comm_semigroup.mul_comm_magma.mul_commutativity l c;    reflexivity p;    mul_congruence (l * c) p (c * l) p;    assert ((l * c) * p = (c * l) * p);    mul_associativity c l p;    trans_lemma [ l * (c * p);                  (l * c) * p;                  (c * l) * p;                  c * (l * p) ];    assert (l * (c * p) = c * (l * p));    trans_lemma [ prod_range body' lo hi;                  l * (bi' * r0);                  l * (c * p);                  c * (l * p) ];    assert (prod_range body' lo hi = c * (l * p));    (* c * (l * p) = c * prod_range body lo hi. *)    reflexivity c;    symmetry (prod_range body lo hi) (l * p);    mul_congruence c (l * p) c (prod_range body lo hi);    assert (c * (l * p) = c * prod_range body lo hi);    trans_lemma [ prod_range body' lo hi;                  c * (l * p);                  c * prod_range body lo hi ]
#pop-options
(* perm_product (row_scale m i c) p = c * perm_product m p.            *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"let perm_product_row_scale  (#t: Type) {| cr: commutative_ring t |} (#n: nat)  (m: square_matrix t n) (i: fin n) (c: t) (p: permutation n)  : Lemma (perm_product (row_scale m i c) p = c * perm_product m p)  = let r : ring t = cr.ring in    let body  : nat -> t =      fun (k: nat) -> if k < n then m (k <: fin n) (p.fwd (k <: fin n)) else one in    let body' : nat -> t =      fun (k: nat) ->        if k < n then (row_scale m i c) (k <: fin n) (p.fwd (k <: fin n)) else one in    elim_equatable_laws t;    transitivity_for_calc_proofs t;    (* body' i = c * body i. *)    assert ((row_scale m i c) i (p.fwd i) == c * m i (p.fwd i));    reflexivity (c * m i (p.fwd i));    assert (body' (i <: nat) = c * body (i <: nat));    (* body' k = body k for k <> i in [0,n). *)    let agree_off (k: nat) : Lemma (0 <= k /\ k < n /\ k <> (i <: nat) ==> body' k = body k)      = if k < n && k <> (i <: nat) then begin          let kf : fin n = k in          assert (kf <> i);          assert ((row_scale m i c) kf (p.fwd kf) == m kf (p.fwd kf));          reflexivity (m kf (p.fwd kf))        end    in    Classical.forall_intro agree_off;    prod_range_extract_scalar_left #t #cr body body' 0 n (i <: nat) c;    assert (prod_range body' 0 n = c * prod_range body 0 n);    perm_product_unfold (row_scale m i c) p;    perm_product_unfold m p;    reflexivity (perm_product (row_scale m i c) p);    reflexivity (perm_product m p);    symmetry (perm_product m p) (prod_range body 0 n);    reflexivity c;    mul_congruence c (prod_range body 0 n) c (perm_product m p);    trans_lemma [ perm_product (row_scale m i c) p;                  prod_range body' 0 n;                  c * prod_range body 0 n;                  c * perm_product m p ]
#pop-options
(* leibniz_term (row_scale m i c) p = c * leibniz_term m p.            *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"let leibniz_term_row_scale  (#t: Type) {| cr: commutative_ring t |} (#n: nat)  (m: square_matrix t n) (i: fin n) (c: t) (p: permutation n)  : Lemma (leibniz_term (row_scale m i c) p = c * leibniz_term m p)  = let r : ring t = cr.ring in    let acg : add_comm_group t = add_comm_group_of_ring t r in    elim_equatable_laws t;    transitivity_for_calc_proofs t;    perm_product_row_scale #t #cr #n m i c p;    let pp  = perm_product m p in    let pp' = perm_product (row_scale m i c) p in    assert (pp' = c * pp);    if parity p then begin      (* leibniz_term ... p = pp'; leibniz_term m p = pp;         want pp' = c * pp.  Already have it.                          *)      assert (leibniz_term (row_scale m i c) p == pp');      assert (leibniz_term m p == pp);      reflexivity (c * pp);      assert (leibniz_term (row_scale m i c) p = c * leibniz_term m p)    end else begin      (* leibniz_term ... p = -pp'; leibniz_term m p = -pp;         want: -pp' = c * (-pp).         We have pp' = c * pp.         neg_congruence on pp' = c * pp gives -pp' = -(c * pp).         Then c * (-pp) = -(c * pp) by a left-distributivity argument:           c * pp + c * (-pp) = c * (pp + (-pp)) = c * zero = zero         hence c * (-pp) is the negation of c * pp, i.e. equals -(c*pp). *)      assert (leibniz_term (row_scale m i c) p == -pp');      assert (leibniz_term m p == -pp);      neg_congruence_lem #t #acg pp' (c * pp);      assert ((-pp') = (-(c * pp)));      (* Show c * (-pp) = -(c * pp). *)      acg.add_group.negation pp;      (* pp + (-pp) = zero *)      reflexivity c;      mul_congruence c (pp + (-pp)) c (zero #t);      (* c * (pp + (-pp)) = c * zero *)      left_distributivity c pp (-pp);      (* c * (pp + (-pp)) = c * pp + c * (-pp) *)      right_absorption c;      (* c * zero = zero *)      symmetry (c * (zero #t)) (zero #t);      trans_lemma [ c * pp + c * (-pp);                    c * (pp + (-pp));                    c * (zero #t);                    zero #t ];      symmetry (c * pp + c * (-pp)) (zero #t);      assert (zero #t = c * pp + c * (-pp));      (* By uniqueness of negation in an additive group:         x + y = zero ⟹ y = -x. *)      let lhs_x = c * pp in      let lhs_y = c * (-pp) in      assert (lhs_x + lhs_y = zero #t);      (* Use neg_unique-style: add -(c*pp) on the left. *)      reflexivity (-(c * pp));      add_congruence (-(c * pp)) (lhs_x + lhs_y) (-(c * pp)) (zero #t);      (* -(c*pp) + (lhs_x + lhs_y) = -(c*pp) + zero *)      acg.add_comm_monoid.add_comm_semigroup.add_semigroup.associativity        (-(c * pp)) lhs_x lhs_y;      symmetry ((-(c * pp)) + lhs_x + lhs_y) ((-(c * pp)) + (lhs_x + lhs_y));      acg.add_group.negation (c * pp);      (* -(c*pp) + (c*pp) = zero *)      reflexivity lhs_y;      add_congruence ((-(c * pp)) + lhs_x) lhs_y (zero #t) lhs_y;      assert (((-(c * pp)) + lhs_x) + lhs_y = (zero #t) + lhs_y);      left_add_identity lhs_y;      assert ((zero #t) + lhs_y = lhs_y);      transitivity (((-(c * pp)) + lhs_x) + lhs_y) ((zero #t) + lhs_y) lhs_y;      assert (((-(c * pp)) + lhs_x) + lhs_y = lhs_y);      right_add_identity (-(c * pp));      assert ((-(c * pp)) + (zero #t) = -(c * pp));      symmetry ((-(c * pp)) + (zero #t)) (-(c * pp));      symmetry ((-(c * pp)) + (lhs_x + lhs_y)) ((-(c * pp)) + (zero #t));      transitivity (-(c * pp)) ((-(c * pp)) + (zero #t))                   ((-(c * pp)) + (lhs_x + lhs_y));      assert (-(c * pp) = (-(c * pp)) + (lhs_x + lhs_y));      assert ((-(c * pp)) + (lhs_x + lhs_y) = ((-(c * pp)) + lhs_x) + lhs_y);      transitivity (-(c * pp)) ((-(c * pp)) + (lhs_x + lhs_y))                   (((-(c * pp)) + lhs_x) + lhs_y);      transitivity (-(c * pp)) (((-(c * pp)) + lhs_x) + lhs_y) lhs_y;      assert (-(c * pp) = lhs_y);      symmetry (-(c * pp)) lhs_y;      trans_lemma [ (-pp'); (-(c * pp)); lhs_y ];      assert ((-pp') = c * (-pp));      assert (leibniz_term (row_scale m i c) p = c * leibniz_term m p)    end
#pop-options
(* det(row_scale m i c) = c * det m. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"let det_row_scale  (#t: Type) {| cr: commutative_ring t |} (#n: nat)  (m: square_matrix t n) (i: fin n) (c: t)  : Lemma (det (row_scale m i c) = c * det m)  = let r : ring t = cr.ring in    let sr : semiring t = r.semiring in    elim_equatable_laws t;    transitivity_for_calc_proofs t;    let f = leibniz_term (row_scale m i c) in    let g = leibniz_term m in    let pointwise (s: permutation n) : Lemma (f s = c * g s)      = leibniz_term_row_scale #t #cr #n m i c s in    Classical.forall_intro pointwise;    sum_over_perms_congruence n f (fun s -> c * g s);    (* sum_over_perms n f = sum_over_perms n (fun s -> c * g s) *)    sum_over_perms_mul_left #t #sr n c g;    (* c * sum_over_perms n g = sum_over_perms n (fun s -> c * g s) *)    symmetry (c * sum_over_perms n g) (sum_over_perms n (fun s -> c * g s));    det_unfold (row_scale m i c);    det_unfold m;    reflexivity (sum_over_perms n f);    reflexivity (sum_over_perms n g);    reflexivity c;    mul_congruence c (sum_over_perms n g) c (det m);    trans_lemma [ det (row_scale m i c);                  sum_over_perms n f;                  sum_over_perms n (fun s -> c * g s);                  c * sum_over_perms n g;                  c * det m ]
#pop-options
(* ==================================================================== *)
(*  ALTERNATING: det m = 0 when two rows of m are equal                  *)
(* ==================================================================== *)
(* perm_product depends only on the pointwise values of m, so two        *)
(* matrices that agree pointwise have equal perm_product for every p.    *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"let perm_product_pointwise_eq  (#t: Type) {| r: ring t |} (#n: nat)  (m1 m2: square_matrix t n) (p: permutation n)  : Lemma (requires forall (a b: fin n). m1 a b = m2 a b)          (ensures  perm_product m1 p = perm_product m2 p)  = let body1 : nat -> t =      fun (k: nat) -> if k < n then m1 (k <: fin n) (p.fwd (k <: fin n)) else one in    let body2 : nat -> t =      fun (k: nat) -> if k < n then m2 (k <: fin n) (p.fwd (k <: fin n)) else one in    elim_equatable_laws t;    let pw (k: nat) : Lemma (0 <= k /\ k < n ==> body1 k = body2 k)      = if k < n then begin          let kf : fin n = k in          assert (m1 kf (p.fwd kf) = m2 kf (p.fwd kf));          ()        end    in    Classical.forall_intro pw;    prod_range_congruence #t body1 body2 0 n;    perm_product_unfold m1 p;    perm_product_unfold m2 p
#pop-options
(* leibniz_term is then also stable under pointwise equality.            *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"let leibniz_term_pointwise_eq  (#t: Type) {| r: ring t |} (#n: nat)  (m1 m2: square_matrix t n) (p: permutation n)  : Lemma (requires forall (a b: fin n). m1 a b = m2 a b)          (ensures  leibniz_term m1 p = leibniz_term m2 p)  = let acg : add_comm_group t = add_comm_group_of_ring t r in    elim_equatable_laws t;    perm_product_pointwise_eq #t #r #n m1 m2 p;    if parity p    then ()    else neg_congruence_lem #t #acg (perm_product m1 p) (perm_product m2 p)
#pop-options
(* Pointwise-equal matrices have equal determinants.                     *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"let det_pointwise_eq  (#t: Type) {| r: ring t |} (#n: nat) (m1 m2: square_matrix t n)  : Lemma (requires forall (a b: fin n). m1 a b = m2 a b)          (ensures  det m1 = det m2)  = let pw (p: permutation n) : Lemma (leibniz_term m1 p = leibniz_term m2 p)      = leibniz_term_pointwise_eq #t #r #n m1 m2 p in    Classical.forall_intro pw;    sum_over_perms_congruence n (leibniz_term m1) (leibniz_term m2)
#pop-options
(* If rows i and j of m are equal, swapping them yields a pointwise-     *)
(* equal matrix.                                                         *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let row_swap_equal_rows_pointwise
  (#t: Type) {| equatable t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires forall (k: fin n). m i k = m j k)
          (ensures  forall (a b: fin n). row_swap m i j a b = m a b)
  = let aux (a b: fin n) : Lemma (row_swap m i j a b = m a b)
      = if a = i then begin
          transposition_fwd_left n i j;
          assert (row_swap m i j a b == m j b);
          assert (m i b = m j b);
          symmetry (m i b) (m j b);
          reflexivity (row_swap m i j a b);
          transitivity (row_swap m i j a b) (m j b) (m i b)
        end
        else if a = j then begin
          transposition_fwd_right n i j;
          assert (row_swap m i j a b == m i b);
          assert (m i b = m j b);
          reflexivity (row_swap m i j a b);
          transitivity (row_swap m i j a b) (m i b) (m j b)
        end
        else begin
          transposition_fwd_other n i j a;
          assert (row_swap m i j a b == m a b);
          reflexivity (m a b)
        end
    in
    Classical.forall_intro_2 aux
#pop-options
(* Strengthened alternating result over a general commutative ring (no       *)
(* char≠2 / integral domain needed). Uses the τ-orbit pair-cancellation     *)
(* lemma sum_over_perms_pair_cancel.                                         *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let det_two_equal_rows_cr
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires ~(i == j) /\
                    (forall (k: fin n). m i k = m j k))
          (ensures  det m = zero)
  = let r : ring t = cr.ring in
    let acg : add_comm_group t = r.add_comm_group in
    let tau = transposition n i j in
    let f : permutation n -> t = leibniz_term m in
    elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    (* respects_perm_eq f. *)
    leibniz_term_respects_perm_eq #t #r #n m;
    (* tau ∘ tau ≡ identity (right inverse of transposition is itself). *)
    transposition_self_inverse n i j;
    (* tau ≠ identity (parity differs when i ≠ j). *)
    let tau_ne_id_aux ()
      : Lemma (requires perm_eq tau (identity n)) (ensures False)
      = parity_perm_eq_invariant tau (identity n);
        parity_transposition n i j;
        parity_identity n
    in
    Classical.move_requires tau_ne_id_aux ();
    assert (~(perm_eq tau (identity n)));
    (* row_swap m i j is pointwise equal to m (rows i,j equal). *)
    row_swap_equal_rows_pointwise #t #_ #n m i j;
    (* Pair-cancellation: f s + f (compose s tau) = zero for every s. *)
    let pair_zero (s: permutation n)
      : Lemma (f s + f (compose s tau) = zero)
      = let a = f s in
        let b = f (compose s tau) in
        (* leibniz_term (row_swap m i j) s = -(leibniz_term m (compose s tau)) = -b. *)
        leibniz_term_row_swap #t #cr #n m i j s;
        assert (leibniz_term (row_swap m i j) s = -b);
        (* leibniz_term (row_swap m i j) s = leibniz_term m s = a. *)
        leibniz_term_pointwise_eq #t #r #n (row_swap m i j) m s;
        assert (leibniz_term (row_swap m i j) s = a);
        symmetry (leibniz_term (row_swap m i j) s) a;
        transitivity a (leibniz_term (row_swap m i j) s) (-b);
        assert (a = -b);
        reflexivity b;
        add_congruence a b (-b) b;
        assert (a + b = -b + b);
        acg.add_group.negation b;
        assert (-b + b = zero);
        transitivity (a + b) (-b + b) (zero #t)
    in
    Classical.forall_intro pair_zero;
    (* Apply the τ-orbit pair-cancel lemma. *)
    sum_over_perms_pair_cancel #t #acg n f tau;
    (* Connect back to det m. *)
    det_unfold m;
    reflexivity (det m);
    transitivity (det m) (sum_over_perms n f) (zero #t)
#pop-options

(* Headline alternating result: in an integral domain where one+one is   *)
(* non-zero, det m = zero whenever two distinct rows of m are equal.     *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 120"let det_two_equal_rows  (#t: Type) {| id: integral_domain t |} (#n: nat)  (m: square_matrix t n) (i j: fin n)  : Lemma (requires ~(i == j) /\                    (forall (k: fin n). m i k = m j k) /\                    (one + one) <> zero #t)          (ensures  det m = zero)  = let cr : commutative_ring t = id.commutative_ring in    let r : ring t = cr.ring in    let d : domain t = id.domain in    elim_equatable_laws t;    transitivity_for_calc_proofs t;    (* row_swap m i j is pointwise equal to m. *)    row_swap_equal_rows_pointwise #t #_ #n m i j;    (* det (row_swap m i j) = det m. *)    det_pointwise_eq #t #r #n (row_swap m i j) m;    (* det (row_swap m i j) = -(det m). *)    det_row_swap #t #cr #n m i j;    (* Hence det m = -(det m). *)    symmetry (det (row_swap m i j)) (det m);    transitivity (det m) (det (row_swap m i j)) (-(det m));    let d0 = det m in    assert (d0 = -d0);    (* (one + one) * d0 = d0 + d0 = d0 + (-d0) = zero. *)    right_distributivity (one #t) (one #t) d0;    assert ((one + one) * d0 = one * d0 + one * d0);    left_mul_identity d0;    assert (one * d0 = d0);    add_congruence (one * d0) (one * d0) d0 d0;    assert (one * d0 + one * d0 = d0 + d0);    transitivity ((one + one) * d0) (one * d0 + one * d0) (d0 + d0);    reflexivity d0;    add_congruence d0 d0 d0 (-d0);    assert (d0 + d0 = d0 + (-d0));    r.add_comm_group.add_group.negation d0;    assert (d0 + (-d0) = zero);    transitivity (d0 + d0) (d0 + (-d0)) (zero #t);    transitivity ((one + one) * d0) (d0 + d0) (zero #t);    assert ((one + one) * d0 = zero);    d.domain_law (one + one) d0;    (* (one+one) = zero \/ d0 = zero; the former is excluded. *)    assert (d0 = zero)
#pop-options
(* ==================================================================== *)
(*  ROW-REPLACE helper                                                   *)
(*  row_replace m i u : matrix with row i replaced by the function u.    *)
(* ==================================================================== *)
let row_replace (#t: Type) (#n: nat)                (m: square_matrix t n) (i: fin n) (u: fin n -> t)              : square_matrix t n  = fun a b -> if a = i then u b else m a b

#push-options "--fuel 4 --ifuel 2 --z3rlimit 200"
private let prod_range_extract_add_left
  (#t: Type) {| cr: commutative_ring t |}
  (b ba br: nat -> t) (lo hi: nat) (i: nat) (c: t)
  : Lemma (requires lo <= i /\ i < hi /\
                    ba i = b i + c * br i /\
                    (forall (k: nat). lo <= k /\ k < hi /\ k <> i ==> ba k = b k) /\
                    (forall (k: nat). lo <= k /\ k < hi /\ k <> i ==> br k = b k))
          (ensures prod_range ba lo hi = prod_range b lo hi + c * prod_range br lo hi)
  = let r : ring t = cr.ring in
    let mcm = cr.mul_comm_monoid in
    elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    prod_range_shape_at b  lo hi i;
    prod_range_shape_at ba lo hi i;
    prod_range_shape_at br lo hi i;
    prod_range_congruence #t ba b lo i;
    prod_range_congruence #t ba b (nat_succ i) hi;
    prod_range_congruence #t br b lo i;
    prod_range_congruence #t br b (nat_succ i) hi;
    let l = prod_range b lo i in
    let rr = prod_range b (nat_succ i) hi in
    let u = b i in
    let v = br i in
    let bai = ba i in
    assert (bai = u + c * v);
    (* prod_range ba lo hi = l * (bai * rr) *)
    reflexivity bai;
    mul_congruence bai (prod_range ba (nat_succ i) hi) bai rr;
    mul_congruence (prod_range ba lo i) (bai * prod_range ba (nat_succ i) hi) l (bai * rr);
    assert (prod_range ba lo hi = l * (bai * rr));
    (* prod_range b lo hi = l * (u * rr) *)
    reflexivity u;
    mul_congruence u (prod_range b (nat_succ i) hi) u rr;
    reflexivity l;
    mul_congruence (prod_range b lo i) (u * prod_range b (nat_succ i) hi) l (u * rr);
    assert (prod_range b lo hi = l * (u * rr));
    (* prod_range br lo hi = l * (v * rr) *)
    reflexivity v;
    mul_congruence v (prod_range br (nat_succ i) hi) v rr;
    mul_congruence (prod_range br lo i) (v * prod_range br (nat_succ i) hi) l (v * rr);
    assert (prod_range br lo hi = l * (v * rr));
    (* l * (bai * rr) = l * ((u + c*v) * rr) *)
    reflexivity rr;
    mul_congruence bai rr (u + c * v) rr;
    reflexivity l;
    mul_congruence l (bai * rr) l ((u + c * v) * rr);
    assert (l * (bai * rr) = l * ((u + c * v) * rr));
    (* (u + c*v) * rr = u * rr + (c*v) * rr *)
    right_distributivity u (c * v) rr;
    mul_congruence l ((u + c * v) * rr) l (u * rr + (c * v) * rr);
    assert (l * ((u + c * v) * rr) = l * (u * rr + (c * v) * rr));
    (* l * (u*rr + (c*v)*rr) = l*(u*rr) + l*((c*v)*rr) *)
    left_distributivity l (u * rr) ((c * v) * rr);
    assert (l * (u * rr + (c * v) * rr) = l * (u * rr) + l * ((c * v) * rr));
    (* l * ((c*v) * rr) = c * (l * (v * rr)) using comm/assoc *)
    mul_associativity c v rr;
    assert ((c * v) * rr = c * (v * rr));
    mul_congruence l ((c * v) * rr) l (c * (v * rr));
    assert (l * ((c * v) * rr) = l * (c * (v * rr)));
    let p1 = v * rr in
    mul_associativity l c p1;
    symmetry ((l * c) * p1) (l * (c * p1));
    mcm.mul_comm_semigroup.mul_comm_magma.mul_commutativity l c;
    reflexivity p1;
    mul_congruence (l * c) p1 (c * l) p1;
    mul_associativity c l p1;
    trans_lemma [ l * (c * p1); (l * c) * p1; (c * l) * p1; c * (l * p1) ];
    assert (l * (c * (v * rr)) = c * (l * (v * rr)));
    transitivity (l * ((c * v) * rr)) (l * (c * (v * rr))) (c * (l * (v * rr)));
    (* Connect l*(u*rr) = prod_range b lo hi, c*(l*(v*rr)) = c * prod_range br lo hi *)
    symmetry (prod_range b lo hi) (l * (u * rr));
    symmetry (prod_range br lo hi) (l * (v * rr));
    reflexivity c;
    mul_congruence c (l * (v * rr)) c (prod_range br lo hi);
    transitivity (l * ((c * v) * rr)) (c * (l * (v * rr))) (c * prod_range br lo hi);
    add_congruence (l * (u * rr)) (l * ((c * v) * rr))
                   (prod_range b lo hi) (c * prod_range br lo hi);
    assert (l * (u * rr) + l * ((c * v) * rr) = prod_range b lo hi + c * prod_range br lo hi);
    (* Final chain via explicit transitivity steps *)
    transitivity (prod_range ba lo hi) (l * (bai * rr)) (l * ((u + c * v) * rr));
    transitivity (prod_range ba lo hi) (l * ((u + c * v) * rr)) (l * (u * rr + (c * v) * rr));
    transitivity (prod_range ba lo hi) (l * (u * rr + (c * v) * rr)) (l * (u * rr) + l * ((c * v) * rr));
    transitivity (prod_range ba lo hi) (l * (u * rr) + l * ((c * v) * rr))
                 (prod_range b lo hi + c * prod_range br lo hi)
#pop-options

(* ==================================================================== *)
(*  ALTERNATING (additive form):                                         *)
(*  det (row_add m i j c) = det m                                        *)
(* ==================================================================== *)
(* perm_product (row_add m i j c) p splits additively:                   *)
(*    = perm_product m p + c * perm_product (row_replace m i (m j)) p    *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 120"
let perm_product_row_add_split
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n) (c: t) (p: permutation n)
  : Lemma (requires ~(i == j))
          (ensures  perm_product (row_add m i j c) p
                  = perm_product m p
                  + c * perm_product (row_replace m i (m j)) p)
  = let r : ring t = cr.ring in
    elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    let body  : nat -> t =
      fun (k: nat) -> if k < n then m (k <: fin n) (p.fwd (k <: fin n)) else one in
    let body_add : nat -> t =
      fun (k: nat) ->
        if k < n then (row_add m i j c) (k <: fin n) (p.fwd (k <: fin n)) else one in
    let body_repl : nat -> t =
      fun (k: nat) ->
        if k < n then (row_replace m i (m j)) (k <: fin n) (p.fwd (k <: fin n)) else one in
    let in_ : nat = i in
    (* body_add k = body k for k <> i in [0,n) *)
    let agree_add (k: nat) : Lemma (0 <= k /\ k < n /\ k <> in_ ==> body_add k = body k)
      = if k < n && k <> in_ then begin
          let kf : fin n = k in
          assert (kf <> i);
          reflexivity (m kf (p.fwd kf))
        end
    in
    Classical.forall_intro agree_add;
    (* body_repl k = body k for k <> i in [0,n) *)
    let agree_repl (k: nat) : Lemma (0 <= k /\ k < n /\ k <> in_ ==> body_repl k = body k)
      = if k < n && k <> in_ then begin
          let kf : fin n = k in
          assert (kf <> i);
          reflexivity (m kf (p.fwd kf))
        end
    in
    Classical.forall_intro agree_repl;
    (* body_add i = body i + c * body_repl i *)
    let u = m i (p.fwd i) in
    let v = m j (p.fwd i) in
    assert (body_add in_ == u + c * v);
    assert (body in_ == u);
    assert (body_repl in_ == v);
    reflexivity v;
    reflexivity c;
    mul_congruence c v c (body_repl in_);
    reflexivity u;
    add_congruence u (c * v) (body in_) (c * body_repl in_);
    assert (body_add in_ = body in_ + c * body_repl in_);
    (* Apply the helper *)
    prod_range_extract_add_left #t #cr body body_add body_repl 0 n in_ c;
    assert (prod_range body_add 0 n
            = prod_range body 0 n + c * prod_range body_repl 0 n);
    (* Bridge prod_range body{,_add,_repl} 0 n <-> perm_product. *)
    perm_product_unfold (row_add m i j c) p;
    perm_product_unfold m p;
    perm_product_unfold (row_replace m i (m j)) p;
    reflexivity (perm_product m p);
    reflexivity (perm_product (row_replace m i (m j)) p);
    symmetry (perm_product m p) (prod_range body 0 n);
    symmetry (perm_product (row_replace m i (m j)) p) (prod_range body_repl 0 n);
    reflexivity c;
    mul_congruence c (prod_range body_repl 0 n) c (perm_product (row_replace m i (m j)) p);
    add_congruence (prod_range body 0 n) (c * prod_range body_repl 0 n)
                   (perm_product m p) (c * perm_product (row_replace m i (m j)) p);
    trans_lemma [ perm_product (row_add m i j c) p;
                  prod_range body_add 0 n;
                  prod_range body 0 n + c * prod_range body_repl 0 n;
                  perm_product m p + c * perm_product (row_replace m i (m j)) p ]
#pop-options
(* leibniz_term version of the same split.                               *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 120"let leibniz_term_row_add_split  (#t: Type) {| cr: commutative_ring t |} (#n: nat)  (m: square_matrix t n) (i j: fin n) (c: t) (p: permutation n)  : Lemma (requires ~(i == j))          (ensures  leibniz_term (row_add m i j c) p                  = leibniz_term m p                  + c * leibniz_term (row_replace m i (m j)) p)  = let r : ring t = cr.ring in    let acg : add_comm_group t = add_comm_group_of_ring t r in    elim_equatable_laws t;    transitivity_for_calc_proofs t;    perm_product_row_add_split #t #cr #n m i j c p;    let pp_ra = perm_product (row_add m i j c) p in    let pp_m  = perm_product m p in    let pp_r  = perm_product (row_replace m i (m j)) p in    assert (pp_ra = pp_m + c * pp_r);    if parity p    then begin      (* leibniz are perm_products directly. *)      assert (leibniz_term (row_add m i j c) p == pp_ra);      assert (leibniz_term m p == pp_m);      assert (leibniz_term (row_replace m i (m j)) p == pp_r);      reflexivity pp_ra;      reflexivity (pp_m + c * pp_r);      ()    end    else begin      (* leibniz are negations of perm_products. *)      (* lhs = -pp_ra = -(pp_m + c*pp_r) = -pp_m + -(c*pp_r) = -pp_m + c*(-pp_r) *)      neg_congruence_lem #t #acg pp_ra (pp_m + c * pp_r);      assert ((-pp_ra) = -(pp_m + c * pp_r));      neg_of_sum #t #(acg.add_group) pp_m (c * pp_r);      assert (-(pp_m + c * pp_r) = -(c * pp_r) + (-pp_m));      let acm = acg.add_comm_monoid.add_comm_semigroup.add_comm_magma in      acm.add_commutativity (-(c * pp_r)) (-pp_m);      assert (-(c * pp_r) + (-pp_m) = (-pp_m) + -(c * pp_r));      (* -(c * pp_r) = c * (-pp_r). *)      ring_neg_xy_is_x_times_neg_y #t #r c pp_r;      assert (-(c * pp_r) = c * (-pp_r));      reflexivity (-pp_m);      add_congruence (-pp_m) (-(c * pp_r)) (-pp_m) (c * (-pp_r));      assert ((-pp_m) + -(c * pp_r) = (-pp_m) + c * (-pp_r));      trans_lemma [ -pp_ra;                    -(pp_m + c * pp_r);                    -(c * pp_r) + (-pp_m);                    (-pp_m) + -(c * pp_r);                    (-pp_m) + c * (-pp_r) ];      assert (leibniz_term (row_add m i j c) p == -pp_ra);      assert (leibniz_term m p == -pp_m);      assert (leibniz_term (row_replace m i (m j)) p == -pp_r);      reflexivity (-pp_ra);      reflexivity ((-pp_m) + c * (-pp_r));      ()    end
#pop-options
(* row_replace m i (m j) has rows i and j both equal to m j.             *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"let row_replace_with_other_row_has_equal_rows  (#t: Type) {| equatable t |} (#n: nat)  (m: square_matrix t n) (i j: fin n)  : Lemma (requires ~(i == j))          (ensures  forall (k: fin n).                      (row_replace m i (m j)) i k = (row_replace m i (m j)) j k)  = let aux (k: fin n)      : Lemma ((row_replace m i (m j)) i k = (row_replace m i (m j)) j k)      = assert ((row_replace m i (m j)) i k == m j k);        assert ((row_replace m i (m j)) j k == m j k);        reflexivity (m j k)    in    Classical.forall_intro aux
#pop-options
(* Headline: det (row_add m i j c) = det m, in an integral domain where  *)
(* one+one is non-zero.                                                  *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 120"let det_row_add  (#t: Type) {| id: integral_domain t |} (#n: nat)  (m: square_matrix t n) (i j: fin n) (c: t)  : Lemma (requires ~(i == j) /\ (one + one) <> zero #t)          (ensures  det (row_add m i j c) = det m)  = let cr : commutative_ring t = id.commutative_ring in    let r : ring t = cr.ring in    let sr : semiring t = r.semiring in    elim_equatable_laws t;    transitivity_for_calc_proofs t;    let f = leibniz_term (row_add m i j c) in    let g = leibniz_term m in    let h = leibniz_term (row_replace m i (m j)) in    let pw (p: permutation n) : Lemma (f p = g p + c * h p)      = leibniz_term_row_add_split #t #cr #n m i j c p in    Classical.forall_intro pw;    let ch : permutation n -> t = fun p -> c * h p in    sum_over_perms_add_named n f g ch;    assert (sum_over_perms n f = sum_over_perms n g + sum_over_perms n ch);    sum_over_perms_mul_left #t #sr n c h;    (* sum n (fun p -> c * h p) = c * sum n h. *)    symmetry (c * sum_over_perms n h) (sum_over_perms n ch);    reflexivity (sum_over_perms n g);    add_congruence (sum_over_perms n g) (sum_over_perms n ch)                   (sum_over_perms n g) (c * sum_over_perms n h);    det_unfold (row_add m i j c);    det_unfold m;    det_unfold (row_replace m i (m j));    (* det (row_replace m i (m j)) = zero by alternating. *)    row_replace_with_other_row_has_equal_rows #t #_ #n m i j;    det_two_equal_rows #t #id #n (row_replace m i (m j)) i j;    assert (det (row_replace m i (m j)) = zero);    reflexivity (sum_over_perms n h);    symmetry (det (row_replace m i (m j))) (sum_over_perms n h);    transitivity (sum_over_perms n h) (det (row_replace m i (m j))) (zero #t);    assert (sum_over_perms n h = zero);    reflexivity c;    mul_congruence c (sum_over_perms n h) c (zero #t);    right_absorption c;    assert (c * zero = zero);    transitivity (c * sum_over_perms n h) (c * zero #t) (zero #t);    assert (c * sum_over_perms n h = zero);    reflexivity (sum_over_perms n g);    add_congruence (sum_over_perms n g) (c * sum_over_perms n h)                   (sum_over_perms n g) (zero #t);    right_add_identity (sum_over_perms n g);    assert (sum_over_perms n g + zero = sum_over_perms n g);    transitivity (sum_over_perms n g + c * sum_over_perms n h)                 (sum_over_perms n g + zero)                 (sum_over_perms n g);    (* Now chain. *)    reflexivity (sum_over_perms n f);    reflexivity (sum_over_perms n g);    symmetry (det m) (sum_over_perms n g);    transitivity (det (row_add m i j c)) (sum_over_perms n f) (sum_over_perms n g + sum_over_perms n ch);    transitivity (det (row_add m i j c)) (sum_over_perms n g + sum_over_perms n ch) (sum_over_perms n g + c * sum_over_perms n h);    transitivity (det (row_add m i j c)) (sum_over_perms n g + c * sum_over_perms n h) (sum_over_perms n g);    transitivity (det (row_add m i j c)) (sum_over_perms n g) (det m)
#pop-options

(* ============================================================== *)
(* Column determinant lemmas, derived via transpose.               *)
(* ============================================================== *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let transpose_col_swap_pointwise (#t: Type) (#n: nat) (m: square_matrix t n) (i j: fin n) (a b: fin n) : Lemma (transpose (col_swap m i j) a b == row_swap (transpose m) i j a b) = ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let det_col_swap (#t: Type) {| cr: commutative_ring t |} (#n: nat) (m: square_matrix t n) (i j: fin n) : Lemma (requires ~(i == j)) (ensures det (col_swap m i j) = -(det m)) = let r : ring t = cr.ring in elim_equatable_laws t; transitivity_for_calc_proofs t; let pw (a b: fin n) : Lemma (transpose (col_swap m i j) a b = row_swap (transpose m) i j a b) = transpose_col_swap_pointwise #t #n m i j a b; reflexivity (transpose (col_swap m i j) a b) in Classical.forall_intro_2 pw; det_pointwise_eq #t #r #n (transpose (col_swap m i j)) (row_swap (transpose m) i j); det_transpose #t #cr #n (col_swap m i j); det_row_swap #t #cr #n (transpose m) i j; det_transpose #t #cr #n m; neg_congruence_lem #t #(r.add_comm_group) (det (transpose m)) (det m); symmetry (det (transpose (col_swap m i j))) (det (col_swap m i j)); transitivity (det (col_swap m i j)) (det (transpose (col_swap m i j))) (det (row_swap (transpose m) i j)); transitivity (det (col_swap m i j)) (det (row_swap (transpose m) i j)) (-(det (transpose m))); transitivity (det (col_swap m i j)) (-(det (transpose m))) (-(det m))
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let transpose_col_scale_to_row_scale (#t: Type) {| cr: commutative_ring t |} (#n: nat) (m: square_matrix t n) (i: fin n) (c: t) (a b: fin n) : Lemma (transpose (col_scale m i c) a b = row_scale (transpose m) i c a b) = elim_equatable_laws t; if (a <: nat) = (i <: nat) then begin assert (transpose (col_scale m i c) a b == m b a * c); assert (row_scale (transpose m) i c a b == c * m b a); cr.mul_comm_monoid.mul_comm_semigroup.mul_comm_magma.mul_commutativity (m b a) c end else begin assert (transpose (col_scale m i c) a b == m b a); reflexivity (m b a) end
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let det_col_scale (#t: Type) {| cr: commutative_ring t |} (#n: nat) (m: square_matrix t n) (i: fin n) (c: t) : Lemma (det (col_scale m i c) = c * det m) = let r : ring t = cr.ring in elim_equatable_laws t; transitivity_for_calc_proofs t; let pw (a b: fin n) : Lemma (transpose (col_scale m i c) a b = row_scale (transpose m) i c a b) = transpose_col_scale_to_row_scale #t #cr #n m i c a b in Classical.forall_intro_2 pw; det_pointwise_eq #t #r #n (transpose (col_scale m i c)) (row_scale (transpose m) i c); det_transpose #t #cr #n (col_scale m i c); det_row_scale #t #cr #n (transpose m) i c; det_transpose #t #cr #n m; reflexivity c; mul_congruence c (det (transpose m)) c (det m); symmetry (det (transpose (col_scale m i c))) (det (col_scale m i c)); transitivity (det (col_scale m i c)) (det (transpose (col_scale m i c))) (det (row_scale (transpose m) i c)); transitivity (det (col_scale m i c)) (det (row_scale (transpose m) i c)) (c * det (transpose m)); transitivity (det (col_scale m i c)) (c * det (transpose m)) (c * det m)
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let transpose_col_add_to_row_add (#t: Type) {| cr: commutative_ring t |} (#n: nat) (m: square_matrix t n) (i j: fin n) (c: t) (a b: fin n) : Lemma (requires ~(i == j)) (ensures transpose (col_add m i j c) a b = row_add (transpose m) i j c a b) = elim_equatable_laws t; if (a <: nat) = (i <: nat) then begin assert (transpose (col_add m i j c) a b == m b a + m b j * c); assert (row_add (transpose m) i j c a b == m b a + c * m b j); cr.mul_comm_monoid.mul_comm_semigroup.mul_comm_magma.mul_commutativity (m b j) c; reflexivity (m b a); add_congruence (m b a) (m b j * c) (m b a) (c * m b j) end else begin reflexivity (m b a) end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 120"
let det_col_add (#t: Type) {| id: integral_domain t |} (#n: nat) (m: square_matrix t n) (i j: fin n) (c: t) : Lemma (requires ~(i == j) /\ (one + one) <> zero #t) (ensures det (col_add m i j c) = det m) = let cr : commutative_ring t = id.commutative_ring in let r : ring t = cr.ring in elim_equatable_laws t; transitivity_for_calc_proofs t; let pw (a b: fin n) : Lemma (transpose (col_add m i j c) a b = row_add (transpose m) i j c a b) = transpose_col_add_to_row_add #t #cr #n m i j c a b in Classical.forall_intro_2 pw; det_pointwise_eq #t #r #n (transpose (col_add m i j c)) (row_add (transpose m) i j c); det_transpose #t #cr #n (col_add m i j c); det_row_add #t #id #n (transpose m) i j c; det_transpose #t #cr #n m; symmetry (det (transpose (col_add m i j c))) (det (col_add m i j c)); transitivity (det (col_add m i j c)) (det (transpose (col_add m i j c))) (det (row_add (transpose m) i j c)); transitivity (det (col_add m i j c)) (det (row_add (transpose m) i j c)) (det (transpose m)); transitivity (det (col_add m i j c)) (det (transpose m)) (det m)
#pop-options
(* ============================================================== *)
(* det_zero_column: derived from det_zero_row via transpose.       *)
(* ============================================================== *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let det_zero_column (#t: Type) {| cr: commutative_ring t |} (#n: nat) (m: square_matrix t n) (j: fin n) : Lemma (requires forall (k: fin n). m k j = zero #t) (ensures det m = zero #t) = let r : ring t = cr.ring in elim_equatable_laws t; transitivity_for_calc_proofs t; let mt = transpose m in let pw (k: fin n) : Lemma (mt j k = zero #t) = assert (mt j k == m k j); reflexivity (m k j) in Classical.forall_intro pw; det_zero_row #t #r #n mt j; det_transpose #t #cr #n m; transitivity (det m) (det mt) (zero #t)
#pop-options
(* ====================================================================== *)
(*  Additive multilinearity of det in a row.                              *)
(*                                                                        *)
(*  If row i of m is split as u + v (other rows unchanged), then          *)
(*     det (row_replace m i (fun k -> u k + v k))                          *)
(*        = det (row_replace m i u) + det (row_replace m i v).             *)
(* ====================================================================== *)


(* ====================================================================== *)
(*  Additive multilinearity of det in a row.                              *)
(*                                                                        *)
(*  Stated with three explicit functions u, v, uv and a hypothesis that   *)
(*  uv k = u k + v k pointwise on fin n. This signature avoids the        *)
(*  closure-equality pitfalls of lambda parameters in the conclusion.     *)
(* ====================================================================== *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 200"
let perm_product_row_split
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i: fin n) (u v uv: fin n -> t) (p: permutation n)
  : Lemma (requires forall (k: fin n). uv k = u k + v k)
          (ensures perm_product (row_replace m i uv) p
                 = perm_product (row_replace m i u) p
                 + perm_product (row_replace m i v) p)
  = let r : ring t = cr.ring in
    elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    let muv = row_replace m i uv in
    let mu  = row_replace m i u in
    let mv  = row_replace m i v in
    let body : nat -> t =
      fun (k: nat) -> if k < n then mu (k <: fin n) (p.fwd (k <: fin n)) else one in
    let body_uv : nat -> t =
      fun (k: nat) -> if k < n then muv (k <: fin n) (p.fwd (k <: fin n)) else one in
    let body_v : nat -> t =
      fun (k: nat) -> if k < n then mv (k <: fin n) (p.fwd (k <: fin n)) else one in
    let in_ : nat = i in
    let agree_uv (k: nat)
      : Lemma (0 <= k /\ k < n /\ k <> in_ ==> body_uv k = body k)
      = if k < n && k <> in_ then begin
          let kf : fin n = k in
          assert (kf <> i);
          reflexivity (m kf (p.fwd kf))
        end
    in
    Classical.forall_intro agree_uv;
    let agree_v (k: nat)
      : Lemma (0 <= k /\ k < n /\ k <> in_ ==> body_v k = body k)
      = if k < n && k <> in_ then begin
          let kf : fin n = k in
          assert (kf <> i);
          reflexivity (m kf (p.fwd kf))
        end
    in
    Classical.forall_intro agree_v;
    let upi = u (p.fwd i) in
    let vpi = v (p.fwd i) in
    let uvi = uv (p.fwd i) in
    assert (uvi = upi + vpi);
    assert (body_uv in_ == uvi);
    assert (body    in_ == upi);
    assert (body_v  in_ == vpi);
    reflexivity (body_uv in_);
    transitivity (body_uv in_) uvi (upi + vpi);
    assert (body_uv in_ = upi + vpi);
    left_mul_identity vpi;
    assert (one * vpi = vpi);
    symmetry (one * vpi) vpi;
    reflexivity upi;
    add_congruence upi vpi upi (one * vpi);
    assert (upi + vpi = upi + one * vpi);
    transitivity (body_uv in_) (upi + vpi) (upi + one * vpi);
    assert (body_uv in_ = body in_ + one * body_v in_);
    prod_range_extract_add_left #t #cr body body_uv body_v 0 n in_ (one #t);
    assert (prod_range body_uv 0 n
            = prod_range body 0 n + one * prod_range body_v 0 n);
    left_mul_identity (prod_range body_v 0 n);
    reflexivity (prod_range body 0 n);
    add_congruence (prod_range body 0 n) (one * prod_range body_v 0 n)
                   (prod_range body 0 n) (prod_range body_v 0 n);
    transitivity (prod_range body_uv 0 n)
                 (prod_range body 0 n + one * prod_range body_v 0 n)
                 (prod_range body 0 n + prod_range body_v 0 n);
    perm_product_unfold muv p;
    perm_product_unfold mu  p;
    perm_product_unfold mv  p;
    reflexivity (perm_product muv p);
    reflexivity (perm_product mu p);
    reflexivity (perm_product mv p);
    symmetry (perm_product mu p) (prod_range body   0 n);
    symmetry (perm_product mv p) (prod_range body_v 0 n);
    add_congruence (prod_range body 0 n) (prod_range body_v 0 n)
                   (perm_product mu p)   (perm_product mv p);
    transitivity (perm_product muv p) (prod_range body_uv 0 n)
                 (prod_range body 0 n + prod_range body_v 0 n);
    transitivity (perm_product muv p)
                 (prod_range body 0 n + prod_range body_v 0 n)
                 (perm_product mu p + perm_product mv p)
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 200"
let leibniz_term_row_split
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i: fin n) (u v uv: fin n -> t) (p: permutation n)
  : Lemma (requires forall (k: fin n). uv k = u k + v k)
          (ensures leibniz_term (row_replace m i uv) p
                 = leibniz_term (row_replace m i u) p
                 + leibniz_term (row_replace m i v) p)
  = let r : ring t = cr.ring in
    let acg : add_comm_group t = add_comm_group_of_ring t r in
    elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    perm_product_row_split #t #cr #n m i u v uv p;
    let muv = row_replace m i uv in
    let mu  = row_replace m i u in
    let mv  = row_replace m i v in
    let pp_uv = perm_product muv p in
    let pp_u  = perm_product mu  p in
    let pp_v  = perm_product mv  p in
    if parity p
    then begin
      assert (leibniz_term muv p == pp_uv);
      assert (leibniz_term mu  p == pp_u);
      assert (leibniz_term mv  p == pp_v);
      reflexivity (pp_u + pp_v)
    end else begin
      neg_congruence_lem #t #acg pp_uv (pp_u + pp_v);
      neg_of_sum #t #(acg.add_group) pp_u pp_v;
      let acm = acg.add_comm_monoid.add_comm_semigroup.add_comm_magma in
      acm.add_commutativity (-pp_v) (-pp_u);
      trans_lemma [ -pp_uv;
                    -(pp_u + pp_v);
                    -pp_v + (-pp_u);
                    (-pp_u) + (-pp_v) ];
      assert (leibniz_term muv p == -pp_uv);
      assert (leibniz_term mu  p == -pp_u);
      assert (leibniz_term mv  p == -pp_v);
      reflexivity ((-pp_u) + (-pp_v))
    end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 200"
let det_row_split
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i: fin n) (u v uv: fin n -> t)
  : Lemma (requires forall (k: fin n). uv k = u k + v k)
          (ensures det (row_replace m i uv)
                 = det (row_replace m i u) + det (row_replace m i v))
  = let r : ring t = cr.ring in
    elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    let muv = row_replace m i uv in
    let mu  = row_replace m i u in
    let mv  = row_replace m i v in
    let f = leibniz_term muv in
    let g = leibniz_term mu in
    let h = leibniz_term mv in
    let pw (p: permutation n) : Lemma (f p = g p + h p)
      = leibniz_term_row_split #t #cr #n m i u v uv p in
    Classical.forall_intro pw;
    sum_over_perms_add_named n f g h;
    det_unfold muv;
    det_unfold mu;
    det_unfold mv;
    reflexivity (sum_over_perms n f);
    reflexivity (sum_over_perms n g);
    reflexivity (sum_over_perms n h);
    symmetry (det mu) (sum_over_perms n g);
    symmetry (det mv) (sum_over_perms n h);
    add_congruence (sum_over_perms n g) (sum_over_perms n h)
                   (det mu)             (det mv);
    transitivity (det muv) (sum_over_perms n f)
                 (sum_over_perms n g + sum_over_perms n h);
    transitivity (det muv) (sum_over_perms n g + sum_over_perms n h)
                 (det mu + det mv)
#pop-options

(* ====================================================================== *)
(*  Column counterpart: det_col_split, via transpose.                     *)
(* ====================================================================== *)

let col_replace (#t: Type) (#n: nat)
                (m: square_matrix t n) (j: fin n) (u: fin n -> t)
              : square_matrix t n
  = fun a b -> if b = j then u a else m a b

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let transpose_col_replace_pointwise (#t: Type) (#n: nat)
  (m: square_matrix t n) (j: fin n) (u: fin n -> t) (a b: fin n)
  : Lemma (transpose (col_replace m j u) a b == row_replace (transpose m) j u a b)
  = ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 200"
let det_col_split
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (j: fin n) (u v uv: fin n -> t)
  : Lemma (requires forall (k: fin n). uv k = u k + v k)
          (ensures det (col_replace m j uv)
                 = det (col_replace m j u) + det (col_replace m j v))
  = let r : ring t = cr.ring in
    elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    let cuv = col_replace m j uv in
    let cu  = col_replace m j u  in
    let cv  = col_replace m j v  in
    let mt  = transpose m in
    let ruv = row_replace mt j uv in
    let ru  = row_replace mt j u  in
    let rv  = row_replace mt j v  in
    let pw_uv (a b: fin n)
      : Lemma (transpose cuv a b = ruv a b)
      = transpose_col_replace_pointwise #t #n m j uv a b;
        reflexivity (ruv a b) in
    Classical.forall_intro_2 pw_uv;
    let pw_u (a b: fin n)
      : Lemma (transpose cu a b = ru a b)
      = transpose_col_replace_pointwise #t #n m j u a b;
        reflexivity (ru a b) in
    Classical.forall_intro_2 pw_u;
    let pw_v (a b: fin n)
      : Lemma (transpose cv a b = rv a b)
      = transpose_col_replace_pointwise #t #n m j v a b;
        reflexivity (rv a b) in
    Classical.forall_intro_2 pw_v;
    det_pointwise_eq #t #r #n (transpose cuv) ruv;
    det_pointwise_eq #t #r #n (transpose cu)  ru;
    det_pointwise_eq #t #r #n (transpose cv)  rv;
    det_transpose #t #cr #n cuv;
    det_transpose #t #cr #n cu;
    det_transpose #t #cr #n cv;
    det_row_split #t #cr #n mt j u v uv;
    symmetry (det (transpose cuv)) (det cuv);
    symmetry (det (transpose cu))  (det cu);
    symmetry (det (transpose cv))  (det cv);
    transitivity (det cuv) (det (transpose cuv)) (det ruv);
    transitivity (det cu)  (det (transpose cu))  (det ru);
    transitivity (det cv)  (det (transpose cv))  (det rv);
    (* det cuv = det ruv = det ru + det rv = det cu + det cv. *)
    assert (det ruv = det ru + det rv);
    symmetry (det ru) (det cu);
    symmetry (det rv) (det cv);
    add_congruence (det ru) (det rv) (det cu) (det cv);
    assert (det ru + det rv = det cu + det cv);
    transitivity (det cuv) (det ruv) (det ru + det rv);
    transitivity (det cuv) (det ru + det rv) (det cu + det cv)
#pop-options

(* ====================================================================== *)
(*  L3: General row-permutation determinant law                            *)
(*       det (permute_rows m sigma) = sign(sigma) * det m                  *)
(*  We split into the two parity cases for clarity.                        *)
(* ====================================================================== *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let perm_product_permute_rows
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (sigma: permutation n) (p: permutation n)
  : Lemma (perm_product (permute_rows m sigma) p =
           perm_product m (compose p (inverse sigma)))
  = let mcm : mul_comm_monoid t = mul_comm_monoid_of_comm_ring t cr in
    elim_equatable_laws t #(mcm.mul_monoid.mul_semigroup.has_mul.eq);
    transitivity_for_calc_proofs t #(mcm.mul_monoid.mul_semigroup.has_mul.eq);
    let sigma_inv = inverse sigma in
    let q = compose p sigma_inv in
    let lhs_body : nat -> t =
      fun (k: nat) -> if k < n
                  then (permute_rows m sigma) (k <: fin n) (p.fwd (k <: fin n))
                  else one in
    let rhs_body : nat -> t =
      fun (k: nat) -> if k < n
                  then m (k <: fin n) (q.fwd (k <: fin n))
                  else one in
    let f : nat -> t =
      fun (k: nat) -> if k < n
                  then m (k <: fin n) (p.fwd ((sigma_inv.fwd (k <: fin n)) <: fin n))
                  else one in
    inverse_left sigma;
    let body_p_hyp (k: nat) : Lemma
      (0 <= k /\ k < n ==>
       lhs_body k = f (sigma.fwd (k <: fin n)))
      = if 0 <= k && k < n then begin
          let kf : fin n = k <: fin n in
          let sk : fin n = sigma.fwd kf in
          compose_fwd sigma_inv sigma kf;
          perm_eq_elim (compose sigma_inv sigma) (identity n) kf;
          identity_fwd n kf;
          assert (sigma_inv.fwd sk == kf);
          reflexivity (m sk (p.fwd kf))
        end in
    Classical.forall_intro body_p_hyp;
    let body_id_hyp (k: nat) : Lemma
      (0 <= k /\ k < n ==> rhs_body k = f k)
      = if 0 <= k && k < n then begin
          let kf : fin n = k <: fin n in
          compose_fwd p sigma_inv kf;
          reflexivity (m kf (p.fwd (sigma_inv.fwd kf)))
        end in
    Classical.forall_intro body_id_hyp;
    prod_range_perm_invariance_fn #t #mcm #n f lhs_body rhs_body sigma;
    perm_product_unfold (permute_rows m sigma) p;
    perm_product_unfold m q;
    reflexivity (perm_product (permute_rows m sigma) p);
    reflexivity (perm_product m q);
    trans_lemma #t #(mcm.mul_monoid.mul_semigroup.has_mul.eq)
                [ perm_product (permute_rows m sigma) p;
                  prod_range lhs_body 0 n;
                  prod_range rhs_body 0 n;
                  perm_product m q ]
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let leibniz_term_permute_rows_even
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (sigma: permutation n) (p: permutation n)
  : Lemma (requires parity sigma == true)
          (ensures leibniz_term (permute_rows m sigma) p =
                   leibniz_term m (compose p (inverse sigma)))
  = let r : ring t = cr.ring in
    let sigma_inv = inverse sigma in
    let q = compose p sigma_inv in
    perm_product_permute_rows #t #cr #n m sigma p;
    sign_homomorphism p sigma_inv;
    parity_inverse sigma;
    let lhs = leibniz_term (permute_rows m sigma) p in
    let pp1 = perm_product (permute_rows m sigma) p in
    let pp2 = perm_product m q in
    let rhs = leibniz_term m q in
    if parity p then begin
      assert (parity q == true);
      assert (lhs == pp1);
      assert (rhs == pp2);
      reflexivity pp1;
      reflexivity pp2;
      assert (pp1 = pp2);
      assert (lhs = rhs)
    end else begin
      assert (parity q == false);
      assert (lhs == -pp1);
      assert (rhs == -pp2);
      neg_congruence_lem #t #(add_comm_group_of_ring t r) pp1 pp2;
      assert ((-pp1) = (-pp2));
      assert (lhs = rhs)
    end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let leibniz_term_permute_rows_odd
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (sigma: permutation n) (p: permutation n)
  : Lemma (requires parity sigma == false)
          (ensures leibniz_term (permute_rows m sigma) p =
                   -(leibniz_term m (compose p (inverse sigma))))
  = let r : ring t = cr.ring in
    let sigma_inv = inverse sigma in
    let q = compose p sigma_inv in
    perm_product_permute_rows #t #cr #n m sigma p;
    sign_homomorphism p sigma_inv;
    parity_inverse sigma;
    let lhs = leibniz_term (permute_rows m sigma) p in
    let pp1 = perm_product (permute_rows m sigma) p in
    let pp2 = perm_product m q in
    let rhs = -(leibniz_term m q) in
    if parity p then begin
      assert (parity q == false);
      assert (lhs == pp1);
      assert (leibniz_term m q == -pp2);
      assert (rhs == -(-pp2));
      reflexivity pp1;
      reflexivity pp2;
      double_negation_lemma #t #(add_comm_group_of_ring t r).add_group pp2;
      symmetry (-(-pp2)) pp2;
      trans_lemma [ pp1; pp2; -(-pp2) ];
      assert (pp1 = -(-pp2));
      assert (lhs = rhs)
    end else begin
      assert (parity q == true);
      assert (lhs == -pp1);
      assert (leibniz_term m q == pp2);
      assert (rhs == -pp2);
      neg_congruence_lem #t #(add_comm_group_of_ring t r) pp1 pp2;
      assert ((-pp1) = (-pp2));
      assert (lhs = rhs)
    end
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 80"
let det_permute_rows_even
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (sigma: permutation n)
  : Lemma (requires parity sigma == true)
          (ensures  det (permute_rows m sigma) = det m)
  = let r : ring t = cr.ring in
    let sigma_inv = inverse sigma in
    let f = leibniz_term (permute_rows m sigma) in
    let g = leibniz_term m in
    leibniz_term_respects_perm_eq #t #r #n m;
    (* sum_over_perms n g = sum_over_perms n (fun s -> g (compose s sigma_inv)). *)
    sum_over_perms_reindex n g sigma_inv;
    let pointwise (s: permutation n) : Lemma (f s = g (compose s sigma_inv))
      = leibniz_term_permute_rows_even #t #cr #n m sigma s in
    Classical.forall_intro pointwise;
    sum_over_perms_congruence n f (fun s -> g (compose s sigma_inv));
    symmetry (sum_over_perms n g) (sum_over_perms n (fun s -> g (compose s sigma_inv)));
    det_unfold (permute_rows m sigma);
    det_unfold m;
    reflexivity (sum_over_perms n f);
    reflexivity (sum_over_perms n g);
    symmetry (det m) (sum_over_perms n g);
    trans_lemma [ det (permute_rows m sigma);
                  sum_over_perms n f;
                  sum_over_perms n (fun s -> g (compose s sigma_inv));
                  sum_over_perms n g;
                  det m ]
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 80"
let det_permute_rows_odd
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (sigma: permutation n)
  : Lemma (requires parity sigma == false)
          (ensures  det (permute_rows m sigma) = -(det m))
  = let r : ring t = cr.ring in
    let sigma_inv = inverse sigma in
    let f = leibniz_term (permute_rows m sigma) in
    let g = leibniz_term m in
    leibniz_term_respects_perm_eq #t #r #n m;
    sum_over_perms_reindex n g sigma_inv;
    let pointwise (s: permutation n) : Lemma (f s = -(g (compose s sigma_inv)))
      = leibniz_term_permute_rows_odd #t #cr #n m sigma s in
    Classical.forall_intro pointwise;
    sum_over_perms_congruence n f (fun s -> -(g (compose s sigma_inv)));
    sum_over_perms_neg #t #(add_comm_group_of_ring t r) n (fun s -> g (compose s sigma_inv));
    symmetry (sum_over_perms n g) (sum_over_perms n (fun s -> g (compose s sigma_inv)));
    det_unfold (permute_rows m sigma);
    det_unfold m;
    reflexivity (sum_over_perms n g);
    reflexivity (sum_over_perms n f);
    symmetry (det m) (sum_over_perms n g);
    neg_congruence_lem #t #(add_comm_group_of_ring t r)
                       (sum_over_perms n (fun s -> g (compose s sigma_inv)))
                       (sum_over_perms n g);
    neg_congruence_lem #t #(add_comm_group_of_ring t r)
                       (sum_over_perms n g)
                       (det m);
    trans_lemma [ det (permute_rows m sigma);
                  sum_over_perms n f;
                  sum_over_perms n (fun s -> -(g (compose s sigma_inv)));
                  -(sum_over_perms n (fun s -> g (compose s sigma_inv)));
                  -(sum_over_perms n g);
                  -(det m) ]
#pop-options

let det_permute_rows
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (sigma: permutation n)
  : Lemma (det (permute_rows m sigma) =
           (if parity sigma then det m else -(det m)))
  = if parity sigma
    then det_permute_rows_even #t #cr #n m sigma
    else det_permute_rows_odd  #t #cr #n m sigma

(* ====================================================================== *)
(*  Laplace expansion: definitions and helpers.                           *)
(*                                                                        *)
(*  We add:                                                               *)
(*    - minus_one_pow : nat -> t  (the ring element (-1)^k)               *)
(*    - skip          : fin (n-1) -> fin n, skipping a chosen index       *)
(*    - minor         : square_matrix t n -> fin n -> fin n               *)
(*                       -> square_matrix t (n-1)                         *)
(*                                                                        *)
(*  These are the foundational definitions used by the Laplace row        *)
(*  expansion theorem.                                                    *)
(* ====================================================================== *)

(* (-1)^k as a ring element. *)
let minus_one_pow (#t: Type) {| r: ring t |} (k: nat) : t
  = if Prims.op_Modulus k 2 = 0 then one else (- (one #t))

let minus_one_pow_zero (#t: Type) {| r: ring t |}
  : Lemma (minus_one_pow #t 0 == one)
  = ()

let minus_one_pow_one (#t: Type) {| r: ring t |}
  : Lemma (minus_one_pow #t 1 == (- (one #t)))
  = ()

let minus_one_pow_even (#t: Type) {| r: ring t |} (k: nat)
  : Lemma (requires Prims.op_Modulus k 2 = 0)
          (ensures  minus_one_pow #t k == one)
  = ()

let minus_one_pow_odd (#t: Type) {| r: ring t |} (k: nat)
  : Lemma (requires Prims.op_Modulus k 2 = 1)
          (ensures  minus_one_pow #t k == (- (one #t)))
  = ()

(* Skip the index `i` when injecting fin (n-1) into fin n. *)
let skip (#n: pos) (i: fin n) (a: fin (Prims.op_Subtraction n 1)) : fin n
  = if (a <: nat) < (i <: nat) then (a <: nat) else Prims.op_Addition a 1

let skip_lt (#n: pos) (i: fin n) (a: fin (Prims.op_Subtraction n 1))
  : Lemma (requires (a <: nat) < (i <: nat))
          (ensures  (skip i a <: nat) == (a <: nat))
  = ()

let skip_ge (#n: pos) (i: fin n) (a: fin (Prims.op_Subtraction n 1))
  : Lemma (requires (a <: nat) >= (i <: nat))
          (ensures  (skip i a <: nat) == Prims.op_Addition a 1)
  = ()

(* skip is injective. *)
let skip_injective (#n: pos) (i: fin n) (a b: fin (Prims.op_Subtraction n 1))
  : Lemma (requires (skip i a <: nat) == (skip i b <: nat))
          (ensures  (a <: nat) == (b <: nat))
  = ()

(* skip never lands on i. *)
let skip_avoids (#n: pos) (i: fin n) (a: fin (Prims.op_Subtraction n 1))
  : Lemma (~((skip i a <: nat) == (i <: nat)))
  = ()

(* The (n-1) x (n-1) minor of m at row i, column j: delete row i and column j. *)
let minor (#t: Type) (#n: pos) (m: square_matrix t n) (i j: fin n)
  : square_matrix t (Prims.op_Subtraction n 1)
  = fun (a: fin (Prims.op_Subtraction n 1)) (b: fin (Prims.op_Subtraction n 1))
      -> m (skip i a) (skip j b)

let minor_at (#t: Type) (#n: pos) (m: square_matrix t n) (i j: fin n)
             (a b: fin (Prims.op_Subtraction n 1))
  : Lemma (minor m i j a b == m (skip i a) (skip j b))
  = ()

(* ====================================================================== *)
(*  Laplace expansion along row i.                                        *)
(*                                                                        *)
(*    det m = Σ_{j: fin n} (-1)^(i+j) * m i j * det (minor m i j)         *)
(*                                                                        *)
(*  The proof has four ingredients, all proved below:                      *)
(*                                                                        *)
(*    (1) inject/project bijection  S_n ≃ fin n × S_{n-1}                 *)
(*    (2) parity_inject: sign (inject σ' i j) = (-1)^(i+j) · sign σ'     *)
(*    (3) sum_over_perms_partition: double-sum reindexing over S_n         *)
(*    (4) inner_sum_eq_cofactor: inner sum = cofactor expansion term       *)
(*                                                                        *)
(*  Final assembly: det_laplace_row (near the end of this file).          *)
(* ====================================================================== *)
(* ====================================================================== *)
(*  inject: building a permutation of fin n from a permutation of         *)
(*          fin (n-1) and a chosen image j for position i.                *)
(* ====================================================================== *)

(* Partial inverse of `skip i`: removes index i, mapping fin n \ {i} into fin (n-1). *)
let unskip (#n: pos) (i: fin n) (k: fin n{(k <: nat) <> (i <: nat)})
  : fin (Prims.op_Subtraction n 1)
  = if (k <: nat) < (i <: nat) then (k <: nat) else Prims.op_Subtraction k 1

let skip_unskip (#n: pos) (i: fin n) (k: fin n)
  : Lemma (requires (k <: nat) <> (i <: nat))
          (ensures  (skip i (unskip i k) <: nat) == (k <: nat))
  = ()

let unskip_skip (#n: pos) (i: fin n) (a: fin (Prims.op_Subtraction n 1))
  : Lemma ((unskip i (skip i a) <: nat) == (a <: nat))
  = ()

(* Build a permutation of fin n with sigma(i) = j whose action on the
   remaining positions is determined by sigma' via the canonical relabelling. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let inject (#n: pos) (sigma': permutation (Prims.op_Subtraction n 1))
           (i j: fin n)
  : permutation n
  = let fwd (k: fin n) : fin n
      = if (k <: nat) = (i <: nat) then j
        else skip j (sigma'.fwd (unskip i k)) in
    let bwd (l: fin n) : fin n
      = if (l <: nat) = (j <: nat) then i
        else skip i (sigma'.bwd (unskip j l)) in
    let fwd_bwd_id (l: fin n) : Lemma (fwd (bwd l) == l)
      = if (l <: nat) = (j <: nat) then ()
        else begin
          let u : fin (Prims.op_Subtraction n 1) = unskip j l in
          let a' : fin (Prims.op_Subtraction n 1) = sigma'.bwd u in
          let k : fin n = skip i a' in
          skip_avoids i a';
          unskip_skip i a';
          sigma'.fwd_bwd_id u;
          skip_unskip j l
        end in
    let bwd_fwd_id (k: fin n) : Lemma (bwd (fwd k) == k)
      = if (k <: nat) = (i <: nat) then ()
        else begin
          let a : fin (Prims.op_Subtraction n 1) = unskip i k in
          let b : fin (Prims.op_Subtraction n 1) = sigma'.fwd a in
          let l : fin n = skip j b in
          skip_avoids j b;
          unskip_skip j b;
          sigma'.bwd_fwd_id a;
          skip_unskip i k
        end in
    { fwd; bwd; fwd_bwd_id; bwd_fwd_id }
#pop-options

let inject_fwd_at_i (#n: pos) (sigma': permutation (Prims.op_Subtraction n 1))
                    (i j: fin n)
  : Lemma ((inject sigma' i j).fwd i == j)
  = ()

let inject_fwd_off (#n: pos) (sigma': permutation (Prims.op_Subtraction n 1))
                   (i j: fin n) (k: fin n)
  : Lemma (requires (k <: nat) <> (i <: nat))
          (ensures  (inject sigma' i j).fwd k
                    == skip j (sigma'.fwd (unskip i k)))
  = ()

let inject_bwd_at_j (#n: pos) (sigma': permutation (Prims.op_Subtraction n 1))
                    (i j: fin n)
  : Lemma ((inject sigma' i j).bwd j == i)
  = ()
(* ====================================================================== *)
(*  project: inverse of `inject`.                                         *)
(*                                                                        *)
(*  Given a permutation sigma of fin n and an index i in fin n, define    *)
(*  sigma' = project sigma i in permutation (n-1) such that               *)
(*     inject sigma' i (sigma.fwd i) = sigma  (modulo perm_eq).           *)
(*                                                                        *)
(*  Concretely:                                                           *)
(*    let j = sigma.fwd i in                                              *)
(*    sigma'.fwd a = unskip j (sigma.fwd (skip i a))                      *)
(*    sigma'.bwd b = unskip i (sigma.bwd (skip j b))                      *)
(*                                                                        *)
(*  The unskip calls are well-defined because skip avoids the chosen      *)
(*  index, and sigma being a bijection preserves that avoidance.          *)
(* ====================================================================== *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let project (#n: pos) (sigma: permutation n) (i: fin n)
  : permutation (Prims.op_Subtraction n 1)
  = let j : fin n = sigma.fwd i in
    sigma.bwd_fwd_id i;
    assert (sigma.bwd j == i);
    sigma.fwd_bwd_id (sigma.fwd i);
    let fwd (a: fin (Prims.op_Subtraction n 1))
      : fin (Prims.op_Subtraction n 1)
      = let k : fin n = skip i a in
        skip_avoids i a;
        assert (~((k <: nat) == (i <: nat)));
        let v : fin n = sigma.fwd k in
        sigma.bwd_fwd_id k;
        assert (sigma.bwd v == k);
        sigma.bwd_fwd_id i;
        assert (sigma.bwd j == i);
        assert (~((v <: nat) == (j <: nat)));
        unskip j v in
    let bwd (b: fin (Prims.op_Subtraction n 1))
      : fin (Prims.op_Subtraction n 1)
      = let l : fin n = skip j b in
        skip_avoids j b;
        assert (~((l <: nat) == (j <: nat)));
        let w : fin n = sigma.bwd l in
        sigma.fwd_bwd_id l;
        assert (sigma.fwd w == l);
        sigma.bwd_fwd_id i;
        assert (sigma.bwd j == i);
        assert (~((w <: nat) == (i <: nat)));
        unskip i w in
    let fwd_bwd_id (b: fin (Prims.op_Subtraction n 1))
      : Lemma (fwd (bwd b) == b)
      = let l : fin n = skip j b in
        skip_avoids j b;
        let w : fin n = sigma.bwd l in
        sigma.fwd_bwd_id l;
        assert (~((w <: nat) == (i <: nat)));
        let a : fin (Prims.op_Subtraction n 1) = unskip i w in
        skip_unskip i w;
        assert ((skip i a <: nat) == (w <: nat));
        let v : fin n = sigma.fwd (skip i a) in
        (* skip i a = w (as nat), and sigma.fwd w = l, so v should equal l. *)
        assert ((skip i a <: nat) == (w <: nat));
        assert (sigma.fwd w == l);
        unskip_skip j b in
    let bwd_fwd_id (a: fin (Prims.op_Subtraction n 1))
      : Lemma (bwd (fwd a) == a)
      = let k : fin n = skip i a in
        skip_avoids i a;
        let v : fin n = sigma.fwd k in
        sigma.bwd_fwd_id k;
        assert (~((v <: nat) == (j <: nat)));
        let b : fin (Prims.op_Subtraction n 1) = unskip j v in
        skip_unskip j v;
        assert ((skip j b <: nat) == (v <: nat));
        let w : fin n = sigma.bwd (skip j b) in
        assert (sigma.bwd v == k);
        unskip_skip i a in
    { fwd; bwd; fwd_bwd_id; bwd_fwd_id }
#pop-options

(* Helper omitted: the roundtrip proof inlines the needed reasoning. *)

(* Roundtrip: inject (project sigma i) i (sigma.fwd i) is perm_eq to sigma. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let inject_project_roundtrip (#n: pos) (sigma: permutation n) (i: fin n)
  : Lemma (perm_eq (inject (project sigma i) i (sigma.fwd i)) sigma)
  = let j : fin n = sigma.fwd i in
    let sigma' = project sigma i in
    let injected = inject sigma' i j in
    sigma.bwd_fwd_id i;
    assert (sigma.bwd j == i);
    let pointwise (k: fin n) : Lemma (injected.fwd k == sigma.fwd k)
      = if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i sigma' i j
        end else begin
          inject_fwd_off sigma' i j k;
          let a : fin (Prims.op_Subtraction n 1) = unskip i k in
          assert (injected.fwd k == skip j (sigma'.fwd a));
          skip_unskip i k;
          assert ((skip i a <: nat) == (k <: nat));
          (* Apply project's bwd_fwd_id: sigma'.bwd (sigma'.fwd a) == a. *)
          sigma'.bwd_fwd_id a;
          let b : fin (Prims.op_Subtraction n 1) = sigma'.fwd a in
          (* Definition of sigma'.bwd b yields skip i (sigma'.bwd b) = sigma.bwd (skip j b). *)
          let lhs1 : fin n = skip j b in
          skip_avoids j b;
          assert (~((lhs1 <: nat) == (j <: nat)));
          let w : fin n = sigma.bwd lhs1 in
          sigma.fwd_bwd_id lhs1;
          assert (sigma.fwd w == lhs1);
          assert (~((w <: nat) == (i <: nat)));
          (* sigma'.bwd b is defined as unskip i w. *)
          assert (sigma'.bwd b == unskip i w);
          assert (unskip i w == a);
          skip_unskip i w;
          assert ((skip i (unskip i w) <: nat) == (w <: nat));
          assert ((skip i a <: nat) == (w <: nat));
          assert ((w <: nat) == (k <: nat));
          (* So sigma.fwd k = lhs1 = skip j b = skip j (sigma'.fwd a) = injected.fwd k. *)
          assert (sigma.fwd w == skip j b);
          assert ((w <: nat) == (k <: nat));
          assert (sigma.fwd k == sigma.fwd w);
          assert (injected.fwd k == skip j (sigma'.fwd a))
        end in
    Classical.forall_intro pointwise;
    perm_eq_intro injected sigma
#pop-options
(* ====================================================================== *)
(*  parity_inject: sign(inject σ' i j) = (-1)^(i+j) · sign(σ').          *)
(*                                                                        *)
(*  Strategy:                                                             *)
(*    1. inject σ' i j ≡ compose (inject id i j) (inject σ' i i)          *)
(*    2. parity (inject σ' i i) == parity σ'                              *)
(*    3. parity (inject id i j) == ((i+j) % 2 = 0)                       *)
(*    4. Combine via sign_homomorphism.                                   *)
(* ====================================================================== *)

(* --- Lemma: inject id i i is identity --------------------------------- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let inject_id_is_identity (#n: pos) (i: fin n)
  : Lemma (perm_eq (inject (identity (Prims.op_Subtraction n 1)) i i) (identity n))
  = let sigma' = identity (Prims.op_Subtraction n 1) in
    let inj = inject sigma' i i in
    let pointwise (k: fin n) : Lemma (inj.fwd k == (identity n).fwd k)
      = if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i sigma' i i;
          identity_fwd n k
        end else begin
          inject_fwd_off sigma' i i k;
          identity_fwd (Prims.op_Subtraction n 1) (unskip i k);
          skip_unskip i k;
          identity_fwd n k
        end
    in
    Classical.forall_intro pointwise;
    perm_eq_intro inj (identity n)
#pop-options

(* --- Lemma: inject (compose σ1 σ2) i i ≡ compose (inject σ1 i i) (inject σ2 i i) --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let inject_compose_diag (#n: pos)
  (sigma1 sigma2: permutation (Prims.op_Subtraction n 1)) (i: fin n)
  : Lemma (perm_eq (inject (compose sigma1 sigma2) i i)
                   (compose (inject sigma1 i i) (inject sigma2 i i)))
  = let c = compose sigma1 sigma2 in
    let inj_c = inject c i i in
    let comp = compose (inject sigma1 i i) (inject sigma2 i i) in
    let pointwise (k: fin n) : Lemma (inj_c.fwd k == comp.fwd k)
      = compose_fwd (inject sigma1 i i) (inject sigma2 i i) k;
        if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i c i i;
          inject_fwd_at_i sigma2 i i;
          inject_fwd_at_i sigma1 i i
        end else begin
          inject_fwd_off c i i k;
          inject_fwd_off sigma2 i i k;
          let a : fin (Prims.op_Subtraction n 1) = unskip i k in
          let b : fin (Prims.op_Subtraction n 1) = sigma2.fwd a in
          let m : fin n = skip i b in
          skip_avoids i b;
          inject_fwd_off sigma1 i i m;
          unskip_skip i b;
          compose_fwd sigma1 sigma2 a
        end
    in
    Classical.forall_intro pointwise;
    perm_eq_intro inj_c comp
#pop-options

(* --- Lemma: inject (transposition a b) i i ≡ transposition n (skip i a) (skip i b) --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let inject_transposition_diag (#n: pos)
  (a b: fin (Prims.op_Subtraction n 1)) (i: fin n)
  : Lemma (perm_eq (inject (transposition (Prims.op_Subtraction n 1) a b) i i)
                   (transposition n (skip i a) (skip i b)))
  = let tau = transposition (Prims.op_Subtraction n 1) a b in
    let inj = inject tau i i in
    let sa : fin n = skip i a in
    let sb : fin n = skip i b in
    let tr = transposition n sa sb in
    let pointwise (k: fin n) : Lemma (inj.fwd k == tr.fwd k)
      = if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i tau i i;
          skip_avoids i a;
          skip_avoids i b;
          transposition_fwd_other n sa sb i
        end else begin
          inject_fwd_off tau i i k;
          let u : fin (Prims.op_Subtraction n 1) = unskip i k in
          (* tau.fwd u cases *)
          if (u <: nat) = (a <: nat) then begin
            transposition_fwd_left (Prims.op_Subtraction n 1) a b;
            assert (tau.fwd u == b);
            assert (skip i (tau.fwd u) == sb);
            unskip_skip i a;
            assert ((u <: nat) == (a <: nat));
            skip_unskip i k;
            assert ((skip i u <: nat) == (k <: nat));
            assert ((k <: nat) == (sa <: nat));
            transposition_fwd_left n sa sb
          end else if (u <: nat) = (b <: nat) then begin
            transposition_fwd_right (Prims.op_Subtraction n 1) a b;
            assert (tau.fwd u == a);
            assert (skip i (tau.fwd u) == sa);
            unskip_skip i b;
            skip_unskip i k;
            assert ((k <: nat) == (sb <: nat));
            transposition_fwd_right n sa sb
          end else begin
            transposition_fwd_other (Prims.op_Subtraction n 1) a b u;
            assert (tau.fwd u == u);
            assert (skip i (tau.fwd u) == skip i u);
            skip_unskip i k;
            assert ((skip i u <: nat) == (k <: nat));
            skip_avoids i a;
            skip_avoids i b;
            unskip_skip i a;
            unskip_skip i b;
            (* k ≠ sa and k ≠ sb *)
            assert (~((k <: nat) == (sa <: nat)));
            assert (~((k <: nat) == (sb <: nat)));
            transposition_fwd_other n sa sb k
          end
        end
    in
    Classical.forall_intro pointwise;
    perm_eq_intro inj tr
#pop-options

(* --- skip i d ≠ skip i (d+1) when d+1 < n-1 --- *)
let skip_adjacent_distinct (#n: pos) (i: fin n) (d: nat{Prims.op_Addition d 1 < Prims.op_Subtraction n 1})
  : Lemma (~((skip i (d <: fin (Prims.op_Subtraction n 1)) <: nat) ==
             (skip i ((Prims.op_Addition d 1) <: fin (Prims.op_Subtraction n 1)) <: nat)))
  = let a : fin (Prims.op_Subtraction n 1) = d in
    let b : fin (Prims.op_Subtraction n 1) = Prims.op_Addition d 1 in
    let h () : Lemma (requires (skip i a <: nat) == (skip i b <: nat)) (ensures False)
      = skip_injective i a b
    in
    Classical.move_requires h ()

(* --- parity_inject_diag: parity (inject σ' i i) == parity σ' --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let rec parity_inject_diag (#n: pos) (sigma': permutation (Prims.op_Subtraction n 1)) (i: fin n)
  : Lemma (ensures parity (inject sigma' i i) == parity sigma')
          (decreases (inversion_count sigma'))
  = let nm1 = Prims.op_Subtraction n 1 in
    match find_descent sigma' 0 with
    | None ->
      find_descent_none_implies_inv_zero sigma';
      let aux (k: fin nm1) : Lemma (sigma'.fwd k == k)
        = inv_zero_implies_identity_fwd sigma' k
      in
      Classical.forall_intro aux;
      let aux2 (k: fin nm1) : Lemma (sigma'.fwd k == (identity nm1).fwd k)
        = aux k; identity_fwd nm1 k
      in
      Classical.forall_intro aux2;
      perm_eq_intro sigma' (identity nm1);
      parity_perm_eq_invariant sigma' (identity nm1);
      parity_identity nm1;
      inject_id_is_identity i;
      let inj_id = inject (identity nm1) i i in
      let inj_s = inject sigma' i i in
      let pw (k: fin n) : Lemma (inj_s.fwd k == inj_id.fwd k)
        = if (k <: nat) = (i <: nat) then begin
            inject_fwd_at_i sigma' i i;
            inject_fwd_at_i (identity nm1) i i
          end else begin
            inject_fwd_off sigma' i i k;
            inject_fwd_off (identity nm1) i i k;
            identity_fwd nm1 (unskip i k)
          end
      in
      Classical.forall_intro pw;
      perm_eq_intro inj_s inj_id;
      parity_perm_eq_invariant inj_s inj_id;
      parity_perm_eq_invariant inj_id (identity n);
      parity_identity n
    | Some d ->
      (* d is an adjacent descent: sigma'.fwd d > sigma'.fwd (d+1), d+1 < nm1 *)
      inv_right_swap_at_descent sigma' d;
      let sigma2 = right_swap sigma' d in
      (* inject_compose_diag: inject(compose sigma' tau) i i ≡ compose (inject sigma' i i) (inject tau i i) *)
      let tau_small = transposition nm1 (d <: fin nm1) ((Prims.op_Addition d 1) <: fin nm1) in
      inject_compose_diag sigma' tau_small i;
      (* inject tau_small i i ≡ transposition n (skip i d) (skip i (d+1)) *)
      inject_transposition_diag (d <: fin nm1) ((Prims.op_Addition d 1) <: fin nm1) i;
      let inj_tau = inject tau_small i i in
      let sa : fin n = skip i (d <: fin nm1) in
      let sb : fin n = skip i ((Prims.op_Addition d 1) <: fin nm1) in
      let tau_big = transposition n sa sb in
      parity_perm_eq_invariant inj_tau tau_big;
      parity_transposition n sa sb;
      skip_adjacent_distinct i d;
      assert (parity tau_big == false);
      assert (parity inj_tau == false);
      (* compose sigma' tau_small is perm_eq to sigma2 = right_swap sigma' d *)
      let comp = compose sigma' tau_small in
      let pw_comp (k: fin nm1) : Lemma (comp.fwd k == sigma2.fwd k)
        = compose_fwd sigma' tau_small k;
          right_swap_fwd_at_k sigma' d k;
          if (k <: nat) = d then
            transposition_fwd_left nm1 (d <: fin nm1) ((Prims.op_Addition d 1) <: fin nm1)
          else if (k <: nat) = Prims.op_Addition d 1 then
            transposition_fwd_right nm1 (d <: fin nm1) ((Prims.op_Addition d 1) <: fin nm1)
          else
            transposition_fwd_other nm1 (d <: fin nm1) ((Prims.op_Addition d 1) <: fin nm1) k
      in
      Classical.forall_intro pw_comp;
      perm_eq_intro comp sigma2;
      parity_perm_eq_invariant comp sigma2;
      (* inject comp i i perm_eq inject sigma2 i i *)
      let inj_comp = inject comp i i in
      let inj_s = inject sigma' i i in
      let composed = compose inj_s inj_tau in
      let inj_s2 = inject sigma2 i i in
      let pw_s2 (k: fin n) : Lemma (inj_comp.fwd k == inj_s2.fwd k)
        = if (k <: nat) = (i <: nat) then begin
            inject_fwd_at_i comp i i;
            inject_fwd_at_i sigma2 i i
          end else begin
            inject_fwd_off comp i i k;
            inject_fwd_off sigma2 i i k
          end
      in
      Classical.forall_intro pw_s2;
      perm_eq_intro inj_comp inj_s2;
      parity_perm_eq_invariant inj_comp inj_s2;
      (* inj_comp perm_eq composed (from inject_compose_diag): 
         inject_compose_diag proved perm_eq (inject (compose sigma' tau_small) i i) (compose (inject sigma' i i) (inject tau_small i i))
         i.e., perm_eq inj_comp composed *)
      parity_perm_eq_invariant inj_comp composed;
      (* sign_homomorphism on composed *)
      sign_homomorphism inj_s inj_tau;
      (* IH *)
      parity_inject_diag sigma2 i;
      assert (parity inj_s2 == parity sigma2);
      (* derive parity sigma2 = not (parity sigma') *)
      sign_homomorphism sigma' tau_small;
      parity_transposition nm1 (d <: fin nm1) ((Prims.op_Addition d 1) <: fin nm1);
      perm_eq_sym comp sigma2;
      parity_perm_eq_invariant sigma2 comp;
      assert (parity comp == (parity sigma' = parity tau_small));
      assert (parity tau_small == false);
      assert (parity sigma2 == not (parity sigma'));
      (* Conclude: parity inj_s == parity sigma' *)
      assert (parity composed == (parity inj_s = parity inj_tau));
      assert (parity inj_tau == false);
      assert (parity inj_comp == parity composed);
      assert (parity inj_comp == parity inj_s2)
#pop-options

(* --- inject σ' i j ≡ compose (inject id i j) (inject σ' i i) --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let inject_compose_decomp (#n: pos)
  (sigma': permutation (Prims.op_Subtraction n 1)) (i j: fin n)
  : Lemma (perm_eq (inject sigma' i j)
                   (compose (inject (identity (Prims.op_Subtraction n 1)) i j)
                            (inject sigma' i i)))
  = let nm1 = Prims.op_Subtraction n 1 in
    let id_perm = identity nm1 in
    let inj_s = inject sigma' i j in
    let inj_id = inject id_perm i j in
    let inj_diag = inject sigma' i i in
    let comp = compose inj_id inj_diag in
    let pointwise (k: fin n) : Lemma (inj_s.fwd k == comp.fwd k)
      = compose_fwd inj_id inj_diag k;
        if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i sigma' i j;
          inject_fwd_at_i sigma' i i;
          inject_fwd_at_i id_perm i j
        end else begin
          inject_fwd_off sigma' i j k;
          inject_fwd_off sigma' i i k;
          let a : fin nm1 = unskip i k in
          let b : fin nm1 = sigma'.fwd a in
          let m : fin n = skip i b in
          skip_avoids i b;
          inject_fwd_off id_perm i j m;
          identity_fwd nm1 (unskip i m);
          unskip_skip i b
        end
    in
    Classical.forall_intro pointwise;
    perm_eq_intro inj_s comp
#pop-options

(* --- inject id step: for i < j, inject id i j ≡ compose (transposition (j-1) j) (inject id i (j-1)) --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let inject_id_step_down (#n: pos) (i j: fin n)
  : Lemma (requires (i <: nat) < (j <: nat))
          (ensures perm_eq (inject (identity (Prims.op_Subtraction n 1)) i j)
                           (compose (transposition n (Prims.op_Subtraction j 1 <: fin n) j)
                                    (inject (identity (Prims.op_Subtraction n 1)) i (Prims.op_Subtraction j 1 <: fin n))))
  = let nm1 = Prims.op_Subtraction n 1 in
    let id_perm = identity nm1 in
    let jm1 : fin n = Prims.op_Subtraction j 1 in
    let inj_j = inject id_perm i j in
    let inj_jm1 = inject id_perm i jm1 in
    let tau = transposition n jm1 j in
    let comp = compose tau inj_jm1 in
    let pointwise (k: fin n) : Lemma (inj_j.fwd k == comp.fwd k)
      = compose_fwd tau inj_jm1 k;
        if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i id_perm i j;
          inject_fwd_at_i id_perm i jm1;
          (* inj_jm1.fwd i = jm1, tau.fwd jm1 = j *)
          transposition_fwd_left n jm1 j
        end else begin
          inject_fwd_off id_perm i j k;
          inject_fwd_off id_perm i jm1 k;
          identity_fwd nm1 (unskip i k);
          let u : fin nm1 = unskip i k in
          let val_j : fin n = skip j u in
          let val_jm1 : fin n = skip jm1 u in
          (* Need: tau.fwd val_jm1 == val_j *)
          if (u <: nat) < (Prims.op_Subtraction j 1) then begin
            (* u < j-1, so skip j u = u (since u < j-1 < j) and skip (j-1) u = u *)
            skip_lt j u;
            skip_lt jm1 u;
            assert ((val_j <: nat) == (u <: nat));
            assert ((val_jm1 <: nat) == (u <: nat));
            (* val_jm1 = u < j-1, so tau fixes it *)
            transposition_fwd_other n jm1 j val_jm1
          end else if (u <: nat) = Prims.op_Subtraction j 1 then begin
            (* u = j-1: skip j u = j-1 (since u < j), skip (j-1) u = u+1 = j *)
            skip_lt j u;
            skip_ge jm1 u;
            assert ((val_j <: nat) == (u <: nat));
            assert ((val_jm1 <: nat) == Prims.op_Addition u 1);
            assert ((val_j <: nat) == Prims.op_Subtraction j 1);
            assert ((val_jm1 <: nat) == (j <: nat));
            (* tau.fwd j = j-1 = val_j *)
            transposition_fwd_right n jm1 j
          end else begin
            (* u >= j (since u > j-1 and u is nat): skip j u = u+1, skip (j-1) u = u+1 *)
            skip_ge j u;
            skip_ge jm1 u;
            assert ((val_j <: nat) == Prims.op_Addition u 1);
            assert ((val_jm1 <: nat) == Prims.op_Addition u 1);
            (* tau fixes val_jm1 since val_jm1 = u+1 >= j+1 > j and >= j > j-1 *)
            transposition_fwd_other n jm1 j val_jm1
          end
        end
    in
    Classical.forall_intro pointwise;
    perm_eq_intro inj_j comp
#pop-options

(* --- inject id step: for j < i, inject id i j ≡ compose (transposition j (j+1)) (inject id i (j+1)) --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let inject_id_step_up (#n: pos) (i j: fin n)
  : Lemma (requires (j <: nat) < (i <: nat))
          (ensures perm_eq (inject (identity (Prims.op_Subtraction n 1)) i j)
                           (compose (transposition n j (Prims.op_Addition j 1 <: fin n))
                                    (inject (identity (Prims.op_Subtraction n 1)) i (Prims.op_Addition j 1 <: fin n))))
  = let nm1 = Prims.op_Subtraction n 1 in
    let id_perm = identity nm1 in
    let jp1 : fin n = Prims.op_Addition j 1 in
    let inj_j = inject id_perm i j in
    let inj_jp1 = inject id_perm i jp1 in
    let tau = transposition n j jp1 in
    let comp = compose tau inj_jp1 in
    let pointwise (k: fin n) : Lemma (inj_j.fwd k == comp.fwd k)
      = compose_fwd tau inj_jp1 k;
        if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i id_perm i j;
          inject_fwd_at_i id_perm i jp1;
          (* inj_jp1.fwd i = jp1, tau.fwd jp1 = j *)
          transposition_fwd_right n j jp1
        end else begin
          inject_fwd_off id_perm i j k;
          inject_fwd_off id_perm i jp1 k;
          identity_fwd nm1 (unskip i k);
          let u : fin nm1 = unskip i k in
          let val_j : fin n = skip j u in
          let val_jp1 : fin n = skip jp1 u in
          (* Need: tau.fwd val_jp1 == val_j *)
          if (u <: nat) < (j <: nat) then begin
            (* u < j < j+1: skip j u = u, skip (j+1) u = u *)
            skip_lt j u;
            skip_lt jp1 u;
            assert ((val_j <: nat) == (u <: nat));
            assert ((val_jp1 <: nat) == (u <: nat));
            transposition_fwd_other n j jp1 val_jp1
          end else if (u <: nat) = (j <: nat) then begin
            (* u = j: skip j u = u+1 = j+1, skip (j+1) u = u = j *)
            skip_ge j u;
            skip_lt jp1 u;
            assert ((val_j <: nat) == Prims.op_Addition u 1);
            assert ((val_jp1 <: nat) == (u <: nat));
            assert ((val_j <: nat) == (jp1 <: nat));
            assert ((val_jp1 <: nat) == (j <: nat));
            (* tau.fwd j = jp1 = val_j *)
            transposition_fwd_left n j jp1
          end else begin
            (* u > j, so u >= j+1: skip j u = u+1, skip (j+1) u = u+1 *)
            skip_ge j u;
            skip_ge jp1 u;
            assert ((val_j <: nat) == Prims.op_Addition u 1);
            assert ((val_jp1 <: nat) == Prims.op_Addition u 1);
            transposition_fwd_other n j jp1 val_jp1
          end
        end
    in
    Classical.forall_intro pointwise;
    perm_eq_intro inj_j comp
#pop-options

(* --- Boolean arithmetic helper --- *)
private let bool_not_even_succ (a b: nat)
  : Lemma (not ((Prims.op_Addition a b) % 2 = 0) == ((Prims.op_Addition a (Prims.op_Addition b 1)) % 2 = 0))
  = ()

private let bool_not_even_pred (a b: nat)
  : Lemma (requires b > 0)
          (ensures not ((Prims.op_Addition a b) % 2 = 0) == ((Prims.op_Addition a (Prims.op_Subtraction b 1)) % 2 = 0))
  = ()

(* --- parity_inject_id: parity (inject id i j) == ((i+j) % 2 = 0) --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let rec parity_inject_id (#n: pos) (i j: fin n)
  : Lemma (ensures parity (inject (identity (Prims.op_Subtraction n 1)) i j) ==
                   ((Prims.op_Addition (i <: nat) (j <: nat)) % 2 = 0))
          (decreases (if (j <: nat) >= (i <: nat) then Prims.op_Subtraction (j <: nat) (i <: nat) else Prims.op_Subtraction (i <: nat) (j <: nat)))
  = let nm1 = Prims.op_Subtraction n 1 in
    let id_perm = identity nm1 in
    if (j <: nat) = (i <: nat) then begin
      inject_id_is_identity i;
      parity_perm_eq_invariant (inject id_perm i j) (identity n);
      parity_identity n
    end else if (j <: nat) > (i <: nat) then begin
      let jm1 : fin n = Prims.op_Subtraction j 1 in
      inject_id_step_down i j;
      let tau = transposition n jm1 j in
      let inj_jm1 = inject id_perm i jm1 in
      let comp = compose tau inj_jm1 in
      parity_perm_eq_invariant (inject id_perm i j) comp;
      sign_homomorphism tau inj_jm1;
      parity_transposition n jm1 j;
      assert (parity tau == false);
      parity_inject_id i jm1;
      assert (parity inj_jm1 == ((Prims.op_Addition (i <: nat) (jm1 <: nat)) % 2 = 0));
      assert (parity comp == (parity tau = parity inj_jm1));
      assert (parity comp == (false = parity inj_jm1));
      assert (parity comp == not (parity inj_jm1));
      bool_not_even_pred (i <: nat) (j <: nat)
    end else begin
      let jp1 : fin n = Prims.op_Addition j 1 in
      inject_id_step_up i j;
      let tau = transposition n j jp1 in
      let inj_jp1 = inject id_perm i jp1 in
      let comp = compose tau inj_jp1 in
      parity_perm_eq_invariant (inject id_perm i j) comp;
      sign_homomorphism tau inj_jp1;
      parity_transposition n j jp1;
      assert (parity tau == false);
      parity_inject_id i jp1;
      assert (parity inj_jp1 == ((Prims.op_Addition (i <: nat) (jp1 <: nat)) % 2 = 0));
      assert (parity comp == not (parity inj_jp1));
      bool_not_even_succ (i <: nat) (j <: nat)
    end
#pop-options

(* --- MAIN: parity_inject --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let parity_inject (#n: pos) (sigma': permutation (Prims.op_Subtraction n 1))
                  (i j: fin n)
  : Lemma (parity (inject sigma' i j) ==
           (parity sigma' = ((Prims.op_Addition (i <: nat) (j <: nat)) % 2 = 0)))
  = let nm1 = Prims.op_Subtraction n 1 in
    let id_perm = identity nm1 in
    inject_compose_decomp sigma' i j;
    let inj_s = inject sigma' i j in
    let inj_id = inject id_perm i j in
    let inj_diag = inject sigma' i i in
    let comp = compose inj_id inj_diag in
    parity_perm_eq_invariant inj_s comp;
    sign_homomorphism inj_id inj_diag;
    parity_inject_id i j;
    parity_inject_diag sigma' i;
    assert (parity comp == (parity inj_id = parity inj_diag));
    assert (parity inj_id == ((Prims.op_Addition (i <: nat) (j <: nat)) % 2 = 0));
    assert (parity inj_diag == parity sigma')
#pop-options

(* ====================================================================== *)
(*  STATUS OF LAPLACE EXPANSION (session L5s2 increment)                  *)
(*                                                                        *)
(*  Added in this session:                                                *)
(*    - project: the (n-1)-permutation extracted from a permutation       *)
(*      of n via removal of the (i, sigma.fwd i) position-image pair.     *)
(*    - inject_project_roundtrip: the canonical inverse relation,         *)
(*           perm_eq (inject (project sigma i) i (sigma.fwd i)) sigma.    *)
(*                                                                        *)
(*  Together with the prior session's `inject` and its `inject_fwd_*`     *)
(*  lemmas, this establishes the bijection                                *)
(*                                                                        *)
(*       S_n  <-->  fin n  x  S_{n-1}                                     *)
(*                                                                        *)
(*  on representatives (i.e. modulo perm_eq), parameterised by the choice *)
(*  of row index `i`.                                                     *)
(*                                                                        *)
(*  All four sub-problems (P1–P4) are proved below:                       *)
(*    (P1) parity_inject — sign relation for inject                       *)
(*    (P2) sum_over_perms_partition — double-sum reindexing               *)
(*    (P3) inner_sum_eq_cofactor — inner sum = cofactor term              *)
(*    (P4) det_laplace_row — final assembly                               *)
(* ====================================================================== *)

(* ====================================================================== *)
(*  Proof of sum_over_perms_partition                                     *)
(*                                                                        *)
(*    sum_over_perms n f =                                                 *)
(*      fin_sum (fun j -> sum_over_perms (n-1) (fun s' -> f (inject s' i j))) *)
(* ====================================================================== *)

(* inject preserves perm_eq *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
let inject_preserves_perm_eq (#n: pos)
  (sp1 sp2: permutation (Prims.op_Subtraction n 1)) (i j: fin n)
  : Lemma (requires perm_eq sp1 sp2)
          (ensures perm_eq (inject sp1 i j) (inject sp2 i j))
  = let aux (k: fin n) : Lemma ((inject sp1 i j).fwd k == (inject sp2 i j).fwd k)
      = if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i sp1 i j;
          inject_fwd_at_i sp2 i j
        end else begin
          inject_fwd_off sp1 i j k;
          inject_fwd_off sp2 i j k;
          perm_eq_elim sp1 sp2 (unskip i k)
        end
    in Classical.forall_intro aux;
    perm_eq_intro (inject sp1 i j) (inject sp2 i j)
#pop-options

(* inject reflects perm_eq *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
let inject_reflects_perm_eq (#n: pos)
  (sp1 sp2: permutation (Prims.op_Subtraction n 1)) (i j: fin n)
  : Lemma (requires perm_eq (inject sp1 i j) (inject sp2 i j))
          (ensures perm_eq sp1 sp2)
  = let aux (a: fin (Prims.op_Subtraction n 1))
      : Lemma (sp1.fwd a == sp2.fwd a)
      = let k = skip i a in
        skip_avoids i a;
        inject_fwd_off sp1 i j k;
        inject_fwd_off sp2 i j k;
        assert ((inject sp1 i j).fwd k == skip j (sp1.fwd a));
        assert ((inject sp2 i j).fwd k == skip j (sp2.fwd a));
        perm_eq_elim (inject sp1 i j) (inject sp2 i j) k;
        skip_injective j (sp1.fwd a) (sp2.fwd a)
    in Classical.forall_intro aux;
    perm_eq_intro sp1 sp2
#pop-options

(* respects_perm_eq transfers through inject *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
let respects_perm_eq_inject (#t: Type) {| m: add_comm_monoid t |}
  (#n: pos) (f: permutation n -> t) (i j: fin n)
  : Lemma (requires respects_perm_eq f)
          (ensures respects_perm_eq (fun s' -> f (inject s' i j)))
  = let g : permutation (Prims.op_Subtraction n 1) -> t
      = fun s' -> f (inject s' i j) in
    let aux (sp1 sp2: permutation (Prims.op_Subtraction n 1))
      : Lemma (perm_eq sp1 sp2 ==> g sp1 = g sp2)
      = if FStar.IndefiniteDescription.strong_excluded_middle (perm_eq sp1 sp2) then begin
          inject_preserves_perm_eq sp1 sp2 i j;
          respects_perm_eq_elim f (inject sp1 i j) (inject sp2 i j)
        end
    in Classical.forall_intro_2 aux;
    respects_perm_eq_intro g
#pop-options

(* If perm_eq p (inject sp i j), then p.fwd i == j *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
let perm_eq_inject_fwd_i (#n: pos) (p: permutation n)
  (sp: permutation (Prims.op_Subtraction n 1)) (i j: fin n)
  : Lemma (requires perm_eq p (inject sp i j))
          (ensures (p.fwd i <: nat) == (j <: nat))
  = inject_fwd_at_i sp i j;
    perm_eq_elim p (inject sp i j) i
#pop-options

(* If p.fwd i ≠ j, then perm_eq p (inject sp i j) is false. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
let perm_eq_inject_false (#n: pos) (p: permutation n)
  (sp: permutation (Prims.op_Subtraction n 1)) (i j: fin n)
  : Lemma (requires (p.fwd i <: nat) <> (j <: nat))
          (ensures perm_eq p (inject sp i j) == false)
  = inject_fwd_at_i sp i j;
    if perm_eq p (inject sp i j) then
      perm_eq_elim p (inject sp i j) i
    else ()
#pop-options

(* If p.fwd i == j, then perm_eq p (inject sp i j) ==
   perm_eq (project p i) sp. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let perm_eq_inject_match (#n: pos) (p: permutation n)
  (sp: permutation (Prims.op_Subtraction n 1)) (i j: fin n)
  : Lemma (requires (p.fwd i <: nat) == (j <: nat))
          (ensures perm_eq p (inject sp i j) == perm_eq (project p i) sp)
  = let pp = project p i in
    if perm_eq p (inject sp i j) then begin
      (* perm_eq p (inject sp i j), so inject (project p i) i j perm_eq inject sp i j *)
      inject_project_roundtrip p i;
      let inj_pp = inject pp i j in
      (* inj_pp.fwd == p.fwd pointwise, and p.fwd == (inject sp i j).fwd pointwise *)
      let aux (k: fin n) : Lemma (inj_pp.fwd k == (inject sp i j).fwd k)
        = perm_eq_elim inj_pp p k;
          perm_eq_elim p (inject sp i j) k
      in Classical.forall_intro aux;
      perm_eq_intro inj_pp (inject sp i j);
      inject_reflects_perm_eq pp sp i j;
      let aux2 (a: fin (Prims.op_Subtraction n 1)) : Lemma (pp.fwd a == sp.fwd a)
        = perm_eq_elim pp sp a
      in Classical.forall_intro aux2;
      perm_eq_intro pp sp
    end else begin
      (* Contrapositive: if perm_eq pp sp, then perm_eq p (inject sp i j) *)
      if perm_eq pp sp then begin
        let aux_eq (a: fin (Prims.op_Subtraction n 1)) : Lemma (pp.fwd a == sp.fwd a)
          = perm_eq_elim pp sp a
        in Classical.forall_intro aux_eq;
        perm_eq_intro pp sp;
        inject_preserves_perm_eq pp sp i j;
        inject_project_roundtrip p i;
        let aux_fwd (k: fin n) : Lemma (p.fwd k == (inject sp i j).fwd k)
          = let inj_pp = inject pp i j in
            perm_eq_elim inj_pp p k;
            perm_eq_elim inj_pp (inject sp i j) k
        in Classical.forall_intro aux_fwd;
        perm_eq_intro p (inject sp i j)
      end else ()
    end
#pop-options

(* Build the inject-image list directly, avoiding L.map to help Z3. *)
let rec fiber_list (#n: pos) (i j: fin n)
  (xs: list (permutation (Prims.op_Subtraction n 1)))
  : Tot (list (permutation n)) (decreases xs)
  = match xs with
    | [] -> []
    | hd :: tl -> inject hd i j :: fiber_list i j tl

(* Named wrapper for inject with i,j fixed — avoids anonymous lambda in L.map. *)
let inject_at (#n: pos) (i j: fin n) (sp: permutation (Prims.op_Subtraction n 1))
  : permutation n
  = inject sp i j

(* fiber_list is the same as L.map (inject_at i j). *)
let rec fiber_list_eq_map (#n: pos) (i j: fin n)
  (xs: list (permutation (Prims.op_Subtraction n 1)))
  : Lemma (ensures fiber_list i j xs == L.map (inject_at i j) xs)
          (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: tl -> fiber_list_eq_map i j tl

(* Counting perm_eq matches in fiber_list: case p.fwd i ≠ j. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let rec fiber_list_count_ne (#n: pos) (p: permutation n)
  (i j: fin n) (xs: list (permutation (Prims.op_Subtraction n 1)))
  : Lemma (requires (p.fwd i <: nat) <> (j <: nat))
          (ensures perm_eq_count p (fiber_list i j xs) == 0)
          (decreases xs)
  = match xs with
    | [] -> 
      perm_eq_count_nil p
    | hd :: xs' ->
        let injected = inject hd i j in
        let fl = fiber_list i j xs' in
        perm_eq_inject_false p hd i j;
        perm_eq_count_cons p injected fl;
        fiber_list_count_ne p i j xs'
#pop-options

(* Counting perm_eq matches in fiber_list: case p.fwd i == j. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec fiber_list_count_eq (#n: pos) (p: permutation n)
  (i j: fin n) (xs: list (permutation (Prims.op_Subtraction n 1)))
  : Lemma (requires (p.fwd i <: nat) == (j <: nat))
          (ensures perm_eq_count p (fiber_list i j xs) ==
                   perm_eq_count (project p i) xs)
          (decreases xs)
  = match xs with
    | [] -> 
      perm_eq_count_nil p;
      perm_eq_count_nil (project p i)
    | hd :: xs' ->
        let injected = inject hd i j in
        let fl = fiber_list i j xs' in
        perm_eq_count_cons p injected fl;
        perm_eq_count_cons (project p i) hd xs';
        perm_eq_inject_match p hd i j;
        fiber_list_count_eq p i j xs'
#pop-options

(* Each fiber has count 0 or 1. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let fiber_count (#n: pos) (p: permutation n) (i j: fin n)
  : Lemma (perm_eq_count p (fiber_list i j (all_permutations (Prims.op_Subtraction n 1))) ==
           (if (p.fwd i <: nat) = (j <: nat) then 1 else 0))
  = let nm1 = Prims.op_Subtraction n 1 in
    if (p.fwd i <: nat) = (j <: nat) then begin
      fiber_list_count_eq p i j (all_permutations nm1);
      all_permutations_count_one nm1 (project p i)
    end else
      fiber_list_count_ne p i j (all_permutations nm1)
#pop-options

(* Build concatenated fibers from j_lo up to n-1. *)
let rec concat_fibers_from (#n: pos) (i: fin n) (j_lo: nat{j_lo <= n})
  : Tot (list (permutation n)) (decreases (Prims.op_Subtraction n j_lo))
  = if j_lo >= n then []
    else L.append
           (fiber_list i (j_lo <: fin n) (all_permutations (Prims.op_Subtraction n 1)))
           (concat_fibers_from i (Prims.op_Addition j_lo 1))

let concat_fibers (#n: pos) (i: fin n) : list (permutation n)
  = concat_fibers_from i 0

(* Count in concatenated fibers equals 1 for every permutation. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 70"
let rec concat_fibers_from_count (#n: pos) (p: permutation n)
  (i: fin n) (j_lo: nat{j_lo <= n})
  : Lemma (ensures perm_eq_count p (concat_fibers_from i j_lo) ==
                   (if (p.fwd i <: nat) >= j_lo then 1 else 0))
          (decreases (Prims.op_Subtraction n j_lo))
  = if j_lo >= n then perm_eq_count_nil p
    else begin
      let fl = fiber_list i (j_lo <: fin n)
                 (all_permutations (Prims.op_Subtraction n 1)) in
      let rest = concat_fibers_from i (Prims.op_Addition j_lo 1) in
      perm_eq_count_append p fl rest;
      fiber_count p i (j_lo <: fin n);
      concat_fibers_from_count p i (Prims.op_Addition j_lo 1)
    end
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
let concat_fibers_count_one (#n: pos) (p: permutation n) (i: fin n)
  : Lemma (perm_eq_count p (concat_fibers i) == 1)
  = concat_fibers_from_count p i 0
#pop-options

(* Named per-fiber function to avoid lambda-matching issues. *)
let per_fiber_fn (#t: Type) {| m: add_comm_monoid t |}
  (#n: pos) (f: permutation n -> t) (i j: fin n)
  (sp: permutation (Prims.op_Subtraction n 1)) : t
  = f (inject_at i j sp)

(* sum_list (map f (fiber_list i j xs)) = sum_list (map (per_fiber_fn f i j) xs).
   Uses per_fiber_fn (named function) to avoid anonymous lambdas that Z3 can't match. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let fiber_list_sum (#t: Type) {| m: add_comm_monoid t |}
  (#n: pos) (f: permutation n -> t) (i j: fin n)
  (xs: list (permutation (Prims.op_Subtraction n 1)))
  : Lemma (ensures sum_list (L.map f (fiber_list i j xs)) =
                   sum_list (L.map (per_fiber_fn #t #m f i j) xs))
  = fiber_list_eq_map i j xs;
    map_map_eq (inject_at i j) f xs;
    (* map_map_eq gives: L.map f (L.map (inject_at i j) xs) == L.map (fun sp -> f (inject_at i j sp)) xs
       per_fiber_fn f i j sp == f (inject_at i j sp) definitionally, so bridge via sum_list_map_congruence *)
    let pfn = per_fiber_fn #t #m f i j in
    let eq_pw (sp: permutation (Prims.op_Subtraction n 1))
      : Lemma (requires L.memP sp xs) (ensures pfn sp = (fun (sp': permutation (Prims.op_Subtraction n 1)) -> f (inject_at i j sp')) sp)
      = reflexivity (pfn sp)
    in Classical.forall_intro (Classical.move_requires eq_pw);
    sum_list_map_congruence pfn (fun (sp: permutation (Prims.op_Subtraction n 1)) -> f (inject_at i j sp)) xs;
    (* sum_list (L.map pfn xs) = sum_list (L.map (fun sp -> ...) xs) *)
    (* And fiber_list_eq_map + map_map_eq give: L.map f (fiber_list i j xs) == L.map (fun sp -> ...) xs *)
    (* So sum_list (L.map f (fiber_list i j xs)) == sum_list (L.map (fun sp -> ...) xs) = sum_list (L.map pfn xs) *)
    symmetry (sum_list (L.map pfn xs))
             (sum_list (L.map (fun (sp: permutation (Prims.op_Subtraction n 1)) -> f (inject_at i j sp)) xs));
    reflexivity (sum_list (L.map f (fiber_list i j xs)))
#pop-options

(* Connect sum_list of fiber_list to sum_over_perms via per_fiber_fn. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let fiber_list_to_sum_over_perms (#t: Type) {| m: add_comm_monoid t |}
  (#n: pos) (f: permutation n -> t) (i j: fin n)
  : Lemma (requires respects_perm_eq f)
          (ensures sum_list (L.map f (fiber_list i j (all_permutations (Prims.op_Subtraction n 1)))) =
                   sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #m f i j))
  = let nm1 = Prims.op_Subtraction n 1 in
    let g = per_fiber_fn #t #m f i j in
    (* fiber_list_sum now gives: sum_list (L.map f fl) = sum_list (L.map g (all_perms nm1)) *)
    fiber_list_sum #t #m f i j (all_permutations nm1);
    (* g respects perm_eq *)
    let g_respects (s1 s2: permutation nm1)
      : Lemma (requires perm_eq s1 s2) (ensures g s1 = g s2)
      = inject_preserves_perm_eq s1 s2 i j;
        respects_perm_eq_elim f (inject s1 i j) (inject s2 i j)
    in Classical.forall_intro_2 (Classical.move_requires_2 g_respects);
    respects_perm_eq_intro g;
    let count_one (p: permutation nm1) : Lemma (perm_eq_count p (all_permutations nm1) == 1)
      = all_permutations_count_one nm1 p
    in Classical.forall_intro count_one;
    (* sum_over_perms nm1 g = sum_list (L.map g (all_perms nm1)) *)
    sum_over_perms_via_count_one_list g (all_permutations nm1);
    (* Chain: sum_list (L.map f fl) = sum_list (L.map g all) = sum_over_perms nm1 g *)
    symmetry (sum_over_perms nm1 g) (sum_list (L.map g (all_permutations nm1)));
    transitivity (sum_list (L.map f (fiber_list i j (all_permutations nm1))))
                 (sum_list (L.map g (all_permutations nm1)))
                 (sum_over_perms nm1 g)
#pop-options

(* Sum over concat_fibers_from decomposes into sum_range of sum_over_perms of fibers. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let rec concat_fibers_from_sum (#t: Type) {| m: add_comm_monoid t |}
  (#n: pos) (f: permutation n -> t) (i: fin n)
  (j_lo: nat{j_lo <= n})
  : Lemma (requires respects_perm_eq f)
          (ensures sum_list (L.map f (concat_fibers_from i j_lo)) =
                   sum_range
                     (fun (k: nat) -> if k < n then sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #m f i (k <: fin n)) else zero)
                     j_lo n)
          (decreases (Prims.op_Subtraction n j_lo))
  = let g (k: nat) : t = if k < n then sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #m f i (k <: fin n)) else zero in
    if j_lo >= n then begin
      reflexivity (zero #t)
    end else begin
      let j : fin n = j_lo in
      let nm1 = Prims.op_Subtraction n 1 in
      let fl = fiber_list i j (all_permutations nm1) in
      let rest = concat_fibers_from i (Prims.op_Addition j_lo 1) in
      L.map_append f fl rest;
      sum_list_append (L.map f fl) (L.map f rest);
      fiber_list_to_sum_over_perms #t #m f i j;
      concat_fibers_from_sum #t #m f i (Prims.op_Addition j_lo 1);
      sum_range_unfold_left g j_lo n;
      let a = sum_list (L.map f fl) in
      let b = sum_over_perms nm1 (per_fiber_fn #t #m f i j) in
      let c = sum_list (L.map f rest) in
      let d = sum_range g (Prims.op_Addition j_lo 1) n in
      add_congruence a c b d;
      transitivity (sum_list (L.map f (concat_fibers_from i j_lo)))
                   (a `( + )` c)
                   (sum_range g j_lo n)
    end
#pop-options

(* fin_sum form. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let concat_fibers_sum_eq_fin_sum (#t: Type) {| m: add_comm_monoid t |}
  (#n: pos) (f: permutation n -> t) (i: fin n)
  : Lemma (requires respects_perm_eq f)
          (ensures sum_list (L.map f (concat_fibers i)) =
                   fin_sum (fun (j: fin n) ->
                     sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #m f i j)))
  = concat_fibers_from_sum #t #m f i 0
#pop-options

(* === Main theorem: sum_over_perms_partition === *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let sum_over_perms_partition (#t: Type) {| m: add_comm_monoid t |}
  (#n: pos) (i: fin n) (f: permutation n -> t)
  : Lemma (requires respects_perm_eq f)
          (ensures sum_over_perms n f =
                   fin_sum (fun (j: fin n) ->
                     sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #m f i j)))
  = let count_one (p: permutation n)
      : Lemma (perm_eq_count p (concat_fibers i) == 1)
      = concat_fibers_count_one p i
    in Classical.forall_intro count_one;
    sum_over_perms_via_count_one_list f (concat_fibers i);
    concat_fibers_sum_eq_fin_sum #t #m f i;
    transitivity (sum_over_perms n f)
                 (sum_list (L.map f (concat_fibers i)))
                 (fin_sum (fun (j: fin n) -> sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #m f i j)))
#pop-options

(* Partition with a named target function: avoids the SMT lambda identity
   problem by threading `g` through the induction so the ensures clause
   talks about `fin_sum g` directly, never an anonymous lambda. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
private let rec concat_fibers_from_sum_target (#t: Type) {| m: add_comm_monoid t |}
  (#n: pos) (f: permutation n -> t) (i: fin n) (g: fin n -> t)
  (j_lo: nat{j_lo <= n})
  : Lemma (requires respects_perm_eq f /\
                    (forall (j: fin n). sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #m f i j) = g j))
          (ensures sum_list (L.map f (concat_fibers_from i j_lo)) =
                   sum_range
                     (fun (k: nat) -> if k < n then g (k <: fin n) else zero)
                     j_lo n)
          (decreases (Prims.op_Subtraction n j_lo))
  = let h (k: nat) : t = if k < n then g (k <: fin n) else zero in
    if j_lo >= n then begin
      reflexivity (zero #t)
    end else begin
      let j : fin n = j_lo in
      let nm1 = Prims.op_Subtraction n 1 in
      let fl = fiber_list i j (all_permutations nm1) in
      let rest = concat_fibers_from i (Prims.op_Addition j_lo 1) in
      L.map_append f fl rest;
      sum_list_append (L.map f fl) (L.map f rest);
      fiber_list_to_sum_over_perms #t #m f i j;
      concat_fibers_from_sum_target #t #m f i g (Prims.op_Addition j_lo 1);
      sum_range_unfold_left h j_lo n;
      let a = sum_list (L.map f fl) in
      let b = sum_over_perms nm1 (per_fiber_fn #t #m f i j) in
      let c = sum_list (L.map f rest) in
      let d = sum_range h (Prims.op_Addition j_lo 1) n in
      (* a = b from fiber_list_to_sum_over_perms, b = g j from requires *)
      transitivity a b (g j);
      (* g j == h j_lo propositionally (SMT knows j_lo < n),
         so a = h j_lo via auto-transitivity *)
      add_congruence a c (h j_lo) d;
      transitivity (sum_list (L.map f (concat_fibers_from i j_lo)))
                   (a `( + )` c)
                   (sum_range h j_lo n)
    end
#pop-options

(* Partition targeting a named function g, bypassing anonymous-lambda issues. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let sum_over_perms_partition_target (#t: Type) {| m: add_comm_monoid t |}
  (#n: pos) (i: fin n) (f: permutation n -> t) (g: fin n -> t)
  : Lemma (requires respects_perm_eq f /\
                    (forall (j: fin n). sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #m f i j) = g j))
          (ensures sum_over_perms n f = fin_sum g)
  = let count_one (p: permutation n)
      : Lemma (perm_eq_count p (concat_fibers i) == 1)
      = concat_fibers_count_one p i
    in Classical.forall_intro count_one;
    sum_over_perms_via_count_one_list f (concat_fibers i);
    concat_fibers_from_sum_target #t #m f i g 0;
    transitivity (sum_over_perms n f)
                 (sum_list (L.map f (concat_fibers i)))
                 (fin_sum g)
#pop-options


(* ====================================================================== *)
(*  P3: perm_product factorization through inject.                        *)
(*                                                                        *)
(*  perm_product m (inject sigma' i j) = m i j * perm_product (minor m i j) sigma'*)
(* ====================================================================== *)

(* prod_range offset lemma: if g a == f (a+lo) pointwise, then
   prod_range f lo hi = prod_range g 0 (hi-lo). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
private let rec prod_range_offset_lem
  (#t: Type) {| mm: mul_monoid t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (requires lo <= hi /\
                     (forall (a: nat). 0 <= a /\ a < Prims.op_Subtraction hi lo ==>
                        g a = f (Prims.op_Addition a lo)))
          (ensures prod_range f lo hi = prod_range g 0 (Prims.op_Subtraction hi lo))
          (decreases (Prims.op_Subtraction hi lo))
  = elim_equatable_laws t #(mm.mul_semigroup.has_mul.eq);
    transitivity_for_calc_proofs t #(mm.mul_semigroup.has_mul.eq);
    let len = Prims.op_Subtraction hi lo in
    if lo >= hi then begin
      prod_range_empty f lo hi;
      prod_range_empty g 0 0
    end else begin
      prod_range_unfold_left f lo hi;
      prod_range_unfold_left g 0 len;
      (* f lo = g 0 *)
      assert (g 0 = f (Prims.op_Addition 0 lo));
      assert (Prims.op_Addition 0 lo == lo);
      (* Recursive call: prod_range f (lo+1) hi = prod_range g' 0 (len-1)
         where g' a = g (a+1) *)
      let lo' = Prims.op_Addition lo 1 in
      let len' = Prims.op_Subtraction len 1 in
      let g' (a: nat) : t = g (Prims.op_Addition a 1) in
      let h (a: nat) : Lemma (requires 0 <= a /\ a < len')
                              (ensures g' a = f (Prims.op_Addition a lo'))
        = assert (g (Prims.op_Addition a 1) = f (Prims.op_Addition (Prims.op_Addition a 1) lo));
          assert (Prims.op_Addition (Prims.op_Addition a 1) lo == Prims.op_Addition a lo')
      in
      Classical.forall_intro (Classical.move_requires h);
      prod_range_offset_lem f g' lo' hi;
      (* prod_range f lo' hi = prod_range g' 0 len' *)
      (* prod_range g 0 len == g 0 * prod_range g (nat_succ 0) len *)
      (* Need: prod_range g (nat_succ 0) len = prod_range g' 0 len' *)
      prod_range_offset_lem g g' (nat_succ 0) len;
      assert (Prims.op_Subtraction len (nat_succ 0) == len');
      (* Now chain *)
      reflexivity (g 0);
      mul_congruence (g 0) (prod_range g (nat_succ 0) len)
                     (g 0) (prod_range g' 0 len');
      symmetry (prod_range g 0 len)
               (g 0 * prod_range g (nat_succ 0) len);
      transitivity (prod_range g 0 len)
                   (g 0 * prod_range g (nat_succ 0) len)
                   (g 0 * prod_range g' 0 len');
      symmetry (prod_range f lo' hi) (prod_range g' 0 len');
      mul_congruence (g 0) (prod_range g' 0 len')
                     (g 0) (prod_range f lo' hi);
      transitivity (prod_range g 0 len)
                   (g 0 * prod_range g' 0 len')
                   (g 0 * prod_range f lo' hi);
      symmetry (g 0) (f lo);
      mul_congruence (g 0) (prod_range f lo' hi)
                     (f lo) (prod_range f lo' hi);
      transitivity (prod_range g 0 len)
                   (g 0 * prod_range f lo' hi)
                   (f lo * prod_range f lo' hi);
      symmetry (prod_range f lo hi) (f lo * prod_range f lo' hi);
      transitivity (prod_range g 0 len)
                   (f lo * prod_range f lo' hi)
                   (prod_range f lo hi);
      symmetry (prod_range g 0 len) (prod_range f lo hi)
    end
#pop-options

(* Bridge lemma: prod_range of a body function = perm_product,
   given pointwise equality on [0, n). Avoids local let-bindings of type
   mul_monoid t that would pollute TC resolution. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let prod_range_eq_perm_product (#t: Type) {| r: ring t |} (#n: nat)
  (m: square_matrix t n) (p: permutation n) (body: nat -> t)
  : Lemma (requires forall (k: nat). 0 <= k /\ k < n ==> body k = m (k <: fin n) (p.fwd (k <: fin n)))
          (ensures prod_range body 0 n = perm_product m p)
  = elim_equatable_laws t;
    let pp_body (k: nat) : t =
      if k < n then m (k <: fin n) (p.fwd (k <: fin n)) else one in
    let pw (k: nat) : Lemma (0 <= k /\ k < n ==> body k = pp_body k)
      = if k >= 0 && k < n then () in
    Classical.forall_intro pw;
    prod_range_congruence body pp_body 0 n;
    perm_product_unfold m p
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 160"
let perm_product_inject_factor
  (#t: Type) {| r: ring t |} (#n: pos)
  (m: square_matrix t n) (sigma': permutation (Prims.op_Subtraction n 1)) (i j: fin n)
  (mul_comm: (a:t -> b:t -> Lemma (a * b = b * a)))
  : Lemma (perm_product m (inject sigma' i j)
           = m i j * perm_product (minor m i j) sigma')
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    let nm1 = Prims.op_Subtraction n 1 in
    let ip1 = Prims.op_Addition (i <: nat) 1 in
    let sigma = inject sigma' i j in
    perm_product_unfold m sigma;
    perm_product_unfold (minor m i j) sigma';
    (* Define bodies matching perm_product_unfold's lambda exactly.
       IMPORTANT: use sigma (= inject sigma' i j) not (inject sigma' i j) inline,
       so the closure matches perm_product's internal lambda which captures its p parameter. *)
    let body_big (k: nat) : t =
      if k < n then m (k <: fin n) (sigma.fwd (k <: fin n)) else one in
    let body_small (a: nat) : t =
      if a < nm1
      then (minor m i j) (a <: fin nm1) (sigma'.fwd (a <: fin nm1))
      else one in
    (* Step 1: Split prod_range body_big 0 n at position i *)
    prod_range_shape_at #t #r.semiring.mul_monoid body_big 0 n (i <: nat);
    (* Step 2: body_big i = m i j *)
    inject_fwd_at_i sigma' i j;
    assert (body_big (i <: nat) == m i j);
    (* Step 3: Left piece: prod_range body_big 0 i = prod_range body_small 0 i *)
    let h_left (k: nat) : Lemma (requires 0 <= k /\ k < (i <: nat))
                                 (ensures body_big k = body_small k)
      = let kf : fin n = k in
        inject_fwd_off sigma' i j kf;
        let a : fin nm1 = unskip i kf in
        assert ((a <: nat) == (k <: nat));
        minor_at m i j a (sigma'.fwd a);
        skip_lt i a;
        reflexivity (m kf (skip j (sigma'.fwd a)))
    in
    Classical.forall_intro (Classical.move_requires h_left);
    prod_range_congruence #t #r.semiring.mul_monoid body_big body_small 0 (i <: nat);
    (* Step 4: Right piece: prod_range body_big ip1 n = prod_range body_small i nm1 *)
    let shifted_big (a: nat) : t = body_big (Prims.op_Addition a ip1) in
    let shifted_small (a: nat) : t = body_small (Prims.op_Addition a (i <: nat)) in
    let len = Prims.op_Subtraction nm1 (i <: nat) in
    let h_right (a: nat) : Lemma (requires 0 <= a /\ a < len)
                                  (ensures shifted_big a = shifted_small a)
      = let k : nat = Prims.op_Addition a ip1 in
        let kf : fin n = k in
        inject_fwd_off sigma' i j kf;
        let u : fin nm1 = unskip i kf in
        assert ((u <: nat) == Prims.op_Subtraction k 1);
        assert ((u <: nat) == Prims.op_Addition a (i <: nat));
        minor_at m i j u (sigma'.fwd u);
        skip_ge i u;
        assert ((skip i u <: nat) == Prims.op_Addition u 1);
        assert ((skip i u <: nat) == k);
        reflexivity (m kf (skip j (sigma'.fwd u)))
    in
    Classical.forall_intro (Classical.move_requires h_right);
    prod_range_congruence #t #r.semiring.mul_monoid shifted_big shifted_small 0 len;
    let h_big_offset (a: nat) : Lemma (requires 0 <= a /\ a < len)
                                       (ensures shifted_big a = body_big (Prims.op_Addition a ip1))
      = reflexivity (shifted_big a)
    in
    Classical.forall_intro (Classical.move_requires h_big_offset);
    prod_range_offset_lem #t #r.semiring.mul_monoid body_big shifted_big ip1 n;
    let h_small_offset (a: nat) : Lemma (requires 0 <= a /\ a < len)
                                         (ensures shifted_small a = body_small (Prims.op_Addition a (i <: nat)))
      = reflexivity (shifted_small a)
    in
    Classical.forall_intro (Classical.move_requires h_small_offset);
    prod_range_offset_lem #t #r.semiring.mul_monoid body_small shifted_small (i <: nat) nm1;
    assert (Prims.op_Subtraction n ip1 == len);
    assert (Prims.op_Subtraction nm1 (i <: nat) == len);
    transitivity (prod_range body_big ip1 n)
                 (prod_range shifted_big 0 len)
                 (prod_range shifted_small 0 len);
    symmetry (prod_range body_small (i <: nat) nm1)
             (prod_range shifted_small 0 len);
    transitivity (prod_range body_big ip1 n)
                 (prod_range shifted_small 0 len)
                 (prod_range body_small (i <: nat) nm1);
    (* Name the pieces *)
    let lp = prod_range body_big 0 (i <: nat) in
    let slp = prod_range body_small 0 (i <: nat) in
    let rp = prod_range body_big ip1 n in
    let srp = prod_range body_small (i <: nat) nm1 in
    assert (lp = slp);
    assert (rp = srp);
    (* Step 5: Reassemble *)
    prod_range_split #t #r.semiring.mul_monoid body_small 0 (i <: nat) nm1;
    symmetry (prod_range body_small 0 nm1) (slp * srp);
    (* Commutativity rearrangement *)
    reflexivity (m i j);
    mul_congruence (m i j) rp (m i j) srp;
    mul_congruence lp (m i j * rp) slp (m i j * srp);
    mul_associativity slp (m i j) srp;
    symmetry ((slp * m i j) * srp) (slp * (m i j * srp));
    mul_comm slp (m i j);
    reflexivity srp;
    mul_congruence (slp * m i j) srp (m i j * slp) srp;
    mul_associativity (m i j) slp srp;
    trans_lemma [ slp * (m i j * srp);
                  (slp * m i j) * srp;
                  (m i j * slp) * srp;
                  m i j * (slp * srp) ];
    reflexivity (m i j);
    mul_congruence (m i j) (slp * srp) (m i j) (prod_range body_small 0 nm1);
    transitivity (slp * (m i j * srp))
                 (m i j * (slp * srp))
                 (m i j * prod_range body_small 0 nm1);
    (* Chain prod_range body_big 0 n -> m i j * prod_range body_small 0 nm1 *)
    transitivity (prod_range body_big 0 n)
                 (lp * (m i j * rp))
                 (slp * (m i j * srp));
    transitivity (prod_range body_big 0 n)
                 (slp * (m i j * srp))
                 (m i j * prod_range body_small 0 nm1);
    (* Bridge body_big -> perm_product m sigma *)
    let h_bb (k: nat) : Lemma (0 <= k /\ k < n ==> body_big k = m (k <: fin n) (sigma.fwd (k <: fin n)))
      = if k >= 0 && k < n then reflexivity (body_big k) in
    Classical.forall_intro h_bb;
    prod_range_eq_perm_product m sigma body_big;
    (* Bridge body_small -> perm_product (minor m i j) sigma' *)
    let h_bs (k: nat) : Lemma (0 <= k /\ k < nm1 ==> body_small k = (minor m i j) (k <: fin nm1) (sigma'.fwd (k <: fin nm1)))
      = if k >= 0 && k < nm1 then reflexivity (body_small k) in
    Classical.forall_intro h_bs;
    prod_range_eq_perm_product (minor m i j) sigma' body_small;
    (* Now: prod_range body_big 0 n = perm_product m sigma
            prod_range body_small 0 nm1 = perm_product (minor m i j) sigma'
            prod_range body_big 0 n = m i j * prod_range body_small 0 nm1  (from the chain)
       So:  perm_product m sigma = m i j * perm_product (minor m i j) sigma' *)
    symmetry (prod_range body_big 0 n) (perm_product m sigma);
    symmetry (prod_range body_small 0 nm1) (perm_product (minor m i j) sigma');
    reflexivity (m i j);
    mul_congruence (m i j) (prod_range body_small 0 nm1) (m i j) (perm_product (minor m i j) sigma');
    (* Chain the full postcondition *)
    transitivity (prod_range body_big 0 n)
                 (m i j * prod_range body_small 0 nm1)
                 (m i j * perm_product (minor m i j) sigma');
    trans_lemma [ perm_product m sigma;
                  prod_range body_big 0 n;
                  m i j * prod_range body_small 0 nm1;
                  m i j * perm_product (minor m i j) sigma' ]
#pop-options

(* ====================================================================== *)(*  P4 helper: leibniz_inject_factor                                      *)
(*                                                                        *)
(*  leibniz_term m (inject sigma' i j)                                    *)
(*    = minus_one_pow(i+j) * m i j * leibniz_term (minor m i j) sigma'    *)
(* ====================================================================== *)

(* minus_one_pow squared = one *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
private let minus_one_pow_square (#t: Type) {| r: ring t |} (k: nat)
  : Lemma (minus_one_pow #t k * minus_one_pow #t k = one)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if Prims.op_Modulus k 2 = 0 then begin
      minus_one_pow_even #t #r k;
      left_mul_identity (one #t)
    end else begin
      minus_one_pow_odd #t #r k;
      (* (-one) * (-one) = -(-(one)) = one *)
      let acg : add_comm_group t = add_comm_group_of_ring t r in
      ring_neg_x_is_minus_one_times_x (-(one #t));
      symmetry (-(-(one #t))) ((-(one #t)) * (-(one #t)));
      double_negation_lemma #t #acg.add_group (one #t);
      transitivity ((-(one #t)) * (-(one #t)))
                   (-(-(one #t)))
                   (one #t)
    end
#pop-options

(* Combine P1 and P3 into the signed factorization:
   leibniz_term m (inject sigma' i j) = minus_one_pow(i+j) * m i j * leibniz_term (minor m i j) sigma' *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let leibniz_inject_factor
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (sigma': permutation (Prims.op_Subtraction n 1)) (i j: fin n)
  : Lemma (leibniz_term m (inject sigma' i j)
           = minus_one_pow #t #cr.ring (Prims.op_Addition (i <: nat) (j <: nat))
             * m i j
             * leibniz_term #t #cr.ring (minor m i j) sigma')
  = let r : ring t = cr.ring in
    let acg : add_comm_group t = add_comm_group_of_ring t r in
    elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    let nm1 = Prims.op_Subtraction n 1 in
    let sigma = inject sigma' i j in
    let ij = Prims.op_Addition (i <: nat) (j <: nat) in
    (* P1: parity (inject sigma' i j) = (parity sigma' = ((i+j) % 2 = 0)) *)
    parity_inject sigma' i j;
    (* P3: perm_product m sigma = m i j * perm_product (minor m i j) sigma' *)
    perm_product_inject_factor #t #r #n m sigma' i j
      cr.mul_comm_monoid.mul_comm_semigroup.mul_comm_magma.mul_commutativity;
    let pp = perm_product m sigma in
    let pp_min = perm_product #t #r (minor m i j) sigma' in
    assert (pp = m i j * pp_min);
    (* leibniz_term m sigma = if parity sigma then pp else -pp *)
    let lhs = leibniz_term m sigma in
    let sign_sp = parity sigma' in
    let ij_even = (Prims.op_Modulus ij 2 = 0) in
    let mop = minus_one_pow #t #r ij in
    (* Case split on sign_sp and ij_even *)
    if sign_sp then begin
      if ij_even then begin
        (* sign_sigma = true, mop = one, lhs = pp, lt_min = pp_min *)
        minus_one_pow_even #t #r ij;
        assert (lhs == pp);
        assert (leibniz_term #t #r (minor m i j) sigma' == pp_min);
        (* Chain: mop * m i j * pp_min → mop * (m i j * pp_min) → one * (m i j * pp_min) → m i j * pp_min → pp *)
        mul_associativity mop (m i j) pp_min;
        reflexivity (m i j * pp_min);
        mul_congruence mop (m i j * pp_min) (one #t) (m i j * pp_min);
        left_mul_identity (m i j * pp_min);
        symmetry pp (m i j * pp_min);
        trans_lemma [ mop * m i j * pp_min;
                      mop * (m i j * pp_min);
                      one * (m i j * pp_min);
                      m i j * pp_min;
                      pp ]
      end else begin
        (* sign_sigma = false, mop = -(one), lhs = -pp, lt_min = pp_min *)
        minus_one_pow_odd #t #r ij;
        assert (lhs == -pp);
        assert (leibniz_term #t #r (minor m i j) sigma' == pp_min);
        (* Chain: mop * m i j * pp_min → mop * (m i j * pp_min) → (-(one)) * (m i j * pp_min) → -(m i j * pp_min) → -pp *)
        mul_associativity mop (m i j) pp_min;
        reflexivity (m i j * pp_min);
        mul_congruence mop (m i j * pp_min) (-(one #t)) (m i j * pp_min);
        ring_neg_x_is_minus_one_times_x (m i j * pp_min);
        symmetry (-(m i j * pp_min)) ((-(one #t)) * (m i j * pp_min));
        neg_congruence_lem #t #acg pp (m i j * pp_min);
        symmetry (-pp) (-(m i j * pp_min));
        trans_lemma [ mop * m i j * pp_min;
                      mop * (m i j * pp_min);
                      (-(one #t)) * (m i j * pp_min);
                      -(m i j * pp_min);
                      -pp ]
      end
    end else begin
      if ij_even then begin
        (* sign_sigma = false, mop = one, lhs = -pp, lt_min = -pp_min *)
        minus_one_pow_even #t #r ij;
        assert (lhs == -pp);
        assert (leibniz_term #t #r (minor m i j) sigma' == -pp_min);
        let lt_min = -pp_min in
        (* Chain: mop * m i j * lt_min → mop * (m i j * lt_min) → one * (m i j * lt_min) → m i j * lt_min *)
        mul_associativity mop (m i j) lt_min;
        reflexivity (m i j * lt_min);
        mul_congruence mop (m i j * lt_min) (one #t) (m i j * lt_min);
        left_mul_identity (m i j * lt_min);
        trans_lemma [ mop * m i j * lt_min;
                      mop * (m i j * lt_min);
                      one * (m i j * lt_min);
                      m i j * lt_min ];
        (* Now show m i j * lt_min = m i j * (-pp_min) = -(m i j * pp_min) = -pp *)
        ring_neg_xy_is_x_times_neg_y (m i j) pp_min;
        symmetry (-(m i j * pp_min)) (m i j * lt_min);
        neg_congruence_lem #t #acg pp (m i j * pp_min);
        symmetry (-pp) (-(m i j * pp_min));
        trans_lemma [ mop * m i j * lt_min;
                      m i j * lt_min;
                      -(m i j * pp_min);
                      -pp ]
      end else begin
        (* sign_sigma = true, mop = -(one), lhs = pp, lt_min = -pp_min *)
        minus_one_pow_odd #t #r ij;
        assert (lhs == pp);
        assert (leibniz_term #t #r (minor m i j) sigma' == -pp_min);
        let lt_min = -pp_min in
        (* Chain: mop * m i j * lt_min → mop * (m i j * lt_min) → (-(one)) * (m i j * lt_min)
           → -(m i j * lt_min) → -(-(m i j * pp_min)) → m i j * pp_min → pp *)
        mul_associativity mop (m i j) lt_min;
        reflexivity (m i j * lt_min);
        mul_congruence mop (m i j * lt_min) (-(one #t)) (m i j * lt_min);
        ring_neg_x_is_minus_one_times_x (m i j * lt_min);
        symmetry (-(m i j * lt_min)) ((-(one #t)) * (m i j * lt_min));
        ring_neg_xy_is_x_times_neg_y (m i j) pp_min;
        symmetry (-(m i j * pp_min)) (m i j * lt_min);
        neg_congruence_lem #t #acg (m i j * lt_min) (-(m i j * pp_min));
        double_negation_lemma #t #acg.add_group (m i j * pp_min);
        symmetry pp (m i j * pp_min);
        trans_lemma [ mop * m i j * lt_min;
                      mop * (m i j * lt_min);
                      (-(one #t)) * (m i j * lt_min);
                      -(m i j * lt_min) ];
        trans_lemma [ -(m i j * lt_min);
                      -(-(m i j * pp_min));
                      m i j * pp_min;
                      pp ];
        transitivity (mop * m i j * lt_min) (-(m i j * lt_min)) pp
      end
    end
#pop-options

(* ====================================================================== *)
(*  P4: det_laplace_row -- Laplace expansion along row i.                 *)
(*                                                                        *)
(*    det m = fin_sum (fun j -> (-1)^(i+j) * m(i,j) * det(minor m i j))  *)
(* ====================================================================== *)

(* Module-level cofactor function — avoids anonymous-lambda identity issues *)
let cofactor_term (#t: Type) {| r: ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n) : t
  = minus_one_pow #t #r (Prims.op_Addition (i <: nat) (j <: nat))
    * m i j
    * det #t #r #(Prims.op_Subtraction n 1) (minor m i j)

(* Helper: the per-fiber sum equals the cofactor expansion term. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let inner_sum_eq_cofactor
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (
      let r : ring t = cr.ring in
      let sr : semiring t = r.semiring in
      sum_over_perms (Prims.op_Subtraction n 1)
        (per_fiber_fn #t #cr.ring.add_comm_group.add_comm_monoid (leibniz_term m) i j)
      = minus_one_pow #t #r (Prims.op_Addition (i <: nat) (j <: nat))
        * m i j
        * det #t #r #(Prims.op_Subtraction n 1) (minor m i j))
  = let r : ring t = cr.ring in
    let sr : semiring t = r.semiring in
    let acg : add_comm_group t = add_comm_group_of_ring t r in
    let acm : add_comm_monoid t = acg.add_comm_monoid in
    elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    let nm1 = Prims.op_Subtraction n 1 in
    let ij = Prims.op_Addition (i <: nat) (j <: nat) in
    let mop = minus_one_pow #t #r ij in
    let f = per_fiber_fn #t #acm (leibniz_term m) i j in
    (* f sp = leibniz_term m (inject sp i j) *)
    (* = mop * m i j * leibniz_term (minor m i j) sp  by leibniz_inject_factor *)
    let g (sp: permutation nm1) : t
      = mop * m i j * leibniz_term #t #r (minor m i j) sp in
    let pw (sp: permutation nm1) : Lemma (f sp = g sp)
      = leibniz_inject_factor #t #cr #n m sp i j
    in
    Classical.forall_intro pw;
    sum_over_perms_congruence nm1 f g;
    (* sum_over_perms nm1 g = mop * m i j * sum_over_perms nm1 (leibniz_term (minor m i j)) *)
    let c = mop * m i j in
    let h = leibniz_term #t #r #nm1 (minor m i j) in
    (* g sp = c * h sp, so sum g = c * sum h *)
    let pw2 (sp: permutation nm1) : Lemma (g sp = c * h sp)
      = mul_associativity mop (m i j) (h sp)
    in
    Classical.forall_intro pw2;
    sum_over_perms_congruence nm1 g (fun sp -> c * h sp);
    sum_over_perms_mul_left #t #sr nm1 c h;
    symmetry (c * sum_over_perms nm1 h) (sum_over_perms nm1 (fun sp -> c * h sp));
    transitivity (sum_over_perms nm1 g)
                 (sum_over_perms nm1 (fun sp -> c * h sp))
                 (c * sum_over_perms nm1 h);
    transitivity (sum_over_perms nm1 f) (sum_over_perms nm1 g)
                 (c * sum_over_perms nm1 h);
    (* sum_over_perms nm1 h = det (minor m i j) *)
    det_unfold #t #r #nm1 (minor m i j);
    symmetry (det #t #r (minor m i j)) (sum_over_perms nm1 h);
    reflexivity c;
    mul_congruence c (sum_over_perms nm1 h) c (det #t #r (minor m i j));
    transitivity (sum_over_perms nm1 f) (c * sum_over_perms nm1 h)
                 (c * det #t #r (minor m i j));
    (* c * det = mop * m i j * det, which is the same as c * det *)
    reflexivity (c * det #t #r (minor m i j))
#pop-options

(* Main theorem: Laplace expansion along row i. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 160"
let det_laplace_row
  (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (m: square_matrix t n) (i: fin n)
  : Lemma (det #t #cr.ring #n m =
           fin_sum #t #cr.ring.add_comm_group.add_comm_monoid #n
             (cofactor_term #t #cr.ring m i))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    leibniz_term_respects_perm_eq #t #cr.ring #n m;
    let pw (j: fin n) : Lemma (
      sum_over_perms (Prims.op_Subtraction n 1)
        (per_fiber_fn #t #cr.ring.add_comm_group.add_comm_monoid (leibniz_term m) i j)
      = cofactor_term #t #cr.ring m i j)
      = inner_sum_eq_cofactor #t #cr #n m i j
    in
    Classical.forall_intro pw;
    sum_over_perms_partition_target #t #cr.ring.add_comm_group.add_comm_monoid #n
      i (leibniz_term m) (cofactor_term #t #cr.ring m i);
    det_unfold m;
    transitivity (det m)
                 (sum_over_perms n (leibniz_term m))
                 (fin_sum #t #cr.ring.add_comm_group.add_comm_monoid
                   (cofactor_term #t #cr.ring m i))
#pop-options