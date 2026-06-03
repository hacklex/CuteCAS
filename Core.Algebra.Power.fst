module Core.Algebra.Power

(* ================================================================ *)
(*  Ring power  x^n  and the BINOMIAL THEOREM in a commutative      *)
(*  ring, with the integer binomial coefficients carried by         *)
(*  `nat_scale` (n-fold repeated addition).                          *)
(*                                                                   *)
(*      (a + b)^n = Σ_{k=0}^{n}  C(n,k) · a^{n-k} · b^k             *)
(*                                                                   *)
(*  This is the field-agnostic engine behind Frobenius additivity   *)
(*  (Core.Algebra.Frobenius): over characteristic p the middle      *)
(*  terms vanish because p | C(p,k).                                 *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module NB = Core.NatBinomial

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Polynomial.Derivative   (* nat_scale + its laws *)
open Core.FinSum

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------- *)
(*  Ring power                                                      *)
(* ---------------------------------------------------------------- *)

let rec rpow (#t:Type) {| r: ring t |} (x: t) (n: nat) : t =
  if n = 0 then one else x * rpow x (n - 1)

let rpow_zero (#t:Type) {| r: ring t |} (x: t)
  : Lemma (rpow x 0 == one) = ()

let rpow_succ (#t:Type) {| r: ring t |} (x: t) (n: nat)
  : Lemma (rpow x (Prims.op_Addition n 1) == x * rpow x n) = ()

(* ---------------------------------------------------------------- *)
(*  The binomial summand:  C(n,k) · ( a^{n-k} · b^k )               *)
(* ---------------------------------------------------------------- *)

let bterm (#t:Type) {| cr: commutative_ring t |} (a b: t) (n k: nat) : t =
  nat_scale #t #(cr.cr_r.r_add) (NB.binom n k)
            (rpow a (if k <= n then n - k else 0) * rpow b k)

(* a * (a^i * b^k) = a^(i+1) * b^k *)
let pull_a (#t:Type) {| cr: commutative_ring t |} (a b: t) (i k: nat)
  : Lemma (a * (rpow a i * rpow b k) = rpow a (Prims.op_Addition i 1) * rpow b k)
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    mul_associativity a (rpow a i) (rpow b k);
    assert (a * rpow a i == rpow a (Prims.op_Addition i 1));
    reflexivity (rpow b k);
    mul_congruence (a * rpow a i) (rpow b k) (rpow a (Prims.op_Addition i 1)) (rpow b k)

(* b * (a^i * b^k) = a^i * b^(k+1) *)
let pull_b (#t:Type) {| cr: commutative_ring t |} (a b: t) (i k: nat)
  : Lemma (b * (rpow a i * rpow b k) = rpow a i * rpow b (Prims.op_Addition k 1))
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    let ai = rpow a i in let bk = rpow b k in
    H.mul_commutativity_cr b (ai * bk);
    mul_associativity ai bk b;
    H.mul_commutativity_cr bk b;
    assert (b * bk == rpow b (Prims.op_Addition k 1));
    reflexivity ai;
    H.trans2 (bk * b) (b * bk) (rpow b (Prims.op_Addition k 1));
    mul_congruence ai (bk * b) ai (rpow b (Prims.op_Addition k 1));
    H.trans3 (b * (ai * bk)) ((ai * bk) * b) (ai * (bk * b)) (ai * rpow b (Prims.op_Addition k 1))

(* a * bterm(n-1,k) = C(n-1,k) · (a^{n-k} · b^k) *)
let a_times_bterm (#t:Type) {| cr: commutative_ring t |} (a b: t) (n:nat{n>=1}) (k:nat{k <= n-1})
  : Lemma (a * bterm a b (n-1) k
           = nat_scale #t #(cr.cr_r.r_add) (NB.binom (n-1) k) (rpow a (n-k) * rpow b k))
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    let c = NB.binom (n-1) k in
    let i = n-1-k in
    assert (bterm a b (n-1) k == nat_scale #t #(cr.cr_r.r_add) c (rpow a i * rpow b k));
    nat_scale_mul_right #t #cr c a (rpow a i * rpow b k);
    pull_a #t #cr a b i k;
    assert (Prims.op_Addition i 1 == n-k);
    nat_scale_congruence #t #(cr.cr_r.r_add) c
        (a * (rpow a i * rpow b k)) (rpow a (n-k) * rpow b k);
    H.trans2 (a * bterm a b (n-1) k)
             (nat_scale #t #(cr.cr_r.r_add) c (a * (rpow a i * rpow b k)))
             (nat_scale #t #(cr.cr_r.r_add) c (rpow a (n-k) * rpow b k))

(* b * bterm(n-1,k-1) = C(n-1,k-1) · (a^{n-k} · b^k) *)
let b_times_bterm (#t:Type) {| cr: commutative_ring t |} (a b: t) (n:nat{n>=1}) (k:nat{1 <= k /\ k <= n})
  : Lemma (b * bterm a b (n-1) (k-1)
           = nat_scale #t #(cr.cr_r.r_add) (NB.binom (n-1) (k-1)) (rpow a (n-k) * rpow b k))
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    let c = NB.binom (n-1) (k-1) in
    let i = n-k in
    assert ((n-1)-(k-1) == i);
    assert (bterm a b (n-1) (k-1) == nat_scale #t #(cr.cr_r.r_add) c (rpow a i * rpow b (k-1)));
    nat_scale_mul_right #t #cr c b (rpow a i * rpow b (k-1));
    pull_b #t #cr a b i (k-1);
    assert (Prims.op_Addition (k-1) 1 == k);
    nat_scale_congruence #t #(cr.cr_r.r_add) c
        (b * (rpow a i * rpow b (k-1))) (rpow a i * rpow b k);
    H.trans2 (b * bterm a b (n-1) (k-1))
             (nat_scale #t #(cr.cr_r.r_add) c (b * (rpow a i * rpow b (k-1))))
             (nat_scale #t #(cr.cr_r.r_add) c (rpow a i * rpow b k))

(* the per-term Pascal recurrence:
   a·bterm(n-1,k) + b·bterm(n-1,k-1) = bterm(n,k)   for 1<=k<=n-1. *)
let bterm_pascal (#t:Type) {| cr: commutative_ring t |} (a b: t) (n:nat{n>=2}) (k:nat{1 <= k /\ k <= n-1})
  : Lemma (a * bterm a b (n-1) k + b * bterm a b (n-1) (k-1) = bterm a b n k)
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    let acg = cr.cr_r.r_add in
    let x : t = rpow a (n-k) * rpow b k in
    let c1 = NB.binom (n-1) k in
    let c2 = NB.binom (n-1) (k-1) in
    a_times_bterm #t #cr a b n k;     (* a*bterm(n-1,k)   = nat_scale c1 x *)
    b_times_bterm #t #cr a b n k;     (* b*bterm(n-1,k-1) = nat_scale c2 x *)
    (* sum of the two nat_scale terms *)
    add_congruence (a * bterm a b (n-1) k) (b * bterm a b (n-1) (k-1))
                   (nat_scale #t #acg c1 x) (nat_scale #t #acg c2 x);
    (* nat_scale c1 x + nat_scale c2 x = nat_scale (c1+c2) x *)
    nat_scale_add #t #acg c1 c2 x;    (* nat_scale (c1+c2) x = ns c1 x + ns c2 x *)
    symmetry (nat_scale #t #acg (Prims.op_Addition c1 c2) x)
             (nat_scale #t #acg c1 x + nat_scale #t #acg c2 x);
    (* c1 + c2 = C(n,k) by Pascal *)
    NB.pascal (n-1) k;                (* C(n-1,k) + C(n-1,k-1) = C(n,k) *)
    assert (Prims.op_Addition c1 c2 == NB.binom n k);
    (* bterm a b n k = nat_scale C(n,k) x  (since k<=n, the if picks n-k) *)
    assert (bterm a b n k == nat_scale #t #acg (NB.binom n k) x);
    H.trans3 (a * bterm a b (n-1) k + b * bterm a b (n-1) (k-1))
             (nat_scale #t #acg c1 x + nat_scale #t #acg c2 x)
             (nat_scale #t #acg (Prims.op_Addition c1 c2) x)
             (bterm a b n k)

(* nat_scale 1 (z) = z ; and bterm at the "all-a" / "all-b" corners. *)

(* bterm n 0 = a^n   (C(n,0)=1, b^0 = one) *)
let bterm_corner_0 (#t:Type) {| cr: commutative_ring t |} (a b: t) (n:nat)
  : Lemma (bterm a b n 0 = rpow a n)
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    let acg = cr.cr_r.r_add in
    (* bterm n 0 = nat_scale 1 (a^n * b^0) = a^n * one *)
    NB.binom_0 n;                                  (* binom n 0 = 1 *)
    assert (bterm a b n 0 == nat_scale #t #acg 1 (rpow a n * rpow b 0));
    nat_scale_one #t #acg (rpow a n * rpow b 0);   (* nat_scale 1 X = X *)
    assert (rpow b 0 == one);
    H.x_mul_one (rpow a n);                        (* a^n * one = a^n *)
    reflexivity (rpow a n);
    mul_congruence (rpow a n) (rpow b 0) (rpow a n) (one #t);  (* a^n * b^0 = a^n * one *)
    H.trans3 (bterm a b n 0)
             (rpow a n * rpow b 0)
             (rpow a n * one)
             (rpow a n)

(* bterm n n = b^n   (C(n,n)=1, a^0 = one) *)
let bterm_corner_n (#t:Type) {| cr: commutative_ring t |} (a b: t) (n:nat)
  : Lemma (bterm a b n n = rpow b n)
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    let acg = cr.cr_r.r_add in
    NB.binom_n n;                                  (* binom n n = 1 *)
    assert (bterm a b n n == nat_scale #t #acg 1 (rpow a 0 * rpow b n));
    nat_scale_one #t #acg (rpow a 0 * rpow b n);
    assert (rpow a 0 == one);
    H.one_mul_x (rpow b n);                        (* one * b^n = b^n *)
    reflexivity (rpow b n);
    mul_congruence (rpow a 0) (rpow b n) (one #t) (rpow b n);
    H.trans3 (bterm a b n n)
             (rpow a 0 * rpow b n)
             (one * rpow b n)
             (rpow b n)

(* boundary: bterm n 0 = a * bterm (n-1) 0   (for n>=1) *)
let bterm_left_edge (#t:Type) {| cr: commutative_ring t |} (a b: t) (n:nat{n>=1})
  : Lemma (bterm a b n 0 = a * bterm a b (n-1) 0)
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    bterm_corner_0 #t #cr a b n;        (* bterm n 0 = a^n *)
    bterm_corner_0 #t #cr a b (n-1);    (* bterm (n-1) 0 = a^(n-1) *)
    (* a * bterm(n-1) 0 = a * a^(n-1) = a^n *)
    reflexivity a;
    mul_congruence a (bterm a b (n-1) 0) a (rpow a (n-1));
    assert (a * rpow a (n-1) == rpow a n);
    H.trans3 (a * bterm a b (n-1) 0) (a * rpow a (n-1)) (rpow a n) (rpow a n);
    symmetry (a * bterm a b (n-1) 0) (rpow a n);
    H.trans2 (bterm a b n 0) (rpow a n) (a * bterm a b (n-1) 0)

(* boundary: bterm n n = b * bterm (n-1) (n-1)   (for n>=1) *)
let bterm_right_edge (#t:Type) {| cr: commutative_ring t |} (a b: t) (n:nat{n>=1})
  : Lemma (bterm a b n n = b * bterm a b (n-1) (n-1))
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    bterm_corner_n #t #cr a b n;          (* bterm n n = b^n *)
    bterm_corner_n #t #cr a b (n-1);      (* bterm (n-1)(n-1) = b^(n-1) *)
    reflexivity b;
    mul_congruence b (bterm a b (n-1) (n-1)) b (rpow b (n-1));
    assert (b * rpow b (n-1) == rpow b n);
    H.trans3 (b * bterm a b (n-1) (n-1)) (b * rpow b (n-1)) (rpow b n) (rpow b n);
    symmetry (b * bterm a b (n-1) (n-1)) (rpow b n);
    H.trans2 (bterm a b n n) (rpow b n) (b * bterm a b (n-1) (n-1))

(* ---------------------------------------------------------------- *)
(*  Pascal MERGE of the two scaled (n-1)-row sums into the n-row sum *)
(* ---------------------------------------------------------------- *)

(* the "a-contribution" function:  a·bterm(n-1,k) padded with zero at k=n. *)
let afn (#t:Type) {| cr: commutative_ring t |} (a b: t) (n:nat{n>=1}) (k:nat) : t =
  if k <= n-1 then a * bterm a b (n-1) k else zero

(* the "b-contribution" function:  b·bterm(n-1,k-1) padded with zero at k=0. *)
let bfn (#t:Type) {| cr: commutative_ring t |} (a b: t) (n:nat{n>=1}) (k:nat) : t =
  if k >= 1 then b * bterm a b (n-1) (k-1) else zero

(* pointwise:  afn k + bfn k = bterm n k   for 0 <= k <= n. *)
let combined_is_bterm (#t:Type) {| cr: commutative_ring t |} (a b: t) (n:nat{n>=1}) (k:nat{k <= n})
  : Lemma (afn a b n k + bfn a b n k = bterm a b n k)
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    if k = 0 then begin
      (* afn 0 = a*bterm(n-1,0) ; bfn 0 = zero ; bterm n 0 = a*bterm(n-1,0) *)
      H.x_plus_zero (afn a b n 0);                       (* afn0 + 0 = afn0 *)
      bterm_left_edge #t #cr a b n;                      (* bterm n 0 = a*bterm(n-1,0) = afn0 *)
      symmetry (bterm a b n 0) (a * bterm a b (n-1) 0);
      H.trans2 (afn a b n 0 + bfn a b n 0) (afn a b n 0) (bterm a b n 0)
    end
    else if k = n then begin
      (* afn n = zero ; bfn n = b*bterm(n-1,n-1) ; bterm n n = b*bterm(n-1,n-1) *)
      H.zero_plus_x (bfn a b n n);                       (* 0 + bfn n = bfn n *)
      bterm_right_edge #t #cr a b n;                     (* bterm n n = b*bterm(n-1,n-1) = bfn n *)
      symmetry (bterm a b n n) (b * bterm a b (n-1) (n-1));
      H.trans2 (afn a b n n + bfn a b n n) (bfn a b n n) (bterm a b n n)
    end
    else begin
      (* 1 <= k <= n-1 : afn k + bfn k = a*bterm(n-1,k) + b*bterm(n-1,k-1) = bterm n k *)
      bterm_pascal #t #cr a b n k
    end

(* sum of the a-contribution over 0..n+1 equals  a · S(n-1). *)
let sum_afn (#t:Type) {| cr: commutative_ring t |} (a b: t) (n:nat{n>=1})
  : Lemma (sum_range (afn a b n) 0 (Prims.op_Addition n 1)
           = a * sum_range (bterm a b (n-1)) 0 n)
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    let acg = cr.cr_r.r_add in
    (* peel the last (zero) term: sum 0 (n+1) = sum 0 n + afn n, afn n = zero *)
    sum_range_unfold_right #t #acg (afn a b n) 0 (Prims.op_Addition n 1);  (* = sum 0 n + afn n *)
    assert (afn a b n n == (zero <: t));
    reflexivity (sum_range (afn a b n) 0 n);
    add_congruence (sum_range (afn a b n) 0 n) (afn a b n n)
                   (sum_range (afn a b n) 0 n) (zero <: t);
    H.x_plus_zero (sum_range (afn a b n) 0 n);
    H.trans3 (sum_range (afn a b n) 0 (Prims.op_Addition n 1))
             (sum_range (afn a b n) 0 n + afn a b n n)
             (sum_range (afn a b n) 0 n + zero)
             (sum_range (afn a b n) 0 n);
    (* on 0..n, afn k = a*bterm(n-1,k) = (pointwise_mul (const a) (bterm(n-1))) k *)
    let body : nat -> t = pointwise_mul (const a) (bterm a b (n-1)) in
    let h (k:nat{0 <= k /\ k < n}) : Lemma (afn a b n k = body k)
      = pointwise_mul_unfold (const a) (bterm a b (n-1)) k;
        const_unfold a k;
        assert (afn a b n k == a * bterm a b (n-1) k);
        reflexivity (a * bterm a b (n-1) k)
    in
    sum_range_congruence (afn a b n) body 0 n h;          (* sum afn 0 n = sum body 0 n *)
    sum_range_mul_left #t #(cr.cr_r) a (bterm a b (n-1)) 0 n;  (* a * sum = sum body *)
    symmetry (a * sum_range (bterm a b (n-1)) 0 n) (sum_range body 0 n);
    H.trans2 (sum_range (afn a b n) 0 n)
             (sum_range body 0 n)
             (a * sum_range (bterm a b (n-1)) 0 n);
    H.trans2 (sum_range (afn a b n) 0 (Prims.op_Addition n 1))
             (sum_range (afn a b n) 0 n)
             (a * sum_range (bterm a b (n-1)) 0 n)

(* sum of the b-contribution over 0..n+1 equals  b · S(n-1). *)
let sum_bfn (#t:Type) {| cr: commutative_ring t |} (a b: t) (n:nat{n>=1})
  : Lemma (sum_range (bfn a b n) 0 (Prims.op_Addition n 1)
           = b * sum_range (bterm a b (n-1)) 0 n)
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    let acg = cr.cr_r.r_add in
    (* peel the first (zero) term: sum 0 (n+1) = bfn 0 + sum 1 (n+1), bfn 0 = zero *)
    sum_range_unfold_left #t #acg (bfn a b n) 0 (Prims.op_Addition n 1);  (* = bfn 0 + sum 1 (n+1) *)
    assert (bfn a b n 0 == (zero <: t));
    reflexivity (sum_range (bfn a b n) 1 (Prims.op_Addition n 1));
    add_congruence (bfn a b n 0) (sum_range (bfn a b n) 1 (Prims.op_Addition n 1))
                   (zero <: t) (sum_range (bfn a b n) 1 (Prims.op_Addition n 1));
    H.zero_plus_x (sum_range (bfn a b n) 1 (Prims.op_Addition n 1));
    H.trans3 (sum_range (bfn a b n) 0 (Prims.op_Addition n 1))
             (bfn a b n 0 + sum_range (bfn a b n) 1 (Prims.op_Addition n 1))
             (zero + sum_range (bfn a b n) 1 (Prims.op_Addition n 1))
             (sum_range (bfn a b n) 1 (Prims.op_Addition n 1));
    (* shift:  sum_range (fun j -> bfn (j+1)) 0 n = sum_range bfn 1 (n+1) *)
    sum_range_shift #t #acg (bfn a b n) 1 0 n;
    symmetry (sum_range (fun (j:nat) -> bfn a b n (Prims.op_Addition j 1)) 0 n)
             (sum_range (bfn a b n) 1 (Prims.op_Addition n 1));
    (* on 0..n, bfn (j+1) = b*bterm(n-1,j) = body j *)
    let body : nat -> t = pointwise_mul (const b) (bterm a b (n-1)) in
    let h (j:nat{0 <= j /\ j < n}) : Lemma (bfn a b n (Prims.op_Addition j 1) = body j)
      = pointwise_mul_unfold (const b) (bterm a b (n-1)) j;
        const_unfold b j;
        assert (bfn a b n (Prims.op_Addition j 1) == b * bterm a b (n-1) j);
        reflexivity (b * bterm a b (n-1) j)
    in
    sum_range_congruence (fun (j:nat) -> bfn a b n (Prims.op_Addition j 1)) body 0 n h;
    sum_range_mul_left #t #(cr.cr_r) b (bterm a b (n-1)) 0 n;   (* b * sum = sum body *)
    symmetry (b * sum_range (bterm a b (n-1)) 0 n) (sum_range body 0 n);
    H.trans4 (sum_range (bfn a b n) 0 (Prims.op_Addition n 1))
             (sum_range (bfn a b n) 1 (Prims.op_Addition n 1))
             (sum_range (fun (j:nat) -> bfn a b n (Prims.op_Addition j 1)) 0 n)
             (sum_range body 0 n)
             (b * sum_range (bterm a b (n-1)) 0 n)

(* the merge:  S(n) = a · S(n-1) + b · S(n-1). *)
let merge (#t:Type) {| cr: commutative_ring t |} (a b: t) (n:nat{n>=1})
  : Lemma (sum_range (bterm a b n) 0 (Prims.op_Addition n 1)
           = a * sum_range (bterm a b (n-1)) 0 n
             + b * sum_range (bterm a b (n-1)) 0 n)
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    let acg = cr.cr_r.r_add in
    (* step1: bterm n = pointwise_add afn bfn  on 0..n+1 *)
    let h (k:nat{0 <= k /\ k < Prims.op_Addition n 1}) : Lemma (bterm a b n k = pointwise_add (afn a b n) (bfn a b n) k)
      = pointwise_add_unfold (afn a b n) (bfn a b n) k;     (* pa k = afn k + bfn k *)
        combined_is_bterm #t #cr a b n k;                   (* afn k + bfn k = bterm n k *)
        symmetry (afn a b n k + bfn a b n k) (bterm a b n k)
    in
    sum_range_congruence (bterm a b n) (pointwise_add (afn a b n) (bfn a b n)) 0 (Prims.op_Addition n 1) h;
    (* step2: split *)
    sum_range_add #t #acg (afn a b n) (bfn a b n) 0 (Prims.op_Addition n 1);
    (* step3: evaluate each *)
    sum_afn #t #cr a b n;
    sum_bfn #t #cr a b n;
    add_congruence (sum_range (afn a b n) 0 (Prims.op_Addition n 1))
                   (sum_range (bfn a b n) 0 (Prims.op_Addition n 1))
                   (a * sum_range (bterm a b (n-1)) 0 n)
                   (b * sum_range (bterm a b (n-1)) 0 n);
    H.trans3 (sum_range (bterm a b n) 0 (Prims.op_Addition n 1))
             (sum_range (pointwise_add (afn a b n) (bfn a b n)) 0 (Prims.op_Addition n 1))
             (sum_range (afn a b n) 0 (Prims.op_Addition n 1)
              + sum_range (bfn a b n) 0 (Prims.op_Addition n 1))
             (a * sum_range (bterm a b (n-1)) 0 n
              + b * sum_range (bterm a b (n-1)) 0 n)

(* ---------------------------------------------------------------- *)
(*  THE BINOMIAL THEOREM                                            *)
(*                                                                   *)
(*    (a + b)^n  =  Σ_{k=0}^{n}  C(n,k) · a^{n-k} · b^k             *)
(* ---------------------------------------------------------------- *)

let rec binomial_theorem (#t:Type) {| cr: commutative_ring t |} (a b: t) (n: nat)
  : Lemma (ensures rpow (a + b) n
                   = sum_range (bterm a b n) 0 (Prims.op_Addition n 1))
          (decreases n)
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    let acg = cr.cr_r.r_add in
    if n = 0 then begin
      (* rpow (a+b) 0 = one ; S(0) = bterm 0 0 = a^0 = one *)
      sum_range_singleton #t #acg (bterm a b 0) 0;     (* S(0) = bterm 0 0 *)
      bterm_corner_0 #t #cr a b 0;                      (* bterm 0 0 = a^0 = one *)
      assert (rpow a 0 == one);
      symmetry (sum_range (bterm a b 0) 0 1) (bterm a b 0 0);
      H.trans2 (rpow (a+b) 0) (one <: t) (rpow a 0);
      (* now relate one to S(0): S(0) = bterm00 = a^0 = one, so rpow(a+b)0 = one = S(0) *)
      symmetry (rpow a 0) (one <: t);
      H.trans3 (rpow (a+b) 0) (one <: t) (rpow a 0) (bterm a b 0 0);
      symmetry (bterm a b 0 0) (sum_range (bterm a b 0) 0 1);
      H.trans2 (rpow (a+b) 0) (bterm a b 0 0) (sum_range (bterm a b 0) 0 1)
    end
    else begin
      (* IH at n-1 *)
      binomial_theorem #t #cr a b (n-1);                (* rpow(a+b)(n-1) = S(n-1) *)
      (* rpow(a+b) n = (a+b) * rpow(a+b)(n-1) *)
      assert (rpow (a+b) n == (a+b) * rpow (a+b) (n-1));
      reflexivity (a+b);
      mul_congruence (a+b) (rpow (a+b) (n-1)) (a+b) (sum_range (bterm a b (n-1)) 0 n);
      (* (a+b)*S(n-1) = a*S(n-1) + b*S(n-1)  (right distributivity) *)
      right_distributivity (sum_range (bterm a b (n-1)) 0 n) a b;  (* (a+b)*S = a*S + b*S *)
      (* merge: S(n) = a*S(n-1)+b*S(n-1) *)
      merge #t #cr a b n;
      symmetry (sum_range (bterm a b n) 0 (Prims.op_Addition n 1))
               (a * sum_range (bterm a b (n-1)) 0 n + b * sum_range (bterm a b (n-1)) 0 n);
      H.trans4 (rpow (a+b) n)
               ((a+b) * rpow (a+b) (n-1))
               ((a+b) * sum_range (bterm a b (n-1)) 0 n)
               (a * sum_range (bterm a b (n-1)) 0 n + b * sum_range (bterm a b (n-1)) 0 n)
               (sum_range (bterm a b n) 0 (Prims.op_Addition n 1))
    end
