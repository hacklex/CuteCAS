module Core.Algebra.Frobenius

(* ================================================================ *)
(*  Frobenius additivity ("freshman's dream") in a commutative      *)
(*  ring of characteristic p (prime):                                *)
(*                                                                   *)
(*      (a + b)^p = a^p + b^p.                                       *)
(*                                                                   *)
(*  The middle binomial terms  C(p,k)·a^{p-k}·b^k  (0<k<p) vanish    *)
(*  because p | C(p,k) (Core.Algebra.BinomialCoefficients.prime_divides_binom) and    *)
(*  the ring has characteristic p (nat_scale p x = zero).            *)
(*                                                                   *)
(*  The characteristic-p hypothesis is taken as a parameter          *)
(*  `char_p : (x:t) -> Lemma (nat_scale p x = zero)`, so the result  *)
(*  is field-agnostic and instantiates at fp p and polynomial(fp p). *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module NB = Core.Algebra.BinomialCoefficients

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Polynomial.Derivative
open Core.FinSum
open Core.Algebra.Power
open Core.NumberTheory

#set-options "--fuel 1 --ifuel 1 --z3rlimit 30"

(* ---------------------------------------------------------------- *)
(*  nat_scale composition:  nat_scale (m*n) x = nat_scale m (nat_scale n x) *)
(* ---------------------------------------------------------------- *)

let rec nat_scale_compose (#t:Type) {| acg: add_comm_group t |} (m n: nat) (x: t)
  : Lemma (ensures nat_scale (Prims.op_Star m n) x = nat_scale m (nat_scale n x))
          (decreases m)
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    if m = 0 then begin
      (* nat_scale 0 x = zero = nat_scale 0 (nat_scale n x) *)
      nat_scale_zero x;
      nat_scale_zero (nat_scale n x);

      H.trans2 (nat_scale (Prims.op_Star 0 n) x) zero (nat_scale 0 (nat_scale n x))
    end
    else begin
      (* m*n = n + (m-1)*n ;  nat_scale (n + (m-1)*n) x = nat_scale n x + nat_scale ((m-1)*n) x *)
      let mn1 = Prims.op_Star (m-1) n in
      assert (Prims.op_Star m n == (n ++ mn1));
      nat_scale_add n mn1 x;                          (* ns(n+(m-1)n)x = ns n x + ns((m-1)n)x *)
      nat_scale_compose (m-1) n x;                    (* ns((m-1)n)x = ns(m-1)(ns n x) *)

      add_congruence (nat_scale n x) (nat_scale mn1 x)
                     (nat_scale n x) (nat_scale (m-1) (nat_scale n x));
      (* nat_scale m (ns n x) = ns n x + ns (m-1) (ns n x)  (via nat_scale_succ) *)
      nat_scale_succ (m-1) (nat_scale n x);           (* ns m Y = Y + ns(m-1)Y *)
      H.trans3 (nat_scale (Prims.op_Star m n) x)
               (nat_scale n x + nat_scale mn1 x)
               (nat_scale n x + nat_scale (m-1) (nat_scale n x))
               (nat_scale m (nat_scale n x))
    end

(* ---------------------------------------------------------------- *)
(*  Vanishing of p-divisible scalings under characteristic p        *)
(* ---------------------------------------------------------------- *)

(* If p | m and nat_scale p (·) is identically zero, then nat_scale m (·) = zero. *)
let nat_scale_p_divisible_zero
  (#t:Type) {| acg: add_comm_group t |}
  (p:pos) (m:nat) (x: t)
  (char_p: (y:t) -> Lemma (nat_scale p y = zero))
  : Lemma (requires m % p = 0)
          (ensures  nat_scale m x = zero)
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    let j = m / p in
    (* m = p * j  (since m % p = 0) *)
    FStar.Math.Lemmas.lemma_div_exact m p;          (* m = p * (m/p) *)
    assert (m == Prims.op_Star p j);
    nat_scale_compose p j x;                (* ns (p*j) x = ns p (ns j x) *)
    char_p (nat_scale j x);                         (* ns p (ns j x) = zero *)
    H.trans2 (nat_scale m x)
             (nat_scale p (nat_scale j x))
             zero

(* ---------------------------------------------------------------- *)
(*  Middle binomial terms vanish at the prime exponent p            *)
(* ---------------------------------------------------------------- *)

let bterm_middle_zero
  (#t:Type) {| cr: commutative_ring t |}
  (p:int{is_prime p}) (a b: t) (k:nat{1 <= k /\ k <= p-1})
  (char_p: (y:t) -> Lemma (nat_scale p y = zero))
  : Lemma (bterm a b p k = zero)
  = (* bterm p k = nat_scale (binom p k) (a^{p-k} b^k), and binom p k % p = 0 *)
    NB.prime_divides_binom p k;                          (* binom p k % p = 0 *)
    let x : t = rpow a (p - k) * rpow b k in
    assert (bterm a b p k == nat_scale (NB.binom p k) x);
    nat_scale_p_divisible_zero p (NB.binom p k) x char_p

(* ---------------------------------------------------------------- *)
(*  FROBENIUS ADDITIVITY  (the freshman's dream)                    *)
(*                                                                   *)
(*     (a + b)^p  =  a^p + b^p   in characteristic p.               *)
(* ---------------------------------------------------------------- *)

let frobenius_add
  (#t:Type) {| cr: commutative_ring t |}
  (p:int{is_prime p}) (a b: t)
  (char_p: (y:t) -> Lemma (nat_scale p y = zero))
  : Lemma (rpow (a + b) p = rpow a p + rpow b p)
  = H.elim_equatable_laws t (); H.trans_for_calc t ();
    let pn : nat = p in
    (* binomial theorem:  (a+b)^p = Σ_{k=0}^{p} bterm p k *)
    binomial_theorem a b pn;                    (* rpow(a+b)p = sum 0 (p+1) *)
    (* split  sum 0 (p+1)  =  sum 0 1  +  sum 1 p  +  sum p (p+1)  *)
    sum_range_split (bterm a b pn) 0 1 (pn ++ 1);   (* = sum 0 1 + sum 1 (p+1) *)
    sum_range_split (bterm a b pn) 1 pn (pn ++ 1);  (* sum 1 (p+1) = sum 1 p + sum p (p+1) *)
    (* sum 0 1 = bterm p 0 = a^p *)
    sum_range_singleton (bterm a b pn) 0;       (* sum 0 1 = bterm p 0 *)
    bterm_corner_0 a b pn;                        (* bterm p 0 = a^p *)
    (* sum p (p+1) = bterm p p = b^p *)
    sum_range_singleton (bterm a b pn) pn;       (* sum p (p+1) = bterm p p *)
    bterm_corner_n a b pn;                        (* bterm p p = b^p *)
    (* middle sum 1 p is zero *)
    let mid_zero (k:nat{1 <= k /\ k < pn}) : Lemma (bterm a b pn k = (zero <: t))
      = bterm_middle_zero p a b k char_p
    in
    sum_range_all_zero (bterm a b pn) 1 pn mid_zero;  (* sum 1 p = zero *)
    (* assemble:  sum 0 (p+1) = (sum 0 1) + ((sum 1 p) + (sum p (p+1)))
                              = a^p + (zero + b^p) = a^p + b^p *)
    let s01 = sum_range (bterm a b pn) 0 1 in
    let s1p = sum_range (bterm a b pn) 1 pn in
    let sp  = sum_range (bterm a b pn) pn (pn ++ 1) in
    (* sum 1 (p+1) = s1p + sp = zero + sp = sp = b^p *)

    add_congruence s1p sp (zero <: t) sp;                (* s1p + sp = zero + sp *)
    H.zero_plus_x sp;                                     (* zero + sp = sp *)
    H.trans3 (sum_range (bterm a b pn) 1 (pn ++ 1))
             (s1p + sp) (zero + sp) sp;                   (* sum 1 (p+1) = sp *)
    (* sp = b^p *)
    H.trans2 (sum_range (bterm a b pn) 1 (pn ++ 1)) sp (rpow b pn);
    (* sum 0 (p+1) = s01 + sum 1 (p+1) = a^p + b^p *)
    (* s01 = a^p *)
    H.trans2 s01 (bterm a b pn 0) (rpow a pn);
    add_congruence s01 (sum_range (bterm a b pn) 1 (pn ++ 1))
                   (rpow a pn) (rpow b pn);
    H.trans3 (rpow (a+b) pn)
             (sum_range (bterm a b pn) 0 (pn ++ 1))
             (s01 + sum_range (bterm a b pn) 1 (pn ++ 1))
             (rpow a pn + rpow b pn)
