module Core.NatBinomial

(* ================================================================ *)
(*  Standalone binomial coefficients over the naturals.             *)
(*                                                                   *)
(*  FStar.Math.Fermat's IMPLEMENTATION proves `binomial`,           *)
(*  `binomial_factorial`, and `binomial_prime`, but its .fsti       *)
(*  exposes only `fermat`/`mod_mult_congr`/`fermat_alt`.  We         *)
(*  re-derive the binomial-coefficient theory we need here, in      *)
(*  particular the characteristic-p fact                            *)
(*                                                                   *)
(*      p | binom p k        for  0 < k < p,  p prime.              *)
(*                                                                   *)
(*  This is the number-theoretic kernel of Frobenius additivity.    *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

open FStar.Math.Lemmas
open FStar.Math.Euclid

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ---------------------------------------------------------------- *)
(*  Factorial and binomial coefficient                              *)
(* ---------------------------------------------------------------- *)

let rec factorial (n:nat) : pos =
  if n = 0 then 1 else n * factorial (n - 1)

let rec binom (n k:nat) : nat =
  match n, k with
  | _, 0 -> 1
  | 0, _ -> 0
  | _, _ -> binom (n - 1) k + binom (n - 1) (k - 1)

let binom_0 (n:nat) : Lemma (binom n 0 == 1) = ()

let rec binom_lt (n:nat) (k:nat{n < k}) : Lemma (binom n k = 0) =
  match n, k with
  | _, 0 -> ()
  | 0, _ -> ()
  | _ -> binom_lt (n - 1) k; binom_lt (n - 1) (k - 1)

let rec binom_n (n:nat) : Lemma (binom n n == 1) =
  match n with
  | 0 -> ()
  | _ -> binom_lt n (n + 1); binom_n (n - 1)

(* Pascal's identity (definitional). *)
let pascal (n:nat) (k:pos{k <= n}) : Lemma
  (binom n k + binom n (k - 1) = binom (n + 1) k) = ()

(* ---------------------------------------------------------------- *)
(*  binom (n+m) n * (n! * m!) = (n+m)!                               *)
(* ---------------------------------------------------------------- *)

let rec binom_factorial (m n:nat)
  : Lemma (binom (n + m) n * (factorial n * factorial m) == factorial (n + m)) =
  match m, n with
  | 0, _ -> binom_n n
  | _, 0 -> ()
  | _ ->
    let reorder1 (a b c d:int) : Lemma (a * (b * (c * d)) == c * (a * (b * d))) =
      assert (a * (b * (c * d)) == c * (a * (b * d))) by (FStar.Tactics.CanonCommSemiring.int_semiring())
    in
    let reorder2 (a b c d:int) : Lemma (a * ((b * c) * d) == b * (a * (c * d))) =
      assert (a * ((b * c) * d) == b * (a * (c * d))) by (FStar.Tactics.CanonCommSemiring.int_semiring())
    in
    calc (==) {
      binom (n + m) n * (factorial n * factorial m);
      == { pascal (n + m - 1) n }
      (binom (n + m - 1) n + binom (n + m - 1) (n - 1)) * (factorial n * factorial m);
      == { addition_is_associative n m (-1) }
      (binom (n + (m - 1)) n + binom (n + (m - 1)) (n - 1)) * (factorial n * factorial m);
      == { distributivity_add_left (binom (n + (m - 1)) n)
                                   (binom (n + (m - 1)) (n - 1))
                                   (factorial n * factorial m)
         }
      binom (n + (m - 1)) n * (factorial n * factorial m) +
      binom (n + (m - 1)) (n - 1) * (factorial n * factorial m);
      == { }
      binom (n + (m - 1)) n * (factorial n * (m * factorial (m - 1))) +
      binom ((n - 1) + m) (n - 1) * ((n * factorial (n - 1)) * factorial m);
      == { reorder1 (binom (n + (m - 1)) n) (factorial n) m (factorial (m - 1));
           reorder2 (binom ((n - 1) + m) (n - 1)) n (factorial (n - 1)) (factorial m)
         }
      m * (binom (n + (m - 1)) n * (factorial n * factorial (m - 1))) +
      n * (binom ((n - 1) + m) (n - 1) * (factorial (n - 1) * factorial m));
      == { binom_factorial (m - 1) n; binom_factorial m (n - 1) }
      m * factorial (n + (m - 1)) + n * factorial ((n - 1) + m);
      == { }
      m * factorial (n + m - 1) + n * factorial (n + m - 1);
      == { }
      n * factorial (n + m - 1) + m * factorial (n + m - 1);
      == { distributivity_add_left m n (factorial (n + m - 1)) }
      (n + m) * factorial (n + m - 1);
      == { }
      factorial (n + m);
    }

(* ---------------------------------------------------------------- *)
(*  p prime, 0 < k < p  ==>  p | binom p k                          *)
(* ---------------------------------------------------------------- *)

(* p does not divide k! when 0 < k < p (all factors are < p). *)
#push-options "--fuel 2"
let rec factorial_not_div_prime (p:int{is_prime p}) (k:pos{k < p})
  : Lemma (requires factorial k % p = 0)
          (ensures False)
          (decreases k) =
  if k = 1 then (assert (factorial 1 == 1); small_mod 1 p)
  else begin
    (* factorial k = k * factorial (k-1); p prime divides product *)
    assert (factorial k == k * factorial (k - 1));
    euclid_prime p k (factorial (k - 1));
    (* p | k impossible (0<k<p), so p | factorial (k-1) *)
    small_mod k p;
    factorial_not_div_prime p (k - 1)
  end
#pop-options

(* binom p k % p = 0 for 0 < k < p. *)
let prime_divides_binom (p:int{is_prime p}) (k:pos{k < p})
  : Lemma (binom p k % p == 0) =
  (* From binom_factorial (p-k) k : binom p k * (k! * (p-k)!) = p!. *)
  binom_factorial (p - k) k;
  assert (binom p k * (factorial k * factorial (p - k)) == factorial p);
  (* p! = p * (p-1)!, so p | p!. *)
  assert (factorial p == p * factorial (p - 1));
  lemma_mod_mul_distr_l p (factorial (p - 1)) p;   (* (p * (p-1)!) % p = (p%p * ...) % p = 0 *)
  assert (factorial p % p == 0);
  (* p prime divides binom p k * (k! * (p-k)!). *)
  euclid_prime p (binom p k) (factorial k * factorial (p - k));
  if binom p k % p <> 0 then begin
    (* then p | k! * (p-k)! *)
    euclid_prime p (factorial k) (factorial (p - k));
    if factorial k % p = 0 then factorial_not_div_prime p k
    else factorial_not_div_prime p (p - k)
  end
