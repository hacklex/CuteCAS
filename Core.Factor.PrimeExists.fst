module Core.Factor.PrimeExists

(* ================================================================ *)
(*  M2 · S4 (C4) — GOOD-PRIME EXISTENCE, number-theoretic core.      *)
(*                                                                   *)
(*  This module closes the *existence* side of PrimeSelect's good-   *)
(*  prime search with self-contained, executable, machine-checked    *)
(*  number theory that the tree previously lacked:                   *)
(*                                                                   *)
(*   Layer 1  is_prime_dec  : executable trial-division primality    *)
(*            is_prime_dec_correct : it agrees with EU.is_prime.      *)
(*   (aux)   least_factor  : least divisor >= 2 of n >= 2, and it     *)
(*            is PRIME (prime-factor existence).                      *)
(*   Layer 3  prime_larger_than : for every bound N there is a prime  *)
(*            p > N  (INFINITUDE OF PRIMES, via Euclid's  N! + 1).    *)
(*            exists_prime_not_dividing : for every nonzero integer n *)
(*            there is a prime p that does NOT divide n.              *)
(*                                                                   *)
(*  Layer 2 (bad-prime => good-prime, i.e. p ∤ lc(B)·res(B,B') ⟹      *)
(*  is_good_prime p B) is the deep resultant-reduction algebra; it    *)
(*  is R2-reported (see the closing comment) because the tree has no  *)
(*  resultant-reduction / squarefree-preservation infrastructure.    *)
(*                                                                   *)
(*  Kept dependency-light (only FStar.Math.Euclid / FStar.Math.       *)
(*  Lemmas) so it verifies standalone and durably.                   *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

open Core.NumberTheory

module Math = FStar.Math.Lemmas
module Cl   = FStar.Classical
module RR   = Core.Factor.ResultantReduction
module PSel = Core.Factor.PrimeSelect
module BIN  = Core.Factor.BadIntNonzero

open Core.Polynomial
open Core.Polynomial.SquareFree
open Core.Polynomial.EmbedQ

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20 --split_queries always"

(* ---------------------------------------------------------------- *)
(*  A generic divisor bound: a positive divisor is <= its multiple.  *)
(* ---------------------------------------------------------------- *)

let pos_divisor_le (d n:int)
  : Lemma (requires n > 0 /\ d > 0 /\ d `divides` n) (ensures d <= n)
  = eliminate exists q. n = q * d
    returns d <= n
    with _.
    ( if q <= 0 then Math.lemma_mult_le_right d q 0     (* q*d <= 0 < n : impossible *)
      else Math.lemma_mult_le_right d 1 q )             (* d = 1*d <= q*d = n         *)

(* ---------------------------------------------------------------- *)
(*  Divisor dichotomy: if nn >= 2 has no divisor in [2, nn-1], then   *)
(*  every divisor of nn is one of 1, -1, nn, -nn  (i.e. nn is prime). *)
(* ---------------------------------------------------------------- *)

let divisor_dichotomy (nn d:int)
  : Lemma (requires nn >= 2 /\ d `divides` nn /\
                    (forall (e:int). (2 <= e /\ e <= nn - 1) ==> ~(e `divides` nn)))
          (ensures d = 1 \/ d = -1 \/ d = nn \/ d = -nn)
  = if d = 0 then
      (* 0 divides nn  =>  nn = q*0 = 0, contradicting nn >= 2 *)
      (eliminate exists q. nn = q * d returns d = 1 \/ d = -1 \/ d = nn \/ d = -nn with _. ())
    else if d > 0 then
      (pos_divisor_le d nn; ())                  (* d <= nn ; forbidden middle range gives contra *)
    else
      (divides_opp d nn; pos_divisor_le (-d) nn; ())

(* ---------------------------------------------------------------- *)
(*  1.  is_prime_dec : executable trial division over [2, n-1].      *)
(* ---------------------------------------------------------------- *)

let rec no_div_upto (n:int) (k:nat) : Tot bool (decreases k)
  = if k < 2 then true
    else (n % k <> 0) && no_div_upto n (k - 1)

let is_prime_dec (n:int) : bool
  = n >= 2 && no_div_upto n (if n >= 1 then n - 1 else 0)

(* no_div_upto characterisation. *)
let rec no_div_upto_spec (n:int) (k:nat)
  : Lemma (ensures (no_div_upto n k = true)
                   <==> (forall (d:int). (2 <= d /\ d <= k) ==> n % d <> 0))
          (decreases k)
  = if k < 2 then () else no_div_upto_spec n (k - 1)

(* mod-view => divides-view : a nonzero e with n % e = 0 divides n; contrapositive. *)
let dm (n:int) (e:int{e <> 0})
  : Lemma (requires e `divides` n) (ensures n % e = 0)
  = divides_mod n e

let no_mod_no_divides_at (n e:int)
  : Lemma (requires 2 <= e /\ e <= n - 1 /\ n % e <> 0) (ensures ~(e `divides` n))
  = Cl.move_requires (dm n) e

let no_mod_no_divides (n:int)
  : Lemma (requires n >= 2 /\ (forall (e:int). (2 <= e /\ e <= n - 1) ==> n % e <> 0))
          (ensures  (forall (e:int). (2 <= e /\ e <= n - 1) ==> ~(e `divides` n)))
  = introduce forall (e:int). (2 <= e /\ e <= n - 1) ==> ~(e `divides` n)
    with begin
      introduce (2 <= e /\ e <= n - 1) ==> ~(e `divides` n)
      with he. no_mod_no_divides_at n e
    end

let prime_no_mod_at (n e:int)
  : Lemma (requires is_prime n /\ 2 <= e /\ e <= n - 1) (ensures n % e <> 0)
  = if n % e = 0 then (is_prime_elim n; mod_divides n e) else ()

let prime_no_mod (n:int)
  : Lemma (requires is_prime n)
          (ensures  (forall (e:int). (2 <= e /\ e <= n - 1) ==> n % e <> 0))
  = introduce forall (e:int). (2 <= e /\ e <= n - 1) ==> n % e <> 0
    with begin
      introduce (2 <= e /\ e <= n - 1) ==> n % e <> 0
      with he. prime_no_mod_at n e
    end

let is_prime_dec_correct (n:int)
  : Lemma (is_prime_dec n = true <==> is_prime n)
  = if n < 2 then ()
    else begin
      no_div_upto_spec n (n - 1);
      introduce is_prime_dec n = true ==> is_prime n
      with hdec. begin
        no_mod_no_divides n;
        introduce forall (d:int). d `divides` n ==> (d = 1 \/ d = -1 \/ d = n \/ d = -n)
        with begin
          introduce d `divides` n ==> (d = 1 \/ d = -1 \/ d = n \/ d = -n)
          with hd. divisor_dichotomy n d
        end;
        is_prime_intro n
      end;
      introduce is_prime n ==> is_prime_dec n = true
      with hpr. prime_no_mod n
    end

(* ---------------------------------------------------------------- *)
(*  2.  least_factor : least divisor >= 2, and it is PRIME.          *)
(* ---------------------------------------------------------------- *)

let rec sf_from (n:int) (d:int)
  : Pure int
    (requires n >= 2 /\ 2 <= d /\ d <= n /\
              (forall (e:int). (2 <= e /\ e < d) ==> n % e <> 0))
    (ensures fun r -> 2 <= r /\ r <= n /\ n % r = 0 /\
                      (forall (e:int). (2 <= e /\ e < r) ==> n % e <> 0))
    (decreases (n - d))
  = if n % d = 0 then d
    else sf_from n (d + 1)

let least_factor (n:int{n >= 2})
  : (r:int{2 <= r /\ r <= n /\ n % r = 0 /\
           (forall (e:int). (2 <= e /\ e < r) ==> n % e <> 0)})
  = sf_from n 2

(* a divisor of m in [2, m-1] would divide n and contradict n-minimality. *)
let edm (n m:int) (e:int{e <> 0})
  : Lemma (requires e `divides` m /\ m `divides` n) (ensures n % e = 0)
  = divides_transitive e m n; divides_mod n e

let not_div_of_min (n m e:int)
  : Lemma (requires 2 <= e /\ e <= m - 1 /\ n % e <> 0 /\ m `divides` n)
          (ensures ~(e `divides` m))
  = Cl.move_requires (edm n m) e

(* least_factor n is prime and divides n : prime-factor existence. *)
let least_factor_prime (n:int{n >= 2})
  : Lemma (is_prime (least_factor n) /\ (least_factor n) `divides` n)
  = let m = least_factor n in
    mod_divides n m;                              (* m divides n *)
    introduce forall (e:int). (2 <= e /\ e <= m - 1) ==> ~(e `divides` m)
    with begin
      introduce (2 <= e /\ e <= m - 1) ==> ~(e `divides` m)
      with he. not_div_of_min n m e
    end;
    introduce forall (d:int). d `divides` m ==> (d = 1 \/ d = -1 \/ d = m \/ d = -m)
    with begin
      introduce d `divides` m ==> (d = 1 \/ d = -1 \/ d = m \/ d = -m)
      with hd. divisor_dichotomy m d
    end;
    is_prime_intro m

(* ---------------------------------------------------------------- *)
(*  3.  Infinitude of primes  (Euclid: a prime factor of N! + 1).    *)
(* ---------------------------------------------------------------- *)

let rec fact (n:nat) : pos = if n = 0 then 1 else n * fact (n - 1)

(* every integer in [2, n] divides n! *)
let rec p_divides_fact (p n:int)
  : Lemma (requires 2 <= p /\ p <= n) (ensures p `divides` (fact n)) (decreases n)
  = if p = n then (divides_reflexive n; divides_mult_right (fact (n - 1)) n n)
    else (p_divides_fact p (n - 1); divides_mult_right n (fact (n - 1)) p)

(* the least prime factor of N!+1 exceeds N. *)
let prime_larger_than_at (bnd:nat) (pf:int)
  : Lemma (requires is_prime pf /\ pf `divides` (fact bnd + 1))
          (ensures pf > bnd)
  = if pf <= bnd then begin
      p_divides_fact pf bnd;                       (* pf divides fact bnd (uses 2 <= pf) *)
      divides_sub (fact bnd + 1) (fact bnd) pf;    (* pf divides ((N!+1) - N!) = 1 *)
      divides_1 pf                                 (* pf = 1 or -1 : contradicts pf >= 2 *)
    end
    else ()

let prime_larger_than (bnd:nat)
  : Lemma (ensures exists (p:int). is_prime p /\ p > bnd)
  = let m : int = fact bnd + 1 in                 (* m >= 2 since fact bnd >= 1 *)
    let pf = least_factor m in
    least_factor_prime m;                          (* is_prime pf /\ pf divides m *)
    prime_larger_than_at bnd pf;                   (* pf > bnd *)
    introduce exists (p:int). is_prime p /\ p > bnd with pf and ()

(* a prime exceeding |n| cannot divide the nonzero integer n. *)
let pdle (p n:int)
  : Lemma (requires is_prime p /\ n <> 0 /\ p `divides` n)
          (ensures p <= (if n >= 0 then n else -n))
  = if n > 0 then pos_divisor_le p n
    else (divides_minus p n; pos_divisor_le p (-n))

let not_div_large (p n:int)
  : Lemma (requires is_prime p /\ n <> 0 /\ p > (if n >= 0 then n else -n))
          (ensures ~(p `divides` n))
  = Cl.move_requires (pdle p) n

let exists_prime_not_dividing (n:int)
  : Lemma (requires n <> 0)
          (ensures  exists (p:int). is_prime p /\ ~(p `divides` n))
  = let b : nat = if n >= 0 then n else -n in      (* b = |n| >= 1 *)
    prime_larger_than b;
    eliminate exists (p:int). is_prime p /\ p > b
    returns exists (p:int). is_prime p /\ ~(p `divides` n)
    with hp. (not_div_large p n;
              introduce exists (q:int). is_prime q /\ ~(q `divides` n) with p and ())

(* ================================================================ *)
(*  LAYER 2 (bad-prime => good-prime) — CLOSED.                      *)
(*                                                                   *)
(*  The resultant-reduction algebra lives in                        *)
(*  Core.Factor.ResultantReduction and culminates in                *)
(*    RR.good_of_not_bad (p:int{is_prime p})                        *)
(*         (b: polynomial int{deg b >= 1}) :                         *)
(*      Lemma (requires ~(p `divides` (RR.bad_int b)))              *)
(*            (ensures  PSel.is_good_prime p b)                      *)
(*  where  RR.bad_int b = lc B · res(B, B').                        *)
(*                                                                   *)
(*  Combined with Layer 3 (exists_prime_not_dividing) this closes    *)
(*  good-prime EXISTENCE:  a prime not dividing bad_int B is good.   *)
(* ================================================================ *)

(* GOOD-PRIME EXISTENCE.  For a degree ≥ 1 integer polynomial whose
   bad integer  lc(B)·res(B,B')  is nonzero (which holds whenever B is
   squarefree over ℚ, since then lc B ≠ 0 and res(B,B') ≠ 0), there is
   a prime p that is good for B: p ∤ lc B, deg B̄ = deg B, and B̄ is
   squarefree over 𝔽ₚ.  The witness is any prime not dividing bad_int B,
   supplied by Layer 3 (infinitude of primes). *)
let good_prime_exists (b: polynomial int{deg b >= 1})
  : Lemma (requires RR.bad_int b <> 0)
          (ensures exists (p:int{is_prime p}). PSel.is_good_prime p b)
  = exists_prime_not_dividing (RR.bad_int b);
    eliminate exists (p:int). is_prime p /\ ~(p `divides` (RR.bad_int b))
    returns exists (p:int{is_prime p}). PSel.is_good_prime p b
    with hp.
      ( RR.good_of_not_bad p b;
        introduce exists (q:int{is_prime q}). PSel.is_good_prime q b
        with p and () )

(* ================================================================ *)
(*  C4c — good-prime existence, now UNCONDITIONAL.                   *)
(*                                                                   *)
(*  The R2 residual  bad_int B <> 0  is discharged from squarefree-  *)
(*  ness over ℚ by Core.Factor.BadIntNonzero.bad_int_nonzero (the    *)
(*  ℤ→ℚ det-hom transport of the resultant + resultant_vanishing_iff *)
(*  over ℚ).  Hence for any degree ≥ 1 integer polynomial B whose ℚ- *)
(*  embedding is squarefree, a good prime exists — no side condition.*)
(* ================================================================ *)
let good_prime_exists_sqfree (b: polynomial int{deg b >= 1})
  : Lemma (requires square_free #qq #BIN.ff (embed_zq b))
          (ensures exists (p:int{is_prime p}). PSel.is_good_prime p b)
  = BIN.bad_int_nonzero b;                (* bad_int b <> 0 *)
    good_prime_exists b
