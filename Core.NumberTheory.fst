module Core.NumberTheory

(* ================================================================ *)
(*  Core.NumberTheory — our own fast replacement for                 *)
(*  FStar.Math.Euclid.  The point: `is_prime` is OPAQUE, so a        *)
(*  refinement  p:int{is_prime p}  does NOT drag a quantified        *)
(*  formula into every VC over  fp p / polynomial (fp p)  (measured  *)
(*  ~2-3x slowdown otherwise).  divides / is_gcd are defined with    *)
(*  the same bodies as the stdlib (defeq), and every fact is proven  *)
(*  by delegating to the stdlib INTERNALLY — that cost is paid once  *)
(*  here and never exposed.  Consumers use ONLY this module.         *)
(* ================================================================ *)

module EU = FStar.Math.Euclid

open FStar.Pervasives

(* ---------------- divisibility --------------------------------- *)
(* divides / is_gcd are NOT the perf problem (an `exists`/gcd-`forall`
   in proof positions, never a pervasive refinement) — only `is_prime`
   is.  So they are `unfold` aliases to the stdlib: consumers name only
   `Core.NumberTheory`, the delegations below are trivial, and no
   quantifier-bridging friction arises.  `is_prime` alone is genuinely
   opaque-and-ours (that is the measured win). *)

unfold let divides (a b:int) : prop = EU.divides a b

let divides_reflexive (a:int) : Lemma (divides a a) [SMTPat (divides a a)]
  = EU.divides_reflexive a

let divides_transitive (a b c:int)
  : Lemma (requires divides a b /\ divides b c) (ensures divides a c)
  = EU.divides_transitive a b c

let divide_antisym (a b:int)
  : Lemma (requires divides a b /\ divides b a) (ensures a = b \/ a = -b)
  = EU.divide_antisym a b

let divides_0 (a:int) : Lemma (divides a 0) = EU.divides_0 a

let divides_1 (a:int) : Lemma (requires divides a 1) (ensures a = 1 \/ a = -1)
  = EU.divides_1 a

let divides_minus (a b:int) : Lemma (requires divides a b) (ensures divides a (-b))
  = EU.divides_minus a b

let divides_opp (a b:int) : Lemma (requires divides a b) (ensures divides (-a) b)
  = EU.divides_opp a b

let divides_plus (a b d:int)
  : Lemma (requires divides d a /\ divides d b) (ensures divides d (a + b))
  = EU.divides_plus a b d

let divides_sub (a b d:int)
  : Lemma (requires divides d a /\ divides d b) (ensures divides d (a - b))
  = EU.divides_sub a b d

let divides_mult_right (a b d:int)
  : Lemma (requires divides d b) (ensures divides d (a * b))
  = EU.divides_mult_right a b d

(* ---------------- gcd (same body as EU: defeq) ------------------- *)

unfold let is_gcd (a b d:int) : prop = EU.is_gcd a b d

let mod_divides (a:int) (b:int{b <> 0})
  : Lemma (requires a % b = 0) (ensures divides b a)
  = EU.mod_divides a b

let divides_mod (a:int) (b:int{b <> 0})
  : Lemma (requires divides b a) (ensures a % b = 0)
  = EU.divides_mod a b

let is_gcd_unique (a b c d:int)
  : Lemma (requires is_gcd a b c /\ is_gcd a b d) (ensures c = d \/ c = -d)
  = EU.is_gcd_unique a b c d

let is_gcd_reflexive (a:int) : Lemma (is_gcd a a a) = EU.is_gcd_reflexive a

let is_gcd_symmetric (a b d:int)
  : Lemma (requires is_gcd a b d) (ensures is_gcd b a d)
  = EU.is_gcd_symmetric a b d

let is_gcd_0 (a:int) : Lemma (is_gcd a 0 a) = EU.is_gcd_0 a

let is_gcd_1 (a:int) : Lemma (is_gcd a 1 1) = EU.is_gcd_1 a

let is_gcd_minus (a b d:int)
  : Lemma (requires is_gcd a (-b) d) (ensures is_gcd b a d)
  = EU.is_gcd_minus a b d

let is_gcd_opp (a b d:int)
  : Lemma (requires is_gcd a b d) (ensures is_gcd b a (-d))
  = EU.is_gcd_opp a b d

let is_gcd_plus (a b q d:int)
  : Lemma (requires is_gcd a b d) (ensures is_gcd a (b + q * a) d)
  = EU.is_gcd_plus a b q d

let euclid_gcd (a b:int) : Pure (int & int & int)
  (requires True)
  (ensures  fun (r, s, d) -> r * a + s * b = d /\ is_gcd a b d)
  = EU.euclid_gcd a b

(* ---------------- primality: OPAQUE (the whole point) ------------ *)

(* The heavy quantifier, hidden.  It is EXACTLY the body of EU.is_prime's
   second conjunct (same divides, same pattern), so revealing it yields
   EU.is_prime verbatim — a trivial, robust bridge. *)
[@@"opaque_to_smt"]
let prime_witness (p:int) : prop =
  forall (d:int).{:pattern (EU.divides d p)}
    (EU.divides d p ==> (d = 1 \/ d = -1 \/ d = p \/ d = -p))

let is_prime (p:int) : prop = 1 < p /\ prime_witness p

let is_prime_gt1 (p:int) : Lemma (requires is_prime p) (ensures 1 < p) = ()

let is_prime_to_eu (p:int) : Lemma (requires is_prime p) (ensures EU.is_prime p)
  = reveal_opaque (`%prime_witness) (prime_witness p)

let is_prime_of_eu (p:int) : Lemma (requires EU.is_prime p) (ensures is_prime p)
  = reveal_opaque (`%prime_witness) (prime_witness p)

(* intro/elim of the primality witness — for the few sites that CONSTRUCT or
   USE the underlying forall (trial division, least-factor, Euclid's lemma).
   The quantifier surfaces ONLY here, never at the 247 refinement sites. *)
let is_prime_elim (p:int)
  : Lemma (requires is_prime p)
          (ensures  1 < p /\ (forall (d:int). divides d p ==> (d = 1 \/ d = -1 \/ d = p \/ d = -p)))
  = reveal_opaque (`%prime_witness) (prime_witness p)

let is_prime_intro (p:int)
  : Lemma (requires 1 < p /\ (forall (d:int). divides d p ==> (d = 1 \/ d = -1 \/ d = p \/ d = -p)))
          (ensures  is_prime p)
  = reveal_opaque (`%prime_witness) (prime_witness p)

(* composite elim: n>1 and not prime ⇒ a proper (nontrivial) divisor exists. *)
let not_prime_elim (n:int)
  : Lemma (requires n > 1 /\ ~(is_prime n))
          (ensures  exists (d:int). divides d n /\ ~(d = 1 \/ d = -1 \/ d = n \/ d = -n))
  = reveal_opaque (`%prime_witness) (prime_witness n)

let bezout_prime (p:int) (a:pos{a < p}) : Pure (int & int)
  (requires is_prime p)
  (ensures  fun (r, s) -> r * p + s * a = 1)
  = is_prime_to_eu p;
    EU.bezout_prime p a

let euclid (n:pos) (a b r s:int)
  : Lemma (requires (a * b) % n = 0 /\ r * n + s * a = 1) (ensures b % n = 0)
  = EU.euclid n a b r s

let euclid_prime (p:int{is_prime p}) (a b:int)
  : Lemma (requires (a * b) % p = 0) (ensures a % p = 0 \/ b % p = 0)
  = is_prime_to_eu p;
    EU.euclid_prime p a b
