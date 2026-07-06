module Core.Modular.PrimeField

(* ================================================================ *)
(*  The finite prime field  F_p = Z/p  as a verified `field`        *)
(*  instance — and ONLY a field.                                     *)
(*                                                                   *)
(*  Representation: `fp p = n:nat{n<p}` (= fin p).  Arithmetic is    *)
(*  mod p.  There is deliberately NO `commutative_ring (fp p)`       *)
(*  instance: when a ring is needed at a prime modulus, it resolves  *)
(*  through the field's projection chain (field → integral_domain →  *)
(*  commutative_ring), a single path.  The composite finite ring     *)
(*  ℤ/m lives in Core.Modular.GaloisRing as the distinct `zmod`      *)
(*  newtype, so there is no ring/field instance overlap on one type. *)
(*                                                                   *)
(*  Inverse via FStar.Math.Euclid.bezout_prime (needs primality).   *)
(* ================================================================ *)

module L  = FStar.List.Tot

open Core.Algebra
open FStar.Math.Euclid
open FStar.Math.Lemmas

(* ---------------------------------------------------------------- *)
(*  Representation and element operations                            *)
(* ---------------------------------------------------------------- *)

let fp (p:int{p > 1}) = n:nat{n < p}

let fp_zero (p:int{p > 1}) : fp p = 0
let fp_one  (p:int{p > 1}) : fp p = 1

let fp_add (#p:int{p > 1}) (a b: fp p) : fp p =
  lemma_mod_lt (a + b) p; (a + b) % p

let fp_mul (#p:int{p > 1}) (a b: fp p) : fp p =
  lemma_mod_lt (a * b) p; (a * b) % p

let fp_neg (#p:int{p > 1}) (a: fp p) : fp p =
  lemma_mod_lt (p - a) p; (p - a) % p

(* ---------------------------------------------------------------- *)
(*  add_comm_group laws (no primality)                               *)
(* ---------------------------------------------------------------- *)

let fp_add_commutativity (#p:int{p > 1}) (a b: fp p)
  : Lemma (fp_add a b == fp_add b a)
  = ()

let fp_add_associativity (#p:int{p > 1}) (a b c: fp p)
  : Lemma (fp_add (fp_add a b) c == fp_add a (fp_add b c))
  = lemma_mod_add_distr c (a + b) p;
    lemma_mod_add_distr a (b + c) p

let fp_add_zero (#p:int{p > 1}) (x: fp p)
  : Lemma (fp_add x (fp_zero p) == x /\ fp_add (fp_zero p) x == x)
  = small_mod x p

let fp_add_negation (#p:int{p > 1}) (x: fp p)
  : Lemma (fp_add (fp_neg x) x == fp_zero p /\ fp_add x (fp_neg x) == fp_zero p)
  = lemma_mod_add_distr x (p - x) p;
    lemma_mod_add_distr x ((p - x)) p;
    cancel_mul_mod 1 p;
    assert ((x + (p - x)) == 1 * p)

(* ---------------------------------------------------------------- *)
(*  ring laws (no primality)                                         *)
(* ---------------------------------------------------------------- *)

let fp_mul_commutativity (#p:int{p > 1}) (a b: fp p)
  : Lemma (fp_mul a b == fp_mul b a)
  = ()

let fp_mul_associativity (#p:int{p > 1}) (a b c: fp p)
  : Lemma (fp_mul (fp_mul a b) c == fp_mul a (fp_mul b c))
  = lemma_mod_mul_distr_l (a * b) c p;
    lemma_mod_mul_distr_r a (b * c) p;
    assert ((a * b) * c == a * (b * c))

let fp_mul_one (#p:int{p > 1}) (x: fp p)
  : Lemma (fp_mul x (fp_one p) == x /\ fp_mul (fp_one p) x == x)
  = small_mod x p

let fp_left_distributivity (#p:int{p > 1}) (x y z: fp p)
  : Lemma (fp_mul x (fp_add y z) == fp_add (fp_mul x y) (fp_mul x z))
  = lemma_mod_mul_distr_r x (y + z) p;
    assert (x * (y + z) == x * y + x * z);
    modulo_distributivity (x * y) (x * z) p

let fp_right_distributivity (#p:int{p > 1}) (x y z: fp p)
  : Lemma (fp_mul (fp_add y z) x == fp_add (fp_mul y x) (fp_mul z x))
  = lemma_mod_mul_distr_l (y + z) x p;
    assert ((y + z) * x == y * x + z * x);
    modulo_distributivity (y * x) (z * x) p

(* ---------------------------------------------------------------- *)
(*  Bundle assembly (ring pieces are `let` building-blocks, NOT      *)
(*  instances; only `fp_field` below is an instance).                *)
(* ---------------------------------------------------------------- *)

let fp_equatable (p:int{p > 1}) : equatable (fp p) =
  default_equatable (fp p)

let fp_acg (p:int{p > 1}) : add_comm_group (fp p) = {
  acg_eq            = fp_equatable p;
  zero              = fp_zero p;
  add               = fp_add;
  add_commutativity = fp_add_commutativity;
  add_associativity = fp_add_associativity;
  add_zero          = fp_add_zero;
  neg               = fp_neg;
  add_negation      = fp_add_negation;
  add_congruence    = (fun _ _ _ _ -> ());
  neg_congruence    = (fun _ _ -> ());
}

let fp_ring (p:int{p > 1}) : ring (fp p) = {
  r_add                = fp_acg p;
  one                  = fp_one p;
  mul                  = fp_mul;
  mul_associativity    = fp_mul_associativity;
  mul_one              = fp_mul_one;
  left_distributivity  = fp_left_distributivity;
  right_distributivity = fp_right_distributivity;
  mul_congruence       = (fun _ _ _ _ -> ());
}

let fp_mic (p:int{p > 1}) : mul_is_commutative (fp p) #(fp_ring p) = {
  mul_commutativity = fp_mul_commutativity;
}

(* ================================================================ *)
(*  Field structure: multiplicative inverse via Bezout              *)
(* ================================================================ *)

let fp_inv (#p:int{is_prime p}) (a: fp p {a <> 0}) : fp p =
  let (r, s) = bezout_prime p a in
  lemma_mod_lt s p; (((s % p) + p) % p)

let fp_bezout_sa_mod (#p:int{is_prime p}) (a: fp p {a <> 0})
  : Lemma (let (r, s) = bezout_prime p a in (s * a) % p == 1)
  = let (r, s) = bezout_prime p a in
    assert (s * a == 1 + (- r) * p);
    lemma_mod_plus 1 (- r) p;
    small_mod 1 p

let fp_inv_correct (#p:int{is_prime p}) (a: fp p {a <> 0})
  : Lemma (fp_mul (fp_inv a) a == fp_one p /\ fp_mul a (fp_inv a) == fp_one p)
  = let (r, s) = bezout_prime p a in
    let ia = fp_inv a in
    fp_bezout_sa_mod a;
    lemma_mod_mul_distr_l ((s % p) + p) a p;
    lemma_mod_plus ((s % p) * a) a p;
    assert (((s % p) + p) * a == (s % p) * a + a * p);
    lemma_mod_mul_distr_l s a p;
    fp_mul_commutativity a ia

let fp_inv_nonzero (#p:int{is_prime p}) (a: fp p {a <> 0})
  : Lemma (fp_inv a <> 0)
  = fp_inv_correct a;
    small_mod 0 p

(* ---------------------------------------------------------------- *)
(*  mul_is_group / skewfield / field assembly                        *)
(* ---------------------------------------------------------------- *)

let fp_inv_member (p:int{is_prime p}) (x: fp p)
  : Pure (fp p) (requires x <> 0) (ensures fun y -> y <> 0)
  = fp_inv_nonzero x; fp_inv x

let fp_mig (p:int{is_prime p}) : mul_is_group (fp p) #(fp_ring p) = {
    inv             = (fun (x: fp p) -> fp_inv_member p x);
    inv_congr       = (fun _ _ -> ());
    inversion_lemma = (fun (x: fp p) -> fp_inv_correct x);
  }

let fp_skewfield (p:int{is_prime p}) : skewfield (fp p) = {
  sf_r   = fp_ring p;
  sf_mig = fp_mig p;
}

let fp_one_ne_zero (p:int{is_prime p})
  : Lemma (not ((fp_one p) = (fp_zero p)))
  = ()

instance fp_field (p:int{is_prime p}) : field (fp p) =
  {
    f_sf          = fp_skewfield p;
    f_mic         = fp_mic p;
    f_one_ne_zero = ();
  }

(* ================================================================ *)
(*  Enumeration of the finite prime field  fp p = {0,1,...,p-1}.     *)
(* ================================================================ *)

let rec fp_enum_from (p:int{p > 1}) (lo:nat{lo <= p}) : Tot (list (fp p)) (decreases (p - lo)) =
  if lo = p then []
  else (lo <: fp p) :: fp_enum_from p (lo + 1)

let fp_enum (p:int{p > 1}) : list (fp p) = fp_enum_from p 0

let rec fp_enum_from_length (p:int{p > 1}) (lo:nat{lo <= p})
  : Lemma (ensures L.length (fp_enum_from p lo) == p - lo) (decreases (p - lo))
  = if lo = p then () else fp_enum_from_length p (lo + 1)

let fp_enum_length (p:int{p > 1}) : Lemma (L.length (fp_enum p) == p)
  = fp_enum_from_length p 0

let rec fp_enum_from_mem (p:int{p > 1}) (lo:nat{lo <= p}) (c: fp p)
  : Lemma (ensures (c >= lo) == L.mem c (fp_enum_from p lo)) (decreases (p - lo))
  = if lo = p then ()
    else fp_enum_from_mem p (lo + 1) c

let fp_enum_complete (p:int{p > 1}) (c: fp p)
  : Lemma (L.mem c (fp_enum p))
  = fp_enum_from_mem p 0 c
