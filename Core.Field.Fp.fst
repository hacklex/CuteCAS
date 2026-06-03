module Core.Field.Fp

(* ================================================================ *)
(*  The finite prime field  F_p = Z/p  as a verified `field`        *)
(*  instance.                                                        *)
(*                                                                   *)
(*  Representation: an element of F_p is a nat in [0, p).            *)
(*  All arithmetic is performed mod p.  Equality (`eq`) is real      *)
(*  decidable equality on the underlying nat, so every congruence    *)
(*  / equatable obligation is discharged by reflexivity of `=`.      *)
(*                                                                   *)
(*  `fp_comm_ring` needs no primality.  `fp_field` uses              *)
(*  `FStar.Math.Euclid.bezout_prime` to build the multiplicative     *)
(*  inverse.                                                         *)
(* ================================================================ *)

module TC = FStar.Tactics.Typeclasses

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
  = (* ((a+b)%p + c)%p = (a+b+c)%p = (a + (b+c)%p)%p *)
    lemma_mod_add_distr c (a + b) p;          (* (c + (a+b)%p)%p = (c+a+b)%p *)
    lemma_mod_add_distr a (b + c) p           (* (a + (b+c)%p)%p = (a+b+c)%p *)

let fp_add_zero (#p:int{p > 1}) (x: fp p)
  : Lemma (fp_add x (fp_zero p) == x /\ fp_add (fp_zero p) x == x)
  = small_mod x p

let fp_add_negation (#p:int{p > 1}) (x: fp p)
  : Lemma (fp_add (fp_neg x) x == fp_zero p /\ fp_add x (fp_neg x) == fp_zero p)
  = (* ((p-x)%p + x) % p = (p-x+x)%p = p%p = 0 *)
    lemma_mod_add_distr x (p - x) p;          (* (x + (p-x)%p)%p = (x+p-x)%p = p%p *)
    lemma_mod_add_distr x ((p - x)) p;
    cancel_mul_mod 1 p;                        (* (1*p)%p = 0 *)
    assert ((x + (p - x)) == 1 * p)

(* ---------------------------------------------------------------- *)
(*  ring laws (no primality)                                         *)
(* ---------------------------------------------------------------- *)

let fp_mul_commutativity (#p:int{p > 1}) (a b: fp p)
  : Lemma (fp_mul a b == fp_mul b a)
  = ()

let fp_mul_associativity (#p:int{p > 1}) (a b c: fp p)
  : Lemma (fp_mul (fp_mul a b) c == fp_mul a (fp_mul b c))
  = (* ((a*b)%p * c)%p = (a*b*c)%p = (a * (b*c)%p)%p *)
    lemma_mod_mul_distr_l (a * b) c p;        (* ((a*b)%p * c)%p = (a*b*c)%p *)
    lemma_mod_mul_distr_r a (b * c) p;        (* (a * (b*c)%p)%p = (a*b*c)%p *)
    assert ((a * b) * c == a * (b * c))

let fp_mul_one (#p:int{p > 1}) (x: fp p)
  : Lemma (fp_mul x (fp_one p) == x /\ fp_mul (fp_one p) x == x)
  = small_mod x p

let fp_left_distributivity (#p:int{p > 1}) (x y z: fp p)
  : Lemma (fp_mul x (fp_add y z) == fp_add (fp_mul x y) (fp_mul x z))
  = (* x * ((y+z)%p) % p = (x*(y+z))%p = (x*y + x*z)%p
       = ((x*y)%p + (x*z)%p)%p *)
    lemma_mod_mul_distr_r x (y + z) p;        (* (x * (y+z)%p)%p = (x*(y+z))%p *)
    assert (x * (y + z) == x * y + x * z);
    modulo_distributivity (x * y) (x * z) p   (* (x*y + x*z)%p = ((x*y)%p + (x*z)%p)%p *)

let fp_right_distributivity (#p:int{p > 1}) (x y z: fp p)
  : Lemma (fp_mul (fp_add y z) x == fp_add (fp_mul y x) (fp_mul z x))
  = lemma_mod_mul_distr_l (y + z) x p;        (* ((y+z)%p * x)%p = ((y+z)*x)%p *)
    assert ((y + z) * x == y * x + z * x);
    modulo_distributivity (y * x) (z * x) p

(* ---------------------------------------------------------------- *)
(*  Bundle assembly: add_comm_group -> ring -> commutative_ring      *)
(* ---------------------------------------------------------------- *)

let fp_equatable (p:int{p > 1}) : equatable (fp p) =
  default_equatable (fp p)

let fp_acg (p:int{p > 1}) : add_comm_group (fp p) = {
  acg_eq            = fp_equatable p;
  zero              = fp_zero p;
  add               = (fun a b -> fp_add a b);
  add_congruence    = (fun _ _ _ _ -> ());
  add_commutativity = (fun a b -> fp_add_commutativity a b);
  add_associativity = (fun a b c -> fp_add_associativity a b c);
  add_zero          = (fun x -> fp_add_zero x);
  neg               = (fun a -> fp_neg a);
  neg_congruence    = (fun _ _ -> ());
  add_negation      = (fun x -> fp_add_negation x);
}

let fp_ring (p:int{p > 1}) : ring (fp p) = {
  r_add                = fp_acg p;
  one                  = fp_one p;
  mul                  = (fun a b -> fp_mul a b);
  mul_congruence       = (fun _ _ _ _ -> ());
  mul_associativity    = (fun a b c -> fp_mul_associativity a b c);
  mul_one              = (fun x -> fp_mul_one x);
  left_distributivity  = (fun x y z -> fp_left_distributivity x y z);
  right_distributivity = (fun x y z -> fp_right_distributivity x y z);
}

let fp_mic (p:int{p > 1}) : mul_is_commutative (fp p) #(fp_ring p) = {
  mul_commutativity = (fun a b -> fp_mul_commutativity a b);
}

let fp_comm_ring (p:int{p > 1}) : commutative_ring (fp p) = {
  cr_r   = fp_ring p;
  cr_mic = fp_mic p;
}

(* ================================================================ *)
(*  Field structure: multiplicative inverse via Bezout              *)
(* ================================================================ *)

(* For 0 < a < p with p prime, bezout_prime gives (r,s) with
   r*p + s*a = 1.  Normalize s into [0,p) to get the inverse. *)
let fp_inv (#p:int{is_prime p}) (a: fp p {a <> 0}) : fp p =
  let (r, s) = bezout_prime p a in
  lemma_mod_lt s p; (((s % p) + p) % p)

(* The Bezout coefficient s satisfies (s * a) % p = 1. *)
let fp_bezout_sa_mod (#p:int{is_prime p}) (a: fp p {a <> 0})
  : Lemma (let (r, s) = bezout_prime p a in (s * a) % p == 1)
  = let (r, s) = bezout_prime p a in
    (* r*p + s*a = 1  ==>  (s*a)%p = (1 - r*p)%p = 1%p = 1 *)
    assert (s * a == 1 + (- r) * p);
    lemma_mod_plus 1 (- r) p;                  (* (1 + (-r)*p)%p = 1%p *)
    small_mod 1 p

(* (inv a * a) % p = 1 and (a * inv a) % p = 1 *)
let fp_inv_correct (#p:int{is_prime p}) (a: fp p {a <> 0})
  : Lemma (fp_mul (fp_inv a) a == fp_one p /\ fp_mul a (fp_inv a) == fp_one p)
  = let (r, s) = bezout_prime p a in
    let ia = fp_inv a in
    fp_bezout_sa_mod a;                        (* (s*a)%p = 1 *)
    (* ia = ((s%p)+p)%p, and (ia * a)%p = (s*a)%p via mod-distr on left *)
    (* (ia * a) % p = (((s%p+p)%p) * a) % p = ((s%p+p) * a) % p *)
    lemma_mod_mul_distr_l ((s % p) + p) a p;
    (* (s%p+p)*a = (s%p)*a + p*a ; reduce the p*a term *)
    lemma_mod_plus ((s % p) * a) a p;          (* ((s%p)*a + a*p)%p = ((s%p)*a)%p *)
    assert (((s % p) + p) * a == (s % p) * a + a * p);
    lemma_mod_mul_distr_l s a p;               (* ((s%p)*a)%p = (s*a)%p *)
    fp_mul_commutativity a ia

let fp_inv_nonzero (#p:int{is_prime p}) (a: fp p {a <> 0})
  : Lemma (fp_inv a <> 0)
  = (* if inv a = 0 then (inv a * a)%p = 0 <> 1 *)
    fp_inv_correct a;
    small_mod 0 p

(* ---------------------------------------------------------------- *)
(*  mul_is_group / skewfield / field assembly                        *)
(* ---------------------------------------------------------------- *)

(* `is_nonzero x` for the fp ring unfolds to `not (eq x zero)`, i.e.
   `not (x = 0)`, i.e. `x <> 0`.

   Wrap inv at the bare element type so the lambda binder is not refined
   by the `<> 0` preconditions of fp_inv / fp_inv_nonzero (which would
   leak into the instance-argument subtyping check on `fp_ring p`). *)
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

let fp_field (p:int{is_prime p}) : field (fp p) =
  let one_ne_zero : squash (not ((fp_one p) = (fp_zero p))) = () in
  {
    f_sf          = fp_skewfield p;
    f_mic         = fp_mic p;
    f_one_ne_zero = one_ne_zero;
  }
