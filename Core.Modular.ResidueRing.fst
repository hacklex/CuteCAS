module Core.Modular.ResidueRing

(* ================================================================ *)
(*  ℤ/m as a finite commutative RING, for ANY modulus m > 1         *)
(*  (m need NOT be prime).                                           *)
(*                                                                   *)
(*  Carrier `zmod m` is a DISTINCT newtype (constructor `Zm`), not a *)
(*  `fin`/`nat` alias, so it shares no typeclass instance with the   *)
(*  prime field `fp` of Core.Modular.GaloisField.  That removes the  *)
(*  ring/field instance duality: `zmod m` carries ONLY a            *)
(*  `commutative_ring` instance (resolved for every m>1, including a  *)
(*  symbolic modulus such as Hensel's pᵏ); `fp p` carries ONLY a     *)
(*  `field` instance.                                                 *)
(*                                                                   *)
(*  Arithmetic is mod-m on the wrapped value; laws mirror the prime  *)
(*  field's (they need no primality).                                *)
(* ================================================================ *)

open Core.Algebra
open FStar.Math.Lemmas

(* ---------------------------------------------------------------- *)
(*  Representation and element operations                            *)
(* ---------------------------------------------------------------- *)

type zmod (m:int) = | Zm : v:nat{v < m} -> zmod m

let zv (#m:int{m > 1}) (x: zmod m) : (r:nat{r < m}) = Zm?.v x

let zmod_zero (m:int{m > 1}) : zmod m = Zm 0
let zmod_one  (m:int{m > 1}) : zmod m = Zm 1

let zmod_add (#m:int{m > 1}) (a b: zmod m) : zmod m =
  lemma_mod_lt (zv a + zv b) m; Zm ((zv a + zv b) % m)

let zmod_mul (#m:int{m > 1}) (a b: zmod m) : zmod m =
  lemma_mod_lt (zv a * zv b) m; Zm ((zv a * zv b) % m)

let zmod_neg (#m:int{m > 1}) (a: zmod m) : zmod m =
  lemma_mod_lt (m - zv a) m; Zm ((m - zv a) % m)

(* ---------------------------------------------------------------- *)
(*  add_comm_group laws                                              *)
(* ---------------------------------------------------------------- *)

let zmod_add_commutativity (#m:int{m > 1}) (a b: zmod m)
  : Lemma (zmod_add a b == zmod_add b a)
  = ()

let zmod_add_associativity (#m:int{m > 1}) (a b c: zmod m)
  : Lemma (zmod_add (zmod_add a b) c == zmod_add a (zmod_add b c))
  = lemma_mod_add_distr (zv c) (zv a + zv b) m;
    lemma_mod_add_distr (zv a) (zv b + zv c) m

let zmod_add_zero (#m:int{m > 1}) (x: zmod m)
  : Lemma (zmod_add x (zmod_zero m) == x /\ zmod_add (zmod_zero m) x == x)
  = small_mod (zv x) m

let zmod_add_negation (#m:int{m > 1}) (x: zmod m)
  : Lemma (zmod_add (zmod_neg x) x == zmod_zero m /\ zmod_add x (zmod_neg x) == zmod_zero m)
  = lemma_mod_add_distr (zv x) (m - zv x) m;
    cancel_mul_mod 1 m;
    assert ((zv x + (m - zv x)) == 1 * m)

(* ---------------------------------------------------------------- *)
(*  ring laws                                                        *)
(* ---------------------------------------------------------------- *)

let zmod_mul_commutativity (#m:int{m > 1}) (a b: zmod m)
  : Lemma (zmod_mul a b == zmod_mul b a)
  = ()

let zmod_mul_associativity (#m:int{m > 1}) (a b c: zmod m)
  : Lemma (zmod_mul (zmod_mul a b) c == zmod_mul a (zmod_mul b c))
  = lemma_mod_mul_distr_l (zv a * zv b) (zv c) m;
    lemma_mod_mul_distr_r (zv a) (zv b * zv c) m;
    assert ((zv a * zv b) * zv c == zv a * (zv b * zv c))

let zmod_mul_one (#m:int{m > 1}) (x: zmod m)
  : Lemma (zmod_mul x (zmod_one m) == x /\ zmod_mul (zmod_one m) x == x)
  = small_mod (zv x) m

let zmod_left_distributivity (#m:int{m > 1}) (x y z: zmod m)
  : Lemma (zmod_mul x (zmod_add y z) == zmod_add (zmod_mul x y) (zmod_mul x z))
  = lemma_mod_mul_distr_r (zv x) (zv y + zv z) m;
    assert (zv x * (zv y + zv z) == zv x * zv y + zv x * zv z);
    modulo_distributivity (zv x * zv y) (zv x * zv z) m

let zmod_right_distributivity (#m:int{m > 1}) (x y z: zmod m)
  : Lemma (zmod_mul (zmod_add y z) x == zmod_add (zmod_mul y x) (zmod_mul z x))
  = lemma_mod_mul_distr_l (zv y + zv z) (zv x) m;
    assert ((zv y + zv z) * zv x == zv y * zv x + zv z * zv x);
    modulo_distributivity (zv y * zv x) (zv z * zv x) m

(* ---------------------------------------------------------------- *)
(*  Bundle assembly: add_comm_group -> ring -> commutative_ring      *)
(*  The ONLY instance for zmod (commutative ring; no field).         *)
(* ---------------------------------------------------------------- *)

let zmod_equatable (m:int{m > 1}) : equatable (zmod m) =
  default_equatable (zmod m)

let zmod_acg (m:int{m > 1}) : add_comm_group (zmod m) = {
  acg_eq            = zmod_equatable m;
  zero              = zmod_zero m;
  add               = zmod_add;
  add_commutativity = zmod_add_commutativity;
  add_associativity = zmod_add_associativity;
  add_zero          = zmod_add_zero;
  neg               = zmod_neg;
  add_negation      = zmod_add_negation;
  add_congruence    = (fun _ _ _ _ -> ());
  neg_congruence    = (fun _ _ -> ());
}

let zmod_ring (m:int{m > 1}) : ring (zmod m) = {
  r_add                = zmod_acg m;
  one                  = zmod_one m;
  mul                  = zmod_mul;
  mul_associativity    = zmod_mul_associativity;
  mul_one              = zmod_mul_one;
  left_distributivity  = zmod_left_distributivity;
  right_distributivity = zmod_right_distributivity;
  mul_congruence       = (fun _ _ _ _ -> ());
}

let zmod_mic (m:int{m > 1}) : mul_is_commutative (zmod m) #(zmod_ring m) = {
  mul_commutativity = zmod_mul_commutativity;
}

instance zmod_comm_ring (m:int{m > 1}) : commutative_ring (zmod m) = {
  cr_r   = zmod_ring m;
  cr_mic = zmod_mic m;
}
