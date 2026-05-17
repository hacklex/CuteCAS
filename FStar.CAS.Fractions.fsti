module FStar.CAS.Fractions

(*
  Public interface for the field-of-fractions construction.

  Given any `integral_domain t`, we build `fraction d` (pairs num/den
  modulo cross-multiplication) and equip it with the full typeclass
  tower up to `field (fraction d)`.

  Heavy proof obligations (associativity / distributivity / congruence /
  domain law / inverse correctness) live in `FStar.CAS.Fractions.fst`.
*)

module TC = FStar.Tactics.Typeclasses

open FStar.CAS.Equatable
open FStar.CAS.Grouplikes
open FStar.CAS.Ringlikes

(* ------------------------------------------------------------------------ *)
(*  Trivial projection instances (transparent so TC can unify chains)       *)
(* ------------------------------------------------------------------------ *)

instance eq_of_id t {| d: integral_domain t |} : equatable t
  = d.commutative_ring.ring.semiring.add_comm_monoid.add_monoid.add_semigroup.has_add.eq

instance has_zero_of_id t {| d: integral_domain t |} : has_zero t
  = d.commutative_ring.ring.semiring.add_comm_monoid.add_monoid.has_zero

instance has_one_of_id t {| d: integral_domain t |} : has_one t
  = d.commutative_ring.mul_comm_monoid.mul_monoid.has_one

(* ------------------------------------------------------------------------ *)
(*  Core types                                                              *)
(* ------------------------------------------------------------------------ *)

type nonzero_of #t (d: integral_domain t) = x:t{x<>zero}

type fraction #t (d: integral_domain t) =
  | Fraction : (num:t) -> (den: nonzero_of d) -> fraction #t d

instance val equatable_of_nonzeros t (d: integral_domain t) : equatable (nonzero_of d)

val ( / ) (#t:Type) {| d: integral_domain t |} (x:t) (y:t)
  : Pure (fraction d) (requires y <> zero) (ensures fun _ -> True)

val fraction_one (t:Type) {| d: integral_domain t |} : fraction d

val product_of_denominators_is_valid_denominator
  (#t:Type) {| d: integral_domain t |} (x y: fraction d)
  : Lemma (x.den * y.den <> (zero <: t))

(* ------------------------------------------------------------------------ *)
(*  Equatable instance                                                      *)
(* ------------------------------------------------------------------------ *)

instance val fraction_equatable t (d: integral_domain t) : equatable (fraction d)

(* ------------------------------------------------------------------------ *)
(*  Additive tower                                                          *)
(* ------------------------------------------------------------------------ *)

val fraction_add (#t:Type) {| dom: integral_domain t |} (x y: fraction dom) : fraction dom

instance val fraction_has_add t (d: integral_domain t) : has_add (fraction d)

val fraction_zero (#t:Type) {| d: integral_domain t |} : fraction d

instance val fraction_has_zero t (d: integral_domain t) : has_zero (fraction d)
instance val fraction_add_semigroup t (d: integral_domain t) : add_semigroup (fraction d)
instance val fraction_add_monoid t (d: integral_domain t) : add_monoid (fraction d)
instance val fraction_add_comm_magma t (d: integral_domain t) : add_comm_magma (fraction d)
instance val fraction_add_comm_semigroup t (d: integral_domain t) : add_comm_semigroup (fraction d)
instance val fraction_add_comm_monoid t (d: integral_domain t) : add_comm_monoid (fraction d)

val fraction_neg (#t:Type) {| d: integral_domain t |} (x: fraction d) : fraction d
val fraction_sub (#t:Type) {| d: integral_domain t |} (x y: fraction d) : fraction d

val fraction_subtraction_definition (#t:Type) {| d: integral_domain t |} (x y: fraction d)
  : Lemma (fraction_sub x y = fraction_add x (fraction_neg y))

instance val fraction_has_neg t (d: integral_domain t) : has_neg (fraction d)
instance val fraction_has_sub t (d: integral_domain t) : has_sub (fraction d)
instance val fraction_add_group t (d: integral_domain t) : add_group (fraction d)
instance val fraction_add_comm_group t (d: integral_domain t) : add_comm_group (fraction d)

(* ------------------------------------------------------------------------ *)
(*  Multiplicative tower                                                    *)
(* ------------------------------------------------------------------------ *)

val fraction_mul (#t:Type) {| d: integral_domain t |} (x y: fraction d) : fraction d

val fraction_one' (#t:Type) {| d: integral_domain t |} : fraction d

instance val fraction_has_mul t (d: integral_domain t) : has_mul (fraction d)
instance val fraction_has_one t (d: integral_domain t) : has_one (fraction d)
instance val fraction_mul_semigroup t (d: integral_domain t) : mul_semigroup (fraction d)
instance val fraction_mul_comm_magma t (d: integral_domain t) : mul_comm_magma (fraction d)
instance val fraction_mul_comm_semigroup t (d: integral_domain t) : mul_comm_semigroup (fraction d)
instance val fraction_mul_monoid t (d: integral_domain t) : mul_monoid (fraction d)
instance val fraction_mul_comm_monoid t (d: integral_domain t) : mul_comm_monoid (fraction d)

(* ------------------------------------------------------------------------ *)
(*  Ring tower                                                              *)
(* ------------------------------------------------------------------------ *)

instance val fraction_semiring t (d: integral_domain t) : semiring (fraction d)
instance val fraction_ring t (d: integral_domain t) : ring (fraction d)
instance val fraction_zero_ne_one_semiring t (d: integral_domain t) : zero_ne_one_semiring (fraction d)
instance val fraction_domain t (d: integral_domain t) : domain (fraction d)
instance val fraction_commutative_ring t (d: integral_domain t) : commutative_ring (fraction d)
instance val fraction_integral_domain t (d: integral_domain t) : integral_domain (fraction d)

val fraction_eq_zero_iff_num_zero (#t:Type) {| dom: integral_domain t |} (x: fraction dom)
  : Lemma ((x = fraction_zero #t #dom) <==> (x.num = (zero <: t)))

val fraction_inv (#t:Type) {| dom: integral_domain t |}
  (x: fraction dom{ x <> fraction_zero #t #dom })
  : fraction dom

val fraction_inv_left (#t:Type) {| dom: integral_domain t |}
  (x: fraction dom{ x <> fraction_zero #t #dom })
  : Lemma (fraction_mul (fraction_inv x) x = fraction_one' #t #dom)

val fraction_inv_right (#t:Type) {| dom: integral_domain t |}
  (x: fraction dom{ x <> fraction_zero #t #dom })
  : Lemma (fraction_mul x (fraction_inv x) = fraction_one' #t #dom)

instance val fraction_division_ring t (d: integral_domain t) : division_ring (fraction d)
instance val fraction_field t (d: integral_domain t) : field (fraction d)
