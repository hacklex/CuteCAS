module Core.Polynomial.Derivative

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div

(* ================================================================ *)
(*  Natural scaling: n * x = x + x + ... + x  (n times)             *)
(* ================================================================ *)

val nat_scale (#t:Type) {| acg: add_comm_group t |} (n: nat) (x: t) : t

val nat_scale_zero (#t:Type) {| acg: add_comm_group t |} (x: t)
  : Lemma (nat_scale 0 x == zero)

val nat_scale_one (#t:Type) {| acg: add_comm_group t |} (x: t)
  : Lemma (nat_scale 1 x = x)

val nat_scale_succ (#t:Type) {| acg: add_comm_group t |} (n: nat) (x: t)
  : Lemma (nat_scale (n ++ 1) x == x + nat_scale n x)

val nat_scale_add (#t:Type) {| acg: add_comm_group t |} (m n: nat) (x: t)
  : Lemma (ensures nat_scale (m ++ n) x = nat_scale m x + nat_scale n x)

val nat_scale_zero_element (#t:Type) {| acg: add_comm_group t |} (n: nat)
  : Lemma (ensures nat_scale n (zero <: t) = (zero <: t))

val nat_scale_distrib (#t:Type) {| acg: add_comm_group t |} (n: nat) (x y: t)
  : Lemma (ensures nat_scale n (x + y) = nat_scale n x + nat_scale n y)

val nat_scale_mul_left (#t:Type) {| cr: commutative_ring t |} (n: nat) (x y: t)
  : Lemma (ensures nat_scale n x * y
                 = nat_scale n (x * y))

val nat_scale_mul_right (#t:Type) {| cr: commutative_ring t |} (n: nat) (x y: t)
  : Lemma (ensures x * nat_scale n y
                 = nat_scale n (x * y))

val nat_scale_congruence (#t:Type) {| acg: add_comm_group t |} (n: nat) (x y: t)
  : Lemma (requires x = y)
          (ensures  nat_scale n x = nat_scale n y)

(* ================================================================ *)
(*  Formal derivative                                                *)
(* ================================================================ *)

val poly_deriv (#t:Type) {| cr: commutative_ring t |} (p: polynomial t) : polynomial t

val poly_deriv_zero (#t:Type) {| cr: commutative_ring t |}
  : Lemma (poly_deriv (poly_zero #t #cr) == (poly_zero #t #cr))

val poly_deriv_const (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (requires L.length p <= 1)
          (ensures  poly_deriv p == (poly_zero #t #cr))

val poly_deriv_coeff (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t) (j: nat)
  : Lemma (ensures coeff (poly_deriv p) j
                 = nat_scale (j ++ 1) (coeff p (j ++ 1)))

val poly_deriv_congruence (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t)
  : Lemma (requires (p = q))
          (ensures  (poly_deriv p = poly_deriv q))

val poly_deriv_add (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t)
  : Lemma (ensures (poly_deriv (p + q)) = ((poly_deriv p) + (poly_deriv q)))

val nat_scale_neg (#t:Type) {| acg: add_comm_group t |} (n: nat) (x: t)
  : Lemma (ensures nat_scale n (- x) = (- (nat_scale n x)))

val poly_deriv_neg (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t)
  : Lemma (ensures (poly_deriv (- p)) = (- (poly_deriv p)))

val poly_deriv_sub (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t)
  : Lemma (ensures (poly_deriv (p -- q)) = ((poly_deriv p) -- (poly_deriv q)))

val coeff_shift (#t:Type) {| cr: commutative_ring t |} (f: polynomial t) (k: nat)
  : Lemma (coeff (zero @ f) k = (if k = 0 then zero else coeff f (k - 1)))

val poly_deriv_scalar_mul (#t:Type) {| cr: commutative_ring t |}
  (c: t) (q: polynomial t)
  : Lemma (ensures (poly_deriv ((c @ poly_zero) * q)) = ((c @ poly_zero) * (poly_deriv q)))

val shift_add (#t:Type) {| cr: commutative_ring t |}
  (a b: polynomial t)
  : Lemma ((zero @ (a + b)) = ((zero @ a) + (zero @ b)))

val poly_deriv_shift (#t:Type) {| cr: commutative_ring t |}
  (f: polynomial t)
  : Lemma ((poly_deriv (zero @ f)) = (f + (zero @ (poly_deriv f))))

val shift_mul (#t:Type) {| cr: commutative_ring t |}
  (f g: polynomial t)
  : Lemma (((zero @ f) * g) = (zero @ (f * g)))

val shift_congruence (#t:Type) {| cr: commutative_ring t |}
  (f g: polynomial t)
  : Lemma (requires (f = g)) (ensures ((zero @ f) = (zero @ g)))

val poly_deriv_cons (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t)
  : Lemma (requires Cons? p)
          (ensures (let p' : polynomial t = L.tl p in
                   ((poly_deriv p) = (p' + (zero @ (poly_deriv p'))))))

val poly_deriv_mul (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t)
  : Lemma (ensures (poly_deriv (p * q)) = (((poly_deriv p) * q) + (p * (poly_deriv q))))