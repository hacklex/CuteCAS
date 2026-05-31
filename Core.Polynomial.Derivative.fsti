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
  : Lemma (nat_scale 0 x == (zero <: t))

val nat_scale_one (#t:Type) {| acg: add_comm_group t |} (x: t)
  : Lemma (nat_scale 1 x = x)

val nat_scale_succ (#t:Type) {| acg: add_comm_group t |} (n: nat) (x: t)
  : Lemma (nat_scale (Prims.op_Addition n 1) x == x + nat_scale n x)

val nat_scale_add (#t:Type) {| acg: add_comm_group t |} (m n: nat) (x: t)
  : Lemma (ensures nat_scale (Prims.op_Addition m n) x = nat_scale m x + nat_scale n x)

val nat_scale_zero_element (#t:Type) {| acg: add_comm_group t |} (n: nat)
  : Lemma (ensures nat_scale n (zero <: t) = (zero <: t))

val nat_scale_distrib (#t:Type) {| acg: add_comm_group t |} (n: nat) (x y: t)
  : Lemma (ensures nat_scale n (x + y) = nat_scale n x + nat_scale n y)

val nat_scale_mul_left (#t:Type) {| cr: commutative_ring t |} (n: nat) (x y: t)
  : Lemma (ensures nat_scale #t #(cr.cr_r.r_add) n x * y
                 = nat_scale #t #(cr.cr_r.r_add) n (x * y))

val nat_scale_mul_right (#t:Type) {| cr: commutative_ring t |} (n: nat) (x y: t)
  : Lemma (ensures x * nat_scale #t #(cr.cr_r.r_add) n y
                 = nat_scale #t #(cr.cr_r.r_add) n (x * y))

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
                 = nat_scale #t #(cr.cr_r.r_add) (Prims.op_Addition j 1) (coeff p (Prims.op_Addition j 1)))

val poly_deriv_congruence (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t)
  : Lemma (requires poly_eq p q)
          (ensures  poly_eq (poly_deriv p) (poly_deriv q))

val poly_deriv_add (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t)
  : Lemma (ensures poly_eq (poly_deriv (poly_add p q))
                           (poly_add (poly_deriv p) (poly_deriv q)))

val nat_scale_neg (#t:Type) {| acg: add_comm_group t |} (n: nat) (x: t)
  : Lemma (ensures nat_scale n (neg x) = neg (nat_scale n x))

val poly_deriv_neg (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t)
  : Lemma (ensures poly_eq (poly_deriv (poly_neg p))
                          (poly_neg (poly_deriv p)))

val poly_deriv_sub (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t)
  : Lemma (ensures poly_eq (poly_deriv (poly_sub p q))
                          (poly_sub (poly_deriv p) (poly_deriv q)))

val coeff_shift (#t:Type) {| cr: commutative_ring t |} (f: polynomial t) (k: nat)
  : Lemma (coeff ((zero <: t) @ f) k = (if k = 0 then (zero <: t) else coeff f (k - 1)))

val poly_deriv_scalar_mul (#t:Type) {| cr: commutative_ring t |}
  (c: t) (q: polynomial t)
  : Lemma (ensures poly_eq (poly_deriv (poly_mul (c @ poly_zero) q))
                           (poly_mul (c @ poly_zero) (poly_deriv q)))

val shift_add (#t:Type) {| cr: commutative_ring t |}
  (a b: polynomial t)
  : Lemma (poly_eq ((zero <: t) @ (poly_add a b))
                   (poly_add ((zero <: t) @ a) ((zero <: t) @ b)))

val poly_deriv_shift (#t:Type) {| cr: commutative_ring t |}
  (f: polynomial t)
  : Lemma (poly_eq (poly_deriv ((zero <: t) @ f))
                   (poly_add f ((zero <: t) @ (poly_deriv f))))

val shift_mul (#t:Type) {| cr: commutative_ring t |}
  (f g: polynomial t)
  : Lemma (poly_eq (poly_mul ((zero <: t) @ f) g)
                   ((zero <: t) @ (poly_mul f g)))

val shift_congruence (#t:Type) {| cr: commutative_ring t |}
  (f g: polynomial t)
  : Lemma (requires poly_eq f g) (ensures poly_eq ((zero <: t) @ f) ((zero <: t) @ g))

val poly_deriv_cons (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t)
  : Lemma (requires Cons? p)
          (ensures (let p' : polynomial t = L.tl p in
                   poly_eq (poly_deriv p)
                           (poly_add p' ((zero <: t) @ (poly_deriv p')))))

val poly_deriv_mul (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t)
  : Lemma (ensures poly_eq (poly_deriv (poly_mul p q))
                           (poly_add (poly_mul (poly_deriv p) q)
                                     (poly_mul p (poly_deriv q))))