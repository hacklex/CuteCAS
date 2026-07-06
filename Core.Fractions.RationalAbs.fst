module Core.Fractions.RationalAbs

(* ================================================================ *)
(*  A small ℚ-absolute-value + order fragment on                    *)
(*    qq = fraction int_id    (ℚ).                                  *)
(*                                                                  *)
(*  This is the prerequisite for the §D Kronecker coefficient       *)
(*  bound.  It is NOT a full ordered_field typeclass — just the     *)
(*  pieces needed downstream:                                       *)
(*    q_abs, q_abs_well_defined, q_abs_mul,                         *)
(*    q_le (decidable bool), q_le_refl, q_le_well_defined,          *)
(*    q_abs_nonneg, q_abs_triangle.                                 *)
(*                                                                  *)
(*  NO admit / assume / sorry.                                      *)
(* ================================================================ *)

module H  = Core.Algebra.Helpers
module ML = FStar.Math.Lemmas

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Fractions
open Core.FinSum

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------- *)
(*  ℚ and its commutative_ring — mirror Core.Polynomial.EmbedQ.     *)
(* ---------------------------------------------------------------- *)

let qq : Type = fraction int_id

(* The ℚ commutative_ring, reached from the single published
   `fraction_field int int_id` via the foundation chain
   id_of_f ∘ cr_of_id (mirrors Core.Polynomial.EmbedQ.crq).  Its
   additive group `crq.cr_r.r_add` is the `add_comm_group qq` that
   `Core.FinSum.sum_range` resolves to for ℚ. *)
let crq : commutative_ring qq =
  cr_of_id (fraction int_id)

(* the qq additive group used by sum_range below. *)
let qacg : add_comm_group qq = crq.cr_r.r_add

(* ---------------------------------------------------------------- *)
(*  Integer absolute value (re-derived locally to avoid an awkward   *)
(*  import of Core.Modular.LagrangeBound).                      *)
(* ---------------------------------------------------------------- *)

let iabs (a:int) : int = if a >= 0 then a else - a

let iabs_mul (a k: int)
  : Lemma (iabs (a * k) == iabs a * iabs k)
  = ()

(* iabs is zero iff its argument is zero. *)
let iabs_zero_iff (a: int)
  : Lemma ((iabs a = 0) <==> (a = 0))
  = ()

(* iabs is always nonnegative. *)
let iabs_nonneg (a: int)
  : Lemma (iabs a >= 0)
  = ()

(* the integer triangle inequality. *)
let iabs_triangle (a b: int)
  : Lemma (iabs (a + b) <= iabs a + iabs b)
  = ()

(* ---------------------------------------------------------------- *)
(*  Helpers to read num/den of a fraction as ints.                  *)
(* ---------------------------------------------------------------- *)

unfold let qnum (x: qq) : int = Fraction?.num x
unfold let qden (x: qq) : int = Fraction?.den x

(* For int, is_nonzero den is precisely den <> 0, so the denominator
   of any qq is a nonzero int. *)
let qden_nonzero (x: qq)
  : Lemma (qden x <> 0)
  = ()

(* ================================================================ *)
(*  1.  q_abs                                                        *)
(* ================================================================ *)

let q_abs (x: qq) : qq =
  (* denominator iabs (den x) <> 0 since den x <> 0 *)
  qden_nonzero x;
  iabs_zero_iff (qden x);
  Fraction (iabs (qnum x)) (iabs (qden x))

(* num/den reveals for q_abs (definitional). *)
let q_abs_num (x: qq)
  : Lemma (qnum (q_abs x) == iabs (qnum x))
  = ()

let q_abs_den (x: qq)
  : Lemma (qden (q_abs x) == iabs (qden x))
  = ()

(* ================================================================ *)
(*  2.  q_abs_well_defined                                          *)
(* ================================================================ *)

let q_abs_well_defined (x y: qq)
  : Lemma (requires x = y) (ensures q_abs x = q_abs y)
  = fraction_eq_reveal x y;
    (* num x * den y == den x * num y *)
    assert (qnum x * qden y == qden x * qnum y);
    iabs_mul (qnum x) (qden y);
    iabs_mul (qden x) (qnum y);
    (* iabs(num x)*iabs(den y) == iabs(den x)*iabs(num y) *)
    assert (iabs (qnum x) * iabs (qden y) == iabs (qden x) * iabs (qnum y));
    fraction_eq_reveal (q_abs x) (q_abs y)

(* ================================================================ *)
(*  3.  q_abs_mul                                                   *)
(* ================================================================ *)

let q_abs_mul (x y: qq)
  : Lemma (q_abs (fraction_mul x y) = fraction_mul (q_abs x) (q_abs y))
  = fraction_mul_reveal x y;
    (* num(x*y) == num x * num y, den(x*y) == den x * den y *)
    fraction_mul_reveal (q_abs x) (q_abs y);
    iabs_mul (qnum x) (qnum y);
    iabs_mul (qden x) (qden y);
    (* num(q_abs(x*y)) = iabs(num x * num y) = iabs(num x)*iabs(num y)
                       = num(q_abs x * q_abs y)  -- and same for den *)
    let lhs = q_abs (fraction_mul x y) in
    let rhs = fraction_mul (q_abs x) (q_abs y) in
    assert (qnum lhs == iabs (qnum x) * iabs (qnum y));
    assert (qden lhs == iabs (qden x) * iabs (qden y));
    assert (qnum rhs == iabs (qnum x) * iabs (qnum y));
    assert (qden rhs == iabs (qden x) * iabs (qden y));
    fraction_eq_reveal lhs rhs

(* ================================================================ *)
(*  4.  q_le  (sign-safe, denominators cleared by their squares)     *)
(*                                                                  *)
(*  num x / den x <= num y / den y                                  *)
(*    <==> num x * den x * (den y)^2 <= num y * den y * (den x)^2    *)
(*  (multiply both sides by (den x)^2 (den y)^2 > 0).               *)
(* ================================================================ *)

let q_le (x y: qq) : bool =
  (qnum x * qden x * (qden y * qden y))
    <= (qnum y * qden y * (qden x * qden x))

(* ================================================================ *)
(*  5.  q_le_refl                                                   *)
(* ================================================================ *)

let q_le_refl (x: qq)
  : Lemma (q_le x x)
  = ()

(* ================================================================ *)
(*  7.  q_abs_nonneg :  0 <= |x|                                     *)
(* ================================================================ *)

let q_abs_nonneg (x: qq)
  : Lemma (q_le (fraction_zero int) (q_abs x))
  = let z = fraction_zero int in
    let a = q_abs x in
    fraction_zero_reveal int #int_id;            (* num z == 0, den z == 1 *)
    assert (qnum z == 0 /\ qden z == 1);
    q_abs_num x; q_abs_den x;                     (* num a, den a are iabs's *)
    iabs_nonneg (qnum x); iabs_nonneg (qden x);
    assert (qnum a >= 0 /\ qden a >= 0);
    (* q_le z a = (num z * den z * (den a)^2) <= (num a * den a * (den z)^2)
               = 0 <= num a * den a                                       *)
    assert (qnum z * qden z * (qden a * qden a) == 0);
    ML.lemma_mult_le_left (qnum a) 0 (qden a);    (* 0 <= num a * den a *)
    assert (qnum a * qden a >= 0);
    assert (qnum a * qden a * (qden z * qden z) == qnum a * qden a)

(* ================================================================ *)
(*  8.  q_abs_triangle :  |x + y| <= |x| + |y|                       *)
(*                                                                  *)
(*  Both q_abs(x+y) and q_abs x + q_abs y share the SAME            *)
(*  denominator  D = iabs(den x) * iabs(den y) > 0, so q_le reduces *)
(*  to a numerator comparison scaled by D^3 >= 0, and the           *)
(*  numerator comparison is the integer triangle inequality.        *)
(* ================================================================ *)

(* monotonicity of multiplication by a nonnegative factor m for the
   particular shape (p <= q ==> p * m <= q * m). *)
let mono_mul_nonneg (p q m: int)
  : Lemma (requires p <= q /\ m >= 0) (ensures p * m <= q * m)
  = ML.lemma_mult_le_right m p q

(* product of two nonnegative ints is nonnegative. *)
let nonneg_mul (a b: int)
  : Lemma (requires a >= 0 /\ b >= 0) (ensures a * b >= 0)
  = ML.lemma_mult_le_right b 0 a

(* d >= 0 ==> d * (d * d) >= 0. *)
let nonneg_cube (d: int)
  : Lemma (requires d >= 0) (ensures d * (d * d) >= 0)
  = nonneg_mul d d;
    nonneg_mul d (d * d)

let q_abs_triangle (x y: qq)
  : Lemma (q_le (q_abs (fraction_add x y)) (fraction_add (q_abs x) (q_abs y)))
  = let s   = fraction_add x y in           (* x + y *)
    let lhs = q_abs s in                     (* |x + y| *)
    let rhs = fraction_add (q_abs x) (q_abs y) in   (* |x| + |y| *)
    (* shape of s *)
    fraction_add_reveal x y;
    assert (qnum s == qnum x * qden y + qden x * qnum y);
    assert (qden s == qden x * qden y);
    (* shape of lhs = q_abs s *)
    q_abs_num s; q_abs_den s;
    assert (qnum lhs == iabs (qnum x * qden y + qden x * qnum y));
    assert (qden lhs == iabs (qden x * qden y));
    (* shape of rhs = q_abs x + q_abs y *)
    fraction_add_reveal (q_abs x) (q_abs y);
    q_abs_num x; q_abs_den x; q_abs_num y; q_abs_den y;
    assert (qnum rhs == iabs (qnum x) * iabs (qden y) + iabs (qden x) * iabs (qnum y));
    assert (qden rhs == iabs (qden x) * iabs (qden y));
    (* the two denominators coincide as ints: D *)
    iabs_mul (qden x) (qden y);
    assert (qden lhs == qden rhs);
    let d = qden lhs in
    iabs_nonneg (qden x * qden y);
    assert (d >= 0);
    (* numerator triangle inequality *)
    iabs_triangle (qnum x * qden y) (qden x * qnum y);
    iabs_mul (qnum x) (qden y);
    iabs_mul (qden x) (qnum y);
    assert (qnum lhs <= qnum rhs);
    (* q_le lhs rhs unfolds to:
         (num lhs * d * (d * d)) <= (num rhs * d * (d * d))
       since den lhs == den rhs == d. Scale num lhs <= num rhs by
       the nonneg factor (d * (d * d)) = d^3.                        *)
    let m = d * (d * d) in
    nonneg_cube d;                          (* 0 <= d * (d * d) *)
    assert (m >= 0);
    mono_mul_nonneg (qnum lhs) (qnum rhs) m;
    (* rearrange (num * d) * (d*d) == num * (d * (d*d)) = num * m *)
    ML.paren_mul_right (qnum lhs) d (d * d);
    ML.paren_mul_right (qnum rhs) d (d * d);
    assert (qnum lhs * qden lhs * (qden rhs * qden rhs)
              == qnum lhs * m);
    assert (qnum rhs * qden rhs * (qden lhs * qden lhs)
              == qnum rhs * m)

(* ================================================================ *)
(*  9.  q_le_trans                                                  *)
(* ================================================================ *)

(* a nonzero int has a strictly positive square (via iabs, which is
   always >= 0 and equal to the value's magnitude). *)
let int_sq_pos (d: int)
  : Lemma (requires d <> 0) (ensures d * d > 0)
  = iabs_nonneg d;
    iabs_zero_iff d;
    assert (iabs d > 0);                       (* iabs d : nat, nonzero *)
    iabs_mul d d;                              (* iabs (d*d) == iabs d * iabs d *)
    ML.lemma_mult_le_left (iabs d) 1 (iabs d); (* iabs d <= iabs d * iabs d *)
    assert (iabs d * iabs d > 0);
    assert (iabs (d * d) > 0);
    iabs_zero_iff (d * d);                     (* iabs (d*d) = 0 <==> d*d = 0 *)
    iabs_nonneg (d * d)                        (* iabs (d*d) >= 0, and = d*d if d*d>=0 *)

(* the denominator-square of any qq is strictly positive. *)
let qden_sq_pos (x: qq)
  : Lemma (qden x * qden x > 0)
  = qden_nonzero x;
    int_sq_pos (qden x)

(* cancel a strictly positive factor from a <= inequality. *)
let cancel_mul_le (p q: int) (n: int)
  : Lemma (requires p * n <= q * n /\ n > 0) (ensures p <= q)
  = if p > q then ML.lemma_mult_lt_right n q p   (* q*n < p*n, contradiction *)

#push-options "--z3rlimit 100"
let q_le_trans (x y z: qq)
  : Lemma (requires q_le x y /\ q_le y z) (ensures q_le x z)
  = let nx = qnum x in let dx = qden x in
    let ny = qnum y in let dy = qden y in
    let nz = qnum z in let dz = qden z in
    let dxx = dx * dx in
    let dyy = dy * dy in
    let dzz = dz * dz in
    (* hypotheses *)
    assert (nx * dx * dyy <= ny * dy * dxx);     (* q_le x y *)
    assert (ny * dy * dzz <= nz * dz * dyy);     (* q_le y z *)
    (* positivity facts *)
    qden_sq_pos x; qden_sq_pos y; qden_sq_pos z;
    assert (dxx > 0 /\ dyy > 0 /\ dzz > 0);
    (* multiply H1 by dzz (>=0, right) ; H2 by dxx (>=0, right) *)
    mono_mul_nonneg (nx * dx * dyy) (ny * dy * dxx) dzz;
    assert ((nx * dx * dyy) * dzz <= (ny * dy * dxx) * dzz);
    mono_mul_nonneg (ny * dy * dzz) (nz * dz * dyy) dxx;
    assert ((ny * dy * dzz) * dxx <= (nz * dz * dyy) * dxx);
    (* the two middle terms are equal as integers (both = ny*dy*dxx*dzz). *)
    assert ((ny * dy * dxx) * dzz == (ny * dy * dzz) * dxx);
    (* add the two inequalities and cancel the common middle term: *)
    assert ((nx * dx * dyy) * dzz <= (nz * dz * dyy) * dxx);
    (* regroup both sides so the cancellable factor dyy is on the right. *)
    assert ((nx * dx * dyy) * dzz == (nx * dx * dzz) * dyy);
    assert ((nz * dz * dyy) * dxx == (nz * dz * dxx) * dyy);
    assert ((nx * dx * dzz) * dyy <= (nz * dz * dxx) * dyy);
    cancel_mul_le (nx * dx * dzz) (nz * dz * dxx) dyy;
    assert (nx * dx * dzz <= nz * dz * dxx)
#pop-options

(* ----------------------------------------------------------------- *)
(*  Pure-integer core of additive monotonicity.                       *)
(*                                                                    *)
(*  With Da = da*da etc. the goal (after expanding the two sum         *)
(*  fractions and clearing denominators) is                           *)
(*    na*da*Db*Dc*Dd + nb*db*Da*Dc*Dd                                 *)
(*       <= nc*dc*Da*Db*Dd + nd*dd*Da*Db*Dc                           *)
(*  obtained by scaling H_ac by Db*Dd and H_bd by Da*Dc and adding.   *)
(* ----------------------------------------------------------------- *)
(* The two degree-6 commutative-semiring identities relating the goal
   sides to the summed-scaled form.  Stated with fully-qualified Prims
   integer operators so `int_semiring` (which matches `Prims.op_Star`/
   `Prims.op_Addition`) is not blinded by the ring `*`/`+` from
   `Core.Algebra.Notation`. *)
let add_mono_ident_lhs (na da nb db dc dd: int)
  : Lemma ((na * db + da * nb) * (da * db) * ((dc * dd) * (dc * dd))
              == (na * da * (dc * dc)) * ((db * db) * (dd * dd))
               + (nb * db * (dd * dd)) * ((da * da) * (dc * dc)))
  = assert (
      Prims.op_Star
        (Prims.op_Star
          (Prims.op_Addition (Prims.op_Star na db) (Prims.op_Star da nb))
          (Prims.op_Star da db))
        (Prims.op_Star (Prims.op_Star dc dd) (Prims.op_Star dc dd))
      == Prims.op_Addition
          (Prims.op_Star
            (Prims.op_Star (Prims.op_Star na da) (Prims.op_Star dc dc))
            (Prims.op_Star (Prims.op_Star db db) (Prims.op_Star dd dd)))
          (Prims.op_Star
            (Prims.op_Star (Prims.op_Star nb db) (Prims.op_Star dd dd))
            (Prims.op_Star (Prims.op_Star da da) (Prims.op_Star dc dc))))
      by (FStar.Tactics.CanonCommSemiring.int_semiring())

let add_mono_ident_rhs (nc dd dc nd da db: int)
  : Lemma ((nc * dd + dc * nd) * (dc * dd) * ((da * db) * (da * db))
              == (nc * dc * (da * da)) * ((db * db) * (dd * dd))
               + (nd * dd * (db * db)) * ((da * da) * (dc * dc)))
  = assert (
      Prims.op_Star
        (Prims.op_Star
          (Prims.op_Addition (Prims.op_Star nc dd) (Prims.op_Star dc nd))
          (Prims.op_Star dc dd))
        (Prims.op_Star (Prims.op_Star da db) (Prims.op_Star da db))
      == Prims.op_Addition
          (Prims.op_Star
            (Prims.op_Star (Prims.op_Star nc dc) (Prims.op_Star da da))
            (Prims.op_Star (Prims.op_Star db db) (Prims.op_Star dd dd)))
          (Prims.op_Star
            (Prims.op_Star (Prims.op_Star nd dd) (Prims.op_Star db db))
            (Prims.op_Star (Prims.op_Star da da) (Prims.op_Star dc dc))))
      by (FStar.Tactics.CanonCommSemiring.int_semiring())

#push-options "--z3rlimit 100"
let q_le_add_mono_core (na da nb db nc dc nd dd: int)
  : Lemma
      (requires
        na * da * (dc * dc) <= nc * dc * (da * da) /\
        nb * db * (dd * dd) <= nd * dd * (db * db) /\
        da * da > 0 /\ db * db > 0 /\ dc * dc > 0 /\ dd * dd > 0)
      (ensures
        (na * db + da * nb) * (da * db) * ((dc * dd) * (dc * dd))
          <= (nc * dd + dc * nd) * (dc * dd) * ((da * db) * (da * db)))
    (* scale H_ac by (db*db * (dd*dd)) >= 0 *)
  = nonneg_mul (db * db) (dd * dd);
    mono_mul_nonneg (na * da * (dc * dc)) (nc * dc * (da * da)) ((db * db) * (dd * dd));
    assert ((na * da * (dc * dc)) * ((db * db) * (dd * dd))
              <= (nc * dc * (da * da)) * ((db * db) * (dd * dd)));
    (* scale H_bd by (da*da * (dc*dc)) >= 0 *)
    nonneg_mul (da * da) (dc * dc);
    mono_mul_nonneg (nb * db * (dd * dd)) (nd * dd * (db * db)) ((da * da) * (dc * dc));
    assert ((nb * db * (dd * dd)) * ((da * da) * (dc * dc))
              <= (nd * dd * (db * db)) * ((da * da) * (dc * dc)));
    (* sum of the two scaled inequalities *)
    assert ((na * da * (dc * dc)) * ((db * db) * (dd * dd))
              + (nb * db * (dd * dd)) * ((da * da) * (dc * dc))
              <= (nc * dc * (da * da)) * ((db * db) * (dd * dd))
              + (nd * dd * (db * db)) * ((da * da) * (dc * dc)));
    (* the LHS sum equals the goal LHS, the RHS sum the goal RHS:
       pure commutative-semiring identities. *)
    add_mono_ident_lhs na da nb db dc dd;
    add_mono_ident_rhs nc dd dc nd da db
#pop-options

(* ================================================================ *)
(* 10.  q_le_add_mono :  a<=c /\ b<=d ==> a+b <= c+d                 *)
(* ================================================================ *)

#push-options "--z3rlimit 100"
let q_le_add_mono (a b c d: qq)
  : Lemma (requires q_le a c /\ q_le b d)
          (ensures q_le (fraction_add a b) (fraction_add c d))
  = let na = qnum a in let da = qden a in
    let nb = qnum b in let db = qden b in
    let nc = qnum c in let dc = qden c in
    let nd = qnum d in let dd = qden d in
    (* shapes of the two sums *)
    fraction_add_reveal a b;
    fraction_add_reveal c d;
    let s1 = fraction_add a b in let s2 = fraction_add c d in
    assert (qnum s1 == na * db + da * nb /\ qden s1 == da * db);
    assert (qnum s2 == nc * dd + dc * nd /\ qden s2 == dc * dd);
    (* hypotheses: q_le a c, q_le b d *)
    assert (na * da * (dc * dc) <= nc * dc * (da * da));   (* H_ac *)
    assert (nb * db * (dd * dd) <= nd * dd * (db * db));   (* H_bd *)
    (* positivity of squares *)
    qden_sq_pos a; qden_sq_pos b; qden_sq_pos c; qden_sq_pos d;
    q_le_add_mono_core na da nb db nc dc nd dd
#pop-options

(* ================================================================ *)
(* 11.  q_le_well_defined :  x=x' /\ y=y' ==> q_le x y == q_le x' y' *)
(*                                                                  *)
(*  q_le clears denominators by their squares, so it is invariant    *)
(*  under the fraction equatable `=` (cross-multiplication).  We      *)
(*  prove the forward implication by scaling the cleared inequality   *)
(*  by (dx'·dy')^2 > 0 and substituting the cross-mult equalities,    *)
(*  then cancelling the common positive factor (dx·dy)^2; the boolean *)
(*  `==` follows by applying the forward lemma in both directions.    *)
(* ================================================================ *)

(* scale an integer equality on the right. *)
let eq_scale_right (a b k: int)
  : Lemma (requires a == b) (ensures a * k == b * k)
  = ()

(* --- four pure commutative-semiring rearrangements (qualified Prims
       ops so int_semiring is not blinded by the ring `*`/`+`). --- *)

(* IdA1 :  (nx*dx*(dy*dy)) * ((dxp*dxp)*(dyp*dyp))
              == (nx*dxp) * (dx*dxp*(dy*dy)*(dyp*dyp))                *)
let wd_idA1 (nx dx dy dxp dyp: int)
  : Lemma ((nx * dx * (dy * dy)) * ((dxp * dxp) * (dyp * dyp))
              == (nx * dxp) * (dx * dxp * (dy * dy) * (dyp * dyp)))
  = assert (
      Prims.op_Star
        (Prims.op_Star (Prims.op_Star nx dx) (Prims.op_Star dy dy))
        (Prims.op_Star (Prims.op_Star dxp dxp) (Prims.op_Star dyp dyp))
      == Prims.op_Star
          (Prims.op_Star nx dxp)
          (Prims.op_Star (Prims.op_Star (Prims.op_Star dx dxp) (Prims.op_Star dy dy))
                         (Prims.op_Star dyp dyp)))
      by (FStar.Tactics.CanonCommSemiring.int_semiring())

(* IdA2 :  (dx*nxp) * (dx*dxp*(dy*dy)*(dyp*dyp))
              == (nxp*dxp*(dyp*dyp)) * ((dx*dy)*(dx*dy))              *)
let wd_idA2 (dx nxp dxp dy dyp: int)
  : Lemma ((dx * nxp) * (dx * dxp * (dy * dy) * (dyp * dyp))
              == (nxp * dxp * (dyp * dyp)) * ((dx * dy) * (dx * dy)))
  = assert (
      Prims.op_Star
        (Prims.op_Star dx nxp)
        (Prims.op_Star (Prims.op_Star (Prims.op_Star dx dxp) (Prims.op_Star dy dy))
                       (Prims.op_Star dyp dyp))
      == Prims.op_Star
          (Prims.op_Star (Prims.op_Star nxp dxp) (Prims.op_Star dyp dyp))
          (Prims.op_Star (Prims.op_Star dx dy) (Prims.op_Star dx dy)))
      by (FStar.Tactics.CanonCommSemiring.int_semiring())

(* IdB1 :  (ny*dy*(dx*dx)) * ((dxp*dxp)*(dyp*dyp))
              == (ny*dyp) * (dy*dyp*(dx*dx)*(dxp*dxp))                *)
let wd_idB1 (ny dy dx dxp dyp: int)
  : Lemma ((ny * dy * (dx * dx)) * ((dxp * dxp) * (dyp * dyp))
              == (ny * dyp) * (dy * dyp * (dx * dx) * (dxp * dxp)))
  = assert (
      Prims.op_Star
        (Prims.op_Star (Prims.op_Star ny dy) (Prims.op_Star dx dx))
        (Prims.op_Star (Prims.op_Star dxp dxp) (Prims.op_Star dyp dyp))
      == Prims.op_Star
          (Prims.op_Star ny dyp)
          (Prims.op_Star (Prims.op_Star (Prims.op_Star dy dyp) (Prims.op_Star dx dx))
                         (Prims.op_Star dxp dxp)))
      by (FStar.Tactics.CanonCommSemiring.int_semiring())

(* IdB2 :  (dy*nyp) * (dy*dyp*(dx*dx)*(dxp*dxp))
              == (nyp*dyp*(dxp*dxp)) * ((dx*dy)*(dx*dy))              *)
let wd_idB2 (dy nyp dyp dx dxp: int)
  : Lemma ((dy * nyp) * (dy * dyp * (dx * dx) * (dxp * dxp))
              == (nyp * dyp * (dxp * dxp)) * ((dx * dy) * (dx * dy)))
  = assert (
      Prims.op_Star
        (Prims.op_Star dy nyp)
        (Prims.op_Star (Prims.op_Star (Prims.op_Star dy dyp) (Prims.op_Star dx dx))
                       (Prims.op_Star dxp dxp))
      == Prims.op_Star
          (Prims.op_Star (Prims.op_Star nyp dyp) (Prims.op_Star dxp dxp))
          (Prims.op_Star (Prims.op_Star dx dy) (Prims.op_Star dx dy)))
      by (FStar.Tactics.CanonCommSemiring.int_semiring())

(* the pure-integer forward core. *)
#push-options "--z3rlimit 100"
let q_le_wd_fwd_core (nx dx nxp dxp ny dy nyp dyp: int)
  : Lemma
      (requires
        nx * dxp == dx * nxp /\          (* H1 : x = x' *)
        ny * dyp == dy * nyp /\          (* H2 : y = y' *)
        dx * dx > 0 /\ dy * dy > 0 /\ dxp * dxp > 0 /\ dyp * dyp > 0 /\
        nx * dx * (dy * dy) <= ny * dy * (dx * dx))   (* Q : q_le x y *)
      (ensures nxp * dxp * (dyp * dyp) <= nyp * dyp * (dxp * dxp))
  = let p = (dxp * dxp) * (dyp * dyp) in
    nonneg_mul (dxp * dxp) (dyp * dyp);
    (* scale Q by p >= 0 *)
    mono_mul_nonneg (nx * dx * (dy * dy)) (ny * dy * (dx * dx)) p;
    assert ((nx * dx * (dy * dy)) * p <= (ny * dy * (dx * dx)) * p);   (* Q' *)
    (* LHS_Q' == (nxp*dxp*(dyp*dyp)) * M    where M = (dx*dy)*(dx*dy) *)
    wd_idA1 nx dx dy dxp dyp;
    eq_scale_right (nx * dxp) (dx * nxp) (dx * dxp * (dy * dy) * (dyp * dyp));  (* uses H1 *)
    wd_idA2 dx nxp dxp dy dyp;
    let m = (dx * dy) * (dx * dy) in
    assert ((nx * dx * (dy * dy)) * p == (nxp * dxp * (dyp * dyp)) * m);
    (* RHS_Q' == (nyp*dyp*(dxp*dxp)) * M *)
    wd_idB1 ny dy dx dxp dyp;
    eq_scale_right (ny * dyp) (dy * nyp) (dy * dyp * (dx * dx) * (dxp * dxp));  (* uses H2 *)
    wd_idB2 dy nyp dyp dx dxp;
    assert ((ny * dy * (dx * dx)) * p == (nyp * dyp * (dxp * dxp)) * m);
    (* so  (nxp*dxp*dyp²)*m <= (nyp*dyp*dxp²)*m,  m > 0 *)
    assert ((nxp * dxp * (dyp * dyp)) * m <= (nyp * dyp * (dxp * dxp)) * m);
    (* dx <> 0 and dy <> 0 (squares are > 0), so dx*dy <> 0, so m > 0 *)
    assert (dx <> 0 /\ dy <> 0);
    assert (dx * dy <> 0);
    int_sq_pos (dx * dy);
    assert (m > 0);
    cancel_mul_le (nxp * dxp * (dyp * dyp)) (nyp * dyp * (dxp * dxp)) m
#pop-options

(* the forward direction at the qq level. *)
let q_le_wd_fwd (x x' y y': qq)
  : Lemma (requires x = x' /\ y = y' /\ q_le x y) (ensures q_le x' y')
  = fraction_eq_reveal x x';      (* nx*dx' == dx*nx' *)
    fraction_eq_reveal y y';       (* ny*dy' == dy*ny' *)
    qden_sq_pos x; qden_sq_pos y; qden_sq_pos x'; qden_sq_pos y';
    q_le_wd_fwd_core (qnum x) (qden x) (qnum x') (qden x')
                     (qnum y) (qden y) (qnum y') (qden y')

let q_le_well_defined (x x' y y': qq)
  : Lemma (requires x = x' /\ y = y') (ensures q_le x y == q_le x' y')
  = (* forward: q_le x y ==> q_le x' y' *)
    introduce q_le x y ==> q_le x' y'
    with _. q_le_wd_fwd x x' y y';
    (* backward: q_le x' y' ==> q_le x y, using symmetry of `=` *)
    introduce q_le x' y' ==> q_le x y
    with _. (fraction_eq_reveal x x';
             fraction_eq_reveal x' x;
             fraction_eq_reveal y y';
             fraction_eq_reveal y' y;
             q_le_wd_fwd x' x y' y)

(* ================================================================ *)
(* 12.  Finite-sum triangle inequality                              *)
(*        |Σ_{j<n} f j|  <=  Σ_{j<n} |f j|                            *)
(*                                                                  *)
(*  Uses the qq additive group `qacg = crq.cr_r.r_add` that          *)
(*  `Core.FinSum.sum_range` resolves to.  The bridge lemmas below     *)
(*  relate that group's `add`/`zero` to `fraction_add`/`fraction_zero`*)
(*  so the order lemmas (stated with `fraction_add`) apply.          *)
(* ================================================================ *)

(* qacg.add IS fraction_add. *)
let qacg_add_reveal (a b: qq)
  : Lemma (qacg.add a b == fraction_add a b)
  = fraction_ring_add_reveal a b

(* The additive-group zero of ℚ has numerator 0.  The published
   `fraction_field` instance is abstract, so we cannot reduce the
   projected zero to `Fraction 0 1`; instead we pin its numerator via
   the additive-identity law (mirrors Core.Polynomial.EmbedQ):
     (0/1 + z) =eq= 0/1   forces   num z = 0. *)
let qacg_zero_num (_:unit)
  : Lemma (qnum (qacg.zero) == 0)
  = let fz = fraction_zero int in
    let z  = qacg.zero in
    H.x_plus_zero #(fraction int_id) #qacg fz;        (* (fz + z) =eq= fz *)
    fraction_ring_add_reveal fz z;       (* fz + z == fraction_add fz z *)
    fraction_add_reveal fz z;
    fraction_zero_reveal int #int_id;
    fraction_eq_reveal (fraction_add fz z) fz

(* the summand function |f j|, named (no anonymous lambda downstream). *)
let qabs_of (f: nat -> qq) (j: nat) : qq = q_abs (f j)

(* base case:  q_le (q_abs qacg.zero) qacg.zero.
   With num z = 0 both sides of the cleared-denominator inequality are 0. *)
let q_abs_sum_le_base (_:unit)
  : Lemma (q_le (q_abs qacg.zero) qacg.zero)
  = let z = qacg.zero in
    qacg_zero_num ();
    assert (qnum z == 0);
    q_abs_num z; q_abs_den z;
    (* num (q_abs z) = iabs (num z) = iabs 0 = 0 *)
    assert (qnum (q_abs z) == 0);
    (* q_le (q_abs z) z : both cleared-denominator sides are 0. *)
    assert (qnum (q_abs z) * qden (q_abs z) * (qden z * qden z) == 0);
    assert (qnum z * qden z * (qden (q_abs z) * qden (q_abs z)) == 0)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let rec q_abs_sum_le (f: nat -> qq) (n: nat)
  : Lemma (ensures q_le (q_abs (sum_range #qq #qacg f 0 n))
                        (sum_range #qq #qacg (qabs_of f) 0 n))
          (decreases n)
  = if n = 0 then begin
      sum_range_empty #qq #qacg f 0 0;             (* sum f 0 0 == qacg.zero *)
      sum_range_empty #qq #qacg (qabs_of f) 0 0;   (* sum g 0 0 == qacg.zero *)
      q_abs_sum_le_base ()
    end
    else begin
      let m = n - 1 in
      H.elim_equatable_laws qq #(qacg.acg_eq) ();  (* `=` refl/sym/trans on qq *)
      let s  = sum_range #qq #qacg f 0 n in           (* the summed value *)
      let t  = sum_range #qq #qacg (qabs_of f) 0 n in
      let sf = sum_range #qq #qacg f 0 m in
      let sg = sum_range #qq #qacg (qabs_of f) 0 m in
      (* explicit fraction_add representatives *)
      let a  = fraction_add sf (f m) in               (* sf + f m *)
      let b  = fraction_add sg (q_abs (f m)) in        (* sg + |f m| *)
      (* unfold both sums on the right (equatable `=`) *)
      sum_range_unfold_right #qq #qacg f 0 n;          (* s = qacg.add sf (f m) *)
      sum_range_unfold_right #qq #qacg (qabs_of f) 0 n; (* t = qacg.add sg (qabs_of f m) *)
      qacg_add_reveal sf (f m);                        (* qacg.add sf (f m) == a *)
      qacg_add_reveal sg (qabs_of f m);                (* qacg.add sg (qabs_of f m) == b' *)
      (* qabs_of f m == q_abs (f m) definitionally, so the second add is b *)
      assert (qabs_of f m == q_abs (f m));
      assert (s = a);                                  (* bridge `=` *)
      assert (t = b);
      (* triangle on the last term:  q_le (q_abs a) (q_abs sf + q_abs (f m)) *)
      q_abs_triangle sf (f m);
      (* IH on the head: q_le (q_abs sf) sg *)
      q_abs_sum_le f m;
      (* reflexivity on the tail: q_le (q_abs (f m)) (q_abs (f m)) *)
      q_le_refl (q_abs (f m));
      (* monotone add: q_le (q_abs sf + q_abs (f m)) (sg + q_abs (f m)) = q_le _ b *)
      q_le_add_mono (q_abs sf) (q_abs (f m)) sg (q_abs (f m));
      (* chain triangle then monotone via transitivity:  q_le (q_abs a) b *)
      q_le_trans (q_abs a)
                 (fraction_add (q_abs sf) (q_abs (f m)))
                 b;
      (* transport q_le (q_abs a) b  to  q_le (q_abs s) t  via well-definedness:
           q_abs s = q_abs a  (q_abs respects `=`),  and  t = b. *)
      q_abs_well_defined s a;                          (* q_abs s = q_abs a *)
      q_le_well_defined (q_abs s) (q_abs a) t b
    end
#pop-options

(* ================================================================ *)
(* 13.  q_le_mul_mono_r :  0 <= c /\ a <= b ==> a*c <= b*c           *)
(*                                                                  *)
(*  After clearing denominators by their squares, q_le (a*c) (b*c)  *)
(*  reduces to scaling the cleared form of  q_le a b  by the         *)
(*  nonnegative factor  nc*dc*(dc*dc).                              *)
(* ================================================================ *)

(* two pure commutative-semiring identities (qualified Prims ops so
   int_semiring is not blinded by the ring `*` from Notation). *)
let mul_mono_ident_lhs (na nc da dc db: int)
  : Lemma ((na * nc) * (da * dc) * ((db * dc) * (db * dc))
              == (na * da * (db * db)) * (nc * dc * (dc * dc)))
  = assert (
      Prims.op_Star
        (Prims.op_Star (Prims.op_Star na nc) (Prims.op_Star da dc))
        (Prims.op_Star (Prims.op_Star db dc) (Prims.op_Star db dc))
      == Prims.op_Star
          (Prims.op_Star (Prims.op_Star na da) (Prims.op_Star db db))
          (Prims.op_Star (Prims.op_Star nc dc) (Prims.op_Star dc dc)))
      by (FStar.Tactics.CanonCommSemiring.int_semiring())

let mul_mono_ident_rhs (nb nc db dc da: int)
  : Lemma ((nb * nc) * (db * dc) * ((da * dc) * (da * dc))
              == (nb * db * (da * da)) * (nc * dc * (dc * dc)))
  = assert (
      Prims.op_Star
        (Prims.op_Star (Prims.op_Star nb nc) (Prims.op_Star db dc))
        (Prims.op_Star (Prims.op_Star da dc) (Prims.op_Star da dc))
      == Prims.op_Star
          (Prims.op_Star (Prims.op_Star nb db) (Prims.op_Star da da))
          (Prims.op_Star (Prims.op_Star nc dc) (Prims.op_Star dc dc)))
      by (FStar.Tactics.CanonCommSemiring.int_semiring())

#push-options "--z3rlimit 100"
let q_le_mul_mono_r (a b c: qq)
  : Lemma (requires q_le (fraction_zero int) c /\ q_le a b)
          (ensures q_le (fraction_mul a c) (fraction_mul b c))
  = let na = qnum a in let da = qden a in
    let nb = qnum b in let db = qden b in
    let nc = qnum c in let dc = qden c in
    fraction_mul_reveal a c;
    fraction_mul_reveal b c;
    let ac = fraction_mul a c in let bc = fraction_mul b c in
    assert (qnum ac == na * nc /\ qden ac == da * dc);
    assert (qnum bc == nb * nc /\ qden bc == db * dc);
    (* H1 : q_le a b *)
    assert (na * da * (db * db) <= nb * db * (da * da));
    (* H2 : q_le 0 c  ==>  0 <= nc * dc *)
    let z = fraction_zero int in
    fraction_zero_reveal int #int_id;
    assert (qnum z == 0 /\ qden z == 1);
    assert (qnum z * qden z * (dc * dc) <= nc * dc * (qden z * qden z));   (* q_le z c *)
    assert (0 <= nc * dc);
    (* dc*dc > 0, so nc*dc*(dc*dc) >= 0 *)
    qden_sq_pos c;
    assert (dc * dc > 0);
    nonneg_mul (nc * dc) (dc * dc);
    assert (nc * dc * (dc * dc) >= 0);
    (* scale H1 by the nonneg factor *)
    mono_mul_nonneg (na * da * (db * db)) (nb * db * (da * da)) (nc * dc * (dc * dc));
    assert ((na * da * (db * db)) * (nc * dc * (dc * dc))
              <= (nb * db * (da * da)) * (nc * dc * (dc * dc)));
    mul_mono_ident_lhs na nc da dc db;
    mul_mono_ident_rhs nb nc db dc da
#pop-options

(* ================================================================ *)
(* 14.  q_le_sum_mono :  (forall j<n. f j <= g j) ==>                *)
(*        Sum_{j<n} f j  <=  Sum_{j<n} g j                            *)
(* ================================================================ *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let rec q_le_sum_mono (f g: nat -> qq) (n: nat)
  (pf: (j:nat{j < n}) -> Lemma (q_le (f j) (g j)))
  : Lemma (ensures q_le (sum_range #qq #qacg f 0 n)
                        (sum_range #qq #qacg g 0 n))
          (decreases n)
  = if n = 0 then begin
      sum_range_empty #qq #qacg f 0 0;             (* sum f 0 0 == qacg.zero *)
      sum_range_empty #qq #qacg g 0 0;             (* sum g 0 0 == qacg.zero *)
      q_le_refl (qacg.zero)
    end
    else begin
      let m = n - 1 in
      H.elim_equatable_laws qq #(qacg.acg_eq) ();
      let sf = sum_range #qq #qacg f 0 m in
      let sg = sum_range #qq #qacg g 0 m in
      let a  = fraction_add sf (f m) in
      let b  = fraction_add sg (g m) in
      sum_range_unfold_right #qq #qacg f 0 n;          (* sum f 0 n = qacg.add sf (f m) *)
      sum_range_unfold_right #qq #qacg g 0 n;          (* sum g 0 n = qacg.add sg (g m) *)
      qacg_add_reveal sf (f m);                        (* qacg.add sf (f m) == a *)
      qacg_add_reveal sg (g m);                        (* qacg.add sg (g m) == b *)
      assert (sum_range #qq #qacg f 0 n = a);
      assert (sum_range #qq #qacg g 0 n = b);
      (* IH on the head + the j=m hypothesis, combined by add-monotonicity *)
      q_le_sum_mono f g m (fun (j:nat{j < m}) -> pf j); (* q_le sf sg *)
      pf m;                                            (* q_le (f m) (g m) *)
      q_le_add_mono sf (f m) sg (g m);                 (* q_le a b *)
      (* transport q_le a b to q_le (sum f) (sum g) via well-definedness *)
      q_le_well_defined (sum_range #qq #qacg f 0 n) a
                        (sum_range #qq #qacg g 0 n) b
    end
#pop-options
