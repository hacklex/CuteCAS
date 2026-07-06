module Core.Fractions.RationalAbsInv

(* ================================================================ *)
(*  §D bound step (c) — the INVERSE-ABS collapse on                 *)
(*    qq = fraction int_id    (ℚ).                                  *)
(*                                                                  *)
(*  Goal (deliverable item 4): the basis denominator's inverse has  *)
(*  q_abs <= one:  iabs n >= 1  ==>  q_le (q_abs (qinv (n/1))) one.  *)
(*                                                                  *)
(*  qinv is the ℚ FIELD inverse `inv` (from `mul_is_group`, reached  *)
(*  through the published `fraction_field int int_id`).  Its        *)
(*  num/den are NOT exposed (fraction_inv is hidden behind the       *)
(*  interface), so we work purely through the inverse LAW            *)
(*  (`inversion_lemma`:  x * inv x = one) + a generic right-inverse  *)
(*  UNIQUENESS lemma:                                                *)
(*     x nonzero /\ x * c = one   ==>   c = inv x.                   *)
(*                                                                  *)
(*  Items, by priority 1,2,4 (3 supports 4):                        *)
(*    1. q_abs_one      :  q_abs one = one                          *)
(*    2. q_abs_inv      :  q_abs (inv x) = inv (q_abs x)            *)
(*    3. q_le_inv_embed_one : n>=1 ==> q_le (inv (n/1)) one          *)
(*    4. q_abs_inv_embed_le_one : iabs n>=1 ==>                     *)
(*                            q_le (q_abs (inv (n/1))) one          *)
(*                                                                  *)
(*  NO admit / assume / sorry.                                      *)
(* ================================================================ *)

module H  = Core.Algebra.Helpers
module ML = FStar.Math.Lemmas

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Fractions
open Core.Fractions.RationalAbs
open Core.Polynomial.EmbedQ
open Core.Polynomial.EmbedQAbs

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------- *)
(*  num/den of an embedded integer (local copy: EmbedQAbs's          *)
(*  embed_num_den is private).                                       *)
(* ---------------------------------------------------------------- *)

let embed_nd (n: int)
  : Lemma (qnum (embed_zq_const n) == n /\ qden (embed_zq_const n) == 1)
  = ()

(* ================================================================ *)
(*  Generic right-inverse UNIQUENESS in the ℚ field.                *)
(*                                                                  *)
(*    is_nonzero x  /\  x * c = one   ==>   c = inv x.               *)
(*                                                                  *)
(*  Proof:  inversion_lemma x  gives  inv x * x = one;  then         *)
(*    c = one * c = (inv x * x) * c = inv x * (x * c)                *)
(*      = inv x * one = inv x.                                       *)
(*  All ops are the qq field/ring ops resolved through              *)
(*  `fraction_field int int_id` (exactly as DerivativeQuotient).    *)
(* ================================================================ *)

#push-options "--z3rlimit 60"
let right_inv_unique (x: qq) (c: qq)
  : Lemma (requires is_nonzero x /\ (x * c) = (one <: qq))
          (ensures  c = (inv x))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    inversion_lemma x;                         (* inv x * x = one /\ x * inv x = one *)
    let ix = inv x in
    (* c = one * c *)
    H.one_mul_x c;                                  (* one * c = c *)
    (* one * c = (ix * x) * c   [since ix*x = one] *)
    mul_congruence (one <: qq) c (ix * x) c;        (* one * c = (ix*x) * c *)
    (* (ix * x) * c = ix * (x * c) *)
    mul_associativity ix x c;
    (* ix * (x*c) = ix * one   [x*c = one] *)
    mul_congruence ix (x * c) ix (one <: qq);
    (* ix * one = ix *)
    H.x_mul_one ix;
    (* chain: c = one*c = (ix*x)*c = ix*(x*c) = ix*one = ix *)
    H.trans5 c
             ((one <: qq) * c)
             ((ix * x) * c)
             (ix * (x * c))
             (ix * (one <: qq))
             ix
#pop-options

(* ================================================================ *)
(*  1.  q_abs_one :  q_abs one = one                                *)
(*                                                                  *)
(*  fraction_one is abstract behind the interface, so we cannot read *)
(*  its num/den.  Instead use the CONCRETE representative            *)
(*  embed_zq_const 1 = Fraction 1 1:                                 *)
(*    (one <: qq) = embed 1     (pin via the mult-identity law)      *)
(*    q_abs (embed 1) = embed (iabs 1) = embed 1   (q_abs_embed)     *)
(*  hence q_abs (one) = one (transport).                            *)
(* ================================================================ *)

(* (one <: qq) = embed_zq_const 1.  Mirror EmbedQ.embed_const_one:    *)
(*   e1 * one = e1   (mult identity) and  fraction_mul e1 one == one   *)
(*   as a Fraction, so one = e1 up to `=`.                            *)
let one_eq_embed1 (_:unit)
  : Lemma ((embed_zq_const 1) = (one <: qq))
  = let e1 = embed_zq_const 1 in
    H.elim_equatable_laws qq ();
    H.x_mul_one e1;                          (* e1 * one = e1 *)
    fraction_ring_mul_reveal e1 (one <: qq);
    fraction_mul_reveal e1 (one <: qq)

let q_abs_one (_:unit)
  : Lemma (q_abs (one <: qq) = (one <: qq))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let e1 = embed_zq_const 1 in
    one_eq_embed1 ();                            (* e1 = one *)
    (* q_abs respects `=`:  q_abs one = q_abs e1 *)
    q_abs_well_defined (one <: qq) e1;
    (* q_abs (embed 1) = embed (iabs 1) = embed 1 *)
    q_abs_embed 1;                               (* q_abs e1 = embed (iabs 1) *)
    embed_nd 1; embed_nd (iabs 1);
    (* embed (iabs 1) = embed 1  (iabs 1 = 1; cross-mult) *)
    fraction_eq_reveal (embed_zq_const (iabs 1)) e1;
    (* chain: q_abs one = q_abs e1 = embed (iabs 1) = e1 = one *)
    H.trans4 (q_abs (one <: qq)) (q_abs e1) (embed_zq_const (iabs 1)) e1 (one <: qq)

(* ================================================================ *)
(*  q_abs of a nonzero fraction is nonzero  (needed for inv(q_abs x)).*)
(*    qnum (q_abs x) = iabs (qnum x), and iabs is 0 iff its arg is.  *)
(*                                                                  *)
(*  Here `is_nonzero x` (the additive-group nonzero on qq) is        *)
(*  `not (x = zero)`; via fraction_eq_reveal that is `qnum x <> 0`.  *)
(* ================================================================ *)

(* is_nonzero x  <==>  qnum x <> 0.                                  *)
(*   is_nonzero x = not (x = (zero<:qq)).  The qq zero is abstract,   *)
(*   but RationalAbs.qacg_zero_num pins qnum (zero) = 0, and the      *)
(*   zero's denominator is nonzero by the fraction refinement; so     *)
(*   the cross-mult  qnum x * qden zero = qden x * 0 = 0  forces      *)
(*   qnum x = 0 (cancel the nonzero qden zero).                       *)
let is_nonzero_iff_num (x: qq)
  : Lemma (is_nonzero x <==> qnum x <> 0)
  = let z : qq = qacg.zero in
    qacg_zero_num ();                       (* qnum z == 0 *)
    qden_nonzero z;                          (* qden z <> 0 *)
    (* (zero <: qq) IS qacg.zero (both the additive identity of crq). *)
    assert ((zero <: qq) == z);
    (* x = zero  <==>  qnum x * qden z = qden x * qnum z = qden x * 0 = 0 *)
    fraction_eq_reveal x z

let q_abs_nonzero (x: qq)
  : Lemma (requires is_nonzero x) (ensures is_nonzero (q_abs x))
  = is_nonzero_iff_num x;
    q_abs_num x;                            (* qnum (q_abs x) == iabs (qnum x) *)
    iabs_zero_iff (qnum x);                 (* iabs (qnum x) = 0 <==> qnum x = 0 *)
    is_nonzero_iff_num (q_abs x)

(* ================================================================ *)
(*  2.  q_abs_inv :  q_abs (inv x) = inv (q_abs x)                   *)
(*                                                                  *)
(*  From the inverse law  x * inv x = one  apply q_abs_mul:          *)
(*    q_abs x * q_abs (inv x) = q_abs one = one                      *)
(*  so q_abs (inv x) is a right-inverse of q_abs x (nonzero), hence  *)
(*  equals inv (q_abs x) by uniqueness.                              *)
(*                                                                  *)
(*  q_abs_mul/q_abs_one are stated with `fraction_mul`/`fraction_one`;*)
(*  bridge to the ring `*`/`one` via fraction_ring_mul_reveal.       *)
(* ================================================================ *)

#push-options "--z3rlimit 80"
let q_abs_inv (x: qq)
  : Lemma (requires is_nonzero x /\ is_nonzero (q_abs x))
          (ensures q_abs (inv x) = inv (q_abs x))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let ix = inv x in
    (* inverse law: x * inv x = one  (ring `*`/`one` on qq) *)
    inversion_lemma x;                          (* x * ix = one /\ ix * x = one *)
    (* ring `*` IS fraction_mul; ring `one` IS fraction_one *)
    fraction_ring_mul_reveal x ix;     (* x * ix == fraction_mul x ix *)
    (* so fraction_mul x ix = one *)
    assert (fraction_mul x ix = (one <: qq));
    (* apply q_abs to both sides: q_abs (fraction_mul x ix) = q_abs one *)
    q_abs_well_defined (fraction_mul x ix) (one <: qq);
    (* q_abs (fraction_mul x ix) = fraction_mul (q_abs x) (q_abs ix) *)
    q_abs_mul x ix;
    (* q_abs one = one *)
    q_abs_one ();
    (* chain: fraction_mul (q_abs x)(q_abs ix) = q_abs (fraction_mul x ix)
                                               = q_abs one = one *)
    H.trans3 (fraction_mul (q_abs x) (q_abs ix))
             (q_abs (fraction_mul x ix))
             (q_abs (one <: qq))
             (one <: qq);
    (* bridge back to the ring `*`/`one`: (q_abs x) * (q_abs ix) = one *)
    fraction_ring_mul_reveal (q_abs x) (q_abs ix);
    assert (((q_abs x) * (q_abs ix)) = (one <: qq));
    (* q_abs x is nonzero (from requires), so uniqueness applies *)
    right_inv_unique (q_abs x) (q_abs ix)
#pop-options

(* ================================================================ *)
(*  3.  q_le_inv_embed_one :  n>=1 ==> q_le (inv (n/1)) one          *)
(*                                                                  *)
(*  recip = Fraction 1 n  is a right-inverse of embed n:            *)
(*    fraction_mul (n/1) (1/n) = (n*1)/(1*n) = n/n = 1   (cross-mult)*)
(*  so by uniqueness  inv (embed n) = recip.  Then q_le recip one    *)
(*  is concrete:  (1*n*1) <= (1*1*(n*n))  i.e.  n <= n^2.            *)
(* ================================================================ *)

(* embedded n is nonzero when n <> 0. *)
let embed_nonzero (n: int)
  : Lemma (requires n <> 0) (ensures is_nonzero (embed_zq_const n))
  = embed_nd n;
    is_nonzero_iff_num (embed_zq_const n)

(* the explicit reciprocal Fraction 1 n  (n nonzero gives a valid den). *)
let recip_frac (n: int{ n <> 0 }) : qq =
  Fraction 1 n

let recip_nd (n: int{ n <> 0 })
  : Lemma (qnum (recip_frac n) == 1 /\ qden (recip_frac n) == n)
  = ()

(* recip_frac n is the field inverse of embed n (clean uniqueness form). *)
let recip_r_eq_inv (n: int{ n <> 0 })
  : Lemma (requires is_nonzero (embed_zq_const n))
          (ensures (recip_frac n) = (inv (embed_zq_const n)))
  = let en = embed_zq_const n in
    let r  = recip_frac n in
    let e1 = embed_zq_const 1 in
    H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    embed_nd n; recip_nd n; embed_nd 1;
    (* fraction_mul en r = Fraction (n*1) (1*n) ; cross-mult to e1 = Fraction 1 1:
         (n*1) * 1  =  (1*n) * 1   -- true *)
    fraction_mul_reveal en r;
    assert (qnum (fraction_mul en r) == n * 1);
    assert (qden (fraction_mul en r) == 1 * n);
    fraction_eq_reveal (fraction_mul en r) e1;
    (* so fraction_mul en r = e1 ; bridge en*r and e1 = one *)
    fraction_ring_mul_reveal en r;            (* en * r == fraction_mul en r *)
    one_eq_embed1 ();                                       (* e1 = (one <: qq) *)
    (* chain:  en * r = fraction_mul en r = e1 = one *)
    H.trans3 (en * r) (fraction_mul en r) e1 (one <: qq);
    assert ((en * r) = (one <: qq));
    right_inv_unique en r

let q_le_inv_embed_one (n: int)
  : Lemma (requires n >= 1)
          (ensures (embed_nonzero n;
                    q_le (inv (embed_zq_const n)) (one <: qq)))
  = embed_nonzero n;
    let en = embed_zq_const n in
    let r  = recip_frac n in
    let e1 = embed_zq_const 1 in            (* concrete one = Fraction 1 1 *)
    H.elim_equatable_laws qq ();
    (* We want  q_le (inv en) one.  First show q_le r e1 (concrete), then
       transport along  r = inv en  and  e1 = one. *)
    recip_nd n;                              (* num r = 1, den r = n *)
    embed_nd 1;                              (* num e1 = 1, den e1 = 1 *)
    (* q_le r e1 = (num r * den r * (den e1)^2) <= (num e1 * den e1 * (den r)^2)
              = (1 * n * 1) <= (1 * 1 * (n*n))  i.e. n <= n*n *)
    assert (qnum r * qden r * (qden e1 * qden e1) == n);
    assert (qnum e1 * qden e1 * (qden r * qden r) == n * n);
    ML.lemma_mult_le_right n 1 n;            (* 1*n <= n*n, i.e. n <= n*n *)
    assert (q_le r e1);
    recip_r_eq_inv n;                        (* r = inv en *)
    one_eq_embed1 ();                        (* e1 = (one <: qq) *)
    q_le_well_defined r (inv en) e1 (one <: qq)

(* ================================================================ *)
(*  4.  q_abs_inv_embed_le_one  (DELIVERABLE)                        *)
(*        iabs n >= 1  ==>  q_le (q_abs (inv (n/1))) one.            *)
(*                                                                  *)
(*  Chain:                                                          *)
(*    q_abs (inv (embed n)) = inv (q_abs (embed n))      [item 2]   *)
(*                          = inv (embed (iabs n))     [q_abs_embed] *)
(*    q_le (inv (embed (iabs n))) one                    [item 3,   *)
(*                                              with iabs n >= 1]    *)
(*  transported with q_le_well_defined / inv_congr.                 *)
(* ================================================================ *)

(* embed (iabs n) is nonzero when iabs n >= 1. *)
let embed_iabs_nonzero (n: int)
  : Lemma (requires iabs n >= 1) (ensures is_nonzero (embed_zq_const (iabs n)))
  = embed_nonzero (iabs n)

#push-options "--z3rlimit 80"
let q_abs_inv_embed_le_one (n: int)
  : Lemma (requires iabs n >= 1 /\ is_nonzero (embed_zq_const n))
          (ensures q_le (q_abs (inv (embed_zq_const n))) (one <: qq))
  = iabs_nonneg n;
    iabs_zero_iff n;                          (* iabs n >= 1 ==> n <> 0 *)
    assert (n <> 0);
    let en = embed_zq_const n in
    embed_nonzero n;                          (* is_nonzero en *)
    H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    q_abs_nonzero en;                         (* is_nonzero (q_abs en) *)
    (* item 2: q_abs (inv en) = inv (q_abs en) *)
    q_abs_inv en;
    (* q_abs en = embed (iabs n)   [q_abs_embed] *)
    q_abs_embed n;
    embed_iabs_nonzero n;                     (* is_nonzero (embed (iabs n)) *)
    (* inv (q_abs en) = inv (embed (iabs n))   [inv_congr] *)
    inv_congr (q_abs en) (embed_zq_const (iabs n));
    (* so q_abs (inv en) = inv (embed (iabs n)) by transitivity *)
    H.trans2 (q_abs (inv en)) (inv (q_abs en)) (inv (embed_zq_const (iabs n)));
    (* item 3: q_le (inv (embed (iabs n))) one,  since iabs n >= 1 *)
    q_le_inv_embed_one (iabs n);
    (* transport the q_le along  q_abs (inv en) = inv (embed (iabs n)) *)
    let o = (one <: qq) in
    q_le_well_defined (inv (embed_zq_const (iabs n))) (q_abs (inv en)) o o
#pop-options
