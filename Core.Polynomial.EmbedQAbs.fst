module Core.Polynomial.EmbedQAbs

(* ================================================================ *)
(*  ℤ ↔ ℚ ABS/ORDER glue.                                           *)
(*                                                                  *)
(*  Connects q_abs / q_le on EMBEDDED integers (n ↦ n/1) back to    *)
(*  iabs / <= on ℤ.  These descend the §D coefficient bound from    *)
(*  ℚ to ℤ.                                                         *)
(*                                                                  *)
(*  All three lemmas are BOUNDED: the embedded integer is the       *)
(*  concrete representative `Fraction n one` with `one #int = 1`,   *)
(*  so num/den are literal ints and the `*1` factors simplify.      *)
(*                                                                  *)
(*  NO admit / assume / sorry.                                      *)
(* ================================================================ *)

module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Fractions
open Core.Fractions.RationalAbs
open Core.Polynomial.EmbedQ

#set-options "--fuel 1 --ifuel 1 --z3rlimit 30"

(* embed_zq_const n = Fraction #int #int_id n (one <: int), and
   `one <: int` is `int_ring.one == 1`, so num = n, den = 1. *)
private let embed_num_den (n: int)
  : Lemma (qnum (embed_zq_const n) == n /\ qden (embed_zq_const n) == 1)
  = ()

(* ---------------------------------------------------------------- *)
(*  1.  q_abs commutes with the embedding.                          *)
(*        q_abs (n/1)  =  (iabs n)/1  =  embed (iabs n).            *)
(* ---------------------------------------------------------------- *)

let q_abs_embed (n: int)
  : Lemma (q_abs (embed_zq_const n) = embed_zq_const (iabs n))
  = let en = embed_zq_const n in
    embed_num_den n;                      (* num en = n, den en = 1 *)
    q_abs_num en; q_abs_den en;           (* num (q_abs en) = iabs n, den = iabs 1 = 1 *)
    embed_num_den (iabs n);               (* num (embed (iabs n)) = iabs n, den = 1 *)
    (* both Fraction (iabs n) 1; cross-mult: iabs n * 1 = 1 * iabs n *)
    fraction_eq_reveal (q_abs en) (embed_zq_const (iabs n))

(* ---------------------------------------------------------------- *)
(*  2.  q_le on embedded integers IS the integer order.             *)
(*        q_le (a/1) (b/1) == (a <= b).                             *)
(* ---------------------------------------------------------------- *)

let q_le_embed (a b: int)
  : Lemma (q_le (embed_zq_const a) (embed_zq_const b) == (a <= b))
  = let ea = embed_zq_const a in
    let eb = embed_zq_const b in
    embed_num_den a;                      (* num ea = a, den ea = 1 *)
    embed_num_den b;                      (* num eb = b, den eb = 1 *)
    (* q_le ea eb = (a*1*(1*1)) <= (b*1*(1*1)) ; both *1 factors are 1. *)
    assert (qnum ea * qden ea * (qden eb * qden eb) == a);
    assert (qnum eb * qden eb * (qden ea * qden ea) == b)

(* ---------------------------------------------------------------- *)
(*  3.  Corollary: a bound on iabs n in ℤ descends to a q_le on the  *)
(*      embedded absolute value.                                     *)
(*        iabs n <= m  ==>  q_le (q_abs (n/1)) (m/1).               *)
(* ---------------------------------------------------------------- *)

let q_abs_embed_le (n m: int)
  : Lemma (requires iabs n <= m)
          (ensures q_le (q_abs (embed_zq_const n)) (embed_zq_const m))
  = (* reflexivity of `=` on qq, so embed m = embed m *)
    H.elim_equatable_laws qq ();
    (* q_abs (embed n) = embed (iabs n) *)
    q_abs_embed n;
    (* q_le (embed (iabs n)) (embed m) == (iabs n <= m) == true *)
    q_le_embed (iabs n) m;
    (* transport q_le along q_abs (embed n) = embed (iabs n)
       via q_le_well_defined. *)
    q_le_well_defined (q_abs (embed_zq_const n)) (embed_zq_const (iabs n))
                      (embed_zq_const m) (embed_zq_const m)
