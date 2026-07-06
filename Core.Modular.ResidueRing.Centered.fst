module Core.Modular.ResidueRing.Centered

(* ================================================================ *)
(*  §D foundation — the CENTERED LIFT  ℤ/m → ℤ.                       *)
(*                                                                   *)
(*  `centered m a` is the representative of `a ∈ zmod m` in the       *)
(*  symmetric range `(−m/2, m/2]`  (a, or a−m if a > m/2).            *)
(*  `to_fp m` reduces an arbitrary integer back into `zmod m`.        *)
(*                                                                   *)
(*  KEY round-trip `centered_roundtrip`:  to_fp (centered a) = a.     *)
(*  KEY bound `centered_bound`:  2·|centered a| ≤ m.                  *)
(*                                                                   *)
(*  Zassenhaus recombination lifts a mod-pᵏ Hensel factor to ℤ via    *)
(*  `centered`; once pᵏ > 2·B (B the coefficient bound) the centered  *)
(*  representative IS the true integer factor.                        *)
(*                                                                   *)
(*  NO admit / assume / sorry in the final version.                  *)
(* ================================================================ *)

open Core.Modular.ResidueRing
open FStar.Math.Lemmas

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* reduce an arbitrary integer into the canonical representative [0,m). *)
let to_fp (m:int{m > 1}) (a: int) : zmod m
  = lemma_mod_lt a m; Zm (((a % m) + m) % m)

(* the centered representative of `a` in (−m/2, m/2]. *)
let centered (m:int{m > 1}) (a: zmod m) : int
  = if 2 * zv a <= m then zv a else zv a - m

(* round-trip: reducing the centered representative recovers a. *)
let centered_roundtrip (m:int{m > 1}) (a: zmod m)
  : Lemma (to_fp m (centered m a) == a)
  = if 2 * zv a <= m then begin
      // centered m a == zv a, with 0 <= zv a < m
      small_mod (zv a) m;              // zv a % m == zv a
      lemma_mod_plus (zv a) 1 m        // (zv a + 1*m) % m == zv a % m == zv a
    end
    else begin
      // centered m a == zv a - m, with -m < zv a - m < 0
      small_mod (zv a) m;              // zv a % m == zv a
      lemma_mod_plus (zv a) (-1) m     // (zv a + (-1)*m) % m == zv a % m == zv a
    end

(* the centered representative is bounded by m/2 in absolute value. *)
let centered_bound (m:int{m > 1}) (a: zmod m)
  : Lemma (2 * (if centered m a >= 0 then centered m a else - (centered m a)) <= m)
  = ()
