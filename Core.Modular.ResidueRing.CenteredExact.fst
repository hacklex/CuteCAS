module Core.Modular.ResidueRing.CenteredExact

(* ================================================================ *)
(*  §D bridge — CENTERED-LIFT EXACTNESS.                             *)
(*                                                                   *)
(*  An integer `v` whose magnitude is strictly below m/2 (i.e.       *)
(*  -m < 2v < m) is recovered EXACTLY by reducing mod m (`to_fp`)    *)
(*  then taking the centered representative (`centered`).            *)
(*                                                                   *)
(*  This is the step that turns the Kronecker / coefficient bound    *)
(*  (pᵏ > 2·B) into exact integer-factor recovery: once the true     *)
(*  integer factor's coefficients satisfy 2·|coeff| < pᵏ, the        *)
(*  centered lift of the mod-pᵏ Hensel factor IS that integer.       *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module ML = FStar.Math.Lemmas
open Core.Modular.ResidueRing
open Core.Modular.ResidueRing.Centered

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* An integer of magnitude < m/2 round-trips through `to_fp` then
   `centered` to itself.  Precondition `-m < 2v < m` is `2|v| < m`
   without an `if`. *)
let centered_recovers_small (m:int{m > 1}) (v: int)
  : Lemma (requires 2 * v < m /\ -m < 2 * v)
          (ensures centered m (to_fp m v) == v)
  = if v >= 0 then begin
      // 0 <= v < m, so to_fp m v == v
      ML.small_mod v m;             // v % m == v   (0 <= v < m)
      ML.lemma_mod_plus v 1 m;      // (v + 1*m) % m == v % m == v
      // to_fp m v == ((v % m) + m) % m == (v + m) % m == v
      // 2*v < m  ==>  2*v <= m, so centered m v == v
      ()
    end
    else begin
      // -m < v < 0, so 0 < v + m < m
      ML.lemma_mod_plus v 1 m;      // (v + 1*m) % m == v % m
      ML.small_mod (v + m) m;       // (v + m) % m == v + m   (0 < v+m < m)
      // hence v % m == v + m, and (v % m) + m == v + 2m
      ML.lemma_mod_plus (v + m) 1 m;// ((v+m) + 1*m) % m == (v+m) % m == v + m
      // to_fp m v == ((v % m) + m) % m == ((v+m) + m) % m == v + m
      // 2*(v+m) = 2v + 2m > m  (since 2v > -m), so centered m (v+m) == (v+m) - m == v
      ()
    end
