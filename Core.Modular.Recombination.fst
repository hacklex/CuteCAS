module Core.Modular.Recombination

(* ================================================================ *)
(*  §D — the recombination SOUNDNESS certificate.                    *)
(*                                                                   *)
(*  A certified integer factorization:  if the candidate factors     *)
(*  `gs` multiply (over ℤ) to `F`  (`F = ∏ gs`, a COMPUTABLE check),  *)
(*  then every `G ∈ gs` genuinely divides `F`.  This is the soundness *)
(*  backbone the executable factorizer emits — whatever subset-       *)
(*  product recombination yields, the product check certifies it.    *)
(*                                                                   *)
(*  NO admit / assume / sorry in the final version.                  *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module PR = Core.Polynomial.Roots

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Int
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Roots

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* every element of a list divides the product of the list. *)
let rec prod_divides_elem (gs: list (polynomial int #int_cr)) (g: polynomial int #int_cr)
  : Lemma (requires L.memP g gs)
          (ensures divides g (PR.poly_prod gs))
          (decreases gs)
  = H.elim_equatable_laws (polynomial int) ();
    match gs with
    | g0 :: rest ->
      (* poly_prod gs == poly_mul g0 (poly_prod rest) == mul g0 (poly_prod rest) *)
      eliminate (g == g0) \/ L.memP g rest
      returns divides g (PR.poly_prod gs)
      with _h.
        begin
          (* head: g0 | g0 * (poly_prod rest) *)
          divides_refl g0;
          divides_mul_right g0 g0 (PR.poly_prod rest)
        end
      and _h.
        begin
          (* tail: IH gives g | poly_prod rest, then g | g0 * poly_prod rest *)
          prod_divides_elem rest g;
          divides_mul_left g g0 (PR.poly_prod rest)
        end

(* ---------------------------------------------------------------- *)
(*  "every element of `gs` divides `f`" as an OPAQUE proposition,     *)
(*  with elim / proof-as-argument / intro.  Hides the `forall` so it  *)
(*  never lands in a consumer's SMT context (mirrors                  *)
(*  Core.Polynomial.CRT.coprime_with_all).                           *)
(* ---------------------------------------------------------------- *)
[@@"opaque_to_smt"]
let all_divide (gs: list (polynomial int #int_cr)) (f: polynomial int #int_cr)
  : prop = forall (g: polynomial int #int_cr). L.memP g gs ==> divides g f

let all_divide_elim (gs: list (polynomial int #int_cr)) (f: polynomial int #int_cr{all_divide gs f})
  : Lemma (forall (g: polynomial int #int_cr). L.memP g gs ==> divides g f)
  = reveal_opaque (`%all_divide) (all_divide gs f)

let all_divide_proof (gs: list (polynomial int #int_cr)) (f: polynomial int #int_cr)
  = (g:polynomial int #int_cr{L.memP g gs}) -> Lemma (divides g f)

let all_divide_intro (gs: list (polynomial int #int_cr)) (f: polynomial int #int_cr)
  (proof: all_divide_proof gs f)
  : Lemma (all_divide gs f)
  = reveal_opaque (`%all_divide) (all_divide gs f);
    let aux (g: polynomial int #int_cr) : Lemma (L.memP g gs ==> divides g f)
      = introduce L.memP g gs ==> divides g f
        with _hm. proof g
    in
    Classical.forall_intro aux

(* certified factorization: F = ∏ gs ⇒ every g ∈ gs divides F. *)
let factorization_sound (f: polynomial int #int_cr) (gs: list (polynomial int #int_cr))
  : Lemma (requires f = (PR.poly_prod gs))
          (ensures all_divide gs f)
  = H.elim_equatable_laws (polynomial int) ();
    let proof (g: polynomial int #int_cr{L.memP g gs}) : Lemma (divides g f)
      = prod_divides_elem gs g;                  (* g | poly_prod gs *)
        (* f == poly_prod gs  (poly_eq), so g | f *)
        poly_eq_symmetry f (PR.poly_prod gs);
        divides_congruence_right g (PR.poly_prod gs) f
    in
    all_divide_intro gs f proof
