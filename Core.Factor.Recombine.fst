module Core.Factor.Recombine

(* ================================================================ *)
(*  M2 · S7 — EXECUTABLE recombination (Zassenhaus subset search).   *)
(*                                                                   *)
(*  Given the mod-pᵏ Hensel-lifted factors `gs : list (poly (zmod    *)
(*  pᵏ))` of a primitive squarefree `bigF ∈ ℤ[z]`, executably        *)
(*  RECOMBINE them into ℤ-factors:                                   *)
(*    1. enumerate boolean subset masks   (`subset_masks`);          *)
(*    2. form the candidate = centered lift of the masked product    *)
(*       (`poly_centered pᵏ (masked_prod gs mask)`);                 *)
(*    3. keep the candidate iff it is non-constant AND divides bigF  *)
(*       over ℤ, tested by a monic Euclidean division                *)
(*       (`divides_test`, remainder = 0).                            *)
(*                                                                   *)
(*  SOUNDNESS  (`try_recombine_sound`) is the load-bearing guarantee: *)
(*  every emitted polynomial genuinely divides bigF — a direct        *)
(*  executable-check-implies-property (rem = 0 ⟹ divides).           *)
(*                                                                   *)
(*  COMPLETENESS (`try_recombine_complete`) WIRES to the finished     *)
(*  §D theory (Core.Modular.RecombinationComplete.recombination_      *)
(*  complete): a true monic ℤ-factor g equals the centered masked     *)
(*  sub-product for a mask that the enumeration `subset_masks`        *)
(*  provably contains — the search WILL find it.                      *)
(*                                                                   *)
(*  Standalone (NOT on build-all).  NO admit / assume / sorry.        *)
(* ================================================================ *)

module L  = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Int
open Core.Algebra.Divisibility
open Core.Modular.ResidueRing
open Core.Modular.ResidueRing.Hensel.Reduce
open Core.Modular.ResidueRing.Hensel.Lift
open Core.Modular.ResidueRing.CenteredPoly
open Core.Modular.RecombinationComplete
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Monic
open Core.Polynomial.Roots
open Core.Polynomial.Eval
open Core.Polynomial.SubsetProd
open Core.Polynomial.KroneckerBound

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  §1 — MONIC Euclidean division over a commutative ring.           *)
(*                                                                   *)
(*  A port of Core.Polynomial.Div's field divmod, specialised to a   *)
(*  MONIC divisor: the leading-coefficient inverse is `one`, so the  *)
(*  step scale is simply `c = coeff p (deg p)`.  The correctness      *)
(*  identity  p = q·quot + rem  holds for ANY divisor (it is purely   *)
(*  algebraic — cancellation only affects TERMINATION quality, which  *)
(*  fuel already guarantees).  This makes the divisibility TEST below *)
(*  sound with no field structure on ℤ.                              *)
(* ================================================================ *)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let poly_mul_nil_right (#t:Type) {| cr: commutative_ring t |}
                       (q: polynomial t)
  : Lemma ((q * ([] <: polynomial t)) = ([] <: polynomial t))
  = H.elim_equatable_laws (polynomial t) ();
    mul_commutativity q ([] <: polynomial t);
    transitivity (q * ([] <: polynomial t))
                 (([] <: polynomial t) * q)
                 ([] <: polynomial t)
#pop-options

#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let divmod_base_case (#t:Type) {| cr: commutative_ring t |}
                     (p q: polynomial t)
  : Lemma (p = ((q * ([] <: polynomial t)) + p))
  = H.elim_equatable_laws (polynomial t) ();
    poly_mul_nil_right q;
    add_congruence ((q * ([] <: polynomial t))) p
                   ([] <: polynomial t) p;
    assert (([] <: polynomial t) + p = p);
    symmetry ((q * ([] <: polynomial t)) + p)
             (([] <: polynomial t) + p);
    transitivity p (([] <: polynomial t) + p)
                 ((q * ([] <: polynomial t)) + p)
#pop-options

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let add_sub_cancel_pub (#t:Type) {| cr: commutative_ring t |}
                       (p s: polynomial t)
  : Lemma (p = ((p -- s) + s))
  = H.elim_equatable_laws (polynomial t) ();
    let ns : polynomial t = - s in
    let ps : polynomial t = p + ns in
    let z : polynomial t = [] in
    add_associativity p ns s;
    add_negation s;
    add_congruence p (ns + s) p z;
    add_zero p;
    transitivity (ps + s) (p + (ns + s)) (p + z);
    transitivity (ps + s) (p + z) p;
    symmetry (ps + s) p
#pop-options

#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let inductive_step (#t:Type) {| cr: commutative_ring t |}
                   (p q mono quot rem: polynomial t)
  : Lemma
      (requires ((p -- (mono * q)) = ((q * quot) + rem)))
      (ensures  (p = ((q * (quot + mono)) + rem)))
  = H.elim_equatable_laws (polynomial t) ();
    let sub_term = mono * q in
    let p2 = p -- sub_term in
    let qm = q * mono in
    let qq = q * quot in
    let lhs_main = (q * (quot + mono)) + rem in

    left_distributivity q quot mono;
    let step1 = qq + qm in
    add_congruence (q * (quot + mono)) rem step1 rem;
    let a1 = step1 + rem in
    add_associativity qq qm rem;
    let a2 = qq + (qm + rem) in
    add_commutativity qm rem;
    add_congruence qq (qm + rem) qq (rem + qm);
    let a3 = qq + (rem + qm) in
    add_associativity qq rem qm;
    symmetry ((qq + rem) + qm) (qq + (rem + qm));
    let a4 = (qq + rem) + qm in
    symmetry p2 (qq + rem);
    add_congruence (qq + rem) qm p2 qm;
    let a5 = p2 + qm in
    mul_commutativity q mono;
    add_congruence p2 qm p2 sub_term;
    let a6 = p2 + sub_term in
    add_sub_cancel_pub p sub_term;
    symmetry p a6;

    transitivity a1 a2 a3;
    transitivity a1 a3 a4;
    transitivity a1 a4 a5;
    transitivity a1 a5 a6;
    transitivity a1 a6 p;
    transitivity lhs_main a1 p;
    symmetry lhs_main p
#pop-options

(* monic-style Euclidean division (Tot; terminates by fuel). *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let rec monic_divmod_fuel (#t:Type) {| cr: commutative_ring t |}
    (p q: polynomial t) (fuel: nat)
  : Tot (polynomial t & polynomial t) (decreases fuel)
  = if fuel = 0 then ([], p)
    else
      let m = deg p in
      let n = deg q in
      if m < 0 || n < 0 then ([], p)
      else if m < n then ([], p)
      else begin
        let c = coeff p m in
        let mono : polynomial t = monomial c (m - n) in
        let sub_term = mono * q in
        let p' = p -- sub_term in
        let (quot, rem) = monic_divmod_fuel p' q (fuel - 1) in
        (quot + mono, rem)
      end
#pop-options

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let rec monic_divmod_fuel_correct (#t:Type) {| cr: commutative_ring t |}
    (p q: polynomial t) (fuel: nat)
  : Lemma
      (ensures (let (quot, rem) = monic_divmod_fuel p q fuel in
                (p = ((q * quot) + rem))))
      (decreases fuel)
  = if fuel = 0 then divmod_base_case p q
    else
      let m = deg p in
      let n = deg q in
      if m < 0 || n < 0 then divmod_base_case p q
      else if m < n then divmod_base_case p q
      else begin
        let c = coeff p m in
        let mono : polynomial t = monomial c (m - n) in
        let sub_term = mono * q in
        let p2 = p -- sub_term in
        monic_divmod_fuel_correct p2 q (fuel - 1);
        let (quot2, rem) = monic_divmod_fuel p2 q (fuel - 1) in
        inductive_step p q mono quot2 rem
      end
#pop-options

(* ================================================================ *)
(*  §2 — the executable ℤ-divisibility TEST + its soundness.         *)
(* ================================================================ *)

(* Euclidean division of `bigF` by `d` over ℤ (fuel = |bigF|+1). *)
let ediv (bigF d: polynomial int) : (polynomial int & polynomial int)
  = monic_divmod_fuel bigF d (L.length bigF ++ 1)

let ediv_correct (bigF d: polynomial int)
  : Lemma (let (quot, rem) = ediv bigF d in bigF = ((d * quot) + rem))
  = monic_divmod_fuel_correct bigF d (L.length bigF ++ 1)

(* d divides bigF over ℤ, tested by a zero remainder. *)
let divides_test (bigF d: polynomial int) : bool
  = let (_, rem) = ediv bigF d in rem = (poly_zero #int)

(* SOUNDNESS of the test: a zero remainder certifies divisibility. *)
let divides_test_sound (bigF d: polynomial int)
  : Lemma (requires divides_test bigF d = true)
          (ensures  divides d bigF)
  = H.elim_equatable_laws (polynomial int) ();
    ediv_correct bigF d;
    let (quot, rem) = ediv bigF d in
    (* bigF = (d*quot) + rem  and  rem = poly_zero *)
    add_congruence (d * quot) rem (d * quot) (poly_zero #int);  (* (d*quot)+rem = (d*quot)+0 *)
    add_zero (d * quot);                                         (* (d*quot)+0 = d*quot *)
    transitivity ((d * quot) + rem) ((d * quot) + (poly_zero #int)) (d * quot);
    transitivity bigF ((d * quot) + rem) (d * quot);            (* bigF = d*quot *)
    divides_intro d bigF quot

(* ================================================================ *)
(*  §3 — enumeration of subset masks.                                *)
(* ================================================================ *)

(* Named cons combinators (η-free; keeps memP_map_intro unification    *)
(* airtight — no lambda). *)
let cons_false (m: list bool) : list bool = false :: m
let cons_true  (m: list bool) : list bool = true  :: m

(* all 2ⁿ boolean masks of length n.  NOTE the search is exponential in *)
(* the number of Hensel factors — correctness-first, not optimised.     *)
let rec subset_masks (n:nat) : Tot (list (list bool)) (decreases n)
  = if n = 0 then [ [] ]
    else
      let rest = subset_masks (n - 1) in
      L.append (L.map cons_false rest) (L.map cons_true rest)

(* COMPLETENESS of the enumeration: every mask is enumerated at its own  *)
(* length. *)
let rec mask_in_subset_masks (mask: list bool)
  : Lemma (ensures L.memP mask (subset_masks (L.length mask)))
          (decreases mask)
  = match mask with
    | [] -> ()
    | b :: m' ->
      mask_in_subset_masks m';                    (* memP m' (subset_masks |m'|) *)
      let rest = subset_masks (L.length m') in
      if b then begin
        LP.memP_map_intro cons_true m' rest;        (* memP (true::m') (map cons_true rest) *)
        LP.append_memP (L.map cons_false rest) (L.map cons_true rest) mask
      end else begin
        LP.memP_map_intro cons_false m' rest;       (* memP (false::m') (map cons_false rest) *)
        LP.append_memP (L.map cons_false rest) (L.map cons_true rest) mask
      end

(* a mask of length n is enumerated by subset_masks n. *)
let mask_complete (n:nat) (mask: list bool)
  : Lemma (requires L.length mask == n)
          (ensures  L.memP mask (subset_masks n))
  = mask_in_subset_masks mask

(* ================================================================ *)
(*  §4 — the executable recombination.                               *)
(* ================================================================ *)

(* candidate ℤ-factor for a mask: the centered lift of the masked      *)
(* sub-product of the Hensel factors. *)
let recomb_candidate (pk:int{pk > 1})
  (gs: list (polynomial (zmod pk))) (mask: list bool)
  : polynomial int
  = poly_centered pk (masked_prod gs mask)

(* keep a candidate iff it is non-constant and divides bigF over ℤ. *)
let recomb_keep (pk:int{pk > 1}) (bigF: polynomial int)
  (gs: list (polynomial (zmod pk))) (mask: list bool)
  : bool
  = let d = recomb_candidate pk gs mask in
    (deg d >= 1) && divides_test bigF d

(* enumerate masks, keep the surviving candidates.  A mask-list         *)
(* filter-then-map — clearly terminating. *)
let try_recombine (pk:int{pk > 1}) (bigF: polynomial int)
  (gs: list (polynomial (zmod pk)))
  : list (polynomial int)
  = L.map (recomb_candidate pk gs)
          (L.filter (recomb_keep pk bigF gs) (subset_masks (L.length gs)))

(* ================================================================ *)
(*  §5 — SOUNDNESS of the search: every output divides bigF.         *)
(* ================================================================ *)

let try_recombine_sound (pk:int{pk > 1}) (bigF: polynomial int)
  (gs: list (polynomial (zmod pk))) (d: polynomial int)
  : Lemma (requires L.memP d (try_recombine pk bigF gs))
          (ensures  divides d bigF)
  = let masks    = subset_masks (L.length gs) in
    let filtered = L.filter (recomb_keep pk bigF gs) masks in
    (* d ∈ map candidate filtered ⟹ ∃ mask ∈ filtered. candidate mask == d *)
    LP.memP_map_elim (recomb_candidate pk gs) d filtered;
    eliminate exists (mask: list bool).
                L.memP mask filtered /\ recomb_candidate pk gs mask == d
    returns divides d bigF
    with _hm.
    begin
      (* mask ∈ filter keep masks ⟹ keep mask = true *)
      L.mem_filter (recomb_keep pk bigF gs) masks mask;
      (* keep mask = true ⟹ divides_test bigF (candidate mask) = true *)
      divides_test_sound bigF d
    end

(* ================================================================ *)
(*  §6 — COMPLETENESS, WIRED to the §D theory.                       *)
(*                                                                   *)
(*  Consumes exactly Core.Modular.RecombinationComplete.recombination *)
(*  _complete (the engine behind recombination_complete_fp): under    *)
(*  its hypothesis bundle a true monic ℤ-factor g equals the centered *)
(*  masked sub-product for `mask`.  We add that `subset_masks`        *)
(*  provably ENUMERATES `mask` — hence the search reaches g.          *)
(* ================================================================ *)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let try_recombine_complete
  (p:int{p > 1}) (n:nat)
  (bigF g k0: polynomial int)
  (gs: list (polynomial (zmod (ppow p (n ++ 1)))))
  (gbars: list (polynomial (zmod p)))
  (mask: list bool)
  (s t: polynomial (zmod p))
  (int_cs: list int)
  : Lemma
      (requires
        bigF = (g * k0) /\ monic g /\
        (poly_to_fp (ppow p (n ++ 1)) bigF) = (poly_prod gs) /\
        L.length mask == L.length gs /\
        L.length gbars == L.length gs /\
        to_base_corr p (n ++ 1) gs gbars /\
        (poly_to_base p (n ++ 1) (poly_to_fp (ppow p (n ++ 1)) g))
          = (masked_prod gbars mask) /\
        all_monic gs /\
        ((s * (masked_prod gbars mask))
         + (t * (masked_prod gbars (negate_mask mask))))
          = (poly_one #(zmod p)) /\
        all_distinct int_cs /\
        deg g < L.length int_cs /\
        (forall (j:nat). j < L.length int_cs ==>
            poly_eval bigF (L.index int_cs j) <> 0) /\
        (ppow p (n ++ 1)) > 2 * (kbound_rhs bigF int_cs))
      (ensures
        L.memP mask (subset_masks (L.length gs)) /\
        g = (recomb_candidate (ppow p (n ++ 1)) gs mask))
  = recombination_complete p n bigF g k0 gs gbars mask s t int_cs;
    mask_complete (L.length gs) mask
#pop-options
