module Core.Polynomial.SubsetProd

(* ================================================================ *)
(*  §D2b — the subset-product theorem (generic over any field).      *)
(*                                                                   *)
(*  A divisor `g` of a product `∏ hs` of IRREDUCIBLE polynomials is   *)
(*  (an associate of) a SUB-PRODUCT:  there is a nonzero scalar `c`   *)
(*  and a boolean mask selecting some of the `hs` such that           *)
(*        g  =  poly_const c  *  masked_prod hs mask.                 *)
(*                                                                   *)
(*  No squarefree hypothesis is needed — the induction handles        *)
(*  repeated factors.  Route: induction on `hs`.                     *)
(*    - h | g : peel the quotient, cancel h, recurse on `rest`,       *)
(*              mask bit = true.                                      *)
(*    - h ∤ g : h irreducible ⟹ coprime g h ⟹ (Euclid) g | ∏ rest,   *)
(*              recurse on `rest`, mask bit = false.                  *)
(*    - base [] : g | poly_one ⟹ deg g = 0 ⟹ g = poly_const c.        *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module IR = Core.Polynomial.Irreducible
module PR = Core.Polynomial.Roots
module SD = Core.Polynomial.SplitDivisor
module FA = Core.Polynomial.Factorization
module UN = Core.Polynomial.Unique
module SF = Core.Polynomial.SquareFree
module PF = Core.Polynomial.PartialFraction

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.GCD
open Core.Polynomial.Roots
open Core.Polynomial.Monic

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  The masked product.  A `true` bit keeps the corresponding factor; *)
(*  a `false` bit drops it.  Made total on ANY `mask` (length excess   *)
(*  on either side collapses to `poly_one`), which keeps the theorem's *)
(*  existential over `mask : list bool` well-typed.                    *)
(* ================================================================ *)

(* The DEFINITION and the small unfold lemmas need only a commutative_ring:
   no inverses are used, only polynomial `*` and `poly_one`.  Relaxing the
   binder here (the MAIN theorem below keeps `{| field t |}`) lets the same
   `masked_prod` be reused at non-field carriers such as `zmod (ppow p k)`
   (Core.Modular.RecombinationComplete). *)
let rec masked_prod (#t:Type) {| cr: commutative_ring t |}
  (hs: list (polynomial t)) (mask: list bool)
  : Tot (polynomial t) (decreases hs)
  = match hs, mask with
    | h :: hs', b :: m' -> if b then h * masked_prod hs' m' else masked_prod hs' m'
    | _ -> poly_one #t

let masked_prod_nil (#t:Type) {| cr: commutative_ring t |} (mask: list bool)
  : Lemma (masked_prod #t ([]) mask == poly_one #t)
  = ()

let masked_prod_cons_true (#t:Type) {| cr: commutative_ring t |}
  (h: polynomial t) (rest: list (polynomial t)) (m': list bool)
  : Lemma (masked_prod (h :: rest) (true :: m') == h * masked_prod rest m')
  = ()

let masked_prod_cons_false (#t:Type) {| cr: commutative_ring t |}
  (h: polynomial t) (rest: list (polynomial t)) (m': list bool)
  : Lemma (masked_prod (h :: rest) (false :: m') == masked_prod rest m')
  = ()

(* masked_prod on the empty mask collapses to poly_one, whatever the list. *)
let masked_prod_mask_nil (#t:Type) {| cr: commutative_ring t |}
  (hs: list (polynomial t))
  : Lemma (masked_prod hs ([]) == poly_one #t)
  = match hs with | [] -> () | _ :: _ -> ()

(* `negate_mask`:  flip every bit of a boolean mask. *)
let rec negate_mask (mask: list bool) : Tot (list bool) (decreases mask)
  = match mask with
    | []      -> []
    | b :: m' -> (not b) :: negate_mask m'

(* ================================================================ *)
(*  `all_monic` — an OPAQUE list predicate with elim / proof /       *)
(*  intro / head / tail bridges (mirrors all_irreducible below).      *)
(* ================================================================ *)

[@@"opaque_to_smt"]
let all_monic (#t:Type) {| cr: commutative_ring t |} (hs: list (polynomial t))
  : prop = forall (h: polynomial t). L.memP h hs ==> monic h

let all_monic_elim (#t:Type) {| cr: commutative_ring t |}
  (hs: list (polynomial t){all_monic hs})
  : Lemma (forall (h: polynomial t). L.memP h hs ==> monic h)
  = reveal_opaque (`%all_monic) (all_monic hs)

let all_monic_proof (#t:Type) {| cr: commutative_ring t |} (hs: list (polynomial t))
  = (h:polynomial t{L.memP h hs}) -> Lemma (monic h)

let all_monic_intro (#t:Type) {| cr: commutative_ring t |}
  (hs: list (polynomial t)) (proof: all_monic_proof hs)
  : Lemma (all_monic hs)
  = reveal_opaque (`%all_monic) (all_monic hs);
    let aux (h: polynomial t) : Lemma (L.memP h hs ==> monic h)
      = introduce L.memP h hs ==> monic h
        with _hm. proof h
    in
    Classical.forall_intro aux

let all_monic_tail (#t:Type) {| cr: commutative_ring t |}
  (h: polynomial t) (rest: list (polynomial t))
  : Lemma (requires all_monic (h :: rest))
          (ensures  all_monic rest)
  = all_monic_elim (h :: rest);
    let proof (x: polynomial t{L.memP x rest}) : Lemma (monic x)
      = assert (L.memP x (h :: rest))
    in
    all_monic_intro rest proof

let all_monic_head (#t:Type) {| cr: commutative_ring t |}
  (h: polynomial t) (rest: list (polynomial t))
  : Lemma (requires all_monic (h :: rest))
          (ensures  monic h)
  = all_monic_elim (h :: rest);
    assert (L.memP h (h :: rest))

(* masked_prod of monic factors is monic. *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let rec masked_prod_monic (#t:Type) {| cr: commutative_ring t |}
  (nz: squash (not (one #t = (zero <: t))))
  (hs: list (polynomial t)) (mask: list bool)
  : Lemma (requires all_monic hs)
          (ensures  monic (masked_prod hs mask))
          (decreases hs)
  = H.elim_equatable_laws t ();
    H.elim_equatable_laws (polynomial t) ();
    match hs, mask with
    | h :: rest, true :: m' ->
      all_monic_tail h rest;
      all_monic_head h rest;
      masked_prod_monic nz rest m';               (* monic (masked_prod rest m') *)
      let xx = masked_prod rest m' in
      monic_deg_mul h xx;                          (* deg (h*xx) = deg h + deg xx /\ lc(h*xx) = lc xx *)
      transitivity (poly_lc (h * xx)) (poly_lc xx) (one <: t);   (* lc(h*xx) = one *)
      masked_prod_cons_true h rest m'              (* masked_prod hs mask == h * xx *)
    | h :: rest, false :: m' ->
      all_monic_tail h rest;
      masked_prod_monic nz rest m';
      masked_prod_cons_false h rest m'             (* masked_prod hs mask == masked_prod rest m' *)
    | [], _ ->
      masked_prod_nil #t mask;
      monic_one nz
    | h :: rest, [] ->
      masked_prod_mask_nil (h :: rest);
      monic_one nz
#pop-options

(* poly_prod gs = (masked_prod gs mask) * (masked_prod gs ¬mask). *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec masked_prod_split (#t:Type) {| cr: commutative_ring t |}
  (gs: list (polynomial t)) (mask: list bool)
  : Lemma (requires L.length mask == L.length gs)
          (ensures  (poly_prod gs)
                    = ((masked_prod gs mask) * (masked_prod gs (negate_mask mask))))
          (decreases gs)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    match gs, mask with
    | [], [] ->
      masked_prod_nil #t ([]);
      poly_mul_one (poly_one #t);                          (* poly_one * poly_one = poly_one *)
      poly_eq_symmetry ((poly_one #t) * (poly_one #t)) (poly_one #t)
    | h :: rest, true :: m' ->
      masked_prod_split rest m';                           (* poly_prod rest = aa * bb *)
      let aa = masked_prod rest m' in
      let bb = masked_prod rest (negate_mask m') in
      assert (negate_mask (true :: m') == false :: negate_mask m');
      masked_prod_cons_true  h rest m';                    (* masked_prod gs mask == h * aa *)
      masked_prod_cons_false h rest (negate_mask m');      (* masked_prod gs ¬mask == bb *)
      mul_congruence h (poly_prod rest) h (aa * bb);       (* h*poly_prod rest = h*(aa*bb) *)
      mul_associativity h aa bb;                           (* (h*aa)*bb = h*(aa*bb) *)
      poly_eq_symmetry ((h * aa) * bb) (h * (aa * bb));
      poly_eq_transitivity (h * (poly_prod rest)) (h * (aa * bb)) ((h * aa) * bb)
    | h :: rest, false :: m' ->
      masked_prod_split rest m';
      let aa = masked_prod rest m' in
      let bb = masked_prod rest (negate_mask m') in
      assert (negate_mask (false :: m') == true :: negate_mask m');
      masked_prod_cons_false h rest m';                    (* masked_prod gs mask == aa *)
      masked_prod_cons_true  h rest (negate_mask m');      (* masked_prod gs ¬mask == h * bb *)
      mul_congruence h (poly_prod rest) h (aa * bb);       (* h*poly_prod rest = h*(aa*bb) *)
      mul_associativity h aa bb;                           (* (h*aa)*bb = h*(aa*bb) *)
      mul_commutativity h aa;                              (* h*aa = aa*h *)
      mul_congruence (h * aa) bb (aa * h) bb;              (* (h*aa)*bb = (aa*h)*bb *)
      mul_associativity aa h bb;                           (* (aa*h)*bb = aa*(h*bb) *)
      poly_eq_symmetry ((h * aa) * bb) (h * (aa * bb));
      poly_eq_transitivity (h * (aa * bb)) ((h * aa) * bb) ((aa * h) * bb);
      poly_eq_transitivity (h * (aa * bb)) ((aa * h) * bb) (aa * (h * bb));
      poly_eq_transitivity (h * (poly_prod rest)) (h * (aa * bb)) (aa * (h * bb))
#pop-options

(* Helper `divides_mul_both_sides` (d | a ⟹ (c·d) | (c·a)) is provided
   publicly by Core.Polynomial.Irreducible (IR.divides_mul_both_sides). *)

(* every masked sub-product divides the full product.
   (reserved for #33 soundness wiring) *)
let rec masked_prod_divides (#t:Type) {| f: field t |}
  (hs: list (polynomial t)) (mask: list bool)
  : Lemma (ensures divides (masked_prod hs mask) (PR.poly_prod hs))
          (decreases hs)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    match hs, mask with
    | h :: rest, b :: m' ->
      masked_prod_divides rest m';                 (* masked_prod rest m' | poly_prod rest *)
      (* poly_prod (h::rest) == h * poly_prod rest *)
      if b then begin
        (* masked_prod = h * masked_prod rest m' ; divide both sides by h *)
        IR.divides_mul_both_sides (masked_prod rest m') (PR.poly_prod rest) h
      end else begin
        (* masked_prod = masked_prod rest m' | poly_prod rest | h * poly_prod rest *)
        divides_mul_left (masked_prod rest m') h (PR.poly_prod rest)
      end
    | _ ->
      (* masked_prod hs mask == poly_one, which divides everything *)
      IR.one_divides_all (PR.poly_prod hs)

(* ================================================================ *)
(*  "every element of `hs` is irreducible" as an OPAQUE proposition,  *)
(*  with elim / proof-as-argument / intro bridges (mirrors            *)
(*  Core.Modular.Recombination.all_divide).                          *)
(* ================================================================ *)

[@@"opaque_to_smt"]
let all_irreducible (#t:Type) {| f: field t |} (hs: list (polynomial t))
  : prop = forall (h: polynomial t). L.memP h hs ==> IR.poly_irreducible h

let all_irreducible_elim (#t:Type) {| f: field t |}
  (hs: list (polynomial t){all_irreducible hs})
  : Lemma (forall (h: polynomial t). L.memP h hs ==> IR.poly_irreducible h)
  = reveal_opaque (`%all_irreducible) (all_irreducible hs)

let all_irreducible_proof (#t:Type) {| f: field t |} (hs: list (polynomial t))
  = (h:polynomial t{L.memP h hs}) -> Lemma (IR.poly_irreducible h)

let all_irreducible_intro (#t:Type) {| f: field t |}
  (hs: list (polynomial t)) (proof: all_irreducible_proof hs)
  : Lemma (all_irreducible hs)
  = reveal_opaque (`%all_irreducible) (all_irreducible hs);
    let aux (h: polynomial t) : Lemma (L.memP h hs ==> IR.poly_irreducible h)
      = introduce L.memP h hs ==> IR.poly_irreducible h
        with _hm. proof h
    in
    Classical.forall_intro aux

(* all_irreducible is preserved by dropping the head. *)
let all_irreducible_tail (#t:Type) {| f: field t |}
  (h: polynomial t) (rest: list (polynomial t))
  : Lemma (requires all_irreducible (h :: rest))
          (ensures  all_irreducible rest)
  = all_irreducible_elim (h :: rest);
    let proof (x: polynomial t{L.memP x rest}) : Lemma (IR.poly_irreducible x)
      = assert (L.memP x (h :: rest))
    in
    all_irreducible_intro rest proof

(* head of an all-irreducible list is irreducible. *)
let all_irreducible_head (#t:Type) {| f: field t |}
  (h: polynomial t) (rest: list (polynomial t))
  : Lemma (requires all_irreducible (h :: rest))
          (ensures  IR.poly_irreducible h)
  = all_irreducible_elim (h :: rest);
    assert (L.memP h (h :: rest))

(* ================================================================ *)
(*  Small numeric / structural helpers                               *)
(* ================================================================ *)

(* an irreducible polynomial has degree >= 1 (local structural helper). *)
private let irreducible_deg_ge1 (#t:Type) {| f: field t |} (q: polynomial t)
  : Lemma (requires IR.poly_irreducible q)
          (ensures  deg q >= 1)
  = ()

(* a divisor of a NONZERO polynomial is itself nonzero. *)
let divisor_nonzero (#t:Type) {| f: field t |} (d p: polynomial t)
  : Lemma (requires divides d p /\ deg p >= 0)
          (ensures  deg d >= 0)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if deg d >= 0 then ()
    else begin
      eliminate exists (k: polynomial t). (p = (d * k))
      returns deg d >= 0
      with _.
      begin
        UN.degree_none_poly_eq_zero d;                 (* d = poly_zero *)
        mul_commutativity d k;                          (* d*k = k*d *)
        mul_congruence k d k (poly_zero #t);             (* k*d = k*poly_zero *)
        H.x_mul_zero k;                                 (* k*zero = zero *)
        poly_eq_transitivity p (d * k) (k * d);
        poly_eq_transitivity (k * d) (k * (poly_zero #t)) (poly_zero #t);
        poly_eq_transitivity p (k * d) (poly_zero #t);
        UN.degree_well_defined p (poly_zero #t)          (* deg p == deg poly_zero < 0 : ⊥ *)
      end
    end

(* the product of a list of irreducible polynomials is nonzero. *)
let rec poly_prod_irred_nonzero (#t:Type) {| f: field t |}
  (hs: list (polynomial t))
  : Lemma (requires all_irreducible hs)
          (ensures  deg (PR.poly_prod hs) >= 0)
          (decreases hs)
  = match hs with
    | [] -> SD.poly_one_deg #t ()
    | h :: rest ->
      all_irreducible_head h rest;
      irreducible_deg_ge1 h;                             (* deg h >= 1 *)
      all_irreducible_tail h rest;
      poly_prod_irred_nonzero rest;                      (* deg (poly_prod rest) >= 0 *)
      (* poly_prod (h::rest) == h * poly_prod rest *)
      UN.degree_mul h (PR.poly_prod rest)                (* deg = deg h + deg (poly_prod rest) *)

(* ================================================================ *)
(*  MAIN THEOREM                                                      *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let rec divisor_of_irreducible_prod (#t:Type) {| f: field t |}
  (hs: list (polynomial t)) (g: polynomial t)
  : Lemma (requires all_irreducible hs /\ divides g (PR.poly_prod hs))
          (ensures  exists (c: t) (mask: list bool).
                       L.length mask == L.length hs /\
                       (not (c = zero)) /\
                       (g = ((poly_const c) * (masked_prod hs mask))))
          (decreases hs)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    H.elim_equatable_laws t ();
    match hs with
    | [] ->
      (* g | poly_prod [] == poly_one.  deg g == 0, so g = poly_const c. *)
      SD.divisor_of_one_deg_ge0 g;                       (* deg g >= 0 *)
      SD.poly_one_deg #t ();                              (* deg poly_one == 0 *)
      IR.divides_degree_le g (poly_one #t);              (* deg g <= 0 *)
      degree_zero_is_singleton g;                         (* g == [poly_lc g], lc <> zero *)
      let c : t = poly_lc g in
      monomial_zero_n_reveal c;                           (* poly_const c == [c] (c <> zero) *)
      assert (poly_const c == g);
      poly_mul_one (poly_const c);                        (* poly_const c * poly_one = poly_const c *)
      masked_prod_nil #t ([]);                            (* masked_prod [] [] == poly_one *)
      introduce exists (c2: t) (mask: list bool).
                  L.length mask == L.length hs /\
                  (not (c2 = zero)) /\
                  (g = ((poly_const c2) * (masked_prod hs mask)))
      with c ([])
      and ()
    | h :: rest ->
      let bigp = PR.poly_prod rest in
      (* poly_prod (h::rest) == h * bigp *)
      all_irreducible_head h rest;                        (* poly_irreducible h *)
      irreducible_deg_ge1 h;                              (* deg h >= 1 *)
      all_irreducible_tail h rest;                        (* all_irreducible rest *)
      Classical.excluded_middle (divides h g);
      eliminate (divides h g) \/ ~(divides h g)
      returns (exists (c: t) (mask: list bool).
                  L.length mask == L.length hs /\
                  (not (c = zero)) /\
                  (g = ((poly_const c) * (masked_prod hs mask))))
      with _hdiv.
      begin
        (* ---- CASE h | g : peel quotient, cancel h, recurse on rest ---- *)
        eliminate exists (w: polynomial t). (g = (h * w))
        returns (exists (c: t) (mask: list bool).
                    L.length mask == L.length hs /\
                    (not (c = zero)) /\
                    (g = ((poly_const c) * (masked_prod hs mask))))
        with _hw.
        begin
          (* divides g (h*bigp): substitute g = h*w and cancel h to get w | bigp. *)
          eliminate exists (k: polynomial t). ((h * bigp) = (g * k))
          returns divides w bigp
          with _hk.
          begin
            (* h*bigp = g*k = (h*w)*k = h*(w*k) *)
            SF.poly_mul_left_congruence g (h * w) k;          (* g*k = (h*w)*k *)
            mul_associativity h w k;                        (* (h*w)*k = h*(w*k) *)
            poly_eq_transitivity (h * bigp) (g * k) ((h * w) * k);
            poly_eq_transitivity (h * bigp) ((h * w) * k) (h * (w * k));
            FA.poly_mul_left_cancel h bigp (w * k);         (* bigp = w*k *)
            poly_eq_symmetry bigp (w * k);
            divides_intro w bigp k
          end;
          (* IH on rest with quotient w *)
          divisor_of_irreducible_prod rest w;
          eliminate exists (c: t) (mask': list bool).
                       L.length mask' == L.length rest /\
                       (not (c = zero)) /\
                       (w = ((poly_const c) * (masked_prod rest mask')))
          returns (exists (c: t) (mask: list bool).
                      L.length mask == L.length hs /\
                      (not (c = zero)) /\
                      (g = ((poly_const c) * (masked_prod hs mask))))
          with _hih.
          begin
            let pc : polynomial t = poly_const c in
            let mm : polynomial t = masked_prod rest mask' in
            (* g = h*w = h*(pc*mm) = pc*(h*mm) = pc * masked_prod hs (true::mask') *)
            mul_congruence h w h (pc * mm);                 (* h*w = h*(pc*mm) *)
            mul_associativity h pc mm;                       (* (h*pc)*mm = h*(pc*mm) *)
            mul_commutativity h pc;                          (* h*pc = pc*h *)
            mul_congruence (h * pc) mm (pc * h) mm;          (* (h*pc)*mm = (pc*h)*mm *)
            mul_associativity pc h mm;                       (* (pc*h)*mm = pc*(h*mm) *)
            masked_prod_cons_true h rest mask';              (* masked_prod hs (true::mask') == h*mm *)
            introduce exists (c2: t) (mask: list bool).
                        L.length mask == L.length hs /\
                        (not (c2 = zero)) /\
                        (g = ((poly_const c2) * (masked_prod hs mask)))
            with c (true :: mask')
            and ()
          end
        end
      end
      and _hndiv.
      begin
        (* ---- CASE h ∤ g : coprime g h, Euclid gives g | bigp ---- *)
        poly_prod_irred_nonzero (h :: rest);               (* deg (poly_prod hs) >= 0 *)
        divisor_nonzero g (PR.poly_prod (h :: rest));       (* deg g >= 0 *)
        IR.irreducible_coprime_or_divides h g;              (* coprime h g \/ divides h g *)
        (* not (divides h g), so coprime h g *)
        IR.coprime_symmetric h g;                           (* coprime g h *)
        (* g | h*bigp = bigp*h, and coprime g h ⟹ g | bigp (Euclid). *)
        mul_commutativity h bigp;                           (* h*bigp = bigp*h *)
        divides_congruence_right g (h * bigp) (bigp * h);   (* divides g (bigp*h) *)
        euclid_lemma g h bigp;                              (* divides g bigp *)
        (* IH on rest with g *)
        divisor_of_irreducible_prod rest g;
        eliminate exists (c: t) (mask': list bool).
                     L.length mask' == L.length rest /\
                     (not (c = zero)) /\
                     (g = ((poly_const c) * (masked_prod rest mask')))
        returns (exists (c: t) (mask: list bool).
                    L.length mask == L.length hs /\
                    (not (c = zero)) /\
                    (g = ((poly_const c) * (masked_prod hs mask))))
        with _hih.
        begin
          masked_prod_cons_false h rest mask';             (* masked_prod hs (false::mask') == masked_prod rest mask' *)
          introduce exists (c2: t) (mask: list bool).
                      L.length mask == L.length hs /\
                      (not (c2 = zero)) /\
                      (g = ((poly_const c2) * (masked_prod hs mask)))
          with c (false :: mask')
          and ()
        end
      end
#pop-options

(* ================================================================ *)
(*  §D2b+ — complementary masked products are COPRIME.               *)
(*                                                                   *)
(*  For an all-irreducible, PAIRWISE-COPRIME family `hs` over a field *)
(*  and any mask, `masked_prod hs mask` and `masked_prod hs ¬mask`   *)
(*  are coprime — hence (by a Bezout identity) generate poly_one.    *)
(*  This is exactly what discharges RecombinationComplete's mod-p    *)
(*  Bezout hypothesis on the fp side (FpZmodBridge).                 *)
(* ================================================================ *)

(* `negate_mask` preserves length and flips each bit (index-wise). *)
let rec negate_mask_length (mask: list bool)
  : Lemma (ensures L.length (negate_mask mask) == L.length mask)
          (decreases mask)
  = match mask with
    | []      -> ()
    | _ :: m' -> negate_mask_length m'

let rec negate_mask_index (mask: list bool) (i:nat)
  : Lemma (requires i < L.length mask /\ i < L.length (negate_mask mask))
          (ensures  L.index (negate_mask mask) i == not (L.index mask i))
          (decreases mask)
  = match mask with
    | []      -> ()
    | b :: m' -> if i = 0 then () else negate_mask_index m' (i - 1)

(* ---- pairwise coprimality: now IR.pairwise_coprime (raw-nat spelling,  *)
(*      shared with Core.Polynomial.CRTMulti; hosted in                   *)
(*      Core.Polynomial.Irreducible next to pairwise_coprime_divides).    *)

(* a masked product of irreducibles is nonzero (deg >= 0). *)
let rec masked_prod_irred_nonzero (#t:Type) {| f: field t |}
  (hs: list (polynomial t)) (mask: list bool)
  : Lemma (requires all_irreducible hs)
          (ensures  deg (masked_prod hs mask) >= 0)
          (decreases hs)
  = match hs, mask with
    | h :: rest, b :: m' ->
      all_irreducible_head h rest;
      irreducible_deg_ge1 h;                     (* deg h >= 1 *)
      all_irreducible_tail h rest;
      masked_prod_irred_nonzero rest m';          (* deg (masked_prod rest m') >= 0 *)
      if b then begin
        masked_prod_cons_true h rest m';          (* masked_prod hs mask == h * masked_prod rest m' *)
        UN.degree_mul h (masked_prod rest m')     (* deg = deg h + deg rest >= 0 *)
      end else masked_prod_cons_false h rest m'
    | [], _ ->
      masked_prod_nil #t mask;
      SD.poly_one_deg #t ()
    | h :: rest, [] ->
      masked_prod_mask_nil (h :: rest);
      SD.poly_one_deg #t ()

(* irreducible q dividing a product divides one of the factors
   (reconstructed locally: Berlekamp's irreducible_prime is downstream). *)
private let irreducible_prime_local (#t:Type) {| f: field t |} (q a b: polynomial t)
  : Lemma (requires IR.poly_irreducible q /\ divides q (a * b))
          (ensures  divides q a \/ divides q b)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if deg a < 0 then begin
      (* a = poly_zero, so q | a (witness poly_zero). *)
      UN.degree_none_poly_eq_zero a;                   (* a = poly_zero *)
      H.x_mul_zero q;                                  (* q * poly_zero = poly_zero *)
      poly_eq_symmetry (q * (poly_zero #t)) (poly_zero #t);
      poly_eq_transitivity a (poly_zero #t) (q * (poly_zero #t));
      divides_intro q a (poly_zero #t)
    end else begin
      Classical.excluded_middle (divides q a);
      eliminate (divides q a) \/ ~(divides q a)
      returns (divides q a \/ divides q b)
      with _hd. ()
      and _hnd.
      begin
        IR.irreducible_coprime_or_divides q a;          (* coprime q a \/ divides q a ; not-div ⟹ coprime *)
        mul_commutativity a b;                           (* a*b = b*a *)
        divides_congruence_right q (a * b) (b * a);      (* divides q (b*a) *)
        euclid_lemma q a b                               (* coprime q a /\ q|(b*a) ⟹ q | b *)
      end
    end

(* an irreducible q dividing masked_prod hs mask divides some KEPT factor:
   there is an INDEX i with mask-bit true and q | hs_i.  Index-wise (not
   memP) so S/¬S disjointness stays airtight under repeated factors. *)
[@@"opaque_to_smt"]
let some_kept_index_divides (#t:Type) {| f: field t |}
  (q: polynomial t) (hs: list (polynomial t)) (mask: list bool)
  : prop = exists (i:nat). i < L.length hs /\ i < L.length mask /\
             L.index mask i == true /\ divides q (L.index hs i)

let some_kept_index_divides_elim (#t:Type) {| f: field t |}
  (q: polynomial t) (hs: list (polynomial t)) (mask: list bool)
  : Lemma (requires some_kept_index_divides q hs mask)
          (ensures  exists (i:nat). i < L.length hs /\ i < L.length mask /\
             L.index mask i == true /\ divides q (L.index hs i))
  = reveal_opaque (`%some_kept_index_divides) (some_kept_index_divides q hs mask)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
private let rec irreducible_divides_masked_prod (#t:Type) {| f: field t |}
  (q: polynomial t) (hs: list (polynomial t)) (mask: list bool)
  : Lemma (requires IR.poly_irreducible q /\ divides q (masked_prod hs mask))
          (ensures  some_kept_index_divides q hs mask)
          (decreases hs)
  = reveal_opaque (`%some_kept_index_divides) (some_kept_index_divides q hs mask);
    H.elim_equatable_laws (polynomial t) ();
    match hs, mask with
    | h :: rest, b :: m' ->
      if b then begin
        masked_prod_cons_true h rest m';                 (* masked == h * masked_prod rest m' *)
        irreducible_prime_local q h (masked_prod rest m');
        eliminate (divides q h) \/ (divides q (masked_prod rest m'))
        returns (some_kept_index_divides q hs mask)
        with _hh.
          (* i = 0: bit true, q | hs_0 = h *)
          introduce exists (i:nat). i < L.length hs /\ i < L.length mask /\
                      L.index mask i == true /\ divides q (L.index hs i)
          with 0 and ()
        and _hr.
        begin
          irreducible_divides_masked_prod q rest m';
          some_kept_index_divides_elim q rest m';
          eliminate exists (j:nat). j < L.length rest /\ j < L.length m' /\
                      L.index m' j == true /\ divides q (L.index rest j)
          returns (some_kept_index_divides q hs mask)
          with _hj.
            introduce exists (i:nat). i < L.length hs /\ i < L.length mask /\
                        L.index mask i == true /\ divides q (L.index hs i)
            with (j ++ 1) and ()
        end
      end else begin
        masked_prod_cons_false h rest m';                (* masked == masked_prod rest m' *)
        irreducible_divides_masked_prod q rest m';
        some_kept_index_divides_elim q rest m';
        eliminate exists (j:nat). j < L.length rest /\ j < L.length m' /\
                    L.index m' j == true /\ divides q (L.index rest j)
        returns (some_kept_index_divides q hs mask)
        with _hj.
          introduce exists (i:nat). i < L.length hs /\ i < L.length mask /\
                      L.index mask i == true /\ divides q (L.index hs i)
          with (j ++ 1) and ()
      end
    | [], _ ->
      (* masked == poly_one ; q | poly_one with deg q >= 1 is impossible. *)
      masked_prod_nil #t mask;
      SD.poly_one_deg #t ();
      IR.divides_degree_le q (poly_one #t)
    | h :: rest, [] ->
      masked_prod_mask_nil (h :: rest);
      SD.poly_one_deg #t ();
      IR.divides_degree_le q (poly_one #t)
#pop-options

(* MAIN: complementary masked products of a pairwise-coprime irreducible
   family are coprime. *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let masked_prod_coprime (#t:Type) {| f: field t |}
  (hs: list (polynomial t)) (mask: list bool)
  : Lemma (requires all_irreducible hs /\ IR.pairwise_coprime hs /\
                    L.length mask == L.length hs)
          (ensures  coprime (masked_prod hs mask)
                            (masked_prod hs (negate_mask mask)))
  = H.elim_equatable_laws (polynomial t) ();
    let a = masked_prod hs mask in
    let b = masked_prod hs (negate_mask mask) in
    let d = poly_gcd a b in
    masked_prod_irred_nonzero hs mask;                   (* deg a >= 0 *)
    masked_prod_irred_nonzero hs (negate_mask mask);     (* deg b >= 0 *)
    SF.gcd_has_degree a b;                               (* deg d >= 0 *)
    coprime_reveal a b;                                  (* coprime a b <==> deg d = 0 *)
    if deg d = 0 then ()
    else begin
      (* deg d >= 1: an irreducible factor q of d divides BOTH a and b,
         hence divides a KEPT factor of mask AND of ¬mask — at DISTINCT
         indices — contradicting pairwise coprimality. *)
      gcd_divides_left  a b;                             (* d | a *)
      gcd_divides_right a b;                             (* d | b *)
      IR.irreducible_factor_exists d;
      IR.pairwise_coprime_elim hs;
      eliminate exists (q: polynomial t). (IR.poly_irreducible q /\ divides q d)
      returns (coprime a b)
      with _hq.
      begin
        divides_trans q d a;                             (* q | a = masked_prod hs mask *)
        divides_trans q d b;                             (* q | b = masked_prod hs ¬mask *)
        irreducible_divides_masked_prod q hs mask;
        irreducible_divides_masked_prod q hs (negate_mask mask);
        some_kept_index_divides_elim q hs mask;
        some_kept_index_divides_elim q hs (negate_mask mask);
        eliminate exists (i:nat). i < L.length hs /\ i < L.length mask /\
                    L.index mask i == true /\ divides q (L.index hs i)
        returns (coprime a b)
        with _hi.
          eliminate exists (j:nat). j < L.length hs /\ j < L.length (negate_mask mask) /\
                      L.index (negate_mask mask) j == true /\ divides q (L.index hs j)
          returns (coprime a b)
          with _hj.
          begin
            negate_mask_length mask;                     (* len ¬mask == len mask *)
            negate_mask_index mask j;                    (* (¬mask)_j == not mask_j ⟹ mask_j = false *)
            assert (i <> j);                             (* mask_i = true, mask_j = false *)
            let hi = L.index hs i in
            let hj = L.index hs j in
            gcd_is_maximal hi hj q;                      (* q | gcd(hi,hj) *)
            coprime_reveal hi hj;                        (* coprime hi hj ⟹ deg gcd = 0 *)
            IR.divides_degree_le q (poly_gcd hi hj)      (* deg q <= 0, contra deg q >= 1 *)
          end
      end
    end
#pop-options

(* COROLLARY: a Bezout identity for the complementary masked products
   (reuses PartialFraction.bezout_identity — coprime ⟹ Bezout). *)
let masked_prod_bezout (#t:Type) {| f: field t |}
  (hs: list (polynomial t)) (mask: list bool)
  : Lemma (requires all_irreducible hs /\ IR.pairwise_coprime hs /\
                    L.length mask == L.length hs)
          (ensures  exists (s tt: polynomial t).
             ((s * (masked_prod hs mask))
              + (tt * (masked_prod hs (negate_mask mask)))) = (poly_one #t))
  = let a = masked_prod hs mask in
    let b = masked_prod hs (negate_mask mask) in
    masked_prod_irred_nonzero hs mask;                   (* deg a >= 0 *)
    masked_prod_coprime hs mask;                         (* coprime a b *)
    PF.bezout_identity a b;                              (* bl*a + br*b = poly_one *)
    introduce exists (s tt: polynomial t).
                ((s * a) + (tt * b)) = (poly_one #t)
    with (PF.bezout_left a b) (PF.bezout_right a b) and ()
