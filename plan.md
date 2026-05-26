# CuteCAS plan — current state (2026-05-27)

> **READ FIRST.** This banner supersedes every entry beneath it.
> Historical sections are kept for context but their concrete paths
> (`core\…`, the old `..\new\` tower, `proto\`, etc.) **no longer
> exist on disk**.

## Layout

- **Flat repo.** All `Core.*.{fst,fsti}` live at the repo root
  (`c:\Projects\CuteCAS\`).
- Build: `fstar.exe --include . --cache_checked_modules --cache_dir obj <Mod>.fst`.
- `legacy\AlgebraTypes.fst` — historical artifact, not on include path.
- `c:\Projects\cutecas-backup\` — full pre-cleanup snapshot. Safety
  net; can be deleted now that Euclidean division has landed.

## Modules (25 .fst + 6 .fsti, ~18.3k LOC, all verify clean from cold cache)

**Foundation (algebra typeclasses + tactics)**
- `Core.Algebra` (+ `.Notation`, `.Int`, `.Helpers`, `.Combinators`,
  `.Divisibility`, `.Test`, `.NotationTest`)
- `Core.Tactics.CanonRing` (carrier-type-aware `canon_ring()` —
  picks the CR/ID/field binder whose carrier matches the goal LHS)
- `Core.Tactics.CanonCommGroup`

**Sums / permutations / matrices**
- `Core.FinSum` (+ `.fsti`)
- `Core.Permutation` (+ `.fsti`, `.Enum`, `.Sum`)
- `Core.Matrix` (+ `.Ring`, `.MultiDistrib`, `.Determinant`,
  `.Determinant.Mul`, `.Sylvester`, `.Resultant`)

**Fractions**
- `Core.Fractions` (+ `.fsti`) — `field (fraction t)` over `integral_domain t`.

**Polynomials (class-based tower)**
- `Core.Polynomial.Class` (~2200 LOC) — `polynomial_commutative_ring`
  + `polynomial_integral_domain` classes and their instances proved
  end-to-end. Two stale `admit()`s in unused helpers
  (`poly_add_cons_cons_compute`, second conjunct of `poly_neg_all_zero`)
  remain as FIXMEs.
- `Core.Polynomial.Class.Div` (+ `.fsti`, **NEW: 670 LOC**) — monomial,
  `poly_sub`, coefficient identities, degree bounds, **Euclidean
  division** (`poly_divmod` + `poly_divmod_correct` +
  `poly_divmod_correct_degree`), and `polynomial_euclidean_domain_instance`.
  Zero admits, zero assumes.
- `Core.Polynomial.Class.Tests` — 25 lemmas exercising the polynomial
  CR / ID / Section-E canon_ring instances. All pass.

## Risch master plan — current standing

The headline ambition is unchanged: a fully verified Risch integrator
for the **purely transcendental** case, with both soundness (output
differentiates to input) and Liouville completeness, no admits / no
assumes. References: Bronstein ch. 5; Geddes–Czapor–Labahn ch. 11–12.

| Phase | Module | Status |
|---|---|---|
| 0 — Typeclass tower | `Core.Algebra*`, `Core.Tactics.*` | ✅ done |
| 1 — Polynomials (ring + ID instance) | `Core.Polynomial.Class` | ✅ done |
| 1.5 — Permutations + det + Sylvester | `Core.Permutation.*`, `Core.Matrix.*` | ✅ done |
| 1.75 — Algebraic constants (ℚ[c]/R(c)) | _not started_ | ⏳ |
| 2a — Euclidean division | `Core.Polynomial.Class.Div` | ✅ done (this push) |
| 2b — Polynomial GCD (Euclid) | _to port from backup_ | ⏳ next |
| 2c — Square-free factorization (Yun) | _to write_ | ⏳ |
| 2d — Resultant ⇔ common factor (L4) | `Core.Matrix.Resultant` + GCD | ⏳ (needs GCD) |
| 2e — Subresultant PRS + correctness | _to write_ | ⏳ |
| 3 — Rational functions + derivations | `Core.Derivation`, `Core.RatFun` | ⏳ |
| 4 — Risch for ℚ(x) (Hermite + LRT) | `Risch.*` | ⏳ |
| 5.0 — Factorization in ℚ[x] (for completeness) | _Berlekamp/Hensel/Zass._ | ⏳ |
| 5 — Liouville for rationals | `Risch.Liouville` | ⏳ |
| 6 — Tower extensions (exp/log layers) | stretch | ⏳ |

**Soundness-only path** (Phases 1 → 4) closes the headline "verified
ℚ(x) integrator" goal. **Tier 0** (soundness + completeness for
rationals) adds Phase 5.0 + Phase 5. Phase 6 is open-ended.

## What's next

1. **Phase 2b — Polynomial GCD via Euclid.** Port from
   `c:\Projects\cutecas-backup\core\Core.Polynomial.GCD.fst` (~920 LOC,
   already verified in the old layout). With `poly_divmod` now in
   `Class.Div`, the port is mostly mechanical name-translation.
2. **Phase 1.75 — algebraic constants.** Unblocked the moment `poly_mod`
   is exposed; can run in parallel with 2b if needed.
3. **Phase 2c — Yun square-free factorization.** Short module, depends
   only on GCD + derivative of a polynomial.
4. **Phase 2d — L4 resultant ⇔ common factor.** Last open item in
   `Core.Matrix.Resultant`; closes the Sylvester chapter.
5. **Phase 2e — Subresultant PRS** (Bronstein §1.4 / GCL §7.3) and
   correctness against the Sylvester determinant.
---
## ✅ 2026-05-23 review pass + Phase A applied (autopilot session)

Full 4-agent (Opus 4.7) audit of `core\` complete. Applied autonomously:
- 22 `#push-options` z3rlimit/fuel reductions across FinSum,
  Determinant, Determinant.Mul, MultiDistrib, Polynomial.Div,
  Polynomial.Mul (no lemma in `core\` needs `z3rlimit > 80`).
- 3 `canon_ring()` collapses in Determinant / Polynomial.Mul (−20 LOC).
- F-005 `assert_norm` cleanup in `Core.FinSum.fst`.
- Polynomial-chain SMTPat reveal-lemma elimination: only
  `polynomial_integral_domain` is still an `instance`; everything
  upstream is plain `let` with explicit reveal-lemma bridges.

Full 32/32 from-scratch verification clean. **Phase B deferred** —
see `core\review_summary.md` for the curated list of risky items
(D-001 matrix triple-instance, D-002 `unfold instance` ×7, D-003
`id_of_f`, F-002 trefl-bridge). D-002 probe revealed only 3 break
sites (Determinant.fst:342, Determinant.Mul.fst:127, Fractions.fst:44)
but each needs manual `compute ()` / local-let fix-up — not
autopilot-safe.

Working artefacts preserved (DO NOT DELETE): `scratch_{smells,
diamonds,canon,perf}.fst`, `review_{smells,diamonds,canon,perf}.md`,
`review_summary.md`, `apply_perf_fixes_v2.ps1`, plus 4 canon helpers.

---

## ✅ 2026-05-25 — Polynomial UFD landed + monic normalization scaffold

**This session (autopilot, 36/36 modules verified clean, zero admits):**

Path (a) — structural-induction route — successfully landed:

- `Core.Polynomial.GCD.{fsti,fst}` extended (~720 LOC total, was ~200):
  - `poly_divmod_unique` (lives in GCD.fst): given two valid `(qi,ri)`
    Euclidean-division decompositions of `p` by `q`, they are
    `poly_eq` on both components.
  - `poly_mod_congruence`: `poly_eq p1 p2 ⇒ poly_eq (mod p1 q) (mod p2 q)`.
  - `poly_divmod_q_congruence`: `poly_eq q1 q2 ⇒ poly_eq (div p q1) (div p q2)`
    and same for `mod` (vary the divisor).
  - `poly_gcd_congruence`: 4th gcd_domain axiom, by structural induction on
    `gcd_measure y1`, recurse via `poly_mod_congruence`.
  - Supporting infrastructure: `poly_eq_well_defined_all_zero`,
    `poly_eq_of_sub_all_zero`, `poly_neg_mul_r`, `poly_mul_sub_distrib`,
    `poly_mul_left_cancel`, `poly_add_left_cancel`, `poly_add_eq_to_sub`,
    plus reveal lemmas `poly_gcd_field_base`/`poly_gcd_field_step` exposing
    the recursion structure of `poly_gcd_field` across the fsti boundary,
    and `gcd_measure_decreases` now public.

- `Core.Polynomial.Domain.fst` got
  `polynomial_cr_of_id_eq_pcr : cr_of_id _ #(polynomial_integral_domain id)
    == polynomial_commutative_ring (cr_of_id t #id)` — bridges the class
  signature's auto-derived `cr_of_id` to the explicit
  `polynomial_commutative_ring`, with body `()` (both sides transparent
  in Domain.fst because `polynomial_integral_domain` is the only
  consumer of `polynomial_commutative_ring` here).

- `Core.Polynomial.UFD.fst` (NEW, 59 LOC):
  - `polynomial_gcd_domain` plain `let` wiring the four axioms.
    `gcd_congruence` uses `polynomial_ring_add_reveal` +
    `polynomial_acg_eq_reveal` chain to translate class-eq to `poly_eq`.
    `gcd_divides_*` and `gcd_is_maximal` use
    `polynomial_cr_of_id_eq_pcr` to translate `cr_of_id …` to
    `polynomial_commutative_ring` so the existing `poly_gcd_*` lemmas
    apply.
  - `instance polynomial_ufd` — marker.

- `Core.Polynomial.Mul.{fsti,fst}` gained `leading_coefficient_none` and
  `leading_coefficient_some` reveal lemmas (None ⇒ zero; Some n ⇒ coeff
  at n).

- `Core.Polynomial.Monic.fst` (NEW, 53 LOC) — appendix scaffolding:
  - `monic_normalize p`: identity on zero polynomials, otherwise
    `scalar_mul (inv lc) p`.
  - `monic_normalize_all_zero_case` reveal lemma.
  - **TODO** (deferred): `monic_normalize_some_case` body reveal,
    `monic_normalize_degree`, `monic_normalize_congruence`,
    `monic_normalize_idempotent`, `monic_normalize_associate`
    (both-ways divisibility), `poly_gcd_monic` + an alternative
    `polynomial_gcd_domain_monic` instance. These need an auxiliary
    `coeff_at_well_defined` lemma (poly_eq preserves coeff_at
    pointwise), which doesn't exist yet — adding it is straightforward
    by structural induction but has SMT-elaboration quirks across the
    Mul.fsti boundary; left as the next concrete task on the monic
    appendix.

**Build state**: `build-all.ps1` order extended with `Core.Polynomial.UFD.fst`
and `Core.Polynomial.Monic.fst`. Clean from-scratch rebuild: all 36 modules
verify, zero admits, zero assumes.

---

## 🚧 2026-05-24 — GCD divisibility core landed (poly UFD WIP)

Toward "implement domains all the way to land poly UFD":

**Landed this session (34/34 modules verified clean, zero admits):**

- `Core.Algebra.Divisibility` extended with 8 derived divisibility
  lemmas: `divides_zero`, `divides_congruence_{left,right}`,
  `divides_{neg,add,sub}`, `divides_mul_{right,left}`.
- `Core.Polynomial.Mul.fsti` gained `polynomial_commutative_ring_cr_r_reveal`
  reveal lemma (needed to bridge `pcr.cr_r ≡ polynomial_ring cr`).
- `Core.Polynomial.GCD.{fsti,fst}` (NEW, ~200 LOC):
  - `gcd_measure` + `gcd_measure_zero_iff_all_zero`.
  - `poly_gcd_field` — Euclidean recursion over a field, terminating
    on `gcd_measure (remainder) < gcd_measure (divisor)` via
    `poly_divmod_correct_degree`.
  - `poly_gcd_divides_left` — gcd p q divides p (by mutual induction
    with divides_right).
  - `poly_gcd_divides_right` — gcd p q divides q.
  - `poly_gcd_maximal` — d | p ∧ d | q ⇒ d | gcd p q.
  All three divisibility proofs use explicit reveal-lemma bridges
  (`polynomial_commutative_ring_cr_r_reveal`, `polynomial_ring_*_reveal`,
  `polynomial_acg_*_reveal`) to translate `poly_divmod_correct`'s
  poly_eq statement into class-eq form on the polynomial
  `commutative_ring`, then chain `divides_mul_right` + `divides_add` /
  `divides_sub` + `divides_congruence_right`. The maximal proof uses
  a manual additive-group cancellation chain (add_commutativity →
  add_associativity → add_negation → add_zero) since `canon_ring`
  picks up the base-field CR by typeclass resolution instead of the
  intended polynomial CR.

**Refined analysis of `gcd_congruence` (the remaining 4th axiom):**

The axiom shape is `eq x1 x2 /\ eq y1 y2 ⇒ eq (gcd x1 y1) (gcd x2 y2)` — i.e.
`poly_eq` inputs, not associates. So the original "monic normalization is
required" reasoning is **too pessimistic**: poly_eq inputs (same poly, possibly
different trailing zeros) should produce poly_eq Euclidean GCDs by structural
induction. Two viable paths to close it:

- **(a) Structural induction route (~150 LOC)**: prove
  `poly_divmod_unique` + `poly_mod_congruence` first, then induct on
  `gcd_measure` over `poly_gcd_field` directly. Stays inside the
  Euclidean recursion; no monic wrapper needed. Aligned with the
  congruence axiom shape exactly.
- **(b) Monic normalization route (~300 LOC)**: wrap as
  `poly_gcd_monic = monic_normalize ∘ poly_gcd_field` and use
  `monic_uniqueness` to get poly_eq from mutual divisibility.
  Heavier but yields a canonical/principal GCD (useful downstream for
  Bézout/Yun/subresultant work).

Recommend **(a) first** to land `polynomial_ufd` quickly, then layer
monic normalization on top as a separate enhancement when the algebraic
representation matters.

**Remaining work to land `polynomial_ufd` (path (a), ~150 LOC):**

0. **`Core.Polynomial.Div.{fsti,fst}` extension:**
   - `poly_divmod_unique`: given (q1,r1) and (q2,r2) both satisfying
     `p ≡ q·qi + ri` and `degree ri < degree q`, then `poly_eq q1 q2`
     and `poly_eq r1 r2`.
   - `poly_mod_congruence`: `poly_eq p1 p2 ⇒ poly_eq (snd (poly_divmod p1 q)) (snd (poly_divmod p2 q))`.

1. **`Core.Polynomial.GCD.fst` extension:**
   - `poly_gcd_congruence`: structural induction on `gcd_measure y1`.
     Base: both args have `all_zero` second arg; return their first args
     (poly_eq by hypothesis). Step: recurse on `(y_i, poly_mod x_i y_i)`;
     use `poly_mod_congruence` to discharge the new second arg
     congruence, recurse.

2. **`Core.Polynomial.UFD.fst` (NEW, ~30 LOC):**
   - `polynomial_gcd_domain` plain `let` with the four axioms.
   - `instance polynomial_ufd` — marker class, 3 lines.

3. **`build-all.ps1`**: append `Core.Polynomial.UFD.fst`.

**Optional follow-up (path (b)) for canonical GCD representation:**

1. **Monic normalization** (`Core.Polynomial.Monic.{fsti,fst}`, NEW):
   - `monic_normalize p = if all_zero p then [] else scalar_mul (inv (lc p)) p`.
   - Supporting lemmas: `degree_scalar_mul_nonzero`,
     `scalar_mul_lc`, `monic_normalize_lc_one`,
     `monic_normalize_divides_both_ways` (monic_normalize p and p
     divide each other), `monic_uniqueness` (two monic-or-zero polys
     with mutual divisibility are poly_eq).
   - `monic_uniqueness` is the hard one: needs `degree_mul`
     (already in `Polynomial.Domain.fst`), `mul_by_unit_means_associate`,
     leading-coefficient arithmetic over a field.

2. **`Core.Polynomial.GCD.fst` extension:**
   - `poly_gcd_monic p q = monic_normalize (poly_gcd_field p q)`.
   - `poly_gcd_monic_congruence`: poly_eq inputs ⇒ poly_eq outputs.
     Proof: associates via gcd_maximal symmetry + monic_uniqueness.
   - Re-prove divides_left/right/maximal for `poly_gcd_monic`
     (trivial given monic_normalize_divides_both_ways).

3. **`Core.Polynomial.UFD.fst` (NEW):**
   - `polynomial_gcd_domain (#t:Type) (f: field t) : gcd_domain (polynomial …)`
     plain `let`, with `gcd = poly_gcd_monic`.
   - `instance polynomial_ufd #t {| f: field t |} : ufd (...)` — 3 lines.

4. **`build-all.ps1`**: add `Core.Polynomial.Monic`, `Core.Polynomial.UFD`.

Estimated effort: 4-6 hours of focused work.

---


## ✅ Public-signature hygiene refactor COMPLETE (H3+H4+H5)

All `.fsti` files in `core\` now carry **hygienic Lemma signatures**: no
`forall`, no inline `fun`, no `if`/`match` in any `requires`/`ensures`
clause. Remaining occurrences live exclusively in `let`/`unfold let`
**definition bodies** (`all_distinct`, `respects_perm_eq`, `fin_sum`,
`fin_prod`) or in comments — these are intentional and allowed.

**What was done:**

- **H3 — `Core.FinSum`**: `sum_list_map_congruence` callback gated by
  `requires memP x xs` (correct API — equality is only required for
  actual list elements). Internal cascade through `Determinant.Mul`
  used contravariant requires-on-callback subtyping so old `prf`
  callbacks continued to typecheck.
- **H4 — `Core.Permutation.Sum`**: 9 lemmas converted to **callback
  form** (`sum_over_perms_{congruence,neg,add,mul_left}_named`,
  `_via_count_one_list`, `_single`, `_all_zero`, `_pair_cancel`,
  `respects_perm_eq_intro`). Inline lambdas in posts replaced with
  named combinators: `fcomp f inverse`, `fcomp f (flip compose q)`,
  `bool_to_nat (perm_eq p h)` (where `bool_to_nat` is `unfold`).
  External cascade applied to 32 call sites in `Core.Matrix.Determinant.fst`
  (26) and `Core.Matrix.Determinant.Mul.fst` (6).
- **H5 — Scan**: confirmed no remaining hygiene violations in any
  `.fsti`. Only `forall`/`fun`/`match` left are in definition bodies
  or doc comments.

**Verified clean from cold cache (2026-05-23):**
Core.FinSum, Core.Permutation.Sum, Core.Matrix.Ring,
Core.Matrix.MultiDistrib, Core.Matrix.Determinant,
Core.Matrix.Determinant.Mul. The entire tower rebuilds without
warnings.

**Reusable tooling produced**:
- `core\h3_cascade2.py`, `core\h4_cascade.py` — arity-aware
  callback-form cascades. Count top-level args; append
  `(fun _ -> ())` when caller is one arg short of new arity.
- Known false positive: 2-callback lemmas (e.g. `respects_perm_eq_intro`)
  need a manual post-pass to fix the second `(fun _ -> ())` →
  `(fun _ _ -> ())`. Use a PowerShell regex pass for these.

**Why this matters**: public Lemma signatures stamped with `forall` or
inline `fun` create unification fragility at call sites. Hygienic
signatures (callbacks + named combinators) deliver their posts
predictably in any diamond-bridged context. This is now a
**non-negotiable repo rule** — see `AGENTS.md` §"Public-signature
hygiene".

---

## 🧩 Pointwise combinator design (decided 2026-05-22)

Function ring abandoned — `equatable.eq : t -> t -> bool`, so functions
cannot have a (bool-valued) equatable instance without a tower-level
redesign. Instead, we introduce a small vocabulary of **named pointwise
combinators** that callers use in place of inline lambdas in lemma
postconditions. This forces a stable named form that survives F*
unification.

**Module**: new `Core.Algebra.Pointwise` (plain `let`, NOT `unfold`).

**Approved combinators**:

```fstar
let const           (#a #t: Type) (v: t) (_: a) : t = v
let pointwise_neg   (#a #t: Type) {| add_comm_group t |}
                    (f: a -> t) (x: a) : t = neg (f x)
let pointwise_add   (#a #t: Type) {| add_comm_group t |}
                    (f g: a -> t) (x: a) : t = f x + g x
let pointwise_mul   (#a #t: Type) {| ring t |}
                    (f g: a -> t) (x: a) : t = f x * g x
let pointwise_mul_left  (#a #t: Type) {| ring t |}
                        (c: t) (f: a -> t) (x: a) : t = c * f x
let pointwise_mul_right (#a #t: Type) {| ring t |}
                        (f: a -> t) (c: t) (x: a) : t = f x * c
let swap_args       (#a #b #c: Type)
                    (f: a -> b -> c) (y: b) (x: a) : c = f x y
let kronecker_delta (#t: Type) {| ring t |}
                    (i j: nat) : t = if i = j then one else zero
let fin_lift        (#t: Type) {| add_comm_group t |} (#n: nat)
                    (f: fin n -> t) (k: nat) : t
                    = if k < n then f (k <: fin n) else zero
```

**Compositions** (no dedicated name needed):
- `mask_at i0 g` = `pointwise_mul (kronecker_delta i0) g`
- `const_zero` = `const zero`, `const_one` = `const one`

**Why no `unfold`**: stable named form must NOT reduce away during
unification. Callers `norm [delta_only [...]]` explicitly when they
need the body.

---

## 🔍 Lambda-in-postcondition survey (post-det_mul)

After delivering `det_mul`, surveyed all inline-lambda postconditions
across foundational modules. Findings:

**Already fixed (3)**: Core.Permutation.Sum.fsti has `_named` variants
for `sum_over_perms_{neg,add,mul_left}`. These were used successfully
in det_mul (Section M).

**Pending (~20 lemmas)**:
- `Core.FinSum.fsti` (16): `sum_list_map_{neg,add,mul_left}`,
  `sum_range_{const_zero,mul_left,mul_right,add_distrib,swap}`,
  `fin_sum_{mul_left,mul_right,swap,const_zero,add}`,
  `kronecker_extract` (x2).
- `Core.Matrix.Determinant.Mul.fst` (2): `sum_list_zeros`,
  `factor_inner_perm_sum`.
- `Core.Matrix.MultiDistrib.fst` (3): `sum_list_map_mul_right`,
  and two specs around the multi-distrib induction.

**Pattern (proven, ~100 LOC effort)**:
`val foo_named (nf f: a -> t) (xs: list a)
  : Lemma (requires forall x. nf x = OP (f x)) (ensures ...named form...)`

**Estimated downstream win**: each `_named` variant removes 5-10 lines
of `assert by trefl` / `leibniz_to_eq` / transitivity bridging from
any caller that wants to use a let-bound named function instead of a
fresh inline lambda. det_expand alone contains ~30 lines of such
bridging that would collapse.

Recommended next: do the FinSum batch (16 entries, big return).

---
## ✅ Latest milestone: det_mul VERIFIED in new tower

`core\Core.Matrix.Determinant.Mul.fst` (1390 LOC, all CRLF, zero
admits/assumes, no lambdas in postconditions) is **fully verified**.
Cauchy-Binet `det (A * B) = det A * det B` proved cleanly in the
diamond-free tower.

Sections delivered: A (term builders), B (perm_product expansion via
fin_sum), C (a_prod factorization), D (injectivity decision), E
(det of phi_matrix), F (Fubini swap with named branch functions),
G (perm_product_expand), H (leibniz_expand), I (factor + det_expand),
J (fin_map <-> permutation combinatorics), K (phi_term split), L
(det_expand_to_perms), M (**det_mul** -- the headline).

Next blockers for Phase 1.5 closure (Sylvester, Resultant) and Phase 2
(GCD, subresultant PRS) require porting Core.Polynomial (~3000 LOC,
draft in Core.Polynomial.fst.draft still under old FStar.CAS.Polynomial
namespace -- needs full rewrite for diamond-free tower, treated as a
separate engagement).

---
# CuteCAS `core\` — diamond-free TC tower rewrite

> This `plan.md` is the source of truth for the migration **inside `core\`**.
> The repo-wide plan still lives in
> `C:\Users\Alex\.copilot\session-state\535d71b3-…\plan.md`.
> This file tracks only the rewrite that lives under `c:\Projects\CuteCAS\core\`.

## 0. Why this folder exists

The old TC tower in `..\new\` (22 `FStar.CAS.*` modules) verifies cleanly
except for one fundamental, architectural failure:

- `FStar.CAS.Matrix.Determinant.Mul.perm_product_to_multidistrib` will not
  close. Root cause: `commutative_ring` exposes TWO syntactically distinct
  paths to its underlying `add_comm_monoid` / `has_mul` / `equatable`
  records (via `ring` directly and via `semiring` derived from `ring`).
  Both paths are propositionally equal but produce different
  `Mkrecord …` syntactic forms in postconditions. SMT does not iota-reduce
  `Mkhas_mul?.op_Star (Mkhas_mul m _) == m` across `let`-bindings; even
  top-level `compute()`-proved bridges (`perm_product_eq_pr_sr`,
  `FStar.CAS.TC.PathKit`) cannot be carried through inner `let` opacity.

This is not paperable per-lemma. The bundled-records design with multiple
parallel projections to the same atomic substructure is **broken** with
respect to F\* / Z3 record-equality, and we need a clean tower.

## 1. Design summary (locked in)

The new tower follows the discipline prototyped in
`c:\Projects\CuteCAS\Sandbox2.fst`:

1. **Bundle fields are hidden from TC search.** Every bundle field that
   stores a sub-instance is tagged `@@@FStar.Tactics.Typeclasses.no_method`,
   so the TC resolver never uses it as a projection.

2. **Forest invariant.** For each ordered class pair `(Source, Target)`
   there is **exactly one** declared `instance` of `Target` from `Source`.
   Multi-step climbs (e.g. `field → ring`) compose through the unique
   per-edge instance. Shortcut instances that duplicate a path are
   forbidden — they re-create diamonds.

3. **Marker classes take dependent params explicitly.** Classes that
   refine an existing structure with extra laws (e.g.
   `mul_is_commutative t (r: ring t)`,
   `mul_is_group t (r: ring t)`) take the underlying bundle as an
   **explicit non-instance** argument. This makes coherence unambiguous:
   `mul_is_commutative t r1` and `mul_is_commutative t r2` are
   distinguishable types when `r1 ≢ r2`, so two `commutative_ring t`
   built from different rings cannot silently coexist.

4. **Divisibility refinements form a single chain
   `integral_domain ← gcd_domain ← ufd ← euclidean_domain`.** Each
   refinement stores its **immediate parent** as a `@@@TC.no_method`
   field; the corresponding `instance` declares only the parent edge
   (`id_of_gcd`, `gcd_of_ufd`, `ufd_of_ed`). Skip-level instances
   (`id_of_ufd`, `gcd_of_ed`, `id_of_ed`) are **forbidden** — F\*
   composes them through the chain automatically, and adding them
   would re-create diamonds.

   **`field` is NOT on this chain.** The fact that every field is
   trivially a Euclidean domain (with `quot = a / b`, `rem = 0`) is
   captured by a plain function
   `field_to_euclidean_domain : field t → euclidean_domain t`, never
   an `instance`. Cross-type upgrades that produce instances on a
   different type (fraction, polynomial, quotient) are also plain
   functions: `polynomial_ed_of_field : field t → euclidean_domain
   (polynomial t)`, `field_of_fractions : integral_domain t →
   field (fraction t)`, etc. None of these are `instance`
   declarations — they would create diamonds the moment we tried to
   compose them.

   Other refinement-style classes that refine ring/integral_domain
   along different axes (`differential_ring`, future `ordered_ring`,
   …) similarly extend `integral_domain` (or `commutative_ring`,
   depending on the math) via a single dedicated chain. They do not
   intermix with the divisibility chain.

5. **No `unfold instance` on records.** F\* WHNF-inlines the body
   eagerly and breaks SMT-term equality at use sites. Plain `instance`
   only.

6. **Named top-level functions over inline lambdas.** Closures bound by
   `let` (named or anonymous) are different SMT terms even with
   identical bodies. Anything that will appear in a postcondition, an
   index of a sum, or under a tactic must be a named top-level
   definition.

## 2. Notes on the design (after Sandbox2 was finalized)

### 2.1 Equality of synthesized records across the chain

The forest only guarantees there is *one* derivation path through the
typeclass graph. It does **not** automatically guarantee that the
synthesized `commutative_ring t` produced by `cr_of_id (id_of_f f)` is
**convertible** with one produced by a user who built a
`commutative_ring t` directly. We may need a small
`cr_of_id_of_f_unfold` SMT lemma (or just rely on F\*'s structural
eta — TBD when we hit a use site).

This is a **theoretical** concern at this point; we will know if it
matters after we port `FinSum` and try to use it from a
`{| commutative_ring t |}` context.

## 3. Folder layout

```
core\
├── plan.md                  ← this file
├── AGENTS.md                ← per-folder agent instructions
├── obj\                     ← .checked cache; never wipe
└── …Core.*.fst / .fsti…     ← the rewrite, files added as work progresses
```

Top-level `.github/copilot-instructions.md` still applies; `AGENTS.md`
in this folder layers on the rewrite-specific principles.

## 4. Migration phases

Each phase ends with **all its modules verifying clean** and **at least
one stress-test lemma** demonstrating that the diamond-failure mode of
the old tower does not reproduce.

### Phase 0 — scaffolding (this commit)
- [x] Folder + obj cache.
- [x] `plan.md` (this file).
- [x] `AGENTS.md` (engineering principles + agent rules).
- [x] `Sandbox2.fst` forest fix (drop direct `field → commutative_ring`
      shortcut so the path goes uniquely via `id_of_f ∘ cr_of_id`).

### Phase 1 — foundation port
- [ ] `Core.Algebra.fst` (or `Core.Atomic` + `Core.Bundles` split if it
      grows past ~600 LOC) — port the verified Sandbox2 tower minus the
      diamond fix from §2.1. Add `nat`/`int` ring/field-free
      instances later only as needed for tests.
- [ ] Stress test: a generic lemma in a `{| commutative_ring t |}`
      context that uses both `+` (resolved via add_comm_group) and `*`
      (resolved via ring) and one law from `mul_is_commutative`. Must
      verify without any explicit `#`-instance annotations.

### Phase 2 — sums and permutations
- [ ] `Core.FinSum` (analogue of `FStar.CAS.FinSum`) — sums indexed by
      `Fin n`, parameterized by `{| add_comm_group t |}`.
- [ ] Stress test: `fin_sum_congruence` callable from a
      `{| commutative_ring t |}` site without `#`-slop. This is the
      exact pattern that broke in the old tower.
- [ ] `Core.Permutation`, `Core.Permutation.Enum`,
      `Core.Permutation.Sum`.

### Phase 3 — matrices
- [ ] `Core.Matrix` (basics, transpose).
- [ ] `Core.Matrix.Ring` (the matrix ring on `n × n`).
- [ ] `Core.Matrix.MultiDistrib` (the multi-distributivity machinery).

### Phase 4 — determinant + the previously stuck lemma
- [ ] `Core.Matrix.Determinant` (Leibniz, multilinearity, alternating,
      transpose, Laplace, det of product).
- [ ] `Core.Matrix.Determinant.Mul` — including
      `perm_product_to_multidistrib`, which is **the acceptance test**
      for the new architecture. If this verifies cleanly, the design
      is validated end-to-end.
- [ ] `Core.Matrix.Sylvester`, `Core.Matrix.Resultant`.

### Phase 5 — refinement classes & polynomial machinery
- [ ] `euclidean_domain`, `gcd_domain`, `ufd` — all extending
      `integral_domain` only (per §1.4). No `field → ED` chain.
- [ ] `Core.Polynomial` — univariate polynomial ring.
- [ ] `Core.Polynomial.Euclidean` — divmod over a field.
- [ ] `Core.Polynomial.GCD` — GCD, Bézout, Euclid's lemma.
- [ ] `polynomial_ed_of_field : field t → euclidean_domain (polynomial t)`
      as a plain function (not an `instance`).

### Phase 6 — fractions
- [ ] `Core.Fractions` — `field_of_fractions : integral_domain t →
      field (fraction t)` as a plain function.

### Phase 7 — differential layer
- [ ] `differential_ring`, `differential_field` — Leibniz-rule based
      derivation classes.
- [ ] Standard derivations on `polynomial K` and `fraction (polynomial K)`.

### Phase 8 — Risch (purely transcendental case)
- [ ] Tower-of-extensions representation.
- [ ] Hermite reduction.
- [ ] Lazard–Rioboo–Trager (LRT) algorithm.
- [ ] Soundness theorem.
- [ ] Liouville (completeness) for the rational case.
- Long-term endpoint of the project.

## 5. Stress-test acceptance gates

Each gate is a single lemma. If it verifies clean **without** explicit
`#`-instance arguments and **without** any `assume`/`admit`, the
corresponding phase is green.

| Gate ID | Phase | Lemma sketch                                              |
|---------|-------|-----------------------------------------------------------|
| G1      | 1     | `(a + b) * c = a*c + b*c` in `{| commutative_ring t |}`   |
| G2      | 2     | `fin_sum f + fin_sum g = fin_sum (fun i. f i + g i)` from `commutative_ring` |
| G3      | 4     | `det_eq_fin_sum_transpose` from `{| commutative_ring t |}` |
| G4      | 4     | `perm_product_to_multidistrib` — **the** acceptance test  |
| G5      | 5     | `gcd_divides_first`, `gcd_is_maximal` from `{| euclidean_domain t |}` |

## 6. Estimates

- Phase 0: this commit.
- Phase 1: ~300 LOC; 1 session.
- Phase 2: ~600 LOC; 1–2 sessions.
- Phase 3: ~1.2k LOC; 2 sessions.
- Phase 4: ~3k LOC; 3–5 sessions (G4 is the big risk).
- Phase 5: ~3k LOC; 3–4 sessions.
- Phase 6: ~1.5k LOC; 1–2 sessions.
- Phase 7: ~500 LOC; 1 session.
- Phase 8: open-ended; the Risch project itself.

**Foundational rewrite total (Phases 0–4):** ~5k LOC and ~7–10 sessions
to the G4 acceptance gate. Past G4 we are doing **new work**, not a
rewrite.

## 7. What we keep / drop from `..\new\`

- **Keep as reference**: `..\new\` will remain in the repo as the
  reference implementation of every algorithm. Proof skeletons,
  comments, and lemma statements port over almost unchanged.
- **Drop**: `..\new\FStar.CAS.TC.PathKit.fst` (the path-bridge module).
  In the new tower there are no paths to bridge.
- **Drop**: every `unfold instance` declaration in `..\new\`. Plain
  `instance` only in `core\`.
- **Drop**: every `assume` / `admit` (already enforced in `..\new\`; the
  rule continues).

## 8. Current standing (2026-05-24, divmod **structural** correctness landed)

- ✅ Phase 0 scaffolding.
- ✅ Phase 1 foundation (`Core.Algebra`, `Helpers`, `Notation`, `Int`).
- ✅ Phase 2 sums & permutations (`Core.FinSum`, `Core.Permutation*`).
- ✅ Phase 3 matrices (`Core.Matrix`, `.Ring`, `.MultiDistrib`).
- ✅ **Phase 1.5 (canonicalization tactics)** — `Core.Tactics.CanonRing`
      + `Core.Tactics.CanonCommGroup` working with full meta-tactics.
- ✅ **Phase 4 Determinant** — `Core.Matrix.Determinant.fst` (~3900 LOC).
- ✅ **Phase 4 Det.Mul** — `Core.Matrix.Determinant.Mul.fst`
      (1390 LOC). Cauchy–Binet `det (A * B) = det A * det B` verified.
      **G4 acceptance gate passed.**
- ✅ **Public-signature hygiene (H3+H4+H5)** — all `.fsti` files clean.
- ✅ **Phase 1.5 closure** — `Core.Matrix.Sylvester` (171 LOC,
      8 lookup lemmas).
- ✅ **Phase 6 — fractions** — `Core.Fractions` (900 LOC) building
      `field_of_fractions : integral_domain t → field (fraction t)`.
- ✅ **Phase 5 — polynomial machinery:**
   - `Core.Polynomial` — additive layer (387 / 160 LOC fst/fsti).
   - `Core.Polynomial.Mul` — multiplication + `commutative_ring`
      instance + eval ring-homomorphism + degree well-definedness.
      **Public surface now exposes the ring axioms** (`poly_mul_commutative`,
      `poly_mul_associative`, `poly_mul_right_distrib`,
      `poly_mul_left_distrib`) so downstream proofs can chain through
      them without going via the `polynomial_commutative_ring` instance.
   - `Core.Polynomial.Div` — `monomial`, `poly_sub` (+ compute reveal),
      `leading_coeff_nonzero`, `poly_divmod` operational + **structural
      correctness theorem** `poly_divmod_correct`:
      `poly_eq p (poly_add (poly_mul q quot) rem)` (no admits).
      Proof skeleton: 3 helpers (`poly_mul_nil_right`,
      `divmod_base_case`, `add_sub_cancel`), one big `inductive_step`
      lemma chaining 7 ring-axiom rewrites, then induction on fuel.
- ✅ **Phase 5 refinement chain** — `Core.Algebra.Divisibility`:
      `gcd_domain` / `ufd` / `euclidean_domain` classes with full
      axioms; three linear-chain projection instances
      (`id_of_gcdd`, `gcdd_of_ufd`, `ufd_of_ed`); `divides` predicate
      + `divides_refl` + `divides_trans`.
- ✅ **Resultant module** — `Core.Matrix.Resultant`:
      `resultant m n p q := det (sylvester_matrix m n p q)` +
      vanishing lemma `resultant_zero_when_p_all_zero`.
- ✅ **Build infrastructure** — `core\build-all.ps1` builds 31
      modules in correct topological order; zero Warning-247.

**Acceptance gates status:**
- G1 (ring distrib): ✅
- G2 (fin_sum from commutative_ring): ✅
- G3 (det_eq_fin_sum_transpose): ✅
- G4 (perm_product_to_multidistrib): ✅
- G5 (euclidean_domain): chain classes ✅ defined; structural
      correctness of divmod ✅ proven; first non-trivial ED instance
      (polynomial-over-field) **pending** the degree-of-remainder bound
      and polynomial integral-domain instance.

### Concrete pending work (Phase 5 closure)

In dependency order — each is its own focused work session:

1. **Degree bound on remainder** (`Core.Polynomial.Div`):
   - `degree rem = None \/ Some?.v (degree rem) < Some?.v (degree q)`
     for `(quot, rem) = poly_divmod p q` (with `q` nonzero).
   - **Foundation lemmas now landed (2026-05-24+):**
     - `coeff_at_above_length`, `degree_lt_length`, `coeff_at_all_zero`,
       `coeff_at_above_degree`, `coeff_at_poly_add`, `coeff_at_poly_neg`
       (all in `Core.Polynomial.Mul.fst`, exposed in `.fsti`).
     - `coeff_at_poly_sub`, `degree_of_monomial`, `coeff_at_monomial`
       (in `Core.Polynomial.Div.fst`).
     - `coeff_at_scalar_mul`, `coeff_at_poly_mul_step` (recursive
       convolution step; in `Core.Polynomial.Mul.fst`).
     - `coeff_at_monomial_mul` (in `Core.Polynomial.Div.fst`):
       `coeff_at (poly_mul (monomial c k) q) (k+j) = c * coeff_at q j`.
     - `cancellation_at` (in `Core.Polynomial.Div.fst`): the key
       algebraic identity — when `c * coeff_at q n = coeff_at p m`,
       the `m`-coefficient of `poly_sub p (poly_mul (monomial c (m-n)) q)`
       vanishes.
     - `coeff_at_monomial_mul_above` (Div.fst): above the leading
       position the monomial-product vanishes.
     - `residue_zero_above` (Div.fst): combining the above, the residue
       `p - mono*q` has every coefficient at position `i > m` equal to
       zero (mod the equatable). Together with `cancellation_at`, this
       gives a residue whose degree is either `None` or `< m`.
     - `degree_decreases` (Div.fst): if `∀ i. i >= k ==> coeff p i = zero`,
       then degree p is None or < k.
     - `divmod_step_degree_decreases` (Div.fst): one divmod step yields a
       residue with degree < m, given the cancellation hypothesis.
     - `lc_cancel_field` (Div.fst): `(x * inv y) * y = x` over a field.
     - `poly_divmod_fuel_degree` (Div.fst): induction on fuel showing
       that with `fuel > degree p`, the resulting remainder has
       `None? (degree rem) \/ degree rem < degree q`.
     - **`poly_divmod_correct_degree`** (Div.fsti + Div.fst): the final
       top-level wrapper. ✅ Done — the full degree-bound theorem is
       proven end-to-end with no admits.

2. **`polynomial` over `integral_domain` integral-domain instance**: ✅ **DONE**
   - `Core.Polynomial.Domain.fst` (~330 LOC):
     - `coeff_at_poly_mul_above`, `coeff_at_poly_mul_top`, `degree_mul`
       (the headline `degree (p ⋅ q) = degree p + degree q` over an ID).
     - `polynomial_domain_law` (forward via `degree_mul`, backward via
       `poly_mul_left_all_zero` + commutativity).
     - `polynomial_domain` and `polynomial_integral_domain` instances.
   - Required reveal-SMTPats added to `Core.Polynomial.Mul.fsti`:
     `polynomial_ring_mul_reveal`, `polynomial_ring_add_reveal`,
     `polynomial_ring_one_reveal`, `poly_one_reveal`; and
     `polynomial_acg_zero_reveal` in `Core.Polynomial.fsti`. Without
     these, the lambda inside the `domain`/`integral_domain` record
     literal cannot bridge `Core.Algebra.eq/mul/zero` against
     `poly_eq/poly_mul/[]` (typeclass projections aren't iota-reduced
     by SMT). With them, no tactics, no `assert_norm` — just the
     reveals + the helper lemma.

3. **Plain function `field_to_ed : field t → euclidean_domain t`**:
   - Trivial gcd (0/1), trivial divmod (a⋅inv(b), 0).
   - Mostly bridging field equatable with cr equatable inside the
     gcd_domain record fields. ~150 LOC.

4. **Plain function `polynomial_ed_of_field`**:
   - Combines #1, #2, #3. Returns full ED structure for polynomial
     over a field. **Closes G5.**

5. **Polynomial GCD + Bézout** (`Core.Polynomial.GCD`, new module):
   - Extended Euclidean algorithm on polynomials over a field.
   - Required for Risch (Phase 8) Hermite reduction.

6. **Resultant deeper theory**:
   - `resultant_swap_sign`: `res(p, q) = (-1)^(m⋅n) ⋅ res(q, p)`.
   - `resultant_multiplicative`: `res(p, q⋅r) = res(p, q) ⋅ res(p, r)`.
   - Building blocks for `resultant = 0 ⇔ common factor`.

### Subsequent phases

- ⏳ **Phase 7 — differential layer** — `differential_ring`,
      `differential_field`, standard derivations on
      `polynomial K` and `fraction (polynomial K)`. Depends on #2/#4.

- ⏳ **Phase 8 — Risch (purely transcendental case)** — tower
      representation, Hermite reduction, LRT algorithm, soundness +
      Liouville completeness.

---

**Last updated:** 2026-05-24 (SMTPat reveal lemmas stripped; polynomial_ring/acg/
equatable/commutative_ring/domain converted from `instance` to plain `let`.
Only `polynomial_integral_domain` remains a top-level TC instance — matching
the Fractions pattern. Reveal lemmas kept as plain `val` (callers invoke
explicitly when bridging abstract record projections to underlying `poly_*`
operators).

