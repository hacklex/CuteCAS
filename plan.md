# CuteCAS plan — current state (2026-06-01)

> **READ FIRST.** This top section is the source of truth and supersedes
> every entry beneath it. The "Milestone archive" at the bottom keeps the
> historical narrative for context, but where it disagrees with this
> section, this section wins. Engineering rules live in `AGENTS.md`
> (design/forest invariant + workflow) and `.github/copilot-instructions.md`
> (repo-wide non-negotiables: CRLF, **never write to git / never risk data
> loss**, no `admit`/`assume` in committed code, resource budget).

## 0. Status at a glance

- **60 modules** (44 `.fst` + 16 `.fsti`), **all verify clean from the
  cache, zero `admit()`, zero `assume`.** (The only `admit`/`assume`
  textual hits are two *comments* in `Core.Polynomial.Irreducible.fst`.)
- **Build / reverify:** `.\build-all.ps1` (regenerated 2026-06-01 with the
  full topological order; `-KeepGoing` to collect all failures, sequential
  per the resource rules). Toolchain: **F\* 2026.05.10** at `C:\FStar`,
  Z3, run with `--include . --cache_checked_modules --cache_dir obj`.
- **This session (2026-06-01) did:** full-tree reverify; **found + fixed one
  regression** — `Core.Fractions.fst` `fr_mig` passed the ring to
  `mul_is_group` positionally instead of as the instance-implicit `#(…)`
  (skewfield⇒domain refactor fallout); regenerated the missing
  `build-all.ps1`; removed dead scratch (`Scratch*.fst`) and stale refactor
  logs; refreshed this plan. Then **proved Hermite soundness** end-to-end —
  single step (`hermite_step_correct` + `normalize_bezout_correct`) lifted
  through the recursion to full reduction (`hermite_reduce_power_correct`) —
  and **completed the LRT resultant** (`res_x` over `k[z]`). Tree stays
  60/60 green, zero admits/assumes.

## 1. Layout & where the rules live

- **Flat repo.** All `Core.*.{fst,fsti}` at the repo root.
- **`AGENTS.md`** — the forest/TC design invariant (one instance per edge,
  `@@@no_method` bundle fields, marker classes, no `unfold instance`,
  **no lambdas in signatures**, public-signature hygiene, sliding-`admit`
  debugging, resource budget, agent escalation cap).
- **`.github/copilot-instructions.md`** — CRLF everywhere; **§2 never write
  to git, §1.5 never risk data loss** (two 2000+ LOC files were destroyed
  by past agents mishandling shell scripts — this is why both rules are
  absolute); no `admit`/`assume`; default limits (no `#push-options`).
- **`legacy/AlgebraTypes.fst`** — old monolithic types, reference only, not
  on the include path.
- **`C:\Projects\cutecas-backup\`** (external) — pre-cleanup snapshot of the
  retired `FStar.CAS.*` tower. Kept for reference (it still holds modules
  with no `Core.*` equivalent: `Modules`, `Grouplikes`, `Multiplicative`,
  `Function.Enum`). Delete only on explicit owner instruction.

## 2. Verified foundation (proven, admit-free)

| Area | Modules | Notes |
|---|---|---|
| Typeclass tower | `Core.Algebra` (+ `.Notation`, `.Int`, `.Helpers`, `.Combinators`, `.Divisibility`, `.Test`, `.NotationTest`) | diamond-free forest; `field → skewfield → domain → ring` edges; divisibility chain `integral_domain ← gcd_domain ← ufd ← euclidean_domain` |
| Canon tactics | `Core.Tactics.CanonRing`, `Core.Tactics.CanonCommGroup` | reflective ring / comm-group canonicalizers |
| Sums & perms | `Core.FinSum`, `Core.Permutation` (+ `.Enum`, `.Sum`), `Core.Vector` | |
| Matrices | `Core.Matrix` (+ `.Ring`, `.MultiDistrib`, `.Determinant`, `.Determinant.Mul`, `.Adjugate`, `.KernelDet`, `.NullVec`, `.Sylvester`, `.Resultant`) | **Cauchy–Binet `det_mul` (G4)** proven; adjugate; `null_vec_implies_det_zero`; Sylvester + `resultant`; `syl_null_vec_is_null` |
| Fractions | `Core.Fractions` | `field_of_fractions : integral_domain t → field (fraction t)` |
| Polynomials | `Core.Polynomial` (+ `.Coeff`, `.Div`, `.GCD`, `.Derivative`, `.SquareFree`, `.Unique`, `.PPInvariant`, `.Factorization`, `.Irreducible`, `.Tests`) | ring/ID, Euclidean `divmod` + correctness + degree bound, GCD (+ Bézout/`ext_gcd`, congruence), **Yun square-free**, derivative, factorization machinery |
| Algebraic constants | `Core.AlgebraicConstant` | ℚ[c]/R(c) layer |
| Differential substrate | `Core.Derivation` | `derivation_on` record (additivity, Leibniz, congruence) + derived `deriv_{zero,neg,one,sub}` + `poly_derivation` |

## 3. Risch frontier (Phases 3–4): implemented but **soundness UNPROVEN**

These six modules typecheck (every signature is `ensures fun _ -> True`)
but prove **no** correctness. They are the entire remaining body of work
for the headline "verified ℚ(x) integrator" goal.

- **`Core.RationalDeriv`** — `rational_deriv` = quotient rule
  `D(p/q) = (p'q − pq')/q²` on `fraction(polynomial t)`. Proven supports:
  `rational_deriv_reveal`, `den_squared_nonzero`, `poly_to_rational`.
  **Deferred:** `D(p/1) ~ poly_deriv p / 1` compatibility (comment only).
- **`Core.Polynomial.PartialFraction`** — `normalize_bezout` +
  `partial_fraction_two` (two-factor PF via `ext_gcd`). ✅ **`normalize_bezout_correct`
  proven** (2026-06-01): the returned `(s,t)` satisfy `s·d1 + t·d2 ≡ 1`.
- **`Core.Risch.Hermite`** — `hermite_step` + `hermite_reduce_power` compute
  the reduction `∫A/Dⁿ = G/Dⁿ⁻¹ + ∫C/Dⁿ⁻¹`. ✅ **Full-reduction soundness
  proven** (2026-06-01): `hermite_step_correct` (single step,
  `A ≡ G'·D − (n−1)·G·D' + C·D`) lifted through the recursion to
  **`hermite_reduce_power_correct`** — combining the rational parts into the
  numerator `N = combined_num parts D` over `D^(n-1)`, it proves the
  cleared-denominator identity `A ≡ N'·D − (n−1)·N·D' + final·D^(n-1)` by
  induction on `n` (helpers `g_deriv_general`, `hermite_algebra`,
  `scalar_poly_succ`, `reduce_pure`).
- **`Core.Risch.LRT`** — ✅ **resultant computation completed** (2026-06-01):
  `lrt_resultant_raw` now returns the real `res_x(p − z·q', q) ∈ k[z]` via
  `Core.Matrix.Resultant.resultant` instantiated at the coefficient ring
  `polynomial t` (no manual bridge needed — `resultant` builds the Sylvester
  matrix internally); `lrt` stores it in `root_sum.rs_resultant`.
  ✅ **Structural residue soundness proven** (2026-06-01):
  `lrt_log_argument_divides_q` and `lrt_log_argument_divides_residue` — each
  log-argument `v_c = gcd(p−c·q', q)` is a genuine factor of `q` and satisfies
  the residue condition `v_c | (p−c·q')` (from the GCD divisibility axioms).
  **Still blocked:** the full derivative identity
  `d/dx[Σ cᵢ·log vᵢ] = p/q` (sum over the roots `cᵢ` of `R`) — needs the
  splitting field of `R` and resultant specialization (see §5).
- **`Core.Risch.Rational`** — `integrate_rational_single_factor` orchestrates
  `poly_antideriv` + Hermite + LRT for the single-squarefree-factor case.
  No end-to-end soundness yet.

## 4. Phase roadmap

| Phase | Scope | Status |
|---|---|---|
| 0–1 | Typeclass tower + canon tactics | ✅ done |
| 1.5 | Perms, det, Cauchy–Binet, adjugate, Sylvester, resultant, kernel/null-vec | ✅ done |
| 1.75 | Algebraic constants ℚ[c]/R(c) (ring + **field** at irreducible `r`) | ✅ `Core.AlgebraicConstant` (+ `.Field`) |
| 2a | Euclidean division (+ correctness + degree bound) | ✅ `Core.Polynomial.Div` |
| 2b | Polynomial GCD + Bézout | ✅ `Core.Polynomial.GCD` |
| 2c | Square-free factorization (Yun) | ✅ `Core.Polynomial.SquareFree` |
| 2d | Resultant ⇔ common factor | ✅ `Core.Matrix.Resultant` + `KernelDet`/`NullVec` |
| 3 | Rational functions + derivations | 🟡 substrate done (`Derivation`, `RationalDeriv`, `PartialFraction`); abstract soundness statement not yet built |
| 4 | Risch for ℚ(x): Hermite + LRT | 🟡 Hermite full-reduction soundness ✅; LRT resultant computation ✅; **LRT soundness still pending** |
| 5.0 | Factorization in ℚ[x] (for completeness) | 🟡 `Factorization`/`Irreducible` present (verify clean) |
| 5 | Liouville completeness for rationals | ⏳ not started |
| 6 | Tower extensions (exp/log layers) | ⏳ stretch |

## 5. What's next — pursuing the ℚ executable integrator + proof

> See **`current-blockers.md`** for the full corrected analysis (ℚ
> specialization, primitive-element tower collapse, the Mignotte→Lagrange
> factor-bound correction, and why the executable never needs ℝ/ℂ).

Hermite full-reduction soundness and the LRT resultant computation are done
(2026-06-01). Decision (2026-06-01): pursue **both** the executable LRT
integrator and its proof over **ℚ**, slowly — no timeline. Dependency order:

1. **Full LRT soundness** (`d/dx[Σ cᵢ·log vᵢ] = p/q`). Structural residue
   soundness is done; the derivative identity is **blocked on missing
   foundations**, in dependency order:
   a. ✅ **DONE** — **`poly_eval` as a ring homomorphism** `polynomial t → t`
      (`Core.Polynomial.Eval.fst`: eval_zero/one/add/neg/mul/congruence). Also
      spun off `Core.FinSum.Convolution.sum_range_convolution` (Cauchy product).
   b. **Determinant specialization**: `det` commutes with a ring hom applied
      entrywise, giving **resultant specialization** `R(c) = res_x(p−c·q', q)`.
      Combined with the proven `resultant_zero_of_common_divisor` (and a
      converse), this yields the base-field Rothstein–Trager criterion
      `R(c)=0 ⟺ deg(gcd(p−c·q', q)) ≥ 1`.
   c. **Soundness over a given splitting field (ℚ, char 0)**:
      ✅ **DONE (2026-06-02)** — `Core.AlgebraicConstant` (CR-only) is upgraded
      to a **field** at an irreducible factor:
      `Core.AlgebraicConstant.Field.algebraic_field : field (algebraic t r)`
      for `poly_irreducible r` (inverse via Bézout/`ext_gcd`; no `admit`/`assume`).
      By the **primitive element theorem** the splitting field is a *single*
      extension `ℚ(θ)` (no type-changing tower). **Remaining:**
      **resultant=∏-over-roots → partial fractions → RT correspondence →
      assembly** gives the derivative identity *relative to* a provided `ℚ(θ)`.
      Companion prereq B (root theory — factor theorem, squarefree ⟹ `q'(α)≠0`)
      is ✅ **DONE (2026-06-02)**: `Core.Polynomial.Root`
      (`factor_theorem`, `squarefree_root_deriv_nonzero`).
   d. **Construction (makes it executable)**: 𝔽_p → Berlekamp → Hensel →
      recombination with the **Lagrange/Kronecker** coefficient bound (NOT
      Mignotte — keeps it ℂ-free) ⇒ factorization over ℚ ⇒ `ℚ(θ)`. Large but
      **finite, not research-frontier**.
2. **Phase-3 abstraction.** Build `differential_field (fraction (poly K))`
   (and finish the `rational_deriv ↔ poly_deriv` compatibility) so soundness
   can be *stated* abstractly as `D(integrate p q) = p/q` instead of ad hoc
   per algorithm — the umbrella that connects the proven Hermite/LRT pieces.

## 6. Acceptance gates (see `AGENTS.md` §5)

G1 ring distrib ✅ · G2 `fin_sum` from `commutative_ring` ✅ ·
G3 `det_eq_fin_sum_transpose` ✅ · G4 `perm_product_to_multidistrib`
(Cauchy–Binet) ✅ · G5 `euclidean_domain` chain ✅ (polynomial-over-field
ED structure available; classes + GCD/divmod correctness proven).

## 7. Known doc/code drifts (found 2026-06-01)

- **`AGENTS.md` §1.3** says marker classes take their base as an *explicit*
  dependent param `(r: ring t)`, but the live code uses instance-implicit
  `{| r: ring t |}` (e.g. `mul_is_group`, `mul_is_commutative`). The `#(…)`
  call convention follows from the actual code. Reconcile the doc or the
  code when convenient (this is what bit `fr_mig`).
- **`.github/copilot-instructions.md` §8** points at a Copilot
  `session-state/<id>/plan.md`; the live plan is this file. Treat this file
  as authoritative.

---

## Milestone archive (compact, newest first)

- **2026-06-01 (proofs)** — Hermite soundness proven end-to-end:
  `hermite_step_correct` (single step, `A ≡ G'·D − (n−1)·G·D' + C·D`) via
  `g_deriv_general` + the abstract `hermite_algebra` cancellation (canon_ring)
  + `normalize_bezout_correct` (Bézout `≡ 1`); then lifted through the
  recursion to `hermite_reduce_power_correct`
  (`A ≡ N'·D − (n−1)·N·D' + final·D^(n-1)`, `N = combined_num parts D`) by
  induction, using `scalar_poly_succ` and the `reduce_pure` ring identity.
  LRT resultant completed:
  `lrt_resultant_raw` now computes `res_x(p − z·q', q) ∈ k[z]` through
  `Core.Matrix.Resultant.resultant` at coefficient ring `polynomial t`;
  `LRT → Resultant` build edge added and `build-all.ps1` reordered.
- **2026-06-01 (hygiene)** — Matrix theorems (det/adj/resultant), Yun's
  algorithm, skewfield⇒domain refactor, FinSum/Adjugate utilities; algebraic
  constants; vectors+matrices; polynomial `D/dx`, `divmod`, GCD.
  Risch/derivation skeleton modules added. Reverified the tree (60/60),
  fixed the `Fractions` regression, rebuilt `build-all.ps1`, cleaned scratch.
- **2026-05-27** — flat-repo cleanup; polynomial UFD + Euclidean-division
  tower; monic-normalization scaffold.
- **2026-05-25** — polynomial UFD landed (GCD congruence via structural
  induction); `polynomial_gcd_domain`; monic-normalization scaffold.
- **2026-05-24** — GCD divisibility core; divmod structural correctness +
  remainder degree bound; `polynomial_integral_domain` instance.
- **2026-05-23** — 4-agent perf/hygiene audit; `z3rlimit`/fuel reductions;
  public-signature hygiene refactor (H3+H4+H5) complete across the tower.
- **2026-05-22** — foundation port (Algebra, FinSum, Permutation, Matrix.*),
  canon tactics, **`det_mul` / Cauchy–Binet verified (G4 passed)** —
  validated the diamond-free forest architecture end-to-end; polynomial
  multiplication ring tower.

> Older rationale (why the forest rewrite exists, the original migration
> phases, the pointwise-combinator decision, the lambda-in-postcondition
> survey) is preserved in git history and distilled into `AGENTS.md`.
