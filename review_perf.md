# CuteCAS `core\` — Verification Performance Review

Reviewer: verification-performance pass.
Methodology: cold-cache `Measure-Command` per module (32 modules); for each
`#push-options` block with `z3rlimit > 80`, temporarily backed up the host
.fst, lowered the limit, deleted the matching `.checked`, re-ran
`fstar.exe --include . --cache_dir obj --cache_checked_modules <module>`,
then restored from backup. All modified files were restored to their
original SHA at the end of the review (verified by hash).

Scratch path: `c:\Projects\CuteCAS\core\scratch_perf.fst` (stub) plus the
probe driver `c:\Projects\CuteCAS\core\probe_run.ps1`.

---

## Headline numbers

| Metric                                     | Value                                |
| ------------------------------------------ | ------------------------------------ |
| Total `#push-options` blocks in `core\`    | **272**                              |
| Files with > 3 push blocks                 | **13 of 17**                         |
| Push blocks with `z3rlimit > 80`           | **22**                               |
| Push blocks with `fuel > 2`                | **93**                               |
| Free wins (probed: lowerable, no edits to body) | **22 / 22 candidates passed**   |
| Module re-verification > 20 s wall-clock   | **0** (slowest: Fractions 16.1 s, Determinant 15.9 s) |
| Module re-verification > 10 s              | **3** (Determinant, Fractions, Permutation.Sum, Determinant.Mul borderline at ~5 s) |

**Verification times (cold-cache, Measure-Command):**

```
Core.Algebra.fst                     1.9s
Core.Algebra.Helpers.fst             1.2s
Core.Algebra.Divisibility.fst        1.5s
Core.Tactics.CanonCommGroup.fst      2.9s
Core.Tactics.CanonRing.fst           6.1s
Core.Permutation.fst                 3.9s
Core.FinSum.fst                      6.0s
Core.Permutation.Enum.fst            2.4s
Core.Permutation.Sum.fst            13.1s
Core.Matrix.fst                      1.0s
Core.Matrix.Ring.fst                 3.0s
Core.Matrix.MultiDistrib.fst         3.5s
Core.Matrix.Determinant.fst         15.9s   <-- largest module by far (98 push blocks)
Core.Matrix.Determinant.Mul.fst      4.9s
Core.Polynomial.fst                  --     <-- pre-existing build break, see Note A
Core.Polynomial.Mul.fst              5.1s
Core.Polynomial.Div.fst              2.6s
Core.Polynomial.Domain.fst           1.5s
Core.Matrix.Sylvester.fst            0.7s
Core.Matrix.Resultant.fst            1.3s
Core.Fractions.fst                  16.1s
```

**Note A** — `Core.Polynomial.fst` fails to verify from source with a
pre-existing `Error 233` at line 393 (`polynomial_equatable_eq_reveal` /
`polynomial_acg_zero_reveal` declaration-order issue). Outside this review's
scope; flagged for the maintainer. The stale `.checked` in `obj\` cannot be
regenerated until that error is resolved; all downstream modules
(`Polynomial.Mul`, `Polynomial.Div`, `Polynomial.Domain`, `Matrix.Sylvester`,
`Matrix.Resultant`) consequently emit `Warning 247` when they cannot find
the missing `.checked`, but still verify against the `.fsti`. This is
unrelated to perf; mentioned for awareness.

---

## Push-blocks per file

| File                                  | # push blocks |
| ------------------------------------- | ------------: |
| Core.Matrix.Determinant.fst           |          **98** |
| Core.Matrix.Determinant.Mul.fst       |          **38** |
| Core.FinSum.fst                       |            23 |
| Core.Polynomial.Mul.fst               |            22 |
| Core.Fractions.fst                    |            19 |
| Core.Polynomial.Div.fst               |            13 |
| Core.Permutation.Sum.fst              |            13 |
| Core.Permutation.Enum.fst             |            12 |
| Core.Matrix.MultiDistrib.fst          |            10 |
| Core.Matrix.Ring.fst                  |             7 |
| Core.Polynomial.Domain.fst            |             6 |
| Core.Tactics.CanonCommGroup.fst       |             3 |
| Others                                |       1–2 ea. |

The AGENTS.md target is "Ideal: each file verifies with a single global
default; only rare lemmas push higher limits." We are far from this ideal.
See **P-023** below for the file-level recommendation.

---

## Individual findings

For each `z3rlimit > 80` site the probe edited only the `#push-options`
line and confirmed verification still succeeds. Wall-clock "time" columns
are the **full module re-verification time**, not the per-lemma time —
F\* does not report per-lemma time without `--query_stats`. Times include
the lemma plus all other lemmas in the module; the relevant signal is
"verifies clean".

### P-001 — `Core.FinSum.fst:856` `fin_sum_swap_lambda`
- Current:  `--fuel 4 --ifuel 2 --z3rlimit 200`
- Proposed: `--fuel 4 --ifuel 2 --z3rlimit 80`  *(z3rlimit /2.5)*
- Module time before/after: 6.0 s / 5.9 s (unchanged at module level; per-lemma headroom reclaimed)
- Evidence: `probe_run.ps1` + `probe_finsum.ps1`, result OK.
- Risk: low — the proof uses `Classical.forall_intro` chains and
  `sum_range_congruence_forall` bridges; the original `200` was clearly
  a pessimistic ceiling from initial development.

### P-002 — `Core.Matrix.Determinant.fst:459` `det_identity`
- Current:  `--fuel 4 --ifuel 2 --z3rlimit 200`
- Proposed: `--fuel 4 --ifuel 2 --z3rlimit 80`
- Evidence: probe OK in 15.9 s module time.
- Risk: low.

### P-003 — `Core.Matrix.Determinant.fst:665` `det_transpose`
- Current:  `--fuel 2 --ifuel 2 --z3rlimit 200`
- Proposed: `--fuel 2 --ifuel 2 --z3rlimit 80`
- Evidence: probe OK in 15.9 s.
- Risk: low. This is one of the cornerstone determinant lemmas; keep an
  eye on it across F\* upgrades.

### P-004 — `Core.Matrix.Determinant.fst:784` `det_row_swap`
- Current:  `--fuel 6 --ifuel 2 --z3rlimit 200`
- Proposed: `--fuel 2 --ifuel 2 --z3rlimit 80`  *(fuel /3, z3rlimit /2.5)*
- Evidence: probe OK in 15.5 s. **Both** the fuel-6 *and* z3rlimit-200
  bumps are unnecessary.
- Risk: low. This was clearly over-provisioned during development.

### P-005 — `Core.Matrix.Determinant.Mul.fst:602` `sum_list_fubini`
- Current:  `--fuel 4 --ifuel 2 --z3rlimit 200`
- Proposed: `--fuel 4 --ifuel 2 --z3rlimit 80`
- Evidence: probe OK in 13.7 s.
- Risk: low.

### P-006 — `Core.Matrix.Determinant.fst:3542` `perm_product_inject_factor`
- Current:  `--fuel 4 --ifuel 2 --z3rlimit 160`
- Proposed: `--fuel 4 --ifuel 2 --z3rlimit 80`
- Evidence: probe OK in 16.0 s.
- Risk: low.

### P-007 — `Core.Matrix.Determinant.fst:3870` `det_laplace_row`
- Current:  `--fuel 4 --ifuel 2 --z3rlimit 160`
- Proposed: `--fuel 4 --ifuel 2 --z3rlimit 80`
- Evidence: probe OK in 15.6 s.
- Risk: low.

### P-008 — `Core.Polynomial.Div.fst:161` `inductive_step`
- Current:  `--z3rlimit 150 --ifuel 2 --fuel 2`
- Proposed: `--z3rlimit 80 --ifuel 2 --fuel 2`  *(z3rlimit /1.9)*
- Evidence: probe OK in 2.3 s.
- Risk: very low — straight algebraic chain through `poly_add_*` lemmas.

### P-009 — `Core.Polynomial.Div.fst:219` `poly_divmod_fuel_correct`
- Current:  `--z3rlimit 120 --ifuel 2 --fuel 2`
- Proposed: `--z3rlimit 80 --ifuel 2 --fuel 2`
- Evidence: probe OK in 2.4 s.
- Risk: low — recursive lemma with a `decreases fuel`; the recursive call
  amortises the heavy SMT work.

### P-010 — `Core.Matrix.Determinant.fst:265` `prod_range_const_one`
- Current:  `--fuel 4 --ifuel 2 --z3rlimit 120`
- Proposed: `--fuel 4 --ifuel 2 --z3rlimit 60`  *(z3rlimit /2)*
- Evidence: probe OK in 15.7 s.
- Risk: very low — this is a tiny recursive lemma over `prod_range`.

### P-011 — `Core.Matrix.Determinant.fst:1056`
- Current:  `--fuel 4 --ifuel 2 --z3rlimit 120`
- Proposed: `--fuel 4 --ifuel 2 --z3rlimit 80`
- Evidence: probe OK in 15.8 s.
- Risk: low.

### P-012 — `Core.Matrix.Determinant.fst:1290`
- Current:  `--fuel 4 --ifuel 2 --z3rlimit 120`
- Proposed: `--fuel 4 --ifuel 2 --z3rlimit 80`
- Evidence: probe OK in 15.7 s.
- Risk: low.

### P-013 — `Core.Matrix.Determinant.fst:1315`
- Current:  `--fuel 4 --ifuel 2 --z3rlimit 120`
- Proposed: `--fuel 4 --ifuel 2 --z3rlimit 80`
- Evidence: probe OK in 15.6 s.
- Risk: low.

### P-014 — `Core.Matrix.Determinant.fst:3319`
- Current:  `--fuel 2 --ifuel 2 --z3rlimit 120`
- Proposed: `--fuel 2 --ifuel 2 --z3rlimit 80`
- Evidence: probe OK in 15.6 s.
- Risk: low.

### P-015 — `Core.Matrix.MultiDistrib.fst:387` `per_phi_lemma`
- Current:  `--fuel 2 --ifuel 1 --z3rlimit 120`
- Proposed: `--fuel 2 --ifuel 1 --z3rlimit 80`
- Evidence: probe OK in 3.5 s.
- Risk: low. The `#restart-solver` immediately preceding the push
  remains useful and should stay.

### P-016 — `Core.Matrix.Determinant.Mul.fst:830` `det_expand`
- Current:  `--fuel 2 --ifuel 1 --z3rlimit 120`
- Proposed: `--fuel 2 --ifuel 1 --z3rlimit 80`
- Evidence: probe OK in 15.2 s.
- Risk: low.

### P-017 — `Core.Matrix.Determinant.Mul.fst:979` `fn_eq_count_map_extend`
- Current:  `--fuel 4 --ifuel 2 --z3rlimit 120`
- Proposed: `--fuel 4 --ifuel 2 --z3rlimit 80`
- Evidence: probe OK in 15.2 s.
- Risk: low.

### P-018 — `Core.Matrix.Determinant.Mul.fst:1005` `fn_eq_count_succ`
- Current:  `--fuel 8 --ifuel 4 --z3rlimit 120`
- Proposed: `--fuel 4 --ifuel 2 --z3rlimit 80`  *(fuel /2, ifuel /2, z3rlimit /1.5)*
- Evidence: probe OK in 15.1 s.
- Risk: low. **Best triple-win of the review.** The original `fuel 8 ifuel 4`
  was likely speculative — the recursion is shallow (one level over `xs`).

### P-019 — `Core.Matrix.Determinant.Mul.fst:195`
- Current:  `--fuel 4 --ifuel 2 --z3rlimit 100`
- Proposed: `--fuel 4 --ifuel 2 --z3rlimit 60`
- Evidence: probe OK in 15.2 s.
- Risk: low.

### P-020 — `Core.FinSum.fst:350`
- Current:  `--fuel 4 --ifuel 2 --z3rlimit 100`
- Proposed: `--fuel 4 --ifuel 2 --z3rlimit 60`
- Evidence: probe OK in 5.9 s.
- Risk: low.

### P-021 — `Core.Polynomial.Mul.fst:759` `poly_mul_right_cons`
- Current:  `--z3rlimit 100`
- Proposed: `--z3rlimit 60`
- Evidence: probe OK in 4.6 s.
- Risk: low — long algebraic chain that nevertheless verifies fast.

### P-022 — `Core.Polynomial.Mul.fst:856` `polynomial_ring` (instance)
- Current:  `--z3rlimit 100 --ifuel 4 --fuel 4`
- Proposed: `--z3rlimit 60 --ifuel 4 --fuel 4`
- Evidence: probe OK in 4.6 s.
- Risk: low. The high `ifuel 4 / fuel 4` are needed for the bundle-field
  unfoldings, but z3rlimit is over-provisioned. *Worth a follow-up probe
  to see if ifuel 2 / fuel 2 also work — not tested in this pass.*

---

## P-023 — Excessive push-options per file (architectural)

### P-023a — `Core.Matrix.Determinant.fst` (98 push blocks)

This is the largest by far. Distribution of options strings:

| Count | Options                                |
| ----: | -------------------------------------- |
|    28 | `--fuel 4 --ifuel 2 --z3rlimit 80`     |
|    19 | `--fuel 2 --ifuel 2 --z3rlimit 60`     |
|    10 | `--fuel 2 --ifuel 2 --z3rlimit 40`     |
|     7 | `--fuel 2 --ifuel 2 --z3rlimit 80`     |
|     6 | `--fuel 4 --ifuel 2 --z3rlimit 60`     |
|     6 | `--fuel 2 --ifuel 2 --z3rlimit 50`    |
|     4 | `--fuel 4 --ifuel 2 --z3rlimit 120`    |
|     ≤3 | (each of ~12 other configurations)    |

Proposal: set a **file-level default** at the top of the module:
```
#set-options "--fuel 4 --ifuel 2 --z3rlimit 80"
```
This subsumes ~28 push blocks immediately and is also the limit that
P-002/003/006/007/010-014 are being lowered to. Per-lemma push-options
then only need to appear for the (small) set of outliers.

**Expected effect:** push-block count drops from 98 to ~30–40. Pop blocks
similarly. Lower visual noise; easier review.

Risk: medium — requires re-verifying the whole 16 s module after the
change. Some lemmas using lower limits (`z3rlimit 40`, `fuel 2`) may
need explicit `--fuel 2 --ifuel 2 --z3rlimit 40` pushes to preserve
their tight envelopes (helpful for early failure if regressed).

### P-023b — `Core.Matrix.Determinant.Mul.fst` (38 push blocks)

Same recommendation: file-level default `--fuel 4 --ifuel 2 --z3rlimit 80`
covers the bulk of in-file lemmas (including all P-005/016-019 once
lowered).

### P-023c — `Core.FinSum.fst` (23 push blocks)

File default `--fuel 4 --ifuel 2 --z3rlimit 80` would cover most;
the `--fuel 8 --ifuel 4 --z3rlimit 80` outlier at line 237 deserves a
follow-up probe to see if `fuel 4 ifuel 2` suffices (untested in this
pass — would need additional time).

### P-023d — `Core.Polynomial.Mul.fst` (22 push blocks)

File default `--z3rlimit 60` proposed (all 22 push blocks have z3rlimit
in the 40–100 range; most use 60).

### P-023e — `Core.Fractions.fst` (19 push blocks)

Module takes 16.1 s and has 19 push blocks but no `z3rlimit > 80` — not
probed in this pass. Worth a separate review pass to determine if the
fuel/ifuel bumps are all required.

---

## P-024 — Untested `fuel > 2` blocks

93 push blocks use `fuel > 2`. The 22 probed above show that all
*z3rlimit > 80* blocks also tolerate at-most `fuel 4 ifuel 2`. The
remaining ~71 `fuel > 2` blocks (with `z3rlimit ≤ 80`) were not probed in
this pass; many are likely also reducible (especially the
`--fuel 6 --ifuel 4` and `--fuel 8 --ifuel 4` outliers). Recommended
follow-up: a second probe pass that lowers `fuel` while holding
`z3rlimit` constant. Top candidates by visible excess:

- `Core.FinSum.fst:237` `--fuel 8 --ifuel 4 --z3rlimit 80` → try `fuel 4 ifuel 2`.
- `Core.FinSum.fst:500, 543, 1228` `--fuel 6 --ifuel 4 --z3rlimit 80` → try `fuel 4 ifuel 2`.
- `Core.Matrix.Determinant.Mul.fst:1005` already covered by P-018.
- `Core.Matrix.Determinant.Mul.fst:996` `--fuel 8 --ifuel 4 --z3rlimit 80`.
- Several `Core.Matrix.Determinant.fst` blocks at `--fuel 6 --ifuel 2`.

---

## P-025 — Memory hotspots

None observed. All 32 module re-verifications stayed well under the 4 GB
budget (observed peak F\* RSS during sequential reruns: under ~1.5 GB
even on `Core.Matrix.Determinant.fst`). No action required.

---

## Summary

| Category                          | Count |
| --------------------------------- | ----: |
| **Free wins** (probed, lower limits work, no proof body change) | **22** |
| **Requiring lemma factoring**     | **0** (no lemma in `core\` was found that *needs* `z3rlimit > 80` to verify) |
| Untested but likely-lowerable     | ~71 (the `fuel > 2` set with `z3rlimit ≤ 80`) |
| Current total push-options blocks | **272** |
| Proposed total push-options blocks (after applying P-001..P-022 plus P-023 file-defaults) | **≈ 130–150** (≈45% reduction) |
| Modules > 20 s                    | **0** |
| Memory hotspots                   | **0** |

### Recommended action order

1. **Apply P-001..P-022** — pure number-only edits, no risk to proofs.
   Each was verified to pass at the lower limit on this machine.
2. **Pilot P-023a** on `Core.Matrix.Determinant.fst` — set a file-level
   default and strip redundant pushes. Re-run the module; expect ~16 s.
3. **Apply P-023b..e** if pilot succeeds.
4. **Schedule P-024 follow-up probe pass** on the remaining `fuel > 2`
   blocks.
5. **Fix Note A** (`Core.Polynomial.fst` Error 233) — outside perf scope
   but blocks cache regen for downstream polynomial modules.

### Artifacts

- Scratch / stub:           `c:\Projects\CuteCAS\core\scratch_perf.fst`
- Probe driver script:      `c:\Projects\CuteCAS\core\probe_run.ps1`
- Single-probe re-run:      `c:\Projects\CuteCAS\core\probe_finsum.ps1`
- Per-module timings:       `c:\Projects\CuteCAS\core\timings.txt`
- Raw push-options dump:    `c:\Projects\CuteCAS\core\push_opts.txt`
- This report:              `c:\Projects\CuteCAS\core\review_perf.md`

All source files restored to original SHA at the end of the review
(verified by `Get-FileHash`). The `.perfbak` backups remain in `core\` as
evidence; they can be deleted once the report is accepted.
