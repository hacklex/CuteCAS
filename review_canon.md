# Canonicalization-tactic review (read-only)

Scope: `c:\Projects\CuteCAS\core\`, excluding `.draft` files.
Reviewer: canonicalization-simplifier sub-agent.
Scratch file with before/after pairs: `core\scratch_canon.fst`
(plus split helpers `scratch_canon_after.fst`, `scratch_canon_before.fst`,
`scratch_canon_empty.fst`, `scratch_canon_empty2.fst`).

## Timing methodology

Wall-clock via PowerShell `Measure-Command` against
`fstar.exe --include . --cache_dir obj <file>` (warm cache). Per-Z3-query
timings via `--query_stats`.

Baselines (3-run average):

| Module variant                                    | Time   |
| ------------------------------------------------- | ------ |
| Empty module, no `open Core.Tactics.CanonRing`    | ~265 ms |
| Empty module, with `open Core.Tactics.CanonRing`  | ~500 ms |
| `scratch_canon_after.fst` (5 `canon_ring()` lemmas, with open) | ~820 ms |
| `scratch_canon_before.fst` (priv helper + 2 explicit lemmas)   | ~420 ms |

Implied per-lemma cost (after subtracting the matching empty baseline):

- `canon_ring()` lemma:   **~60–65 ms wall** (Z3 query closed by tactic; cost
  is tactic reflection + `T.trefl`, no SMT round-trip).
- Small explicit chain:   **~5–15 ms wall** (Z3 query <20 ms, sometimes <5 ms).

The user threshold is 50 ms (explicit) vs 250 ms (tactic). All measured
`canon_ring()` invocations land at ~60 ms — comfortably **below** the
250 ms cutoff. So the "tactic too slow" failure mode is not currently
triggered anywhere in `core\`. The deciding factor in every finding
below is therefore **LOC / readability**, not raw verification time.

---

## C-001  `double_negation_lemma`  (Core.Matrix.Determinant.fst:186-195)

Current code (9 lines + reliance on the 28-line helper
`priv_group_cancel_right`):

```fstar
let double_negation_lemma (#t: Type) {| cr: commutative_ring t |} (x: t)
  : Lemma ((-(-x)) = x)
  = let g = cr.cr_r.r_add in
    let nx = g.neg x in
    let nnx = g.neg nx in
    g.add_negation nx;
    g.add_negation x;
    g.acg_eq.symmetry g.zero (g.add x nx);
    g.acg_eq.transitivity (g.add nnx nx) g.zero (g.add x nx);
    priv_group_cancel_right g nnx x nx
```

Proposed:

```fstar
let double_negation_lemma (#t: Type) {| cr: commutative_ring t |} (x: t)
  : Lemma ((-(-x)) = x)
  = assert ((-(-x)) = x) by canon_ring ()
```

Timing (from scratch):

- BEFORE: Z3 query 11 ms (`priv_group_cancel_right_local` helper itself
  costs 31–64 ms on top, but only when the helper isn't already in the
  cache — it's shared with several other lemmas).
- AFTER: tactic ~60 ms wall, 0 ms SMT.

LOC saved in this lemma: **8**. Within the 250 ms threshold rule.
**Net win.**  Action: **apply**.

---

## C-002  `neg_of_sum_local`  (Core.Matrix.Determinant.fst:197-204)

Current:

```fstar
let neg_of_sum_local (#t: Type) {| cr: commutative_ring t |} (x y: t)
  : Lemma (-(x + y) = (-x) + (-y))
  = let g = cr.cr_r.r_add in
    H.neg_of_sum #t #g x y;
    g.add_commutativity (g.neg y) (g.neg x);
    g.acg_eq.transitivity (g.neg (g.add x y)) (g.add (g.neg y) (g.neg x))
                          (g.add (g.neg x) (g.neg y))
```

Proposed:

```fstar
let neg_of_sum_local (#t: Type) {| cr: commutative_ring t |} (x y: t)
  : Lemma (-(x + y) = (-x) + (-y))
  = assert (-(x + y) = (-x) + (-y)) by canon_ring ()
```

Timing:

- BEFORE: Z3 query **4 ms**.
- AFTER: tactic ~60 ms wall.

LOC saved: **4**. Tactic is ~55 ms slower but still **far** below the
250 ms threshold. The explicit version is at 4 ms which is *well* under
50 ms, so the user's rule ("if explicit <50 ms and tactic >250 ms, keep
explicit") doesn't fire — the tactic stays within budget.
**Net win** on LOC. Action: **apply** (small absolute time cost).

---

## C-003  Numerator commutativity in `fraction_add_is_commutative`
        (Core.Fractions.fst:282-283)

Current code already uses `canon_ring()`:

```fstar
assert (a * e + b * c = c * b + e * a) by canon_ring();
assert (b * e = e * b) by canon_ring();
```

Verified in scratch as `frac_add_comm_num_CURRENT`. Tactic cost ~60 ms.
The explicit chain version would be at least 6–8 lines of `add_/mul_*` +
`transitivity`. **Net win is already realized.** Action: **leave**.

---

## C-004  `mul_middle_swap`  (Core.Fractions.fst:111-114)

Already uses `canon_ring()`:

```fstar
private let mul_middle_swap (#t:Type) {| d: integral_domain t |} (a b c e: t)
  : Lemma ((a * b) * (c * e) = (a * c) * (b * e))
  = assert ((a * b) * (c * e) = (a * c) * (b * e)) by canon_ring()
```

This is the canonical 4-AC-juggle and is precisely the use case `canon_ring`
was written for. The hand-written alternative requires 4–6 `mul_*` rewrites
plus transitivity. Action: **leave** (already correct).

---

## C-005  Numerator identity in `fraction_add_is_associative`
        (Core.Fractions.fst:299-301)

Already uses `canon_ring()`:

```fstar
assert ((a * dd + b * c) * f + (b * dd) * e
      = a * (dd * f) + b * (c * f + dd * e)) by canon_ring();
```

This is a 6-variable polynomial identity; the hand version would be 15+
explicit rewrites. Action: **leave** (already correct, big LOC win
realized).

---

## C-006  `priv_neg_mul_r`  (Core.Matrix.Determinant.fst:100-115)

Current code (14 lines) — full body shown in `Core.Matrix.Determinant.fst`.
The lemma proves `-(x*y) = x*(-y)` over a commutative ring via four
intermediate transitivity steps through `priv_neg_mul_l` and two
`mul_commutativity` invocations.

Proposed:

```fstar
private let priv_neg_mul_r (#t:Type) (cr: commutative_ring t) (x y: t)
  : Lemma (cr.cr_r.r_add.acg_eq.eq (cr.cr_r.r_add.neg (cr.cr_r.mul x y))
                                    (cr.cr_r.mul x (cr.cr_r.r_add.neg y)))
  = assert (-(x * y) = x * (-y)) by canon_ring ()
```

Caveat: the original lemma takes `cr` as an *explicit* (positional) arg,
so there is no `{| cr: commutative_ring t |}` instance binder in scope.
`canon_ring()` walks scoped binders looking for a `commutative_ring` type;
it will not see a positional `cr`. To use the tactic the lemma signature
would need to switch to `{| cr: commutative_ring t |}`. That's a small
caller-side cascade (the file has a handful of `priv_neg_mul_r cr x y`
calls).

Verified in scratch as `priv_neg_mul_r_AFTER` with an instance binder:
tactic closes in ~60 ms.

Timing: BEFORE — explicit Z3 query <20 ms but a long chain. AFTER — ~60 ms
tactic. LOC saved in the lemma body: **13**. Caller updates: ~3-5 sites.

Action: **discuss** — net win on LOC but requires a small signature
change. Defer unless the maintainer is willing to rewire callers.

---

## C-007  `priv_neg_x_eq_neg_one_mul`  (Core.Matrix.Determinant.fst:120-129)

This lemma is parameterised by `r: ring t`, **not** `commutative_ring`.
`canon_ring` requires a commutative-ring binder (its AST normalizes
products by sorting atoms, which is unsound without commutativity).
**Not a candidate.** Action: **leave**.

---

## C-008  `fraction_add_left_congruence`  (Core.Fractions.fst:308-342)

Current: 30 lines of explicit `mul_middle_swap`, `mul_commutativity`,
`left_/right_distributivity`, `add_congruence`, `transitivity`, …

Goal (after letting `a,b,c,dd,e,f = x1.num, x1.den, y.num, y.den, x2.num,
x2.den`):

```
requires  a * f = b * e
ensures   (a * dd + b * c) * (f * dd) = (b * dd) * (e * dd + f * c)
```

This is the textbook "substitute, then ring-canonicalize" pattern that
`canon_ring_subst_auto` was designed for. **Tested and failed**:

```
Tactic failed
canon_ring_subst_auto: no in-scope equality hypothesis matches a goal subterm
```

The auto-substitution looks for the LHS of the equality hypothesis as a
**literal subterm** of the goal. Here `a * f` only appears after
distribution; the raw goal has no `a * f` subterm. A "canonicalize-then-
substitute" tactic would unlock this proof; the current
"substitute-then-canonicalize" tactic does not.

LOC saving *if* the tactic could close it: **~28**. Currently impossible.

Action: **leave** (note as future tactic improvement: a
`canon_ring_then_subst` variant that first normalizes both sides before
attempting substitution would collapse this and several similar
fraction-arithmetic lemmas).

---

## C-009  Head equality in `poly_mul_right_cons`
        (Core.Polynomial.Mul.fst:788-797)

Current (8 lines):

```fstar
(* heads: (b*a)+zero  =  (a*b)+zero *)
cr.cr_mic.mul_commutativity b a;
H.x_plus_zero (b * a);
H.x_plus_zero (a * b);
let ba_z = (b * a) + zr in
let ab_z = (a * b) + zr in
symmetry ab_z (a * b);
transitivity ba_z (b * a) (a * b);
transitivity ba_z (a * b) ab_z;
assert (ba_z = ab_z)
```

Proposed:

```fstar
assert ((b * a) + (zero <: t) = (a * b) + (zero <: t)) by canon_ring ()
```

Timing (scratch):

- BEFORE: Z3 query **6 ms**.
- AFTER: tactic ~60 ms wall.

LOC saved: **8**. Tactic ~55 ms slower in absolute terms, still well
under the 250 ms threshold. Action: **apply** — clear readability and
LOC win.

---

## C-010  `eval_scalar_mul` (Core.Polynomial.Mul.fst:1116-1152)

The body already uses one `canon_ring()` call at line 1141 to discharge
`x * (a * ep') = a * (x * ep')`. The surrounding 15 lines of
`add_congruence` / `left_distributivity` / `symmetry` / `H.trans3` could
**not** be collapsed by a single `canon_ring()` because the lemma has
intermediate `eval (scalar_mul a (b :: p')) x = start` definitional
unfolding goals that are not pure ring identities. The mixed style is
appropriate. Action: **leave**.

---

## C-011  `Core.Matrix.Determinant.Mul.fst:191`

```fstar
= assert ((a * b) * (c * d) = (a * c) * (b * d)) by canon_ring ()
```

Single-line `canon_ring()` for an AC juggle. Already optimal. Action:
**leave**.

---

## C-012  `priv_neg_mul_l` (Core.Matrix.Determinant.fst:71-95)

Parameterised by `r: ring t` (non-commutative). Same as C-007: not a
candidate. Action: **leave**.

---

## Summary

- **Net wins** (apply `canon_ring()`): **3** — C-001, C-002, C-009.
- **Net wins gated on signature change**: **1** — C-006 (requires
  changing `cr` from positional to instance binder).
- **Net losses** (current is better): **0**. No `canon_ring()` call in
  `core\` exceeds the 250 ms threshold — every existing tactic call is
  in the ~60 ms range, well within budget.
- **Already-optimal `canon_ring()` calls**: C-003, C-004, C-005, C-011
  — leave as is.
- **Cannot be collapsed by current tactics**: C-007, C-008, C-010, C-012
  — leave (C-008 would unlock with a future `canon-then-subst` tactic).

Total potential LOC reduction in `core\` from applying C-001+C-002+C-009:
roughly **20 lines** (8 + 4 + 8). Plus another **13 lines** if C-006 is
accepted with its caller cascade.

No regressions discovered.
