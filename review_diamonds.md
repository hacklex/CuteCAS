# Typeclass-diamond review — `core\`

Date: 2026-05-23 (post polynomial-collapse cleanup).
Reviewer: typeclass-diamond agent (read-only).
Scratch demo: `core\scratch_diamonds.fst` (verifies clean).
Reviewed live files only — `.draft` and `.fst~` files were skipped.

## Headline

The polynomial chain is **clean** (only `polynomial_integral_domain`
remains as `instance`; `polynomial_ring`, `polynomial_acg`,
`polynomial_equatable`, `polynomial_commutative_ring`,
`polynomial_mul_is_commutative`, `polynomial_domain` are plain `let`
functions).

The fraction chain is **clean** (`fraction_field` is the only
declared `instance`; everything else under `fraction t` is reachable
through the foundation projection chain).

**Surprising bottom line**: every architectural diamond enumerated
below is currently **provably benign**: in the scratch file, all
three "two-path" probes (matrix triple instance, field→domain via
sf vs id, equatable int via default vs acg) close their `==`
postcondition **without** `compute ()` — plain SMT discharges them.
So no current proof in `core\` is failing because of these diamonds.

However, the diamonds are real in the architectural sense:

- F\* TC search **does** see multiple reachable paths and must
  arbitrate. The current happy-path verification masks any
  search-order surprise that may bite when new code grows.
- `unfold instance` on records is **explicitly forbidden** by
  AGENTS.md §1.5 and plan.md §1.4 / 5 — yet there are SEVEN live
  `unfold instance` declarations in `Core.Algebra.fst`. They work
  today only because they directly project a stored `@@@TC.no_method`
  field; introduce a more complex body and they will reignite the
  old-tower failure mode.
- `id_of_f` violates AGENTS.md §1.4 ("**`field` is NOT on the
  divisibility chain**. Trivially-…-from-field is a plain function,
  not an instance"). It is a documented shortcut, but the
  in-file comment only worries about the parallel `cr_of_f`
  shortcut it correctly avoids.
- The matrix tower mirrors the pre-collapse polynomial situation
  (three `instance`s on the same concrete type at three abstract
  levels). The polynomial collapse pattern should be replicated for
  matrices.

## Severity counts

- High:  2  (matrix triple instance, `unfold instance` rule violation)
- Med:   2  (`id_of_f` shortcut, `default_equatable` vs concrete-type acg chain)
- Low:   2  (`int` triple instance — analogous to matrix; cosmetic
              `unfold instance` on `eq_of_acg` / `mic_of_cr`)

---

## D-001 [HIGH] — Matrix: three parallel `instance` declarations

**Locations:**

- `Core.Matrix.fst:212` — `instance matrix_equatable t {| equatable t |} n : equatable (square_matrix t n)`
- `Core.Matrix.fst:312` — `instance matrix_add_comm_group t {| g: add_comm_group t |} n : add_comm_group (square_matrix t n)`
- `Core.Matrix.Ring.fst:587` — `instance matrix_ring t {| r: ring t |} n : ring (square_matrix t n)`

**Paths.** With `r: ring t` in scope a call site needing
`add_comm_group (square_matrix t n)` can be discharged by:

- direct: `matrix_add_comm_group t #(acg_of_r t #r) n`,
- composed: `acg_of_r (square_matrix t n) #(matrix_ring t #r n)`,
  which after the `unfold instance acg_of_r` body becomes
  `(matrix_ring t #r n).r_add`. Inspecting the body of
  `matrix_ring` (line 590) this is identically
  `matrix_add_comm_group t #(acg_of_r t #r) n`.

The same shape holds one level up for `equatable (square_matrix t n)`.

**Bench result.** `scratch_diamonds.fst::probe_matrix_acg_eq_smt_only`
proves the two paths' records `==` with **plain SMT**, no
`compute ()` needed. So today the diamond is benign at the proof
level.

**Why still flag as HIGH.**

1. The forest invariant (AGENTS §1.2 / plan §2.1.2) says **at most
   one instance per ordered (Source,Target) pair**. The matrix tower
   declares **three** `instance`s on the same concrete type, one for
   each (Source=Matrix, Target=Equatable/Acg/Ring). This is exactly
   the pattern the polynomial collapse removed.
2. TC search arbitrates between two candidates whenever an
   `acg`-consumer site sees `r: ring t`. Any future addition (e.g.
   a `commutative_ring (square_matrix t n)` constructed by a
   different code path) immediately reintroduces a NON-benign
   diamond. The architecture should not depend on the SMT encoder
   silently normalizing two record projections to the same term.
3. Echoes plan §2.1.2 "Shortcut instances that duplicate a path are
   forbidden — they re-create diamonds." `matrix_equatable` and
   `matrix_add_comm_group` are exactly such shortcut instances
   relative to `matrix_ring`.

**Affected lemmas / call sites (sample).** Anywhere
`add_comm_group (square_matrix t n)` or `equatable (square_matrix t n)`
is required: `matrix_add_congruence`, `matrix_add_zero`, all
`matrix_*` ACG lemmas in `Core.Matrix.fst`, every callback into
`Core.FinSum` whose carrier is matrices, all of
`Core.Matrix.MultiDistrib`, all `det`/`Permutation.Sum` use sites in
`Core.Matrix.Determinant`/`Mul`.

**Proposed fix.** Mirror the polynomial collapse:

1. Convert `instance matrix_equatable` → `let matrix_equatable`.
2. Convert `instance matrix_add_comm_group` → `let matrix_add_comm_group`.
3. Keep `instance matrix_ring` as the sole terminal instance.
4. Existing `matrix_ring` body already calls `matrix_add_comm_group`
   and `matrix_equatable` as ordinary functions — no body change
   needed.

**Scratch tested?** Yes — see `probe_matrix_acg_eq_*` in scratch
file. Both compute-driven and plain-SMT probes pass, confirming the
records align. The collapse is safe.

**Risk of applying automatically.** **Medium.** Every call site
that currently picks `matrix_add_comm_group` or `matrix_equatable`
via TC will instead need to receive a `ring t` (and TC will compose
through `matrix_ring`). Most internal call sites take
`add_comm_group t` directly, which is fine. Call sites that take
only `equatable t` will lose the matrix-equatable instance and
must either widen their constraint or accept the structure
explicitly. Worth a focused audit before applying.

---

## D-002 [HIGH] — `unfold instance` declarations on record-type instances

**Locations** (all in `Core.Algebra.fst`):

- `:88`  `unfold instance eq_of_acg`
- `:149` `unfold instance acg_of_r`
- `:192` `unfold instance r_of_d`
- `:227` `unfold instance r_of_cr`
- `:229` `unfold instance mic_of_cr`
- `:250` `unfold instance d_of_id`
- `:252` `unfold instance cr_of_id`

**Why flagged.** AGENTS.md §1.5 verbatim:

> ### 1.5 No `unfold instance` on record types
>
> F\* WHNF-inlines `unfold instance` bodies eagerly. For records,
> this means projections on the inlined form become syntactically
> distinct from projections on the un-inlined form, breaking SMT
> equality. **Use plain `instance` only.**

plan.md §5 (drop list, line 373): "Drop: every `unfold instance`
declaration in `..\new\`. Plain `instance` only in `core\`."

The rule is unambiguous: there should be **zero** `unfold instance`
declarations in `core\`. There are seven.

**Why it works today.** All seven bodies are
`<class>.<no_method_field>`, a single projection. F\* normalizes
both the unfolded and the non-unfolded forms equivalently when the
source instance is itself a constructor literal. The bug surface
appears when:

1. The instance argument is *not* a literal constructor — e.g. when
   it is the result of another `instance` body (deeper composition
   through more levels).
2. The body is more complex than a field projection — e.g.
   `cr_of_id` (line 252) builds a fresh `commutative_ring` record:

   ```fstar
   unfold instance cr_of_id ... : commutative_ring t = {
     cr_r   = id.id_d.d_r;
     cr_mic = id.id_mic;
   }
   ```

   With `unfold`, every use of `cr_of_id` is replaced by a fresh
   record literal. Take `cr_r` of one expansion and `cr_r` of
   another — F\* sees two record literals and may or may not
   collapse them at the SMT layer.

**Proposed fix.** Drop `unfold` on all seven. They will still
compose through TC search; SMT projections through plain `instance`
already normalize correctly (this review's scratch confirms).

**Scratch tested?** Partially. The probes verify the *unfolded* and
*non-unfolded* paths produce SMT-equal results; we did not test the
inverse (whether dropping `unfold` breaks an existing proof). Given
that the polynomial / fraction towers do not use `unfold instance`
anywhere and verify clean, the risk is low.

**Risk of applying automatically.** **Low–medium.** Mechanical
removal of `unfold`. A full tower rebuild is required to confirm
nothing in the proof corpus relied on the WHNF inlining. If
something breaks, fall back to `compute ()` at the site.

---

## D-003 [MED] — `id_of_f` shortcut violates AGENTS §1.4

**Location:** `Core.Algebra.fst:271` —
`instance id_of_f (t:Type) {| f: field t |} : integral_domain t = { ... }`.

**The rule.** AGENTS.md §1.4: "**`field` is NOT on the divisibility
chain.** Trivially-ED-from-field is a **plain function**, not an
instance ... All plain functions, never `instance`. Cross-tower
upgrades on a different result type are exactly the situations where
TC chains catastrophically diamond."

`id_of_f` is precisely such a cross-tower upgrade (field →
integral_domain), declared as `instance`.

**The diamond.** Given `f: field t`, both paths reach `domain t`:

- A: `d_of_sf t #(sf_of_f t #f)`  — uses `sf_of_f` + `d_of_sf`
  (both plain instances). After delta on
  `sf_of_f`: `d_of_sf t #(.. record literal f.f_sf)`.
- B: `d_of_id t #(id_of_f t #f)`  — `d_of_id` is `unfold instance`,
  so this WHNF-reduces to `(id_of_f t #f).id_d`, which after another
  delta on `id_of_f`'s plain-instance body is `f.f_sf.sf_d`.

`probe_field_domain_eq_smt_only` in scratch confirms these are
SMT-equal today (passes with `= ()`). Benign at the proof level.

**Why still flag.** The in-file comment at line 277 says:

> Note: field → commutative_ring composes uniquely via id_of_f ∘
> cr_of_id. We deliberately do NOT declare a direct `cr_of_f`
> shortcut — that would create a diamond.

The author was aware of the diamond risk, declined `cr_of_f`, but
declared `id_of_f` itself — which AGENTS §1.4 says is the same kind
of cross-tower instance and should be a plain function. By their
own logic the comment applies to `id_of_f` too.

**Affected sites.** Every consumer of `integral_domain (fraction d)`
in `Core.Fractions` (the fraction tower goes field → id via this
edge), and any future field-rooted module.

**Proposed fix.** Convert
`instance id_of_f` → `let field_to_id` (plain function). All
current users have a `field` in scope; they would call
`field_to_id f` explicitly. The fraction module's
`integral_domain (fraction d)` consumers would need a one-liner
helper or an explicit `field_to_id (fraction_field t d)` pass.

**Scratch tested?** Yes — `probe_field_domain_eq*`. Both paths
align.

**Risk of applying automatically.** **Medium.** This impacts
several users in fractions and (future) polynomial-over-field code.
A targeted cascade similar to the h4 cascade pattern is feasible,
but should be done with care because `integral_domain` is a heavily
used class.

---

## D-004 [MED] — `default_equatable` (eqtype) overlaps with all concrete-type acg chains

**Locations:**

- `Core.Algebra.fst:44` — `instance default_equatable (t: eqtype) : equatable t`
- `Core.Algebra.Int.fst:19` — `instance int_acg : add_comm_group int`
- `Core.Algebra.fst:88` — `unfold instance eq_of_acg`

**The diamond.** `int` is an `eqtype` and has `int_acg`. F\* TC
search for `equatable int` can satisfy via either:

- A: `default_equatable int` directly,
- B: `eq_of_acg int #int_acg` (composes through the acg chain),
  which after the unfold reduces to `int_acg.acg_eq`.

These two records have different `eq` functions in general
(`(=)` vs whatever `int_acg.acg_eq.eq` is). For `int` they happen
to coincide because `int_acg.acg_eq` IS the eqtype eq, but the
diamond manifests for **any future eqtype with a custom
`add_comm_group` instance whose `acg_eq` is non-default**.

**Bench result.** `probe_int_equatable_eq_smt_only` passes (both
paths converge for `int` today).

**Risk for the future.** As soon as someone declares an `eqtype`
with a non-extensional `acg_eq` (e.g. a quotient type where
`(=)` on representatives is finer than the desired structural eq),
the two paths diverge **and** TC search will silently pick one,
producing inconsistent equatable behaviour across lemmas.

**Proposed fix.** Either:

1. Drop `default_equatable` and force every type that needs an
   `equatable` to declare one explicitly (cleanest, aligns with
   "no convenience instances" doctrine), OR
2. Restrict `default_equatable` to types not otherwise covered
   (impossible without TC priority machinery F\* lacks), OR
3. Keep `default_equatable` but **convert it to a plain `let`** and
   apply it explicitly when needed.

Option 3 matches the AGENTS §1.4 doctrine for cross-tower
upgrades.

**Scratch tested?** Yes — `probe_int_equatable_eq*`. Records align
for `int` (the only current eqtype with both paths in scope).

**Risk of applying automatically.** **Low.** Few use sites today;
mostly affects how tests and ad-hoc proofs in
`Core.Algebra.NotationTest` set up `equatable` for basic types.

---

## D-005 [LOW] — Int: four parallel `instance` declarations

**Locations** (`Core.Algebra.Int.fst`):

- `:19` `instance int_acg : add_comm_group int`
- `:32` `instance int_ring : ring int`
- `:43` `instance int_mic : mul_is_commutative int #int_ring`
- `:47` `instance int_cr : commutative_ring int`

**Same shape as D-001** (matrix). With `int_cr` in scope, TC can
reach `ring int` via either `int_ring` or `r_of_cr int_cr`. Likewise
for `add_comm_group int` via `int_acg` vs `acg_of_r int_ring`.

`int_mic` is a marker class with explicit base parameter
(`#int_ring`), so it's well-defined; that one is fine.

**Why LOW.** `int` is only used for tests / notation demos; it does
not feed any production proof in the verified tower. Still, it
exists as a tutorial for newcomers and currently models the **wrong
pattern**.

**Proposed fix.** Collapse to a single terminal instance,
`int_cr` (commutative_ring is the strongest int satisfies in this
file). Demote `int_acg`, `int_ring` to plain `let`s.

**Scratch tested?** Not explicitly (the int case is structurally
identical to matrix triple-instance; the matrix probe covers the
reasoning). The int `equatable` portion is covered by D-004.

**Risk of applying automatically.** **Low.** `Core.Algebra.Int.fst`
has only `Core.Algebra.NotationTest` as a consumer.

---

## D-006 [LOW] — Cosmetic `unfold instance` on `eq_of_acg`/`mic_of_cr`

Subset of D-002, called out separately because these two have
genuinely zero-content bodies (`acg.acg_eq` / `cr.cr_mic`). Even
under `unfold`, they cannot generate distinct record literals —
they project a stored field. The risk for these two is purely
"rule-following": AGENTS §1.5 prohibits `unfold instance` on
records absolutely. Including them in any D-002 fix is mechanical.

---

## Cross-module pollution check

Scanned every `open` and re-export. **No module re-exports an
instance it does not declare locally.** The fraction and polynomial
modules each ship exactly one terminal instance; the matrix module
ships three (D-001); Algebra ships the foundation tower. No
unexpected `instance val` leaks. ✔

## `#`-instance override evidence

Searched for `#(matrix_*)`, `#(polynomial_*)`, `#(fraction_*)`,
`#(int_*)`:

- `Core.Algebra.Int.fst:43` — `mul_is_commutative int #int_ring` —
  CORRECT use (marker class needs its base spelled out).
- `Core.Polynomial.Mul.fst:915` — `mul_is_commutative (polynomial cr) #(polynomial_ring cr)` —
  CORRECT (same reason; `polynomial_ring` is now a plain `let`, so
  it must be passed explicitly).

No emergency-disambiguation overrides found. The codebase does not
appear to be papering over a diamond with `#`-overrides today.

---

## Top 3 most critical diamonds

1. **D-001 (matrix triple instance)** — directly mirrors the
   pre-collapse polynomial structure that was just fixed. The
   collapse pattern is proven to work; not applying it to matrices
   is an inconsistency the next round of refactoring will trip
   over.
2. **D-002 (`unfold instance` rule violation)** — seven explicit
   violations of an unambiguous "non-negotiable" rule. Even though
   they are benign today, they constitute architectural debt the
   AGENTS doctrine was written specifically to outlaw.
3. **D-003 (`id_of_f` cross-tower shortcut)** — the in-file comment
   anticipates the rule but applies it inconsistently. Converting
   `id_of_f` to a plain function (matching `field_of_fractions`,
   `polynomial_ed_of_field`, etc., per AGENTS §1.4 example list)
   closes the rule violation without affecting any production
   proof.

---

## Verification notes

- Scratch file `core\scratch_diamonds.fst` verifies clean (no
  warnings, no errors, no admits in final form).
- All probes use plain SMT (`= ()`); none required `compute ()`.
  This is the empirical evidence that today's diamonds are benign.
- The fact that they are *benign* under SMT does not relax the
  architectural rules — see D-001/D-002/D-003 reasoning.
- Polynomial collapse VERIFIED clean: only
  `polynomial_integral_domain` is an `instance`; six predecessors
  are plain `let`s. ✔
- Fraction module VERIFIED clean: only `fraction_field` is an
  `instance`. ✔
- Matrix module is the remaining structural outlier. ✗
