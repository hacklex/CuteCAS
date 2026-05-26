# CuteCAS — agent instructions

> This file layers on top of `.github\copilot-instructions.md`.
> All repo-wide rules from that file still apply (CRLF, no git, no
> admit / no assume in committed code, resource budget, Windows paths,
> back-up-before-script-edits, …). The rules below apply
> **additionally** to all `Core.*` modules at the repo root.

## 1. Design rules (the forest invariant)

These are non-negotiable. Every PR / commit / agent action on the
`Core.*` tower must respect them.

### 1.1 Bundle fields are `@@@TC.no_method`

Every field of a class that stores a sub-instance — that is, any field
whose type is itself a class — **must** be tagged
`@@@FStar.Tactics.Typeclasses.no_method`. This prevents the TC resolver
from using bundle fields as projections, which was the root cause of
the multi-path diamonds in the old tower.

```fstar
class commutative_ring t = {
  [@@@TC.no_method] cr_r:   ring t;
  [@@@TC.no_method] cr_mic: mul_is_commutative t cr_r
}
```

The standalone explicit `instance` declarations are what drive TC
search; the fields are storage only.

### 1.2 Exactly one `instance` per ordered class pair

For each ordered pair `(Source, Target)` of classes in the tower, there
must be **at most one** declared `instance` of `Target` from `Source`.
Multi-step climbs (e.g. `field → ring`) compose through the unique
edges (`f_sf : skewfield`, `sf_d : domain`, `d_r : ring`). Adding a
shortcut instance recreates a diamond and is forbidden.

When unsure whether a new instance is necessary, **don't add it** —
F\* will compose through the existing edges automatically.

### 1.3 Marker classes take their base as an explicit dependent param

A class that refines an existing structure with extra laws (without
adding new data) takes the underlying structure as an **explicit
non-instance parameter**:

```fstar
class mul_is_commutative t (r: ring t) = {
  mul_commutativity: (x:t) -> (y:t) -> Lemma (mul x y `eq` mul y x)
}
```

NOT `{| r: ring t |}`. The dependent parameter makes
`mul_is_commutative t r1` and `mul_is_commutative t r2` distinguishable
when `r1 ≢ r2`, which is what we want for coherence.

### 1.4 Divisibility refinements form a single chain off `integral_domain`

The divisibility refinements form a **linear chain**:

```
integral_domain  ←  gcd_domain  ←  ufd  ←  euclidean_domain
                    (every ED is a UFD is a GCD-domain is an ID)
```

Each refinement stores its **immediate parent** as a
`@@@TC.no_method` field. **Exactly one** `instance` is declared per
edge:

```fstar
class gcd_domain         t = { [@@@TC.no_method] gcd_id : integral_domain t; … }
class ufd                t = { [@@@TC.no_method] ufd_gcd: gcd_domain t;       … }
class euclidean_domain   t = { [@@@TC.no_method] ed_ufd : ufd t;              … }

instance id_of_gcd  t {| g: gcd_domain        t |} : integral_domain t = g.gcd_id
instance gcd_of_ufd t {| u: ufd               t |} : gcd_domain       t = u.ufd_gcd
instance ufd_of_ed  t {| e: euclidean_domain  t |} : ufd              t = e.ed_ufd
```

**Skip-level instances are forbidden** (`id_of_ufd`, `gcd_of_ed`,
`id_of_ed`, …). F\* composes them through the chain automatically;
declaring them creates diamonds the moment two paths reach the same
ancestor.

A function `f {| gcd_domain t |}` is callable from a
`{| euclidean_domain t |}` site because TC composition resolves the
`ED → UFD → GCD` path uniquely. Mathematical content stays DRY: an
ED implementation provides only its Euclidean structure, and its
GCD / UFD / ID evidence is derived once and projected.

**`field` is NOT on the divisibility chain.** Trivially-ED-from-field
is a **plain function**, not an instance:

```fstar
val field_to_ed (#t:Type) (f: field t) : euclidean_domain t
```

Use it explicitly. Same for every cross-type upgrade:

```fstar
val polynomial_ed_of_field   : #t:Type -> field t          -> euclidean_domain (polynomial t)
val field_of_fractions       : #t:Type -> integral_domain t -> field (fraction t)
val differential_field_of_X  : … -> differential_field …
```

All plain functions, never `instance`. Cross-tower upgrades on a
different result type are exactly the situations where TC chains
catastrophically diamond.

Other refinements along orthogonal axes (`differential_ring`, future
`ordered_ring`, `topological_ring`, …) form their **own** chains
rooted at the appropriate point (typically `ring` or
`commutative_ring`). They do not intermix with the divisibility
chain.

### 1.5 No `unfold instance` on record types

F\* WHNF-inlines `unfold instance` bodies eagerly. For records, this
means projections on the inlined form become syntactically distinct
from projections on the un-inlined form, breaking SMT equality. Use
plain `instance` only. If you need normalization, use the `compute()`
tactic at the use site.

### 1.6 Named top-level functions over inline lambdas

If an expression involving lambdas might appear in a postcondition,
under a tactic, as an index of a `fin_sum`, etc., **bind it as a named
top-level function**. Closures bound by `let` (even named `let`) are
distinct SMT terms from inline lambdas even with identical bodies.

```fstar
let cofactor_body (#t:Type) (m: matrix t n n) (i j: nat{i<n}) (k:nat{k<n}) : t = …
  
let det_via_cofactor m i =
  fin_sum (cofactor_body m i) ← good
  // not: fin_sum (fun k -> …) ← bad
```

This was a major source of friction in the old tower (it produced the
let-binding opacity that defeated `compute()`-based bridges).

## 2. Workflow rules

### 2.1 Scratch-file isolation when developing a lemma

Never re-verify thousands of LOC on every iteration. When working on a
new lemma:

1. Identify the verified prefix it depends on (whatever is already
   committed and `.checked`-cached in `obj\`).
2. Create a `Scratch.<problem>.fst` that `open`s only that prefix.
3. Develop the lemma in the scratch file. Re-verification is near-free
   because all dependencies hit the cache.
4. Move the lemma to its final home once stable.

### 2.2 Always verify with caching

Invoke F\* with `--cache_checked_modules --cache_dir obj`. Never wipe
`obj\` wholesale; invalidate targeted files only.

**Critical**: `--cache_checked_modules` only writes the `.checked` file
for the module **on the command line** — it does NOT cache transitive
dependencies. If you verify `Core.Matrix.Determinant.Mul.fst` directly
on an empty cache, F\* will re-load every dependency from source and
emit **Warning 247** ("Checked file ... was not written. Reason:
checked file ...does not exist") for the target. The module still
verifies; only its `.checked` is skipped.

**Fix**: verify modules in **topological order**, with each `.fsti`
BEFORE its matching `.fst`. After pulling fresh sources, after any
large refactor, or any time you see Warning 247, rebuild the tower
in dependency order from a clean `obj\` cache.

### 2.3 Back up before script-driven edits

Any non-trivial script edit (PowerShell loop, regex pass, mass rename,
`Set-Content`) MUST be preceded by `Copy-Item path path.bak`. Verify
immediately after (line count, first/last lines, run F\*).

**Known PowerShell footgun**:
`Get-Content path | Set-Content -NoNewline path2` **concatenates all
lines into one**, silently destroying the file. Use
`[System.IO.File]::WriteAllLines($path, $lines)` to write line arrays
back, or pipe to `Set-Content` **without** `-NoNewline`.

### 2.4 Sliding `admit()` for debugging — the only acceptable workflow

When a lemma body fails:

1. Insert `admit()` at the **end** of the body. Confirm the lemma now
   passes — this proves the setup is fine and only the conclusion is
   wrong.
2. **Slide the `admit()` upward**, statement by statement, until it
   stops passing. The first statement above the failing point is the
   actual failure.
3. At the failing point, insert
   `assert (fact_you_expect); admit()` to test the precondition.
4. Fix ONLY the identified gap.

Blind body rewrites are forbidden. They waste verification budget and
introduce new bugs.

### 2.5 Tactic-driven debug introspection

When `compute ()` / `smt ()` / `canon_ring ()` fails and you don't know
why, use **tactic-level introspection**:

```fstar
assert (P) by (FStar.Tactics.compute (); FStar.Tactics.dump "after_compute")
```

`dump` prints the proof state (goals + context) after the named phase.
Read what's actually there before guessing.

For deeper inspection, write a small tactic that walks the goal term
and `T.print`s pieces of interest. Tactic-level debug ALWAYS beats
flailing at SMT.

### 2.6 Decompose proofs into small top-level lemmas

No monolithic proof bodies. Every non-trivial sub-fact factors out as
a named top-level lemma. Small lemmas:

- are easier for Z3,
- are easier to debug with sliding `admit()`,
- are reusable.

Examples of obvious factoring candidates:

- `minor (transpose m) i j = transpose (minor m j i)`.
- Index-wise equality bridges (`forall i j. m1.[i,j] = m2.[i,j] → m1 ≡ m2`).
- `fin_sum` congruence bridges (one helper per index pattern).

### 2.7 No `admit()` / `assume` in committed code

Rule §4 of repo-wide instructions stands. `admit()` is a development
tool only. Strip every `admit()` before declaring a lemma done. Same
for `assume`.

### 2.8 Tighten resource limits after success

Once a lemma verifies, **lower** `--z3rlimit` (and `--fuel`/`--ifuel`
where applicable) until verification breaks, then back off slightly.
Counter-intuitively, some lemmas verify **faster** under tighter
limits because Z3 spends less time exploring dead ends.

Target: per-lemma `--z3rlimit` in **30–80**. If a single lemma needs
`> 80`, factor it. If it needs `> 150` even after factoring, escalate
to the user.

### 2.9 Canonicalization tactics first

Prefer `assert (X = Y) by (canon_ring ())` over manual chains of
`mul_commutativity` / `mul_associativity` / `left_distributivity`.
As the tower grows, add canonicalization tactics for each algebraic
structure (`canon_acg`, `canon_ring`, `canon_field`,
`canon_module`, …).

When a formula-level identity can be settled by a canonicalization
tactic, it **must** be — the alternative (writing the chain by hand)
is wasted work that breaks under future tower changes.

### 2.10 One module per file; split past ~600 LOC

When a `.fst` exceeds ~600 LOC or ~25 lemmas, split along a natural
seam. Use `.fst` + `.fsti` pairs for any heavy module:
declarations + class definitions in `.fsti`, proofs and helpers
in `.fst`.

## 3. Agent rules

### 3.1 The 10-attempt escalation cap

A sub-agent has at most **10 attempts** to verify a single lemma.
After 10 failed attempts:

1. **Stop.**
2. Summarize what was tried, what each attempt produced, and what the
   current best understanding of the failure is.
3. Escalate to the orchestrator (or, if the orchestrator hit the cap,
   to the user).

Walking in circles consuming tokens is **the** failure mode for
sub-agents on hard problems. The cap exists to prevent this.

### 3.2 The orchestrator follows the same cap

If a sub-agent escalates to the orchestrator (this conversation), the
orchestrator gets at most **10 attempts** to fix it personally. If the
orchestrator can't, **stop and report to the user**.

### 3.3 Attempt-counter scripts when needed

AI agents are bad at counting their own attempts. If unsure, write a
small verification-runner that maintains a counter file (e.g.
`scratch\attempts.txt`) and increments it on each F\* invocation. When
the counter hits 10, the script exits with a clear escalation message.

### 3.4 Sub-agent prompts: full context, brevity rules waived

When delegating to a sub-agent, include:

- The relevant section(s) of this file.
- The repo-wide `.github/copilot-instructions.md` highlights (no
  admit/assume, CRLF, no git, …).
- The specific lemma, its surrounding code (or a path to it), and any
  prior failed attempts.
- The escalation rule (§3.1) explicitly.

Brevity in agent prompts is false economy. Pay the tokens up front.

### 3.5 When delegation fails repeatedly, do it yourself

If two sub-agent dispatches on the **same** lemma both hit the 10-attempt
cap, the orchestrator must take over directly. Don't dispatch a third
agent on a problem that has already been demonstrated too hard for
delegated work.

## 3.6 Public signature hygiene (the four rules)

A **public** `Lemma`'s `requires (...)`, `ensures (...)`, or
`: Lemma (...)` body **must never** contain:

1. **`forall x. P x`** — convert to argument-form
   `(pf: (x: T) -> Lemma (requires <P's hypothesis>) (ensures P x))`.
   The lemma accepts the per-element proof function as an argument.
   Callers define a named helper lemma and pass it. This replaces
   `Classical.forall_intro` chains, which are SMT-pattern-fragile.

2. **`fun args -> expr`** — extract into a named top-level function
   `let my_fn args = expr`. If `expr` itself contains a `forall`,
   mark `my_fn` `[@@@ "opaque_to_smt"]` and provide companion
   `my_fn_intro` / `my_fn_elim` lemmas next to its definition.

3. **`if cond then A else B`** in a pre or post — split the lemma
   into two sibling lemmas: one with `requires cond` and conclusion
   `A`, another with `requires ~cond` and conclusion `B`. Naming
   convention: suffix with case (`_match` / `_nomatch`, `_in_range`
   / `_out_of_range`, etc.). If a unified form is useful, derive it
   as a thin wrapper calling both halves.

4. **`match e with | p1 -> ... | p2 -> ...`** in a pre or post —
   same treatment as `if`: split by branch.

**Why:** SMT compares syntactic shapes. Lambdas in posts skolemize
to fresh names that don't unify across call sites. `forall` triggers
are fragile across F\* versions. `if` in a post smuggles two lemmas
into one, multiplying per-caller query cost.

**Allowed locations** for these constructs:
- `decreases (...)` clauses (a measure, not a condition). Note: even
  here, prefer direct measures over `if`-guards — F\* accepts
  `(decreases (hi - lo))` directly when `lo, hi : nat` and the
  recursive branch only fires when `lo < hi`.
- Top-level type definitions where the expression is the *value*,
  not a logical proposition.
- Proof bodies (`let ... = body`) — SMT sees these only through
  the post, so internal lambdas are fine.

**Workflow when refactoring an existing public lemma**: bottom-up.
Fix the foundation first; consumers cascade naturally. Don't refactor
top-of-stack code while the bottom still has violations — every
foundation change will invalidate the consumer fixes.

### 3.6.1 Mechanical cascade tooling (proven 2026-05-23)

When a callback-form refactor of a foundational lemma triggers many
caller updates, **do not edit caller sites by hand at scale**. Use an
arity-aware cascade script. The recipe:

1. Build an arity table mapping each refactored lemma name → new
   total arity (including callback args).
2. For each call site, count top-level non-`#`-prefixed args. If
   one short of the new arity, append ` (fun _ -> ())`.
3. Multi-callback lemmas (2+ callback args) need a post-pass: a
   simple PowerShell/regex sweep replaces `(fun _ -> ())` with
   `(fun _ _ -> ())` etc. where the second callback is missing.
4. **Always back up before running** (see §2.3) — `.cascade-bak`
   suffix is conventional.
5. Verify the cascade-modified file builds before moving on. If
   not, the cascade missed something — manual fix on those sites,
   not a broader script rewrite.

The arity-1 `(fun _ -> ())` callback works because the caller's
existing `Classical.forall_intro pf` (or equivalent) provides the
forall fact to SMT, so the wrapper's pointwise goal closes
automatically. This pattern is **deliberately exploited** by the
refactor design — it lets old call sites continue working with
minimal change.

### 3.6.2 Status — hygiene refactor complete (2026-05-23)

H3 (`Core.FinSum`), H4 (`Core.Permutation.Sum`), and H5 (full scan)
are all complete. The entire `Core.*` tower has hygienic public
signatures and verifies clean from a cold cache. Any new `.fsti` or
`val` declaration **must** follow §3.6 from day one — there is no
longer any precedent for `forall`/`fun`/`if`/`match` in a Lemma
pre/post inside `Core.*`.

## 4. Resource budget (reminder)

From repo-wide rules:

- Peak Z3 memory **well under 4 GB** per `fstar.exe`.
- CPU load **under ~50%**. Single-threaded; no `--parallel N` with
  large `N`; no concurrent `fstar.exe` invocations.
- Per-lemma `--z3rlimit` **30–80**; factor if higher.

If verification is hitting the budget, the proof is wrong-shaped.
**Factor it.** Do not raise the budget.

## 5. The acceptance gates

See `plan.md` §5 for the list of stress-test lemmas that gate each
phase. The most important is **G4**:
`perm_product_to_multidistrib`. If that verifies clean in the new
tower, the architectural rewrite is validated.

---

**Last updated:** 2026-05-23 (added §3.6.1 cascade tooling recipe;
§3.6.2 hygiene refactor status — H3+H4+H5 complete).
