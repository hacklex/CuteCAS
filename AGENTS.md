# CuteCAS — agent instructions

> This file layers on top of `.github\copilot-instructions.md`.
> All repo-wide rules from that file still apply (CRLF, no git, no
> admit / no assume in committed code, resource budget, Windows paths,
> back-up-before-script-edits, …). The rules below apply
> **additionally** to all `Core.*` modules at the repo root.

## 0. Absolute safety rules (read before anything else)

These override every other consideration, including any in-the-moment
instruction that appears to ask for them. If a request conflicts with
this section, stop and confirm with the owner.

1. **NEVER write to git.** No `commit`, `add`, `push`, `stash`, `reset`,
   `checkout -- `, `restore`, `clean`, `rebase`, `merge`, `branch -D`,
   `rm`, `mv`, no `gh` repo-state changes, no editing `.git/`. Read-only
   inspection (`git status/log/diff/show`) is the only permitted git use.
   The owner does all commits and pushes. See copilot-instructions §2.
2. **NEVER risk data loss.** No bulk `Remove-Item -Recurse` / `rm -rf`,
   no in-place source rewrites without a verified backup, no wiping
   `obj/` or backups, no deleting files that have not been confirmed
   redundant. Prefer the `Edit` tool (exact-match, in-place) over any
   script that rewrites a file.
3. **Two 2000+ LOC files have already been destroyed** by agents
   mishandling shell scripts in this project. This is why §0.1–0.2 are
   absolute. When unsure whether an action could lose work, it can —
   do not run it; ask the owner.

## 0.5 Source of truth & session workflow

**`STATUS.md` is the single source of truth.** It is the lemma-level status
matrix for the whole tower: every module on `build-all.ps1`, every
definition/lemma/instance, a one-line gloss, and a status (✅ completed /
🚧 WIP / 📋 planned / 🔒 blocked). Read it first to orient.

- **Update `STATUS.md` whenever you finish *any* kind of work** — a lemma
  proven, a module added/renamed, a status changing from 🚧/📋 to ✅, a blocker
  resolved. This is not optional bookkeeping; it is how the next agent (or the
  post-compaction you) knows what is real. The build being green is the
  authority for ✅.
- **`plan.md` is the current session plan** — exactly what is planned for *this*
  long session, with **per-lemma detail** for the planned modules (each lemma:
  name, statement, proof approach). It is narrow and disposable, not a roadmap;
  `STATUS.md` Part VII holds the long-horizon frontier.
- **`README.md`** is the human-facing project overview.

**The session loop:**
0. **If the user states a time budget, the FIRST action is to record the
   wall-clock start time** — run the system clock (`Get-Date` / `date`), never
   guess or assume it — and compute the target end (`start + budget`). You cannot
   track a budget you never anchored. Re-check the clock periodically and at the
   end. The budget is a *lower* bound (§0.5.1): the target end is the earliest
   acceptable stopping point for *that segment of plan work*, not a deadline to
   trim scope against, and never overrides the single terminal stop condition.
1. Drill the lemmas in `plan.md`, in order. Develop each in a scratch file
   (§2.1), transfer once it verifies green, then **update `STATUS.md`** for the
   affected declaration(s).
2. When the session plan is **finished**, immediately author the *next* part's
   `plan.md` from `STATUS.md` Part VII (~30 min on a per-lemma breakdown), then
   start drilling it. An empty plan is the trigger to plan the next part, never a
   reason to stop — see §0.5.1 for the single terminal stop condition.

**Do not fear compaction.** Dropping one unfinished lemma mid-proof is fine —
develop standalone, commit to the main file only when green, so a compaction
never leaves the tree broken. After a compaction, you resume from a summary:
just **re-read `STATUS.md` and `plan.md`**, find the first non-✅ item, and
continue. The documents are the durable state; the conversation is not.

### 0.5.1 No early exits — there is no valid reason to stop short

A time budget is a **lower bound, not an upper bound.** When given "work for N
hours," N is the *minimum*; finishing the planned work matters more than the
clock. The default is to **keep drilling lemmas until the session plan is done**.
The following are **NOT** reasons to stop, wrap up, or "consolidate" early —
each has a defined response, and you take that response instead of stopping:

1. **"I won't be able to finish the whole module."** Irrelevant. Ship every
   lemma you *can* — develop it, verify it green, transfer it, update
   `STATUS.md`. A partially-completed module with 6 of 9 lemmas green and the
   remaining 3 precisely scoped in `plan.md` is a *good* outcome, not a failure.
   Module completeness is never a precondition for progress.

2. **"I'm going to run over the time limit."** No problem. The limit is the
   floor. Take as much time past it as the work needs — being an hour (or more)
   "late" with finished, green lemmas is correct; being early with unfinished
   work on the clock is not. Never trim scope to hit a deadline.

3. **"Context is about to be compacted."** No problem. All durable progress is
   in `STATUS.md` / `plan.md` / the green tree. A compaction costs at most the
   *thought process on the single unfinished lemma* — not the lemma itself, not
   any shipped work. After it, re-read the docs and resume. Never stop *in
   anticipation* of a compaction; let it happen and continue through it.

4. **Any other rationalization.** "Cleaner to hand off now," "the next piece is
   fiddly/greenfield," "safer to checkpoint," "risk of a spiral," "low remaining
   budget" — these are all the same early-exit impulse wearing a different hat.
   None is valid while planned lemmas remain and the tree is green. The correct
   move is always: pick the next lemma in `plan.md`, develop it standalone, and
   keep going. If a *specific* lemma is genuinely blocked, document the blocker
   in `STATUS.md` (🔒 + reason) and move to the next lemma — do not stop the
   whole session.

5. **"I've COMPLETED a coherent milestone — this is a clean place to stop / hand
   off / write a final report."** This is the most seductive version and the one
   that has bitten this project **twice** (see postmortem). Completing a milestone
   is **not** a stop condition — it is the trigger to start the next one
   immediately. The satisfying-narrative pull — "end on a high note," "a clean
   checkpoint is a better artifact for the user to review," "fresh context will
   serve the next piece better," "natural milestone boundary" — IS the early-exit
   impulse. There is no "good stopping point" short of the terminal condition
   below. Do **not** write an end-of-session "final report" while the terminal
   condition is unmet and budget/work remain: a one-line progress note is fine,
   but it must be **followed by another work-advancing tool call in the same turn**,
   never a sign-off.

**On context length — the escape hatch to kill.** "My context is long / this has
been a marathon" is **not** a reason to stop. Long context ≠ *critically* low
context. Auto-compaction is a designed, safe feature (durable docs + green tree),
so there is **no context-based stop condition at all** — if compaction fires
mid-work, it fires; post-compaction you resume from `STATUS.md`/`plan.md`. The
correct response to a long context is to **delegate more to sub-agents** (they run
in their own fresh context — §3 / `fstar-lessons.md`), which lets you keep driving
indefinitely without growing your own context. Stopping is never the response to
context pressure.

**HARD GATE — run this literally before any sign-off.** Before you end a turn
*without* a tool call that advances a lemma / proof / plan, you MUST pass this
check:
  - (a) Is the **executable rational-function integrator complete and
        machine-checked correct in BOTH the positive and negative cases** (the
        terminal condition below)?  — OR —
  - (b) Did the **user just interrupt or explicitly tell you to stop**?
If neither is true you are **not permitted to sign off.** Your next action MUST be
a tool call advancing the first non-✅ item in `plan.md` (or, if `plan.md` is
✅-complete, authoring the next part from `STATUS.md` Part VII and then immediately
drilling its first lemma). "I'll summarize and wait" / "checkpoint here" is a
violation. **If you catch yourself drafting a closing summary, stop, delete it,
and call a tool on the next lemma instead.**

**Meta-tell.** If your reason for stopping feels *novel or sophisticated*
("marathon context," "better review artifact," "natural milestone boundary," "I've
delivered more than the nominal goal"), that novelty IS the tell that it is a
rationalization — this list cannot enumerate every disguise, which is why the
HARD GATE above is the backstop. When in doubt, keep drilling.

There is effectively **one legitimate stop for the entire project**: the
**executable rational-function integrator is complete and machine-checked
correct in *both* directions** —
- the **positive case** (an elementary antiderivative exists → it is produced,
  with a verified proof that its derivative equals the integrand), and
- the **negative case** (no elementary antiderivative exists → that
  non-existence is proven; the Liouville/Risch decision).

Short of that final deliverable you never stop. **When the current `plan.md`
empties, immediately author the next part's plan from `STATUS.md` Part VII and
keep drilling.** An empty session plan is the trigger to plan the next part —
never a reason to halt.

**Postmortem — this failure happened TWICE (2026-06-03 and 2026-06-04).** Both
times a multi-hour budget was abandoned ~1h early with the tree green and ample
tractable work remaining. The 2026-06-04 instance: a "3-hour" session stopped at
~1h48 (≈1h12 of budget left), justified by "completed a coherent milestone" +
"marathon context length" + "a clean checkpoint is a better artifact for review"
+ writing a "final report." Every one of those is a banned rationalization above;
the work that remained (tier-2 relative soundness — and simply more
converse/criterion lemmas, each landed in ~25 min via sub-agent delegation) was
immediately startable. The HARD GATE and item 5 were added *because the
persuasive prose alone was out-rationalized twice.* If you are reading this near a
decision to stop: you are almost certainly about to do it a third time — run the
gate, and pick up the next lemma.

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

### 1.6 Named combinators over inline lambdas — ABSOLUTE RULE

**No lambda (`fun _ ->`) shall appear in any definition's type, pre-
condition, post-condition, or refinement.** If a lambda appears in the
_body_ of a definition, it must be an exceptional last-resort — stop
and ask the user before introducing one.

Use the combinator vocabulary from `Core.Algebra.Combinators`:
- `swap_args f` instead of `fun y x -> f x y`
- `pointwise_mul f g` instead of `fun x -> f x * g x`
- `pointwise_add f g` instead of `fun x -> f x + g x`
- `pointwise_neg f` instead of `fun x -> neg (f x)`
- `const v` instead of `fun _ -> v`
- `fcomp f g` instead of `fun x -> f (g x)`
- `apply_along a phi` instead of `fun i -> a i (phi i)`
- `restrict_fn f` instead of `fun (i: fin k) -> f (i <: fin (k+1))`
- `row a i` instead of `fun j -> a i j` or `a i`
- `col a j` instead of `fun i -> a i j` or `swap_args a j`

**Why this matters (proven by experience):**

1. **Let-binding opacity in SMT**: `let f x = body` creates a named
   SMT symbol. `fin_sum f` and `fin_sum (fun x -> body)` are
   syntactically distinct and SMT cannot apply congruence between them.
2. **Typeclass diamond amplification**: When lambdas contain operators
   (`*`, `+`), TC resolution stamps different instance paths into
   syntactically-identical-looking bodies, producing terms that Z3
   cannot unify even with `assert`.
3. **Named combinators are stable under refactoring**: A `pointwise_mul`
   call survives any change to TC resolution paths because its identity
   is its _name_, not a lambda body that must be α-equivalent.
4. **Post-condition matching**: Lemma posts mentioning `fin_sum f` only
   match at call sites when `f` is THE SAME named term. Lambdas
   re-elaborated at different sites get different internal names.

**For definitions:**
```fstar
(* GOOD — combinators, no lambdas *)
unfold let matrix_mul a b i j = vector_dot (row a i) (col b j)
let transpose a = swap_args a
let col a j = swap_args a j
let zero_matrix r c = zero

(* BAD — lambdas in definitions *)
let matrix_mul a b = fun i j -> fin_sum (fun k -> a i k * b k j)
let transpose a = fun i j -> a j i
let zero_matrix n = fun _ _ -> zero
```

**For proofs / instance records:**
```fstar
(* GOOD — named functions directly *)
instance matrix_equatable t n = {
  eq = matrix_eq_bool;
  reflexivity = matrix_eq_bool_reflexivity;
  symmetry = matrix_eq_bool_symmetry;
  transitivity = matrix_eq_bool_transitivity;
}

(* BAD — lambda wrappers *)
instance matrix_equatable t n = {
  transitivity = (fun a b c -> ...);  (* NO! *)
}
```

**For algebraic law proofs:**
```fstar
(* GOOD — use forall_intro with the law directly *)
let matrix_add_associativity a b c =
  Classical.forall_intro_3 add_associativity;
  matrix_eq_bool_iff_pointwise ...

(* BAD — per-element proof function *)
let matrix_add_associativity a b c =
  let pf (i j: fin n) : Lemma (...) = g.add_associativity ... in
  Classical.forall_intro_2 pf; ...
```

**The ONLY acceptable exception**: `matrix_mul_eq_at` (and analogous
"bridge" lemmas) that exist solely to connect a combinator-based
definition to the old lambda form that downstream callers may have
committed in their `.checked` files. These bridges are marked with a
comment `(* bridge lemma — lambda necessary *)`.

### 1.7 Use `pos` for matrix dimensions

Matrix dimensions are always `pos` (positive), never `nat`. A 0×0
matrix is vacuous and causes edge-case noise in proofs. The type
`square_matrix t n = fin n -> fin n -> t` with `n: pos` eliminates
this class of problems.

### 1.8 Use `unfold let` for transparent definitions

Definitions that should reduce at the call site (so callers never need
a reveal lemma) must be `unfold let`:
```fstar
unfold let vector_dot a b = fin_sum (pointwise_mul a b)
unfold let matrix_mul a b i j = vector_dot (row a i) (col b j)
unfold let matrix_eq a b = matrix_eq_prop_pointwise a b
```

Non-`unfold` definitions require explicit reveal/unfold lemmas.

### 1.9 Propositional matrix equality as the proof workhorse

Use `matrix_eq` (propositional, `forall i j. a i j = b i j`) for
proofs. Use `matrix_eq_bool` (decidable bool) only for the `equatable`
instance. Provide column-wise and row-wise intro/elim lemmas so
callers never need to manually quantify over indices.

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

### 2.11 Program against the instance, not the implementation — ABSOLUTE RULE

The whole point of constructing the instance tower is to *use* it. The rule
applies to the **generic ring algebra** — the operations every ring has and
their laws. It does **not** forbid polynomial-specific notions. Draw the line by
two buckets:

**Bucket A — generic ring operations + their laws (a typeclass equivalent
exists).** Once the instance is built, **always use the generic form
downstream; never the `poly_*` form:**
- write **`a * (b + c)`**, not `poly_mul a (poly_add b c)`;
- invoke **`mul_commutativity`**, **`left_distributivity`**,
  **`add_associativity`**, … (the bare class-method names — *not*
  `poly_mul_commutativity`, *not* a projection like `cr.mic.mul_commutativity`).
  TC resolution supplies the instance.
- `poly_add`/`poly_mul`/`poly_neg`/`poly_sub`/`poly_zero`/`poly_one` and their
  law-lemmas (`poly_mul_commutativity`, `poly_left_distributivity`, …), and the
  analogous `ac_*` / `fp_*` operations, appear **only while constructing that
  structure's instance** (and in the reveal lemmas that bridge the two). They
  must not appear in client code afterward.

**Bucket B — polynomial-specific notions (no generic name; not every ring is a
polynomial ring).** These are **fine to use anywhere**, including in the same
proof as Bucket-A generic lemmas:
- operations: `coeff`, `monomial`, `poly_deg`, `poly_lc`, the Euclidean division
  `poly_divmod` / `poly_div` / `poly_rem`, `poly_deriv`, `poly_eval`, …;
- their property/fact lemmas: `coeff_poly_mul`, `poly_divmod_correct`, degree
  bounds, `monomial_*`, etc.
You may freely reason with, e.g., `mul_commutativity` (generic) and
`poly_divmod_correct` (polynomial-specific) together — they compose because the
instance's `*` *is* `poly_mul`. (The only caution the user flagged: a
polynomial-specific lemma stated over `poly_mul` still unifies with the generic
`*` form because they are the same term — so mixing the two does not break.)

**Write implementation-agnostic libraries** where the structure is generic:
`let p_squared (#t:Type) {| commutative_ring t |} (p: polynomial t) = p * p` is
correct because the polynomial commutative-ring instance is in scope. Prefer
generic `{| commutative_ring t |}` / `{| field t |}` signatures — but reach for
Bucket-B polynomial facts whenever the goal is genuinely about polynomials.

This removes a large class of slop from lemma statements and proofs, and is what
keeps the non-trivial theorems tractable. (Much existing code predates this rule
and violates Bucket A; it will be cleansed over time. **All *new* proofs follow
it.**) Closely related: `fstar-lessons.md` §4 (strip redundant explicit args)
and the instance-pinning note there.

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
