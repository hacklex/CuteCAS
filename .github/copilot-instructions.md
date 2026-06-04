# Copilot / agent instructions for this repository

This repository is a Windows F\* sandbox driving the **CuteCAS** project: an
in-progress verified Risch symbolic integrator (purely transcendental case)
built on a typeclass tower of algebraic structures.

## 0. Layout and module naming

The repository is **flat**: all source `.fst` / `.fsti` files live at the
repository root (`c:\Projects\CuteCAS\`). There is no `core\`,
`new\`, or `proto\` subdirectory anymore — those folders were
consolidated into the root in the 2026-05-25 cleanup. Run F\* from the
repo root with `--include . --cache_checked_modules --cache_dir obj`.

All actively developed modules live under the **`Core.*`** namespace
(e.g. `Core.Algebra`, `Core.Algebra.Notation`, `Core.FinSum`,
`Core.Permutation`, `Core.Permutation.Enum`, `Core.Permutation.Sum`,
`Core.Matrix`, `Core.Matrix.Ring`, `Core.Matrix.Determinant`,
`Core.Polynomial`, `Core.Polynomial.Div`, `Core.Polynomial.GCD`,
`Core.Polynomial.Derivative`, `Core.Polynomial.SquareFree`,
`Core.Fractions`, `Core.AlgebraicConstant`, `Core.Derivation`,
`Core.Risch.Hermite`, `Core.Risch.LRT`, `Core.Risch.Rational`,
`Core.Tactics.CanonRing`, `Core.Tactics.CanonCommGroup`, …).
New modules MUST use this namespace.

The earlier `FStar.CAS.*` and `FStar.Algebra.*` names are **retired**:
the old tower was discarded when the fine-grained-TC `Core.*` rewrite
landed. Do not re-introduce those names.

Heavy modules (≳400 LOC with a clear public/private separation) ship as
`.fst` + `.fsti` pairs: signatures and class declarations in `.fsti`, proofs
and helper lemmas in `.fst`.

Legacy artifacts live under `legacy\` (currently just
`legacy\AlgebraTypes.fst`, the old monolithic algebraic-types module).
They are kept for reference only — **not** part of the new tower, not
maintained, not on the include path.

Agents working in this repo MUST follow the rules below.

## 1. Line endings: CRLF everywhere

All files in this repository use **Windows line endings (CRLF, `\r\n`)** —
source files (`.fst`, `.fsti`), documentation (`.md`), scripts, everything.

- When creating or editing files, write CRLF newlines.
- Never introduce lone LF (`\n`) characters. Emacs and other editors with
  Unix-mode defaults will visibly show `^M` glyphs if any line breaks are
  CRLF in an otherwise-LF file, and vice versa — the result is editor-level
  noise that we do not tolerate.
- If a tool emits LF-only content, normalize it to CRLF before committing.
- A quick sanity check after editing:

  ```powershell
  $b = [System.IO.File]::ReadAllBytes("path\to\file");
  $crlf = 0; $lone = 0;
  for ($i=0; $i -lt $b.Length; $i++) {
    if ($b[$i] -eq 10) {
      if ($i -gt 0 -and $b[$i-1] -eq 13) { $crlf++ } else { $lone++ }
    }
  };
  "CRLF=$crlf  LoneLF=$lone"
  ```

  `LoneLF` must be `0`.

## 1.5. Script edits: back up first, verify after

> **This rule has already been violated at a cost.** Two large (2000+ LOC)
> source files were destroyed by agents mishandling shell scripts. Treat
> every script-driven edit as live ordnance. If you cannot guarantee a file
> survives an operation, do not run the operation — use the `Edit` tool
> (exact-match, in-place) or hand the step to the owner.

When making **script-driven** edits to source files (e.g., PowerShell loops,
`Set-Content`, regex passes, mass rename), follow this rule **strictly**:

- **Back up the file first** to a side path before the script runs:
  `Copy-Item path\to\file.fst path\to\file.fst.bak` (or to a temp folder).
- **Sanity-check the file IMMEDIATELY after** the script writes it:
  - line count via `(Get-Content path).Count` matches expectation,
  - first/last few lines look intact,
  - if it's an F\* source: try running it.
- **Known PowerShell footgun**: `Get-Content` returns lines WITHOUT line
  terminators; piping the result into `Set-Content -NoNewline` will
  CONCATENATE all lines into ONE giant line with no separator, silently
  destroying the file. NEVER chain those two together on real source files.
  To safely write line arrays back, use
  `[System.IO.File]::WriteAllLines($path, $lines)` (which handles
  separators correctly) or pipe to `Set-Content` WITHOUT `-NoNewline`.

If you skip the backup and corrupt a file, the user will (rightly) be upset.
Treat any non-trivial script edit as destructive until proven otherwise.

## 2. Git: NEVER write — this is an absolute, non-negotiable prohibition

**The agent NEVER performs any git operation that writes, moves, or could
destroy data.** The repository owner — and ONLY the owner — stages, commits,
pushes, and manages branches. This is not a preference; it is a hard safety
boundary.

> **Why this rule is absolute.** AI agents have *already destroyed two large
> (2000+ LOC) source files* in this project through careless shell handling.
> Lost work is unacceptable. Every rule below exists to make a repeat
> impossible. When in doubt, do nothing and ask the owner.

**FORBIDDEN — never run any of these, under any circumstance, even if asked
mid-flow without an explicit, deliberate confirmation:**

- `git commit`, `git add`, `git push`, `git stash`, `git stash pop`
- `git reset` (any mode — `--soft`, `--mixed`, and especially `--hard`)
- `git checkout -- <path>` / `git restore` (discards working-tree edits)
- `git clean` (deletes untracked files — this is how uncommitted work vanishes)
- `git rebase`, `git merge`, `git cherry-pick`, `git revert`
- `git branch -D` / `git branch -d`, creating or switching branches
- `git rm`, `git mv`
- `gh` (GitHub CLI) for any repo-state change (PRs, pushes, branch ops)
- Editing anything under `.git/` directly.

**ALSO FORBIDDEN — non-git operations that risk the same data loss:**

- Bulk file deletion / overwrite via shell (`Remove-Item -Recurse`, `rm -rf`,
  `del /s`) without first confirming, per item, that the content is redundant.
- The `Get-Content | Set-Content -NoNewline` footgun (see §1.5) and any
  pipeline that rewrites a source file in place without a backup.
- Wiping `obj/`, deleting backups, or removing scratch files that have not
  been confirmed redundant.

**ALLOWED (read-only):** passive inspection only — `git status`, `git log`,
`git diff`, `git show`, `git stash list`. Use these solely to answer a
question; never as a step toward a write. The owner knows their working tree.

If a task seems to require a git write (e.g. "commit this", "undo my changes"),
**stop and tell the owner to run it themselves** (they can use `! <command>`
in the session). Do not run it for them.

## 3. Resource budget when running F\*

F\* verification can be expensive. Hard constraints on this machine:

- **Memory**: keep peak resident memory **well under 4 GB** per `fstar.exe`
  invocation. If a query needs more, the proof is wrong-shaped — split it,
  factor lemmas out, or lower the rlimit, do not throw memory at it.
- **CPU**: keep verification load **under ~50% of available CPU**. Do not
  spawn parallel `fstar.exe` processes. Do not run `--parallel N` with
  large `N`. Single-threaded verification is the default.
- Verify one module at a time. Do not kick off whole-tree rebuilds
  speculatively.
- **DO NOT use `#push-options` / `#pop-options` in this project.** All proofs
  in this project verify under F\*'s default limits. When verification fails,
  the problem is proof structure (missing lemma, wrong decomposition, SMT
  can't see a fact), NOT resource exhaustion. If you temporarily use
  `#push-options` during proof development to isolate a failure, **remove it
  once the proof is done** — you almost certainly didn't need it.
- If a lemma genuinely won't verify under defaults after structural fixes,
  that is a signal to decompose further (factor out a helper lemma, add an
  intermediate assertion), not to bump rlimit.
- One module per file. When a `.fst` grows past ~600 LOC or ~25 lemmas,
  split it along a natural seam.
- Always use the `.checked` cache (`--cache_checked_modules --cache_dir obj`).
  Targeted invalidation only — never wipe the whole `obj/` dir without
  reason.

## 4. No `admit()` and no `assume`

The Risch verification project's headline deliverable is "no admits and no
assumes". Both soundness (returned antiderivative differentiates to the
input) and completeness (Liouville) must be fully proven.

- Do not insert `admit()`, `assume`, `magic ()`, or other proof-skipping
  primitives in any committed code.
- If a proof is stuck, factor it, add a stronger lemma, or ask for guidance.
  Do not paper over with `admit()`.

## 5. F\* installation hygiene

- F\* is installed at `C:\FStar` on this machine; `fstar.exe` is on `PATH`.
- New F\* builds are installed by **erasing `C:\FStar` entirely** and
  unpacking the fresh build in its place. Do **not** keep multiple F\*
  installs around.
- Do **not** use WSL or attempt a Linux-side F\* install. This project is
  Windows-native.

## 6. Style conventions

- snake_case for values, PascalCase for types, all-lowercase for module
  aliases.
- Operator overloads (`+`, `*`, `=`, `-`) only on single-type structures
  (rings, fields). Heterogeneous operations (e.g. scalar multiplication)
  use named functions or distinct symbols.
- Prefer explicit lemma invocations over `Classical.forall_intro_*` +
  `reveal_opaque` + SMT-pattern auto-firing. Explicit chains survive F\*
  evolution.
- Per-lemma `let ( * ) = r.mul in …`-style bindings to short-circuit
  typeclass resolution.
- **ABSOLUTE: no lambdas in definitions, postconditions, preconditions,
  or type refinements.** Use named combinators from
  `Core.Algebra.Combinators` (`swap_args`, `pointwise_mul`,
  `pointwise_add`, `const`, `fcomp`, `apply_along`, `restrict_fn`).
  Use `row`/`col` instead of partial application of a matrix. Use
  `vector_dot` instead of `fin_sum (fun k -> ...)`.
  Lambdas in proof bodies are acceptable only as a last resort; stop
  and ask if you feel one is needed.
- **Instance records list named functions directly** — no lambda wrappers:
  ```fstar
  instance foo = { op = named_op; law = named_law_lemma }
  (* NOT: { op = (fun x y -> ...); law = (fun a b c -> ...) } *)
  ```
- **Use `Classical.forall_intro_N` with the law directly** when the law's
  type matches, rather than writing per-element proof helpers:
  ```fstar
  Classical.forall_intro_3 add_associativity  (* good *)
  (* NOT: let pf i j = add_associativity ... in forall_intro_2 pf *)
  ```
- Matrix dimensions are `pos`, never `nat`. `square_matrix t n` with
  `n: pos`.
- Use `unfold let` for definitions that should be transparent (e.g.
  `vector_dot`, `matrix_mul`, `matrix_eq`).
- The "no lambdas" rule is what doomed the old tower's Det.Mul and
  me_col_k_is_zero: hours were spent on `fun (k:fin n) -> ...` lambdas
  that SMT could not bridge across TC-instance boundaries. The fix that
  finally worked: replace all named `let f x = ...` with inline
  combinator calls so every `fin_sum` argument is a single named term.

## 7. Proof development methodology

When developing new lemmas or proofs:

### 7.1 Isolate new work in temporary files

Never re-verify already-proven modules. When working on a new lemma:

- Create a **temporary scratch file** (e.g. `Scratch.fst`) that `open`s the
  already-verified modules (their `.checked` files in `obj/` will be reused).
- Prove the lemma in the scratch file first, then move it to its final home
  once verified.
- This avoids wasting minutes re-checking hundreds of lines of proven code
  on every iteration.

### 7.2 Decompose proofs into small lemmas

Do NOT write monolithic proof bodies. Factor out every non-trivial
sub-fact as its own named lemma. Examples of obvious factoring candidates:

- `minor (transpose m) i j = transpose (minor m j i)` — separate lemma.
- Any indexed-value equality (e.g. showing two matrix expressions agree at
  every slot) — write an explicit formula for each side's `(i,j)`-th entry
  and show they refer to the same original matrix slot.
- Any `fin_sum` congruence bridge — wrap in a one-line helper that calls
  `fin_sum_congruence_cr`.

Small lemmas are easier for Z3, easier to debug, and reusable.

### 7.3 Use sliding `admit()` / `assert()` to pinpoint failures

When a lemma body fails verification, do **NOT** rewrite the entire body
speculatively. Instead:

1. Insert `admit()` at the END of the failing body — confirm the lemma
   passes (proving the setup code is fine, only the conclusion is wrong).
2. **Slide the `admit()` upward** between statements to find the exact
   statement that breaks.
3. When you find the failing statement, insert `assert (fact_you_expect)`
   followed by `admit()` to test whether the precondition you think holds
   actually does.
4. Once you identify the exact gap, fix ONLY that gap.

This is the **only** acceptable debugging workflow for stuck proofs.
Blind full-body rewrites are forbidden — they waste verification time and
often introduce new issues.

### 7.4 `admit()` is a debugging tool, not committed code

Rule §4 still applies: no `admit()` in final committed code. But during
development iterations, `admit()` is the correct way to isolate failures.
Remove all `admit()` calls before declaring a lemma done.

## 7.5 Delegate lemma proofs to sub-agents — be economical with context

Compaction is survivable (§8), but context is still worth conserving. The big
win: **keep the main context focused on the big picture and hand individual
lemma proofs to sub-agents.** A small lemma proved in a fresh agent context does
not suffer from — and does not add — the irrelevant litter of the orchestrating
session. So:

- **Dispatch atomic lemmas to agents; orchestrate from the main loop.** You hold
  the plan and the architecture; agents grind out one concrete proof each.
- **Hand each agent a precise, self-contained task:** the exact lemma statement
  to prove, and — when you are confident a particular definition/lemma is
  *unavoidable* for the proof — point to it by name (and module) so the agent
  doesn't burn tokens rediscovering it. Give directions only where they reliably
  save effort; don't over-script.
- **Every agent prompt must require following `fstar-lessons.md`** (the proof
  checklist: no signature lambdas, no `if`/`match` in specs, minimize explicit
  args, no redundant reflexivity when `elim_equatable_laws` is present, instance
  pinning, etc.). Either tell the agent to read it, or inline the relevant rules.
- **The time budget applies to *you*, not to agents.** Agents receive concrete
  tasks and must return **either the expected result (green, admit-free) or an
  honest "could not prove X"** — never lazy prose about how a lemma "would take
  1000 lines / several sessions." If an agent stalls into that, the task was too
  big: **split it into smaller lemmas and dispatch those.**
- **Never dispatch a genuinely too-big task.** Keep each atomic unit small enough
  for an agent to finish in one session. Right-sizing the decomposition is your
  job, not the agent's.

(`AGENTS.md` §3 covers the agent escalation cap and sub-agent prompt rules;
`fstar-lessons.md` is the shared proof-style checklist for all agents.)

## 8. Working with the plan — `STATUS.md` is the source of truth

**`STATUS.md` (repo root) is the single source of truth.** It is the
lemma-level status matrix for the whole tower (every module, every
definition/lemma/instance, a gloss, a ✅/🚧/📋/🔒 status). Read it first.
**Update it whenever you finish any kind of work** (a lemma proven, a module
added, a status changed, a blocker resolved) — the green build is the authority
for ✅.

- **`plan.md`** is the *current session* plan only: exactly what is planned for
  this long session, with per-lemma detail for the planned modules. It is narrow
  and disposable; the long-horizon frontier lives in `STATUS.md` Part VII.
- When the session plan finishes with > 30 minutes left, author the next part's
  `plan.md` from `STATUS.md` Part VII, then drill it.
- **Compaction-resilient:** develop each lemma standalone and transfer to the
  main file only once green, so the tree is never broken across a compaction.
  After a compaction, re-read `STATUS.md` + `plan.md`, find the first non-✅
  item, and continue. The documents are the durable state, not the conversation.

**Anchor the clock first.** Whenever the user explicitly states a time budget,
your *first* action is to record the wall-clock start time from the system clock
(`Get-Date` / `date` — never guess it) and compute the target end. You cannot
track a budget you never anchored; re-check the clock periodically and at the end.

**No early exits.** A time budget is a *lower* bound, not an upper bound — keep
drilling lemmas until the session plan is done. None of the following is a reason
to stop early; each has a response you take *instead* of stopping:
- *"Can't finish the whole module"* → ship every lemma you can, record progress
  in `STATUS.md`/`plan.md`. Module completeness is never a precondition.
- *"I'll run overtime"* → fine; the limit is the floor. Take the time the work
  needs. Late-with-green-lemmas beats early-with-unfinished-work.
- *"Context is about to compact"* → fine; durable progress is in the docs and the
  green tree. A compaction costs at most the thought process on one unfinished
  lemma. Let it happen and continue; never stop in anticipation of it.
- *"I've COMPLETED a coherent milestone — clean place to stop / hand off / write a
  final report"* → THE rationalization that broke this rule twice (2026-06-03,
  -04). Completing a milestone is the trigger to start the next one, never a stop.
  "End on a high note / better review artifact / fresh context for the next piece"
  is the same impulse. Do not write an end-of-session "final report" while work
  remains — a one-line progress note is OK *only if followed by another
  work-advancing tool call in the same turn.*
- *"My context is long / marathon session"* → not a stop. Long ≠ *critically* low;
  compaction is safe (durable docs). There is **no context-based stop at all.**
  The response to long context is to **delegate more to sub-agents** (fresh
  context each), not to stop.
- *Any other rationalization* ("cleaner to hand off," "next piece is fiddly,"
  "safer to checkpoint," "low budget," "more than the nominal goal already") is
  the same impulse in disguise — if your reason feels *novel/sophisticated*, that
  novelty is the tell. Not valid while planned lemmas remain. If one specific
  lemma is blocked, mark it 🔒 in `STATUS.md` and move to the next.

**HARD GATE — before any sign-off.** You may end a turn without a
work-advancing tool call ONLY if (a) the executable integrator is complete +
proven in both cases, OR (b) the user just interrupted/told you to stop.
Otherwise your next action MUST be a tool call on the first non-✅ item in
`plan.md` (or author the next part from `STATUS.md` Part VII, then drill it). If
you catch yourself drafting a closing summary, delete it and pick up the next
lemma. See `AGENTS.md` §0.5.1 for the full rule + postmortem.

The only legitimate stop is the whole project's terminal goal: a complete
executable integrator, machine-checked correct in **both** the positive case (an
elementary antiderivative exists → produced and verified) and the negative case
(none exists → proven; Liouville/Risch decision). When the current `plan.md`
empties, immediately author the next part from `STATUS.md` Part VII and keep
drilling — an empty plan triggers the next plan, it never ends the session.

`AGENTS.md` §0.5 / §0.5.1 state this workflow in full; the design/safety rules
there and above remain authoritative. (The former
`C:\Users\Alex\.copilot\session-state\<id>\plan.md` location is retired.)

## 9. F\* MCP server

When available, use the **fstar-mcp** tools (`fstar-create_session`,
`fstar-typecheck_buffer`, `fstar-get_proof_context`, etc.) for interactive
verification instead of spawning `fstar.exe` from the command line. The MCP
server gives incremental feedback, proof context, and hover information
without full-module re-verification overhead.

## 10. IDE-accelerated refactoring tools

The `tools\` directory contains IDE-accelerated refactoring scripts:

- **`tools\fstar-refactor-ide.ps1`** — batch transforms per-definition.
  Uses F\*'s IDE `full-buffer` protocol for incremental verification
  (10-100× faster than standalone `fstar.exe`). Modes: `count`, `list`,
  `get`, `transform`. Built-in safety checks: definition count, line count,
  CRLF integrity, and F\* segment parse count (all compared pre vs post).
  Transform scripts live in `tools\transforms\*.ps1`.

- **`tools\remove-push-pop.ps1`** — removes `#push-options`/`#pop-options`
  pairs. Processes last-to-first; each removal is verified by the IDE
  before writing.

Usage example:
```powershell
# Count definitions in a file
.\tools\fstar-refactor-ide.ps1 -File Foo.fst -Mode count

# Run a transform (verifies each change, rolls back failures)
.\tools\fstar-refactor-ide.ps1 -File Foo.fst -Mode transform `
    -Script .\tools\transforms\drop-fin-casts.ps1 -LogFile log.txt

# Remove unnecessary push-pop pairs
.\tools\remove-push-pop.ps1 -File Foo.fst -LogFile log.txt
```

These tools are **safe by construction**: every edit is verified by the F\*
IDE before being committed to disk. Failures are rolled back automatically.

## 11. Proof style: why verification succeeds under defaults

This project's proofs are structured as **explicit lemma chains** — each step
invokes a specific lemma, giving Z3 a series of small obligations rather than
one big one. This style means:

- Z3 never needs high fuel/ifuel (we don't rely on recursive unfolding).
- Z3 never needs high rlimit (each individual obligation is trivial).
- When verification *fails*, it's because SMT can't see a needed fact
  (wrong decomposition, missing intermediate lemma), never because it
  ran out of time searching.

Corollary: **never blame resource limits for a failed proof.** The fix is
always structural: factor, assert an intermediate, or invoke a missing lemma.
