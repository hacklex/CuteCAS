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
`Core.Polynomial.Class`, `Core.Polynomial.Class.Div`, `Core.Fractions`,
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

## 2. Git: never run git commands

**The agent does not interact with git.** The repository owner reviews and
commits changes manually.

- Do **not** run `git add`, `git commit`, `git push`, `git stash`, `git reset`,
  `git checkout`, `git rebase`, or any other git subcommand.
- Do not create or switch branches.
- Do not invoke GitHub CLI (`gh`) for repo state changes.
- You may *read* state passively only if strictly necessary (e.g., `git status`
  to answer a question the user asked), but prefer not to. The user knows
  what's in their working tree.

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
- Per-lemma `--z3rlimit` should be in the **30–80** range. If a single
  lemma needs `--z3rlimit > 80` to close, that is a code smell: factor it,
  rewrite it, or split the file.
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
- **NEVER write lambdas in postconditions, lemma statements, or `prod_range
  /fin_sum/sum_over_fns_to` arguments.** F\* does not reduce lambda bodies
  through SMT-equality reliably; you will produce unprovable lemmas. Instead,
  give every function used in a lemma statement a top-level (or `private let`)
  name, take any captured implicits as parameters of that named function,
  and write lemma statements using the **name**. Examples of mandatory
  factoring:
  - `prod_range (fun (k:fin n) -> a i k * b k j) 0 n` → introduce
    `let row_col_term (a b: ...) (i j: fin n) (k:fin n) : t = a i k * b k j`,
    then `prod_range (row_col_term a b i j) 0 n`.
  - `sum_over_fns_to n m (fun phi -> prod_range (inner_term phi) 0 n)` →
    introduce a named outer term too.
  - Lambdas inside proof *bodies* (between `let .. in` etc., not on the
    SMT side) are fine — the rule is about postconditions and lemma
    statements and any argument that SMT will need to unify across calls.
- The "no lambdas" rule is what doomed the old `..\new\` tower's Det.Mul:
  hours were spent on `fun (k:fin n) -> ...` lambdas that SMT could not
  bridge to other definitions. Don't repeat that mistake.

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

## 8. Working with the plan

There is a long-running session plan at
`C:\Users\Alex\.copilot\session-state\<session-id>\plan.md`. Agents read it
at session start, update it at meaningful milestones, and respect the phase
structure laid out there. The phase plan and the rules above are
authoritative; this `.github/copilot-instructions.md` file just makes the
non-negotiables explicit to any future agent that hasn't seen the plan yet.

## 9. F\* MCP server

When available, use the **fstar-mcp** tools (`fstar-create_session`,
`fstar-typecheck_buffer`, `fstar-get_proof_context`, etc.) for interactive
verification instead of spawning `fstar.exe` from the command line. The MCP
server gives incremental feedback, proof context, and hover information
without full-module re-verification overhead.
