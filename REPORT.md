# Autopilot report

> Running document for decisions made during autonomous work in `core\`.
> Each entry is a small report of what I did and why, plus any questions
> I'd have asked if you were online. Read top-down newest-first.

## Format

```
### YYYY-MM-DD HH:MM  <phase> <short title>
**What:** one-line summary.
**Why:** rationale.
**Decision made on your behalf (if any):** ...
**Question I'd have asked (if any):** ...
```

---

### 2026-05-22 ~late  Phase 4 (matrix tower)  MultiDistrib ✅
**What:** Ported `FStar.CAS.Matrix.MultiDistrib.fst` (675 LOC) →
`Core.Matrix.MultiDistrib.fst`. Verified clean on first try. Contains
the Cauchy–Binet kernel identity `prod_range_of_fin_sum` (∏ Σ = Σ ∏
over functions), the workhorse for `det(MN) = det M · det N`.
**Why:** Direct prerequisite for `Determinant.Mul`. Was the blocker in
the old `new\` tower because the diamond made `*` opaque in the
elaboration of `matrix_mul_eq_at`. In the new tower, no diamond exists,
so the proof transcribes mechanically.
**Decisions made on your behalf:**
- Dropped the legacy `mm: mul_monoid t{mm == mm_of_semiring r}`
  parameter from all lemmas. The new tower has no `mul_monoid`/
  `semiring` separation; `ring` covers both. Cleaner signatures.
- Replaced `acm_of_semiring t #r` with `acg_of_r t #r` (ring →
  add_comm_group projection).
- Inlined the helpers (sum_list_append, sum_list_concatMap,
  sum_list_map_compose, sum_list_map_all_fins_eq_fin_sum,
  sum_over_fns_to_split_head, prod_range_extend_pointwise,
  per_phi_lemma) inside MultiDistrib — they're tightly coupled to the
  proof and not consumed elsewhere yet. If Determinant ever needs
  them, lift to Core.FinSum at that point.
**Question I'd have asked:** none — port was 100% mechanical given the
new tower's structure.

### 2026-05-22 ~late  Phase 4 (matrix tower)  Matrix.Ring ✅
**What:** Ported `FStar.CAS.Matrix.Ring.fst` → `Core.Matrix.Ring.fst`.
~520 LOC, verified clean on first try. Provides the `matrix_ring`
instance: square_matrix forms a (non-commutative) ring.
**Why:** Needed by `Matrix.Determinant.Mul` and downstream resultant
work.
**Decisions made on your behalf:**
- Dropped the intermediate `matrix_semiring` instance — no semiring
  class in the new tower. Construct `matrix_ring` directly.
- Field-name translations from old tower:
  - `r.sr_zero_absorb_l/r` → `zero_mul_x` / `x_mul_zero` (Helpers)
  - `mul_one_l` / `mul_one_r` → unified `one_mul_x` / `x_mul_one`
- `right_distributivity` args canonicalized to old-tower order:
  `r.right_distributivity x y z : (y+z)*x = y*x + z*x` (x is the
  right factor, listed first).

### 2026-05-22 ~late  Phase 1  Custom operators (`--`, unary `-`, int ring)
**What:** Extended `Core.Algebra.Notation.fst` with unary `op_Minus`
(TC-based `neg`) and binary `( -- )` (TC-based `x + neg y`).
Created `Core.Algebra.Int.fst` providing `int_acg`, `int_ring`,
`int_mic`, `int_cr` so integer literals (`-5`, `42`) resolve under
the new operators. Smoke-tested in `Core.Algebra.NotationTest.fst`.
**Why:** User asked for nicer ergonomics. Binary `-` cannot be
overloaded without breaking `n - 1` nat refinements; binary `--`
sidesteps the issue (greedy lexer keeps them distinct). Unary `-`
overload via `op_Minus` (source `-x` desugars to `op_Minus x`, NOT
`( ~- )`) is safe because negative-integer literals are rare in this
codebase.
**Decisions made on your behalf:**
- Int multiplication uses `Prims.op_Star` (not `op_Multiply` — that
  name doesn't exist in current F\* 2026.05.10 Prims).
- `FStar.Mul` module not present as a separate module; rely on the
  built-in `Prims` operators.

### 2026-05-22 08:30  Phase 1.5  Deferring canon_ring tactic
**What:** Skipping the dedicated `canon_ring` tactic for now. Will write
derived helpers (Core.Algebra.Helpers) as needed by downstream proofs.
**Why:** The old `..\new\FStar.CAS.Tactics.CanonRing.fst` (1063 LOC)
was reported failing on trivial distributivity in Sandbox.fst before
this rewrite. Investing in a clean tactic up-front is high-risk and
tangential to the migration's critical path (FinSum → matrix → det).
The forest discipline of the new tower may make manual proofs
significantly easier anyway; canonicalization may turn out to be
unnecessary.
**Decision made on your behalf:** Build a Core.Algebra.Helpers module
incrementally — adding derived AC/distributivity helpers when actual
downstream proofs hit them. Revisit a real canon_ring tactic only if
manual proofs become unwieldy (e.g. >5 chained eq_trans steps).
**Question I'd have asked:** "Want me to try porting canon_ring first
or push to FinSum?" — guess: FinSum, because that's where G2/G4
acceptance lives.

### 2026-05-22 08:20  Phase 1  Foundation port ✅
**What:** `Core.Algebra.fst` + `Core.Algebra.Test.fst` (G1 stress
test) verify clean. Forest invariant holds: G1.5 (the
field → commutative_ring composition) verifies without `#`-slop, no
diamonds.
**Why:** Validates the Sandbox2 design at the actual TC resolution
level.
**Decisions made on your behalf:**
- Renamed `inv_congruence` to `inv_op_congr` in `op_group` and
  `inv_congr` in `mul_is_group` to avoid duplicate top-level names
  (TC field-projector collision). Plain naming; reversible if you
  want different names.
- Added `add_associativity` to `add_comm_group` (Sandbox2 didn't have
  it). Needed for ring laws.
- Added `mul_associativity` to `ring`. Same reason.
- Added `neg_congruence` to `add_comm_group`. Needed at every
  congruence chain.
- Added `op_associativity` to `op_group` for symmetry with ring.
- `d_of_id`: declared `integral_domain → domain` instance. The
  forest needs this edge to be explicit so the composition through
  `cr_of_id`'s use of `id_d.d_r` is consistent.
- Provided `unfold let ( + ), ( * ), ( - ), ( ~- ), ( = )` operators
  via the bundle projection (resolved via TC).

### 2026-05-22 (later)  Phase 2 complete + operator architecture revised

**What:** Verified clean: Core.Permutation (.fsti + .fst), Core.FinSum
(.fsti + .fst), Core.Permutation.Enum, Core.Permutation.Sum. Zero
admits, zero PORT_CANON markers — every old canon tactic call was
replaced with an explicit lemma chain.

**Architecture revision — infix operators moved to Core.Algebra.Notation:**
Defining `unfold let ( + )` at the top level of Core.Algebra made F*
try to resolve `add_comm_group nat` for ordinary integer arithmetic
(e.g. `i + 1 < n` in refinement types), failing hard with no fallback
to Prims. Solution: split operators into an opt-in module:
- `Core.Algebra` — classes, instances, NO infix `+ * - ~-`.
- `Core.Algebra.Notation` — opens Core.Algebra, defines infix
  operators via dual TC constraint `{| equatable t |} {| acg/ring t |}`.
- `Core.Algebra` keeps `( = )` since it always resolves via
  `default_equatable: (t: eqtype) -> equatable t`.

Files that use nat arithmetic in refinements (Permutation.fsti)
open only `Core.Algebra`. Files that need infix algebra (FinSum,
Permutation.Sum, proof bodies) open both.

**right_distributivity argument order corrected:**
Original Sandbox2 had `right_distributivity x y z: (x+y)*z = x*z + y*z`.
Old tower had `right_distributivity x y z: (y+z)*x = y*x + z*x`. To
keep ported code's call sites working I switched Core.Algebra to the
old tower's convention. Documented; reversible.

**Added `neg_zero`, `neg_of_sum` to Helpers** (~70 LOC manual AC chain).
Earlier deferred as "too painful without canon_ring"; turned out tractable.

**Added `mul_commutativity_cr` bridge in Helpers:** the marker-class
field `mul_commutativity` has a dependent `(r: ring t)` parameter that
F* can't always infer from `x:t, y:t`. The bridge exposes commutativity
under `commutative_ring t` as an ordinary lemma. Call as
`mul_commutativity_cr x y`. Future code should use this not the raw
marker-class field.

**Added `mic_of_cr` instance** so the marker class is reachable via TC
search from commutative_ring contexts.

### 2026-05-22 (further later)  Matrix port hit structural mismatch

**What:** Started Phase 3 port (Core.Matrix.fst). Old code is built
on the fine-grained atomic classes `has_zero`, `has_one`, `has_add`,
`has_neg`, `has_sub`, `has_mul`, with bundle classes (add_comm_monoid,
ring) projecting to them via `has_X_of_Y` instances. The new tower
has only bundle classes, no atomic data classes.

**Option considered:** Re-introduce `has_zero` etc. as fully-derived
view classes with single-instance derivation from acg/ring. This would
preserve the forest invariant (single edge per pair) while letting
ported code work as-is. Risk: each new derived class is another node
in the resolution graph; need to verify no diamond reintroduction.

**Status:** Paused — handing back to user for direction. Foundation
+ Permutation + FinSum are a solid landing pad: the design works,
the diamond is gone, and the equality / ring resolution is clean
through 2000+ LOC of nontrivial verified code (FinSum has
~50 lemmas across range/list/range-mul-acm domains).

**Question I would have asked:** Do you want me to (a) add the
atomic data classes back as derived views to ease the matrix port,
or (b) hand-port matrix lemma-by-lemma with new-tower signatures?
Best guess if you were here: (a) — minimizes diff from old code,
preserves forest invariant via single-derivation discipline.


### 2026-05-22 (evening)  Core.Matrix verified — architecture proven through 13 modules

**What:** Core.Matrix.fst ported and verified (zero admits). Translated
old-tower signatures:
- `{| equatable t |} {| has_add t |}`                  → `{| add_comm_group t |}`
- `{| equatable t |} {| has_zero t |} {| has_one t |}` → `{| ring t |}`
- `{| m: add_comm_monoid t |}`                         → `{| g: add_comm_group t |}`
- `{| r: semiring t |}`                                → `{| r: ring t |}`

The new `add_comm_group` has flat fields (no nested `acm_*` accessors).
The `matrix_add_comm_group` instance constructor just lists fields
directly. matrix_sub dropped (new tower has no `sub` field on
add_comm_group; subtraction is just `add x (neg y)` at use sites).

Used `acg_of_r t #r` to project from ring to add_comm_group for the
fin_sum call inside matrix_mul.

**13 modules verified clean.** Stopping point — Matrix.Ring (≥25KB,
many `let pf_*` chained calls with semiring projections that need
manual `zero_mul_x`/`x_mul_zero`/`one_mul_x`/`x_mul_one` rewrites) is
the next natural piece but a full hour+ of careful porting. The user
is away; better to checkpoint here with a clean state than push a
half-ported file.

**Concrete next steps (in this order):**
1. Port Core.Matrix.Ring.fst — multiplicative tower lift, ~25KB. Watch
   for: `r.sr_zero_absorb_*` → `zero_mul_x`/`x_mul_zero`, `mul_one_l/r`
   → `one_mul_x`/`x_mul_one`, `mul_assoc` → `mul_associativity`.
2. Port Core.Matrix.MultiDistrib.fst — fin_sum * fin_sum bilinear
   expansion, ~30KB. Heavy use of `fin_sum_mul_left/right` and double
   `fin_sum_swap`. The L1 in Permutation.Sum already exercises this
   pattern so the new tower handles it.
3. Port Core.Polynomial.fst — ~2500 LOC, but mostly mechanical: same
   semiring → ring rewrite plus has_zero/has_one collapse.
4. Port Core.Matrix.Determinant.fst — 169KB. This is the heavyweight;
   suggest opening it in pieces (defs first, then row/col lemmas,
   then det_mul). Strong candidate for opus-4.7 sub-agent IF the
   user wants to spend tokens; manual is safer.
5. Sylvester (~7KB) and Resultant (~8KB) are quick once Determinant
   is up.

**Honest projection:** Determinant.Mul.perm_product_to_multidistrib —
the original stuck-lemma in the old tower — is the real test of
whether the new architecture works end-to-end. Best guess: it works
cleanly now because the diamond literally cannot form (forest invariant).
But until verified, treat with caution.


## 2026-05-22 — CanonRing tactic port (partial)

Ported `FStar.CAS.Tactics.CanonRing` (1063 LOC) to
`Core.Tactics.CanonRing` (739 LOC). VERIFIED.

**Kept (TC-agnostic, unchanged):**
- Flat `cr_eq` record bundling ops + axioms.
- AST (`rexp`), normalization (distribute → flatten → sort → reflect),
  soundness proofs.
- `ring_reflect` (normalized-forms equality ⇒ originals equatable-equal).
- `ring_reflect_squash` wrapper.

**Rewritten for new tower:**
- `cr_neg_mul_l`: `(-x)*y = -(x*y)`  (was `ring_neg_mul_l`).
- `cr_double_neg`: `-(-x) = x`  (was `ring_double_neg`).
- `comm_ring_to_cr_eq`: builder over the new `commutative_ring` class.
  Field paths: `cr.cr_r` for ring, `cr.cr_r.r_add` for additive
  group, `cr.cr_mic.mul_commutativity` for commutativity. Cleanly
  delegates to `Core.Algebra.Helpers` (qualified as `H.` to dodge
  the cr_eq record-field projector shadowing top-level helper names).

**Deferred:**
- Meta-tactic `canon_ring()` (lines 928-1100 of the old file) and the
  tests using it. The meta-tactic hardcodes old-tower projector names
  (`__proj__Mkring__item__ring_add` etc.) and would need an empirical
  pass to discover the new-tower projector mangling. Determinant proofs
  can use `ring_reflect` manually or just write longhand; we can come
  back to wire up `canon_ring()` once Determinant exposes a real need.

**Architectural note:** name collision between cr_eq record fields
(`zero_plus_x`, `one_mul_x` etc.) and top-level Helpers lemmas of the
same names. F* auto-generates record projectors that shadow top-level
imports. Fix: `module H = Core.Algebra.Helpers` + qualified calls. Did
NOT rename the cr_eq fields because legacy AST/proof code references
them by name.

## 2026-05-22 — CanonCommGroup ported; Determinant scoped (not ported)

**CanonCommGroup port: VERIFIED.** Same shape as CanonRing — TC-agnostic
AST/normalization (~377 LOC) kept verbatim; the builder
`add_comm_group_to_acg_eq` plus its three private helpers
(`acg_cancel_right`, `acg_neg_add`, `acg_double_neg_lem`)
retargeted to the new tower's flat `add_comm_group`. Meta-tactic
`canon_comm_group()` deferred. File at
`c:\Projects\CuteCAS\core\Core.Tactics.CanonCommGroup.fst`.

**Determinant port: not feasible in remaining autopilot time.** Scoped
the file (`c:\Projects\CuteCAS\new\FStar.CAS.Matrix.Determinant.fst`,
3808 LOC) and discovered it is tightly coupled to old-tower bridge
machinery that does not exist in `core`:

- **41+ uses** of `acm_of_ring`, `mm_of_ring`, `semiring_of_cr_local`,
  `equatable_of_ring`, `equatable_of_acm`, `acg_of_ring_local`.
- The vast majority are **diamond-papering bridge asserts**:
  `assert (equatable_of_ring t #cr.cr_r == equatable_of_acm t ...)`
  — workarounds for the OLD tower's diamond. In the new tower these
  are unnecessary BUT removing them is non-mechanical: each invocation
  of a downstream API (`sum_over_perms_mul_left_named`,
  `sum_list_nil`, `prod_range` etc.) currently passes an explicit
  `#(acm_of_ring ...)`, `#(semiring_of_cr_local ...)`, or
  `#(mm_of_ring ...)` that has no analogue in the new tower. Each
  call site needs targeted rewriting.
- 9 calls to `canon_ring()` — those would be replaced cleanly by
  the local helpers I already drafted (using `Helpers`).

**What I did do:**

1. Verified the bulk-rename approach works for imports + simple field
   paths (`ring_add → r_add.add` etc.).
2. Drafted the new local helpers section using `Helpers` calls
   (saved as `Core.Matrix.Determinant.fst.draft`).
3. Confirmed F* hits the bridge-machinery issues in the function
   bodies, not the signatures — so signatures translate fine; bodies
   need expert care.

**The draft file** is preserved at
`c:\Projects\CuteCAS\core\Core.Matrix.Determinant.fst.draft` with
bulk renames applied (do NOT verify; rename to `.fst` only when
resuming work).

**Recommendation:** the Determinant port needs an interactive session
with the user (or a careful incremental approach over several hours).
Mechanical bulk substitution will not work because of the diamond-
bridge invocations that need targeted deletion and signature healing.

Concrete next steps to resume on Determinant:
1. Delete all bridge asserts (`assert (equatable_of_ring ... == ...)`)
   — they are no-ops in the new tower.
2. Delete `acg_of_ring_local` definition (use `acg_of_r` instance).
3. Delete `semiring_of_cr_local` (no semiring class in new tower);
   every consumer must be migrated to use `ring` API directly,
   typically via `prod_range` already taking `{| ring t |}`.
4. Delete every `mm_of_ring t #cr.cr_r` binding and every
   `#(acm_of_ring ...)` / `#(equatable_of_acm ...)` explicit instance
   argument — F* will resolve through the forest chain
   `commutative_ring → ring → add_comm_group → equatable` uniquely.
5. Drop the old local helpers (now redundant) and use the inlined
   `H.zero_mul_x`/`H.x_mul_zero`/`H.neg_zero`/`H.neg_of_sum`
   plus 4 new private helpers (`group_cancel_right`,
   `neg_x_eq_neg_one_mul`, `neg_mul_l`, `neg_mul_r`).
6. Verify lemma-by-lemma, applying sliding-`admit()` per AGENTS.md
   when a body fails.

This is ~3-5 hours of careful proof-shepherding work. Worth scheduling
a dedicated session.

## 2026-05-22 — Determinant port: deep proof-work phase confirmed

Resumed the Determinant port. Got the prelude (imports, helpers, bulk
renames, `acg_of_ring_local`, deletion of `semiring_of_cr_local`,
qualification of all Helpers calls) building cleanly through ~265 lines.

**First non-trivial lemma** `prod_range_const_one` (line 265) does NOT
verify with mechanical translation — SMT-fails. Replaced body with
`admit()` to unblock; next failure is at line 327 inside
`perm_product_id_identity` (an assert).

This confirms: every nontrivial proof in Determinant likely needs
manual attention. The architecture is right (forest TC, no diamond),
but proof shapes that depended on the old tower's incidental
unification behaviour need re-shepherding. Pattern observed: SMT
struggles to chain reflexivity / mul_congruence / one_mul_x even when
all the right facts are introduced.

**Honest estimate**: 3808 LOC × \~30 minutes / lemma × ~80 lemmas ≈
40 hours of focused work. Could be faster with a strong canon_ring()
meta-tactic (the OLD file leans on it for distributivity-heavy
identities), but porting the meta-tactic itself is ~4 hours.

**Pragmatic recommendation**: port `canon_ring()` (the meta-tactic
deferred earlier) FIRST. With it in place, ~30% of Determinant proofs
that were `= assert ... by canon_ring ()` become trivial again, and
the residue is much smaller. Without it, Determinant proofs that span
distribution + negation chains have to be hand-shepherded.

**State of Determinant.fst**: prelude builds; `prod_range_const_one`
admit()'d; rest fails at first downstream assertion. NOT in a
ready-to-commit state.

## 2026-05-22 sleep-shift wrap-up

Polynomial multiplication ring tower complete:
- ring (polynomial cr) instance: assembled via explicit reveal lemmas
  (polynomial_equatable_eq_reveal, polynomial_acg_eq_reveal,
  polynomial_acg_add_reveal) added to Core.Polynomial.fsti so the
  ring-class operator-resolution chain reduces from
  `(polynomial_acg cr).acg_eq.eq` down to bare `poly_eq`. Without
  these reveals, SMT could not discharge the field-type assertion
  for mul_congruence, mul_associative, distributivity.
- commutative_ring (polynomial cr) instance: built via
  poly_mul_commutative.

Key new lemmas:
- poly_mul_right_nil: all_zero (poly_mul p [])
- poly_add_swap_middle: a + (b + z) eq b + (a + z)
- poly_mul_right_cons: right-Horner identity
- poly_mul_commutative: full commutativity

Build status: 27/27 cached green.

Open follow-ups for next session:
- degree / leading_coefficient / eval (Phase 1 completion)
- Euclidean division (poly_divmod) over a field (Phase 2 start,
  unblocks algebraic constants)
- AGENTS.md note: ring-instance fields require reveal lemmas when the
  underlying equatable/acg instances are opaque via fsti. Pattern:
  add SMTPat reveal val .eq p q == direct_predicate p q. Saved
  ~6 unsuccessful elaboration attempts.
