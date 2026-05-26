# Proof-smell findings (smell-hunter)

Scratch file: `c:\Projects\CuteCAS\core\scratch_smells.fst` (verifies clean
against the live obj/ cache, 2026-05-23).

Scope: only `core\` source files, `.draft` files skipped.

---

## F-001  Core.Algebra.fst:88,149,192,227,229,250,252  severity=high

- smell: Seven `unfold instance` declarations on record types, in direct
  contradiction to AGENTS.md §1.5 — which the file's own header comment
  (line 16) restates verbatim ("Plain `instance` only; no `unfold instance`
  on records").
- current code:
  ```fstar
  unfold instance eq_of_acg (t:Type) {| acg: add_comm_group t |} : equatable t = acg.acg_eq
  unfold instance acg_of_r  (t:Type) {| r:   ring t |}            : add_comm_group t = r.r_add
  unfold instance r_of_d    (t:Type) {| d:   domain t |}          : ring t = d.d_r
  unfold instance r_of_cr   (t:Type) {| cr:  commutative_ring t |} : ring t = cr.cr_r
  unfold instance mic_of_cr (t:Type) {| cr:  commutative_ring t |} : ... = cr.cr_mic
  unfold instance d_of_id   (t:Type) {| id:  integral_domain t |} : domain t = id.id_d
  unfold instance cr_of_id  (t:Type) {| id:  integral_domain t |} : commutative_ring t = {...}
  ```
- proposed fix: drop the leading `unfold` from each declaration. F\*
  WHNF-inlining of these projections is the exact diamond pathology §1.5
  warns against — two call sites can see the same instance in folded and
  unfolded form, breaking SMT term equality. (See scratch lines 99–128
  for the rationale block.)
- verified in scratch: no — cascade is repo-wide; needs orchestrator
  bottom-up roll-out (drop one `unfold`, rebuild Matrix.Ring +
  Polynomial.Mul + Determinant, repeat).
- risk if applied automatically: HIGH. Every consumer that currently
  relies on the inline form will need either an explicit `compute ()`
  tactic call (per §1.5 guidance) or a local `let ( + ) = r.r_add.add`
  short-circuit. Roll out one instance at a time. Start with
  `mic_of_cr` (smallest reverse-dep set) and end with `eq_of_acg`
  (largest).

---

## F-002  Core.Matrix.Determinant.fst:3361,3436,3850  severity=med

- smell: Three public-facing lemmas whose **`ensures`** contains the
  inline lambda `(fun (j: fin n) -> sum_over_perms (n-1) (per_fiber_fn f i j))`.
  Each lemma body then needs an `assert ... by (FStar.Tactics.norm
  [delta_only [`%fin_sum]; iota; zeta; primops]; FStar.Tactics.trefl ())`
  workaround at lines 3373 / 3451 / 3893 to bridge `fin_sum h` to its
  internal `sum_range`-with-zero-extension form.
- current code (line 3361, abbreviated):
  ```fstar
  let concat_fibers_sum_eq_fin_sum (#t: Type) {| cr: commutative_ring t |}
    (#n: pos) (f: permutation n -> t) (i: fin n)
    : Lemma (requires respects_perm_eq f)
            (ensures sum_list (L.map f (concat_fibers i)) =
                     fin_sum (fun (j: fin n) ->
                       sum_over_perms (Prims.op_Subtraction n 1)
                                      (per_fiber_fn #t #cr f i j)))
    = concat_fibers_from_sum #t #cr f i 0;
      assert (fin_sum (fun (j: fin n) -> ...)
              == sum_range (fun (k: nat) -> if k < n then ... else zero) 0 n)
        by (FStar.Tactics.norm [delta_only [`%fin_sum]; iota; zeta; primops];
            FStar.Tactics.trefl ())
  ```
- proposed fix: expose a named `fin_sum_unfold` lemma in `Core.FinSum.fsti`
  that delivers the defining equation
  `fin_sum f = sum_range (fin_extend_zero f) 0 n`
  where `fin_extend_zero` is the named top-level form of the inline
  `fun k -> if k < n then f k else zero`. The named combinator and its
  `_unfold` lemma are sketched in `scratch_smells.fst` lines 78–88 and
  compile clean. With `fin_sum_unfold` in hand, the three trefl
  gymnastics collapse to a single explicit lemma call AND the inline
  `fun (j: fin n) -> ...` in the public `ensures` becomes
  `per_fiber_sum_fn f i` (a named combinator). This is exactly the
  pattern §3.6 mandates for public posts. See scratch §F-003 block.
- verified in scratch: partial (named combinator + unfold lemma
  typecheck; the cascade into Determinant.fst is not exercised).
- risk if applied automatically: MEDIUM. Affects three public lemmas in
  Determinant.fst and any caller using their post. The new
  `fin_sum_unfold` lemma must NOT carry an SMTPat (§1.6 — would
  re-create the diamond), so callers update by hand.

---

## F-003  Core.Polynomial.Mul.fsti:179, Core.Polynomial.Div.fsti:37  severity=info

- smell: SMTPats containing `Prims.op_Addition` (e.g.
  `[SMTPat (coeff_at (a :: p') (Prims.op_Addition i 1))]`).
- current code:
  ```fstar
  val coeff_at_cons_succ_compute (#t:Type) {| cr: commutative_ring t |}
                                 (a: t) (p': polynomial cr) (i: nat)
    : Lemma (coeff_at (a :: p') (Prims.op_Addition i 1) == coeff_at p' i)
            [SMTPat (coeff_at (a :: p') (Prims.op_Addition i 1))]
  ```
- assessment: **NOT a smell.** Per the reviewer brief: "fsti `_compute`
  lemmas with computational SMTPats are by design and are OK." The
  `Prims.op_Addition i 1` shape is the standard F\* "successor pattern"
  for SMT-triggered structural induction on a `nat` index. Flagged here
  only to document that the pattern was inspected and accepted.
- verified in scratch: n/a.
- risk if applied automatically: n/a — do nothing.

---

## F-004  Core.Matrix.Ring.fst:72,112,515,523,553,561  severity=low

- smell: Six `assert_norm` calls that discharge the value of the
  identity / zero matrix at an index:
  ```fstar
  assert_norm (id_mat i k == (if (i <: nat) = (k <: nat) then r.one else r.r_add.zero))
  assert_norm (zm i k == zero #t)
  ```
- current code:
  ```fstar
  let pf (k: fin n) : Lemma
      (id_mat i k * a k j
       = (if (i <: nat) = (k <: nat) then one else zero #t) * a k j)
    = assert_norm (id_mat i k == (if (i <: nat) = (k <: nat) then r.one else r.r_add.zero));
      reflexivity (id_mat i k * a k j)
  ```
- proposed fix: expose two `_compute` lemmas in `Core.Matrix.fsti` with
  the same SMTPat shape as `coeff_at_cons_succ_compute` in
  `Core.Polynomial.Mul.fsti`:
  ```fstar
  val id_matrix_compute (#t:Type) {| r: ring t |} (n: nat) (i j: fin n)
    : Lemma (id_matrix n i j == (if (i <: nat) = (j <: nat) then one else zero))
            [SMTPat (id_matrix n i j)]

  val zero_matrix_compute (#t:Type) {| r: ring t |} (n: nat) (i j: fin n)
    : Lemma (zero_matrix n i j == zero)
            [SMTPat (zero_matrix n i j)]
  ```
  After this, all six `assert_norm` calls vanish. The SMT-pattern form
  is the project-wide convention for "constructor at concrete index";
  `assert_norm` is a stylistic outlier here.
- verified in scratch: no — would require touching Core.Matrix.fsti.
- risk if applied automatically: LOW. Adding `_compute` SMTPats is
  purely additive; the `assert_norm` calls can be removed
  one-by-one after the lemmas land. Cascading the SMTPat into
  Determinant.fst's many matrix-index expressions may slightly
  increase Z3 trigger fan-out — monitor verification time.

---

## F-005  Core.FinSum.fst:481-482  severity=low

- smell: A pair of `assert_norm` calls inside a base case of a
  recursive proof, immediately followed by `neg_zero #t ()`.
- current code:
  ```fstar
  | [] -> assert_norm (sum_list (map (fun x -> neg (f x)) []) == (zero #t));
          assert_norm (neg (sum_list (map f [])) == neg (zero #t));
          neg_zero #t ()
  ```
- proposed fix: replace with direct invocations of the existing
  `sum_list_nil_compute` / equivalent computational lemmas (already in
  Core.FinSum.fsti). `assert_norm` here works around the absence of a
  named unfold lemma; a direct call would be more stable across F\*
  versions.
- verified in scratch: no.
- risk if applied automatically: LOW. Local to a private `*_lambda`
  helper; no public-API impact.

---

## Summary

- HIGH: 1  (F-001 — `unfold instance` cluster, repo-wide cascade)
- MED:  1  (F-002 — three trefl-bridge sites in Determinant.fst)
- LOW:  2  (F-004 matrix index lemmas, F-005 FinSum assert_norm base case)
- INFO: 1  (F-003 — Polynomial SMTPats, confirmed-OK by reviewer brief)

### Things that LOOKED smelly but are not

- All `.fsti` files are clean on §3.6 (no `forall` / inline `fun` /
  `if` / `match` in any public `requires`/`ensures`). The only `forall`
  occurrences in `.fsti` are inside the **defining body** of `let`
  predicates such as `respects_perm_eq` (Core.Permutation.Sum.fsti:108)
  and `all_distinct` (Core.Permutation.Enum.fsti:52) — explicitly
  allowed by §3.6 "Allowed locations".
- The `private let *_lambda` helpers in Core.FinSum.fst (4 occurrences:
  sum_list_map_{neg,add,mul_left,mul_right}_lambda) contain inline
  `fun` in `ensures`. These are **private**, not in any `.fsti`, and
  paired with public hygienic wrappers that re-state the post in
  `pointwise_*` form. This is the documented two-layer bridging
  pattern and is acceptable.
- The `_compute` SMTPats in Polynomial.{Mul,Div}.fsti are by design
  (covered explicitly in the reviewer brief).
- Norm-trefl chains in Core.Tactics.Canon{Ring,CommGroup}.fst are
  internal to the canonicalization tactics themselves; they are the
  *implementation* of the canonicalizer, not a workaround for proof
  instability.

### Critical issues for human review before auto-apply

**F-001 is the only HIGH-severity item and absolutely MUST NOT be
auto-applied.** Dropping `unfold` from those seven instances will
break every consumer that currently relies on TC-projection inlining,
and the fix-up at each break site is non-mechanical (sometimes
`compute ()`, sometimes a local operator short-circuit, sometimes
a named `let ( + ) = ...` binding). Roll out one instance per PR,
starting with `mic_of_cr` (smallest blast radius). The orchestrator
should plan a dedicated session for this.

F-002 is the next most impactful but is safe to apply mechanically
once `fin_sum_unfold` lands in the .fsti — the cascade is contained
to three sites in Determinant.fst.

F-004 and F-005 are local, safe, and uncontroversial.
