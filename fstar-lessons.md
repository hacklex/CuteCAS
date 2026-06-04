# F\* proof lessons — read before proving any lemma

> **Every agent dispatched to prove a lemma must follow this file.** It is the
> distilled set of style/proof rules that make verification succeed under
> default resource limits in this repo. Hard-won; violating them is the usual
> cause of a proof that "should work" but doesn't. The forest/typeclass design
> rules live in `AGENTS.md`; this file is the *proof-writing* checklist.

## Program against the instance, not the implementation (the #1 rule)

The rule is about the **generic ring algebra** (the ops every ring has + their
laws), NOT about polynomial-specific notions. Two buckets:

**Bucket A — generic ring ops + laws (have a typeclass equivalent): use the
generic form, never `poly_*`.**
- Write **`a * (b + c)`**, not `poly_mul a (poly_add b c)`; invoke
  **`mul_commutativity`**, **`left_distributivity`**, **`add_associativity`** —
  the bare class-method names, *not* `poly_mul_commutativity`, *not* a projection
  like `cr.mic.mul_commutativity`. TC resolution supplies the instance.
- `poly_add`/`poly_mul`/`poly_neg`/`poly_sub`/`poly_zero`/`poly_one` and their
  law-lemmas (`poly_mul_commutativity`, …), plus analogous `ac_*` / `fp_*`, are
  for **constructing** the instance only (+ reveal bridges). Not in client code
  afterward.

**Bucket B — polynomial-specific notions (no generic name): fine to use
anywhere.**
- `coeff`, `monomial`, `poly_deg`, `poly_lc`, `poly_divmod`/`poly_div`/
  `poly_rem`, `poly_deriv`, `poly_eval`, … and their fact lemmas
  (`coeff_poly_mul`, `poly_divmod_correct`, degree bounds, …) are legitimate
  everywhere. You may mix them with Bucket-A generic lemmas in one proof — e.g.
  reason with `mul_commutativity` and `poly_divmod_correct` together. They
  compose because the instance's `*` *is* `poly_mul` (same term).

Write implementation-agnostic signatures where the structure is generic
(`let p_squared (#t:Type) {| commutative_ring t |} (p: polynomial t) = p * p`),
but reach for Bucket-B polynomial facts whenever the goal is about polynomials.

This is the single biggest slop-remover. (`AGENTS.md` §2.11 is the full rule;
much existing code predates it and will be cleansed — but **all new proofs
follow it**.)

## Signature hygiene (types, pre/post-conditions, refinements)

1. **No anonymous lambdas in any signature.** No `fun _ -> …` in a type,
   `requires`, `ensures`, or refinement. Use the named combinators in
   `Core.Algebra.Combinators` (`swap_args`, `pointwise_mul`, `pointwise_add`,
   `pointwise_neg`, `const`, `fcomp`, `flip`, `kronecker_delta`, `fin_lift`, …).
   A lambda in a *body* is a last resort — avoid it. (See `AGENTS.md` §1.6.)

2. **No `if`/`match` in pre/post-conditions or pure-function specs.** A branch in
   a spec blocks unification and SMT. Instead: define a *named* function for the
   branching value and expose a reveal lemma
   (`assert (f x == …) by (norm [delta_only [`%f]; iota; zeta; primops]; trefl())`),
   then reason over the named symbol. Or factor the cases into separate lemmas.

3. **`requires (x = y)` on a typeclass `=` is a trap.** The typeclass `eq` is a
   bool-valued function; a propositional `requires` over it confuses resolution.
   Use a concrete boolean equality (`eq_t`) or state the divisibility/equality
   you actually mean.

## Explicit-argument economy (apply AFTER the proof verifies)

4. **Strip redundant implicits once green.** Remove `#t #f #r`,
   `#instance`, and `let cr_p : … = TC.solve` scaffolding that the value
   arguments already determine. Keep an explicit `#r` only where **no value
   argument** pins it down. Bare operators (`+`, `*`, `--`, `one`, `zero`) are
   preferred over `poly_add`/`poly_mul`/… once instance resolution is unambiguous.

5. **No redundant `reflexivity`/`symmetry` steps.** Once
   `H.elim_equatable_laws t ()` is invoked, equatable reflexivity and symmetry
   are universally in scope — do **not** sprinkle per-term `reflexivity #t …` /
   `symmetry …` calls. Likewise `H.trans_for_calc t ()` makes transitivity
   available for `calc`. Add these elimination lemmas once at the top, then drop
   the manual per-step congruence noise.

## Arithmetic and instance resolution

6. **Arithmetic under `Core.Algebra.Notation`.** Never qualify `-`. Plain `nat`
   `+`/`-` on indices is fine; only reach for `Prims.op_Addition` /
   `Prims.op_Subtraction` if a bare `+` genuinely resolves to the *ring* `+` and
   fails. When index arithmetic misbehaves, suspect an `int`-typed literal first.

7. **Pin one instance per structure and stay consistent.** Refined-coefficient
   bare ops can fail TC resolution — pass the instance explicitly there. For
   `polynomial t`, the add-group is `polynomial_acg cr` (its `.add` *is*
   `poly_add`) and the ring is `(polynomial_commutative_ring_instance #t #cr).pcr`
   (its `.mul`/`.one` *are* `poly_mul`/`poly_one`); choose the projection whose
   field literally equals the standalone function your other lemmas mention, so
   the `eval_*` / `*_unfold` lemmas apply with no bridge. Bridge two records with
   one `assert (A == B)` when both are defeq with the same fields.

8. **Pushing a homomorphism through an aggregate** (det / sum_over_perms /
   prod_range / sum_list): the inline lambda inside the aggregate will **not**
   unify with a separately-written lambda. Add a **named per-index function** in
   the defining module plus a reveal lemma
   (`aggregate … == aggregate_via (named_fn …)`), then both sides reference one
   symbol and `*_congruence` / `eval_*` compose. Expose abstract `let`s with
   reveal lemmas so downstream modules can transport through them.

## Proof construction & resources

9. **Decompose into small named top-level lemmas.** No monolithic bodies —
   factor every non-trivial sub-fact (index bridges, `fin_sum` congruences, ring
   rearrangements). Easier for Z3, debuggable with sliding `admit()`, reusable.
   (`AGENTS.md` §2.6.)

10. **Ring/group equalities via tactics.** Prefer
    `assert (X = Y) by (canon_ring ())` (or `canon_comm_group ()`) over manual
    `mul_commutativity`/`associativity`/`distributivity` chains. (`AGENTS.md` §2.9.)

11. **Tighten resources after success.** Target per-lemma `--z3rlimit` in
    **30–80**; if a lemma needs `> 80`, factor it. (`AGENTS.md` §2.8.)

12. **Never leave an unclosed `(*`.** A dangling comment silently swallows later
    definitions; the module still "verifies" standalone and only a cross-module
    import reveals the loss. If defs go mysteriously missing, check comment
    balance and wipe stale `obj/*.checked`.

13. **No `admit` / `assume` / `sorry` in returned code.** Sliding `admit()` is a
    development tool only; strip every one before declaring a lemma done.

## What "done" means for a dispatched proof

Return either (a) the **complete, green, admit-free** lemma text ready to paste,
or (b) an **honest failure**: the specific obligation you could not discharge and
what you tried. Do **not** return prose about how the lemma "would take hundreds
of lines" or "needs multiple sessions" — if it feels that big, it was scoped too
large; report that so it can be split into smaller atomic lemmas.
