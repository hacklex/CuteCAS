# CuteCAS

A formally-verified small computer-algebra core in [F\*](https://www.fstar-lang.org/),
built bottom-up from an abstract algebra typeclass tower toward a **verified and
executable rational-function integrator** (Risch / Lazard–Rioboo–Trager over ℚ).

Every committed module verifies clean, with **zero `admit` / `assume` / `sorry`**
and **no ℝ/ℂ axioms** — the whole development stays over ℤ / ℚ / 𝔽_p / ℤ/pᵏ and
explicit algebraic extensions.

## Status

- **91 modules** verify clean from cache (foundation → linear algebra →
  polynomials → finite fields/Berlekamp → algebraic constants/derivations/
  fractions → Risch skeleton).
- **Proven headline results:** Cauchy–Binet `det_mul`, Laplace/adjugate,
  resultant ⇔ common factor, the Poisson product formula, the polynomial UFD +
  Euclidean tower, Yun square-free factorization, `poly_eval` as a ring
  homomorphism commuting with `det` (resultant specialization), field of
  fractions, `algebraic t r` is a **field** at an irreducible `r`, Hermite
  full-reduction soundness, Frobenius/Fermat over 𝔽_p, the X^p−X split, CRT,
  and the Berlekamp forward + reverse split and reducibility criterion.
- **In progress:** the full LRT derivative identity and the ℚ-construction
  (Berlekamp–Zassenhaus: Hensel lift, recombination, primitive element) feeding
  the executable integrator.

The exhaustive, per-lemma status of every module lives in **`STATUS.md`** — that
file is the source of truth for what is done and what remains.

## Documents

| File | Role |
|---|---|
| **`STATUS.md`** | **Source of truth.** Lemma-level status matrix for the whole tower; long-horizon frontier (Part VII). Updated after any finished work. |
| `plan.md` | The *current* session's plan: exactly what is being drilled now, per-lemma. Narrow and disposable. |
| `AGENTS.md` | Engineering rules: the diamond-free typeclass-forest design invariant, proof-development workflow, source-of-truth/session workflow (§0.5). |
| `.github/copilot-instructions.md` | Repo-wide non-negotiables: CRLF, never write to git, never risk data loss, no admit/assume, resource budget. |

## Building

```powershell
.\build-all.ps1            # verify the whole tower in dependency order (stop at first failure)
.\build-all.ps1 -KeepGoing # verify all, collect every failure
```

Toolchain: F\* at `C:\FStar` with Z3, run with
`--include . --cache_checked_modules --cache_dir obj`. Modules are verified
**sequentially** (one at a time, default resource limits) per the resource
rules in `AGENTS.md`.

## Architecture in one paragraph

The algebra is a **diamond-free forest of typeclasses**:
`equatable → add_comm_group → ring → commutative_ring`, with
`field → skewfield → domain → ring` edges and a single divisibility chain
`integral_domain ← gcd_domain ← ufd ← euclidean_domain`. Exactly one `instance`
sits on each ordered class pair, bundle fields are `@@@no_method`, and
**signatures contain no lambdas** (named combinators only) so unification stays
predictable. Reflective `canon_ring` / `canon_comm_group` tactics discharge ring
and group equalities. See `AGENTS.md` for the full invariant.

## History

This began as a personal sandbox for learning F\* by formalizing abstract
algebra (equivalence relations, grouplikes, ringlikes, fields of fractions,
polynomial rings — some of which fed into F\*'s standard library). It has since
grown into the verified-CAS effort described above.
