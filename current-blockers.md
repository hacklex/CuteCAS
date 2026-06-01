# Current blockers — LRT (Rothstein–Trager) soundness

> Saved 2026-06-01 so it survives context compaction. This is the standing
> assessment of why the **full LRT derivative identity** is not currently
> deliverable, what *is* achievable, and what was already landed.

## The goal

The full LRT soundness theorem:

    d/dx[ Σ_{cᵢ : R(cᵢ)=0} cᵢ · log(vᵢ) ] = p/q,    vᵢ = gcd(p − cᵢ·q', q)

i.e. the symbolic `root_sum` produced by `lrt` differentiates back to the
integrand. `R(z) = res_x(p − z·q', q)` (already computed — `lrt_resultant_raw`).

## Prerequisite tower

| # | Prerequisite | Status / scale |
|---|---|---|
| A | `poly_eval : polynomial t → t` as a **ring homomorphism** | **achievable** (Hermite-class); foundation validated in scratch |
| B | Root theory: `a` root ⟺ `(x−a)∣p`; squarefree ⟹ `q'(α)≠0` | achievable, moderate |
| C | `algebraic t r` is a **field** when `r` irreducible (inverse via `ext_gcd`) | achievable, moderate–large |
| D | **det specialization** ⇒ **resultant specialization** `R(c)=res_x(p−c·q',q)` ⇒ base-field Rothstein–Trager criterion `R(c)=0 ⟺ gcd nontrivial` | achievable, large; needs A |
| E | **Constructive splitting field of `R`** (iterated extensions, track all roots) | **THE WALL — research-frontier** |
| F | **Partial-fraction / residue** decomposition over the splitting field; Rothstein–Trager correspondence `{p(α)/q'(α)} = roots of R`, `v_c = Π_{α:res=c}(x−α)` | research-frontier |
| G | Assembly: `Σ_c c·v_c'/v_c = Σ_α res_α/(x−α) = p/q` | moderate *given* E,F |

## Verdict

**The full identity (E–G) is not realistically achievable on this foundation.**
It requires constructive splitting fields + a residue/partial-fraction theorem
over the extension — frontier formalization not finished in mathlib/mathcomp —
and the project's **no-`assume` rule forbids shortcutting it**. Building A–D
(real, reusable machinery) does **not** by itself reach the headline.

## What IS landed (verified, 60/60 green)

Structural residue soundness in `Core.Risch.LRT.fst`:
- `lrt_log_argument_divides_q` — each `v_c = gcd(p−c·q', q)` divides `q`.
- `lrt_log_argument_divides_residue` — `v_c | (p − c·q')` (residue condition
  `p ≡ c·q'` on `v_c`).

These are honest *partial* soundness (each LRT term is `log` of a genuine
factor of `q` on which the residue condition holds), but NOT the derivative
identity.

## Prerequisite-A finding (`poly_eval`)

`poly_eval` foundation verified in scratch (`cpow`, `poly_eval`,
`eval_zero`, `eval_one`, `eval_congruence`). The remaining ring-hom laws
(`eval_add`, `eval_neg`, `eval_mul`) must be proved through a **coefficient-sum
bridge** `eval p c = Σ_{i<len} coeff p i · cⁱ` rather than by structural
(Horner) induction, because the cons used to build polynomials is a *trimming
smart-cons* `@` (`x @ [] = if x=zero then [] else [x]`), so
`poly_neg (a::p)` is not syntactically `neg a :: poly_neg p` and the one-step
Horner equation does not fire. All needed pieces exist publicly:
`poly_add_coeff`, `poly_neg_coeff`, `coeff_poly_mul`, and
`sum_range_add / sum_range_neg / sum_range_mul_left`. So A is a genuine
multi-lemma module, not a quick win — but tractable.

## Options (decision)

1. **Stop** (recommended): keep the structural residue soundness; document the
   full identity as a flagged research goal. Verified-CAS story stays honest.
2. **Build A–D** over several sessions: `poly_eval` ring hom, root theory,
   `algebraic` field extension, resultant specialization → RT criterion.
   Reusable (also feeds factorization/completeness) but won't reach the identity.
3. **Relax `no-assume`** for one clearly-marked classical interface (the residue
   theorem) so the identity can be *assembled* on an assumed lemma — breaks the
   "no assumes" headline guarantee; deliberate choice only.

(Initial lean was option **1**. **Superseded** — see the update below: owner
wants both the executable integrator and its proof; specializing to ℚ makes
this a large-but-finite program, so we pursue it slowly.)

---

## Update 2026-06-01 (cont.) — pursue the ℚ executable + proof, slowly

Owner wants **both** the executable integrator **and** its correctness proof,
no timeline, LoC not a concern. Specializing the base field to **ℚ (char 0)**
moves the verdict from "infeasible" to "large but finite, well-mapped."

### What ℚ + char 0 changes

- **Factorization becomes algorithmic (Wall 1 dissolves in principle).** Over ℚ,
  irreducibility is decidable and factoring is computable
  (**Berlekamp–Zassenhaus**). Cost: build 𝔽_p (ℤ/p as a field + primality),
  Berlekamp over 𝔽_p, Hensel lifting, recombination. Large but known-finite
  (cf. Isabelle AFP `Berlekamp_Zassenhaus`).
- **The tower collapses (Walls 2/3) via the primitive element theorem.** In
  char 0, `ℚ(α₁,…,αₖ) = ℚ(θ)` — a **single** simple extension
  `algebraic ℚ m_θ`, one F* type, no type-changing recursion. `θ = α + c·β`
  (finitely many bad `c`, found by search over ℚ); `m_θ` = the irreducible
  factor of `Res_y(f(x−c·y), g(y))` through θ — so PET **consumes**
  factorization (depends on Wall 1).
- **The payload (Wall 4) is unchanged**: resultant = ∏ over roots (Poisson),
  partial fractions over the splitting field, RT correspondence, assembly.
  Field-agnostic; still the core proving.

### CORRECTION — factor-coefficient bound (supersedes the earlier "Hadamard" remark)

The earlier "swap to Hadamard" was **wrong**: Hadamard bounds *determinants*
(hence resultants), **not** factor coefficients. The Landau–Mignotte factor
bound genuinely routes through **Mahler measure / complex root magnitudes**
(needs ℂ + FTA). It is *not* avoidable naively — factor coefficients can be
~`2ⁿ` larger than `f`'s, so there is no "`‖g‖ ≤ ‖f‖`" shortcut.

**Honest ℂ-free substitution = the Kronecker / Lagrange-interpolation bound.**
For `f ∈ ℤ[x]`, pick distinct integers `cⱼ` with `f(cⱼ) ≠ 0`. Any factor `g | f`
has `g(cⱼ) | f(cⱼ)` in ℤ, so `|g(cⱼ)| ≤ |f(cⱼ)|`; and `g = Σ g(cⱼ)·Lⱼ`
(Lagrange) gives `‖g‖∞ ≤ Σ |f(cⱼ)|·‖Lⱼ‖ =: B` — explicit, **integer/rational
only, no ℂ / no FTA**. Already machine-checked (AFP
`Polynomial_Factorization.Kronecker_Factorization`).

### KEY INSIGHT — the bound is a PARAMETER, decoupled from the algorithm

- The executable (Berlekamp–Zassenhaus) is **entirely over ℤ / 𝔽_p / ℤ_{p^k}** —
  no ℝ/ℂ, no heuristics, no noncomputable steps (deterministic Berlekamp).
- ℝ/ℂ only ever appeared in the **proof of the tight bound**, never in the
  computation. Swap Mignotte's number for the Lagrange `B` (elementary proof)
  and the **same fast algorithm** is fully ℂ-free-correct. Cost: looser
  constant ⇒ more Hensel steps ⇒ slower by a polynomial factor — NOT a change of
  algorithm and NOT a loss of correctness.
- Do **not** conflate Kronecker's *method* (slow whole algorithm: factor the
  integers `f(cⱼ)`, try all divisor combinations) with the Lagrange *bound*
  (used inside fast BZ).
- Recombination speed is a separate axis: Zassenhaus `2ʳ` vs van Hoeij/LLL
  (poly-time, also ℂ-free over ℚ; its own proof cost).

### Revised work order (all HIGH confidence unless noted; slow & steady)

0. `poly_eval` ring hom via the coeff-sum bridge (prereq A; decoupled, anytime).
1. `algebraic ℚ r` as a **field** when `r` irreducible (inverse via `ext_gcd`) —
   prereq C.
2. **resultant = ∏ over roots** (Poisson), via resultant multiplicativity +
   `Res(x−α, B) = B(α)`.
3. **RT payload** *relative to a given splitting field*: `q'(α)=∏_{β≠α}(α−β)`,
   partial fractions, RT correspondence, assembly ⇒ **soundness without
   construction**.
4. **Construction (for the executable):** 𝔽_p → Berlekamp → Hensel →
   recombination (with the **Lagrange** bound, not Mignotte) ⇒ factorization
   over ℚ; then primitive element ⇒ `ℚ(θ)`. MED confidence on the 𝔽_p/Berlekamp
   encoding; everything else HIGH.

Step 3 gives the **correctness theorem**; step 4 makes it **executable**.
Neither needs ℝ/ℂ at any point.
