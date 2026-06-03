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
| B | Root theory: `a` root ⟺ `(x−a)∣p`; squarefree ⟹ `q'(α)≠0` | ✅ **DONE (2026-06-02)** — `Core.Polynomial.Root` |
| C | `algebraic t r` is a **field** when `r` irreducible (inverse via `ext_gcd`) | ✅ **DONE (2026-06-02)** — `Core.AlgebraicConstant.Field.algebraic_field` |
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

0. ✅ **DONE (2026-06-01)** — `poly_eval` ring hom (`Core.Polynomial.Eval.fst`),
   via the coeff-sum bridge. Spun off a reusable public lemma
   **`Core.FinSum.Convolution.sum_range_convolution`** (Cauchy product), which
   `eval_mul` rests on. Tree at 62 modules, all green.
1. ✅ **DONE (2026-06-02)** — `algebraic t r` as a **field** when `r` irreducible
   (inverse via `ext_gcd`/Bézout) — prereq C. See `Core.AlgebraicConstant.Field.fst`.
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

### Refinement (2026-06-01) — three tiers; executable needs NO splitting field

Earlier "PET collapses the tower" was right about the *type* (always
`ℚ[x]/(m)`, base ℚ) but undersold *construction*: splitting `R·q` requires
**factoring over the number field `ℚ(θ)`** at each adjunction (**Trager**:
norm via resultant → factor over ℚ → gcd back), with its own
"finitely-many-bad-shift `s`, search" step. Constructive, ℂ-free, known — but
its own algorithm+proof. Net: the deliverable splits into three tiers, all
ℂ-free, in increasing difficulty:

1. **Executable integrator** — needs only **one simple extension per
   irreducible factor `R_i` of `R`**: factor `R` over ℚ (BZ), then compute
   `gcd(p − c·q', q)` in `ℚ[x]/(R_i)` with `c` the symbolic root. **No
   splitting field, no tower, no Trager.** This is the LRT/Rioboo point — the
   output `RootSum(R_i, c ↦ c·log(gcd …))` keeps roots symbolic. Cleanest tier.
2. **Relative soundness** — `d/dx[LRT] = p/q` over a *given* splitting field of
   `R·q` (parameter, not constructed); descends to a `ℚ(x)` identity by
   injectivity `ℚ(x) ↪ K(x)`. The RT-payload work (resultant=∏roots, partial
   fractions, correspondence, assembly). No construction.
3. **Unconditional soundness** — *construct* the splitting field (Trager + PET)
   to discharge tier-2's existence hypothesis. Heaviest tier; only this one
   needs the splitting-field construction.

So: tiers 1+2 are clean and high-confidence; tier 3 is the heavy (still finite,
still ℂ-free) part. We can ship 1+2 long before 3.

### Confidence audit (2026-06-01)

No categorical blocker remains: **nothing forces ℝ/ℂ** (every step is
ℤ/ℚ/𝔽_p/ℤ_{p^k}/algebraic-ext; the only ℝ/ℂ temptation, Mignotte, is replaced
by the elementary Lagrange bound), and **no theorem on the path is unknown** —
each is named with a known ℂ-free proof. "Care, not blocker" items: the Poisson
resultant=∏-roots formula (cleanest via `Res = lc^·det(mult_B on ℚ[x]/A)`,
eigenvalues `B(αᵢ)`), the Berlekamp kernel theorem (+ new 𝔽_p infra), and
Trager. Residual risk is **volume + F\* representation friction**, not
impossibility.

---

## Update 2026-06-02 — prereq C DONE: `algebraic t r` is a field

`Core.AlgebraicConstant.Field.fst` (verified, no `admit`/`assume`; full tree 63
modules green) constructs `algebraic_field : field (algebraic t r)` for any
`r : {Some?(poly_deg r) /\ poly_irreducible r}` over any base `field t`
(specialises to ℚ).

### What was built
- **Inverse** `ac_inv x = [bezout_right r x.rep]`: for `x ≠ 0`, `x.rep` is not
  divisible by the irreducible `r`, so `irreducible_coprime_or_divides` gives
  `coprime r x.rep`; `bezout_right` is the cofactor of `x.rep` in the normalized
  Bézout identity `bezout_left·r + bezout_right·x.rep ~ 1`. The inverse is itself
  nonzero (else `r | 1`, contradicting `r_not_divides_one`).
- **Inversion identity** `ac_inv_correct`: `[x.rep · bezout_right] = [1]` in the
  quotient, proved at the divides level — from Bézout, `x.rep·br − 1 ~ −(bl·r)`,
  which `r` divides. Ring rearrangements via two standalone `canon_ring` lemmas
  (`add_neg_self`, `residue_id`).
- **`inv_congr`**: inverse respects `ac_eq` (standard uniqueness-of-inverse
  argument `ia = ia·1 = ia·(b·ib) = (ia·b)·ib = (ia·a)·ib = 1·ib = ib`, using only
  the exposed `ac_*` ring laws).
- **`1 ≠ 0`** in the quotient (`ac_one_ne_zero`), then assembly
  `mul_is_group → skewfield → field`.

### Interface additions to `Core.AlgebraicConstant` (`.fsti`)
Because the quotient operations and the `commutative_ring`/`equatable`
instances are abstract through the interface, the field construction needed
explicit reveals (all proved `= ()` inside the module, where the definitions and
the private `ac_eq_iff_divides` SMT-pattern are visible):
- `ac_eq_zero_iff_divides` : `[a] = 0  <==>  r | a.rep`.
- `ac_eq_divides` : `[a] = [b]  <==>  r | (a.rep − b.rep)` (explicit, no pattern).
- `ac_mul_rep` / `ac_add_rep` / `ac_one_rep` : operation reps.
- `ac_eq` to `is_nonzero` bridge: `is_nonzero` (w.r.t. the algebraic ring) reduces
  to `not (ac_eq · ac_zero)` only once `algebraic_ring_reveal` exposes that the
  instance's `mul`/`one`/`add`/`neg`/`zero`/`eq` ARE the `ac_*` operations (the
  instances are not `unfold`, so their projections don't reduce in SMT alone).

### Next (per the revised work order): step 2
`resultant = ∏ over roots` (Poisson) + RT payload relative to a given splitting
field. Prereq B (root theory: factor theorem, squarefree ⟹ `q'(root) ≠ 0`) is the
natural companion. No ℝ/ℂ at any point.

---

## Update 2026-06-02 (cont.) — prereq B DONE: root theory

`Core.Polynomial.Root.fst` (verified, no `admit`/`assume`; full tree 64 modules
green) over any base `field t`:

- **`poly_linear a = [neg a; one]`** — the monic degree-1 polynomial `x − a`
  (`poly_linear_deg : poly_deg = Some 1`; trimmed because `one ≠ 0` in a field).
- **`eval_linear_root a : poly_eval (x−a) a = 0`** and `eval_singleton`
  (`poly_eval [c0] c = c0`) — the small-polynomial evaluations, via two
  `sum_range_unfold_left` steps over the coeff-sum `poly_eval`.
- **Factor theorem** (`factor_forward`, `factor_backward`, `factor_theorem`):
  `poly_eval p a = 0  <==>  (x − a) | p`. Forward uses Euclidean division
  (`p = (x−a)·q + r`, `deg r < 1`), evaluates at `a` (ring-hom laws ⇒ first term
  vanishes), so `r` is a constant vanishing at `a`, hence `r ≈ 0`
  (`small_eval_zero_is_zero`); backward is `eval_mul` + `eval_linear_root`.
- **`squarefree_root_deriv_nonzero`**: `square_free q /\ q(a)=0 ==> q'(a) ≠ 0`.
  If both `q(a)=q'(a)=0` then `(x−a) | q` and `(x−a) | q'`, so `(x−a) | gcd(q,q')`,
  forcing `deg(gcd) ≥ 1` — contradicting `square_free q = coprime q q'`
  (`deg(gcd)=0`).

Gotcha logged: a bare `Some 0` literal defaults to `option int`; against
`poly_deg : option nat` it must be written `(Some 0 <: option nat)`.

Prereqs **A, B, C all done.** Next: step 2 / prereq D — determinant/resultant
specialization (`R(c) = res_x(p − c·q', q)`) ⇒ base-field Rothstein–Trager
criterion, and the resultant=∏-over-roots (Poisson) payload. No ℝ/ℂ.

---

## Update 2026-06-02 (cont.) — step 2 started: product/eval layer landed; resultant core scoped

**Landed (verified, no `admit`/`assume`; full tree now 65 modules green):**

- **`Core.Polynomial.Root.eval_linear`** — generalised the linear-poly evaluation
  to any point: `poly_eval (x − a) c = (neg a + c)` (the root case is now its
  corollary).
- **`Core.Polynomial.Product.fst`** — the polynomial-product / evaluation layer
  that the Poisson RHS and the Rothstein–Trager log-arguments both consume:
  - `poly_prod ps` = `p1*…*pn`; `eval_poly_prod : poly_eval (poly_prod ps) c =
    prod (poly_eval pᵢ c)` (ring hom over the fold);
  - `poly_prod_linears as` = `(x−a1)*…*(x−an)`;
    `eval_poly_prod_linears : poly_eval (poly_prod_linears as) c = prod (c − aᵢ)`;
  - `prod_linears_vanishes : a ∈ as ==> poly_eval (poly_prod_linears as) a = 0`
    (every listed root is a genuine root of the factored polynomial).

  This is the field-agnostic part of the RT payload: it lets us *state and
  compute* a split polynomial `A = lc·∏(x−αᵢ)` and the `v_c = ∏(x−α)` products,
  and evaluate them. It does NOT yet connect to the resultant.

**The resultant = ∏-over-roots core remains the heavy wall.** Concretely, what it
needs (none present yet — the determinant API has only Leibniz/Laplace/`col_add`,
NO triangular/diagonal/scalar lemma):

1. **New determinant theory** — `det` of a (lower-/upper-)triangular matrix =
   `∏` of the diagonal. Provable from `det_laplace_row` (expand along row 0:
   off-diagonal entries vanish so `fin_sum` collapses to one cofactor) + minor
   stays triangular + induction on `n`. Reusable, ~150–250 lines, index-heavy,
   likely wants `#push-options`.
2. **Base case `Res(x−α, B) = B(α)`** — the Sylvester matrix of monic `x−α`
   (formal deg 1) and `B` (deg `d`) is `(d+1)×(d+1)`: rows `0..d−1` upper-
   bidiagonal (`1` on diag, `−α` on superdiag), last row `= B`'s coeffs reversed.
   `d` det-preserving column ops `Cⱼ += α·Cⱼ₋₁` clear the superdiagonal, leaving a
   triangular matrix with corner entry `Σ bₖαᵏ = B(α)`; conclude with (1).
   Needs the iterated-`det_col_add` bookkeeping + (1).
3. **Multiplicativity `Res(A·C, B) = Res(A,B)·Res(C,B)`** (at matching formal
   degrees) — the Sylvester-block factorisation + `det_mul` (Cauchy–Binet,
   already proven). Harder than (1)/(2).
4. **Poisson assembly** — induct on a *provided* factorisation `A = lc·∏(x−αᵢ)`
   using (2) base-stepped by (3) and `Res(const c, B) = c^{deg B}`:
   `Res(A,B) = lc^{deg B} · ∏ B(αᵢ)`. The `∏ B(αᵢ)` side already has its
   evaluation machinery from `Core.Polynomial.Product`.

Then the **RT correspondence + assembly** (tier 2, relative to a given splitting
field) sits on top. The splitting-field *construction* (tier 3) is the separate
research wall (item E). **Recommended next concrete step: build the triangular-
determinant theorem (1)** — it is the reusable unlock for the base case and is
self-contained.

---

## Update 2026-06-02 (cont.) — step 1 DONE: triangular determinant theorem

`Core.Matrix.Triangular.fst` (verified, no `admit`/`assume`; full tree 66 modules
green):

- **`diagonal_product_from m k`** / **`diagonal_product m`** — the diagonal product
  `m[0][0]·…·m[n-1][n-1]`, via a *named recursion* (not `prod_range`-with-lambda),
  which sidesteps the lambda-unification friction when relating `m` to its minor.
- **`is_lower_triangular m`** — entries strictly above the diagonal vanish.
- **`determinant_size_one`** — `det` of a 1×1 matrix is its single entry (via
  `sum_over_perms_single` + size-1 permutation uniqueness through `perm_eq_intro`).
- **`cofactor_row_zero_off_diagonal`** + **`cofactor_row_zero_collapses`** — in a
  lower-triangular matrix the row-0 cofactor sum collapses to the corner term
  (`fin_sum_congruence` + `fin_sum_kronecker`; off-diagonal cofactors vanish
  because `m[0][k]=0` for `k>0`).
- **`diagonal_from_minor`** + **`diagonal_product_peel`** —
  `diagonal_product m = m[0][0] · diagonal_product (minor m 0 0)`.
- **`det_lower_triangular : is_lower_triangular m ==> det m = diagonal_product m`**
  — Laplace expansion along row 0 + induction on the (triangular) minor.

Lessons codified (recurring F* friction): (1) hand-rolled lambdas don't unify with
`fin_sum`/`prod_range` internal lambdas — pass the *exact* combinator term
(`pointwise_mul (fin_kronecker_delta i0) f`) or use a named recursion; (2) nat
index arithmetic must use `Prims.op_Addition` (bare `+` resolves to the typeclass
and fails `add_comm_group nat`); (3) `cofactor_term` associates as
`(minus_one_pow * m i j) * det`, not `minus_one_pow * (m i j * det)`.

**Next: step 2** — base case `Res(x−α, B) = B(α)`. Sylvester matrix of monic
`x−α` (formal deg 1) and `B` (deg `d`) is `(d+1)×(d+1)`, upper-bidiagonal with
last row `= B`'s reversed coeffs; `d` det-preserving column operations
(`det_col_add`) triangularize it (corner `= B(α)`), then `det_lower_triangular`
finishes. (Then step 3 multiplicativity via Sylvester block + `det_mul`, step 4
Poisson assembly.)

---

## Update 2026-06-02 (cont.) — determinant toolkit for step 2 complete

Applied owner feedback on arithmetic notation (never qualify `-`; keep
`Prims.op_Addition` only where bare `+` truly fails a nat-index position —
saved as memory `fstar-arith-notation`). Cleaned `Core.Matrix.Triangular.fst`
accordingly.

Extended `Core.Matrix.Triangular.fst` (verified, 66 modules green) with the rest
of the determinant toolkit step 2 needs:
- `diagonal_product_from_pointwise` / `diagonal_product_pointwise` — the diagonal
  product depends only on the diagonal entries.
- `is_upper_triangular` + `det_upper_triangular` — upper-triangular determinant =
  diagonal product (via `det_transpose` to the lower-triangular case).

So the full triangular-determinant theory (both directions) is in hand. The
remaining step-2 work is purely the Sylvester computation:
`Res(x−α, B) = B(α)` via `det_mul` with the unipotent upper-triangular shear
`U[k][j] = α^{j−k}` (for `k≤j`):
  - `det U = 1`  (`det_upper_triangular` + `diagonal_product_pointwise` vs identity);
  - `M = matrix_mul S U` is lower-triangular with diagonal `[1,…,1, B(α)]`
    (the hard part: evaluate each `vector_dot` entry — the bidiagonal rows
    collapse to two terms `α^{j−i} − α·α^{j−i−1} = 0`; the last row's corner is
    `Σ_m coeff B m · α^m = poly_eval B α`);
  - `det S = det (S·U) = det M = B(α)`.
This is the large matrix-entry computation that remains for step 2; steps 3
(multiplicativity via Sylvester block + `det_mul`) and 4 (Poisson assembly) follow.

---

## Update 2026-06-02 (cont.) — step 2 scaffolding complete; entry computation remains

`Core.Matrix.ResultantLinear.fst` (verified, 67 modules green) now holds the
shear machinery for `Res(x−α,B)=B(α)`:
- `det_unipotent_upper_triangular` — det of a unipotent (1's on diagonal) upper-
  triangular matrix is `1` (general, reusable; via `det_upper_triangular` +
  `diagonal_product_pointwise` vs identity + `det_identity`).
- `shear a` = `U[k][j] = a^{j−k}` (k≤j) else 0; `shear_upper_triangular`,
  `shear_diagonal_one`, and **`det_shear_is_one`** (`det U = 1`).

So all the surrounding pieces are done. The ONE remaining piece of step 2 is the
matrix-product entry computation: `M = matrix_mul S U` (S = `sylvester_matrix 1 d
(x−α) B`) is lower-triangular with diagonal `[1,…,1, B(α)]`, computed via
`matrix_mul_to_fin_sum` (`M[i][j] = fin_sum (k ↦ S[i][k]·U[k][j])`):
- bidiagonal rows `i<d`: only `k=i,i+1` survive → `a^{j−i} − a·a^{j−i−1} = δ_{ij}`;
- last row corner: `Σ_k coeff B(d−k)·a^{d−k} = Σ_m coeff B m · a^m = poly_eval B a`.
Then `det S = det(S·U) = diagonal_product M = B(α)` (`det_mul` + `det_shear_is_one`
+ `det_lower_triangular`). The two-nonzero-term `fin_sum` collapse (via
`fin_sum_add` + scaled `fin_sum_kronecker`) and the corner `poly_eval` reindex are
the work left. Steps 3 (multiplicativity) and 4 (Poisson assembly) follow.

---

## Update 2026-06-02 (cont.) — step 2 DONE (Res(x−α,B)=B(α)); step 3 partial (Res_{0,n}(const,B)=cⁿ); multiplicativity peeling BLOCKED

All in `Core.Matrix.ResultantLinear.fst` (verified, no `admit`/`assume`/`sorry`;
full tree **67 modules ALL GREEN**, ~46s).

### Step 2 — `Res_{1,d}(x−α, B) = B(α)`  ✅ DONE

Public theorem:
```
let resultant_linear (#t:Type) {| f: field t |} (a: t) (b: polynomial t)
  : Lemma (requires Some? (poly_deg b))
          (ensures (let cr = cr_of_id t #(id_of_f t) in
                    resultant #t #cr 1 (Some?.v (poly_deg b)) (poly_linear #t #f a) b
                    = poly_eval b a))
```
Handles BOTH `d = Some?.v(poly_deg b) >= 1` (the shear/bidiagonal route) and the
degenerate `d = 0` (`resultant_linear_const`: 1×1 Sylvester = `[coeff b 0]`).

Supporting lemmas now in the module (all reusable):
- `cpow_succ`, `coeff_poly_linear_0/_1`, `linear_shape` predicate +
  `poly_linear_is_linear_shape`.
- `syl_diag_one / syl_super_neg_a / syl_p_other_zero / syl_last_row` — Sylvester
  entries of `sylvester_matrix 1 d (x−α) B` (bidiagonal p-rows + reversed-coeff q-row).
- `shear_entry_le / _gt`, `bidiag_value` (`a^{j−i} − a·a^{j−i−1} = δ_{ij}`).
- **`bidiag_row_times_shear`** (generic `#n`): a bidiagonal row dotted with the
  shear column gives a row of the identity. `mul_row_bidiag` is the Sylvester wrapper.
- `last_row_entry_value`, **`matrix_mul_diag_value`** (generic `#n` diagonal-entry
  bridge), `mul_corner_is_eval` (`M[d][d] = poly_eval b a` via reindex
  `Σ_{k≤d} coeff b(d−k)·a^{d−k} = Σ_{m≤d} coeff b m·a^m`).
- `mul_is_lower_triangular`, `diag_prod_from_is_eval`, `mul_diagonal_product_is_eval`.
- Assembly: `det(S·U)=det S·det U` (`det_mul`), `det U=1` (`det_shear_is_one`),
  `det(S·U)=diagonal_product(S·U)=B(α)` (`det_lower_triangular`) ⇒ `det S = B(α)`.

### Step 3 — `Res_{0,n}(const c, B) = cⁿ`  ✅ DONE (one of the two Poisson pieces)

```
let resultant_const (#t:Type) {| f: field t |} (c: t{not (c = zero)}) (b: polynomial t) (n: nat{n >= 1})
  : Lemma (let cr = cr_of_id t #(id_of_f t) in
           resultant #t #cr 0 n ([c] <: polynomial t) b = cpow c n)
```
With `m_deg = 0` the Sylvester matrix of `[c]` (deg 0) and `B` (deg n) is the n×n
**diagonal** matrix `S[i][j] = (if i=j then c else 0)` (p-block only, no q-rows),
so `det S = ∏ c = cⁿ` via `det_lower_triangular` + `syl_const_diag_from`
(`diagonal_product_from = cpow c (n−k)`, `cpow_succ` induction). Supporting:
`coeff_const_poly`, `syl_const_entry`, `syl_const_lower_triangular`.

### Step 3 — peeling `Res_{m+1,n}((x−α)·A, B) = B(α)·Res_{m,n}(A, B)`  ❌ BLOCKED

This is the remaining Poisson induction step and is the genuine wall. Status:

**Why blocked.** It is multiplicativity-in-the-first-argument of the resultant,
`Res_{m1+m2,n}(A·C, B) = Res_{m1,n}(A,B)·Res_{m2,n}(C,B)` (specialised to the
linear factor `C = x−α`, using step 2 for the `B(α)` factor). The standard
machine-checked proof (cf. mathcomp/CoqEAL `resultant`, ~several hundred lines)
goes through the **"resultant = determinant of the multiplication-by-A map on
k[x]/(B), times lc(B)^{deg A}"** interpretation, or an explicit Sylvester-matrix
**block factorisation** `S(A·C,B) = (block matrix in S(A,·), S(C,·)) · permutation`
discharged by `det_mul` + a determinant block/permutation lemma. NEITHER bridge
exists in the tree yet:
  - no "resultant as det of the mult map" theorem (would need the
    `k[x]/(B)`-module-basis determinant, a sizable new development);
  - no Sylvester block-factorisation lemma (the (m+n)×(m+n) → (m+1+n)×(m+1+n)
    size change has no det-preserving column/row script as clean as step 2's
    single shear; the bidiagonal-shear trick of step 2 is special to the linear
    monic factor and does NOT generalise to multiplying by a general `A`).

**Concrete next approach (recommended, in order):**
1. Prove the Sylvester-map identity `S(A,B)·(u‖v) = coeffs(u·A + v·B)` i.e. the
   Sylvester matrix IS the matrix of the linear map
   `(u,v) ↦ u·A + v·B : k[x]_{<n} × k[x]_{<m} → k[x]_{<m+n}` in the monomial basis.
   (Reuses `coeff_poly_mul_named` / `poly_add_coeff`; index-heavy but elementary.)
2. From (1), get `Res(A·C,B)` multiplicativity by composing the maps for `A` and
   `C` and applying `det_mul` (already proven). The composition introduces a
   triangular change-of-basis whose det is `lc`-power = `1` for monic `x−α`,
   giving the clean peeling constant `B(α)` via step 2.
3. Poisson assembly (step 4): induct on a provided `A = lc·∏(x−αᵢ)` with the
   peeling lemma base-stepped by `resultant_const`, yielding
   `Res(A,B) = lc^{deg B}·∏ B(αᵢ)`; the `∏ B(αᵢ)` side already has its evaluation
   machinery in `Core.Polynomial.Product`.

Estimated size of (1)+(2): comparable to step 2 (the determinant/triangular
toolkit is reusable), but it needs the new Sylvester-as-map lemma first. Until
that lands, peeling/multiplicativity is not deliverable. Everything proven above
is committed and green; nothing is left in a broken state.

---

## Update 2026-06-02 (cont.) — step-3 prerequisite (1) DONE: Sylvester-as-map bridge; peeling factorization now FULLY scoped

`Core.Matrix.ResultantMul.fst` (verified, no `admit`/`assume`/`sorry`; full tree
**68 modules ALL GREEN**, ~44s). This lands recommended step (1) — the
Sylvester-as-linear-map bridge — and pins down the exact remaining matrix
factorization for peeling.

### Landed (verified, reusable)

```
let combo_vec (#t) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{m_deg+n_deg>0}) (u v: polynomial t) : vector t (m_deg+n_deg)
  (* slot j<n: coeff u (n-1-j); slot j>=n: coeff v (m-1-(j-n)) — u,v reversed *)

let sylvester_action (#t) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{m_deg+n_deg>0}) (p q u v: polynomial t) (i: fin (m_deg+n_deg))
  : Lemma (requires L.length u <= n_deg /\ L.length v <= m_deg)
          (ensures vector_dot (row (transpose (sylvester_matrix m_deg n_deg p q)) i)
                              (combo_vec m_deg n_deg u v)
                 = coeff (poly_add (poly_mul u p) (poly_mul v q)) ((m_deg+n_deg-1) - i))
```

i.e. `Syl(P,Q)^T` IS the matrix of the map `(u,v) ↦ u·P + v·Q` in the monomial
bases (with the descending-degree / reversed-coefficient layout the codebase
uses). This is the `+`-version of `Core.Matrix.Resultant.syl_null_vec_is_null`,
stated as a clean forward action over a commutative ring, plus the helper
`vdot_via_name` (vector_dot through a named pointwise function). Reusable for ALL
multiplicativity / map-composition arguments.

### The exact peeling factorization (CONCRETE next step — all pieces named)

Goal: `Res_{m+1,n}((x−α)A, B) = B(α)·Res_{m,n}(A, B)` (N := m+n; size N+1).

The map `φ' : (u,w) ↦ u·(x−α)·A + w·B`  (deg u<n, deg w<m+1) decomposes by
dividing `w = (x−α)·w_q + w(α)`  (deg w_q < m, w(α) a CONSTANT — Euclidean div by
the monic `x−α`, remainder is the constant `poly_eval w α`):

    u(x−α)A + wB = (x−α)·(u·A + w_q·B) + w(α)·B.

So  φ'  =  Ψ ∘ Θ  where
  • Θ : (u,w) ↦ (u, w_q, w(α))  is a UNIMODULAR (triangular, det ±1) change of
    basis on `k[x]_{<n} × k[x]_{<m+1}` (dim N+1 → dim n+m+1 = N+1); the only
    analytic content is the division `w = (x−α)w_q + w(α)`.
  • Ψ : (u, v', c) ↦ (x−α)·(u·A + v'·B) + c·B  (deg u<n, deg v'<m, c a scalar).

Ψ itself factors as a matrix PRODUCT discharged by `det_mul` (already proven):

    Ψ  =  Mul' · (Syl_{m,n}(A,B) ⊕ [1])

where (in the monomial basis of `k[x]_{<N+1}`):
  • `Syl_{m,n}(A,B) ⊕ [1]` is the block-diagonal `(N+1)×(N+1)` matrix carrying the
    smaller Sylvester matrix and a 1 in the last slot — `det = Res_{m,n}(A,B)`
    (needs a tiny "block-diag with a corner 1" det lemma: cofactor-expand the
    last row/col, OR `det_laplace` once).
  • `Mul'` has columns  `[(x−α)x^0 | (x−α)x^1 | … | (x−α)x^{N−1} | B]`  — i.e. the
    multiplication-by-(x−α) operator on the first N monomials, with B in the last
    column. **`Mul'` is EXACTLY `sylvester_matrix N 1 (x−α) B`** (N copies of the
    `(x−α)`-shift, 1 copy of B), so

        det Mul' = Res_{N,1}(x−α, B) = B(α)   ←  by `resultant_linear`
                                                  (already proven, step 2; note the
                                                  degree-arg orientation N,1 vs 1,d
                                                  may need the skew-symmetry lemma
                                                  `resultant_skew_symmetry`, parity
                                                  `(N·1)` — already proven).

Then  det S' = det φ' = det Ψ · det Θ = (det Mul' · det(Syl⊕1)) · (±1)
             = B(α) · Res_{m,n}(A,B)  (sign is +1; verify via the parity bookkeeping).

### What remains to mechanize (in order; each piece's tool exists)
1. **block-diag-corner-1 det**: `det (S ⊕ [1]) = det S` for an `(N+1)` matrix that
   is `S` on the top-left `N×N` block, `1` at `(N,N)`, and `0` in the last
   row/col off the corner. One Laplace expansion along the last row
   (`det_laplace_row`) — the minor is `S`, the off-corner entries vanish. ~40 lines.
2. **`Mul' = sylvester_matrix N 1 (x−α) B`** entrywise (`sylvester_*_block_lookup`
   + `coeff_poly_linear`), then `det Mul' = B(α)` via `resultant_linear`
   (+ `resultant_skew_symmetry` for the N,1 vs 1,N orientation). ~60 lines.
3. **The matrix equation `S'^T = (Syl(A,B)⊕1)^T · Mul'^T`** (equivalently
   `S' = Mul' · (Syl(A,B)⊕1)` after transposing) PROVED VIA THE BRIDGE: both
   sides are the matrix of the SAME map `φ'` on basis vectors; apply
   `sylvester_action` to evaluate `S'^T·e` and the product on `e`, and the
   division identity `w=(x−α)w_q+w(α)` to match. This is where `Θ` (the division)
   enters. The largest piece (~150–250 lines): needs `poly_div`/`poly_mod` by the
   monic `poly_linear α` and `poly_eval w α = remainder`, plus reconciling the
   monomial-basis column indexing of `Mul'·(Syl⊕1)` with `S'`. The unimodular Θ
   may be foldable into the column indexing rather than a separate matrix.
4. **assembly**: `det_mul` (Mul', Syl⊕1) + the three det values + parity ⇒ peeling.
   Then **step 4 (Poisson)**: induct on a provided `A = lc·∏(x−αᵢ)` using peeling,
   base case `resultant_const` (`Res_{0,n}([c],B)=cⁿ`), RHS fold mirroring
   `eval_prod_sub` in `Core.Polynomial.Product`.

**Status:** the bridge + `det_mul` + `resultant_linear` + `resultant_const` +
`resultant_skew_symmetry` are ALL proven; the peeling now reduces to the four
mechanical pieces above (no new conceptual wall, no ℝ/ℂ, no `assume`). The single
nontrivial analytic input is Euclidean division of `w` by the monic `x−α` (the
remainder = `poly_eval w α`), which `Core.Polynomial.Div` + `Core.Polynomial.Root`
already support. Nothing is left broken; tree is 68 modules ALL GREEN.

---

## Update 2026-06-02 (cont.) — Task 1 DONE; peeling pieces #1/#2 DONE; the Θ-division RED HERRING eliminated (L-matrix reformulation); ONE entry identity remains

Tree now **69 modules ALL GREEN** (~43s). New work in
`Core.Matrix.ResultantLinear.fst` (extended) and the new
`Core.Matrix.ResultantPeel.fst`. No `admit`/`assume`/`sorry`.

### Task 1 DONE — generalized linear resultant to a larger FORMAL degree
`Core.Matrix.ResultantLinear.resultant_linear_formal`:
```
resultant_linear_formal (a:t) (b:polynomial t) (bigN:nat{bigN>=1})
  : Lemma (requires Some?(poly_deg b) /\ Some?.v(poly_deg b) <= bigN)
          (ensures resultant 1 bigN (poly_linear a) b = poly_eval b a)
```
i.e. `Res_{1,N}(x−a, B) = B(a)` for ANY formal degree `N >= deg B` (the old
`resultant_linear` was tied to `N = deg B`). The shear/bidiagonal machinery is
generic in the size; the only change was the corner reindex, where summing the
`eval_term` past `deg b` is harmless by `Core.Polynomial.Eval.eval_extend`.
Supporting (also new): `mul_corner_is_eval_formal`, `diag_prod_from_is_eval_formal`.

### Peeling pieces DONE (all in `Core.Matrix.ResultantPeel.fst`)
- `coeff_linear_mul`: `coeff ((x−a)·A) k = coeff A (k−1) + (−a)·coeff A k`
  (the convolution `(x−a)·A = x·A − a·A` at the coefficient level).
- **Piece #1** `block_diag_corner1` + `block_diag_corner1_det`:
  `det (S ⊕ [1]) = det S` via one Laplace expansion along the LAST row
  (`det_laplace_row` + a single-index `fin_sum` collapse `fin_sum_collapse_at` +
  `det_pointwise_eq` to identify the `(N,N)` minor with `S`). DONE.
- **Piece #2** `det_mul_block_is_eval`:
  `det (sylvester_matrix 1 N (x−a) b) = poly_eval b a` — immediate from
  Task 1 + `resultant_unfold`. DONE.
- **det of the row-op matrix** `peel_L` / `det_peel_L = one` (unipotent
  upper-triangular, via `det_unipotent_upper_triangular`). DONE.
- **Reusable generic collapses** (over a real `#nn:pos`, anchoring `fin_sum`):
  `left_two_term_row`, `left_one_term_row` (LEFT row of `lmat` has ≤2 nonzero ⇒
  `(lmat·rmat)[i][j]` = the ≤2-term combo of rmat rows) and
  `right_three_term_col` (COLUMN j of rmat has ≤3 nonzero ⇒
  `(lmat·rmat)[i][j]` = the ≤3-term combo of lmat entries). DONE.

### KEY ADVANCE — the Θ (Euclidean-division) change-of-basis is NOT needed
The prior plan routed peeling through a unimodular `Θ` encoding
`w = (x−α)w_q + w(α)` (the "largest, ~150–250 line, division" piece). **That was
avoidable.** The correct matrix orientation is

    matrix_mul C Mul'  =  matrix_mul L S'

(NOT `Mul'·C`), where  `C = block_diag_corner1 (Syl_{m,n}(A,B))`,
`Mul' = sylvester_matrix 1 N (x−α) B`,  `S' = sylvester_matrix (m+1) n ((x−α)A) B`,
and **`L = peel_L a m n`** is the explicit unipotent bidiagonal row-op matrix
`L[i][i]=1`, `L[i][i+1]=−a` for the inner q-block `n ≤ i < N`, else 0.
Worked out entrywise:
- p-rows `i<n`:  `(C·Mul')[i][j] = coeff A(m+i−j) − a·coeff A(m+i−j+1)
                 = coeff((x−α)A)(m+1+i−j) = S'[i][j] = (L·S')[i][j]`  (L diag only).
- inner q-rows `n ≤ i < N`:  `(C·Mul')[i][j] = coeff b(i−j) − a·coeff b(i−j+1)
                 = S'[i][j] − a·S'[i+1][j] = (L·S')[i][j]`  (L bidiagonal here).
- last row `i = N`:  `(C·Mul')[N][j] = coeff b(N−j) = S'[N][j] = (L·S')[N][j]`.
Then, since `det L = 1` and `det_mul`,
    det C · det Mul' = det(C·Mul') = det(L·S') = det S'
  ⇒  **det S' = poly_eval B a · Res_{m,n}(A,B)**  (the peeling lemma) — no Θ, no
  division, no `poly_div`/`poly_rem`, no parity bookkeeping (L is genuinely det 1).

### THE ONE REMAINING GAP — the pointwise identity `C·Mul' = L·S'`
Reduces to proving, for all `i j : fin (N+1)`,
`matrix_mul mat_C mat_Mul i j = matrix_mul mat_L mat_S' i j`, then `det_pointwise_eq`
+ `det_mul` (on both products) + `det_peel_L` + `block_diag_corner1_det` +
`det_mul_block_is_eval` assemble the peeling theorem.

All TOOLS are in hand:
- `(L·S')[i][j]`: LEFT collapse — `left_one_term_row` for `i<n` and `i=N`
  (L row = single diagonal `1`), `left_two_term_row` for `n ≤ i < N`
  (L row = `1` at i, `−a` at i+1). Gives `S'[i][j]` resp. `S'[i][j]−a·S'[i+1][j]`.
- `(C·Mul')[i][j]`: RIGHT collapse — `right_three_term_col` on column j of Mul'
  (nonzero rows among `{j, j−1, N}`, weights `{1, −a, coeff b(N−j)}`), then
  `mat_C` entries are inner-Sylvester lookups (`sylvester_p/q_block_lookup`) plus
  the corner row. Match to `S'` via `coeff_linear_mul` (p-rows) / Sylvester q-block
  lookups (q-rows).
- Sylvester entry lookups: `Core.Matrix.Sylvester.sylvester_{p,q}_block_lookup`.

What makes it WORK-but-tedious (not a conceptual wall): the column-j structure of
`Mul'` has BOUNDARY cases — `j=0` (no `j−1` row), `j=N` (the `k=j` and `k=N` rows
COINCIDE) — so `right_three_term_col`'s 3 distinct nonzero rows degenerate to 2
there, needing a dummy zero-weight index or a 2-term variant. Combined with the
3 `i`-regions this is ~9 entry sub-cases, each a Sylvester lookup + a
`coeff_linear_mul`/index-arithmetic match. Estimated ~150–250 lines of careful
index bookkeeping; HIGH confidence, no new lemmas, no ℝ/ℂ, no `assume`.

F* friction logged this session (obey next time): `fin_sum`'s `add_comm_group`
instance + `let`-vs-inlined term matching is brittle — when chaining a lemma whose
`fin_sum` result must equal a goal `fin_sum`, INLINE the same terms (no `let`
aliases for the matrix/index) and annotate `fin_sum #t #(acg_of_r t #cr.cr_r) #n`,
OR collapse with the SAME lets as `det_laplace_row` produced (this fixed
`block_diag_corner1_det`).

### After the entry identity: assembly + Poisson (step 4) — UNCHANGED plan
Peeling `Res_{m+1,n}((x−a)A,B) = B(a)·Res_{m,n}(A,B)` then inducts (step 4,
`Core.Matrix.ResultantPoisson.fst`) on a PROVIDED `A = lc·∏(x−αᵢ)`
(`poly_prod_linears`), base case `resultant_const` (`Res_{0,n}([c],B)=cⁿ`), RHS a
fold mirroring `eval_prod_sub` in `Core.Polynomial.Product`, giving
`Res(A,B) = lc^{deg B}·∏ B(αᵢ)`. Nothing is left broken; 69 modules ALL GREEN.

---

## Update 2026-06-02 (cont.) — DONE: pointwise identity, PEELING lemma, AND Poisson formula. 70 modules ALL GREEN.

The closing push fully landed (no `admit`/`assume`/`sorry`; full tree **70 modules
ALL GREEN**, ~63s).

### Task 1 — pointwise identity `C*Mul' = L*S'` (all i,j)  DONE
`Core.Matrix.ResultantPeel.peel_pointwise`. All matrices coerced to a single size
`size_peel m n = (m+n)+1` via index-level `fin`-refinement coercions (`mat_c_peel`,
`mat_mul_peel`, `mat_sprime_peel`, `mat_l_peel`) so `matrix_mul` instances line up
— dissolves the `Prims.op_Addition`-ordering size friction (`1+N` vs `N+1` vs
`(m+1)+n` are propositionally equal; wrappers re-index, SMT discharges the `fin`
bound). 3 row-regions x 3 column-cases:
- last row i=bigN: collapse the single-entry C-row (corner=one) via
  `left_one_term_row` (`peel_pointwise_last`).
- inner q-rows: RHS `left_two_term_row`; LHS column collapses with a NEW
  `right_two_term_col` (boundary cols) + `right_three_term_col` (interior);
  coeff-B vanishing at i+1>n (`peel_lhs_qrow`/`peel_rhs_qrow`/`peel_pointwise_qrow`).
- p-rows i<n: reconciled via `coeff_linear_mul` packaged as `peel_prow_bridge`
  (guards the nat index, else both vanish); needs `L.length A <= m+1`.

Logged: `Prims.op_Subtraction`/`op_Addition` on nats are genuine INTEGER ops
(can be negative, NOT truncated), so `coeff p (i-j)` with `i<j` is at a negative
index = 0, matching the int-sub Sylvester lookups — why the boundary coeff-
vanishing arguments go through.

### Task 2 — PEELING lemma  DONE  `Core.Matrix.ResultantPeel.peel`
`resultant (m+1) n (poly_mul (poly_linear a) A) b = poly_eval b a * resultant m n A b`
(req `L.length A <= m+1`, `Some?(poly_deg b)`, `deg b <= n`). From `peel_pointwise`
+ `det_pointwise_eq` + `det_mul` (twice) + the four det values (`det_mat_c_peel`,
`det_mat_mul_peel` via new `det_size_transport`, `det_mat_l_peel=one`,
`det_mat_sprime_peel`). No Theta-division, no parity.

### Task 3 — POISSON product formula  DONE  `Core.Matrix.ResultantPoisson.fst`
`poisson (lc:t{lc<>0}) (roots) (b) (n>=1) : Res (length roots) n (scaled_prod lc
roots) b = cpow lc n * root_eval_product b roots` (req `Some?(poly_deg b)`,
`deg b <= n`). Relative to a PROVIDED factorization `scaled_prod lc roots` (linears
folded outside `[lc]`, so the head peels via `peel`); `root_eval_product b roots =
prod poly_eval b ai`. Induction on roots: head peels one `(x-a)` (factor
`poly_eval b a`), base `resultant_const` (`cpow lc n`). Degrees via
`scaled_prod_degree`/`scaled_prod_length`. NO splitting field constructed.

Full Poisson chain machine-checked; step 4 complete. Nothing left broken.

---

## Update 2026-06-03 — Berlekamp over 𝔽_p: computable pieces + reachable lemmas DONE; CRT/Frobenius-additivity is the WALL. 72 modules ALL GREEN.

`Core.Field.Berlekamp.fst` (verified, no `admit`/`assume`/`sorry`; full tree **72
modules ALL GREEN**, ~49s). Field-generic (works over any `field t`, hence `fp p`).

### What is built and VERIFIED

**1. Modular exponentiation (total, computable):**
- `poly_pow_mod g k m = g^k mod m` (naive reduce-after-multiply) + reveals
  `poly_pow_mod_zero`, `poly_pow_mod_succ`. Also `poly_pow g k` (no reduction)
  + `poly_pow_zero`/`poly_pow_succ`.

**2. Congruence algebra modulo m in any commutative ring** (`cong m x y := m | (x−y)`):
- `cong_refl`, `cong_sym`, `cong_trans`, `cong_mul` (multiplicative compatibility),
  `cong_eq_right`. All via the `Core.Algebra.Divisibility` toolkit (`divides_add/
  sub/mul_left/mul_right/neg/congruence_right`) + `canon_ring`.
- `cong_of_divmod : p = m*q + r ==> cong m p r`; `rem_cong : cong m p (poly_rem p m)`.

**3. poly_pow_mod CORRECTNESS (the headline computable-correctness theorem):**
- `poly_pow_mod_correct : cong f (poly_pow_mod g k f) (poly_pow g k)` — i.e. the
  modular-exponentiation routine computes the TRUE power modulo f. Induction on k,
  `cong_mul` + `rem_cong` + `cong_sym`/`cong_trans`. This is the substantive proof.

**4. Berlekamp Q matrix (Frobenius map) as a `square_matrix t n`:**
- `mono_x k = x^k`; `berlekamp_qcol f q j = (x^j)^q mod f`;
  `berlekamp_Q f q n i j = coeff (berlekamp_qcol f q j) i`. (`q` = Frobenius
  exponent, `= p` for `fp p`; supplied by caller, no primality assumed here.)

**5. `Q − I` and the kernel hook:**
- `berlekamp_QmI` (= Q − I), `berlekamp_QmI_t` (transpose).
- `berlekamp_kernel_vector : det(Q−I)=0 ==> ∃ nonzero v. (Q−I)·v = 0` — direct
  specialisation of `Core.Matrix.KernelDet.det_zero_implies_null_vec`. Gives the
  Berlekamp subalgebra membership at the coefficient-vector level.

**6. Factor extraction (computable) + reachable divisibility:**
- `berlekamp_split f h c = gcd(f, h − c)`;
  `berlekamp_split_divides_f` (gcd | f) and `berlekamp_split_divides_shift`
  (gcd | (h−c)) via `gcd_divides_left/right`.

**7. Reachable correctness:**
- `berlekamp_membership_via_powmod : cong f (poly_pow h q) h <==>
  cong f (poly_pow_mod h q f) h` — the COMPUTABLE membership test equals the
  mathematical kernel condition `h^q ≡ h (mod f)` (rests on `poly_pow_mod_correct`).
- `berlekamp_kernel_residue : h kernel element ==> each gcd(f,h−c) | f and | (h−c)`.

### THE WALL — first correctness obligation that cannot be discharged

Two independent missing theories block the headline theorem (kernel dimension =
number of distinct irreducible factors; the gcd's are the factors). Both are
genuinely absent from the codebase (greps confirm: no Fermat, no binomial-
coefficient divisibility, no field enumeration, no CRT).

**(W1) Frobenius additivity / "freshman's dream"** — needed to bridge the *matrix*
kernel (`berlekamp_kernel_vector`'s vector `v`) to the *polynomial* condition
`h^p ≡ h (mod f)` (the spec's "h in the kernel ⟺ h^p ≡ h mod f"). The Q matrix is
the matrix of `β ↦ β^p` ONLY because that map is 𝔽_p-LINEAR, which is
`(a+b)^p = a^p + b^p` over char p. Exact missing lemma:
```
val frobenius_add (#p:int{is_prime p}) (a b: polynomial (fp p))
  : Lemma (poly_eq (poly_pow (poly_add a b) p)
                   (poly_add (poly_pow a p) (poly_pow b p)))
```
Its proof needs the characteristic-p binomial theorem `p | C(p,k)` for `0<k<p`
(absent) plus the binomial expansion of `poly_pow` (absent). Without it the
coefficient vector `v` from the kernel cannot be shown to satisfy `h^p ≡ h`.

**(W2) The product/splitting identity + Fermat** — the spec's
"∏_{c∈𝔽_p}(X−c) = X^p − X applied at h", i.e.
```
val prod_shifts_eq_frobenius (#p:int{is_prime p}) (h: polynomial (fp p))
  : Lemma (poly_eq (poly_prod_linears [h−0; h−1; …; h−(p−1)])   (* ∏_{c} (h − c) *)
                   (poly_sub (poly_pow h p) h))                 (* h^p − h *)
```
needs (i) ENUMERATION of `fp p` as exactly `{0,…,p−1}` (a `list (fp p)` of all
elements — absent), and (ii) FERMAT'S LITTLE THEOREM `c^p = c ∀ c∈𝔽_p` to know
those `p` constants are exactly the roots of `X^p − X` (absent). This is what
makes `∏_c gcd(f, h−c) = f` for a kernel element `h` — the actual splitting.

**(W3) CRT decomposition** `𝔽_p[x]/(f) ≅ ∏_i 𝔽_p[x]/(f_i)` — even granting W1/W2,
the dimension count (kernel dim = #distinct irreducible factors) is the CRT
isomorphism, which is not in the codebase at all and is the deepest layer.

So the FIRST obligation on the headline path that I cannot prove is **W1
(`frobenius_add`)** — it is the immediate next step (connecting the verified Q
matrix to a polynomial statement) and it bottoms out on the characteristic-p
binomial divisibility `p | C(p,k)`, a number-theoretic fact with no current
support. Everything up to and excluding W1 is machine-checked and green.

---

## Update 2026-06-03 — W1 (Frobenius additivity) DISSOLVED + Fermat in fp p + the W2 wall pinned. 78 modules ALL GREEN.

The Frobenius-additivity wall (W1) is fully machine-checked (no `admit`/`assume`/
`sorry`; full tree **78 modules ALL GREEN**, ~55s). Five new modules:

### 1. `Core.NatBinomial.fst` — binomial coefficients + `p | C(p,k)`
ulib `FStar.Math.Fermat`'s `binomial`/`binomial_prime` are NOT exposed by its
.fsti, so re-derived standalone:
- `factorial`, `binom`, `binom_0/_lt/_n`, `pascal`.
- `binom_factorial : binom (n+m) n * (n! * m!) = (n+m)!`.
- `factorial_not_div_prime` (p ∤ k! for 0<k<p via `euclid_prime`).
- **`prime_divides_binom (p:int{is_prime p}) (k:pos{k<p}) : binom p k % p == 0`**.

### 2. `Core.Algebra.Power.fst` — ring power + BINOMIAL THEOREM
In an arbitrary `commutative_ring` (equatable `=`, with `nat_scale` carrying the
integer coefficients):
- `rpow x n` (ring power); `bterm a b n k = C(n,k)·(a^{n-k}·b^k)`.
- per-term Pascal recurrence (`bterm_pascal`), corner/edge lemmas, the Pascal
  MERGE (`merge : S(n) = a·S(n-1) + b·S(n-1)`).
- **`binomial_theorem : rpow (a+b) n = sum_range (bterm a b n) 0 (n+1)`**.

### 3. `Core.Algebra.Frobenius.fst` — freshman's dream, char-p generic
- `nat_scale_compose : nat_scale (m·n) x = nat_scale m (nat_scale n x)`.
- `nat_scale_p_divisible_zero` (p|m ∧ char p ⟹ nat_scale m x = 0).
- `bterm_middle_zero` (middle terms vanish via `prime_divides_binom`).
- **`frobenius_add (p:int{is_prime p}) (a b:t) (char_p:(y:t)->Lemma(nat_scale p y = 0))
  : rpow (a+b) p = rpow a p + rpow b p`** — char-p hypothesis is a parameter.

### 4. `Core.Field.Frobenius.fst` — instantiation at fp p and (fp p)[x]
- `fp_nat_scale_is_mul` (nat_scale n x = (n·x)%p), `fp_char_p` (nat_scale p x = 0).
- **`frobenius_fp`** : (a+b)^p = a^p + b^p in fp p.
- `coeff_nat_scale` (coeff commutes with nat_scale over the poly ring),
  `poly_fp_char_p` (char p for (fp p)[x], coefficient-wise).
- **`frobenius_poly_fp (p:int{is_prime p}) (a b: polynomial (fp p))
  : (a+b)^p poly_eq a^p + b^p`** — THE W1 STATEMENT, now PROVEN.
- `fp_rpow_is_pow` + **`fermat_fp (p:int{is_prime p}) (c: fp p) : rpow c p = c`**
  (Fermat in fp p, via ulib `FStar.Math.Fermat.fermat`).

### 5. `Core.Field.BerlekampFrobenius.fst` — bridge to Berlekamp's congruence layer
- `poly_pow_is_rpow` (Berlekamp's field-form `poly_pow` = ring-form `rpow`).
- **`frobenius_additive_mod_f : cong f ((a+b)^p) (a^p + b^p)`** — the Frobenius
  map is additive modulo f, i.e. EXACTLY what makes the Berlekamp Q matrix
  𝔽_p-linear (Q is the matrix of β↦β^p; W1's purpose in the spec).

### 6. `Core.Field.FpEnum.fst` — fp enumeration + roots of X^p − X (reachable W2)
- `fp_enum = [0;…;p-1]`, `fp_enum_length` (= p), `fp_enum_complete` (∀c. c ∈ enum).
- `polyX = x`, `eval_polyX` (eval X c = c), `eval_poly_pow` (eval(g^k) = (eval g)^k).
- **`fp_elt_is_root_of_xpx (p:int{is_prime p}) (c: fp p)
  : poly_eval (X^p − X) c = 0`** — every field element is a root of X^p − X (Fermat).

### THE WALL (W2 product identity) — precisely located

`X^p − X = ∏_{c∈fp p}(X − c)`  is NOT provable on the current foundation.
Both sides are now KNOWN to be monic degree-p polynomials agreeing (value 0) on
all p field elements (`fp_elt_is_root_of_xpx` + `eval_poly_prod_linears`/
`prod_linears_vanishes` from `Core.Polynomial.Product`). What is MISSING to
conclude equality is the **distinct-roots factorization theorem**:

```
val poly_split_distinct_roots (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t)
  : Lemma (requires Some? (poly_deg p)
                 /\ L.length roots == Some?.v (poly_deg p)        (* deg-many roots *)
                 /\ no_repeats_p roots                            (* distinct       *)
                 /\ (forall c. L.mem c roots ==> poly_eval p c = zero))  (* all roots *)
          (ensures poly_eq p (poly_scale (poly_lc p) (poly_prod_linears roots)))
```

equivalently the interpolation-uniqueness form "two polynomials of degree ≤ n
agreeing on n+1 distinct points are poly_eq". Neither exists in the tree
(greps confirm: `degree_mul` exists, but no distinct-roots count / no
interpolation / no Vandermonde / no "≤deg roots" bound). The factor theorem
(`Core.Polynomial.Root.factor_theorem`, `(x−a)|p ⟺ p(a)=0`) + `degree_mul` are
the building blocks, but the full theorem needs an induction that, at each step,
divides out one `(x−cᵢ)`, shows the remaining roots survive in the quotient
(needs `(x−cⱼ)|quotient` for j≠i, i.e. **the quotient still vanishes at the other
roots — which itself requires that a field is an integral domain and cⱼ−cᵢ ≠ 0**),
and counts degrees down to a constant = lc. That "roots survive division by a
coprime linear factor" step + the degree countdown bookkeeping is the genuine
missing development (~several hundred lines; standard but not present).

This is the FIRST obligation on the W2 path that cannot be discharged. Beyond it,
W3 (the CRT dimension count `𝔽_p[x]/(f) ≅ ∏ 𝔽_p[x]/(f_i)`) remains the deepest
layer and is entirely absent (no quotient-ring-product / CRT framework).

Everything up to and excluding `poly_split_distinct_roots` is machine-checked
and green. W1 is no longer a wall: it is proven.

---

## Update 2026-06-03 (cont.) — poly_split_distinct_roots PROVEN, W2 splitting identity PROVEN, CRT (two coprime moduli) PROVEN. 81 modules ALL GREEN.

The `poly_split_distinct_roots` wall is DISSOLVED, W2 (`X^p - X = prod_{c}(X-c)`)
is closed, and the heart of W3 (CRT for two coprime moduli) is now machine-checked
(no `admit`/`assume`/`sorry`; full tree **81 modules ALL GREEN**, ~58s).

### 1. `Core.Polynomial.Split.fst` — distinct-roots factorization (the wall)
- `poly_scale a p = poly_mul (a @ poly_zero) p` (= [a]*p).
- `poly_eq_lc` (poly_eq preserves leading coeff), `coeff_linear_mul`
  (coeff ((x-a)*A) k), `poly_lc_mul_linear` (lc((x-a)*q)=lc q),
  **`poly_lc_mul`** (lc(p*q)=lc p * lc q over an integral domain, via the
  convolution at index deg p+deg q with `sum_range_all_zero` killing all but
  the i=deg p term), `poly_add_deg_dominant` (deg/lc of a+b when deg a>deg b),
  `sub_nonzero_of_distinct`, `root_survives_division`, `poly_scale_scalar_congr`,
  `poly_mul_swap_mid`, `mul_linear_nonzero_quotient`.
- **`poly_split_distinct_roots`** : for `p` over a field with `Some?(poly_deg p)=n`,
  `length roots = n`, **`all_distinct roots`** (pairwise distinct under the FIELD `=`),
  and every listed element a root ⟹ `poly_eq p (poly_scale (poly_lc p) (poly_prod_linears roots))`.
  Induction on roots: factor out `(x-c0)` (factor theorem), the other roots survive in
  the quotient (`root_survives_division`, using `cj-c0 ≠ 0` in a field), recurse,
  reassemble (lc tracked through the monic factor by `poly_lc_mul_linear`/`poly_eq_lc`).

  NOTE on the hypothesis: the spec asked for `no_repeats_p roots` (propositional `==`),
  but the correct general-field hypothesis is `all_distinct` under the field's `eq`
  (an arbitrary `equatable` does NOT satisfy `eq x y <==> x == y`; `root_survives_division`
  genuinely needs `cj <> c0` under `=`). Over `fp p`, `eq` IS `==` (fp_equatable =
  default_equatable), so the two coincide — W2 below proves `all_distinct (fp_enum p)`.
- Added `poly_linear_lc` (monic) to `Core.Polynomial.Root.fst`.

### 2. `Core.Field.BerlekampSplit.fst` — W2 splitting identity
- `poly_one_deg_lc`, `poly_pow_monic` (deg(g^k)=k*deg g, lc=one for monic g),
  `polyX_deg`, `xp_monic` (X^p monic deg p), `xpx_monic` (X^p - X monic deg p),
  `fp_enum_from_distinct`/`fp_enum_distinct` (the enumeration is `all_distinct`).
- **`xpx_splits`** : `poly_eq (X^p - X) (poly_prod_linears (fp_enum p))` over `fp p`,
  i.e. `X^p - X = prod_{c in fp p}(X - c)`. Via `poly_split_distinct_roots` (both sides
  monic degree p, all p elements are roots by Fermat) + `poly_scale one ~ id`.
  W2 is CLOSED. With it the Berlekamp splitting `prod_c (h-c) ≡ h^p - h (mod f)`
  follows by substituting `h` (eval homomorphism, already in the tree).

### 3. `Core.Polynomial.CRT.fst` — CRT for two coprime moduli (heart of W3)
At the divisibility level (which is exactly the content of the quotient
isomorphism `t[x]/(f*g) ≅ t[x]/(f) × t[x]/(g)`):
- **`crt_inj`** (trivial kernel / injectivity):
  `coprime f g /\ f|a /\ g|a ==> (f*g)|a` (via `euclid_lemma`).
- **`crt_surj_f` / `crt_surj_g`** (surjectivity): the explicit Bezout witness
  `crt_witness f g b c = c*(bl*f) + b*(br*g)` (bl,br = Bezout cofactors,
  `bl*f + br*g ~ 1` from `bezout_identity`) satisfies `f | (witness - b)` and
  `g | (witness - c)`, i.e. `phi([witness]) = ([b],[g])`. So phi is onto.
- Supporting: `abstract_crt_surj` (fully abstract over any commutative ring +
  a Bezout hypothesis), `abstract_surj_identity`/`abstract_mul_assoc_swap`/
  `abstract_add_comm` (canon_ring ring identities), `bezout_sum_is_one`.

  KEY F* LESSON (logged): **`canon_ring` works on an ABSTRACT `commutative_ring`
  instance variable but FAILS on the concrete `polynomial_commutative_ring_instance`**
  (its projections don't reduce for the reflective tactic — even `(x+y)-y=x` fails).
  Fix: prove every ring identity as a lemma over `(#p:Type) {| pr: commutative_ring p |}`
  using `+`/`*`/`neg`, then instantiate at `#(polynomial t) #cr_p`; F* substitutes the
  instance and the `+`/`*`/`neg` become `poly_add`/`poly_mul`/`poly_neg` automatically.

### REMAINING for the full Berlekamp dimension theorem (the honest gap)
CRT for two coprime moduli is the inductive STEP. The full
`t[x]/(f) ≅ ∏_i t[x]/(f_i)` (distinct irreducible factors) and the resulting
"kernel dim = #distinct irreducible factors" need, beyond `crt_inj`/`crt_surj_*`:
1. An **iterated CRT** over a list of pairwise-coprime factors (fold the 2-moduli
   isomorphism; needs `coprime f (g*h)` from `coprime f g /\ coprime f h`, and a
   product-of-quotients carrier).
2. A **product-ring `commutative_ring` instance** for the codomain
   `algebraic t f_1 × ... × algebraic t f_k` (n-ary; F* tuple/list-indexed ring),
   plus wrapping `crt_*` into the `algebraic` quotient (`ac_eq_zero_iff_divides`
   already bridges `[a]=0 ⟺ r | a.rep`, so `crt_inj`/`crt_surj` lift directly).
3. A **𝔽_p-vector-space DIMENSION theory** (basis, dim of a product = sum of dims,
   dim of the Frobenius kernel) to turn the ring iso into the dimension count.
   This linear-algebra layer over the quotient is entirely absent and is the
   genuine next development; (1)+(2) are mechanical given the present CRT core,
   (3) is the substantial missing framework. None of it needs ℝ/ℂ or any `assume`.

So the FIRST not-yet-formalized obligation is now the **product-quotient carrier +
its commutative_ring instance** (item 2) — straightforward but not present — followed
by the dimension theory (item 3). Everything through CRT-for-two-coprime-moduli is
machine-checked and green.

---

## Update 2026-06-03 (cont.) — Berlekamp SPLITTING-STEP correctness: parts 1+2+3-forward DONE; reverse direction (f | prod(h-c)) is the WALL. 82 modules ALL GREEN.

New module `Core.Field.BerlekampSplitCorrect.fst` (verified, no `admit`/`assume`/
`sorry`; full tree **82 modules ALL GREEN**, ~62s). This makes the EXECUTABLE
Berlekamp factorization step correct: the computed factor list is a genuine
(partial) factorization of `f` — its entries divide `f`, are pairwise coprime,
and their PRODUCT divides `f`.

### What is built and VERIFIED
- `berlekamp_factors f h cs = L.map (fun c -> berlekamp_split f h c) cs`
  (= `map (gcd(f, h-c))`); `berlekamp_factors_length`, `berlekamp_factors_index`.
- const-poly coefficient layer: `const_poly_is_if` (`const_poly c = if c=0 then []
  else [c]`, via `norm`+`trefl`), `const_poly_coeff0`, `const_poly_coeff_high`,
  `const_poly_deg_le0`.
- **Part 1** `berlekamp_factors_divide_f`: each `gcd(f, h-c) | f` (`gcd_divides_left`).
  `berlekamp_factors_have_degree`: each factor is nonzero (`gcd_has_degree`, needs
  `Some?(poly_deg f)`).
- **Part 2** `berlekamp_split_pairwise_coprime` (FIELD-GENERIC): for `c <> c'`,
  `coprime (gcd(f,h-c)) (gcd(f,h-c'))`.  A common divisor `d` of `h-[c]` and
  `h-[c']` divides their difference `[c']-[c]` — a nonzero constant of degree 0
  (`shift_diff_is_const` via the abstract-CR `canon_ring` trick + `const_diff_deg`)
  — so `deg d <= 0` (`divides_degree_le`), forcing `coprime`.  Supporting field
  lemma: `abstract_shift_diff` ((h-cc)-(h-cc') = cc'-cc, abstract instance).
- **Part 3 (forward)** `berlekamp_factors_product_divides_f` (over fp p,
  `Some?(poly_deg f)`):
  `poly_prod (berlekamp_factors f h (fp_enum p)) | f`.  From each-divides-f +
  each-has-degree + pairwise-coprime (distinct enum entries via `fp_enum_index :
  index (fp_enum p) k = k`), iterate `crt_inj` via
  `Core.Polynomial.Irreducible.pairwise_coprime_divides`; bridge `poly_prod ==
  flat_product` (`poly_prod_is_flat`).

  This is exactly the iterated-CRT "coprime factors that each divide f have a
  product dividing f" — the `crt_inj` direction of the splitting theorem.

### THE WALL — reverse direction `f | prod(h-c)`  (hence `prod gcd = f` and part 4)

The other half of part 3 (`f | prod_c gcd(f,h-c)`, giving `prod = f` up to units,
both monic => equal) and ALL of part 4 (>=2 nontrivial factors) need

```
f | prod_{c in fp_enum p} (h - [c])        (= h^p - h  for a Berlekamp element h)
```

i.e. the SUBSTITUTION  `X |-> h`  in the proven splitting identity
`xpx_splits : X^p - X ~ prod_{c}(X - c)`  (Core.Field.BerlekampSplit).  Concretely
the missing lemma is

```
val subst_prod (p:int{is_prime p}) (h: polynomial (fp p))
  : Lemma (poly_eq (poly_sub (BK.poly_pow h p) h)                       (* h^p - h *)
                   (poly_prod (L.map (fun c -> poly_sub h (const_poly c)) (fp_enum p))))
```

**Why it is a wall.** It is the value of the polynomial-ring HOMOMORPHISM
`phi : fp[X] -> fp[X]`,  `phi(X) = h`,  `phi(a) = [a]` for `a in fp p`, applied to
`xpx_splits`.  No such substitution / composition homomorphism exists in the tree
(grep: `poly_eval : polynomial t -> t` evaluates at a point IN the coefficient
field `t`; there is NO `polynomial t -> polynomial t` substitution, and no
coefficient-embedding `t -> polynomial t` ring hom).  Building it is a NEW module
on the scale of `Core.Polynomial.Eval` itself: define `phi` by the coefficient sum
`Sum_i [coeff q i] * h^i`, then re-derive the ring-hom laws (`phi_add`, `phi_mul`,
`phi_one`, `phi_congruence`) — the coefficient embedding `a |-> [a]` must be shown
multiplicative/additive — and finally prove `phi (poly_prod_linears roots) =
poly_prod (map (\c. h - [c]) roots)` and `phi (X^p - X) = h^p - h`.  All elementary,
ChC-free, no `assume`; but it is the genuine next development, not reachable from
the present CRT/gcd/Product machinery alone.

Once `subst_prod` lands, the reverse direction is short: `f | h^p - h` (Berlekamp
hypothesis, `cong f (poly_pow h p) h`) + `subst_prod` give `f | prod(h-c)`; then
gcd-distributes-over-coprime-product (`gcd(f, prod(h-c)) = prod gcd(f,h-c)` for
pairwise-coprime `h-c`, provable from `pairwise_coprime_divides` + `gcd_is_maximal`
+ Euclid) and `gcd(f, m) = f` when `f | m` give `prod gcd(f,h-c) ~ f`; both monic
=> equal.  Part 4 (>=2 nontrivial) then additionally needs the kernel-DIMENSION
count (W3, the deepest absent layer — fp-vector-space dim of the Frobenius kernel
= number of distinct irreducible factors).

So the FIRST obligation that cannot currently be discharged is **`subst_prod`
(the `X |-> h` substitution homomorphism)** — everything in parts 1, 2 and the
forward (crt_inj) direction of part 3 is machine-checked and green.

---

## Update 2026-06-03 (cont.) — PART 1 CORE DONE: substitution homomorphism phi_h built & verified. 83 modules ALL GREEN.

New module `Core.Polynomial.Subst.fst` (verified, no `admit`/`assume`/`sorry`;
full tree **83 modules ALL GREEN**, ~60s). This is the "new module on the scale of
`Core.Polynomial.Eval`" the prior update identified as the FIRST obligation
blocking the Berlekamp reverse direction (`f | prod_c (h-c)`). The hard,
reusable core is complete:

### Built and VERIFIED (commutative_ring-generic)
- **`const0 c = monomial c 0`** (the coefficient embedding `t -> t[X]`) proven a
  RING HOMOMORPHISM: `const0_zero/_congr/_add/_neg/_mul/_one`, plus
  **`const0_sum_range`** (commutes with finite sums, NAMED form to dodge
  lambda-unification).
- **`poly_subst h g = Sum_i [coeff g i] * h^i`** (substitution `X |-> h`,
  evaluated in the polynomial ring) with the full ring-hom laws:
  - `subst_congr` (respects `poly_eq`), `subst_add`, `subst_neg`, `subst_sub`,
    **`subst_mul`** (the crux — via `sum_range_convolution` + per-`k` bridge
    `subst_conv` + the abstract `mul4_swap` `canon_ring` lemma + `const0_sum_range`),
    `subst_one`.
  - Supporting: `subst_term`/`subst_term_high`/`subst_extend`, `conv_coeff_t`
    (t-level convolution range lemma), `subst_pq_high`.

Four F* instance-resolution traps were found & logged to memory
`fstar-instance-resolution` (refined-coeff bare ops fail TC; `requires (x=y)`
needs an `eq_t` helper; internal `fun i->F(g i)` lambdas need NAMED-form lemmas;
pin one polynomial add-group `(pcr cr).cr_r.r_add`).

### REMAINING for `subst_prod` (the actual reverse-split input) — mechanical, bounded
`subst_prod : poly_eq (h^p - h) (poly_prod (map (\c. h - [c]) (fp_enum p)))`
follows by applying `phi_h` to `xpx_splits` (`X^p-X ~ prod_c (X-c)`). Needs only:
1. **`subst_pow`** `phi_h(g^k) ~ (phi_h g)^k` (induction, `subst_mul`+`subst_one`);
2. **`subst_const0`** `phi_h([c]) ~ [c]` (case-split `c=0`, like `subst_one`);
3. **`subst_linear`** `phi_h(x-c) ~ h-[c]` (2-term `poly_subst` of `[neg c; one]`);
4. **`subst_poly_prod_linears`** `phi_h(prod_linears roots) ~ poly_prod (map (\c. h-[c]) roots)`
   (induction, `subst_mul`+`subst_linear`);
5. assembly: `subst_congr` on `xpx_splits`, with `xpx = poly_sub (poly_pow polyX p) polyX`
   and `phi_h(polyX)~h` (`subst_linear 0`).

CAVEAT (the one real friction left): `xpx`/`poly_prod_linears`/`poly_pow`/`const_poly`
are typed with DIFFERENT `commutative_ring (fp p)` instances — `fp_comm_ring p`
(a standalone record) vs `cr_of_id (fp p) #(id_of_f (fp p) #(fp_field p))` (threaded
through `fp_field`). The application module must thread ONE consistently (use the
`cr_of_id` form to match Berlekamp's `const_poly`/`poly_pow`), or prove
`fp_comm_ring p == cr_of_id ...`. This instance-matching is the only non-obvious
step left; everything else is a direct application of the verified homs.

Nothing left broken; 83 modules ALL GREEN.

---

## Update 2026-06-03 (cont.) — #27 DONE (subst_prod), #28 first half DONE (reverse_divides). 85 modules ALL GREEN.

Two new modules (verified, no `admit`/`assume`/`sorry`; full tree **85 modules ALL
GREEN**, ~61s).

### `Core.Field.SubstProd.fst` — #27 subst_prod  ✅ DONE
The substitution homomorphism applied to the splitting identity:
- `subst_pow` (phi_h(g^k)=(phi_h g)^k), `subst_const0` (phi_h([c])=[c]),
  `subst_linear` (phi_h(x−c)=h−[c]), `subst_poly_prod_linears`
  (phi_h(∏(x−aᵢ))=∏(h−[aᵢ])), `subst_X` (phi_h(X)=h), plus `poly_pow_congr`,
  `poly_sub_congr`.
- **`subst_prod (p)(h) : poly_sub (h^p) h  ~  ∏_{c∈fp p} (h − [c])`** — applies
  `phi_h` (subst_congr) to `xpx_splits` (`X^p−X ~ ∏(X−c)`), with the LHS reduced via
  `subst_sub`+`subst_pow`+`subst_X` and the RHS via `subst_poly_prod_linears`.

F* friction logged (all in memory `fstar-instance-resolution`): the
`fp_comm_ring p` vs `fcr (fp_field p) = cr_of_id(id_of_f fp_field)` duality —
they are DEFEQ (`test_cr` proves `==` by `()`), but `poly_eq`/`poly_subst`/
`poly_sub` are instance-parameterized so SMT treats the two as distinct atoms.
Fixes that worked: (a) write the instance LITERALLY (`fp_field p`, not a `let f`)
so it matches sub-lemma signatures and the goal; (b) one `assert (cr ==
fp_comm_ring p)` to seed congruence-closure; (c) annotate `poly_sub`'s instance
explicitly (its inferred cr differed between the lemma and the goal).

### `Core.Field.BerlekampReverse.fst` — #28 first half  ✅ DONE
- **`reverse_divides (p)(f h) : cong f (h^p) h  ==>  f | ∏_{c}(h − [c])`** — the
  kernel condition `cong f (h^p) h = f | (h^p − h)` transported through
  `subst_prod` by `divides_congruence_right`. (`shift_product` = `∏(h−[c])`.)
- `const0_eq_const_poly` : `const0 c ~ const_poly c` (bridges `subst_prod`'s
  `[c]` to Berlekamp's `gcd(f, h − const_poly c)` factors).

Gotcha logged: `open FStar.Math.Euclid` SHADOWS `Core.Algebra.Divisibility.divides`
with the int-only Euclid `divides` (no implicits) → "Inconsistent argument
qualifiers". Use `module EU = FStar.Math.Euclid` and `EU.is_prime` instead of
opening it.

### #28 second half (∏gcd ~ f) — ✅ DONE (2026-06-03)
New module **`Core.Polynomial.CoprimeProduct.fst`** (9 lemmas, all green), abstract
over any field-coefficient polynomial ring:
- `divides_mul_pair`, `coprime_both_divisors`, `pcd2` (coprime divisors → product
  divides, via `euclid_lemma`).
- **`divisor_splits`** (crux): `g | m·n ⟹ g | gcd(g,m)·gcd(g,n)`, by a 4-term
  Bézout expansion (`ext_gcd_correct`/`is_gcd` + an abstract `canon_ring` identity).
  UNCONDITIONAL (no coprimality needed).
- Two-factor distribution: `gcd_mn_divides_prod` (B, unconditional),
  `prod_divides_gcd_mn` (A, needs `coprime m n`).
- `gcd_prod_divides_prod_gcd` : list form `gcd(f,∏ms) | ∏ gcd(f,ms)` (induction on B).
- **`f_divides_prod_gcd`** (capstone-B): `f | ∏ms ⟹ f | ∏ gcd(f,ms)`. Key shortcut:
  `f | ∏ms ⟹ f | gcd(f,∏ms)` is just `gcd_is_maximal`+`divides_refl`, so direction B
  needs NO coprimality / associate bookkeeping — only the unconditional list lemma.
- `poly_prod_congr` : `poly_prod` respects pointwise `poly_eq`.

In **`Core.Field.BerlekampReverse.fst`**:
- `split_eq_const0` : bridges Subst `const0` shift to Berlekamp `const_poly` shift.
- **`reverse_split_divides`** : kernel element ⟹ `f | ∏_c gcd(f,h−[c])`.
- **`berlekamp_reverse_associates`** : the #28 theorem — `f` and the Berlekamp factor
  product MUTUALLY DIVIDE (associates). `∏gcd | f` reuses #25; `f | ∏gcd` is new.

Gotcha logged (memory `fstar-comment-nesting-trap`): an unclosed `(*` in a doc
comment silently swallowed all later defs; the module still "verified" standalone
(truncated) and only the cross-module import surfaced it.

86 modules ALL GREEN.

### #29 (kernel-dim = #factors) — STARTED via the CRT/counting route (2026-06-03)
New module **`Core.Field.BerlekampKernel.fst`** (all green) — avoids abstract
vector-space/rank-nullity theory, which is greenfield (matrix infra is only
`null_vec_implies_det_zero`). Instead it builds the CRT structure of the kernel:
- `divides_self_mul`; **`cong_mul_iff`**: `coprime m n ⟹ (cong(m·n) ⟺ cong m ∧ cong n)`
  (the kernel condition splits over coprime moduli; `⟸` is `CR.crt_inj`).
- **`cong_prod_iff`**: list form `cong(∏ms) ⟺ ∀i. cong(msᵢ)` for pairwise-coprime ms
  — i.e. h is a Berlekamp element mod f ⟺ mod every factor (CRT splitting of kernel).
- **`irreducible_prime`** (reusable!): `poly_irreducible q ∧ q | a·b ⟹ q|a ∨ q|b`,
  via `~(q|a) ⟹ coprime q a` (q irreducible: gcd(q,a) is a unit or ~q) + `euclid_lemma`;
  the unit step uses the singleton inverse like `euclid_lemma`. Plus the list form
  `irreducible_divides_prod` (q | ∏ms ⟹ q | some msᵢ).
- **`cong_pow`** (reusable): `cong m a b ⟹ cong m (a^k) (b^k)` (cong respects
  poly-powers; induction via `BK.cong_mul` + `poly_pow_succ`). NB `cong_mul`'s
  precondition pairs `(x1,x2)`,`(y1,y2)` not `(x1,y1)` — call as `cong_mul m a b a' b'`.
- **`kernel_factor_constant`**: for an irreducible factor q, `cong q (h^p) h ⟹
  ∃c. q | (h−[c])` (a kernel element is CONSTANT on each irreducible factor), via
  `reverse_divides` (q | ∏_c(h−[c])) + `irreducible_divides_prod`.
- **`const0_pow`**: `(const0 c)^k ~ const0 (rpow c k)` (const0 ring-hom induction).
- **`kernel_const_is_kernel`** (converse): `q | (h−[c]) ⟹ cong q (h^p) h`, via
  `cong_pow` + `const0_pow` + Fermat `rpow c p == c` (`fermat_fp`) + `cong_sym/trans/eq_right`.
- **`kernel_factor_iff`** (MILESTONE): for irreducible q,
  `cong q (h^p) h  ⟺  ∃c. q | (h − [c])`  — i.e. a Berlekamp element is exactly one
  that is CONSTANT modulo q. The kernel is now fully *characterized* structurally
  (combine with `cong_prod_iff`: constant on every irreducible factor of f).

REMAINING for the *count* "dim = #factors":
  (a) per-factor kernel IFF — ✅ DONE (`kernel_factor_iff`).
  (b) distinctness of the p residues mod q — ✅ DONE (`const0_distinct_mod_irred`:
      c≠c' ⟹ q∤(const0 c − const0 c'), since the difference is a constant unit).
      Combined with `kernel_factor_iff` the per-factor kernel residues are pinned to
      EXACTLY the p distinct constants {[c] : c∈𝔽_p}.  (Achievability of each via
      `CR.crt_surj` is the only un-formalized half, but straightforward.)
  (c) a cardinality/dimension notion to conclude |kernel| = p^r ⟹ dim = r — needs a
      counting or finite-dim framework that does NOT yet exist (the real remaining gap;
      multi-session — start fresh).
NB: the algorithm's *splitting* guarantee is already secured by #28 (any kernel element
splits f); #29 is the *counting* result (kernel large enough to separate all factors).

### Berlekamp reducibility CRITERION — ✅ DONE (`Core.Field.BerlekampCriterion.fst`)
Algorithmically-essential content of #29 via CRT (no abstract dimension):
`nonunit_not_div_const_diff`, `splitter_in_kernel`, `splitter_not_constant`,
**`berlekamp_splitter_exists`** (coprime nonunit factorization ⟹ a non-constant kernel
element exists — a genuine splitter), `irreducible_kernel_is_constant` (converse).
Caveat logged: `square_free_coprime_factors` needs `char_zero`, so the "reducible ⟹
coprime factorization" wrapper over 𝔽_p is blocked (char-p squarefree gap) — the
criterion is stated in the reusable coprime-factorization form instead.

### §5.1.b DETERMINANT SPECIALIZATION — ✅ DONE (2026-06-03)
The eval-at-c ring hom (#15) commutes with det — the LRT-soundness foundation.
- **`Core.Polynomial.EvalSum.fst`**: `eval_sum_range`, `eval_prod_range`, `eval_sum_list`
  (poly_eval carries through sum_range/prod_range/sum_list; the poly sum/product use
  `polynomial_acg cr` / `(polynomial_commutative_ring_instance).pcr.cr_r`, whose
  add/mul fields ARE poly_add/poly_mul, matching Eval).
- Added `sum_over_perms_reveal` to `Core.Permutation.Sum` (exposes the sum_list def) and
  **`perm_entry` + `perm_product_via`** to `Core.Matrix.Determinant` (a NAMED per-index
  function so a hom can be pushed through perm_product without lambda-unification —
  the key trick; `perm_product_via` proved by `norm [delta_only perm_product,perm_entry]; trefl`).
- **`Core.Matrix.DetEval.fst`**: `eval_sum_over_perms`, `perm_product_eval`, `leibniz_eval`,
  and **`det_eval`**: `poly_eval (det m) c = det (eval_matrix m c)`.
- **`Core.Matrix.DetEval.resultant_eval`**: `poly_eval (resultant P Q) c =
  det (eval_matrix (sylvester_matrix P Q) c)` (det_eval + resultant_unfold).
- **`Core.Risch.LRTResultant.embed_const_eval`**: `poly_eval (embed_const c0) c = c0`
  (one of the two Sylvester-entry lemmas; revealed via `norm [delta_only embed_const]`).

REMAINING for the full RT spec `R(c)=res_x(p−c·q',q)` (all bounded, `det_eval` in hand):
  (i) `pzq_coeff_eval`: `poly_eval (p_minus_z_qprime_coeff p q' i) c = coeff p i − c·coeff q' i`
      — eval of the degree-≤1 z-coefficient; mirror `eval_linear`'s proof
      (`eval_term` + `sum_range_unfold_left _ 0 2`) over its 3 cases (embed_const / [0;b] / [a;b]).
  (ii) `eval_matrix (sylvester_matrix pzq q_emb) c = sylvester_matrix (p−c·q') q` entry-wise
      (`det_pointwise_eq`, using (i) + embed_const_eval on the Sylvester entries).
  (iii) chain with `resultant_eval` ⇒ `poly_eval (lrt_resultant_raw p q) c = res(p−c·q',q)`.

91 modules ALL GREEN.
