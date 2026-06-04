# Session plan — §A base-field RT criterion COMPLETE; next = tier-2 / executable path

> **⏱ SESSION CLOCK (survives compaction — re-read this after any compaction).**
> Budget **3h**, anchored from the system clock. **Start 2026-06-04 11:17:55 +0700.**
> **Target floor 2026-06-04 14:17:55 +0700.** The target is a *lower* bound
> (AGENTS §0.5.1): do NOT stop at 14:17 if planned/STATUS work remains — keep
> drilling until the only terminal stop (executable integrator, both cases) or an
> explicit user stop. Re-run `date` periodically to check elapsed.

> **RESUME POINTER (fresh session, 2026-06-04 — updated).** Tree is GREEN (full
> build exit 0, 95 modules). §A (RT criterion) is done. **Tier-2 RT soundness is
> now ESSENTIALLY COMPLETE** in the new module `Core.Risch.RTSoundness` (59 green
> top-level decls, admit-free). Capstone proven:
> **`rt_soundness_partition`** — `d/dx[Σ_i c_i·log(∏ group_i)] = p/q` relative to a
> residue-homogeneous ordered partition of `q`'s roots (`L.flatten groups == roots`).
> En route, fully green & reusable: `partial_fraction_decomposition`
> (`p/q = Σ_b (p(β_b)/q'(β_b))/(x−β_b)`), `interpolation_identity`,
> `low_degree_many_roots_zero` (interpolation uniqueness), `scaled_log_deriv`
> (`c·v'/v = Σ c/(x−β)`), `log_deriv_prod_linears`, the whole fraction-sum algebra
> (`frac_sum`/`frac_sum_append`/`frac_sum_flatten`/`frac_sum_eq_of_residue_eq`).
> Also added public reveals to `Core.Fractions` (`fraction_add_reveal`,
> `fraction_eq_reveal`, `fraction_zero_reveal`).
>
> NEW untracked files to commit: `Core.Risch.RTSoundness.fst` (+ prior
> `Core.Matrix.ResultantConverse.fst`, `Core.Risch.RTCriterion.fst`). Modified:
> `Core.Fractions.fst/.fsti` (additive reveals), `build-all.ps1` (added RTSoundness).
>
> **START NEXT (the ONE remaining gap to fully-unconditional T8):**
>  - **T6 `vc_factorization`**: `gcd(p−c·q', q) ~ ∏_{β: q(β)=0 ∧ r_β=c}(x−β)`.
>    Sub-pieces: (a) common-root characterization `(p−c·q')(β)=0 ∧ q(β)=0 ⟺
>    q(β)=0 ∧ residue=c` (via `q'(β)≠0`); (b) gcd-of-split = ∏ common linear factors
>    (a real gcd-theory lemma — `gcd_divides`/`gcd_is_maximal` + the ∏-of-distinct
>    construction). This discharges `rt_soundness_partition`'s residue-homogeneous-
>    partition hypothesis by exhibiting the algorithm's gcd output as that partition.
>  - THEN the **executable ℚ-factorization path** (§C Hensel #30 → §D → §E → §F)
>    for the runnable integrator (tier-1). §C Hensel is greenfield (ℤ/pᵏ reduction
>    maps); the `fp_comm_ring (p^k)` ring already exists.
> Apply `AGENTS.md §0.5.1` (the HARD GATE — keep drilling; only the executable
> integrator or an explicit stop ends a session).

---

## ACTIVE SESSION PLAN (2026-06-04, 3h) — Tier-2 relative RT soundness

**Goal:** the rational-function identity `Σ_c c·(v_c'/v_c) = p/q` — the derivative
of the LRT answer `Σ cᵢ·log vᵢ` — **relative to a given splitting field** K of R·q
(K a parameter, not constructed). Foundations confirmed present & green: Poisson
`resultant=lc^n·∏eval` (`ResultantPoisson.poisson`), `poly_split_distinct_roots`,
`eval_poly_prod_linears`, `factor_theorem`, `squarefree_root_deriv_nonzero`,
`partial_fraction_two`/`bezout_identity`, Leibniz `poly_deriv_mul`+linearity,
`rational_deriv` (quotient rule), `algebraic_field`, `rt_criterion` (§A done).

**New module:** `Core.Risch.RTSoundness.fst` (add to `build-all.ps1` only once green).
Develop standalone; transfer/verify via fstar-mcp; update STATUS Part VII §A per lemma.

Decomposition (dependency order). **The combinatorial heart (Phase 1) is FRACTION-FREE**
— since `(x−β_j) | v`, each `v/(x−β_j)` is an *exact* polynomial, so the log-derivative
identity is a polynomial identity until the final assembly.

### Phase 1 — log-derivative core (fraction-free)  [START HERE]
- **T1 `poly_deriv_linear`**: `poly_eq (poly_deriv (poly_linear a)) poly_one`.
  (D(x−a) = trim[nat_scale 1 one] = [one] = poly_one.) Tiny; unblocks all of Phase 1.
- **T3a `deriv_prod_linears_step`** (the reusable Leibniz cons-step, cleaner than an
  explicit skip-sum and sufficient downstream): `poly_eq
  (poly_deriv (poly_prod_linears (a::rest)))
  (poly_add (poly_prod_linears rest) (poly_mul (poly_linear a) (poly_deriv (poly_prod_linears rest))))`.
  I.e. for `v=(x−a)·w`, `v' = w + (x−a)·w'` — the log-derivative recursion
  `v'/v = 1/(x−a) + w'/w`. Via `poly_deriv_mul` + T1 + `poly_mul_one` + congruences.
  (The explicit `Σ_a ∏_{i≠a}` skip-sum form is deferred; introduce only if assembly needs it.)

### Phase 2 — simple-pole residues
- ✅ **T4 `simple_residue`**: if `q ~ poly_mul (poly_linear b) w` then
  `poly_eval (poly_deriv q) b = poly_eval w b` (q'(β)=w(β)). GREEN.
- **T5 `partial_fraction_simple`** (rational-fn identity): for q = lc·∏(x−β_j)
  squarefree, deg p < deg q: `p/q = Σ_j r_j/(x−β_j)`, `r_j = p(β_j)/q'(β_j)`.
  **Route = interpolation** (chosen over iterated `partial_fraction_two` — avoids
  fraction-induction bookkeeping until the very end). Building blocks:
    - **L0 `prod_linears_peel`**: for `b ∈ roots`,
      `poly_prod_linears roots ~ poly_mul (poly_linear b) (poly_prod_linears (remove1 b roots))`.
      Induction on roots; head case definitional, tail case uses poly_mul comm/assoc.
    - **L1 `low_degree_many_roots_zero`** (interpolation uniqueness, reusable):
      `r` with `all_distinct roots`, `r(β)=0 ∀β∈roots`, and `(Some?(poly_deg r) ⇒
      deg r < length roots)` ⇒ `poly_eq r poly_zero`. Induction peeling a root via
      `factor_theorem`/`factor_forward` (so `(x−β)|r`, `r~(x−β)·r'`),
      `root_survives_division` (rest stay roots of `r'`), degree drops by 1.
    - **L2 `deriv_split_eval`**: q ~ lc·∏(x−β_j) ⇒ `q'(β_k) = lc·∏_{i≠k}(β_k−β_i)`
      (= residue denominator), via L0 + T4 + `eval_poly_prod_linears`.
    - **T5 assembly**: `P := Σ_j r_j·(q/(x−β_j))` (each cofactor an exact poly via L0);
      `p ~ P` by L1 applied to `p−P` (agrees at all β_k by L2, deg < n); hence
      `p/q = P/q = Σ_j r_j/(x−β_j)`.

### Phase 2.5 — fraction-level partial fractions (GREEN as of 2026-06-04)
- ✅ **interpolation_identity** (THE fraction-free heart): `p ~ residue_sum p roots roots`.
- ✅ **pf_same_denom**: `p/q = (residue_sum)/q` as fractions (`fraction_eq_reveal`).
- ✅ **residue_term_as_simple**: each summand `(r_b·cofactor_b)/q = r_b/(x−β_b)`.
- 🚧 **pf_decomp** (in progress): `p/q = Σ_b r_b/(x−β_b)` (frac_sum of simple terms);
  needs frac-add congruence + same-denom-split, both from the public Fractions reveals.

### Phase 3 — RT grouping + assembly (capstone)
- **T6 `vc_factorization`**: `v_c := gcd(p−c·q', q) ~ ∏_{j: r_j=c}(x−β_j)` —
  the roots partition by residue value `c` (a root of R). Via `rt_criterion` +
  `factor_theorem` + `poly_split_distinct_roots`.
- **T7 `log_deriv_vc`**: lift T3 to the fraction: `v_c'/v_c = Σ_{j:r_j=c} 1/(x−β_j)`.
- **T8 `rt_soundness`** (capstone): `Σ_c c·(v_c'/v_c) = p/q`. Assembly of T5+T7
  over the residue partition. This is the tier-2 headline.

**Session order:** Phase 1 fully (T1→T2→T3), then T4→T5, then push into Phase 3.
Delegate each atomic lemma to a sub-agent with the precise statement + key lemmas
(per AGENTS §0.5 / delegate-lemmas memory). T8 may carry into the next session;
that is NOT a stop condition — when this plan empties, author the next part.

---

## (archived) Session plan — finish §A (LRT soundness, step 1)

> **Status (2026-06-04).** The **RT resultant specialization is DONE and green**
> (generic form): `Core.Risch.LRTResultant.resultant_eval_specialized` proves
> `poly_eval (resultant pzq q_emb) c = resultant n dq (p − poly_scale c q') q`.
> All of §A.1–§A.5 (see `STATUS.md` Part VII §A) are ✅. Two pieces remain to
> close §A; both are precisely scoped below.
>
> **Source of truth is `STATUS.md`.** Update it after each lemma goes green.
> Develop in a scratch file (open `Core.Risch.LRTResultant`), transfer when green.

## TASK 1 — literal `lrt_resultant_raw` corollary — ✅ DONE (2026-06-04)

`lrt_resultant_specializes` is proven and green in `Core.Risch.LRTResultant.fst`
(with helpers `trim_length_le`, `coeff_zero_above_k_of_scale`, `poly_scale_deg_le`).
So **`poly_eval(lrt_resultant_raw p q) c = res_x(p − c·q', q)` is fully proven.**
The reference code below is retained for context; the actual proof needed no
`admit` (poly_scale_deg_le mirrors `poly_add_degree_bound`). **Next task is TASK 2.**

```fstar
(* needs: open Core.Polynomial.Derivative; module RES = Core.Matrix.Resultant *)
let rec trim_length_le (#t:Type) {| cr: commutative_ring t |} (cs: list t)
  : Lemma (ensures L.length (trim #t #cr cs) <= L.length cs) (decreases cs)
  = match cs with [] -> () | _ :: cs' -> trim_length_le #t #cr cs'

(* MISSING HELPER — prove this (the only gap):
   deg(poly_scale c qq) <= deg qq, i.e. its high coeffs vanish.
   Approach: coeff (poly_scale c qq) i = c * coeff qq i (poly_mul_singleton_coeff);
   for i >= k > deg qq, coeff qq i = 0 (coeff_above_degree), so coeff = c*0 = 0.
   Then "all coeffs >= k are zero ==> poly_deg < k" — find/prove the converse of
   coeff_above_degree (check Core.Polynomial.Div.fst's poly_deg helpers; the
   leading_coeff_nonzero / poly_deg machinery has the contrapositive). Handle
   c=0 (poly_scale = poly_zero, deg None) and qq=0 separately. *)
let poly_scale_deg_le (#t:Type) {| f: field t |} (c: t) (qq: polynomial t) (k: nat)
  : Lemma (requires (None? (poly_deg qq) \/ Some?.v (poly_deg qq) < k))
          (ensures (None? (poly_deg (SP.poly_scale c qq)) \/
                    Some?.v (poly_deg (SP.poly_scale c qq)) < k))
  = admit ()  // <-- the one remaining proof

#push-options "--z3rlimit 150 --fuel 2 --ifuel 2"
let lrt_resultant_specializes (#t:Type) {| f: field t |} (p q: polynomial t) (c: t)
  : Lemma (requires Some? (poly_deg q) /\ Some?.v (poly_deg q) >= 1)
          (ensures (let q'  = poly_deriv #t #(cr_of_id t #(id_of_f t)) q in
                    let dq  = Some?.v (poly_deg q) in
                    let dp  = (match poly_deg p with | None -> 0 | Some d -> d) in
                    let dq' = (match poly_deg q' with | None -> 0 | Some d -> d) in
                    let n   = (if dp > dq' then dp else dq') in
                    poly_eval (LRT.lrt_resultant_raw p q) c
                    = RES.resultant #t #(cr_of_id t #(id_of_f t)) n dq
                        (poly_sub p (SP.poly_scale c q')) q))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let q'  = poly_deriv #t #cr q in
    let dq  = Some?.v (poly_deg q) in
    let dp  = (match poly_deg p with | None -> 0 | Some d -> d) in
    let dq' = (match poly_deg q' with | None -> 0 | Some d -> d) in
    let n   = (if dp > dq' then dp else dq') in
    LRT.build_aux_length p q' 0 (Prims.op_Addition n 1);
    trim_length_le #(polynomial t) #(crp f)
      (LRT.build_p_minus_z_qprime p q' (Prims.op_Addition n 1));      (* bound 1 *)
    map_length (fun (cc:t) -> LRT.embed_const #t #cr cc) q;
    trim_length_le #(polynomial t) #(crp f) (LRT.embed_poly q);       (* bounds 3,4 *)
    poly_scale_deg_le #t #f c q' (Prims.op_Addition n 1);            (* feeds bound 2 *)
    poly_sub_degree_bound #t #cr p (SP.poly_scale c q') (Prims.op_Addition n 1); (* bound 2 *)
    resultant_eval_specialized #t #f p q' q n dq c
#pop-options
```
(WIP copy saved at `%TEMP%\lrt_corollary_wip.fst.txt`.) Once `poly_scale_deg_le`
is proven and the `admit` removed, this corollary closes; transfer both into
`Core.Risch.LRTResultant.fst`, full-build, update `STATUS.md`.

## TASK 2 — §A.6/7 the RT criterion `iff` — ✅ DONE (2026-06-04)

`Core.Matrix.ResultantConverse.resultant_converse` (the hard converse) +
`Core.Risch.RTCriterion.rt_criterion` (the iff `poly_eval(lrt_resultant_raw p q) c
= 0 ⟺ deg(gcd(p−c·q', q)) ≥ 1`) are proven and green, admit-free. **§A's
base-field RT machinery is complete.** Next part = tier-2 relative soundness
(splitting field / sum-over-roots) — author its plan from `STATUS.md` Part VII §A
when starting next session. Original TASK 2 decomposition (now done) retained below.

### (done) original TASK 2 decomposition — §A.6/7 the RT criterion `iff` (resultant converse)

`R(c) = 0  ⟺  deg(gcd(p − c·q', q)) ≥ 1`. Forward (common factor ⟹ R=0) is
`Core.Matrix.Resultant.resultant_zero_of_common_divisor` (proven) composed with
`lrt_resultant_specializes`. **The converse `resultant m_deg n_deg P Q = 0 ⟹
deg(gcd P Q) ≥ 1` is the work.** ALL building blocks exist — it is assembly +
a coprime endgame. Put it in a new `Core.Matrix.ResultantConverse.fst` (matrix
level, generic P Q), then a thin `Core.Risch.RTCriterion.fst` wraps it via
`lrt_resultant_specializes`. Precise per-lemma decomposition (verified the hooks
exist 2026-06-04):

  Setup: `P Q : polynomial t`, `m_deg n_deg` with `len P ≤ m_deg+1`,
  `len Q ≤ n_deg+1`, `deg Q = n_deg` (Q the monic-ish denominator), `Q ≠ 0`.
  1. **`resultant_unfold` + `det_transpose`**: `resultant = det(Syl) =
     det(transpose Syl)`. So `res = 0 ⟹ det(Sᵀ) = 0`.
  2. **`KernelDet.det_zero_implies_null_vec (transpose Syl)`**: gives
     `∃ w (k:fin size). is_nonzero (w k) ∧ ∀ i. vector_dot (row (Sᵀ) i) w = 0`.
     (size = m_deg+n_deg.)
  3. **NEW `combo_vec_surjective`**: any `w : fin size → t` equals
     `ResultantMul.combo_vec m_deg n_deg u v` for `u,v` read off w
     (u = first n_deg slots as a poly, v = remaining m_deg slots; trim each).
     Need `len u ≤ n_deg`, `len v ≤ m_deg`, and `w = combo_vec u v`
     (pointwise). [combo_vec def at ResultantMul.fst:49 — invert its packing.]
  4. **`ResultantMul.sylvester_action m_deg n_deg P Q u v i`** (needs len bounds
     from 3): `vector_dot (row Sᵀ i) (combo_vec u v) = coeff (u·P + v·Q)
     (size−1−i)`. With step 2 (=0 for all i) ⟹ `coeff (u·P + v·Q) j = 0` for all
     j∈[0,size) (and ≥size by degree) ⟹ **NEW** `u·P + v·Q ~ poly_zero`
     (`equal_coeffs_means_poly_eq`). So `u·P ~ neg (v·Q)`.
  5. **NEW `not_both_zero`**: `w` nonzero ⟹ not (u ~ 0 ∧ v ~ 0) (contrapose
     step 3's pointwise eq with `is_nonzero (w k)`).
  6. **NEW coprime endgame** `common_factor_of_relation`: from `u·P ~ neg(v·Q)`,
     `deg u < n_deg = deg Q`, `(u,v)` not both zero, `Q ≠ 0`: suppose
     `coprime P Q` (deg gcd = 0). Then `Q | u·P` (since u·P ~ −v·Q, Q | v·Q ⟹
     Q | u·P), coprime ⟹ `Q | u` (`GCD.euclid_lemma`), but `deg u < deg Q` ⟹
     `u ~ 0` (`divides_degree_le` / `Irreducible.divides_degree_le`); then
     `v·Q ~ 0` ⟹ `v ~ 0` (`Q≠0`, integral domain `poly_domain_law`) ⟹ both
     zero, contradicting (5). Hence `¬coprime P Q`, i.e. `deg(gcd P Q) ≥ 1`.
  7. **`resultant_converse`** = chain 1→6. Then **`rt_criterion`** (Risch level):
     `poly_eval (lrt_resultant_raw p q) c = 0 ⟺ deg(gcd (p − c·q') q) ≥ 1`,
     combining `lrt_resultant_specializes` + `resultant_zero_of_common_divisor`
     (forward) + `resultant_converse` (backward). Mind the length/deg
     hypotheses: discharge via the same bounds as `lrt_resultant_specializes`
     (`poly_scale_deg_le`, `trim_length_le`, q's degree).

  Hooks confirmed present: `det_zero_implies_null_vec` (KernelDet:809),
  `sylvester_action`/`combo_vec` (ResultantMul:83/49), `det_transpose`,
  `resultant_unfold`, `GCD.euclid_lemma`, `Irreducible.divides_degree_le`,
  `poly_domain_law`, `equal_coeffs_means_poly_eq`. New work: steps 3,5,6 (the
  combo decomposition + the coprime endgame) — ~4–6 small lemmas. Est. 1 focused
  session. Start here next.

## After §A

Per `STATUS.md` Part VII: §A tier-2 relative soundness (resultant=∏roots →
partial fractions → RT correspondence → assembly), then §B–§F (ℚ construction).
When this plan empties, author the next part from `STATUS.md` Part VII (§0.5).
