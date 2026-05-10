# Gaussian-field axiom vetting (2026-05-09)

Vetted with Gemini deep-think (2.5-pro and 3.1-pro-preview, with the latter
flagging issues confirmed by both models). Each entry uses the user's audit
rating scale: Standard / Likely correct / Needs review / Placeholder /
Flagged. Source rating per the user's CLAUDE.md axiom-management protocol.

| Axiom | File:Line | Rating | Sources | Notes |
|-------|-----------|--------|---------|-------|
| `polynomial_dense_L2_of_subGaussian` | GeneralResults/PolynomialDensityGaussian.lean:90 | **Standard** | DT-2.5 | Multivariate polynomial density in L²(μ) for sub-Gaussian probability measures. Janson, *Gaussian Hilbert Spaces*, Thm 2.6. The sub-Gaussian hypothesis implies Carleman's condition → moment determinacy → polynomial density. Hypothesis sufficient and standard. Lean signature correct. |
| `fourierMultiplier_schwartz_bound` | SchwartzFourier/ResolventUniformBound.lean:150 | **Likely correct** | DT-2.5 | Hörmander multiplier theorem for `𝓢(ℝ)`: bounded uniformly across symbol families with uniform derivative bounds. Stein, *Singular Integrals*, Ch. VI. The Schwartz-space form (continuity in the Fréchet topology) is the natural and correct formulation; uniformity over symbol families with same `(k, l, deriv_order, B, N)` matches what's typically proved. |
| `embed_l2_uniform_bound` | Cylinder/MethodOfImages.lean:326 | **Standard** | DT-2.5 | Periodization of cylinder test functions to torus: ℓ²-norm bounded by a continuous Schwartz seminorm uniformly in `Lt ≥ 1`. Stein-Weiss Ch. VII (Poisson summation). The uniformity is correct: as `Lt → ∞`, the Riemann sum converges to a finite integral; for `Lt ≥ 1`, the bound is uniform. Lower bound on `Lt` is necessary (the bound deteriorates as `Lt → 0`). |
| `cylinderMassOperator_equivariant_of_heat_comm` | Cylinder/GreenFunction.lean:277 | **⚠ Flagged — needs hypothesis fix** | DT-2.5, DT-3.1 | Axiom is **mathematically false as written**. Counterexample: `S = 2·id` commutes with the heat semigroup, but then the axiom would conjure a `U : ell2' ≃ₗᵢ[ℝ] ell2'` with `T(2f) = U(Tf)`. Since `U` is an isometry and `T` is linear, this forces `‖Tf‖ = 2‖Tf‖` ⇒ `Tf = 0`. Since `T` is injective (m > 0), this forces the test-function space to be trivial. Contradiction. **Fix:** add hypothesis that `S` is an L²-isometric continuous linear equivalence (`≃L[ℝ]` instead of `→L[ℝ]`, plus `h_S_iso : ∀ f, ‖S f‖_{L²} = ‖f‖_{L²}`). The intended use cases (Euclidean translations, time reflection, rotations) automatically satisfy both. |

## Detailed entries

### `polynomial_dense_L2_of_subGaussian`

**Statement.** For any probability measure `μ` on `Fin n → ℝ` with sub-Gaussian
tails (`∃ a > 0, ∫ exp(a · ‖x‖²) dμ < ∞`) and any `f ∈ L²(μ)`, multivariate
polynomials approximate `f` in L²(μ) arbitrarily well.

**Vet (DT-2.5):** Standard. The sub-Gaussian condition implies Carleman's
condition, hence determinacy, hence polynomial density. Hypothesis is
strong but right; weaker hypotheses (e.g., second moment alone) wouldn't
suffice. Lean form is correct.

### `fourierMultiplier_schwartz_bound`

**Statement.** For any smooth Fourier symbol `σ` with `|D^m σ(p)| ≤ B(1+|p|)^N`
for `m ≤ deriv_order`, the multiplier `M_σ : f ↦ 𝓕⁻¹(σ · 𝓕f)` satisfies the
Schwartz seminorm bound `p_{k,l}(M_σ f) ≤ C' · sup_{(k',l') ∈ s} p_{k',l'}(f)`
where `(C', s)` depend only on `(k, l, deriv_order, B, N)`, not on `σ`.

**Vet (DT-2.5):** Likely correct. Standard form for continuity of `M_σ` on
the Fréchet space `𝓢(ℝ)`. The use of a Finset sup of seminorms is the
canonical way to express continuity. Uniformity over the symbol family is
correctly captured by the quantifier order (`∃ s C', ∀ σ`).

### `embed_l2_uniform_bound`

**Statement.** There's a single continuous Schwartz seminorm `q` on cylinder
test functions such that for all torus circumferences `Lt ≥ 1`, the L²-norm
of the time-periodized function on the torus is bounded by `q(f)²`.

**Vet (DT-2.5):** Standard. Direct application of Poisson summation +
Parseval: the L²-norm is `(1/Lt) Σ_k |𝓕h(2πk/Lt)|²`, controlled uniformly
by Riemann-sum-to-integral approximation for `Lt ≥ 1`.

### `cylinderMassOperator_equivariant_of_heat_comm`

**Statement (current, FALSE).** If a CLM `S : CylinderTestFunction L →L[ℝ]
CylinderTestFunction L` commutes with the heat semigroup, then ∃ a linear
isometric equivalence `U : ell2' ≃ₗᵢ[ℝ] ell2'` such that `T(Sf) = U(Tf)`.

**Vet (DT-2.5 + DT-3.1, both reach the same conclusion):**
The hypothesis is insufficient. Heat-semigroup commutation gives `[S, A] = 0`
and hence `[S, T] = 0` (as a *linear* intertwining), but does NOT give
norm preservation, which is required for `U` to be an isometry. Contradiction
example: `S = 2·id` satisfies the hypothesis trivially, but then `U(Tf) = 2Tf`
which is not an isometry.

**Fix (suggested by both 2.5 and 3.1):**

```lean
axiom cylinderMassOperator_equivariant_of_heat_comm
    (mass : ℝ) (hmass : 0 < mass)
    -- (1) Upgrade S to a continuous linear equivalence (for surjectivity of U)
    (S : CylinderTestFunction L ≃L[ℝ] CylinderTestFunction L)
    -- (2) Add L²-isometry hypothesis (for U to be an isometry)
    (h_S_iso : ∀ f, ‖S f‖_{L²} = ‖f‖_{L²})
    (h_heat : ∀ {t : ℝ} (ht : 0 ≤ t) (f : CylinderTestFunction L),
      cylinderHeatSemigroup L ht mass (S f) =
      S (cylinderHeatSemigroup L ht mass f)) :
    ∃ U : ell2' ≃ₗᵢ[ℝ] ell2', ...
```

(The `‖·‖_{L²}` notation should be replaced with whatever the project uses
for the L² norm on cylinder test functions.)

**Physical interpretation (from DT-3.1):** the intended use cases — Euclidean
translations, time reflection, rotations — automatically satisfy both the
bijection and L²-isometry conditions, so the strengthening is harmless. By
Wigner's theorem, symmetries in QFT are represented by full unitaries, which
matches the strengthened conclusion type.

**Action items:**
1. Open an issue / PR on gaussian-field with the fix.
2. Update consumers in `Cylinder/GreenFunction.lean` to pass the additional
   `h_S_iso` hypothesis. The existing call sites (spatial translation, time
   reflection equivariance) should naturally satisfy this.
3. The fix is mathematically straightforward and doesn't require new
   theorems — just rearranging the hypotheses.

## Process notes

- Models used: `gemini-2.5-pro` (default for the 4 calls run), then re-run
  on axiom #4 with explicit `gemini-3.1-pro-preview` to confirm the failure.
  Both models agreed; 3.1-pro-preview produced a sharper proof-of-failure
  via the explicit `S = 2·id` counterexample.
- The local MCP server at `~/Documents/GitHub/gaussian-field/tools/gemini_mcp/server.py`
  has been updated to default to `gemini-3.1-pro-preview` for both `chat_gemini`
  and `deep_think_gemini`. (The `tools/` directory is gitignored, so this is
  a local-only change.)
