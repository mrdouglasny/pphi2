# Proof plan: `polynomial_chaos_exp_moment_bridge` (pphi2 Cluster A central axiom)

**Status:** Awaiting upstream prerequisites (Codex on
`polynomial_chaos_concentration` + gaussian-field agent on bridge
axioms). This plan is ready to execute as soon as those land.
Estimated effort: **2–3 weeks of focused Lean work**, ≈ 800–1500 lines
across 4–5 files.

## Target

Convert `polynomial_chaos_exp_moment_bridge` from axiom to theorem in
`Pphi2/NelsonEstimate/PolynomialChaosBridge.lean`:

```lean
theorem polynomial_chaos_exp_moment_bridge
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (a : ℝ) (ha : 0 < a),
    ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (FinLatticeField d N),
        (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K
```

This is the lattice Nelson exponential moment bound: the L²-norm of
the Boltzmann weight `exp(-V_a)` is uniformly bounded in `(a, N)`.
Per the existing docstring, the over-statement `∀ a > 0` is preserved
for downstream-consumer convenience; the proof should target
`a ∈ (0, 1]` (textbook Glimm–Jaffe Ch. 8) and absorb the large-`a`
case via `K = max(K_small, 1)` (the integral is bounded by 1 for
large `a` since `V_a → +∞` pointwise; see notes).

## Available upstream (after both parallel agents finish)

### From markov-semigroups (Codex deliverable)

```lean
theorem polynomial_chaos_concentration (n d : ℕ) (hd : 1 ≤ d) :
    ∃ c_d : ℝ, 0 < c_d ∧
      ∀ (F : Lp ℝ 2 (stdGaussianFin n)),
        F ∈ wienerChaosLE n d → ∀ (lam : ℝ), 0 < lam →
          (stdGaussianFin n) {x | lam * ‖F‖ < |F x|} ≤
            2 * ENNReal.ofReal (Real.exp (-c_d * lam ^ ((2 : ℝ) / d)))
```

### From gaussian-field (parallel agent deliverable)

```lean
theorem gffOrthonormalProj_pushforward_eq_stdGaussian
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measure.map (gffOrthonormalProj d N a mass ha hmass)
      (latticeGaussianMeasure d N a mass ha hmass) =
    Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)

theorem siteWickMonomial_eigenbasis_expansion
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (k : ℕ) (x : FinLatticeSites d N) :
    ∃ (coeff : (FinLatticeSites d N → ℕ) → ℝ),
      (∀ α, coeff α ≠ 0 → MultiIndexLattice.totalDegree α = k) ∧
      ∀ ω, wickMonomial k (gffSiteVariance d N a mass ha hmass x)
              (ω (Pi.single x 1)) =
            ∑ α ∈ multiIndicesOfDegree d N k, coeff α *
              gffMultiWickMonomial d N a mass ha hmass α ω
```

Plus the multivariate Wick / Hermite identifications already available
(`gffMultiWickMonomial_eq_hermite_product`, etc.).

### Already in pphi2 (existing infrastructure)

- `Pphi2/NelsonEstimate/CovarianceSplit.lean`:
  - `smoothCovEigenvalue T m`, `roughCovEigenvalue T m`
  - `covariance_split T m`: `λ_m = smooth + rough`
  - `smoothWickConstant`, `roughWickConstant`
  - `smoothVariance_le_log`: `c_S ≤ K₁ · (1 + |log T|)` for `d = 2`
  - `roughCovariance_sq_summable`: `∑ |C_R(x,y)|² ≤ M · T^δ`
- `Pphi2/NelsonEstimate/SmoothLowerBound.lean`:
  - `smooth_interaction_lower_bound_log`: classical deterministic
    `V_S(φ_S) ≥ -C(1 + |log T|)²` for the smooth interaction.
- `Pphi2/NelsonEstimate/RoughErrorBound.lean`:
  - **placeholder `True` theorems** for `rough_error_variance`,
    `rough_error_Lp_bound`, `rough_error_tail_bound`. These need to
    be promoted to real bounds before the bridge can close.
- `Pphi2/NelsonEstimate/HeatKernelBound.lean`:
  - heat kernel and `smoothVariance_from_heat_kernel`,
    `roughVariance_from_heat_kernel` infrastructure.
- `Pphi2/NelsonEstimate/WickBinomial.lean`:
  - Wick binomial expansion `:φ⁴: = Σ Cₖ :φ_S^k: · :φ_R^{4-k}:`.

## Mathematical strategy: Glimm–Jaffe Ch. 8 dynamical cutoff

For an even-degree interaction polynomial `P` with positive leading
coefficient and the GFF on `(ℤ/Nℤ)²` with spacing `a` and mass `m`:

### Step 1: Covariance split

Pick a scale parameter `T > 0` (the "cutoff scale"). Split the GFF
covariance `C = C_S(T) + C_R(T)` so that φ = φ_S + φ_R with `φ_S, φ_R`
independent Gaussians of covariances `C_S, C_R`. Concretely
(infrastructure already there):

* `C_S` keeps the low-frequency modes (large eigenvalues of M_a),
  `C_R` keeps the high-frequency tail.
* `c_S(T) := tr(C_S diag) ≤ K₁(1 + |log T|)` for d = 2 (smooth Wick
  constant grows polylogarithmically — `smoothVariance_le_log`).
* `‖C_R‖_{HS}² := ∑_{x,y} |C_R(x,y)|² ≤ M · T^δ` for some δ > 0
  (`roughCovariance_sq_summable`).

### Step 2: Decompose V

Apply Wick binomial expansion (`WickBinomial.lean`):
```
V(φ) = a^d Σ_x P(:φ(x)²:_{c_a})
     = V_S(φ_S) + E_R(φ, φ_S)
```
where:
* `V_S(φ_S) := a^d Σ_x P(:φ_S(x)²:_{c_S})` is a polynomial in φ_S only
  (the smooth interaction).
* `E_R := V - V_S` is the **rough error**: a polynomial of total
  degree `≤ 2 deg P` in (φ_S, φ_R) with **at least one φ_R factor in
  every monomial**. For φ⁴ (deg P = 4 in φ): E_R has the form
  `4 :φ_S³:·φ_R + 6 :φ_S²:·:φ_R²: + 4 φ_S·:φ_R³: + :φ_R⁴:`
  (each term has at least one rough factor).

### Step 3: Smooth-side classical bound

By `smooth_interaction_lower_bound_log` (already proved):
```
V_S(φ_S) ≥ -C₁ · (1 + |log T|)²   (deterministically, ∀ φ_S)
```
Reason: P is bounded below as a polynomial in `:φ²:_{c_S}` because
P(τ) is bounded below in τ ∈ ℝ; the lattice volume `a^d Σ_x ≤ L²`
(physical volume bounded); the only T-dependence is via c_S, which
grows at most as `(1 + |log T|)`.

### Step 4: Rough-side polynomial-chaos concentration

E_R is a polynomial of total degree ≤ deg P in **the rough field
φ_R**. Specifically, E_R(φ, φ_S) is a Wick polynomial in φ_R (with
coefficients depending on φ_S), and after centering it lies in the
chaos `H^{≤ deg P}(φ_R)` of the rough field.

The chain to apply `polynomial_chaos_concentration`:

(a) **Push the rough field forward to standard Gaussian**: The rough
    Gaussian field φ_R with covariance C_R has spectral decomposition
    `C_R = Σ_k roughCovEigenvalue · (e_k ⊗ e_k)` (the same eigenbasis
    as M_a, restricted to the high-frequency modes). Apply the
    gaussian-field analogue of `gffOrthonormalProj_pushforward_eq_stdGaussian`
    for the **rough** measure (a parallel construction; may need to
    instantiate the bridge for `latticeGaussianMeasure_rough` with
    rough Wick constant).

    *Implementation note:* If the upstream bridge is only stated for
    the full GFF, derive the rough version by post-composing with the
    smooth Cameron-Martin shift, OR work directly with the joint
    `(φ_S, φ_R)` measure.

(b) **Identify E_R - E[E_R | φ_S] as element of `wienerChaosLE` of
    the rough Gaussian**: The conditional centering E[E_R | φ_S]
    removes any φ_S-only constants; the remainder is a φ_R-polynomial
    of degree ≤ deg P. Use `siteWickMonomial_eigenbasis_expansion`
    applied to the rough variance to express each `:φ_R^k:_{c_R}`
    factor as a multivariate Hermite polynomial in the orthogonalized
    rough coordinates (ξ_k^R). The result lives in `wienerChaosLE n
    (deg P)` of the standard Gaussian on `Fin (rough modes) → ℝ`.

(c) **Apply concentration**: `polynomial_chaos_concentration` (Janson
    5.10) gives, for each centered F = E_R(φ, φ_S) - E[E_R | φ_S] in
    H^{≤ deg P}:
    ```
    P(|F| > λ ‖F‖_{L²}) ≤ 2 exp(-c_d · λ^{2/deg P})
    ```
    with `c_d` independent of (a, N) (since it depends only on
    deg P).

(d) **L² norm bound on E_R**: `‖E_R‖_{L²}² ≤ K₂ · T^{δ}` for some
    δ = δ(deg P) > 0, by:
    - Wick orthogonality: cross-terms in `E[E_R²]` vanish.
    - Diagonal terms: each is a sum over multi-indices α of
      `(coeff α)² · ∏_k roughCovEigenvalue^{α_k}`.
    - The smallest `roughCovEigenvalue` factor gives `T^{δ}`.

    The `RoughErrorBound.lean` placeholder `rough_error_variance`
    needs to be promoted to this real bound. See **discharge work**
    below.

(e) **Conditional tail bound**: combining (c) and (d):
    ```
    P(|E_R - E[E_R|φ_S]| > λ | φ_S) ≤ 2 exp(-c_d (λ / (K₂ T^{δ/2}))^{2/deg P})
                                     = 2 exp(-c · λ^{2/deg P} / T^{δ/deg P})
    ```
    integrating over φ_S preserves the bound (since it's deterministic
    in λ, T, and the constants don't depend on φ_S).

### Step 5: Dynamical cutoff — chosen T = T(M)

For each "depth" M > 0 of the deviation `V ≤ -M`, the split
```
V = V_S + E_R ≥ -C₁(1+|log T|)² + E_R   (using Step 3)
```
gives `V ≤ -M ⇒ E_R ≤ -M + C₁(1+|log T|)²`. Choose T = T(M) so that
`C₁(1+|log T(M)|)² = M/2`, i.e.
```
T(M) := exp(-(√(M/(2C₁)) - 1))   (positive for M > 2C₁)
```
Then `V ≤ -M ⇒ |E_R| ≥ M/2`, so by Step 4(e):
```
P(V ≤ -M) ≤ P(|E_R| ≥ M/2) ≤ 2 exp(-c (M/2)^{2/deg P} / T(M)^{δ/deg P})
                            = 2 exp(-c' · M^{2/deg P} · exp(δ √M / deg P))
                            = doubly-exponential decay in M.
```
Crucially the bound is **uniform in (a, N)** — no a- or N-dependence
in the constants once T(M) is chosen.

### Step 6: Integrate to get exp moment bound

```
∫ exp(-V)² dμ_GFF ≤ ∫ exp(2|V|) dμ_GFF
                  = 1 + ∫₀^∞ 2 · 2 exp(2M) · μ{V ≤ -M} dM   (layer-cake-ish)
```
Wait — exp(-V)² for V ≤ -M means -V ≥ M, so exp(-V)² = exp(-2V) ≥
exp(2M) when V ≤ -M. The relevant inequality is:
```
∫ exp(-2V) dμ = ∫ exp(-2V) · 1_{V ≥ 0} dμ + ∫ exp(-2V) · 1_{V < 0} dμ
              ≤ 1 + ∫_{V<0} exp(-2V) dμ
              = 1 + ∫₀^∞ 2 exp(2M) · μ{V ≤ -M} dM   (layer-cake)
```
Substituting Step 5:
```
∫₀^∞ 2 exp(2M) · 2 exp(-c' M^{2/deg P} exp(δ√M/deg P)) dM
```
which converges (the doubly-exponential decay dominates `exp(2M)`)
**uniformly in N**. Call this finite integral `K`. Then
`∫ exp(-V)² dμ ≤ K + 1`.

This `K + 1` is the witness for the bridge axiom, with the additional
`max(·, 1)` absorbing the degenerate small/large `a` corners.

## ⚠️ 2026-05-09 plan revision: field decomposition is essential

A first-pass implementation in `Pphi2/NelsonEstimate/LatticeSetup.lean`
attempted the **Wick-constant-only** decomposition: `V_S(T)` re-evaluates
`V` at the smooth Wick constant `c_S(T)` instead of `c_a`, and
`E_R(T) := V - V_S(T)` is the deterministic difference. This works for
the smooth side (`V_S(T) ≥ -M/2` deterministic, proved as
`latticeSmoothInteraction_lower_bound_at_cutoff_quartic`), but the L²
norm of the resulting chaos-2 piece scales as `‖K_GFF‖²_HS ∝ N^d` —
**not uniform in N**. The bridge axiom asserts a uniform-in-N bound,
so this decomposition cannot discharge the bridge directly.

The correct path is the **genuine Glimm–Jaffe field decomposition**:
`φ = φ_S + φ_R` with `(φ_S, φ_R)` jointly Gaussian, independent, with
covariances `C_S(T), C_R(T)` (per-mode covariance split, not a partition
of modes). Each ξ_k is split as `ξ_k = √(C_S(k)/C(k)) · η_S,k + √(C_R(k)/C(k)) · η_R,k`
with `η_S, η_R` new i.i.d. N(0,1) variables. Then:

* `V_S(φ_S) := V` evaluated at the smooth field φ_S.
* `E_R := V(φ_S + φ_R) - V_S(φ_S)` — every term in the Wick binomial
  expansion contains at least one φ_R factor.
* `‖E_R‖² ≤ (rough covariance HS norm)^k · combinatorial factors`,
  controlled uniformly by `roughCovariance_sq_summable`
  (`Σ_k C_R(T,k)² ≤ |Λ| · T · a^d · c_a = L^d · T · c_a` — uniform in N).

The abstract chain (`DynamicalCutoff`, `LayerCake`, `BridgeFromTail`,
`IntegrabilityHelpers`, `ChaosTailBridge`, `LatticeBridge`) built today
(2026-05-08/09) is **fully reusable** for the field decomposition: it
operates on abstract `V_S, E_R : ℝ → α → ℝ` and is agnostic to which
decomposition produces them. The smooth-side bound transfers directly
since `smooth_interaction_lower_bound_log_uniform` is universally
quantified over the field argument.

The new infrastructure needed (Phase 1 substance):

1. Define a joint Gaussian measure on `Configuration × Configuration`
   with covariances `C_S(T), C_R(T)`. Cleanest realization: use the
   gaussian-field pushforward `gffOrthonormalProj_pushforward_eq_stdGaussian`
   (theorem) to identify the GFF with `Measure.pi (gaussianReal 0 1)`,
   then introduce a SECOND copy of `Measure.pi (gaussianReal 0 1)` for
   the new `η_R,k` variables. The joint structure is then
   `(Measure.pi μ_ξ) × (Measure.pi μ_η)` on a doubled product space.

2. Define φ_S, φ_R as functions of the joint variables with covariances
   matching `C_S, C_R`.

3. Prove the pushforward identity: `(η_S, η_R) ↦ φ_S + φ_R` pushes
   the joint product Gaussian to the original GFF. By Gaussian
   characterization (variance matches because `C_S + C_R = C`), this
   is automatic via characteristic-function uniqueness.

4. Apply the multivariate Wick binomial
   (`gaussian-field/SchwartzNuclear.HermiteWick.wickMonomial_pow_sum_expansion`,
   now a theorem) to expand `:(φ_S + φ_R)^n:_{c_S+c_R}`. Identify the
   chaos-LE-(deg P) structure of E_R.

5. Apply Janson 5.10 (`polynomial_chaos_concentration`, theorem) to
   the rough field marginal, conditional on φ_S, then integrate over
   φ_S via Fubini. This gives the rough tail bound.

6. Plug into `chaos_neg_tail_bound` + `lintegral_layer_cake_lt_top_of_eventual_decay`,
   construct `LatticeRoughErrorSetup`, apply `bridgeAxiom_of_setup_real`.

Total estimated effort for the field-decomposition Phase 1: 800–1500
lines, multi-week. This is reduced from the original plan estimate
because the abstract chain (~600 lines today) is already in place.

The simpler `LatticeSetup.lean` content remains useful as algebraic
building blocks (the `wickMonomial_four_diff` identity, measurability
lemmas, smooth-side bound) — see the file's docstring for which
theorems transfer to the field-decomposition setting.

## Discharge work breakdown (legacy, prior to 2026-05-09 revision)

### Phase 1: Promote `RoughErrorBound.lean` placeholders (≈ 200–400 lines)

Currently the file has three `True`-conclusion placeholders:
- `rough_error_variance` → `‖E_R‖_{L²}² ≤ K · T^δ`.
- `rough_error_Lp_bound` → `‖E_R‖_{L^p} ≤ K · p^{deg P / 2} · T^{δ/2}`.
- `rough_error_tail_bound` → `P(|E_R| > λ) ≤ exp(-c λ^{2/deg P} T^{-δ/deg P})`.

**Sub-strategy**:
1. Prove `rough_error_variance` directly via Wick orthogonality +
   `roughCovariance_sq_summable`. Pure Gaussian-integration calculation.
2. Replace `rough_error_Lp_bound` with the `polynomial_chaos_concentration`-based
   derivation: identify E_R as element of chaos via the gaussian-field
   bridge axioms, apply Janson 5.10. The `p^{deg P / 2}` factor follows.
3. Derive `rough_error_tail_bound` from `polynomial_chaos_concentration`
   directly (it IS the tail bound for a chaos-LE element).

This phase is the heart of the discharge — it ties the gaussian-field
bridge to the markov-semigroups concentration and instantiates them
on the pphi2-specific rough field.

### Phase 2: Glue layer in `PolynomialChaosBridge.lean` (≈ 300–500 lines)

The actual bridge derivation:
1. Set up T = T(M) and the dynamical cutoff machinery.
2. Combine smooth lower bound + rough tail bound to get
   `P(V ≤ -M) ≤ doubly-exp(-M^{2/deg P})`.
3. Layer-cake integration to get `∫ exp(-V)² dμ ≤ K`.
4. Pick K independent of (a, N).

Sub-tasks:
- A `dynamicalCutoffScale (P : InteractionPolynomial) (M : ℝ) : ℝ`
  helper computing T(M).
- A `dynamicalCutoff_implies_rough_event` lemma: `V ≤ -M ⇒ |E_R| ≥ M/2`
  given the cutoff-scale choice.
- A `rough_event_prob_bound` lemma: integrate the conditional tail
  bound over φ_S.
- An `exp_moment_layer_cake` lemma: `∫ exp(-2V) dμ ≤ 1 + ∫₀^∞ 2 exp(2M) P(V ≤ -M) dM`.
- A `dynamic_cutoff_integral_finite` lemma: the layer-cake integral
  converges uniformly in N.

### Phase 3: Tighten the ∀ a > 0 hypothesis (recommended, ≈ 100–200 lines)

Currently the bridge is over-stated to `∀ a > 0`. **Recommendation**:
during this discharge, tighten the signature to `0 < a ∧ a ≤ 1` and
migrate downstream consumers (`nelson_exponential_estimate_lattice`,
`nelson_exponential_estimate`, the AsymTorus variant). Reasoning per
reviewer: the `K = max(K_small, 1)` absorption works mathematically
but adds an annoying branch to every downstream lemma that consumes
the bound, and downstream users of pphi2 only ever care about the
continuum limit `a → 0`. Aligning the theorem's context with its
physical meaning is worth the mechanical refactor cost.

The two existing call sites in
`Pphi2/NelsonEstimate/NelsonEstimate.lean:91` and
`Pphi2/AsymTorus/AsymTorusInteractingLimit.lean:78` need the
small-`N` absorption argument (the integral is finite for each fixed
`N` even at coarse spacing); cleanest to add a single
`nelson_per_N_integral_finite` axiom (per-`(a, N)` deterministic
finiteness) and combine via `max` with the bridge witness for `a ≤ 1`.

## Critical Mathlib gaps / sub-axioms expected

- **Joint Gaussian split via the orthogonalized-coordinate
  decomposition**: the cleanest approach is to do the smooth/rough
  split *after* the gaussian-field pushforward:
  ```
  (latticeGaussianMeasure …).map gffOrthonormalProj
    = Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)
    ≃ (μ_S' on smoothModes) ⊗ (μ_R' on roughModes)
  ```
  where `smoothModes T := {k | roughCovEigenvalue T (modeIndex k) ≤ T}`
  and `roughModes T := smoothModes Tᶜ`. The product factorisation
  is a partition of an `Measure.pi` over a `Fintype`, which **is**
  Mathlib-style but the explicit lemma is missing. Estimate ~30 lines:
  ```lean
  lemma Measure.pi_split {ι : Type*} [Fintype ι] (s : Finset ι)
      (μ : ι → Measure ℝ) :
      (Measure.pi μ).map (Equiv.subtypeSumEquiv s).toMeasurableEquiv
        = Measure.prod
            (Measure.pi (fun i : s => μ i))
            (Measure.pi (fun i : (sᶜ : Finset ι) => μ i))
  ```
  This **avoids the conditional-concentration trap** entirely:
  - The "conditional expectation `E[E_R | φ_S]`" becomes a literal
    parameterised Lebesgue integral on the rough factor: for each
    fixed `ξ_S`, integrate `E_R(ξ_S, ξ_R) ∂μ_R'`. No `condexp` API.
  - Janson 5.10 applies to the rough marginal `wienerChaosLE
    roughModes (deg P)` verbatim, giving a deterministic-in-`ξ_S`
    tail bound.
  - Outer integral over `μ_S'` is plain Fubini
    (`MeasureTheory.integral_prod`).

- **Layer-cake for `Real.exp` moments**: need
  `∫ exp(-2V) dμ ≤ 1 + 2 ∫₀^∞ exp(2M) μ{V ≤ -M} dM`. Derivable from
  Mathlib's standard layer-cake (`MeasureTheory.lintegral_comp_eq_lintegral_meas_lt`)
  on the restricted domain `{V < 0}` — splitting first into
  `{V ≥ 0}` (where `exp(-2V) ≤ 1`, integral ≤ 1) and `{V < 0}` (where
  layer-cake applies cleanly). Avoids needing to track bounded
  vs. tail regimes inside the measure pushforward.

- **Wick orthogonality with multi-index sum**: when proving
  `‖E_R‖_{L²}² ≤ K · T^δ` (Phase 1), the cross-terms vanish by Wick
  orthogonality and the diagonal becomes a sum over multi-indices α
  of `(coeff α)² · ∏_k roughCovEigenvalue^{α_k}`. **Isolate the
  combinatorial sum in a helper lemma** to avoid typeclass synthesis
  timeouts in the main bound — Lean's `ring`/`linarith` handle the
  arithmetic once the indexing is fixed in a private lemma.

## Effort estimate

* Phase 1 (rough error bounds): 1 week of focused work, ~200–400 lines.
* Phase 2 (dynamical cutoff glue): 1.5 weeks, ~300–500 lines. Most of
  the engineering is in the conditional integration and layer-cake.
* Phase 3 (tighten): 2 days if attempted, optional otherwise.

Total: **2–3 weeks**, ≈ **800–1500 lines** across:
- `Pphi2/NelsonEstimate/RoughErrorBound.lean` (extend significantly).
- `Pphi2/NelsonEstimate/PolynomialChaosBridge.lean` (replace axiom).
- Likely 1–2 new files for the dynamical-cutoff machinery and the
  conditional concentration helpers.

## Pre-flight checklist (do NOT start until these land)

- [ ] Codex output: `polynomial_chaos_concentration` is a theorem in
  markov-semigroups main.
- [ ] gaussian-field agent output: `gffOrthonormalCoord_normal`,
  `gffOrthonormalCoord_independent`,
  `gffOrthonormalProj_pushforward_eq_stdGaussian`,
  `gffOrthonormalProj_charFun` are theorems.
- [ ] gaussian-field agent output: `siteWickMonomial_eigenbasis_expansion`
  is a theorem (or stays as a self-contained axiom — the present
  plan only uses its conclusion).
- [ ] pphi2 lake-manifest bumped to pull both upstream commits.
- [ ] `lake build` clean across all three projects.

After all of the above are checked: `Pphi2/NelsonEstimate/RoughErrorBound.lean`
is the right entry point — replace the `True`-conclusion placeholders
with real bounds, then move to `PolynomialChaosBridge.lean`.

## References

- Glimm and Jaffe, *Quantum Physics: A Functional Integral Point of
  View*, Springer (1987), Chapter 8 (the dynamical cutoff method).
- Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Princeton
  (1974), Chapter V.
- S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), Theorem 5.10
  (the upstream concentration result).
- pphi2/docs/polynomial-chaos-concentration.md (pphi2's own writeup
  of the LD framing, vetted with Gemini).
- markov-semigroups/docs/polynomial-chaos-concentration-proof-plan.md
  (Codex deliverable plan).
