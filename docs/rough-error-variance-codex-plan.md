# `rough_error_variance` — Codex implementation plan

*Revised plan superseding (parts of) `rough-error-variance-design.md`. The
original design doc had real bugs: name collisions with
`Pphi2/NelsonEstimate/LatticeSetup.lean`, a phantom `δ ∈ (0,1)` exponent
when the proven rough-covariance bound is already linear in T, and no
account of pre-existing infrastructure. See `axiom_audit.md` for the
review trail.*

## Goal

Prove the L² bound on the rough-field error of a general Wick-polynomial
interaction, on the canonical joint measure of `(φ_S, φ_R)`, uniform in
`(a, N)` at fixed `(L, P, mass)`. This is **Step 1** of the discharge of
axiom `polynomial_chaos_exp_moment_bridge`
(`Pphi2/NelsonEstimate/PolynomialChaosBridge.lean:116`); Phase 2 will
feed this into Janson 5.10
(`gaussian-hilbert/PolynomialChaosConcentration.lean:469`,
`polynomial_chaos_concentration`) for L^p and stretched-exponential tail
bounds.

The general polynomial form is the target. Specialize the *proof body*
to pure quartic only if the general case gets stuck — keep the theorem
*signature* general so the bridge axiom can consume it directly.

## Prerequisites (assumed available)

- `wickMonomial_add_binomial` — `Pphi2/NelsonEstimate/WickBinomial.lean:95`
  (general `n` binomial decomposition of `wickMonomial n (c₁+c₂) (x+y)`).
- `roughCovariance_sq_summable` —
  `Pphi2/NelsonEstimate/CovarianceSplit.lean:203`
  (linear-in-T HS bound: `(1/|Λ|) Σ_k C_R(k)² ≤ T · a^d · c_a`).
- `canonicalSumFieldFunction`, `canonicalSmoothFieldFunction`,
  `canonicalRoughFieldFunction`, `CanonicalJoint`,
  `canonicalJointMeasure` —
  `Pphi2/NelsonEstimate/FieldDecomposition.lean:44–100`.
- `canonicalSumFieldFunction_eq_smooth_plus_rough` —
  `FieldDecomposition.lean:102`.
- Cross-moment vanishing and per-field self-moments —
  `FieldDecomposition.lean:413, 487, 567, 647`.
- **`gff_wickPower_two_site_inner`** (being added in
  `gaussian-field/GaussianField/WickMultivariate.lean` by another agent).
  Statement: for a centered lattice GFF with covariance C and per-site
  Wick subtraction,
  ```
  ∫ wickMonomial n (gffSiteVariance d N a mass ha hmass x) (ω(δ_x)) *
      wickMonomial m (gffSiteVariance d N a mass ha hmass y) (ω(δ_y))
      ∂(latticeGaussianMeasure d N a mass ha hmass) =
    if n = m then n.factorial * (gffCovariance d N a mass x y) ^ n else 0
  ```

## Theorem statement

File: `Pphi2/NelsonEstimate/RoughErrorBound.lean` — replaces the current
`True` stub at line 62.

```lean
/-- L² bound on the rough-field error of a Wick-polynomial interaction.

For any `InteractionPolynomial P`, the variance of the rough error
`E_R = :V(φ_S+φ_R):_c − :V(φ_S):_{c_S}` on the canonical joint measure
is bounded by `K(P, mass, L) · T`, uniform in `(a, N)`.

This is Step 1 of the discharge of `polynomial_chaos_exp_moment_bridge`.
Phase 2 (separate theorem `rough_error_Lp_bound`) feeds this into
`polynomial_chaos_concentration` (Janson 5.10) to obtain the L^p and
stretched-exponential tail bounds. -/
theorem rough_error_variance
    {d N : ℕ} [NeZero N]
    (P : InteractionPolynomial)
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) :
    ∃ K : ℝ, 0 < K ∧
      ∫ η, (canonicalRoughError d N a mass T P η) ^ 2
        ∂(canonicalJointMeasure d N a mass) ≤ K * T := by
  sorry
```

## Definitions to add (in `RoughErrorBound.lean`)

```lean
noncomputable def canonicalSmoothInteraction
    {d N : ℕ} [NeZero N] (a mass T : ℝ) (P : InteractionPolynomial) :
    CanonicalJoint d N → ℝ := fun η =>
  a ^ d * ∑ x : FinLatticeSites d N,
    wickPolynomial P (smoothWickConstant d N a mass T)
      (canonicalSmoothFieldFunction d N a mass η x)

noncomputable def canonicalFullInteractionJoint
    {d N : ℕ} [NeZero N] (a mass T : ℝ) (P : InteractionPolynomial) :
    CanonicalJoint d N → ℝ := fun η =>
  a ^ d * ∑ x : FinLatticeSites d N,
    wickPolynomial P (wickConstant d N a mass)
      (canonicalSumFieldFunction d N a mass η x)

noncomputable def canonicalRoughError
    {d N : ℕ} [NeZero N] (a mass T : ℝ) (P : InteractionPolynomial) :
    CanonicalJoint d N → ℝ := fun η =>
  canonicalFullInteractionJoint d N a mass T P η -
    canonicalSmoothInteraction d N a mass T P η
```

These names are deliberately distinct from `latticeSmoothInteraction` /
`latticeRoughError` in `LatticeSetup.lean:101,114`, which are on
`Configuration` (deterministic, not under expectation) and serve a
different purpose in the dynamical-cutoff layer-cake.

## Proof structure (5 steps)

### S1. Pointwise decomposition

Apply `wickMonomial_add_binomial` to each monomial
`wickMonomial k (c_S + c_R) (φ_S(x) + φ_R(x))`:

```
:φ(x)^k:_c = Σ_{j=0}^{k} C(k,j) · :φ_S(x)^j:_{c_S} · :φ_R(x)^{k-j}:_{c_R}
```

The `j = k` term equals `:φ_S(x)^k:_{c_S}`, which cancels against
`canonicalSmoothInteraction`. Sum over `k` weighted by `P.coeff k`:

```
canonicalRoughError P η =
  a^d · Σ_x Σ_k Σ_{j=0}^{k-1} P.coeff k · C(k,j) ·
    :φ_S(x)^j:_{c_S} · :φ_R(x)^{k-j}:_{c_R}
```

Lemma name: `canonicalRoughError_pointwise_decomposition`. Pure algebra,
no integration.

### S2. Reindex by `(j, m)` where `m = k − j ≥ 1`

Group by smooth-degree / rough-degree pair:

```
canonicalRoughError P η = Σ_{j ≥ 0, m ≥ 1} A(j,m) · M_{j,m}(η)
```

where

```
A(j,m)    = P.coeff (j+m) · C(j+m, j)
M_{j,m}(η) = a^d · Σ_x :φ_S(x)^j:_{c_S} · :φ_R(x)^m:_{c_R}
```

The `(j, m)` sum is finite because `P` has finite degree (`P.n ≤ deg P`).
Lemma name: `canonicalRoughError_eq_sum_M`.

### S3. Cross-term orthogonality on the joint measure

The joint measure factorizes as a product of two independent GFFs. For
distinct `(j, m) ≠ (j', m')`,
`∫ M_{j,m} · M_{j',m'} d(canonicalJointMeasure) = 0` — either the
smooth-side factors or the rough-side factors are orthogonal in the
respective single-GFF L². Apply `gff_wickPower_two_site_inner` to each
side separately and use the product structure
(`canonicalJointMeasure_eq_smoothMeasure_prod_roughMeasure` — verify
exact name in `FieldDecomposition.lean`).

Conclude:

```
‖canonicalRoughError P‖²_{L²(canonicalJointMeasure)}
  = Σ_{j ≥ 0, m ≥ 1} A(j,m)² · ‖M_{j,m}‖²_{L²}
```

Lemma name: `canonicalRoughError_L2_sq_eq_sum`.

### S4. Bound `‖M_{j,m}‖²_{L²}` per `(j, m)`

By `gff_wickPower_two_site_inner` applied to φ_S and φ_R separately:

```
‖M_{j,m}‖²_{L²} = a^{2d} · Σ_{x,y}
  (j! · C_S(x,y)^j) · (m! · C_R(x,y)^m)
```

Bound the rough-covariance factor by case on `m`:

- **m = 1.** By Cauchy-Schwarz on the y-sum:
  `Σ_x |C_R(x,y)| · |C_S(x,y)|^j
     ≤ √(Σ_x C_R(x,y)²) · √(Σ_x C_S(x,y)^{2j})`.
  The first factor is `O(√(|Λ| · T · a^d))` via
  `roughCovariance_sq_summable`. This is the `T^{1/2}`-in-norm /
  `T`-in-variance term.

- **m ≥ 2.** Pointwise: `|C_R(x,y)|^m ≤ ‖C_R‖_∞^{m−2} · C_R(x,y)²`.
  Then `Σ_x C_R(x,y)² ≤ |Λ| · T · a^d · c_a` again by
  `roughCovariance_sq_summable`. The `‖C_R‖_∞` factor is uniformly
  bounded in `(a, N)` at fixed `(L, mass)` from the heat-kernel
  representation of `C_R`.

Smooth-covariance side bounds (`Σ_x C_S(x,y)^k`, `‖C_S‖_∞`):
- Use `smoothVariance_le_log` (`CovarianceSplit.lean:140`) for the
  diagonal, which gives `c_S = C_S(x,x) ≤ A + B · |log T|`.
- Off-diagonal `Σ_x C_S(x,y)^k` is bounded by standard Hilbert-Schmidt
  arguments on the smooth covariance, uniformly in `(a, N)` at fixed L
  (the smooth covariance has finite trace).

Each `‖M_{j,m}‖²_{L²}` is `O(T)`. The polylog factors from the smooth
side are absorbed into `K(P, mass, L)`. Lemma name: `M_jm_L2_sq_bound`.

### S5. Sum over `(j, m)`, absorb into K

The `(j, m)` sum is finite (bounded by `(deg P + 1)²`); each term is
`O(T)`; constants depend only on `P`, `mass`, `L`. Conclude:

```
‖E_R‖²_{L²} ≤ K(P, mass, L) · T
```

Take `K` to be the explicit sum of bounds from S4 over all `(j, m)`
pairs with `j + m ≤ deg P`, `m ≥ 1`. Existential closes
`rough_error_variance`.

## Specialization fallback

If S4's `m ≥ 2` bookkeeping gets unwieldy at general degree, specialize
the *proof body* (not the theorem statement) to pure quartic by
case-splitting on `P.coeff k = 0 for k ≠ 4`. Keep the theorem signature
general; leave a `sorry` on non-quartic monomials with a TODO comment
explaining what's needed. The bridge axiom signature stays correct.

## Out of scope (Phase 2)

Do not implement in this PR:

- `rough_error_Lp_bound` — comes from feeding `rough_error_variance`
  into `polynomial_chaos_concentration`
  (`gaussian-hilbert/PolynomialChaosConcentration.lean:469`).
- Explicit chaos-projection identification of
  `E_R ∈ ⊕_{k=1}^{deg P} 𝓗_k` — Janson 5.10 needs only the L² bound and
  the maximum chaos degree (= `deg P`), not the projection.
- The bridge axiom discharge itself — that's a downstream consumer.

## Acceptance criteria

- `lake build` clean from scratch on the
  `session/2026-05-09-pin-and-discharge-update` branch.
- `#print axioms rough_error_variance` shows only `propext`,
  `Classical.choice`, `Quot.sound` (plus whatever
  `gff_wickPower_two_site_inner` introduces upstream).
- No new pphi2 axioms.
- Theorem signature matches the statement in this doc (general `P`, not
  specialized to quartic).
- The `True` stub at `RoughErrorBound.lean:62` is replaced.
