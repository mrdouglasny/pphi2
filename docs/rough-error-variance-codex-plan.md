# `rough_error_variance` — Codex implementation plan

*Revised 2026-05-10 (rev 2) after Gemini deep-think review (see
[`rough-error-variance-deep-think-prompt.md`](rough-error-variance-deep-think-prompt.md)
for the prompt and verbatim Gemini reply).*

*This rev fixes four issues in the previous plan: (i) a quantifier
order that allowed `K` to depend on `(a, N)`, (ii) a misuse of
Cauchy–Schwarz for the m=1 cross-term that yielded `O(T^{1/2})` instead
of `O(T)`, (iii) a use of `‖C_R‖_∞` for m≥2 that fails because the 2D
rough covariance carries the UV divergence `C_R(x,x) ∼ log(1/a)`, and
(iv) an `≤ K · T` RHS that is provably wrong because `‖C_S‖_∞ ∼
1+|log T|` injects a polylog factor. See `axiom_audit.md` for the full
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

## Convention reminder (the codebase is right; the original prompt was wrong)

In `CovarianceSplit.lean:13–17`:
- `roughCovariance T` has eigenvalues `(1 − exp(−T·λ_k))/λ_k`. For large
  `λ_k` (UV) this is `≈ 1/λ_k`, so it carries the UV singularity.
  Position-space: `C_R(x,x) ∼ log(1/a)` in 2D — diverges as `a → 0`.
- `smoothCovariance T` has eigenvalues `exp(−T·λ_k)/λ_k`. For large
  `λ_k` this is exponentially small, so it is the IR / low-frequency
  piece. Position-space: `C_S(x,x) ∼ 1 + |log T|` — diverges as `T → 0`
  but is `(a, N)`-uniform.

This is the standard Glimm–Jaffe heat-kernel cutoff convention. All
analytic bounds below assume this mapping.

## Prerequisites

### Available now

- `wickMonomial_add_binomial` — `Pphi2/NelsonEstimate/WickBinomial.lean:95`
  (general `n` binomial decomposition of `wickMonomial n (c₁+c₂) (x+y)`).
- `roughCovariance_sq_summable` —
  `Pphi2/NelsonEstimate/CovarianceSplit.lean:203`
  (`(1/|Λ|) · Σ_k C_R(k)² ≤ T · a^d · wickConstant ≤ T / mass²`,
  uniform in `(a, N)`).
- `canonicalSumFieldFunction`, `canonicalSmoothFieldFunction`,
  `canonicalRoughFieldFunction`, `CanonicalJoint`,
  `canonicalJointMeasure` —
  `Pphi2/NelsonEstimate/FieldDecomposition.lean:44–100`.
- `canonicalSumFieldFunction_eq_smooth_plus_rough` —
  `FieldDecomposition.lean:102`.
- Cross-moment vanishing and per-field self-moments —
  `FieldDecomposition.lean:413, 487, 567, 647`.
- `gff_wickPower_two_site_inner` (added separately in
  `gaussian-field/GaussianField/WickMultivariate.lean`):
  ```
  ∫ wickMonomial n (gffSiteVariance d N a mass ha hmass x) (ω(δ_x)) *
      wickMonomial m (gffSiteVariance d N a mass ha hmass y) (ω(δ_y))
      ∂(latticeGaussianMeasure d N a mass ha hmass) =
    if n = m then n.factorial * (gffCovariance d N a mass x y) ^ n else 0
  ```

### Required upstream — file as `sorry` exactly when Codex hits them

Codex should flag the **exact** signatures it needs against the actual
`canonicalSmoothCovariance` / `canonicalRoughCovariance` / measure-API
names in this codebase, then we file them as named upstream sorries.
Sketches below for orientation only.

1. **`canonicalSmoothCovariance_uniform_bound`** — `(a, N)`-uniform
   pointwise bound on the smooth covariance. Replaces the existing
   `smoothVariance_le_log_uniform`
   (`CovarianceSplit.lean:112`), whose proven constant
   `(a^d)⁻¹ · mass⁻²` is **not** `(a, N)`-uniform (the file's own
   docstring at lines 86–95 marks the `O(L^d / mass²)` uniform constant
   as Phase 2). Standard textbook (Glimm–Jaffe Thm 8.5.2).
   Approximate signature:
   ```lean
   ∃ C > 0, ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
              (h_vol : (N : ℝ) * a = L)
              (T : ℝ) (hT : 0 < T) (x y),
     canonicalSmoothCovariance d N a mass T x y ≤ C * (1 + |Real.log T|)
   ```

2. **`canonicalRoughCovariance_Lm_bound`** — `(a, N)`-uniform L^m
   summability of the rough covariance, for **all** m ≥ 1 (this unifies
   what the previous plan rev mishandled as separate m=1 and m≥2 cases).
   Standard textbook (Glimm–Jaffe Thm 8.5.2). Approximate signature:
   ```lean
   ∀ (m : ℕ) (hm : 1 ≤ m),
     ∃ C > 0, ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
                 (h_vol : (N : ℝ) * a = L)
                 (T : ℝ) (hT : 0 < T) (x),
       a^d * ∑ y, canonicalRoughCovariance d N a mass T x y ^ m ≤ C * T
   ```

3. **`joint_wick_factorization`** — measure-theoretic factorization of
   independent smooth × rough Wick monomial products under the canonical
   joint measure. Mathlib does **not** automatically split the integral
   of a product into a product of integrals; without this helper, S3
   drowns in `Integrable` typeclass goals. Approximate signature:
   ```lean
   ∫ η, f_smooth(canonicalSmoothFieldFunction … η) *
        f_rough(canonicalRoughFieldFunction … η)
        ∂(canonicalJointMeasure d N a mass) =
   (∫ η_S, f_smooth η_S ∂(canonicalSmoothMeasure d N a mass)) *
   (∫ η_R, f_rough η_R ∂(canonicalRoughMeasure d N a mass))
   ```
   (Adjust to match the exact `FieldDecomposition` API. May follow
   trivially from the product structure of `canonicalJointMeasure` if
   that is already a `Measure.prod`; check this before sorry-ing.)

## Theorem statement

File: `Pphi2/NelsonEstimate/RoughErrorBound.lean` — replaces the current
`True` stub at line 62.

```lean
/-- L² bound on the rough-field error of a Wick-polynomial interaction.

For any `InteractionPolynomial P`, the variance of the rough error
`E_R = :V(φ_S+φ_R):_c − :V(φ_S):_{c_S}` on the canonical joint measure
is bounded by `K(P, mass, L) · T · (1 + |log T|)^{deg P − 1}`, uniform
in `(a, N)` at fixed `(L, mass, P)`.

This is Step 1 of the discharge of `polynomial_chaos_exp_moment_bridge`.
Phase 2 (separate theorem `rough_error_Lp_bound`) feeds this into
`polynomial_chaos_concentration` (Janson 5.10) to obtain the L^p and
stretched-exponential tail bounds. -/
theorem rough_error_variance
    {d : ℕ} (P : InteractionPolynomial)
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
        (h_vol : (N : ℝ) * a = L),
        ∫ η, (canonicalRoughError d N a mass T P η) ^ 2
          ∂(canonicalJointMeasure d N a mass) ≤
        K * T * (1 + |Real.log T|) ^ (P.n - 1) := by
  sorry
```

Quantifier order is critical: `K` is bound **outside** the lattice
binders so that it cannot depend on `(a, N)`. The `(N : ℝ) * a = L`
constraint pins the macroscopic period.

`P.n - 1` is the maximum power of `‖C_S‖_∞ ≤ 1 + |log T|` that appears
in any cross-term (because `j ≤ P.n − 1` whenever `m ≥ 1` and `j + m ≤
P.n`). For pure quartic this is `(1+|log T|)^3`.

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

### S1. Pointwise binomial decomposition

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

Lemma: `canonicalRoughError_pointwise_decomposition`. Pure algebra, no
integration.

### S2. Reindex by `(j, m)` where `m = k − j ≥ 1`

```
canonicalRoughError P η = Σ_{j ≥ 0, m ≥ 1} A(j,m) · M_{j,m}(η)

A(j,m)    = P.coeff (j+m) · C(j+m, j)
M_{j,m}(η) = a^d · Σ_x :φ_S(x)^j:_{c_S} · :φ_R(x)^m:_{c_R}
```

Sum is finite: `j + m ≤ P.n`. Lemma:
`canonicalRoughError_eq_sum_M`.

### S3. Cross-term orthogonality on the joint measure

Square `canonicalRoughError`, integrate. Distinct `(j, m) ≠ (j', m')`
give zero cross-expectation:

1. Expand `M_{j,m} · M_{j',m'}` and apply
   `joint_wick_factorization` to split each per-site contribution into
   `(smooth integral) · (rough integral)`.
2. Apply `gff_wickPower_two_site_inner` to the smooth side: zero unless
   `j = j'`.
3. Apply `gff_wickPower_two_site_inner` to the rough side: zero unless
   `m = m'`.

Conclude:

```
‖canonicalRoughError P‖²_{L²(canonicalJointMeasure)}
  = Σ_{j ≥ 0, m ≥ 1} A(j,m)² · ‖M_{j,m}‖²_{L²}
```

Lemma: `canonicalRoughError_L2_sq_eq_sum`.

### S4. Bound `‖M_{j,m}‖²_{L²}` per `(j, m)` — uniform-m treatment

By two applications of `gff_wickPower_two_site_inner` and
`joint_wick_factorization` (or the explicit factorization of
`canonicalJointMeasure` as a product):

```
‖M_{j,m}‖²_{L²} = a^{2d} · Σ_{x,y}
  (j! · C_S(x,y)^j) · (m! · C_R(x,y)^m)
```

**Do not case-split on m.** For all `m ≥ 1`, factor out
`canonicalSmoothCovariance_uniform_bound` (giving
`‖C_S‖_∞^j ≤ Const · (1+|log T|)^j`), then sum the rough-side L^m using
`canonicalRoughCovariance_Lm_bound` (giving `≤ C_m · T`). Combined with
the volume sum (`a^d · Σ_x 1 = L^d`):

```
‖M_{j,m}‖²_{L²} ≤ j! · m! · L^d · Const^j · C_m · (1 + |log T|)^j · T
```

Each `‖M_{j,m}‖²_{L²}` is `O(T · (1+|log T|)^j)` with constant uniform
in `(a, N)`. Lemma: `M_jm_L2_sq_bound`.

### S5. Sum over `(j, m)`, absorb into K

The `(j, m)` sum is finite (`(j, m)` with `j + m ≤ P.n`, `m ≥ 1`); each
term has at most `(1+|log T|)^{P.n − 1}` polylog factor; constants
depend only on `P`, `mass`, `L`. Conclude:

```
‖E_R‖²_{L²} ≤ K(P, mass, L) · T · (1 + |Real.log T|) ^ (P.n − 1)
```

Existential closes `rough_error_variance`.

## Specialization fallback

If S4's uniform-m bookkeeping gets unwieldy, specialize the *proof
body* (not the theorem statement) to pure quartic by case-splitting on
`P.coeff k = 0 for k ≠ 4`. Keep the theorem signature general; leave a
`sorry` on non-quartic monomials with a TODO comment. The bridge axiom
signature stays correct.

## Out of scope (Phase 2)

Do not implement in this PR:

- `rough_error_Lp_bound` — comes from feeding `rough_error_variance`
  into `polynomial_chaos_concentration`
  (`gaussian-hilbert/PolynomialChaosConcentration.lean:469`). Janson
  5.10 takes the L² bound as input and produces L^p plus
  stretched-exponential tail.
- Explicit chaos-projection identification of
  `E_R ∈ ⊕_{k=1}^{P.n} 𝓗_k` — Janson 5.10 needs only the L² bound and
  the maximum chaos degree (= `P.n`), not the projection.
- The bridge axiom discharge itself — that's a downstream consumer.
- Discharging the three upstream sorries
  (`canonicalSmoothCovariance_uniform_bound`,
  `canonicalRoughCovariance_Lm_bound`, `joint_wick_factorization`).
  These are parallel-tracked work; each sorry's discharge is a
  textbook exercise (Glimm–Jaffe Thm 8.5.2 and Mathlib measure-theory
  product factorization respectively).

## Acceptance criteria

- `lake build` clean from scratch on the
  `session/2026-05-09-pin-and-discharge-update` branch.
- `#print axioms rough_error_variance` shows only `propext`,
  `Classical.choice`, `Quot.sound` plus the three named upstream
  sorries (or whatever they become after upstream discharge) plus
  whatever `gff_wickPower_two_site_inner` introduces.
- No new pphi2 axioms beyond the three named upstream sorries.
- Theorem signature matches the statement in this doc (general `P`,
  `K` bound outside `(a, N)`, RHS = `K · T · (1+|log T|)^{P.n − 1}`).
- The `True` stub at `RoughErrorBound.lean:62` is replaced.

## Codex hand-off note

When you hit each of the three upstream prerequisites in S3/S4, **flag
the exact signature you need** against the actual
`canonicalSmoothCovariance` / `canonicalRoughCovariance` /
`canonicalJointMeasure` API in this codebase. Do not invent the
prerequisite signatures from the sketches above — they are
illustrative only. We will then file the upstream sorries with the
right names and types.
