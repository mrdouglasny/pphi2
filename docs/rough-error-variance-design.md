# Design doc: `rough_error_variance` (Step 1 of bridge axiom discharge)

*Drafted 2026-05-10. Concrete plan for the first sub-step of
`polynomial_chaos_exp_moment_bridge` discharge: replacing the
`True`-stub `rough_error_variance` in
`Pphi2/NelsonEstimate/RoughErrorBound.lean:62` with a real bound
`‖E_R‖²_{L²(joint)} ≤ K · T^δ`. Companion to
[`polynomial-chaos-exp-moment-bridge-proof-plan.md`](polynomial-chaos-exp-moment-bridge-proof-plan.md).
Estimated effort: ~200-400 lines, ~1 week of focused Lean work.*

## Goal

Replace the placeholder

```lean
theorem rough_error_variance :
    ∃ (C : ℝ), 0 < C ∧ True := ⟨1, one_pos, trivial⟩
```

with a real `L²` bound on the rough error `E_R = V_a(φ_S + φ_R) - V_S(φ_S)`,
of the shape `‖E_R‖²_{L²(joint Gaussian)} ≤ K(P, c_S) · T^δ` where
`δ > 0` depends only on `deg P` and `d`, and `K` depends polynomially
on the smooth Wick constant `c_S` (which itself is `O(1 + |log T|)` for
`d = 2` by `smoothVariance_le_log`). The key fact is **uniformity in
N** — `K` does not depend on the lattice size.

This bound is the input to step 2 of the proof plan
(`rough_error_tail_bound` via `polynomial_chaos_concentration`) and
ultimately to the dynamical-cutoff integration that closes the bridge
axiom.

## Available infrastructure (verified by audit 2026-05-10)

### From `Pphi2/NelsonEstimate/`

**This morning's variance machinery in `FieldDecomposition.lean`:**
- `CanonicalJoint d N : Type := ((Fin d → Fin N) → ℝ) × ((Fin d → Fin N) → ℝ)` — the joint configuration type.
- `canonicalJointMeasure d N : Measure (CanonicalJoint d N)` — `Measure.prod` of two `stdGaussianFin` factors.
- `canonicalSmoothFieldFunction d N (η : CanonicalJoint d N) (x : FinLatticeSites d N) : ℝ` — the smooth field at site `x` from the joint variables (η_S component re-spectralized).
- `canonicalRoughFieldFunction d N (η : CanonicalJoint d N) (x : FinLatticeSites d N) : ℝ` — the rough field at site `x`.
- `canonicalSumFieldFunction = canonicalSmoothFieldFunction + canonicalRoughFieldFunction` (proved at line 102).
- `canonicalSumFieldFunction_covariance` (line 663): proved spectral form
  `∫ φ(η)(x) · φ(η)(y) ∂μ_joint = (a^d)⁻¹ Σ_k λ_k⁻¹ e_k(x) e_k(y)`.
- `canonicalSmoothRough_cross_moment_zero` (line 413): proved cross-moment vanishing.
- `pi_gaussian_bilinear_moment` (line 288): the Plancherel/Parseval helper for i.i.d. N(0,1).

**Covariance split machinery in `CovarianceSplit.lean`:**
- `smoothCovEigenvalue d N a mass T m`, `roughCovEigenvalue d N a mass T m` — per-mode split.
- `smoothWickConstant d N a mass T`, `roughWickConstant d N a mass T` — averaged Wick constants.
- `wickConstant_split T : c_a = c_S + c_R` (proved).
- `smoothVariance_le_log T : smoothWickConstant ≤ smoothVarianceConstant · (1 + |log T|)` (for `d = 2`, proved).
- `roughCovariance_sq_summable T (hT : 0 < T) : ∑_m roughCovEigenvalue² ≤ M · T^δ` (proved, line 203).

**Wick binomial in `WickBinomial.lean`:**
- `wickMonomial_add_binomial n c₁ c₂ x y : :( x + y )^n :_{c₁+c₂} = Σ_{k=0}^{n} C(n,k) :x^k:_{c₁} · :y^{n-k}:_{c₂}` (proved).
- `wickMonomial_four_add_binomial`, `wickMonomial_two_add` (explicit small-degree expansions).

**Interaction functional in `InteractingMeasure/LatticeMeasure.lean`:**
- `interactionFunctional P a mass : Configuration (FinLatticeField d N) → ℝ` defined as `a^d · Σ_x :P(ω(δ_x)):_{c_a}`.
- Note: this is on `Configuration (FinLatticeField d N)`, **not** on `CanonicalJoint`. Need a transfer.

### From `gaussian-field` (already proved, no axioms)

- `gffOrthonormalProj_pushforward_eq_stdGaussian` — pushforward identifies the lattice GFF with `Measure.pi (gaussianReal 0 1)` (so `latticeGaussianMeasure ↔ stdGaussianFin (N^d)` after re-spectralizing).
- `gffMultiWickMonomial_orthogonality` — multi-index Wick orthogonality on the GFF.
- `gffMultiWickMonomial_eq_hermite_product` — Wick monomials are products of Hermite functions in the orthogonalized coords.
- `siteWickMonomial_eigenbasis_expansion` — site Wick monomial as a finite Hermite combination.

### From `gaussian-hilbert` (already proved, modulo OU placeholders)

- `polynomial_chaos_concentration` — Janson Theorem 5.10 (the eventual consumer of `rough_error_variance` after step 2 of the plan).

## Type-design decisions

### D1. Express `E_R` on `CanonicalJoint`, not `Configuration × Configuration`

This morning's `FieldDecomposition.lean` works on `CanonicalJoint d N`
which is `((Fin d → Fin N) → ℝ) × ((Fin d → Fin N) → ℝ)` (two copies
of the lattice indexed by sites, viewed as raw real-valued tuples).
Build `E_R` directly on this type — avoids the `Configuration`
indirection and reuses the proved variance machinery.

### D2. Define V on the smooth field via the canonical functions

```lean
/-- `V_S(η) = a^d · Σ_x :P(canonicalSmoothFieldFunction η x):_{c_S}`. -/
noncomputable def latticeSmoothInteraction
    (d N : ℕ) [NeZero N] (P : InteractionPolynomial) (a mass T : ℝ)
    (η : CanonicalJoint d N) : ℝ :=
  a ^ d * ∑ x : FinLatticeSites d N,
    wickPolynomial P (smoothWickConstant d N a mass T)
      (canonicalSmoothFieldFunction d N a mass η x)

/-- `V(η) = a^d · Σ_x :P(canonicalSumFieldFunction η x):_{c_a}`. -/
noncomputable def latticeFullInteraction
    (d N : ℕ) [NeZero N] (P : InteractionPolynomial) (a mass : ℝ)
    (η : CanonicalJoint d N) : ℝ :=
  a ^ d * ∑ x : FinLatticeSites d N,
    wickPolynomial P (wickConstant d N a mass)
      (canonicalSumFieldFunction d N a mass η x)

/-- The rough error: `E_R = V - V_S`. -/
noncomputable def latticeRoughError
    (d N : ℕ) [NeZero N] (P : InteractionPolynomial) (a mass T : ℝ)
    (η : CanonicalJoint d N) : ℝ :=
  latticeFullInteraction d N P a mass η - latticeSmoothInteraction d N P a mass T η
```

### D3. The bound shape

```lean
theorem rough_error_variance
    (d N : ℕ) [NeZero N] (P : InteractionPolynomial) (a mass T : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hT : 0 < T) :
    ∃ (K : ℝ) (δ : ℝ), 0 < K ∧ 0 < δ ∧
      ∫ η, (latticeRoughError d N P a mass T η) ^ 2
        ∂(canonicalJointMeasure d N a mass) ≤ K * T ^ δ
```

Key features:
- The bound `K · T^δ` is the canonical shape from
  `roughCovariance_sq_summable`.
- `K` is allowed to depend on `(d, P, mass)` but **not** on `(a, N, T)`
  in a problematic way (technically may include `(1 + |log T|)`-style
  factors from the smooth Wick constant; the dynamical cutoff
  argument absorbs these).
- `δ` is a structural constant (depends only on `d` and `deg P`); for
  `d = 2`, `deg P = 4`, expect `δ = δ_rough · const(deg P)` where
  `δ_rough` is the exponent from `roughCovariance_sq_summable`.

### D4. Joint measure typeclass facts

`canonicalJointMeasure` is `Measure.prod` of two `stdGaussianFin`
factors. We need:
- `IsProbabilityMeasure (canonicalJointMeasure d N a mass)` (likely
  already an instance via `Measure.prod` of probability measures).
- Fubini for splitting the integral over the joint measure into the
  smooth-then-rough iterated integral when convenient.
- Independence of the smooth and rough field functions (the proved
  `canonicalSmoothRough_cross_moment_zero` is the L²-version of this).

## Proof structure

Five sub-steps for the L² bound on `latticeRoughError`. Each can be a
separate file or section; total ~250-400 lines.

### S1. Wick binomial expansion of the integrand (≈40-60 lines)

For each site `x`, expand the Wick polynomial using `wickMonomial_add_binomial`:
```
:P(φ_S(x) + φ_R(x)):_{c_S + c_R} = Σ_k coefficient_k · :φ_S(x)^a:_{c_S} · :φ_R(x)^b:_{c_R}
```
where the sum runs over multi-indices summing to `deg P`. The smooth-only
term (b = 0 across all monomials) gives back `V_S`; the rest is `E_R`.
This identifies `E_R` site-by-site as a finite linear combination of
mixed Wick monomials.

**Helper lemma** (in `RoughErrorBound.lean`):
```lean
private lemma latticeRoughError_eq_mixed_wick
    (d N : ℕ) [NeZero N] (P : InteractionPolynomial) (a mass T : ℝ)
    (η : CanonicalJoint d N) :
    latticeRoughError d N P a mass T η =
      a ^ d * ∑ x : FinLatticeSites d N,
        ∑ b ∈ Finset.range (P.degree + 1),
          (if b = 0 then 0 else
            mixedWickCoefficient P b
              (canonicalSmoothFieldFunction d N a mass η x)
              (canonicalRoughFieldFunction d N a mass η x)
              (smoothWickConstant d N a mass T) (roughWickConstant d N a mass T))
```
where `mixedWickCoefficient P b φ_S φ_R c_S c_R` packages the
combinatorial coefficient × `:φ_S^{deg P - b}:_{c_S} · :φ_R^b:_{c_R}`.

### S2. Square the integrand and apply Wick orthogonality (≈80-120 lines)

Expanding `(E_R)²` gives a double sum over sites and over Wick-monomial
indices. The integral against `canonicalJointMeasure` of `:φ_S^a₁(x):·:φ_R^b₁(x):·:φ_S^a₂(y):·:φ_R^b₂(y):`
factors via independence of the smooth and rough fields:
```
∫ ... = (∫ :φ_S^a₁(x): · :φ_S^a₂(y): ∂μ_S) · (∫ :φ_R^b₁(x): · :φ_R^b₂(y): ∂μ_R)
```
Each factor is a Wick-Hermite inner product. By Wick orthogonality
(via `gffMultiWickMonomial_orthogonality` from gaussian-field, or its
canonical-coordinate analogue from `FieldDecomposition.lean`), the
result is nonzero only when `(a₁, x) ≅ (a₂, y)` and similarly for `b`.

**Helper lemma**:
```lean
private lemma latticeRoughError_sq_integral_eq_diagonal_sum
    (d N : ℕ) [NeZero N] (P : InteractionPolynomial) (a mass T : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (hT : 0 < T) :
    ∫ η, (latticeRoughError d N P a mass T η) ^ 2
      ∂(canonicalJointMeasure d N a mass) =
    a ^ (2 * d) * ∑ x : FinLatticeSites d N,
      ∑ b ∈ Finset.range (P.degree + 1) \ {0},
        (mixedWickCoefficient P b ...)^2 *
          smoothFactorial b * roughFactorial b *
          (smoothWickConstant ...)^(deg P - b) *
          (roughCov_diagonal x)^b
```
The cross-terms (different `(a₁, b₁)` vs `(a₂, b₂)`) vanish; the
diagonal terms group sites where the result depends on the variance
factors.

### S3. Bound the diagonal sum via `roughCovariance_sq_summable` (≈50-80 lines)

Each diagonal term involves `(roughCov_diagonal x)^b ≤ C · (∑ roughCovEigenvalue²)`
for `b ≥ 1` (since `(roughCovEigenvalue)^b ≤ (roughCovEigenvalue)^2 · (max)^{b-2}`).
Summing over sites and `b` gives:
```
diagonal sum ≤ K(P, c_S, c_R) · ∑_m roughCovEigenvalue²
              ≤ K(P, c_S, c_R) · M · T^δ          (by roughCovariance_sq_summable)
```

**Key sub-lemmas**:
- `roughCov_diagonal_sq_le`: `(roughCovariance(x, x))² ≤ (∑_m roughCovEigenvalue²)`
  — true because `roughCovariance(x, x) = Σ_m roughCovEigenvalue · |e_m(x)|²`
  and `Σ |e_m(x)|² = 1` (orthonormality).
- `roughCov_diagonal_pow_le_sq`: for `b ≥ 2`, `roughCov_diagonal^b ≤
  (max roughCovEigenvalue)^{b-2} · roughCov_diagonal²`. The
  `(max roughCovEigenvalue)^{b-2}` factor is bounded by `T^{(b-2)·δ'}`
  for some δ' > 0 (via the `roughCovEigenvalue_le_T` bound).

### S4. Bound the smooth Wick constant powers (≈30-50 lines)

The factor `(smoothWickConstant)^{deg P - b}` is bounded by
`(smoothVarianceConstant · (1 + |log T|))^{deg P - b}` via
`smoothVariance_le_log`. This contributes a polylogarithmic factor in
T, which is absorbed into the `K`-constant for the dynamical cutoff
argument.

### S5. Assemble the final bound (≈30-50 lines)

Combine S1–S4 to get
```
∫ E_R² ∂μ ≤ a^{2d} · |Λ| · K(P, c_S(T)) · T^δ
          ≤ K'(P, mass) · L^d · (1 + |log T|)^{deg P} · T^δ
          ≤ K''(P, mass, L) · T^{δ/2}             (absorbing the log factor for sufficiently small T)
```
The volume factor `L^d = (a · N)^d` is absorbed by the constraint
`a · N ≤ L` (from the volume signature change in the bridge axiom).

## Outstanding questions / open design items

1. **Multi-index notation for the cross terms (S2).** `wickPolynomial P` is a
   `Polynomial` of arbitrary degree (per `Polynomial.lean`). The Wick
   binomial expansion at each site involves a sum over `b ∈ {0, ..., deg P}`
   for each monomial of `P`. Need to pick a convenient indexing — likely
   a sigma-type or a `Finset.product`. Resolution: see how `wickPolynomial`
   itself is structured (it's `P.eval (wickMonomial · c x)` modulo Wick-orderings;
   the binomial expansion is a `Finset.sum_pow` on the polynomial).

2. **Site-vs-multi-site Wick orthogonality.** The mixed product
   `:φ_R^b₁(x): · :φ_R^b₂(y):` has expectation
   `b₁! · C_R(x, y)^{b₁} · δ_{b₁, b₂}` (Isserlis). For the
   diagonal-x case (x = y), this is `b₁! · C_R(x, x)^{b₁}`. The
   off-diagonal case has the cross-covariance `C_R(x, y)`, which is
   in general non-trivial — but when summed against `(coefficient)²`
   the contribution is bounded by the L² norm of `C_R` (HS-like).
   Resolution: write a helper `roughCov_HS_norm := √(∑_{x,y} C_R(x,y)²)`
   and use Cauchy-Schwarz on the bilinear form.

3. **Whether to define `roughCov_diagonal` and `roughCov_HS_norm` here
   or in `CovarianceSplit.lean`.** Decision: in `CovarianceSplit.lean`
   alongside the existing `roughCovEigenvalue` machinery, since other
   downstream consumers will want them too.

## Sub-task breakdown

| # | Task | File | Lines | Days |
|---|---|---|---|---|
| 1 | Define `latticeRoughError` + `latticeFullInteraction` + `latticeSmoothInteraction` (D2/D3) | `RoughErrorBound.lean` | 50 | 1 |
| 2 | Helper sums: `roughCov_diagonal`, `roughCov_HS_norm`, with bound by `roughCovariance_sq_summable` | `CovarianceSplit.lean` (extend) | 80 | 2 |
| 3 | S1: site-by-site Wick binomial expansion of `latticeRoughError` (`latticeRoughError_eq_mixed_wick`) | `RoughErrorBound.lean` | 60 | 2 |
| 4 | S2: square + Wick orthogonality reduction (`latticeRoughError_sq_integral_eq_diagonal_sum`) | `RoughErrorBound.lean` | 100 | 3 |
| 5 | S3: bound the diagonal sum via S2 lemmas + `roughCovariance_sq_summable` | `RoughErrorBound.lean` | 70 | 2 |
| 6 | S4: smooth Wick constant powers via `smoothVariance_le_log` | `RoughErrorBound.lean` | 40 | 1 |
| 7 | S5: final assembly into `rough_error_variance` | `RoughErrorBound.lean` | 40 | 1 |
| 8 | Build + axiom check + commit | — | — | 1 |
| **Total** | | | **~440** | **~13 days** |

The 13-day estimate matches the 1-week-of-focused-work estimate from
the proof plan (+ buffer for type-class skirmishes).

## Mathlib helpers needed

None new; this proof uses only:
- `MeasureTheory.integral_mul_const`, `integral_const_mul`, `integral_finset_sum`
- `MeasureTheory.Measure.prod_*` and `MeasureTheory.integral_prod` for Fubini
- `IsProbabilityMeasure` instance for `Measure.prod` of probability measures
- `Finset.sum_pow`, `Finset.sum_mul_sum`, `Finset.prod_*`
- `Real.sq_nonneg`, `Real.exp_nonneg`, `pow_nonneg`

All standard Mathlib.

## Starter code (drop into `RoughErrorBound.lean` next session)

```lean
import Pphi2.NelsonEstimate.CovarianceSplit
import Pphi2.NelsonEstimate.WickBinomial
import Pphi2.NelsonEstimate.FieldDecomposition
import Pphi2.InteractingMeasure.LatticeMeasure

noncomputable section

namespace Pphi2

variable (d N : ℕ) [NeZero N] (a mass T : ℝ)

/-- The lattice smooth interaction `V_S` evaluated on a joint configuration. -/
noncomputable def latticeSmoothInteraction
    (P : InteractionPolynomial) :
    CanonicalJoint d N → ℝ := fun η =>
  a ^ d * ∑ x : FinLatticeSites d N,
    wickPolynomial P (smoothWickConstant d N a mass T)
      (canonicalSmoothFieldFunction d N a mass η x)

/-- The lattice full interaction `V` evaluated on a joint configuration. -/
noncomputable def latticeFullInteractionJoint
    (P : InteractionPolynomial) :
    CanonicalJoint d N → ℝ := fun η =>
  a ^ d * ∑ x : FinLatticeSites d N,
    wickPolynomial P (wickConstant d N a mass)
      (canonicalSumFieldFunction d N a mass η x)

/-- The lattice rough error `E_R = V - V_S`. -/
noncomputable def latticeRoughError
    (P : InteractionPolynomial) :
    CanonicalJoint d N → ℝ := fun η =>
  latticeFullInteractionJoint d N a mass P η -
    latticeSmoothInteraction d N a mass T P η

/-- **L² bound on the rough error.**

  `‖E_R‖²_{L²(joint)} ≤ K · T^δ`

with K depending on (P, mass, T-polylog) and δ > 0 from
`roughCovariance_sq_summable`. -/
theorem rough_error_variance
    (P : InteractionPolynomial)
    (ha : 0 < a) (hmass : 0 < mass) (hT : 0 < T) :
    ∃ (K δ : ℝ), 0 < K ∧ 0 < δ ∧
      ∫ η, (latticeRoughError d N a mass T P η) ^ 2
        ∂(canonicalJointMeasure d N a mass) ≤ K * T ^ δ := by
  sorry  -- Sub-tasks 3-7 in the design doc

end Pphi2
```

## References

- pphi2/docs/polynomial-chaos-exp-moment-bridge-proof-plan.md (parent plan)
- pphi2/docs/polynomial-chaos-concentration.md (Jaffe-vetted math writeup)
- Glimm-Jaffe Ch. 8 (the dynamical cutoff proof)
- Simon, *P(φ)₂ Euclidean QFT*, Ch. V Lemma V.11 (the rough-error tail bound)
- Janson, *Gaussian Hilbert Spaces*, Theorem 5.10 (the Bonami-Nelson bound consumer)
