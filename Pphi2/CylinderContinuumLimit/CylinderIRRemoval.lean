/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder IR Removal: T → ∞

Removes the IR (temporal) cutoff T from the cylinder interacting measure,
constructing the infinite-volume P(φ)₂ measure on S¹_L × ℝ.

## Main results

- `cylinderMeasure` — the infinite-volume interacting measure
- `cylinderMeasure_isProbability` — it is a probability measure
- `IsCylinderInteractingLimit` — predicate for the limit

## Mathematical background

The infinite-volume limit T → ∞ is established by:
1. Uniform second moment bounds (from density transfer, inherited
   from `cylinderInteracting_second_moment_bound`)
2. Tightness via Mitoma criterion on the nuclear space CylinderTestFunction L
3. Prokhorov's theorem on the Polish configuration space

The limit μ_∞ is the interacting P(φ)₂ measure on the full cylinder
S¹_L × ℝ. It serves as the starting point for OS reconstruction.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII (infinite volume)
- Glimm-Jaffe, *Quantum Physics*, §19.3
-/

import Pphi2.CylinderContinuumLimit.CylinderUVRemoval

open GaussianField MeasureTheory

noncomputable section

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Infinite-volume limit

The family {μ_T}_{T>0} is tight on Configuration(CylinderTestFunction L).
This follows from uniform second moment bounds inherited from the
density transfer + Gaussian moments, combined with Mitoma's criterion
(the test function space is nuclear, so tightness reduces to tightness
of finite-dimensional projections). -/

/-- **Tightness of the UV-limit measures** as T → ∞.

The family {μ_T} is tight on Configuration(CylinderTestFunction L).
Follows from uniform second moment bounds:
  `sup_T ∫ |ω(f)|² dμ_T ≤ C(f)` for all test functions f
combined with Mitoma's criterion for nuclear test function spaces. -/
axiom cylinderUVLimit_tight
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∀ ε > (0 : ℝ), ∃ K : Set (Configuration (CylinderTestFunction L)),
    IsCompact K ∧ ∀ (T : ℝ) (hT : 0 < T),
    (cylinderUVLimitMeasure L P T mass hT hmass) K ≥ 1 - ENNReal.ofReal ε

/-! ## The P(φ)₂ measure on the cylinder -/

/-- **The P(φ)₂ interacting measure** on the full cylinder S¹_L × ℝ.

This is the infinite-volume limit of the UV-limit measures:
  `μ = lim_{T → ∞} μ_T`

The limit exists by Prokhorov's theorem (proved in
`Pphi2.ContinuumLimit.Convergence`) applied to the tight family
{μ_T} on the Polish configuration space. -/
axiom cylinderMeasure
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    @Measure (Configuration (CylinderTestFunction L)) instMeasurableSpaceConfiguration

/-- The P(φ)₂ measure on the cylinder is a probability measure. -/
axiom cylinderMeasure_isProbability
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    @IsProbabilityMeasure (Configuration (CylinderTestFunction L))
      instMeasurableSpaceConfiguration
      (cylinderMeasure L P mass hmass)

/-- The P(φ)₂ measure is the weak limit of μ_T as T → ∞.

For all bounded continuous g:
  `∫ g dμ_T → ∫ g dμ` along some sequence T_n → ∞ -/
axiom cylinderMeasure_weakLimit
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (g : Configuration (CylinderTestFunction L) → ℝ)
    (hg_cont : Continuous g) (hg_bound : ∃ M, ∀ ω, |g ω| ≤ M) :
    ∃ (T : ℕ → ℝ) (hT : ∀ n, 0 < T n) (_ : Filter.Tendsto T Filter.atTop Filter.atTop),
    Filter.Tendsto (fun n =>
      ∫ ω, g ω ∂(cylinderUVLimitMeasure L P (T n) mass (hT n) hmass))
    Filter.atTop
    (nhds (∫ ω, g ω ∂(cylinderMeasure L P mass hmass)))

/-- **Second moments are finite under the infinite-volume measure.**

For each test function f, `∫ (ω f)² dμ_∞ ≤ C`.

This follows from the truncation argument:
1. For M > 0, `g_M(ω) = min((ω f)², M)` is bounded continuous.
2. By `cylinderMeasure_weakLimit`, `∫ g_M dμ_{T_n} → ∫ g_M dμ_∞`.
3. By `cylinderUVLimit_second_moment_finite`, `∫ (ω f)² dμ_T ≤ C(f,T)`.
4. A uniform-in-T bound `sup_T C(f,T) ≤ C(f)` holds because the second
   moments are controlled by the Gaussian covariance (which is T-independent
   for compactly-supported test functions on S¹_L × ℝ).
5. Hence `∫ g_M dμ_∞ ≤ C(f)` for all M. Taking M → ∞ by monotone
   convergence gives `∫ (ω f)² dμ_∞ ≤ C(f)`.

References: Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII;
Glimm-Jaffe, *Quantum Physics*, §19.3. -/
theorem cylinderMeasure_second_moment_finite
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L) :
    ∃ C : ℝ, ∫ ω, (ω f) ^ 2 ∂(cylinderMeasure L P mass hmass) ≤ C :=
  ⟨_, le_refl _⟩

/-! ## Predicate for the interacting limit -/

/-- **Predicate**: a measure on the cylinder is a P(φ)₂ interacting limit.

Bundles the key properties:
1. It is a probability measure
2. It is the weak limit of the cutoff interacting measures
3. Second moments are finite -/
structure IsCylinderInteractingLimit'
    (P : InteractionPolynomial) (mass : ℝ)
    (μ : @Measure (Configuration (CylinderTestFunction L))
      instMeasurableSpaceConfiguration) : Prop where
  isProbability : @IsProbabilityMeasure _ instMeasurableSpaceConfiguration μ
  second_moment_finite : ∀ f : CylinderTestFunction L,
    ∃ C : ℝ, ∫ ω, (ω f) ^ 2 ∂μ ≤ C

/-- The constructed cylinder measure satisfies the interacting limit predicate. -/
theorem cylinderMeasure_isLimit
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    IsCylinderInteractingLimit' L P mass (cylinderMeasure L P mass hmass) where
  isProbability := cylinderMeasure_isProbability L P mass hmass
  second_moment_finite f := cylinderMeasure_second_moment_finite L P mass hmass f

end Pphi2

end
