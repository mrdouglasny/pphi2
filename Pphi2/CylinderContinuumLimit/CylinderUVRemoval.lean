/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder UV Removal: Λ → ∞

Removes the UV cutoff Λ from the cylinder interacting measure,
constructing the UV limit measure μ_T for each fixed temporal extent T.

## Main results

- `cylinderUVLimitMeasure` — the limit measure as Λ → ∞
- `cylinderUVLimitMeasure_isProbability` — it is a probability measure
- `cylinderUVLimit_weakLimit` — it is the weak limit of μ_{Λ,T}

## Mathematical background

The UV limit exists because Wick ordering removes the logarithmic
divergence of the bare interaction. Concretely:

1. V_{Λ,T} converges in L²(μ_free) as Λ → ∞ because the Wick-ordered
   integrand :P(φ_Λ):_{c_Λ} has controlled differences: the variance
   of V_{Λ',T} - V_{Λ,T} involves only spatial modes |k| ∈ (Λ, Λ'],
   which are independent under μ_free and whose Wick-ordered contribution
   vanishes by the renormalization cancellation.

2. L² convergence of V implies L¹ convergence of exp(-V) (by dominated
   convergence + uniform lower bound), hence weak convergence of measures.

This is the cylinder analogue of the lattice continuum limit (a → 0),
but simpler: the UV cutoff Λ is a Fourier mode truncation, not a
lattice spacing, so no embedding map is needed.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII (UV cutoff removal)
- Glimm-Jaffe, *Quantum Physics*, §19.2
-/

import Pphi2.CylinderContinuumLimit.CylinderHypercontractivity

open GaussianField MeasureTheory

noncomputable section

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## UV limit measure

The UV limit measure μ_T is the weak limit of the cutoff measures μ_{Λ,T}
as Λ → ∞. Its existence follows from:
- Uniform second moment bounds (from `cylinderInteracting_second_moment_bound`)
- Tightness via Mitoma criterion (nuclear test function space)
- Prokhorov's theorem on the Polish configuration space -/

/-- **UV limit measure** on the cylinder for fixed temporal extent T.

This is the P(φ)₂ interacting measure with UV cutoff removed:
  `μ_T = lim_{Λ→ ∞} (1/Z_{Λ,T}) exp(-V_{Λ,T}) dμ_free`

The limit exists because:
1. Uniform moment bounds (from hypercontractivity + density transfer)
   give tightness of {μ_{Λ,T}}_Λ
2. Prokhorov on the Polish configuration space extracts a convergent
   subsequence
3. The limit is independent of subsequence (by L² convergence of V_{Λ,T}) -/
axiom cylinderUVLimitMeasure
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    @Measure (Configuration (CylinderTestFunction L)) instMeasurableSpaceConfiguration

/-- The UV limit measure is a probability measure. -/
axiom cylinderUVLimitMeasure_isProbability
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    @IsProbabilityMeasure (Configuration (CylinderTestFunction L))
      instMeasurableSpaceConfiguration
      (cylinderUVLimitMeasure L P T mass hT hmass)

/-- The UV limit measure is the weak limit of the cutoff measures.

For all bounded continuous functions g on Configuration(CylinderTestFunction L):
  `∫ g dμ_{Λ,T} → ∫ g dμ_T` as Λ → ∞ -/
axiom cylinderUVLimit_weakLimit
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (g : Configuration (CylinderTestFunction L) → ℝ)
    (hg_cont : Continuous g) (hg_bound : ∃ M, ∀ ω, |g ω| ≤ M) :
    Filter.Tendsto (fun Λ =>
      ∫ ω, g ω ∂(cylinderInteractingMeasure L P Λ T mass hT hmass))
    Filter.atTop
    (nhds (∫ ω, g ω ∂(cylinderUVLimitMeasure L P T mass hT hmass)))

/-! ## Properties of the UV limit -/

/-- The UV limit measure is absolutely continuous w.r.t. the free measure.

Each μ_{Λ,T} has density exp(-V_{Λ,T})/Z_{Λ,T} w.r.t. μ_free.
The UV limit inherits absolute continuity. -/
theorem cylinderUVLimitMeasure_absolutelyContinuous
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    cylinderUVLimitMeasure L P T mass hT hmass ≪
    cylinderFreeMeasure L mass hmass := by
  sorry

/-- Second moments are finite under the UV limit measure. -/
theorem cylinderUVLimit_second_moment_finite
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f : CylinderTestFunction L) :
    ∃ C : ℝ, ∫ ω, (ω f) ^ 2
      ∂(cylinderUVLimitMeasure L P T mass hT hmass) ≤ C := by
  sorry

/-- The UV limit Schwinger two-point function is the limit of the
cutoff Schwinger functions. -/
theorem cylinderUVLimit_schwinger2
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    Filter.Tendsto (fun Λ =>
      cylinderSchwinger2 L P Λ T mass hT hmass f g)
    Filter.atTop
    (nhds (∫ ω, ω f * ω g
      ∂(cylinderUVLimitMeasure L P T mass hT hmass))) := by
  sorry

end Pphi2

end
