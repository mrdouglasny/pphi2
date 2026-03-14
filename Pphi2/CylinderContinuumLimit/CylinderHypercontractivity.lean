/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder Hypercontractivity and Density Transfer

Establishes L^p control on the cylinder interaction and the Cauchy-Schwarz
density transfer bound from the interacting measure to the free measure.

## Main results

- `cylinderFieldEval_wickMonomial_integral` — Hermite orthogonality (axiom)
- `cylinderBoltzmannWeight_sq_integrable` — uniform L² bound on exp(-V) (axiom)
- `cylinderV_mean_nonpos` — ∫ V_{Λ,T} dμ_free ≤ 0
- `cylinderPartitionFunction_ge_one` — Z_{Λ,T} ≥ 1 by Jensen
- `cylinderDensityTransfer` — Cauchy-Schwarz density transfer

## Mathematical background

The key input is Nelson's hypercontractive estimate, proved in
`GaussianField.Hypercontractive` as the Gross log-Sobolev inequality.
Applied to the cylinder Fourier mode decomposition, it gives uniform
L^p bounds on Wick-ordered polynomials of the regularized field.

The density transfer (Cauchy-Schwarz) converts integrals against the
interacting measure to integrals against the free Gaussian measure:

  `∫ F dμ_V ≤ √K · (∫ F² dμ_free)^{1/2}`

where K = sup_Λ ∫ exp(-2V) dμ_free is the exponential moment bound.

## References

- Nelson, *Construction of quantum fields from Markoff fields* (1973)
- Gross, "Logarithmic Sobolev inequalities" (1975)
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. V, VIII
-/

import Pphi2.CylinderContinuumLimit.CylinderInteraction

open GaussianField MeasureTheory

noncomputable section

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Axioms from hypercontractivity

These two axioms encode the analytical content of Nelson's hypercontractive
estimate applied to the cylinder field. They are consequences of the
Gross log-Sobolev inequality (`gross_log_sobolev` in gaussian-field)
applied to the Fourier mode decomposition of φ_Λ on S¹_L × ℝ. -/

/-- **Hermite orthogonality**: Wick monomials of degree ≥ 1 have zero
expectation under the free Gaussian measure.

Since `cylinderRegularizedFieldEval L Λ mass hmass θ t` is Gaussian
under the free measure with variance `cylinderWickConstant L mass Λ`,
and `wickMonomial n c` is the nth probabilist's Hermite polynomial
scaled to variance c, the integral vanishes by orthogonality.

This is the cylinder analogue of `wickMonomial_latticeGaussian`. -/
axiom cylinderFieldEval_wickMonomial_integral
    (n : ℕ) (hn : 1 ≤ n) (Λ : ℕ) (mass : ℝ) (hmass : 0 < mass) (θ t : ℝ) :
    Integrable (fun ω => wickMonomial n (cylinderWickConstant L mass Λ)
        (cylinderRegularizedFieldEval L Λ mass hmass θ t ω))
      (cylinderFreeMeasure L mass hmass) ∧
    ∫ ω, wickMonomial n (cylinderWickConstant L mass Λ)
        (cylinderRegularizedFieldEval L Λ mass hmass θ t ω)
      ∂(cylinderFreeMeasure L mass hmass) = 0

/-- **Exponential moment bound**: `∫ exp(-2V_{Λ,T}) dμ_free ≤ K` uniformly in Λ.

This is the key estimate combining:
1. Nelson's hypercontractive bound: ‖V_{Λ,T}‖_{Lp(μ_free)} ≤ C·p^{n/2}
2. Exponential moment from moment growth: Σ (2^k/k!) ‖V‖_{Lk}^k < ∞
3. Uniformity in Λ from Wick ordering (cancels UV divergence)

The bound K depends on P, L, T, mass but NOT on the UV cutoff Λ.
This is the cylinder analogue of `exponential_moment_bound`. -/
axiom cylinderBoltzmannWeight_sq_integrable
    (P : InteractionPolynomial) (T mass : ℝ) (hT : 0 < T) (hmass : 0 < mass) :
    ∃ K : ℝ, 0 < K ∧ ∀ Λ : ℕ,
    ∫ ω, (interactingBoltzmannWeight (cylinderV L P Λ T mass hT hmass) ω) ^ 2
      ∂(cylinderFreeMeasure L mass hmass) ≤ K

/-! ## Partition function lower bound

From Hermite orthogonality of Wick monomials, the interaction has
nonpositive mean: ∫ V dμ_free ≤ 0. Jensen's inequality then gives
Z = ∫ exp(-V) dμ_free ≥ exp(-∫V dμ_free) ≥ 1. -/

/-- The partition function satisfies Z_{Λ,T} ≥ 1.

**Proof sketch**: By Hermite orthogonality, ∫ :P(φ_Λ(θ,t)): dμ_free = P.coeff[0] ≤ 0
for each (θ,t), so ∫ V dμ_free ≤ 0. Jensen's inequality for the convex
function exp gives Z = ∫ exp(-V) dμ ≥ exp(-∫V dμ) ≥ exp(0) = 1. -/
theorem cylinderPartitionFunction_ge_one
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass) :
    1 ≤ interactingPartitionFunction (cylinderV L P Λ T mass hT hmass)
      (cylinderFreeMeasure L mass hmass) := by
  sorry

/-! ## Density transfer

The Cauchy-Schwarz density transfer converts integrals against the
interacting measure μ_V to integrals against the free measure μ_free.

For nonneg F with F² integrable under μ_free:
  `∫ F dμ_V = (1/Z) ∫ F·exp(-V) dμ_free`
            `≤ (1/Z) · (∫ F²)^{1/2} · (∫ exp(-2V))^{1/2}`  (Cauchy-Schwarz)
            `≤ K^{1/2} · (∫ F² dμ_free)^{1/2}`             (since Z ≥ 1) -/

/-- **Cauchy-Schwarz density transfer**: bounds interacting expectations
by free Gaussian expectations.

  `∫ F dμ_V ≤ √K · (∫ F² dμ_free)^{1/2}`

This is the cylinder analogue of `density_transfer_bound` from the lattice. -/
theorem cylinderDensityTransfer
    (P : InteractionPolynomial) (Λ : ℕ) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (K : ℝ) (hK : 0 < K)
    (hK_bound : ∫ ω, (interactingBoltzmannWeight
        (cylinderV L P Λ T mass hT hmass) ω) ^ 2
      ∂(cylinderFreeMeasure L mass hmass) ≤ K)
    (F : Configuration (CylinderTestFunction L) → ℝ)
    (hF_nn : ∀ ω, 0 ≤ F ω)
    (hF_sq_int : Integrable (fun ω => F ω ^ 2)
      (cylinderFreeMeasure L mass hmass)) :
    ∫ ω, F ω ∂(cylinderInteractingMeasure L P Λ T mass hT hmass) ≤
    K ^ (1/2 : ℝ) * (∫ ω, F ω ^ 2
      ∂(cylinderFreeMeasure L mass hmass)) ^ (1/2 : ℝ) := by
  sorry

/-- **Uniform moment bound**: second moments under the interacting measure
are bounded uniformly in the UV cutoff Λ.

  `sup_Λ ∫ |ω(f)|² dμ_{Λ,T} ≤ C(f)`

Follows from density transfer + Gaussian second moments. -/
theorem cylinderInteracting_second_moment_bound
    (P : InteractionPolynomial) (T mass : ℝ)
    (hT : 0 < T) (hmass : 0 < mass)
    (f : CylinderTestFunction L) :
    ∃ C : ℝ, ∀ Λ : ℕ,
    ∫ ω, (ω f) ^ 2 ∂(cylinderInteractingMeasure L P Λ T mass hT hmass) ≤ C := by
  sorry

end Pphi2

end
