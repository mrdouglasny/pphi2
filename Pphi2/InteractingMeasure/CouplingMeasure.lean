/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.U4AffineBound

/-!
# Coupling-`g` interacting lattice measure (Route A foundation)

The weak-coupling family `μ_g ∝ e^{−g·V} μ_GFF` at the lattice level, and the bridge
`connectedFourPoint μ_g f = u4(…,g)`. For `g = 1` this is `interactingLatticeMeasure`; the point of
the family is *small* `g`, where `lattice_u4_neg_uniform` gives `u₄(μ_g) ≤ −c < 0`. This is the
foundation of Route A (discharge φ⁴₂ non-Gaussianity at weak coupling) — see
`planning/route-A-weak-coupling-plan.md`.

## Main results
* `interactingLatticeMeasureCoupling` — `μ_g = Z(g)⁻¹ · (e^{−g·V} · μ_GFF)`.
* `interactingLatticeMeasureCoupling_isProbability` — `μ_g` is a probability measure (`g ≥ 0`).
* `integral_pow_interactingLatticeMeasureCoupling` — `∫ (ωf)ⁿ dμ_g = normalizedMoment(…,n,g)`.
* `connectedFourPoint_interactingLatticeMeasureCoupling_eq_u4` — `connectedFourPoint μ_g f = u4(g)`.
-/

namespace Pphi2

open MeasureTheory GaussianField

variable (d N : ℕ) [NeZero N]

/-- The coupling-`g` interacting lattice measure `μ_g = Z(g)⁻¹ · (e^{−g·V} · μ_GFF)`, with
`Z(g) = partitionFn(g) = ∫ e^{−g·V}`. For `g = 1` it agrees with `interactingLatticeMeasure`. -/
noncomputable def interactingLatticeMeasureCoupling (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (g : ℝ) :
    @Measure (Configuration (FinLatticeField d N)) instMeasurableSpaceConfiguration :=
  (ENNReal.ofReal (partitionFn d N a mass ha hmass P g))⁻¹ •
    (latticeGaussianMeasure d N a mass ha hmass).withDensity
      (fun ω => ENNReal.ofReal (Real.exp (-(g * interactionFunctional d N P a mass ω))))

/-- The coupling weight `e^{−g·V}` is integrable against the lattice GFF (for `g ≥ 0`):
`V ≥ -B` gives `e^{−g·V} ≤ e^{g·B}`. -/
theorem expNegCoupling_integrable (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) {g : ℝ} (hg : 0 ≤ g) :
    Integrable (fun ω => Real.exp (-(g * interactionFunctional d N P a mass ω)))
      (latticeGaussianMeasure d N a mass ha hmass) := by
  obtain ⟨B, hB_bound⟩ := interactionFunctional_bounded_below d N P a mass ha hmass
  haveI := latticeGaussianMeasure_isProbability d N a mass ha hmass
  apply Integrable.of_bound (C := Real.exp (g * B))
  · exact ((interactionFunctional_measurable d N P a mass).const_mul g).neg.exp.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp_of_le (by nlinarith [hB_bound ω, hg])

/-- `partitionFn(g) > 0` for `g ≥ 0` (it is `≥ 1` by `partitionFn_ge_one`). -/
theorem partitionFn_pos_of_nonneg (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) {g : ℝ} (hg : 0 ≤ g) :
    0 < partitionFn d N a mass ha hmass P g :=
  lt_of_lt_of_le one_pos (partitionFn_ge_one d N P a mass ha hmass hg)

/-- The coupling-`g` interacting lattice measure is a probability measure (`g ≥ 0`). -/
theorem interactingLatticeMeasureCoupling_isProbability (P : InteractionPolynomial)
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) {g : ℝ} (hg : 0 ≤ g) :
    IsProbabilityMeasure (interactingLatticeMeasureCoupling d N P a mass ha hmass g) := by
  constructor
  have hZ := partitionFn_pos_of_nonneg d N P a mass ha hmass hg
  have hZ_ne : ENNReal.ofReal (partitionFn d N a mass ha hmass P g) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hZ).ne'
  have hZ_ne_top : ENNReal.ofReal (partitionFn d N a mass ha hmass P g) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  unfold interactingLatticeMeasureCoupling
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (expNegCoupling_integrable d N P a mass ha hmass hg)
      (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le))]
  simp only [smul_eq_mul]
  exact ENNReal.inv_mul_cancel hZ_ne hZ_ne_top

/-- `∫ (ωf)ⁿ dμ_g = normalizedMoment(…,n,g) = M_n(g)/Z(g)` (`g ≥ 0`). -/
theorem integral_pow_interactingLatticeMeasureCoupling (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (n : ℕ) {g : ℝ} (hg : 0 ≤ g) :
    (∫ ω, (ω f) ^ n ∂(interactingLatticeMeasureCoupling d N P a mass ha hmass g))
      = normalizedMoment d N a mass ha hmass P f n g := by
  have hZ := partitionFn_pos_of_nonneg d N P a mass ha hmass hg
  have hw_meas : Measurable (fun ω =>
      Real.toNNReal (Real.exp (-(g * interactionFunctional d N P a mass ω)))) :=
    ((interactionFunctional_measurable d N P a mass).const_mul g).neg.exp.real_toNNReal
  have wd : ∫ ω, (ω f) ^ n ∂((latticeGaussianMeasure d N a mass ha hmass).withDensity
        (fun ω => ENNReal.ofReal (Real.exp (-(g * interactionFunctional d N P a mass ω)))))
      = ∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω)) * (ω f) ^ n
        ∂(latticeGaussianMeasure d N a mass ha hmass) := by
    change ∫ ω, (ω f) ^ n ∂((latticeGaussianMeasure d N a mass ha hmass).withDensity
      (fun ω => ↑(Real.toNNReal (Real.exp (-(g * interactionFunctional d N P a mass ω)))))) = _
    rw [integral_withDensity_eq_integral_smul hw_meas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [NNReal.smul_def, smul_eq_mul]
    rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
  unfold interactingLatticeMeasureCoupling normalizedMoment gibbsMoment
  rw [integral_smul_measure, wd,
    show ((ENNReal.ofReal (partitionFn d N a mass ha hmass P g))⁻¹).toReal
        = (partitionFn d N a mass ha hmass P g)⁻¹ from by
      rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le], smul_eq_mul, div_eq_inv_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  ring

/-- **Route-A bridge.** The connected four-point of the coupling-`g` interacting lattice measure is
`u₄` at coupling `g`: `connectedFourPoint μ_g f = u4(…,g)` (`g ≥ 0`). Generalizes
`connectedFourPoint_interactingLatticeMeasure_eq_u4_one` from `g = 1` to arbitrary `g ≥ 0`, so that
`lattice_u4_neg_uniform` (`u₄(g₀) ≤ −c` for small `g₀`) becomes a strict-negativity statement about
an actual measure. -/
theorem connectedFourPoint_interactingLatticeMeasureCoupling_eq_u4 (a mass : ℝ) (ha : 0 < a)
    (hmass : 0 < mass) (P : InteractionPolynomial) (f : FinLatticeField d N) {g : ℝ} (hg : 0 ≤ g) :
    connectedFourPoint (interactingLatticeMeasureCoupling d N P a mass ha hmass g) f
      = u4 d N a mass ha hmass P f g := by
  unfold connectedFourPoint u4
  rw [integral_pow_interactingLatticeMeasureCoupling d N a mass ha hmass P f 4 hg,
    integral_pow_interactingLatticeMeasureCoupling d N a mass ha hmass P f 2 hg]

end Pphi2
