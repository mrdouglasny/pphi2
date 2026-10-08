/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Second moments of the continuum-embedded interacting measures

## Main results

- `continuumMeasure_sq_integrable` — `(ω f)²` is integrable under each `ν_a`

## Removed (2026-10-08, issue #63)

`continuum_second_moment_uniform` and `continuumMeasures_tight` claimed a second-moment
bound, hence tightness, for `{ν_a}_{a ∈ (0,1]}` at **fixed lattice size `N`**. Their proofs
rested on `nelson_exponential_estimate_master_bounded`, which is false: at fixed `N` the
physical volume `(N a)^d` shrinks to zero and `∫ e^{-2V_a} dμ_GFF → ∞`. Both were deleted
with the axiom. The supported continuum limits fix the physical volume instead: see
`TorusContinuumLimit/` and `AsymTorus/`.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, §V.1
- Glimm-Jaffe, *Quantum Physics*, §19.4
-/

import Pphi2.ContinuumLimit.Hypercontractivity
import Pphi2.GaussianContinuumLimit.GaussianTightness

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! ## Integrability of `(ω f)²` under the interacting continuum measure -/

/-- Integrability of the squared evaluation functional under the interacting
continuum measure.

Mirrors `gaussianContinuumMeasure_sq_integrable`: push through
`integrable_map_measure`, rewrite `(ι ω) f = ω g_f` where
`g_f = latticeTestField`, and reduce to lattice integrability. The
interacting case dominates `bw ω ≤ exp(B)` to transfer from the Gaussian
L²-integrability (`pairing_product_integrable`). -/
theorem continuumMeasure_sq_integrable
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : ContinuumTestFunction d) :
    Integrable (fun ω : Configuration (ContinuumTestFunction d) =>
      (ω f) ^ 2) (continuumMeasure d N P a mass ha hmass) := by
  -- Push through Measure.map to reduce to lattice integrability.
  unfold continuumMeasure
  apply (integrable_map_measure
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
    (latticeEmbedLift_measurable d N a ha).aemeasurable).mpr
  -- Rewrite using `latticeEmbedLift_eval_eq`: `(ι ω) f = ω g_f`
  set g_f := latticeTestField d N a f
  have h_eval : ∀ ω : Configuration (FinLatticeField d N),
      (latticeEmbedLift d N a ha ω) f = ω g_f :=
    fun ω => latticeEmbedLift_eval_eq d N a ha f ω
  have h_congr :
      ((fun ω : Configuration (ContinuumTestFunction d) => (ω f) ^ 2) ∘
        latticeEmbedLift d N a ha) =
      fun ω : Configuration (FinLatticeField d N) => (ω g_f) * (ω g_f) := by
    ext ω
    simp only [Function.comp, h_eval, sq]
  rw [h_congr]
  -- Goal: Integrable (fun ω => (ω g_f) * (ω g_f)) (interactingLatticeMeasure ...)
  -- Now follow the `field_second_moment_finite` pattern for general g_f.
  obtain ⟨B, hB⟩ := interactionFunctional_bounded_below d N P a mass ha hmass
  have hZ := partitionFunction_pos d N P a mass ha hmass
  set μ_GFF := latticeGaussianMeasure d N a mass ha hmass
  set bw := boltzmannWeight d N P a mass
  -- Step 1: reduce via `interactingLatticeMeasure` definition
  suffices h : Integrable (fun ω : Configuration (FinLatticeField d N) =>
      (ω g_f) * (ω g_f))
      (μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) by
    unfold interactingLatticeMeasure
    exact h.smul_measure (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ).ne'))
  -- Step 2: withDensity → multiplicative weight under μ_GFF
  have hf_meas : Measurable (fun ω : Configuration (FinLatticeField d N) =>
      ENNReal.ofReal (bw ω)) :=
    ENNReal.measurable_ofReal.comp
      ((interactionFunctional_measurable d N P a mass).neg.exp)
  apply (integrable_withDensity_iff hf_meas
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  have hbw_simp : ∀ ω : Configuration (FinLatticeField d N),
      (ENNReal.ofReal (bw ω)).toReal = bw ω :=
    fun ω => ENNReal.toReal_ofReal (le_of_lt (boltzmannWeight_pos d N P a mass ω))
  simp_rw [hbw_simp]
  -- Goal: Integrable (fun ω => (ω g_f)*(ω g_f) * bw ω) μ_GFF
  -- Step 3: L² integrability of (ω g_f)*(ω g_f) under μ_GFF via pairing_product_integrable
  have h_sq_int : Integrable (fun ω : Configuration (FinLatticeField d N) =>
      (ω g_f) * (ω g_f)) μ_GFF := by
    have : μ_GFF = GaussianField.measure (latticeCovarianceGJ d N a mass ha hmass) := rfl
    rw [this]
    exact pairing_product_integrable
      (latticeCovarianceGJ d N a mass ha hmass) g_f g_f
  -- Step 4: dominate (ω g_f)*(ω g_f) * bw ω by (ω g_f)*(ω g_f) * exp(B)
  apply (h_sq_int.mul_const (Real.exp B)).mono
  · exact
      (((configuration_eval_measurable g_f).mul
        (configuration_eval_measurable g_f)).aestronglyMeasurable).mul
        ((interactionFunctional_measurable d N P a mass).neg.exp.aestronglyMeasurable)
  · exact Filter.Eventually.of_forall fun ω => by
      simp only [Real.norm_eq_abs]
      have h1 : 0 ≤ (ω g_f) * (ω g_f) := mul_self_nonneg _
      have h2 : 0 < bw ω := boltzmannWeight_pos d N P a mass ω
      have h3 : bw ω ≤ Real.exp B := by
        change Real.exp (-interactionFunctional d N P a mass ω) ≤ Real.exp B
        exact Real.exp_le_exp_of_le (by linarith [hB ω])
      rw [abs_of_nonneg (mul_nonneg h1 (le_of_lt h2)),
          abs_of_nonneg (mul_nonneg h1 (le_of_lt (Real.exp_pos B)))]
      exact mul_le_mul_of_nonneg_left h3 h1

end Pphi2

end
