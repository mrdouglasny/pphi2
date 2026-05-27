/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Exponential moment bound for the constructed Gaussian measure

A Fernique-type companion to `pairing_memLp`/`second_moment_eq_covariance`: the evaluation
`ω ↦ ω g` of a centered Gaussian field is `N(0, σ²)` with `σ² = ⟪T g, T g⟫`, so its exponential
moment generating function is controlled,

  `∫ exp(t·|ω g|) d(measure T) ≤ 2·exp(t²/2 · ∫ (ω g)² d(measure T))`.

The bound is stated over the abstract `GaussianField` setup `(E, H, T)`, so it instantiates
verbatim at any lattice covariance (square `latticeCovarianceGJ` or heterogeneous
`latticeCovarianceAsymGJ`).

## Main result

* `GaussianField.gaussian_exp_abs_moment` — integrability of `exp(t·|ω g|)` together with the
  `2·exp(t²σ²/2)` bound on its integral.

## Reference

Glimm–Jaffe, *Quantum Physics*, §I.3 (Gaussian moment generating function); the bound
`E[e^{t|X|}] ≤ 2 e^{t²σ²/2}` for `X ∼ N(0,σ²)` is the union bound `e^{t|x|} ≤ e^{tx} + e^{-tx}`
combined with the Gaussian MGF.
-/

import GaussianField.Properties
import Mathlib.Probability.Distributions.Gaussian.Real

noncomputable section

namespace GaussianField

open MeasureTheory ProbabilityTheory TopologicalSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]

/-- **Gaussian exponential-modulus moment bound.** For the centered Gaussian field with
covariance operator `T`, the evaluation `ω ↦ ω g` is `N(0, σ²)` with `σ² = ⟪T g, T g⟫`, so
`exp(t·|ω g|)` is integrable and

  `∫ exp(t·|ω g|) d(measure T) ≤ 2·exp(t²/2 · ∫ (ω g)² d(measure T))`.

Proof: pushforward to `N(0, σ²)` (`pairing_is_gaussian`), bound `e^{t|x|} ≤ e^{tx} + e^{-tx}`
pointwise, and evaluate both halves by the Gaussian MGF `e^{σ²t²/2}`, matching `σ²` to the
second moment via `second_moment_eq_covariance`. -/
theorem gaussian_exp_abs_moment (T : E →L[ℝ] H) (g : E) (t : ℝ) :
    Integrable (fun ω : Configuration E => Real.exp (t * |ω g|)) (measure T) ∧
    ∫ ω : Configuration E, Real.exp (t * |ω g|) ∂(measure T) ≤
      2 * Real.exp (t ^ 2 / 2 * ∫ ω, (ω g) ^ 2 ∂(measure T)) := by
  set μ := measure T
  -- Step 1: Pushforward by evaluation is a 1D Gaussian N(0, v)
  have h_gauss : μ.map (fun ω : Configuration E => ω g) =
      gaussianReal 0 (@inner ℝ H _ (T g) (T g) : ℝ).toNNReal :=
    pairing_is_gaussian T g
  set v := (@inner ℝ H _ (T g) (T g) : ℝ).toNNReal with hv_def
  -- Step 2: Integrability of exp(t·x) and exp(-t·x) under N(0, v)
  have h_int_pos : Integrable (fun x : ℝ => Real.exp (t * x)) (gaussianReal 0 v) :=
    integrable_exp_mul_gaussianReal t
  have h_int_neg : Integrable (fun x : ℝ => Real.exp (-(t * x))) (gaussianReal 0 v) := by
    simp_rw [show ∀ x, -(t * x) = (-t) * x from fun x => by ring]
    exact integrable_exp_mul_gaussianReal (-t)
  -- Step 3: Pull back integrability to configuration space
  have h_eval_meas : Measurable (fun ω : Configuration E => ω g) :=
    configuration_eval_measurable g
  have h_int_pos_conf : Integrable (fun ω : Configuration E => Real.exp (t * ω g)) μ := by
    rw [← h_gauss] at h_int_pos
    rwa [integrable_map_measure h_int_pos.aestronglyMeasurable
      h_eval_meas.aemeasurable] at h_int_pos
  have h_int_neg_conf : Integrable (fun ω : Configuration E => Real.exp (-(t * ω g))) μ := by
    rw [← h_gauss] at h_int_neg
    rwa [integrable_map_measure h_int_neg.aestronglyMeasurable
      h_eval_meas.aemeasurable] at h_int_neg
  -- Step 4: Pointwise bound exp(t·|x|) ≤ exp(t·x) + exp(-t·x)
  have h_pointwise : ∀ x : ℝ, Real.exp (t * |x|) ≤
      Real.exp (t * x) + Real.exp (-(t * x)) := by
    intro x
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-(t * x))]
    · push Not at hx; rw [abs_of_neg hx, show t * (-x) = -(t * x) from by ring]
      linarith [Real.exp_pos (t * x)]
  -- Step 5: Integrability of exp(t·|ω g|)
  have h_int_sum : Integrable (fun ω : Configuration E =>
      Real.exp (t * ω g) + Real.exp (-(t * ω g))) μ :=
    h_int_pos_conf.add h_int_neg_conf
  have h_int_abs : Integrable (fun ω : Configuration E => Real.exp (t * |ω g|)) μ := by
    apply h_int_sum.mono ((h_eval_meas.abs.const_mul t).exp.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (t * |ω g|)
          ≤ Real.exp (t * ω g) + Real.exp (-(t * ω g)) := h_pointwise (ω g)
        _ ≤ |Real.exp (t * ω g) + Real.exp (-(t * ω g))| := le_abs_self _
  -- Step 6: MGF values for exp(t·x) and exp(-t·x)
  have h_mgf_pos : ∫ ω : Configuration E, Real.exp (t * ω g) ∂μ =
      Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    have h_eq : ∫ ω, Real.exp (t * ω g) ∂μ =
        ∫ x, Real.exp (t * x) ∂(μ.map (fun ω : Configuration E => ω g)) :=
      (integral_map h_eval_meas.aemeasurable
        ((measurable_const.mul measurable_id).exp.aestronglyMeasurable)).symm
    rw [h_eq, h_gauss]
    have := congr_fun (@mgf_id_gaussianReal (0 : ℝ) v) t
    simp only [mgf, id] at this
    rw [this]; simp [zero_mul, zero_add]
  have h_mgf_neg : ∫ ω : Configuration E, Real.exp (-(t * ω g)) ∂μ =
      Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    have h_eq : ∫ ω, Real.exp (-(t * ω g)) ∂μ =
        ∫ x, Real.exp ((-t) * x) ∂(μ.map (fun ω : Configuration E => ω g)) := by
      rw [show (fun ω : Configuration E => Real.exp (-(t * ω g))) =
            (fun x : ℝ => Real.exp ((-t) * x)) ∘ (fun ω : Configuration E => ω g) from by
        ext ω; simp [neg_mul]]
      exact (integral_map h_eval_meas.aemeasurable
        ((measurable_const.mul measurable_id).exp.aestronglyMeasurable)).symm
    rw [h_eq, h_gauss]
    have := congr_fun (@mgf_id_gaussianReal (0 : ℝ) v) (-t)
    simp only [mgf, id] at this
    rw [this]; congr 1; ring
  -- Step 7: Integral bound
  have h_integral_bound : ∫ ω, Real.exp (t * |ω g|) ∂μ ≤
      2 * Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    calc ∫ ω, Real.exp (t * |ω g|) ∂μ
        ≤ ∫ ω, (Real.exp (t * ω g) + Real.exp (-(t * ω g))) ∂μ := by
          apply integral_mono h_int_abs h_int_sum
          exact fun ω => h_pointwise (ω g)
      _ = ∫ ω, Real.exp (t * ω g) ∂μ + ∫ ω, Real.exp (-(t * ω g)) ∂μ :=
          integral_add h_int_pos_conf h_int_neg_conf
      _ = Real.exp ((v : ℝ) * t ^ 2 / 2) + Real.exp ((v : ℝ) * t ^ 2 / 2) := by
          rw [h_mgf_pos, h_mgf_neg]
      _ = 2 * Real.exp ((v : ℝ) * t ^ 2 / 2) := by ring
  -- Step 8: Match the second moment to ∫ (ω g)² dμ
  have h_second_moment : ∫ ω, (ω g) ^ 2 ∂μ = @inner ℝ H _ (T g) (T g) :=
    second_moment_eq_covariance T g
  have h_inner_nonneg : (0 : ℝ) ≤ @inner ℝ H _ (T g) (T g) := by
    rw [real_inner_self_eq_norm_sq]; exact sq_nonneg _
  have h_v_eq : (v : ℝ) = ∫ ω, (ω g) ^ 2 ∂μ := by
    rw [h_second_moment]; exact Real.coe_toNNReal _ h_inner_nonneg
  refine ⟨h_int_abs, ?_⟩
  calc ∫ ω, Real.exp (t * |ω g|) ∂μ
      ≤ 2 * Real.exp ((v : ℝ) * t ^ 2 / 2) := h_integral_bound
    _ = 2 * Real.exp (t ^ 2 / 2 * ∫ ω, (ω g) ^ 2 ∂μ) := by rw [h_v_eq]; ring_nf

end GaussianField

end
