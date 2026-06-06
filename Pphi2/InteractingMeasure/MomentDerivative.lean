/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.MomentIntegrability
import Pphi2.InteractingMeasure.WickConstantBridge
import Pphi2.MathlibContrib.ParametricIntegralWithin

/-!
# Moment derivative of the Gibbs family (u₄ step 2c, brick 2)

The first-order (right) derivative in the coupling `g` of the unnormalised moment
`g ↦ ∫ (ω f)ⁿ e^{-g V} dμ_GFF`, where `V = interactionFunctional` is the lattice interaction:

  `d/dg⁺ ∫ (ω f)ⁿ e^{-g V} |_{g=0} = -∫ (ω f)ⁿ V`.

This is the brick-2 instantiation: it applies the one-sided
`hasDerivWithinAt_Ici_integral_of_dominated_of_deriv_le` to `F g ω = (ω f)ⁿ e^{-g V ω}`, whose
`g`-derivative `-(ω f)ⁿ V e^{-g V}` is dominated for `g ≥ 0` by `e^{B}·|(ω f)ⁿ V|` (using `V ≥ -B`,
`interactionFunctional_bounded_below`), which is integrable by brick 1
(`integrable_powMul_interaction`).
-/

namespace Pphi2

open MeasureTheory GaussianField Set
open scoped NNReal ENNReal

variable (d N : ℕ) [NeZero N]

/-- `interactionFunctional` written with `Pi.single` (matching the brick-1 integrand). -/
lemma interactionFunctional_eq_single (P : InteractionPolynomial) (a mass : ℝ)
    (ω : Configuration (FinLatticeField d N)) :
    interactionFunctional d N P a mass ω =
      a ^ d * ∑ z, wickPolynomial P (wickConstant d N a mass) (ω (Pi.single z (1 : ℝ))) := by
  unfold interactionFunctional
  simp_rw [finLatticeDelta_eq_single]

/-- **Moment derivative (one-sided).** `g ↦ ∫ (ω f)ⁿ e^{-g V} dμ_GFF` has right-derivative
`-∫ (ω f)ⁿ V dμ_GFF` at `g = 0`, where `V = interactionFunctional`. -/
theorem moment_hasDerivWithinAt (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (n : ℕ) :
    HasDerivWithinAt
      (fun g => ∫ ω, (ω f) ^ n *
        Real.exp (-(g * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass))
      (-∫ ω, (ω f) ^ n * interactionFunctional d N P a mass ω
        ∂(latticeGaussianMeasure d N a mass ha hmass))
      (Ici 0) 0 := by
  set μ := latticeGaussianMeasure d N a mass ha hmass
  set V := interactionFunctional d N P a mass with hV
  -- `V` is measurable and bounded below.
  have hV_meas : Measurable V := interactionFunctional_measurable d N P a mass
  obtain ⟨B₀, hB₀⟩ := interactionFunctional_bounded_below d N P a mass ha hmass
  set B := |B₀| with hB
  have hB_nonneg : 0 ≤ B := abs_nonneg _
  have hVlb : ∀ ω, -B ≤ V ω := fun ω => (neg_le_neg (le_abs_self B₀)).trans (hB₀ ω)
  -- The integrand and its `g`-derivative.
  set F : ℝ → Configuration (FinLatticeField d N) → ℝ :=
    fun g ω => (ω f) ^ n * Real.exp (-(g * V ω)) with hF
  set F' : ℝ → Configuration (FinLatticeField d N) → ℝ :=
    fun g ω => (ω f) ^ n * (-V ω) * Real.exp (-(g * V ω)) with hF'
  -- `(ω f)ⁿ · V` is integrable (brick 1, rewritten to `interactionFunctional`).
  have hpowV_int : Integrable (fun ω => (ω f) ^ n * V ω) μ := by
    have h := integrable_powMul_interaction d N a mass ha hmass P f n
    have heq : (fun ω => (ω f) ^ n *
          (a ^ d * ∑ z, wickPolynomial P (wickConstant d N a mass) (ω (Pi.single z (1 : ℝ))))) =
        (fun ω => (ω f) ^ n * V ω) := by
      funext ω; rw [hV, interactionFunctional_eq_single]
    rwa [heq] at h
  -- Measurability of `(ω f)ⁿ`.
  have hpow_meas : Measurable (fun ω : Configuration (FinLatticeField d N) => (ω f) ^ n) :=
    (configuration_eval_measurable f).pow_const n
  -- `F 0` integrable: it is `(ω f)ⁿ`.
  have hF0_int : Integrable (F 0) μ := by
    refine (integrable_pow_pairing d N a mass ha hmass f n).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    simp [hF]
  -- The bound function `e^B · |(ω f)ⁿ V|`, integrable.
  have hbound_int : Integrable (fun ω => Real.exp B * |(ω f) ^ n * V ω|) μ :=
    (hpowV_int.abs).const_mul (Real.exp B)
  -- The derivative value `∫ F' 0` is `-∫ (ω f)ⁿ V`.
  have heq_deriv : (∫ ω, F' 0 ω ∂μ) = -∫ ω, (ω f) ^ n * V ω ∂μ := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hF', zero_mul, neg_zero, Real.exp_zero, mul_one]
    ring
  rw [← heq_deriv]
  refine (hasDerivWithinAt_Ici_integral_of_dominated_of_deriv_le (μ := μ) (F := F)
    (F' := F') (x₀ := 0) (bound := fun ω => Real.exp B * |(ω f) ^ n * V ω|)
    one_pos ?_ hF0_int ?_ ?_ hbound_int ?_).2
  · -- measurability of `F g` for `g ∈ Ici 0 ∩ ball 0 1`
    intro g _
    exact (hpow_meas.mul ((hV_meas.const_mul g).neg.exp)).aestronglyMeasurable.congr
      (Filter.Eventually.of_forall fun ω => by simp only [hF])
  · -- measurability of `F' 0`
    exact ((hpow_meas.mul hV_meas.neg).mul
      ((hV_meas.const_mul (0 : ℝ)).neg.exp)).aestronglyMeasurable.congr
      (Filter.Eventually.of_forall fun ω => by simp only [hF'])
  · -- derivative bound for `g ∈ Ici 0 ∩ ball 0 1`
    refine Filter.Eventually.of_forall fun ω g hg => ?_
    have hg0 : (0 : ℝ) ≤ g := mem_Ici.mp hg.1
    have hg1 : g < 1 := by
      have := mem_ball_zero_iff.mp hg.2; rwa [Real.norm_eq_abs, abs_of_nonneg hg0] at this
    have hexp : Real.exp (-(g * V ω)) ≤ Real.exp B :=
      Real.exp_le_exp.mpr (by nlinarith [hVlb ω, hg0, hg1, hB_nonneg])
    calc ‖F' g ω‖ = |(ω f) ^ n * V ω| * Real.exp (-(g * V ω)) := by
            rw [hF', Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le,
              show (ω f) ^ n * -V ω = -((ω f) ^ n * V ω) from by ring, abs_neg]
      _ ≤ |(ω f) ^ n * V ω| * Real.exp B := mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
      _ = Real.exp B * |(ω f) ^ n * V ω| := mul_comm _ _
  · -- within-`Ici 0` derivative of `g ↦ F g ω`
    refine Filter.Eventually.of_forall fun ω g _ => ?_
    have hlin : HasDerivAt (fun g => -(g * V ω)) (-V ω) g := by
      simpa using ((hasDerivAt_id g).mul_const (V ω)).neg
    have hd : HasDerivAt (fun g => F g ω) (F' g ω) g := by
      have hh := (hlin.exp).const_mul ((ω f) ^ n)
      convert hh using 1
      rw [hF']; ring
    exact hd.hasDerivWithinAt

end Pphi2
