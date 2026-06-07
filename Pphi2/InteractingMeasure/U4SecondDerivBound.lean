/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.U4DerivativeClosedForm
import Pphi2.InteractingMeasure.InteractingMomentBound
import Pphi2.InteractingMeasure.FreeMomentBound
import Pphi2.TorusContinuumLimit.TorusInteractingLimit

/-!
# Uniform bound on `u₄''` (uniform-discharge leaf `L5c`)

Toward `|u₄''(t)| ≤ K` uniform in `N` on `[0,1]`, the input for the affine derivative bound
`u₄'(t) ≤ -s + K·t`. Every `normalizedMoment*`/`normalizedMomentDeriv*` reduces to ratios
`(∫ (ωf)ⁿ Vᵇ e^{-gV})/Z` (`n ≤ 4`, `b ≤ 2`), each bounded uniformly by `abs_interacting_moment_le`
(`|⟨X⟩_t| ≤ ‖X‖_{L²}√K`) + the L3 free-moment bounds + Nelson's `expMoment_two_le_uniform`.

This file builds the bound bottom-up; `normalizedMoment_abs_le` is the pattern-setter (the `b=0`,
single-ratio case) establishing the `f_c`/Nelson/L3 plumbing the derivative bounds reuse.
-/

namespace Pphi2

open MeasureTheory GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-- **`|m_n(g)| ≤ B_n` uniform** (the `b=0` pattern-setter). The normalised moment
`normalizedMoment n g = (∫(ωf_c)ⁿ e^{-gV})/Z` for the normalised-constant test function `f_c` is
bounded uniformly in `N` and `g ∈ [0,1]` via `abs_interacting_moment_le` (with `X = (ωf_c)ⁿ`) and the
uniform field moment `torus_normConst_field_moment_uniform`. -/
theorem normalizedMoment_abs_le (mass : ℝ) (hmass : 0 < mass) (P : InteractionPolynomial) (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ) [NeZero N], ∀ g : ℝ, 0 ≤ g → g ≤ 1 →
      |normalizedMoment 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass P
          (fun _ : FinLatticeSites 2 N => (Fintype.card (FinLatticeSites 2 N) : ℝ)⁻¹) n g| ≤
        B := by
  obtain ⟨K, hK1, hKbd⟩ := expMoment_two_le_uniform L P mass hmass
  obtain ⟨Cf, hCf, hCfb⟩ := torus_normConst_field_moment_uniform L mass hmass n
  refine ⟨Cf ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) + 1, by positivity, fun N _ g hg0 hg1 => ?_⟩
  have ha : 0 < circleSpacing L N := circleSpacing_pos L N
  set fc : FinLatticeField 2 N :=
    fun _ => (Fintype.card (FinLatticeSites 2 N) : ℝ)⁻¹ with hfc
  set μ := latticeGaussianMeasure 2 N (circleSpacing L N) mass ha hmass with hμ
  have hXmem : MemLp (fun ω => (ω fc) ^ n) 2 μ := by
    rw [memLp_two_iff_integrable_sq
      ((configuration_eval_measurable fc).pow_const n).aestronglyMeasurable]
    refine (integrable_pow_pairing 2 N (circleSpacing L N) mass ha hmass fc (2 * n)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    show (ω fc) ^ (2 * n) = ((ω fc) ^ n) ^ 2
    rw [← pow_mul]; congr 1; ring
  have hbd := abs_interacting_moment_le 2 N P (circleSpacing L N) mass ha hmass
    (fun ω => (ω fc) ^ n) hXmem hg0 hg1 hK1 (hKbd N)
  have hsq : (∫ ω, ((ω fc) ^ n) ^ 2 ∂μ) = ∫ ω, (ω fc) ^ (2 * n) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show ((ω fc) ^ n) ^ 2 = (ω fc) ^ (2 * n)
    rw [← pow_mul]; congr 1; ring
  rw [hsq] at hbd
  -- `normalizedMoment` unfolds definitionally to the ratio bounded by `hbd`
  refine le_trans (le_of_eq ?_) (le_trans hbd ?_)
  · rfl
  · have hmono : (∫ ω, (ω fc) ^ (2 * n) ∂μ) ^ (1 / 2 : ℝ) ≤ Cf ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (integral_nonneg fun ω => (even_two_mul n).pow_nonneg _) (hCfb N)
        (by norm_num)
    have : (∫ ω, (ω fc) ^ (2 * n) ∂μ) ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ)
        ≤ Cf ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg (le_trans zero_le_one hK1) _)
    linarith

end Pphi2
