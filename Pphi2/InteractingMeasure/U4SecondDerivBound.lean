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

/-- **Ratio `L²` bound (reusable).** For `X ∈ L²(μ_GFF)` with `∫X² ≤ C`, the Gibbs ratio
`(∫ X e^{-gV})/Z` is bounded by `C^{1/2}·K^{1/2}` (`g ∈ [0,1]`, Nelson `K`). Thin wrapper over
`abs_interacting_moment_le` + rpow monotonicity; the workhorse for every `u₄''` ratio. -/
theorem ratio_l2_bound {N : ℕ} [NeZero N] (mass : ℝ) (hmass : 0 < mass) (P : InteractionPolynomial)
    (X : Configuration (FinLatticeField 2 N) → ℝ)
    (hX : MemLp X 2 (latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass))
    (C : ℝ) (hC : ∫ ω, (X ω) ^ 2
        ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass) ≤ C)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1) {K : ℝ} (hK1 : 1 ≤ K)
    (hKbd : ∫ ω, Real.exp (-(2 * interactionFunctional 2 N P (circleSpacing L N) mass ω))
        ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass) ≤ K) :
    |(∫ ω, X ω * Real.exp (-(g * interactionFunctional 2 N P (circleSpacing L N) mass ω))
        ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass)) /
      (∫ ω, Real.exp (-(g * interactionFunctional 2 N P (circleSpacing L N) mass ω))
        ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass))|
      ≤ C ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) := by
  refine le_trans (abs_interacting_moment_le 2 N P (circleSpacing L N) mass (circleSpacing_pos L N)
    hmass X hX hg0 hg1 hK1 hKbd) ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (le_trans zero_le_one hK1) _)
  exact Real.rpow_le_rpow (integral_nonneg fun ω => sq_nonneg _) hC (by norm_num)

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

/-- **`|m_n'(g)| ≤ B'_n` uniform.** `m_n'(g) = (M_n/Z)(Z'/Z)·(sign) − M_n'/Z` decomposes into three
Gibbs ratios with *positive-integral* numerators (observables `(ωf)ⁿV`, `(ωf)ⁿ`, `V`; the minus
signs absorbed by `field_simp;ring`), each bounded uniformly by `ratio_l2_bound` + L3 + Nelson. -/
theorem normalizedMomentDeriv_abs_le (mass : ℝ) (hmass : 0 < mass) (P : InteractionPolynomial)
    (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ) [NeZero N], ∀ g : ℝ, 0 ≤ g → g ≤ 1 →
      |normalizedMomentDeriv 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass P
          (fun _ : FinLatticeSites 2 N => (Fintype.card (FinLatticeSites 2 N) : ℝ)⁻¹) n g| ≤
        B := by
  obtain ⟨K, hK1, hKbd⟩ := expMoment_two_le_uniform L P mass hmass
  obtain ⟨C1, hC1, hC1b⟩ := torus_free_product_moment_uniform L mass hmass P n 1 le_rfl
  obtain ⟨Cf, hCf, hCfb⟩ := torus_normConst_field_moment_uniform L mass hmass n
  obtain ⟨C0, hC0, hC0b⟩ := torus_free_product_moment_uniform L mass hmass P 0 1 le_rfl
  refine ⟨Cf ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) * (C0 ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ))
    + C1 ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) + 1, by positivity, fun N _ g hg0 hg1 => ?_⟩
  have ha : 0 < circleSpacing L N := circleSpacing_pos L N
  set fc : FinLatticeField 2 N :=
    fun _ => (Fintype.card (FinLatticeSites 2 N) : ℝ)⁻¹ with hfc
  set μ := latticeGaussianMeasure 2 N (circleSpacing L N) mass ha hmass with hμ
  have hZ : (∫ ω, Real.exp (-(g * interactionFunctional 2 N P (circleSpacing L N) mass ω)) ∂μ) ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one
      (partitionFn_ge_one 2 N P (circleSpacing L N) mass ha hmass hg0)).ne'
  -- observables and their MemLp / L² bounds
  have hXMD : MemLp (fun ω => (ω fc) ^ n * interactionFunctional 2 N P (circleSpacing L N) mass ω) 2 μ := by
    simpa only [pow_one] using
      memLp_pairing_pow_mul_interaction_pow (circleSpacing L N) mass ha hmass P fc n 1 le_rfl
  have hXGM : MemLp (fun ω => (ω fc) ^ n) 2 μ := by
    rw [memLp_two_iff_integrable_sq
      ((configuration_eval_measurable fc).pow_const n).aestronglyMeasurable]
    refine (integrable_pow_pairing 2 N (circleSpacing L N) mass ha hmass fc (2 * n)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    show (ω fc) ^ (2 * n) = ((ω fc) ^ n) ^ 2
    rw [← pow_mul]; congr 1; ring
  have hXPD : MemLp (fun ω => interactionFunctional 2 N P (circleSpacing L N) mass ω) 2 μ := by
    simpa only [pow_one, pow_zero, one_mul] using
      memLp_pairing_pow_mul_interaction_pow (circleSpacing L N) mass ha hmass P fc 0 1 le_rfl
  have hCMD : ∫ ω, ((ω fc) ^ n * interactionFunctional 2 N P (circleSpacing L N) mass ω) ^ 2 ∂μ ≤ C1 := by
    refine le_trans (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_))) (hC1b N)
    show ((ω fc) ^ n * interactionFunctional 2 N P (circleSpacing L N) mass ω) ^ 2 = (ω fc) ^ (2 * n) * interactionFunctional 2 N P (circleSpacing L N) mass ω ^ (2 * 1)
    ring
  have hCGM : ∫ ω, ((ω fc) ^ n) ^ 2 ∂μ ≤ Cf := by
    refine le_trans (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_))) (hCfb N)
    show ((ω fc) ^ n) ^ 2 = (ω fc) ^ (2 * n)
    rw [← pow_mul]; congr 1; ring
  have hCPD : ∫ ω, (interactionFunctional 2 N P (circleSpacing L N) mass ω) ^ 2 ∂μ ≤ C0 := by
    refine le_trans (le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_))) (hC0b N)
    show (interactionFunctional 2 N P (circleSpacing L N) mass ω) ^ 2 = (ω fc) ^ (2 * 0) * interactionFunctional 2 N P (circleSpacing L N) mass ω ^ (2 * 1)
    simp
  -- the three ratio bounds
  have hrMD := ratio_l2_bound L mass hmass P (fun ω => (ω fc) ^ n * interactionFunctional 2 N P (circleSpacing L N) mass ω) hXMD C1 hCMD hg0 hg1 hK1
    (hKbd N)
  have hrGM := ratio_l2_bound L mass hmass P (fun ω => (ω fc) ^ n) hXGM Cf hCGM hg0 hg1 hK1 (hKbd N)
  have hrPD := ratio_l2_bound L mass hmass P (fun ω => interactionFunctional 2 N P (circleSpacing L N) mass ω) hXPD C0 hCPD hg0 hg1 hK1 (hKbd N)
  -- |Gibbs ratio| bounds: relate each Gibbs def to its `ratio_l2_bound`
  have hbMD : |momentDeriv 2 N (circleSpacing L N) mass ha hmass P fc n g
      / partitionFn 2 N (circleSpacing L N) mass ha hmass P g| ≤ C1 ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) := by
    unfold momentDeriv partitionFn; rw [neg_div, abs_neg]; exact hrMD
  have hbGM : |gibbsMoment 2 N (circleSpacing L N) mass ha hmass P fc n g
      / partitionFn 2 N (circleSpacing L N) mass ha hmass P g| ≤ Cf ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) := by
    unfold gibbsMoment partitionFn; exact hrGM
  have hbPD : |partitionFnDeriv 2 N (circleSpacing L N) mass ha hmass P g
      / partitionFn 2 N (circleSpacing L N) mass ha hmass P g| ≤ C0 ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) := by
    unfold partitionFnDeriv partitionFn; rw [neg_div, abs_neg]; exact hrPD
  have hZ' : partitionFn 2 N (circleSpacing L N) mass ha hmass P g ≠ 0 := by unfold partitionFn; exact hZ
  -- decomposition with Gibbs defs as atoms (no `exp` args exposed to `ring`)
  have hdecomp : normalizedMomentDeriv 2 N (circleSpacing L N) mass ha hmass P fc n g
      = momentDeriv 2 N (circleSpacing L N) mass ha hmass P fc n g
          / partitionFn 2 N (circleSpacing L N) mass ha hmass P g
        - (gibbsMoment 2 N (circleSpacing L N) mass ha hmass P fc n g
            / partitionFn 2 N (circleSpacing L N) mass ha hmass P g)
          * (partitionFnDeriv 2 N (circleSpacing L N) mass ha hmass P g
            / partitionFn 2 N (circleSpacing L N) mass ha hmass P g) := by
    unfold normalizedMomentDeriv; field_simp
  rw [hdecomp]
  calc |momentDeriv 2 N (circleSpacing L N) mass ha hmass P fc n g
            / partitionFn 2 N (circleSpacing L N) mass ha hmass P g
          - gibbsMoment 2 N (circleSpacing L N) mass ha hmass P fc n g
              / partitionFn 2 N (circleSpacing L N) mass ha hmass P g
            * (partitionFnDeriv 2 N (circleSpacing L N) mass ha hmass P g
              / partitionFn 2 N (circleSpacing L N) mass ha hmass P g)|
      ≤ |momentDeriv 2 N (circleSpacing L N) mass ha hmass P fc n g
            / partitionFn 2 N (circleSpacing L N) mass ha hmass P g|
        + |gibbsMoment 2 N (circleSpacing L N) mass ha hmass P fc n g
              / partitionFn 2 N (circleSpacing L N) mass ha hmass P g
            * (partitionFnDeriv 2 N (circleSpacing L N) mass ha hmass P g
              / partitionFn 2 N (circleSpacing L N) mass ha hmass P g)| := abs_sub _ _
    _ = |momentDeriv 2 N (circleSpacing L N) mass ha hmass P fc n g
            / partitionFn 2 N (circleSpacing L N) mass ha hmass P g|
        + |gibbsMoment 2 N (circleSpacing L N) mass ha hmass P fc n g
              / partitionFn 2 N (circleSpacing L N) mass ha hmass P g|
          * |partitionFnDeriv 2 N (circleSpacing L N) mass ha hmass P g
              / partitionFn 2 N (circleSpacing L N) mass ha hmass P g| := by rw [abs_mul]
    _ ≤ C1 ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ)
        + Cf ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) * (C0 ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ)) := by
        gcongr
    _ ≤ _ := by linarith

end Pphi2
