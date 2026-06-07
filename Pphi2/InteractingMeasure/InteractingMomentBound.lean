/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.UniformBounds

/-!
# Absolute interacting-moment bound (uniform-discharge leaf `L5c`, analytic input)

The signed companion of `interacting_moment_le_L2_of_expBound`: the interacting moment
`⟨X⟩_t = (∫ X e^{-tV})/(∫ e^{-tV})` of any `L²` observable `X` is controlled in absolute value by its
free `L²` norm,
`|⟨X⟩_t| ≤ ‖X‖_{L²(μ_GFF)}·√K` (`t ∈ [0,1]`, `K` the Nelson exp-moment bound). Applied with
`X = (ωf)ⁿ Vᵇ` and the L3 free-moment bounds, this bounds each interacting moment appearing in the
`u₄''` expansion uniformly in `N` — the input for the affine derivative bound
`u₄'(t) ≤ -s + K·t`.
-/

namespace Pphi2

open MeasureTheory GaussianField

variable (d N : ℕ) [NeZero N]

/-- **Absolute interacting moment ≤ free `L²` norm.** For `X ∈ L²(μ_GFF)`, `t ∈ [0,1]`, and a Nelson
exp-bound `∫e^{-2V} ≤ K` (`K ≥ 1`):
`|(∫ X e^{-tV})/(∫ e^{-tV})| ≤ (∫ X²)^{1/2}·K^{1/2}`. From `|∫ X e^{-tV}| ≤ ∫ |X| e^{-tV}`
(`abs_integral_le_integral_abs`, `e^{-tV} > 0`) and `interacting_moment_le_L2_of_expBound`. -/
lemma abs_interacting_moment_le (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a)
    (hmass : 0 < mass) (X : Configuration (FinLatticeField d N) → ℝ)
    (hX : MemLp X 2 (latticeGaussianMeasure d N a mass ha hmass))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {K : ℝ} (hK1 : 1 ≤ K)
    (hKbound : ∫ ω, Real.exp (-(2 * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K) :
    |(∫ ω, X ω * Real.exp (-(t * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass)) /
      (∫ ω, Real.exp (-(t * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass))|
      ≤ (∫ ω, (X ω) ^ 2 ∂(latticeGaussianMeasure d N a mass ha hmass)) ^ (1 / 2 : ℝ) *
        K ^ (1 / 2 : ℝ) := by
  set μ := latticeGaussianMeasure d N a mass ha hmass with hμ
  set V := interactionFunctional d N P a mass with hV
  have hZpos : 0 < ∫ ω, Real.exp (-(t * V ω)) ∂μ :=
    lt_of_lt_of_le zero_lt_one (partitionFn_ge_one d N P a mass ha hmass ht0)
  have hnum : |∫ ω, X ω * Real.exp (-(t * V ω)) ∂μ|
      ≤ ∫ ω, |X ω| * Real.exp (-(t * V ω)) ∂μ := by
    refine le_trans (abs_integral_le_integral_abs) (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show |X ω * Real.exp (-(t * V ω))| = |X ω| * Real.exp (-(t * V ω))
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [abs_div, abs_of_pos hZpos]
  refine le_trans ((div_le_div_iff_of_pos_right hZpos).mpr hnum) ?_
  exact interacting_moment_le_L2_of_expBound d N P a mass ha hmass X hX ht0 ht1 hK1 hKbound

end Pphi2
