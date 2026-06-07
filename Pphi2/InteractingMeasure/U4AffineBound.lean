/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.U4DerivativeClosedForm
import Pphi2.InteractingMeasure.U4Derivative
import Pphi2.InteractingMeasure.U4SecondDerivBound

/-!
# Affine derivative bound for `u₄` (uniform-discharge leaf `L5d`)

Assembles the affine bound `deriv u₄ t ≤ -s + K·t` on `(0,g₀)` — the final `hbound` leaf of
`exists_uniform_neg_of_uniform_affine_bound'` — from:
* `u4Deriv_zero_eq` — `u₄'(0) = -6 a^d ∑(C_af)⁴ = -s` (the closed-form first derivative at `g=0`
  equals the leading slope, by derivative-uniqueness against `u4_hasDerivWithinAt`);
* `u4Deriv2_abs_le_uniform` (L5c) — `|u₄''| ≤ K` uniform;
* the mean value theorem on `u4Deriv`.
-/

namespace Pphi2

open MeasureTheory GaussianField Set Topology

variable (d N : ℕ) [NeZero N]

/-- **`m_n'(0)` is the free connected correlator.** Evaluating the closed-form normalised-moment
derivative at `g=0` (where `Z(0)=1`, `e^{-0·V}=1`) gives `-⟨(ωf)ⁿV⟩₀ + ⟨(ωf)ⁿ⟩₀⟨V⟩₀`. -/
lemma normalizedMomentDeriv_zero (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (n : ℕ) :
    normalizedMomentDeriv d N a mass ha hmass P f n 0
      = -(∫ ω, (ω f) ^ n * interactionFunctional d N P a mass ω
            ∂(latticeGaussianMeasure d N a mass ha hmass))
        + (∫ ω, (ω f) ^ n ∂(latticeGaussianMeasure d N a mass ha hmass))
          * (∫ ω, interactionFunctional d N P a mass ω
            ∂(latticeGaussianMeasure d N a mass ha hmass)) := by
  haveI := latticeGaussianMeasure_isProbability d N a mass ha hmass
  unfold normalizedMomentDeriv momentDeriv gibbsMoment partitionFn partitionFnDeriv
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, integral_const, smul_eq_mul,
    probReal_univ, one_pow, div_one]
  ring

/-- **`m_n(0)` is the free moment.** `Z(0)=1`, so `normalizedMoment n 0 = ∫(ωf)ⁿ`. -/
lemma normalizedMoment_zero (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (n : ℕ) :
    normalizedMoment d N a mass ha hmass P f n 0
      = ∫ ω, (ω f) ^ n ∂(latticeGaussianMeasure d N a mass ha hmass) := by
  haveI := latticeGaussianMeasure_isProbability d N a mass ha hmass
  unfold normalizedMoment gibbsMoment partitionFn
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, integral_const, smul_eq_mul,
    probReal_univ, div_one]

/-- **L5d — `u₄'(0) = -s`.** The closed-form first derivative at `g=0` equals the leading slope
`-6 a^d ∑(C_af)⁴`. Proof: `u4Deriv 0` assembles (via the `g=0` evaluations) into the within-derivative
of `u₄` at `0`, which `u4_hasDerivWithinAt` identifies as `-6 a^d ∑(C_af)⁴`; conclude by
derivative-uniqueness on `Ici 0`. -/
lemma u4Deriv_zero_eq (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (hP : P.n = 4) (f : FinLatticeField d N) :
    u4Deriv d N a mass ha hmass P f 0
      = -6 * a ^ d * ∑ z, (∑ x, f x * gffPositionCovariance d N a mass x z) ^ 4 := by
  haveI := latticeGaussianMeasure_isProbability d N a mass ha hmass
  have h4 := normalizedMoment_hasDerivWithinAt d N a mass ha hmass P f 4
  have h2 := normalizedMoment_hasDerivWithinAt d N a mass ha hmass P f 2
  have hu : HasDerivWithinAt (u4 d N a mass ha hmass P f)
      (u4Deriv d N a mass ha hmass P f 0) (Ici 0) 0 := by
    have hcomb := h4.sub ((h2.pow 2).const_mul (3 : ℝ))
    convert hcomb using 1
    unfold u4Deriv
    rw [normalizedMomentDeriv_zero, normalizedMomentDeriv_zero, normalizedMoment_zero]
    simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, integral_const, smul_eq_mul,
      probReal_univ, div_one, pow_one]
    ring
  have h2u := u4_hasDerivWithinAt d N a mass ha hmass P hP f
  have heq := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq hu.hasFDerivWithinAt h2u.hasFDerivWithinAt
  simpa using heq

/-- **Right-continuity at `0` of a weighted Gibbs integral.** For any integrable weight `w`,
`g ↦ ∫ w·e^{-gV}` is continuous within `Ici 0` at `0`. Dominated convergence with bound
`|w|·e^{B}` (`V ≥ -B`, so `e^{-gV} ≤ e^{B}` for `g ∈ [0,1]`); the integrand is continuous in `g`. -/
lemma continuousWithinAt_weighted_exp (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (w : Configuration (FinLatticeField d N) → ℝ)
    (hw_meas : Measurable w)
    (hw_int : Integrable w (latticeGaussianMeasure d N a mass ha hmass)) :
    ContinuousWithinAt
      (fun g => ∫ ω, w ω * Real.exp (-(g * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass)) (Ici 0) 0 := by
  set μ := latticeGaussianMeasure d N a mass ha hmass with hμ
  have hV_meas : Measurable (interactionFunctional d N P a mass) :=
    interactionFunctional_measurable d N P a mass
  obtain ⟨B₀, hB₀⟩ := interactionFunctional_bounded_below d N P a mass ha hmass
  set B := |B₀| with hB
  have hB_nonneg : 0 ≤ B := abs_nonneg _
  have hVlb : ∀ ω, -B ≤ interactionFunctional d N P a mass ω :=
    fun ω => le_trans (neg_le_neg (le_abs_self B₀)) (by simpa using hB₀ ω)
  have hg_ev : ∀ᶠ g in 𝓝[Ici 0] (0 : ℝ), 0 ≤ g ∧ g ≤ 1 := by
    have h0 : ∀ᶠ g in 𝓝[Ici 0] (0 : ℝ), (0 : ℝ) ≤ g := by
      filter_upwards [self_mem_nhdsWithin] with g hg using hg
    have h1 : ∀ᶠ g in 𝓝[Ici 0] (0 : ℝ), g ≤ 1 :=
      eventually_nhdsWithin_of_eventually_nhds
        (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [h0, h1] with g hg0 hg1 using ⟨hg0, hg1⟩
  refine continuousWithinAt_of_dominated
    (bound := fun ω => |w ω| * Real.exp B) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun g =>
      (hw_meas.mul ((hV_meas.const_mul g).neg.exp)).aestronglyMeasurable
  · filter_upwards [hg_ev] with g hg
    refine Filter.Eventually.of_forall fun ω => ?_
    have hexp : Real.exp (-(g * interactionFunctional d N P a mass ω)) ≤ Real.exp B :=
      Real.exp_le_exp.mpr (by nlinarith [hVlb ω, hg.1, hg.2, hB_nonneg])
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
  · exact hw_int.abs.mul_const _
  · exact Filter.Eventually.of_forall fun ω =>
      (continuous_const.mul (Real.continuous_exp.comp
        ((continuous_id.mul continuous_const).neg))).continuousWithinAt

/-- **Right-continuity at `0` of `u₄'`.** `u4Deriv` is `ContinuousWithinAt (Ici 0) 0` — every
constituent Gibbs integral (`gibbsMoment`, `momentDeriv`, `partitionFn`, `partitionFnDeriv`) is, by
`continuousWithinAt_weighted_exp`, and `Z(0)=1≠0` keeps the quotients continuous. The continuity
input for the MVT affine bound. -/
lemma continuousWithinAt_u4Deriv (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) :
    ContinuousWithinAt (u4Deriv d N a mass ha hmass P f) (Ici 0) 0 := by
  have hV_meas : Measurable (interactionFunctional d N P a mass) :=
    interactionFunctional_measurable d N P a mass
  have hf_meas : Measurable (fun ω : Configuration (FinLatticeField d N) => ω f) :=
    configuration_eval_measurable f
  -- integrabilities of the weights
  have hint_powV : ∀ n : ℕ, Integrable (fun ω => (ω f) ^ n * interactionFunctional d N P a mass ω)
      (latticeGaussianMeasure d N a mass ha hmass) := fun n =>
    (integrable_powMul_interaction d N a mass ha hmass P f n).congr
      (Filter.Eventually.of_forall fun ω => by simp only [interactionFunctional_eq_single])
  have hint_V : Integrable (interactionFunctional d N P a mass)
      (latticeGaussianMeasure d N a mass ha hmass) :=
    (hint_powV 0).congr (Filter.Eventually.of_forall fun ω => by simp)
  -- the four constituent continuities
  have hcZ : ContinuousWithinAt (partitionFn d N a mass ha hmass P) (Ici 0) 0 := by
    unfold partitionFn
    simpa using continuousWithinAt_weighted_exp d N a mass ha hmass P (fun _ => 1)
      measurable_const (integrable_const 1)
  have hZ0 : partitionFn d N a mass ha hmass P 0 ≠ 0 := by
    unfold partitionFn
    exact (lt_of_lt_of_le one_pos (partitionFn_ge_one d N P a mass ha hmass le_rfl)).ne'
  have hcGM : ∀ n : ℕ, ContinuousWithinAt (gibbsMoment d N a mass ha hmass P f n) (Ici 0) 0 :=
    fun n => continuousWithinAt_weighted_exp d N a mass ha hmass P (fun ω => (ω f) ^ n)
      (hf_meas.pow_const n) (integrable_pow_pairing d N a mass ha hmass f n)
  have hcMD : ∀ n : ℕ, ContinuousWithinAt (momentDeriv d N a mass ha hmass P f n) (Ici 0) 0 :=
    fun n => (continuousWithinAt_weighted_exp d N a mass ha hmass P
      (fun ω => (ω f) ^ n * interactionFunctional d N P a mass ω)
      ((hf_meas.pow_const n).mul hV_meas) (hint_powV n)).neg
  have hcPD : ContinuousWithinAt (partitionFnDeriv d N a mass ha hmass P) (Ici 0) 0 :=
    (continuousWithinAt_weighted_exp d N a mass ha hmass P (interactionFunctional d N P a mass)
      hV_meas hint_V).neg
  -- normalised moment + derivative continuity
  have hcNM : ∀ n : ℕ, ContinuousWithinAt (normalizedMoment d N a mass ha hmass P f n) (Ici 0) 0 :=
    fun n => by unfold normalizedMoment; exact (hcGM n).div hcZ hZ0
  have hcNMD : ∀ n : ℕ,
      ContinuousWithinAt (normalizedMomentDeriv d N a mass ha hmass P f n) (Ici 0) 0 := fun n => by
    unfold normalizedMomentDeriv
    exact (((hcMD n).mul hcZ).sub ((hcGM n).mul hcPD)).div (hcZ.pow 2) (pow_ne_zero 2 hZ0)
  unfold u4Deriv
  exact (hcNMD 4).sub (((hcNM 2).mul (hcNMD 2)).const_mul 6)

end Pphi2
