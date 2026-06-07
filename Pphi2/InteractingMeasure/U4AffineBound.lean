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

open MeasureTheory GaussianField Set

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

end Pphi2
