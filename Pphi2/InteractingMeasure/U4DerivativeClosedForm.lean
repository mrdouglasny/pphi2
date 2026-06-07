/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.U4DerivativeInterior

/-!
# Closed-form first derivative of the Gibbs-family `u₄` (uniform-discharge leaf `L5a`)

The interior-`t` quotient-rule companion of `normalizedMoment_hasDerivWithinAt` (which is only at
`g=0`), giving an explicit value for `deriv u₄_N t` — the prerequisite for the affine bound
`u₄'(t) ≤ -s + K·t` (`hbound` of `exists_uniform_neg_of_uniform_affine_bound'`).

* `normalizedMoment_hasDerivAt` — `m_n(t) = M_n(t)/Z(t)` has derivative
  `(M_n'(t)·Z(t) − M_n(t)·Z'(t)) / Z(t)²` with `M_n'(t) = -∫(ωf)ⁿVe^{-tV}`, `Z'(t) = -∫Ve^{-tV}`.
* `u4_hasDerivAt` — `u₄ = m₄ − 3 m₂²` has derivative `m₄'(t) − 6 m₂(t) m₂'(t)` at interior `t`.
-/

namespace Pphi2

open MeasureTheory GaussianField Set

variable (d N : ℕ) [NeZero N]

/-- **L5a — normalised-moment derivative at interior `t > 0`.** The normalised moment
`m_n(g) = (∫(ωf)ⁿe^{-gV})/(∫e^{-gV})` has derivative `(M_n'(t)·Z(t) − M_n(t)·Z'(t))/Z(t)²` at `t`,
where `M_n'(t) = -∫(ωf)ⁿVe^{-tV}` (`moment_hasDerivAt`) and `Z'(t) = -∫Ve^{-tV}`
(`partitionFn_hasDerivAt`). The quotient rule on the Gibbs family. -/
theorem normalizedMoment_hasDerivAt (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun g => (∫ ω, (ω f) ^ n * Real.exp (-(g * interactionFunctional d N P a mass ω))
          ∂(latticeGaussianMeasure d N a mass ha hmass)) /
        (∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω))
          ∂(latticeGaussianMeasure d N a mass ha hmass)))
      (((-∫ ω, (ω f) ^ n * interactionFunctional d N P a mass ω *
              Real.exp (-(t * interactionFunctional d N P a mass ω))
              ∂(latticeGaussianMeasure d N a mass ha hmass)) *
            (∫ ω, Real.exp (-(t * interactionFunctional d N P a mass ω))
              ∂(latticeGaussianMeasure d N a mass ha hmass)) -
          (∫ ω, (ω f) ^ n * Real.exp (-(t * interactionFunctional d N P a mass ω))
              ∂(latticeGaussianMeasure d N a mass ha hmass)) *
            (-∫ ω, interactionFunctional d N P a mass ω *
              Real.exp (-(t * interactionFunctional d N P a mass ω))
              ∂(latticeGaussianMeasure d N a mass ha hmass))) /
        (∫ ω, Real.exp (-(t * interactionFunctional d N P a mass ω))
          ∂(latticeGaussianMeasure d N a mass ha hmass)) ^ 2)
      t := by
  have hZne : (∫ ω, Real.exp (-(t * interactionFunctional d N P a mass ω))
      ∂(latticeGaussianMeasure d N a mass ha hmass)) ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (partitionFn_ge_one d N P a mass ha hmass ht.le)).ne'
  exact (moment_hasDerivAt d N a mass ha hmass P f n ht).div
    (partitionFn_hasDerivAt d N a mass ha hmass P ht) hZne

/-- **Partition-function second derivative at interior `t > 0`.** `Z''(t) = ∫ V² e^{-tV}` — the
`n = 0` case of `moment_hasDerivAt2`. Together with `partitionFn_hasDerivAt` this gives `Z ∈ C²` on
`(0,∞)`, an ingredient for the normalised-moment second derivative. -/
theorem partitionFn_hasDerivAt2 (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun g => -∫ ω, interactionFunctional d N P a mass ω *
        Real.exp (-(g * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass))
      (∫ ω, (interactionFunctional d N P a mass ω) ^ 2 *
        Real.exp (-(t * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass))
      t := by
  have h := moment_hasDerivAt2 d N a mass ha hmass P (0 : FinLatticeField d N) 0 ht
  simpa only [pow_zero, one_mul] using h

end Pphi2
