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

/-! ## Closed-form `u₄'`, `u₄''` as functions (L5a/L5b) -/

/-- Unnormalised moment `M_n(g) = ∫ (ωf)ⁿ e^{-gV}`. -/
noncomputable def gibbsMoment (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (n : ℕ) (g : ℝ) : ℝ :=
  ∫ ω, (ω f) ^ n * Real.exp (-(g * interactionFunctional d N P a mass ω))
    ∂(latticeGaussianMeasure d N a mass ha hmass)

/-- Partition function `Z(g) = ∫ e^{-gV}`. -/
noncomputable def partitionFn (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (g : ℝ) : ℝ :=
  ∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω))
    ∂(latticeGaussianMeasure d N a mass ha hmass)

/-- `M_n'(g) = -∫ (ωf)ⁿ V e^{-gV}`. -/
noncomputable def momentDeriv (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (n : ℕ) (g : ℝ) : ℝ :=
  -∫ ω, (ω f) ^ n * interactionFunctional d N P a mass ω *
    Real.exp (-(g * interactionFunctional d N P a mass ω))
    ∂(latticeGaussianMeasure d N a mass ha hmass)

/-- `M_n''(g) = ∫ (ωf)ⁿ V² e^{-gV}`. -/
noncomputable def momentDeriv2 (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (n : ℕ) (g : ℝ) : ℝ :=
  ∫ ω, (ω f) ^ n * (interactionFunctional d N P a mass ω) ^ 2 *
    Real.exp (-(g * interactionFunctional d N P a mass ω))
    ∂(latticeGaussianMeasure d N a mass ha hmass)

/-- `Z'(g) = -∫ V e^{-gV}`. -/
noncomputable def partitionFnDeriv (a mass : ℝ) (ha : 0 < a)
    (hmass : 0 < mass) (P : InteractionPolynomial) (g : ℝ) : ℝ :=
  -∫ ω, interactionFunctional d N P a mass ω *
    Real.exp (-(g * interactionFunctional d N P a mass ω))
    ∂(latticeGaussianMeasure d N a mass ha hmass)

/-- `Z''(g) = ∫ V² e^{-gV}`. -/
noncomputable def partitionFnDeriv2 (a mass : ℝ) (ha : 0 < a)
    (hmass : 0 < mass) (P : InteractionPolynomial) (g : ℝ) : ℝ :=
  ∫ ω, (interactionFunctional d N P a mass ω) ^ 2 *
    Real.exp (-(g * interactionFunctional d N P a mass ω))
    ∂(latticeGaussianMeasure d N a mass ha hmass)

/-- Normalised moment `m_n(g) = M_n(g)/Z(g) = ⟨(ωf)ⁿ⟩_g`. -/
noncomputable def normalizedMoment (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (n : ℕ) (g : ℝ) : ℝ :=
  gibbsMoment d N a mass ha hmass P f n g / partitionFn d N a mass ha hmass P g

/-- Closed-form `m_n'(g)` (quotient rule). -/
noncomputable def normalizedMomentDeriv (a mass : ℝ) (ha : 0 < a)
    (hmass : 0 < mass) (P : InteractionPolynomial) (f : FinLatticeField d N)
    (n : ℕ) (g : ℝ) : ℝ :=
  (momentDeriv d N a mass ha hmass P f n g * partitionFn d N a mass ha hmass P g -
      gibbsMoment d N a mass ha hmass P f n g *
        partitionFnDeriv d N a mass ha hmass P g) /
    (partitionFn d N a mass ha hmass P g) ^ 2

/-- Closed-form `m_n''(g)` (second quotient-rule derivative). -/
noncomputable def normalizedMomentDeriv2 (a mass : ℝ) (ha : 0 < a)
    (hmass : 0 < mass) (P : InteractionPolynomial) (f : FinLatticeField d N)
    (n : ℕ) (g : ℝ) : ℝ :=
  (((momentDeriv2 d N a mass ha hmass P f n g *
          partitionFn d N a mass ha hmass P g +
        momentDeriv d N a mass ha hmass P f n g *
          partitionFnDeriv d N a mass ha hmass P g) -
      (momentDeriv d N a mass ha hmass P f n g *
          partitionFnDeriv d N a mass ha hmass P g +
        gibbsMoment d N a mass ha hmass P f n g *
          partitionFnDeriv2 d N a mass ha hmass P g)) *
      (partitionFn d N a mass ha hmass P g) ^ 2 -
    (momentDeriv d N a mass ha hmass P f n g *
        partitionFn d N a mass ha hmass P g -
      gibbsMoment d N a mass ha hmass P f n g *
        partitionFnDeriv d N a mass ha hmass P g) *
      (2 * (partitionFn d N a mass ha hmass P g) ^ (2 - 1) *
        partitionFnDeriv d N a mass ha hmass P g)) /
    ((partitionFn d N a mass ha hmass P g) ^ 2) ^ 2

/-- The Gibbs-family connected four-point `u₄(g) = m₄(g) − 3 m₂(g)²`. -/
noncomputable def u4 (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (g : ℝ) : ℝ :=
  normalizedMoment d N a mass ha hmass P f 4 g -
    3 * (normalizedMoment d N a mass ha hmass P f 2 g) ^ 2

/-- Closed-form `u₄'(g) = m₄'(g) − 6 m₂(g) m₂'(g)`. -/
noncomputable def u4Deriv (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (g : ℝ) : ℝ :=
  normalizedMomentDeriv d N a mass ha hmass P f 4 g -
    6 * (normalizedMoment d N a mass ha hmass P f 2 g *
      normalizedMomentDeriv d N a mass ha hmass P f 2 g)

/-- Closed-form `u₄''(g) = m₄''(g) − 6 (m₂'(g)² + m₂(g) m₂''(g))`. -/
noncomputable def u4Deriv2 (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (g : ℝ) : ℝ :=
  normalizedMomentDeriv2 d N a mass ha hmass P f 4 g -
    6 * (normalizedMomentDeriv d N a mass ha hmass P f 2 g *
        normalizedMomentDeriv d N a mass ha hmass P f 2 g +
      normalizedMoment d N a mass ha hmass P f 2 g *
        normalizedMomentDeriv2 d N a mass ha hmass P f 2 g)

/-- `m_n` has the closed-form derivative `normalizedMomentDeriv` at interior `t > 0`. -/
theorem normalizedMoment_hasDerivAt_explicit (a mass : ℝ) (ha : 0 < a)
    (hmass : 0 < mass) (P : InteractionPolynomial) (f : FinLatticeField d N)
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (normalizedMoment d N a mass ha hmass P f n)
      (normalizedMomentDeriv d N a mass ha hmass P f n t) t := by
  simpa [normalizedMoment, gibbsMoment, partitionFn, normalizedMomentDeriv,
    momentDeriv, partitionFnDeriv] using
    (normalizedMoment_hasDerivAt d N a mass ha hmass P f n ht)

/-- `m_n'` (the closed-form first derivative) is itself differentiable at interior `t`, with the
explicit second derivative `normalizedMomentDeriv2` — the `C²` step. -/
theorem normalizedMomentDeriv_hasDerivAt (a mass : ℝ) (ha : 0 < a)
    (hmass : 0 < mass) (P : InteractionPolynomial) (f : FinLatticeField d N)
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (normalizedMomentDeriv d N a mass ha hmass P f n)
      (normalizedMomentDeriv2 d N a mass ha hmass P f n t) t := by
  have hZne : partitionFn d N a mass ha hmass P t ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (partitionFn_ge_one d N P a mass ha hmass ht.le)).ne'
  have hZ2ne : (partitionFn d N a mass ha hmass P t) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hZne
  have hM := moment_hasDerivAt d N a mass ha hmass P f n ht
  have hMd := moment_hasDerivAt2 d N a mass ha hmass P f n ht
  have hZ := partitionFn_hasDerivAt d N a mass ha hmass P ht
  have hZd := partitionFn_hasDerivAt2 d N a mass ha hmass P ht
  have hnum := (hMd.mul hZ).sub (hM.mul hZd)
  have hden := hZ.pow 2
  simpa [gibbsMoment, partitionFn, momentDeriv, momentDeriv2, partitionFnDeriv,
    partitionFnDeriv2, normalizedMomentDeriv, normalizedMomentDeriv2] using
    hnum.div hden (by simpa [partitionFn] using hZ2ne)

/-- **L5a — closed-form `u₄'(t)`.** `HasDerivAt u₄ (u4Deriv t) t` at interior `t > 0`, with
`u4Deriv t = m₄'(t) − 6 m₂(t) m₂'(t)`. -/
theorem u4_hasDerivAt (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (u4 d N a mass ha hmass P f)
      (u4Deriv d N a mass ha hmass P f t) t := by
  have h4 := normalizedMoment_hasDerivAt_explicit d N a mass ha hmass P f 4 ht
  have h2 := normalizedMoment_hasDerivAt_explicit d N a mass ha hmass P f 2 ht
  have h := h4.sub ((h2.pow 2).const_mul (3 : ℝ))
  convert h using 1
  · simp [u4Deriv]
    ring

/-- **L5b — closed-form `u₄''(t)`.** `u₄'` is differentiable at interior `t > 0` with
`HasDerivAt u4Deriv (u4Deriv2 t) t`, where `u4Deriv2 t = m₄''(t) − 6 (m₂'(t)² + m₂(t) m₂''(t))`.
This is the `C²` structure the affine bound `u₄'(t) ≤ -s + K·t` needs. -/
theorem u4_hasDerivAt2 (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun g => u4Deriv d N a mass ha hmass P f g)
      (u4Deriv2 d N a mass ha hmass P f t) t := by
  have h4 := normalizedMomentDeriv_hasDerivAt d N a mass ha hmass P f 4 ht
  have hm2 := normalizedMoment_hasDerivAt_explicit d N a mass ha hmass P f 2 ht
  have hd2 := normalizedMomentDeriv_hasDerivAt d N a mass ha hmass P f 2 ht
  have h := h4.sub ((hm2.mul hd2).const_mul (6 : ℝ))
  simpa [u4Deriv, u4Deriv2] using h

end Pphi2
