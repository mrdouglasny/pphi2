/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.UniformBounds

/-!
# Interior differentiability of the Gibbs-family `u₄` (uniform-discharge leaf `hderiv`)

The two-sided, general-interior-`t` companions of the `g=0` derivative theorems, providing the
`hderiv` hypothesis of `exists_uniform_neg_of_uniform_affine_bound'`:

* `partitionFn_hasDerivAt` — `d/dg ∫ e^{-gV} |_t = -∫ V e^{-tV}` (`t>0`).
* `u4_differentiableAt` — `DifferentiableAt ℝ u₄_N t` for `t>0`, hence (via `.hasDerivAt`)
  `HasDerivAt u₄_N (deriv u₄_N t) t`. Using `DifferentiableAt` (not a closed-form derivative) keeps
  the proof robust; the derivative *value* bound is the separate `s`/`K` work.

Built on `moment_hasDerivAt` (general `t`); `Z_t = ∫e^{-tV} > 0` from `partitionFn_ge_one`.
-/

namespace Pphi2

open MeasureTheory GaussianField Set

variable (d N : ℕ) [NeZero N]

/-- **Partition-function derivative at general `t>0` (two-sided).** -/
theorem partitionFn_hasDerivAt (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun g => ∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass))
      (-∫ ω, interactionFunctional d N P a mass ω *
        Real.exp (-(t * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass))
      t := by
  have h := moment_hasDerivAt d N a mass ha hmass P (0 : FinLatticeField d N) 0 ht
  convert h using 2 with g
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_); simp
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_); simp

/-- **`u₄_N` is differentiable at every interior `t>0`** — the `hderiv` leaf. Via `.hasDerivAt` this
gives `HasDerivAt u₄_N (deriv u₄_N t) t`, the form `exists_uniform_neg_of_uniform_affine_bound'`
consumes. -/
theorem u4_differentiableAt (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ
      (fun g =>
        (∫ ω, (ω f) ^ 4 * Real.exp (-(g * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass)) /
          (∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass))
        - 3 * ((∫ ω, (ω f) ^ 2 * Real.exp (-(g * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass)) /
          (∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass))) ^ 2) t := by
  have hZne : (∫ ω, Real.exp (-(t * interactionFunctional d N P a mass ω))
      ∂(latticeGaussianMeasure d N a mass ha hmass)) ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (partitionFn_ge_one d N P a mass ha hmass ht.le)).ne'
  have hZ := partitionFn_hasDerivAt d N a mass ha hmass P ht
  have hM4 : DifferentiableAt ℝ
      (fun g => (∫ ω, (ω f) ^ 4 * Real.exp (-(g * interactionFunctional d N P a mass ω))
          ∂(latticeGaussianMeasure d N a mass ha hmass)) /
        (∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω))
          ∂(latticeGaussianMeasure d N a mass ha hmass))) t :=
    ((moment_hasDerivAt d N a mass ha hmass P f 4 ht).div hZ hZne).differentiableAt
  have hM2 : DifferentiableAt ℝ
      (fun g => (∫ ω, (ω f) ^ 2 * Real.exp (-(g * interactionFunctional d N P a mass ω))
          ∂(latticeGaussianMeasure d N a mass ha hmass)) /
        (∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω))
          ∂(latticeGaussianMeasure d N a mass ha hmass))) t :=
    ((moment_hasDerivAt d N a mass ha hmass P f 2 ht).div hZ hZne).differentiableAt
  exact hM4.sub ((hM2.pow 2).const_mul 3)

/-- **`hcont` leaf: `u₄_N` is continuous on `[0,g₀]`.** Interior continuity from `u4_differentiableAt`;
left-endpoint (`g=0`) continuity from the one-sided `u4_hasDerivWithinAt`. -/
theorem u4_continuousOn (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (hP : P.n = 4) (f : FinLatticeField d N) (g₀ : ℝ) :
    ContinuousOn
      (fun g =>
        (∫ ω, (ω f) ^ 4 * Real.exp (-(g * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass)) /
          (∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass))
        - 3 * ((∫ ω, (ω f) ^ 2 * Real.exp (-(g * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass)) /
          (∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass))) ^ 2)
      (Set.Icc 0 g₀) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hx0 | hxpos
  · subst hx0
    exact (u4_hasDerivWithinAt d N a mass ha hmass P hP f).continuousWithinAt.mono
      Set.Icc_subset_Ici_self
  · exact (u4_differentiableAt d N a mass ha hmass P f hxpos).continuousAt.continuousWithinAt

end Pphi2
