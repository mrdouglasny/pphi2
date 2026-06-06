/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.MomentDerivative

/-!
# Connected-correlator derivative of the Gibbs family (u₄ step 2c, bricks 3–4)

* **Brick 3** — partition function derivative: `d/dg⁺ ∫ e^{-g V} |₀ = -∫ V` (the `n = 0` case of
  `moment_hasDerivWithinAt`), with `Z 0 = ∫ e^0 = 1`.
* **Brick 4** — the quotient rule for the normalised moment `⟨φ(f)ⁿ⟩_g = (∫ (ω f)ⁿ e^{-gV})/Z_g`:
  using `Z 0 = 1`, `d/dg⁺ ⟨φ(f)ⁿ⟩_g |₀ = -∫ (ω f)ⁿ V + (∫ (ω f)ⁿ)(∫ V) = -⟨(ω f)ⁿ ; V⟩^c`
  (the free connected/truncated correlator).
-/

namespace Pphi2

open MeasureTheory GaussianField Set

variable (d N : ℕ) [NeZero N]

/-- `Z 0 = ∫ e^{-0·V} dμ_GFF = 1` (the lattice GFF is a probability measure). -/
lemma partitionFn_zero (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (P : InteractionPolynomial) :
    (∫ ω, Real.exp (-(0 * interactionFunctional d N P a mass ω))
      ∂(latticeGaussianMeasure d N a mass ha hmass)) = 1 := by
  simp [integral_const, measure_univ]

/-- **Brick 3 — partition function derivative.** `d/dg⁺ ∫ e^{-g V} dμ_GFF |_{g=0} = -∫ V dμ_GFF`. -/
theorem partitionFn_hasDerivWithinAt (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) :
    HasDerivWithinAt
      (fun g => ∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass))
      (-∫ ω, interactionFunctional d N P a mass ω
        ∂(latticeGaussianMeasure d N a mass ha hmass))
      (Ici 0) 0 := by
  have h := moment_hasDerivWithinAt d N a mass ha hmass P (0 : FinLatticeField d N) 0
  convert h using 2 with g
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_); simp
  · refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_); simp

/-- **Brick 4 — connected-correlator derivative.** The normalised moment
`⟨φ(f)ⁿ⟩_g = (∫ (ω f)ⁿ e^{-gV})/(∫ e^{-gV})` has right-derivative at `g = 0` equal to
`-∫ (ω f)ⁿ V + (∫ (ω f)ⁿ)(∫ V)`, the free connected correlator `-⟨(ω f)ⁿ ; V⟩^c`. -/
theorem normalizedMoment_hasDerivWithinAt (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (n : ℕ) :
    HasDerivWithinAt
      (fun g => (∫ ω, (ω f) ^ n * Real.exp (-(g * interactionFunctional d N P a mass ω))
          ∂(latticeGaussianMeasure d N a mass ha hmass)) /
        (∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω))
          ∂(latticeGaussianMeasure d N a mass ha hmass)))
      (-(∫ ω, (ω f) ^ n * interactionFunctional d N P a mass ω
          ∂(latticeGaussianMeasure d N a mass ha hmass)) +
        (∫ ω, (ω f) ^ n ∂(latticeGaussianMeasure d N a mass ha hmass)) *
          (∫ ω, interactionFunctional d N P a mass ω
            ∂(latticeGaussianMeasure d N a mass ha hmass)))
      (Ici 0) 0 := by
  set μ := latticeGaussianMeasure d N a mass ha hmass
  set V := interactionFunctional d N P a mass
  have hnum := moment_hasDerivWithinAt d N a mass ha hmass P f n
  have hZ := partitionFn_hasDerivWithinAt d N a mass ha hmass P
  have hZ0 : (∫ ω, Real.exp (-(0 * V ω)) ∂μ) = 1 := partitionFn_zero d N a mass ha hmass P
  have hnum0 : (∫ ω, (ω f) ^ n * Real.exp (-(0 * V ω)) ∂μ) = ∫ ω, (ω f) ^ n ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_); simp
  have hdiv := hnum.div hZ (by rw [hZ0]; exact one_ne_zero)
  convert hdiv using 1
  rw [hZ0, hnum0]
  ring

end Pphi2
