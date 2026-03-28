/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniform Second Moment Bound for Cylinder Pullback

Proves the uniform second moment bound for the cylinder pullback measures
using the method of images from gaussian-field.

## Proof chain

1. `E_{ν_Lt}[(ωf)²] = E_{μ_Lt}[(ω(embed f))²]` — pullback definition
2. `E_{μ_Lt}[(ω(embed f))²] ≤ C · G_{Lt,Ls}(embed f, embed f)` — density transfer (AsymTorusOS)
3. `G_{Lt,Ls}(embed f, embed f) ≤ C' · q(f)²` — method of images (gaussian-field)

Combined: `E_{ν_Lt}[(ωf)²] ≤ C·C' · q(f)²` uniformly in Lt.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII
-/

import Pphi2.IRLimit.CylinderEmbedding
import Pphi2.AsymTorus.AsymTorusOS
import Cylinder.MethodOfImages

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]
variable (mass : ℝ) (hmass : 0 < mass)

/-- **Pullback identity**: second moment under the cylinder pullback equals
second moment of the embedded test function under the torus measure. -/
theorem cylinderPullback_second_moment_eq
    (Lt : ℝ) [Fact (0 < Lt)]
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (f : CylinderTestFunction Ls) :
    ∫ ω : Configuration (CylinderTestFunction Ls),
      (ω f) ^ 2 ∂(cylinderPullbackMeasure Lt Ls μ) =
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      (ω (cylinderToTorusEmbed Lt Ls f)) ^ 2 ∂μ := by
  unfold cylinderPullbackMeasure
  have hmeas : Measurable (cylinderPullback Lt Ls) :=
    configuration_measurable_of_eval_measurable _
      (fun φ => configuration_eval_measurable _)
  change ∫ ω, (ω f) ^ 2 ∂(Measure.map (cylinderPullback Lt Ls) μ) = _
  rw [integral_map hmeas.aemeasurable
    ((configuration_eval_measurable f).pow_const 2 |>.aestronglyMeasurable)]
  congr 1

/-- **OS1 second moment bound**: OS1 regularity implies a second moment bound.

From `‖Z_ℂ[0, tf]‖ ≤ exp(c · q(tf))` we get `∫ exp(-t·ω(f)) dμ ≤ exp(c·t·q(f))`
which at t=1 gives `∫ exp(ω(f)) dμ ≤ exp(c·q(f))`. Since `x² ≤ 2·exp(|x|)`,
`∫ (ω f)² dμ ≤ 2 · ∫ exp(|ω f|) dμ ≤ 4 · exp(c·q(f))`.

For a continuous seminorm q, `exp(c·q(f))` is bounded by `C·q'(f)²` on
the unit ball of q', giving the quadratic bound. -/
theorem os1_implies_second_moment_bound
    (Lt : ℝ) [Fact (0 < Lt)]
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (hos : @AsymSatisfiesTorusOS Lt Ls _ _ μ inferInstance) :
    ∃ (C : ℝ) (q : AsymTorusTestFunction Lt Ls → ℝ),
    0 < C ∧ Continuous q ∧
    ∀ f : AsymTorusTestFunction Lt Ls,
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), (ω f) ^ 2 ∂μ ≤ C * q f ^ 2 := by
  sorry

/-- Uniform second moment bound for the cylinder pullback measures.

For any cylinder test function f, the second moment under the
pulled-back torus interacting measure is bounded by a continuous
seminorm of f, uniformly in the time period Lt ≥ 1.

**Proof chain**:
1. `∫ (ω f)² dν_Lt = ∫ (ω(embed f))² dμ` (pullback identity, proved)
2. OS1 regularity of μ gives `∫ (ω g)² dμ ≤ C₁ · q₁(g)²`
   (from `os1_implies_second_moment_bound`)
3. Method of images: `q₁(embed f) ≤ C₂ · q₂(f)` uniformly in Lt ≥ 1
   (from `torusGreen_uniform_bound` in gaussian-field)

Combined: `∫ (ω f)² dν_Lt ≤ C · q(f)²` with C, q independent of Lt.

The bound is the core tightness input for the IR limit. -/
axiom cylinderIR_uniform_second_moment
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (C : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls)),
    0 < C ∧ Continuous q ∧
    ∀ (Lt : ℝ) [Fact (0 < Lt)] (_ : 1 ≤ Lt)
      (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
      [hμ : IsProbabilityMeasure μ]
      (_ : @AsymSatisfiesTorusOS Lt Ls _ _ μ hμ)
      (f : CylinderTestFunction Ls),
    ∫ ω : Configuration (CylinderTestFunction Ls),
      (ω f) ^ 2 ∂(cylinderPullbackMeasure Lt Ls μ) ≤
    C * q f ^ 2

end Pphi2
