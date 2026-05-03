/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder Pullback Second-Moment Identities

Bridge lemmas relating the cylinder-pullback second moment to the torus
second moment of the embedded test function. The uniform-in-`Lt` second
moment **bound** lives in `Pphi2.IRLimit.UniformExponentialMoment` (it is
derived there from `cylinderIR_uniform_exponential_moment`).

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
  have hmeas : Measurable (cylinderPullback Lt Ls) :=
    configuration_measurable_of_eval_measurable _
      (fun φ => configuration_eval_measurable _)
  change ∫ ω, (ω f) ^ 2 ∂(Measure.map (cylinderPullback Lt Ls) μ) = _
  rw [integral_map hmeas.aemeasurable
    ((configuration_eval_measurable f).pow_const 2 |>.aestronglyMeasurable)]
  congr 1

/-- **Cutoff-level density transfer** for cylinder pullbacks.

This is the proved finite-cutoff step behind the IR second-moment argument:
the pullback second moment is controlled by the corresponding lattice Gaussian
second moment of the embedded test function. -/
theorem cylinderPullback_second_moment_density_transfer_cutoff
    (Lt : ℝ) [Fact (0 < Lt)] (P : InteractionPolynomial) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (f : CylinderTestFunction Ls),
    ∫ ω : Configuration (CylinderTestFunction Ls),
      (ω f) ^ 2 ∂(cylinderPullbackMeasure Lt Ls
        (asymTorusInteractingMeasure Lt Ls N P mass hmass)) ≤
    C * ∫ ω : Configuration (FinLatticeField 2 N),
      (ω (asymLatticeTestFn Lt Ls N (cylinderToTorusEmbed Lt Ls f))) ^ 2
        ∂(latticeGaussianMeasure 2 N (asymGeomSpacing Lt Ls N) mass
          (asymGeomSpacing_pos Lt Ls N) hmass) := by
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    asymTorus_interacting_second_moment_density_transfer Lt Ls P mass hmass
  refine ⟨C, hC_pos, fun N _ f => ?_⟩
  haveI : IsProbabilityMeasure
      (asymTorusInteractingMeasure Lt Ls N P mass hmass) :=
    asymTorusInteractingMeasure_isProbability Lt Ls N P mass hmass
  rw [cylinderPullback_second_moment_eq Ls Lt
    (asymTorusInteractingMeasure Lt Ls N P mass hmass) f]
  exact hC_bound (cylinderToTorusEmbed Lt Ls f) N

end Pphi2
