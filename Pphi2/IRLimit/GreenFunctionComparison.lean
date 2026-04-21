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

/-- Uniform second moment bound for the cylinder pullback measures.

For any cylinder test function f, the second moment under the
pulled-back torus interacting measure is bounded by a continuous
seminorm of f, uniformly in the time period Lt ≥ 1.

**Proof chain**:
1. `∫ (ω f)² dν_Lt = ∫ (ω(embed f))² dμ` (pullback identity, proved above)
2. At fixed cutoff, the interacting measure's second moment is bounded quadratically:
   `∫ (ω g)² dμ_int ≤ C₁ · G_{Lt,Ls}(g, g)` (density transfer via
   Cauchy-Schwarz: `E_int[X²] ≤ (1/Z)·E_GFF[X⁴]^{1/2}·E_GFF[e^{-2V}]^{1/2}`
   with X⁴ bounded by hypercontractivity and e^{-2V} by Nelson's estimate)
3. `G_{Lt,Ls}(embed f, embed f) ≤ C₂ · q(f)²` uniformly in Lt ≥ 1
   (from `torusGreen_uniform_bound` in gaussian-field)

Combined: `∫ (ω f)² dν_Lt ≤ C · q(f)²` with C, q independent of Lt.

NOTE: The quadratic bound requires the specific interacting measure structure
(Nelson estimate + Gaussian hypercontractivity + density transfer), not just
abstract OS axioms. The cutoff-level density-transfer step is proved above; the
remaining axiom packages the passage to the torus UV limit together with the
genuinely new uniform-in-`Lt` cylinder seminorm control.

**Structural gap** (blocker for the proof): like
`cylinderIR_uniform_exponential_moment`, this axiom would be derivable by
differentiating the OS1 CF bound (Cauchy bound on 2nd derivative at `t=0`)
if `AsymSatisfiesTorusOS.os1` guaranteed its continuous bound `q_torus`
satisfied `q_torus(g) ≤ C' · G_torus_Lt(g, g)`. The current abstract OS1
does not. `AsymSatisfiesTorusOS` must be extended with a `G_torus`-compatible
OS1 clause before this axiom can be discharged; that refactor is scheduled
separately. -/
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
