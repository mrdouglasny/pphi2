/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.General

/-!
# Field redefinition for the general interacting measure

The Gibbs construction `interactingMeasure V μ = Z⁻¹ · μ.withDensity(exp(−V))` is **covariant**
under a measurable field redefinition `S` (a measurable equivalence of configuration space):
pushing it forward by `S` gives the interacting measure with the **transformed potential** `V ∘ S⁻¹`
over the **transformed free measure** `S_* μ`, with the **same partition function** (change of
variables). This is the abstract core of the "field redefinition theorem"; specializing `S` to a
field scaling `ω ↦ c • ω` (where the free GFF covariance scales by `c²` and a quartic coupling by
`c⁴`) translates between different `(mass, coupling)` parametrisations — see
`planning/lambda-coupling-family-plan.md`. The broad coupling-parameterised class is
`interactingMeasure (λ • V) μ`; the implemented fixed-coupling theory is the `λ = 1` case.

## Main result
* `interactingMeasure_map_measurableEquiv` —
  `S_* (interactingMeasure V μ) = interactingMeasure (V ∘ S.symm) (S_* μ)`.
-/

open GaussianField MeasureTheory

noncomputable section

namespace Pphi2

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- **Partition function is invariant under a field redefinition.** `Z[V ∘ S⁻¹, S_* μ] = Z[V, μ]`
by change of variables (`S.symm ∘ S = id`). -/
theorem interactingPartitionFunction_map_measurableEquiv
    (S : Configuration E ≃ᵐ Configuration E) (V : Configuration E → ℝ)
    (μ : Measure (Configuration E)) (hV_meas : Measurable V) :
    interactingPartitionFunction (V ∘ S.symm) (Measure.map S μ)
      = interactingPartitionFunction V μ := by
  have hfm : AEStronglyMeasurable (interactingBoltzmannWeight (V ∘ ⇑S.symm)) (Measure.map S μ) :=
    ((hV_meas.comp S.symm.measurable).neg.exp).aestronglyMeasurable
  unfold interactingPartitionFunction
  rw [integral_map S.measurable.aemeasurable hfm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [interactingBoltzmannWeight, Function.comp_apply, S.symm_apply_apply]

/-- **Field redefinition covariance of the interacting measure.** For a measurable equivalence `S`
of configuration space, `S_* (interactingMeasure V μ) = interactingMeasure (V ∘ S⁻¹) (S_* μ)`. The
Gibbs construction commutes with the change of variables; the partition function is preserved. -/
theorem interactingMeasure_map_measurableEquiv
    (S : Configuration E ≃ᵐ Configuration E) (V : Configuration E → ℝ)
    (μ : Measure (Configuration E)) (hV_meas : Measurable V) :
    Measure.map S (interactingMeasure V μ) = interactingMeasure (V ∘ S.symm) (Measure.map S μ) := by
  have hg'_meas : Measurable (fun ω => ENNReal.ofReal (interactingBoltzmannWeight (V ∘ ⇑S.symm) ω)) :=
    interactingBoltzmannWeight_ennreal_measurable (V ∘ S.symm) (hV_meas.comp S.symm.measurable)
  unfold interactingMeasure
  rw [Measure.map_smul,
    interactingPartitionFunction_map_measurableEquiv S V μ hV_meas]
  congr 1
  -- `S_* (μ.withDensity g) = (S_* μ).withDensity (g ∘ S⁻¹)`
  ext A hA
  rw [Measure.map_apply S.measurable hA,
    withDensity_apply _ (S.measurable hA), withDensity_apply _ hA,
    setLIntegral_map hA hg'_meas S.measurable]
  refine lintegral_congr fun ω => ?_
  simp only [interactingBoltzmannWeight, Function.comp_apply, S.symm_apply_apply]

end Pphi2

end
