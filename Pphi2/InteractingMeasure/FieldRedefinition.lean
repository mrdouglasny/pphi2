/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.General
import GaussianField.Properties
import GaussianField.Hypercontractive

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

/-! ## Field-scaling map and the moment-level field redefinition

The full `Configuration`-measure identity `map (c•·) (GaussianField.measure T) = measure (c•T)`
needs Cramér–Wold/Minlos uniqueness on the infinite-dimensional `Configuration` (only available
post-pushforward-to-ℝ); it is deferred (possibly to be added as an axiom). What `u₄` actually
consumes — the **moment / connected-four-point scaling** — is provable directly here. -/

/-- The field rescaling `ω ↦ c • ω` is measurable (each evaluation `(c•ω) φ = c · ω φ`). -/
theorem measurable_configuration_const_smul (c : ℝ) :
    Measurable (fun ω : Configuration E => c • ω) := by
  apply configuration_measurable_of_eval_measurable
  intro φ
  show Measurable (fun ω : Configuration E => c * ω φ)
  exact measurable_const.mul (configuration_eval_measurable φ)

/-- The field rescaling as a measurable equivalence (`c ≠ 0`), inverse `ω ↦ c⁻¹ • ω`. -/
def fieldRescaleEquiv (c : ℝ) (hc : c ≠ 0) : Configuration E ≃ᵐ Configuration E where
  toFun := fun ω => c • ω
  invFun := fun ω => c⁻¹ • ω
  left_inv := fun ω => by show c⁻¹ • (c • ω) = ω; rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  right_inv := fun ω => by show c • (c⁻¹ • ω) = ω; rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
  measurable_toFun := measurable_configuration_const_smul c
  measurable_invFun := measurable_configuration_const_smul c⁻¹

@[simp] theorem fieldRescaleEquiv_apply (c : ℝ) (hc : c ≠ 0) (ω : Configuration E) :
    fieldRescaleEquiv c hc ω = c • ω := rfl

@[simp] theorem fieldRescaleEquiv_symm_apply (c : ℝ) (hc : c ≠ 0) (ω : Configuration E) :
    (fieldRescaleEquiv c hc).symm ω = c⁻¹ • ω := rfl

/-- **Moment scaling under field rescaling.** `∫ (ωf)ⁿ d((c•·)_* μ) = cⁿ · ∫ (ωf)ⁿ dμ`. -/
theorem integral_pow_map_const_smul (c : ℝ) (μ : Measure (Configuration E)) (f : E) (n : ℕ) :
    ∫ ω, (ω f) ^ n ∂(Measure.map (fun ω => c • ω) μ) = c ^ n * ∫ ω, (ω f) ^ n ∂μ := by
  rw [integral_map (measurable_configuration_const_smul c).aemeasurable
    ((configuration_eval_measurable f).pow_const n).aestronglyMeasurable]
  simp_rw [show ∀ ω : Configuration E, (c • ω) f = c * ω f from fun _ => rfl, mul_pow]
  rw [integral_const_mul]

/-- The (diagonal) connected four-point `u₄(f) = ∫(ωf)⁴ − 3(∫(ωf)²)²` of a configuration measure. -/
noncomputable def connectedFourPoint (μ : Measure (Configuration E)) (f : E) : ℝ :=
  (∫ ω, (ω f) ^ 4 ∂μ) - 3 * (∫ ω, (ω f) ^ 2 ∂μ) ^ 2

/-- **`u₄` scales by `c⁴` under field rescaling.** `u₄((c•·)_* μ; f) = c⁴ · u₄(μ; f)`. -/
theorem connectedFourPoint_map_const_smul (c : ℝ) (μ : Measure (Configuration E)) (f : E) :
    connectedFourPoint (Measure.map (fun ω => c • ω) μ) f = c ^ 4 * connectedFourPoint μ f := by
  unfold connectedFourPoint
  rw [integral_pow_map_const_smul c μ f 4, integral_pow_map_const_smul c μ f 2]
  ring

/-- **(A)+(C) at the moment level — the field-redefinition coupling translation.** Via the field
redefinition `ω ↦ c•ω` (`c ≠ 0`), the connected four-point of the interacting theory with potential
`V ∘ (c⁻¹•·)` over the rescaled free measure `(c•·)_* μ` equals `c⁴ ×` that of the original theory
`(V, μ)`. Specializing `V = λ • interactionFunctional` and `μ = GaussianField.measure T` (whose
rescaling `(c•·)_* μ` has covariance `c²` larger, i.e. a different mass), this is exactly the
`(m,λ) ↔ (m',λ')` translation: `u₄ ≠ 0` is preserved (up to the `c⁴` factor) along the redefinition,
so a strict `u₄ < 0` at one `(m,λ)` gives one at the translated parameters. -/
theorem connectedFourPoint_interactingMeasure_field_rescale
    (c : ℝ) (hc : c ≠ 0) (V : Configuration E → ℝ) (μ : Measure (Configuration E))
    (hV_meas : Measurable V) (f : E) :
    connectedFourPoint (interactingMeasure (V ∘ (fun ω => c⁻¹ • ω)) (Measure.map (fun ω => c • ω) μ)) f
      = c ^ 4 * connectedFourPoint (interactingMeasure V μ) f := by
  have hcore := interactingMeasure_map_measurableEquiv (fieldRescaleEquiv c hc) V μ hV_meas
  have h1 : (⇑(fieldRescaleEquiv c hc)) = (fun ω : Configuration E => c • ω) := rfl
  have h2 : (⇑(fieldRescaleEquiv c hc).symm) = (fun ω : Configuration E => c⁻¹ • ω) := rfl
  rw [h1, h2] at hcore
  rw [← hcore, connectedFourPoint_map_const_smul]

/-! ## Free-field baseline: `u₄ = 0` (the `g = 0` anchor of the perturbation) -/

section FreeBaseline
open ProbabilityTheory
variable [DyninMityaginSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- **The free field has vanishing connected four-point** (Isserlis / Wick). For the Gaussian field
`GaussianField.measure T`, `u₄(f) = ⟨φ(f)⁴⟩ − 3⟨φ(f)²⟩² = 0`: the 1D law of `ω ↦ ω f` is a centered
Gaussian (`pairing_is_gaussian`), whose moments satisfy `⟨X⁴⟩ = 3⟨X²⟩²`. This is the `g = 0` baseline
of the perturbative `u₄` expansion, and confirms the test classifies the free field as
**non-interacting** (so a `TorusIsInteracting`-style test cannot be satisfied by the free field). -/
theorem connectedFourPoint_gaussianMeasure_eq_zero (T : E →L[ℝ] H) (f : E) :
    connectedFourPoint (GaussianField.measure T) f = 0 := by
  have hlaw := GaussianField.pairing_is_gaussian (T := T) f
  have e4 : ∫ ω, (ω f) ^ 4 ∂(GaussianField.measure T)
      = ∫ x : ℝ, x ^ 4 ∂((GaussianField.measure T).map (fun ω : Configuration E => ω f)) :=
    (integral_map (GaussianField.configuration_eval_measurable f).aemeasurable
      ((continuous_pow 4).measurable.aestronglyMeasurable)).symm
  have e2 : ∫ ω, (ω f) ^ 2 ∂(GaussianField.measure T)
      = ∫ x : ℝ, x ^ 2 ∂((GaussianField.measure T).map (fun ω : Configuration E => ω f)) :=
    (integral_map (GaussianField.configuration_eval_measurable f).aemeasurable
      ((continuous_pow 2).measurable.aestronglyMeasurable)).symm
  have key : ∫ ω, (ω f) ^ 4 ∂(GaussianField.measure T)
      = 3 * (∫ ω, (ω f) ^ 2 ∂(GaussianField.measure T)) ^ 2 := by
    rw [e4, e2, hlaw, integral_pow4_gaussianReal, integral_sq_gaussianReal]
  simp only [connectedFourPoint, key]; ring

end FreeBaseline

end Pphi2

end
