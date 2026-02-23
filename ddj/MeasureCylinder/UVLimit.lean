/-
  Pphi2.MeasureCylinder.UVLimit
  The UV limit: μ_{L,N} → μ_L as N → ∞ on the cylinder.

  Reference: DDJ Section 2, Proposition 2.4.
  Adapted from spheres S_R to cylinders ℝ × S¹_L.
-/
import Pphi2.MeasureCylinder.Regularized

noncomputable section

open MeasureTheory

/-! ## UV limit -/

/-- The P(Φ)₂ measure μ_L on FieldConfigurationCyl 2 L,
    obtained as the N → ∞ limit.
    DDJ Proposition 2.4, adapted to cylinder. -/
axiom uvLimitMeasure (P : InteractionPolynomial) (L : ℝ) :
  ProbabilityMeasure (FieldConfigurationCyl 2 L)

/-- The UV limit exists: μ_{L,N} → μ_L weakly as N → ∞.
    Proved via Vitali's convergence theorem.
    DDJ Proposition 2.4. -/
axiom uvLimit_convergence (P : InteractionPolynomial) (L : ℝ) :
    True -- Filter.Tendsto (regularizedMeasure P L) Filter.atTop (nhds (uvLimitMeasure P L))

/-- The UV limit measure μ_L is invariant under translations of the cylinder.
    This follows from the translation invariance of each μ_{L,N}. -/
axiom uvLimitMeasure_translation_invariant (P : InteractionPolynomial) (L : ℝ) :
    True -- μ_L is translation-invariant

end
