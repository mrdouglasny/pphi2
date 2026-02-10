/-
  Pphi2.MeasureCylinder.Regularized
  The regularized P(Φ)₂ measure μ_{L,N} on the cylinder ℝ × S¹_L.

  Reference: DDJ Section 2, Eqs. (2.2)-(2.5).
  Adapted from spheres S_R to cylinders ℝ × S¹_L.
-/
import Pphi2.GaussianCylinder.Covariance

noncomputable section

open MeasureTheory

/-! ## The regularized measure μ_{L,N} -/

/-- The regularized P(Φ)₂ measure on FieldConfigurationTorus 2 L:
    μ_{L,N}(dφ) = (1/Z) exp(-∫ P(φ(x), c_{L,N}) dx) ν_{L,N}(dφ).
    DDJ Eq. (2.2), adapted to cylinder. -/
axiom regularizedMeasure (P : InteractionPolynomial) (L : ℝ) (N : ℕ+) :
  ProbabilityMeasure (FieldConfigurationTorus 2 L)

/-- The auxiliary measure μ^g_{L,N} with extra factor exp(φ(g)ⁿ/n).
    μ^g_{L,N}(dφ) = (1/Z^g) exp(φ(g)ⁿ/n) μ_{L,N}(dφ).
    DDJ Eq. (2.5), adapted to cylinder. -/
axiom auxiliaryMeasure (P : InteractionPolynomial) (L : ℝ) (N : ℕ+)
    (g : TestFunctionTorus 2 L) :
  ProbabilityMeasure (FieldConfigurationTorus 2 L)

/-- μ_{L,N}^g is well-defined and concentrated on L²₁(ℝ × S¹_L).
    DDJ Lemma 2.1. -/
axiom auxiliaryMeasure_wellDefined (P : InteractionPolynomial) (L : ℝ) (N : ℕ+)
    (g : TestFunctionTorus 2 L) :
    True -- well-definedness conditions

/-- μ_{L,N} is invariant under translations of the cylinder
    (time shifts along ℝ, spatial shifts mod L on S¹_L). -/
axiom regularizedMeasure_translation_invariant (P : InteractionPolynomial) (L : ℝ)
    (N : ℕ+) :
    True -- precise statement requires group action on measures

end
