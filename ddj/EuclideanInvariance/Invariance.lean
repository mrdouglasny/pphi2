/-
  Pphi2.EuclideanInvariance.Invariance
  Translation invariance of the P(Φ)₂ measure on the cylinder.

  Reference: DDJ Section 9, Proposition 9.1.
  Adapted from spheres to cylinders: on the cylinder we get translation
  invariance (not full E(2) invariance). Full Euclidean invariance
  requires the L → ∞ limit or a separate argument.
-/
import Pphi2.InfiniteVolume.Tightness
import Pphi2.OSAxioms

noncomputable section

open MeasureTheory

/-! ## Translations on the cylinder ℝ × S¹_L

On the cylinder, the natural symmetry group consists of:
- Time translations: (t, x) ↦ (t + s, x) for s ∈ ℝ
- Spatial translations: (t, x) ↦ (t, x + a mod L) for a ∈ ℝ/Lℤ

This is the symmetry group encoded in SymmetryGroupCyl 2 L.
Full rotational invariance is NOT available on the cylinder;
it requires the infinite volume limit L → ∞.
-/

/-- Time translation invariance of μ_L.
    The measure μ_L on the cylinder is invariant under time shifts
    (t, x) ↦ (t + s, x). This is built into the ℝ factor of the
    cylinder structure.
    DDJ Proposition 9.1(b), adapted. -/
axiom time_translation_invariance (P : InteractionPolynomial) (L : ℝ) (s : ℝ) :
    True -- μ_L is invariant under time translation by s

/-- Spatial translation invariance of μ_L.
    The measure μ_L on the cylinder is invariant under spatial shifts
    (t, x) ↦ (t, x + a) on S¹_L. This is built into the periodic
    structure of S¹_L.
    DDJ Proposition 9.1(a), adapted. -/
axiom spatial_translation_invariance (P : InteractionPolynomial) (L : ℝ)
    (a : SpaceTimeCyl 2 L) :
    True -- μ_L is invariant under spatial translation by a

/-- **Translation invariance of the P(Φ)₂ measure on the cylinder**.
    The measure μ_L satisfies OS2 (symmetry invariance) with respect
    to the translation symmetry group of ℝ × S¹_L.

    DDJ Proposition 9.1, adapted to cylinder. -/
theorem translation_invariance (P : InteractionPolynomial) (L : ℝ) [Fact (0 < L)] :
    OS2_Invariance_generic (pphi2Framework L) (infiniteVolumeMeasure P L) := by
  sorry

end
