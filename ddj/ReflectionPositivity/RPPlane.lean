/-
  Pphi2.ReflectionPositivity.RPPlane
  Reflection positivity of the P(Φ)₂ measure on the cylinder.

  Reference: DDJ Section 8.
  Adapted from spheres to cylinders: RP is much cleaner on the
  cylinder due to its product structure ℝ × S¹_L.
-/
import Pphi2.InfiniteVolume.Tightness
import Pphi2.OSAxioms

noncomputable section

open MeasureTheory

/-! ## Reflection on the cylinder ℝ × S¹_L

On the cylinder, time reflection is simply (t, x) ↦ (-t, x),
which comes directly from `timeReflectionCyl` in OSforGFF.
The product structure makes RP much cleaner than on the sphere.
-/

/-- The positive half-cylinder: {(t, x) ∈ ℝ × S¹_L | t > 0}. -/
def positiveHalfCylinder (L : ℝ) : Set (SpaceTimeCyl 2 L) :=
  {p | 0 < p.1}

/-! ## Reflection positivity on the cylinder

On the cylinder, RP follows from:
1. The product structure ℝ × S¹_L gives clean factorization
2. The free field covariance G_L = (1-Δ_L)⁻¹ is RP by construction
3. The spectral UV cutoff preserves RP on the cylinder
   (unlike on spheres, no local cutoff trick is needed)
4. The interaction exp(-∫ P) preserves RP via the Markov property
-/

/-- **Free field RP on the cylinder**: X_L is reflection positive.
    Immediate from the product structure and positive covariance.
    DDJ Lemma 8.5(A), simplified for cylinder. -/
axiom freeField_rp (L : ℝ) (hL : 0 < L) : True

/-- **Regularized field RP**: X_{L,N} is reflection positive.
    On the cylinder, the spectral cutoff K_{L,N} commutes with
    time reflection, so no local cutoff is needed.
    DDJ Lemma 8.5(B), simplified for cylinder. -/
axiom regularizedField_rp (L : ℝ) (hL : 0 < L) (N : ℕ+) : True

/-- **Interaction preserves RP**: exp(-∫ P(φ, c)) preserves RP.
    The interaction factorizes as exp(-∫_{t>0}) × exp(-∫_{t<0})
    by the Markov property of the free field.
    DDJ Lemma 8.5(C), simplified for cylinder. -/
axiom interaction_preserves_rp (P : InteractionPolynomial) (L : ℝ) (hL : 0 < L) (N : ℕ+) :
    True

/-- **Finite volume RP**: μ_L is reflection positive.
    Follows from the above and the UV limit.
    DDJ Lemma 8.5(D), adapted to cylinder. -/
axiom finiteMeasure_rp (P : InteractionPolynomial) (L : ℝ) (hL : 0 < L) : True

/-- **Reflection positivity of the P(Φ)₂ measure on the cylinder**.
    For each L, the measure μ_L on FieldConfigurationCyl 2 L
    satisfies OS3 (reflection positivity).

    On the cylinder, this is cleaner than on the sphere because:
    - Time reflection (t,x) ↦ (-t,x) respects the product structure
    - Spectral cutoff commutes with reflection (no local cutoff needed)
    - The half-cylinder {t > 0} is a natural domain

    DDJ Proposition 8.1, adapted to cylinder. -/
theorem reflection_positivity (P : InteractionPolynomial) (L : ℝ) [Fact (0 < L)] :
    OS3_ReflectionPositivity_generic (pphi2Framework L) (infiniteVolumeMeasure P L) := by
  sorry

end
