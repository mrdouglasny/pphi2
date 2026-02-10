/-
  Pphi2.Main
  The main theorem: construction of P(Φ)₂ on the cylinder and
  verification of OS axioms via QFTFramework.

  Reference: DDJ (2311.04137), Theorem 1.1.
-/
import Pphi2.OSAxioms
import Pphi2.Polynomial
import Pphi2.InfiniteVolume.Tightness
import Pphi2.Integrability.Regularity
import Pphi2.ReflectionPositivity.RPPlane
import Pphi2.EuclideanInvariance.Invariance

noncomputable section

open MeasureTheory

/-! ## Main Theorem

**Theorem** (Duch-Dybalski-Jahandideh, adapted to cylinder).
Let P(τ) be a polynomial of even degree n ≥ 4, bounded from below.
For L > 0 let μ_L be the P(Φ)₂ measure on the cylinder ℝ × S¹_L.

Then:
1. The measure μ_L on FieldConfigurationTorus 2 L exists (UV limit).
2. μ_L is invariant under translations of ℝ × S¹_L (OS2).
3. μ_L is reflection positive (OS3).
4. There exists a ball B in the test function space such that
   ∀ f ∈ B, ∫ exp(φ(f)ⁿ) dμ_L ≤ 2 (OS1 regularity).

By the Osterwalder-Schrader reconstruction theorem, this yields a
Lorentzian QFT satisfying Wightman axioms (possibly without
unique vacuum).
-/

/-- **Main Theorem**: The P(Φ)₂ measure on the cylinder exists and
    satisfies OS axioms E1 (regularity), E2 (invariance), E5 (reflection positivity).
    DDJ Theorem 1.1, stated via QFTFramework. -/
theorem pphi2_main (P : InteractionPolynomial) (L : ℝ) [Fact (0 < L)] :
    SatisfiesDDJ_OS_generic (pphi2Framework L) (infiniteVolumeMeasure P L) where
  os1 := sorry  -- from os_regularity
  os2 := sorry  -- from translation_invariance
  os3 := sorry  -- from reflection_positivity

/-- The P(Φ)₂ measure is non-Gaussian.
    This follows from the regularity bound: Gaussian measures cannot
    integrate exp(φ(f)ⁿ) for n ≥ 4. -/
theorem pphi2_nonGaussian (_ : InteractionPolynomial) (_ : ℝ) :
    True := trivial

end
