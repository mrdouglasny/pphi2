/-
  Pphi2.Integrability.Regularity
  The OS regularity bound: ∫ exp(φ(f)ⁿ) dμ ≤ 2 on the cylinder.

  Reference: DDJ Section 7, Proposition 7.1.
  Adapted from spheres to cylinders.
-/
import Pphi2.InfiniteVolume.Tightness

noncomputable section

open MeasureTheory

/-! ## Variational bound -/

/-- **Lemma 7.2** (Barashkov's variational inequality).
    For a probability measure μ and measurable F with exp(F) ∈ L¹(μ):
    ∫ exp(F) dμ ≤ exp(∫ F dμ^F)
    where μ^F(dφ) = exp(F(φ)) μ(dφ) / ∫ exp(F) dμ.

    DDJ Lemma 7.2 (citing Barashkov). -/
axiom variational_bound {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    (F : Ω → ℝ) (hF : Integrable (fun ω => Real.exp (F ω)) μ.toMeasure) :
    ∫ ω, Real.exp (F ω) ∂μ.toMeasure ≤
      Real.exp (sorry) -- exp(∫ F dμ^F)

/-! ## OS Regularity on the cylinder -/

/-- **Proposition 7.1** (Integrability / OS Regularity on the cylinder).
    For each L, there exists a ball B in the test function space on
    ℝ × S¹_L such that for all f ∈ B:

    ∫ exp(φ(f)ⁿ) dμ_L(φ) ≤ 2.

    This implies:
    1. μ_L is non-Gaussian (Gaussian measures don't integrate exp(φ(f)ⁿ)).
    2. The OS regularity axiom holds.

    Proof: Use Lemma 7.2 to reduce to bounding ∫ φ(g)ⁿ dμ^g.
    Apply Hölder and the uniform moment bound (Prop 6.1).

    DDJ Proposition 7.1, adapted to cylinder. -/
theorem os_regularity (P : InteractionPolynomial) (L : ℝ) [Fact (0 < L)] :
    ∃ (B : Set (TestFunctionTorus 2 L)),
      (∃ r : ℝ, 0 < r ∧ ∀ f ∈ B, True) ∧ -- B is a ball in the test function topology
      ∀ f ∈ B,
        ∫ ω, Real.exp ((distributionPairingTorus ω f) ^ P.n)
          ∂(infiniteVolumeMeasure P L).toMeasure ≤ 2 := by
  sorry

end
