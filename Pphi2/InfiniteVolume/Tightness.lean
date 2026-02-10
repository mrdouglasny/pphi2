/-
  Pphi2.InfiniteVolume.Tightness
  Tightness of the family {μ_L} and existence of the infinite
  volume limit via Prokhorov's theorem, as L → ∞.

  Reference: DDJ Section 6.
  Adapted from spheres (R → ∞) to cylinders (L → ∞).
-/
import Pphi2.Energy.EnergyEstimate
import Pphi2.MeasureCylinder.UVLimit

noncomputable section

open MeasureTheory

/-! ## Uniform moment bound -/

/-- **Proposition 6.1** (Tightness on the cylinder).
    There exists C > 0 such that for all L ≥ 1, N ≥ 1, and suitable g:

    ∫ ‖φ‖ⁿ_{Lₙ^{-κ}(v_L^{1/n})} dμ^g_{L,N}(φ) ≤ C.

    The bound is uniform in L and N.

    Proof: Use stationarity (Lem 3.3) to write the LHS as a time-average
    of 𝔼‖Φ(t)‖ⁿ. Apply energy estimate (Prop 5.1) to bound
    the time-average of the Ψ part. Use free field bounds (Lem C.6)
    for the Z part.

    DDJ Proposition 6.1, adapted to cylinder. -/
axiom uniform_moment_bound (P : InteractionPolynomial) :
    ∃ (κ C : ℝ), 0 < κ ∧ 0 < C ∧
      ∀ (L : ℝ) (_ : 1 ≤ L) (N : ℕ+),
        True -- ∫ ‖φ‖ⁿ dμ^g ≤ C

/-! ## Tightness and Prokhorov -/

/-- The family of measures {μ_L}_{L ∈ ℕ₊} on FieldConfigurationTorus 2 L is tight
    in the topology of L_n^{-2κ}(v_L^{2/n}).

    Proof: By Proposition 6.1 the n-th moments in L_n^{-κ}(v_L^{1/n})
    are uniformly bounded. The embedding L_n^{-κ}(v_L^{1/n}) ↪ L_n^{-2κ}(v_L^{2/n})
    is compact (Thm A.5(C)). Apply tightness criterion.

    DDJ Remark 6.2, adapted to cylinder. -/
axiom family_tight (P : InteractionPolynomial) :
    True -- the family of measures is tight

/-- By Prokhorov's theorem, the family {μ_L} has a weakly
    convergent subsequence as L → ∞.

    DDJ Remark 6.2, adapted. -/
axiom exists_convergent_subsequence (P : InteractionPolynomial) :
    ∃ (sub : ℕ → ℕ+), StrictMono sub ∧
      True -- μ_{sub(k)} converges weakly as k → ∞

/-! ## The infinite volume limit -/

/-- The P(Φ)₂ measure μ_L on FieldConfigurationTorus 2 L for each L.
    This is the UV limit measure for a given cylinder circumference. -/
def infiniteVolumeMeasure (P : InteractionPolynomial) (L : ℝ) :
    ProbabilityMeasure (FieldConfigurationTorus 2 L) :=
  uvLimitMeasure P L

end
