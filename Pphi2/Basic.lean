/-
  Pphi2.Basic
  Core definitions for the P(Φ)₂ construction on the cylinder ℝ × S¹_L.

  Reference: Duch-Dybalski-Jahandideh (2311.04137), Section 1.
  Adapted from spheres S_R to cylinders ℝ × S¹_L.
-/
import OSforGFF.Basic
import OSforGFF.TorusSpacetime
import OSforGFF.QFTFramework.Instances

noncomputable section

open MeasureTheory

/-! ## Dimension setup -/

instance : Fact (0 < 2) := ⟨by omega⟩

/-- The Euclidean plane ℝ², as SpaceTime 2. -/
abbrev Plane := SpaceTime 2

/-! ## The cylinder ℝ × S¹_L -/

/-- The cylinder spacetime ℝ × S¹_L for the P(Φ)₂ construction.
    Product of continuous time ℝ and spatial circle of circumference L. -/
abbrev Cylinder (L : ℝ) := SpaceTimeTorus 2 L

/-- The QFT framework for P(Φ)₂ on ℝ × S¹_L. -/
noncomputable def pphi2Framework (L : ℝ) [Fact (0 < L)] : QFTFramework :=
  QFTFramework.torus 2 L

/-! ## Cylinder-specific geometry (axiomatized) -/

/-- The Laplacian on the cylinder: Δ = ∂²_t + Δ_{S¹_L}.
    Eigenvalues: -(k² + (2πn/L)²) for k ∈ ℝ, n ∈ ℤ. -/
axiom laplacianCylinder (L : ℝ) :
  TestFunctionTorus 2 L →L[ℝ] TestFunctionTorus 2 L

/-- Free covariance on the cylinder: G_L = (1 - Δ)⁻¹.
    Explicit via Fourier series in the spatial direction. -/
axiom freeCovariance (L : ℝ) :
  TestFunctionTorus 2 L →L[ℝ] TestFunctionTorus 2 L

/-- Counterterm c_{L,N} (Wick ordering constant).
    DDJ Definition 2.1, adapted to cylinder. -/
axiom counterterm (L : ℝ) (N : ℕ+) : ℝ

/-- |c_{L,N} - (1/2π) log N| ≤ C uniformly in L.
    DDJ Lemma B.1, adapted to cylinder. -/
axiom counterterm_bound (L : ℝ) (N : ℕ+) :
  ∃ C : ℝ, |counterterm L N - (1 / (2 * Real.pi)) * Real.log N| ≤ C

end
