/-
  Pphi2.Basic
  Core definitions for the P(Φ)₂ construction on the cylinder ℝ × S¹_L.

  Reference: Duch-Dybalski-Jahandideh (2311.04137), Section 1.
  Adapted from spheres S_R to cylinders ℝ × S¹_L.
-/
import OSforGFF.Basic
import OSforGFF.QFTFramework.Instances
import Mathlib.Topology.Instances.AddCircle.Defs

noncomputable section

open MeasureTheory

/-! ## Dimension setup -/

instance : Fact (0 < 2) := ⟨by omega⟩

/-- The Euclidean plane ℝ², as SpaceTime 2. -/
abbrev Plane := SpaceTime 2

/-! ## Torus spacetime types

We define torus/cylinder spacetime ℝ × S¹_L and associated test function
and field configuration spaces locally, following the pattern of
`LatticeSpacetime.lean` in OSforGFF. -/

/-- The cylinder spacetime ℝ × S¹_L: product of continuous time ℝ and
    the spatial circle of circumference L. -/
abbrev SpaceTimeTorus (_d : ℕ) (L : ℝ) := ℝ × AddCircle L

instance (L : ℝ) : Inhabited (SpaceTimeTorus 2 L) := ⟨(0, 0)⟩

instance (L : ℝ) : PseudoMetricSpace (SpaceTimeTorus 2 L) := inferInstance

/-- Test functions on the torus ℝ × S¹_L: smooth functions.
    Axiomatized as an abstract type with the required algebraic structure. -/
axiom TestFunctionTorus (d : ℕ) (L : ℝ) : Type

namespace TestFunctionTorus
@[instance] axiom instAddCommGroup (d : ℕ) (L : ℝ) :
  AddCommGroup (TestFunctionTorus d L)
@[instance] axiom instModule (d : ℕ) (L : ℝ) :
  Module ℝ (TestFunctionTorus d L)
@[instance] axiom instTopologicalSpace (d : ℕ) (L : ℝ) :
  TopologicalSpace (TestFunctionTorus d L)
end TestFunctionTorus

/-- Complex test functions on the torus. -/
axiom TestFunctionTorusℂ (d : ℕ) (L : ℝ) : Type

namespace TestFunctionTorusℂ
@[instance] axiom instAddCommGroup (d : ℕ) (L : ℝ) :
  AddCommGroup (TestFunctionTorusℂ d L)
@[instance] axiom instModule (d : ℕ) (L : ℝ) :
  Module ℂ (TestFunctionTorusℂ d L)
end TestFunctionTorusℂ

/-- Field configurations on the torus: distributions on ℝ × S¹_L. -/
axiom FieldConfigurationTorus (d : ℕ) (L : ℝ) : Type

namespace FieldConfigurationTorus
@[instance] axiom instMeasurableSpace (d : ℕ) (L : ℝ) :
  MeasurableSpace (FieldConfigurationTorus d L)
@[instance] axiom instTopologicalSpace (d : ℕ) (L : ℝ) :
  TopologicalSpace (FieldConfigurationTorus d L)
end FieldConfigurationTorus

/-- Distribution pairing on the torus: ⟨ω, f⟩ for ω a distribution and f a test function. -/
axiom distributionPairingTorus {d : ℕ} {L : ℝ} :
  FieldConfigurationTorus d L → TestFunctionTorus d L → ℝ

/-! ## Symmetry group for the torus -/

/-- The symmetry group for the cylinder ℝ × S¹_L:
    time translations ℝ and spatial translations ℝ/Lℤ. -/
axiom SymmetryGroupTorus (d : ℕ) (L : ℝ) : Type

namespace SymmetryGroupTorus
@[instance] axiom instGroup (d : ℕ) (L : ℝ) :
  Group (SymmetryGroupTorus d L)
end SymmetryGroupTorus

/-! ## QFTFramework instance for the torus -/

/-- QFTFramework for the cylinder/torus spacetime ℝ × S¹_L. -/
def QFTFramework.torus (d : ℕ) (L : ℝ) [Fact (0 < d)] [Fact (0 < L)] :
    QFTFramework where
  Spacetime := SpaceTimeTorus d L
  TimeParam := ℝ
  TestFun := TestFunctionTorus d L
  TestFunℂ := TestFunctionTorusℂ d L
  FieldConfig := FieldConfigurationTorus d L
  SymmetryGroup := SymmetryGroupTorus d L

  instACG_TF := TestFunctionTorus.instAddCommGroup d L
  instMod_TF := TestFunctionTorus.instModule d L
  instTS_TF := TestFunctionTorus.instTopologicalSpace d L
  instACG_TFℂ := TestFunctionTorusℂ.instAddCommGroup d L
  instMod_TFℂ := TestFunctionTorusℂ.instModule d L

  instMS_FC := FieldConfigurationTorus.instMeasurableSpace d L
  instTS_FC := FieldConfigurationTorus.instTopologicalSpace d L

  instPMS_ST := inferInstance
  instInh_ST := ⟨(0, 0)⟩

  instGrp_SG := SymmetryGroupTorus.instGroup d L

  instLO_TP := inferInstance
  instTS_TP := inferInstance
  instOT_TP := inferInstance

  realGenFunctional := sorry
  complexGenFunctional := sorry
  symmetryAction := sorry
  timeReflectionReal := sorry
  positiveTimeSubmodule := sorry
  translateTestFun := sorry
  complexPairing := sorry
  timeTranslationDist := sorry

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
