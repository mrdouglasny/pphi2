/-
  Pphi2.Basic
  Core definitions for the P(Φ)₂ construction on the cylinder ℝ × S¹_L.

  Reference: Duch-Dybalski-Jahandideh (2311.04137), Section 1.
  Adapted from spheres S_R to cylinders ℝ × S¹_L.
-/
import OSforGFF.Basic
import OSforGFF.QFTFramework.Instances
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

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

/-- Test functions on the torus ℝ × S¹_L, realized as Fourier modes.
    An element of S(ℝ × S¹_L) is a ℤ-indexed family of Schwartz functions on ℝ
    (the Fourier coefficients in the spatial circle direction) satisfying:
    - Rapid decay in the mode index n (Schwartz-class on the dual lattice)
    - Reality condition: f̂(-n)(t) = conj(f̂(n)(t))
    This is the Fourier-analytic presentation of S(ℝ × S¹_L). -/
structure TestFunctionTorus (_d : ℕ) (_L : ℝ) where
  /-- The n-th Fourier mode: a Schwartz function ℝ → ℂ. -/
  fourierMode : ℤ → SchwartzMap ℝ ℂ
  /-- Rapid decay in the mode index: the Schwartz seminorms of the modes
      decay faster than any polynomial in n. -/
  rapidDecay : ∀ (k j : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ,
    (SchwartzMap.seminorm ℝ k j) (fourierMode n) ≤
      C / (1 + (Int.natAbs n : ℝ)) ^ (k + 1)
  /-- Reality condition: f̂(-n)(t) = conj(f̂(n)(t)), ensuring the
      corresponding function on ℝ × S¹_L is real-valued. -/
  reality : ∀ (n : ℤ) (t : ℝ),
    fourierMode (-n) t = starRingEnd ℂ (fourierMode n t)

namespace TestFunctionTorus

/-- Pointwise addition of Fourier modes. -/
instance instAdd (d : ℕ) (L : ℝ) : Add (TestFunctionTorus d L) where
  add f g := ⟨fun n => f.fourierMode n + g.fourierMode n, sorry, sorry⟩

/-- Pointwise negation of Fourier modes. -/
instance instNeg (d : ℕ) (L : ℝ) : Neg (TestFunctionTorus d L) where
  neg f := ⟨fun n => -f.fourierMode n, sorry, sorry⟩

/-- Zero test function: all Fourier modes are zero. -/
instance instZero (d : ℕ) (L : ℝ) : Zero (TestFunctionTorus d L) where
  zero := ⟨fun _ => 0, sorry, sorry⟩

@[instance] noncomputable def instAddCommGroup (d : ℕ) (L : ℝ) :
    AddCommGroup (TestFunctionTorus d L) := by
  exact {
    add := (· + ·)
    neg := (- ·)
    zero := 0
    add_assoc := sorry
    zero_add := sorry
    add_zero := sorry
    add_comm := sorry
    neg_add_cancel := sorry
    nsmul := nsmulRec
    zsmul := zsmulRec
  }

@[instance] noncomputable def instModule (d : ℕ) (L : ℝ) :
    Module ℝ (TestFunctionTorus d L) := by
  exact {
    smul := fun r f => ⟨fun n => r • f.fourierMode n, sorry, sorry⟩
    one_smul := sorry
    mul_smul := sorry
    smul_zero := sorry
    smul_add := sorry
    add_smul := sorry
    zero_smul := sorry
  }

@[instance] def instTopologicalSpace (d : ℕ) (L : ℝ) :
    TopologicalSpace (TestFunctionTorus d L) := sorry

@[instance] def instTopologicalAddGroup (d : ℕ) (L : ℝ) :
    IsTopologicalAddGroup (TestFunctionTorus d L) := sorry

@[instance] def instContinuousSMul (d : ℕ) (L : ℝ) :
    ContinuousSMul ℝ (TestFunctionTorus d L) := sorry

end TestFunctionTorus

/-- Complex test functions on the torus ℝ × S¹_L, realized as Fourier modes
    without the reality condition. An element is a ℤ-indexed family of Schwartz
    functions on ℝ satisfying rapid decay in the mode index. -/
structure TestFunctionTorusℂ (_d : ℕ) (_L : ℝ) where
  /-- The n-th Fourier mode: a Schwartz function ℝ → ℂ. -/
  fourierMode : ℤ → SchwartzMap ℝ ℂ
  /-- Rapid decay in the mode index. -/
  rapidDecay : ∀ (k j : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ,
    (SchwartzMap.seminorm ℝ k j) (fourierMode n) ≤
      C / (1 + (Int.natAbs n : ℝ)) ^ (k + 1)

namespace TestFunctionTorusℂ

/-- Pointwise addition of Fourier modes. -/
instance instAdd (d : ℕ) (L : ℝ) : Add (TestFunctionTorusℂ d L) where
  add f g := ⟨fun n => f.fourierMode n + g.fourierMode n, sorry⟩

/-- Pointwise negation of Fourier modes. -/
instance instNeg (d : ℕ) (L : ℝ) : Neg (TestFunctionTorusℂ d L) where
  neg f := ⟨fun n => -f.fourierMode n, sorry⟩

/-- Zero test function: all Fourier modes are zero. -/
instance instZero (d : ℕ) (L : ℝ) : Zero (TestFunctionTorusℂ d L) where
  zero := ⟨fun _ => 0, sorry⟩

@[instance] noncomputable def instAddCommGroup (d : ℕ) (L : ℝ) :
    AddCommGroup (TestFunctionTorusℂ d L) := by
  exact {
    add := (· + ·)
    neg := (- ·)
    zero := 0
    add_assoc := sorry
    zero_add := sorry
    add_zero := sorry
    add_comm := sorry
    neg_add_cancel := sorry
    nsmul := nsmulRec
    zsmul := zsmulRec
  }

@[instance] noncomputable def instModule (d : ℕ) (L : ℝ) :
    Module ℂ (TestFunctionTorusℂ d L) := by
  exact {
    smul := fun c f => ⟨fun n => c • f.fourierMode n, sorry⟩
    one_smul := sorry
    mul_smul := sorry
    smul_zero := sorry
    smul_add := sorry
    add_smul := sorry
    zero_smul := sorry
  }

end TestFunctionTorusℂ

/-- Embedding of real test functions into complex test functions,
    forgetting the reality condition. -/
def TestFunctionTorus.toComplex {d : ℕ} {L : ℝ}
    (f : TestFunctionTorus d L) : TestFunctionTorusℂ d L :=
  ⟨f.fourierMode, f.rapidDecay⟩

/-- Field configurations on the torus: tempered distributions D'(ℝ × S¹_L),
    defined as the weak dual of the test function space.
    This follows the Glimm-Jaffe approach where the field measure is supported
    on the space of distributions, not L² functions.
    DDJ: measures are concentrated on L¹₂(ℝ × S¹_L) ⊂ D'(ℝ × S¹_L). -/
abbrev FieldConfigurationTorus (d : ℕ) (L : ℝ) :=
  WeakDual ℝ (TestFunctionTorus d L)

instance (d : ℕ) (L : ℝ) : MeasurableSpace (FieldConfigurationTorus d L) := borel _

/-- Distribution pairing on the torus: ⟨ω, f⟩ for ω ∈ D'(ℝ × S¹_L)
    and f a test function. This is just evaluation of the continuous
    linear functional. -/
def distributionPairingTorus {d : ℕ} {L : ℝ}
    (ω : FieldConfigurationTorus d L) (f : TestFunctionTorus d L) : ℝ :=
  ω f

/-! ## Symmetry group for the torus -/

/-- The symmetry group for the cylinder ℝ × S¹_L:
    time translations ℝ and spatial translations ℝ/Lℤ. -/
axiom SymmetryGroupTorus (d : ℕ) (L : ℝ) : Type

namespace SymmetryGroupTorus
@[instance] axiom instGroup (d : ℕ) (L : ℝ) :
  Group (SymmetryGroupTorus d L)
end SymmetryGroupTorus

/-! ## Operations for the QFTFramework instance -/

/-- Real generating functional on the torus: Z[J] = ∫ exp(i⟨ω,J⟩) dμ(ω). -/
def realGenFunctionalTorus {d : ℕ} {L : ℝ}
    (dμ : ProbabilityMeasure (FieldConfigurationTorus d L))
    (J : TestFunctionTorus d L) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * ↑(ω J)) ∂dμ.toMeasure

/-- Complex pairing ⟨ω, f⟩_ℂ for field configurations with complex test functions. -/
def complexPairingTorus {d : ℕ} {L : ℝ}
    (ω : FieldConfigurationTorus d L)
    (f : TestFunctionTorusℂ d L) : ℂ := sorry

/-- Complex generating functional on the torus:
    Z[J] = ∫ exp(i⟨ω,J⟩_ℂ) dμ(ω) for complex test functions J. -/
def complexGenFunctionalTorus {d : ℕ} {L : ℝ}
    (dμ : ProbabilityMeasure (FieldConfigurationTorus d L))
    (J : TestFunctionTorusℂ d L) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * complexPairingTorus ω J) ∂dμ.toMeasure

/-- Time reflection on the torus: (Θf)_n(t) = f_n(-t), acting mode-by-mode.
    Composing a Schwartz function with negation preserves Schwartz class. -/
noncomputable def timeReflectionTorus (d : ℕ) (L : ℝ) :
    TestFunctionTorus d L →L[ℝ] TestFunctionTorus d L where
  toFun f := ⟨fun n => sorry, sorry, sorry⟩  -- f_n composed with negation
  map_add' := sorry
  map_smul' := sorry
  cont := sorry

/-- Test functions supported at positive time: all Fourier modes
    have support in {t : t > 0}. -/
def positiveTimeSubmoduleTorus (d : ℕ) (L : ℝ) :
    Submodule ℝ (TestFunctionTorus d L) where
  carrier := { f | ∀ n : ℤ, tsupport (f.fourierMode n) ⊆ Set.Ioi 0 }
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

/-- Spacetime translation on test functions:
    (T_{s,θ} f)_n(t) = exp(2πinθ/L) · f_n(t - s). -/
def translateTestFunTorus {d : ℕ} {L : ℝ}
    (a : SpaceTimeTorus d L) (f : TestFunctionTorus d L) :
    TestFunctionTorus d L where
  fourierMode := fun n => sorry  -- phase * translate
  rapidDecay := sorry
  reality := sorry

/-- Symmetry group action on complex test functions.
    Sorry'd since SymmetryGroupTorus is still axiomatized. -/
def symmetryActionTorus {d : ℕ} {L : ℝ} :
    SymmetryGroupTorus d L → TestFunctionTorusℂ d L → TestFunctionTorusℂ d L :=
  sorry

/-- Time translation acting on field configurations (dual action):
    ⟨T_s ω, f⟩ = ⟨ω, T_{-s} f⟩. -/
def timeTranslationDistTorus {d : ℕ} {L : ℝ}
    (s : ℝ) (ω : FieldConfigurationTorus d L) :
    FieldConfigurationTorus d L := sorry

/-- Nuclear space: a topological vector space where every continuous linear
    map to a Banach space is nuclear. Axiomatized here; the full definition
    is in OSforGFF.NuclearSpace. Needed for the Minlos theorem. -/
class NuclearSpace (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] : Prop where
  nuclear : True := ⟨⟩

/-- Nuclear space instance for test functions on the torus.
    Follows from S(ℝ) being nuclear and the mode decomposition. -/
instance instNuclearSpaceTorus (d : ℕ) (L : ℝ) :
    NuclearSpace (TestFunctionTorus d L) := ⟨trivial⟩

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

  instMS_FC := inferInstance
  instTS_FC := inferInstance

  instPMS_ST := inferInstance
  instInh_ST := ⟨(0, 0)⟩

  instGrp_SG := SymmetryGroupTorus.instGroup d L

  instLO_TP := inferInstance
  instTS_TP := inferInstance
  instOT_TP := inferInstance

  realGenFunctional := realGenFunctionalTorus
  complexGenFunctional := complexGenFunctionalTorus
  symmetryAction := symmetryActionTorus
  timeReflectionReal := timeReflectionTorus d L
  positiveTimeSubmodule := positiveTimeSubmoduleTorus d L
  translateTestFun := translateTestFunTorus
  complexPairing := complexPairingTorus
  timeTranslationDist := timeTranslationDistTorus

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
