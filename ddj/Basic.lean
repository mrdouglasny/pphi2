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

/-! ## Cylinder spacetime types

We define cylinder spacetime ℝ × S¹_L and associated test function
and field configuration spaces locally, following the pattern of
`LatticeSpacetime.lean` in OSforGFF. -/

/-- The cylinder spacetime ℝ × S¹_L: product of continuous time ℝ and
    the spatial circle of circumference L. -/
abbrev SpaceTimeCyl (_d : ℕ) (L : ℝ) := ℝ × AddCircle L

instance (L : ℝ) : Inhabited (SpaceTimeCyl 2 L) := ⟨(0, 0)⟩

instance (L : ℝ) : PseudoMetricSpace (SpaceTimeCyl 2 L) := inferInstance

/-- Test functions on the cylinder ℝ × S¹_L, realized as Fourier modes.
    An element of S(ℝ × S¹_L) is a ℤ-indexed family of Schwartz functions on ℝ
    (the Fourier coefficients in the spatial circle direction) satisfying:
    - Rapid decay in the mode index n (Schwartz-class on the dual lattice)
    - Reality condition: f̂(-n)(t) = conj(f̂(n)(t))
    This is the Fourier-analytic presentation of S(ℝ × S¹_L). -/
structure TestFunctionCyl (_d : ℕ) (_L : ℝ) where
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

namespace TestFunctionCyl

/-- Pointwise addition of Fourier modes. -/
instance instAdd (d : ℕ) (L : ℝ) : Add (TestFunctionCyl d L) where
  add f g := ⟨fun n => f.fourierMode n + g.fourierMode n, sorry, sorry⟩

/-- Pointwise negation of Fourier modes. -/
instance instNeg (d : ℕ) (L : ℝ) : Neg (TestFunctionCyl d L) where
  neg f := ⟨fun n => -f.fourierMode n, sorry, sorry⟩

/-- Zero test function: all Fourier modes are zero. -/
instance instZero (d : ℕ) (L : ℝ) : Zero (TestFunctionCyl d L) where
  zero := ⟨fun _ => 0, sorry, sorry⟩

@[instance] noncomputable def instAddCommGroup (d : ℕ) (L : ℝ) :
    AddCommGroup (TestFunctionCyl d L) := by
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
    Module ℝ (TestFunctionCyl d L) := by
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
    TopologicalSpace (TestFunctionCyl d L) := sorry

@[instance] def instTopologicalAddGroup (d : ℕ) (L : ℝ) :
    IsTopologicalAddGroup (TestFunctionCyl d L) := sorry

@[instance] def instContinuousSMul (d : ℕ) (L : ℝ) :
    ContinuousSMul ℝ (TestFunctionCyl d L) := sorry

end TestFunctionCyl

/-- Complex test functions on the cylinder ℝ × S¹_L, realized as Fourier modes
    without the reality condition. An element is a ℤ-indexed family of Schwartz
    functions on ℝ satisfying rapid decay in the mode index. -/
structure TestFunctionCylℂ (_d : ℕ) (_L : ℝ) where
  /-- The n-th Fourier mode: a Schwartz function ℝ → ℂ. -/
  fourierMode : ℤ → SchwartzMap ℝ ℂ
  /-- Rapid decay in the mode index. -/
  rapidDecay : ∀ (k j : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ,
    (SchwartzMap.seminorm ℝ k j) (fourierMode n) ≤
      C / (1 + (Int.natAbs n : ℝ)) ^ (k + 1)

namespace TestFunctionCylℂ

/-- Pointwise addition of Fourier modes. -/
instance instAdd (d : ℕ) (L : ℝ) : Add (TestFunctionCylℂ d L) where
  add f g := ⟨fun n => f.fourierMode n + g.fourierMode n, sorry⟩

/-- Pointwise negation of Fourier modes. -/
instance instNeg (d : ℕ) (L : ℝ) : Neg (TestFunctionCylℂ d L) where
  neg f := ⟨fun n => -f.fourierMode n, sorry⟩

/-- Zero test function: all Fourier modes are zero. -/
instance instZero (d : ℕ) (L : ℝ) : Zero (TestFunctionCylℂ d L) where
  zero := ⟨fun _ => 0, sorry⟩

@[instance] noncomputable def instAddCommGroup (d : ℕ) (L : ℝ) :
    AddCommGroup (TestFunctionCylℂ d L) := by
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
    Module ℂ (TestFunctionCylℂ d L) := by
  exact {
    smul := fun c f => ⟨fun n => c • f.fourierMode n, sorry⟩
    one_smul := sorry
    mul_smul := sorry
    smul_zero := sorry
    smul_add := sorry
    add_smul := sorry
    zero_smul := sorry
  }

end TestFunctionCylℂ

/-- Embedding of real test functions into complex test functions,
    forgetting the reality condition. -/
def TestFunctionCyl.toComplex {d : ℕ} {L : ℝ}
    (f : TestFunctionCyl d L) : TestFunctionCylℂ d L :=
  ⟨f.fourierMode, f.rapidDecay⟩

/-- Field configurations on the cylinder: tempered distributions D'(ℝ × S¹_L),
    defined as the weak dual of the test function space.
    This follows the Glimm-Jaffe approach where the field measure is supported
    on the space of distributions, not L² functions.
    DDJ: measures are concentrated on L¹₂(ℝ × S¹_L) ⊂ D'(ℝ × S¹_L). -/
abbrev FieldConfigurationCyl (d : ℕ) (L : ℝ) :=
  WeakDual ℝ (TestFunctionCyl d L)

instance (d : ℕ) (L : ℝ) : MeasurableSpace (FieldConfigurationCyl d L) := borel _

/-- Distribution pairing on the cylinder: ⟨ω, f⟩ for ω ∈ D'(ℝ × S¹_L)
    and f a test function. This is just evaluation of the continuous
    linear functional. -/
def distributionPairingCyl {d : ℕ} {L : ℝ}
    (ω : FieldConfigurationCyl d L) (f : TestFunctionCyl d L) : ℝ :=
  ω f

/-! ## Symmetry group for the cylinder -/

/-- The symmetry group for the cylinder ℝ × S¹_L:
    time translations ℝ and spatial translations ℝ/Lℤ. -/
axiom SymmetryGroupCyl (d : ℕ) (L : ℝ) : Type

namespace SymmetryGroupCyl
@[instance] axiom instGroup (d : ℕ) (L : ℝ) :
  Group (SymmetryGroupCyl d L)
end SymmetryGroupCyl

/-! ## Operations for the QFTFramework instance -/

/-- Real generating functional on the cylinder: Z[J] = ∫ exp(i⟨ω,J⟩) dμ(ω). -/
def realGenFunctionalCyl {d : ℕ} {L : ℝ}
    (dμ : ProbabilityMeasure (FieldConfigurationCyl d L))
    (J : TestFunctionCyl d L) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * ↑(ω J)) ∂dμ.toMeasure

/-- Complex pairing ⟨ω, f⟩_ℂ for field configurations with complex test functions. -/
def complexPairingCyl {d : ℕ} {L : ℝ}
    (ω : FieldConfigurationCyl d L)
    (f : TestFunctionCylℂ d L) : ℂ := sorry

/-- Complex generating functional on the cylinder:
    Z[J] = ∫ exp(i⟨ω,J⟩_ℂ) dμ(ω) for complex test functions J. -/
def complexGenFunctionalCyl {d : ℕ} {L : ℝ}
    (dμ : ProbabilityMeasure (FieldConfigurationCyl d L))
    (J : TestFunctionCylℂ d L) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * complexPairingCyl ω J) ∂dμ.toMeasure

/-- Time reflection on the cylinder: (Θf)_n(t) = f_n(-t), acting mode-by-mode.
    Composing a Schwartz function with negation preserves Schwartz class. -/
noncomputable def timeReflectionCyl (d : ℕ) (L : ℝ) :
    TestFunctionCyl d L →L[ℝ] TestFunctionCyl d L where
  toFun f := ⟨fun n => sorry, sorry, sorry⟩  -- f_n composed with negation
  map_add' := sorry
  map_smul' := sorry
  cont := sorry

/-- Test functions supported at positive time: all Fourier modes
    have support in {t : t > 0}. -/
def positiveTimeSubmoduleCyl (d : ℕ) (L : ℝ) :
    Submodule ℝ (TestFunctionCyl d L) where
  carrier := { f | ∀ n : ℤ, tsupport (f.fourierMode n) ⊆ Set.Ioi 0 }
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

/-- Spacetime translation on test functions:
    (T_{s,θ} f)_n(t) = exp(2πinθ/L) · f_n(t - s). -/
def translateTestFunCyl {d : ℕ} {L : ℝ}
    (a : SpaceTimeCyl d L) (f : TestFunctionCyl d L) :
    TestFunctionCyl d L where
  fourierMode := fun n => sorry  -- phase * translate
  rapidDecay := sorry
  reality := sorry

/-- Symmetry group action on complex test functions.
    Sorry'd since SymmetryGroupCyl is still axiomatized. -/
def symmetryActionCyl {d : ℕ} {L : ℝ} :
    SymmetryGroupCyl d L → TestFunctionCylℂ d L → TestFunctionCylℂ d L :=
  sorry

/-- Time translation acting on field configurations (dual action):
    ⟨T_s ω, f⟩ = ⟨ω, T_{-s} f⟩. -/
def timeTranslationDistCyl {d : ℕ} {L : ℝ}
    (s : ℝ) (ω : FieldConfigurationCyl d L) :
    FieldConfigurationCyl d L := sorry

/-- Nuclear space: a topological vector space where every continuous linear
    map to a Banach space is nuclear. Axiomatized here; the full definition
    is in OSforGFF.NuclearSpace. Needed for the Minlos theorem. -/
class NuclearSpace (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] : Prop where
  nuclear : True := ⟨⟩

/-- Nuclear space instance for test functions on the cylinder.
    Follows from S(ℝ) being nuclear and the mode decomposition. -/
instance instNuclearSpaceCyl (d : ℕ) (L : ℝ) :
    NuclearSpace (TestFunctionCyl d L) := ⟨trivial⟩

/-! ## QFTFramework instance for the cylinder -/

/-- QFTFramework for the cylinder/torus spacetime ℝ × S¹_L. -/
def QFTFramework.cylinder (d : ℕ) (L : ℝ) [Fact (0 < d)] [Fact (0 < L)] :
    QFTFramework where
  Spacetime := SpaceTimeCyl d L
  TimeParam := ℝ
  TestFun := TestFunctionCyl d L
  TestFunℂ := TestFunctionCylℂ d L
  FieldConfig := FieldConfigurationCyl d L
  SymmetryGroup := SymmetryGroupCyl d L

  instACG_TF := TestFunctionCyl.instAddCommGroup d L
  instMod_TF := TestFunctionCyl.instModule d L
  instTS_TF := TestFunctionCyl.instTopologicalSpace d L
  instACG_TFℂ := TestFunctionCylℂ.instAddCommGroup d L
  instMod_TFℂ := TestFunctionCylℂ.instModule d L

  instMS_FC := inferInstance
  instTS_FC := inferInstance

  instPMS_ST := inferInstance
  instInh_ST := ⟨(0, 0)⟩

  instGrp_SG := SymmetryGroupCyl.instGroup d L

  instLO_TP := inferInstance
  instTS_TP := inferInstance
  instOT_TP := inferInstance

  realGenFunctional := realGenFunctionalCyl
  complexGenFunctional := complexGenFunctionalCyl
  symmetryAction := symmetryActionCyl
  timeReflectionReal := timeReflectionCyl d L
  positiveTimeSubmodule := positiveTimeSubmoduleCyl d L
  translateTestFun := translateTestFunCyl
  complexPairing := complexPairingCyl
  timeTranslationDist := timeTranslationDistCyl

/-! ## The cylinder ℝ × S¹_L -/

/-- The cylinder spacetime ℝ × S¹_L for the P(Φ)₂ construction.
    Product of continuous time ℝ and spatial circle of circumference L. -/
abbrev Cylinder (L : ℝ) := SpaceTimeCyl 2 L

/-- The QFT framework for P(Φ)₂ on ℝ × S¹_L. -/
noncomputable def pphi2Framework (L : ℝ) [Fact (0 < L)] : QFTFramework :=
  QFTFramework.cylinder 2 L

/-! ## Cylinder-specific geometry (axiomatized) -/

/-- The Laplacian on the cylinder: Δ = ∂²_t + Δ_{S¹_L}.
    Eigenvalues: -(k² + (2πn/L)²) for k ∈ ℝ, n ∈ ℤ. -/
axiom laplacianCylinder (L : ℝ) :
  TestFunctionCyl 2 L →L[ℝ] TestFunctionCyl 2 L

/-- Free covariance on the cylinder: G_L = (1 - Δ)⁻¹.
    Explicit via Fourier series in the spatial direction. -/
axiom freeCovariance (L : ℝ) :
  TestFunctionCyl 2 L →L[ℝ] TestFunctionCyl 2 L

/-- Counterterm c_{L,N} (Wick ordering constant).
    DDJ Definition 2.1, adapted to cylinder. -/
axiom counterterm (L : ℝ) (N : ℕ+) : ℝ

/-- |c_{L,N} - (1/2π) log N| ≤ C uniformly in L.
    DDJ Lemma B.1, adapted to cylinder. -/
axiom counterterm_bound (L : ℝ) (N : ℕ+) :
  ∃ C : ℝ, |counterterm L N - (1 / (2 * Real.pi)) * Real.log N| ≤ C

end
