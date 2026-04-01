import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Euclidean QFT formulation layers

This file records a distinction that matters for rigorous QFT formalization:

1. Concrete positive-measure models on configuration spaces
2. Generating-functional / simple-tensor moment models
3. Distributional Schwinger-function models
4. Additional reconstruction hypotheses (for example OS 1975 linear-growth input)

The Glimm-Jaffe/Nelson `P(Φ)₂` construction naturally lives at (1).
The original Osterwalder-Schrader axioms are closer to (3), and the
reconstruction theorem needs extra growth data as in (4). Gauge and fermionic
theories may fit later layers without fitting the first one.

By keeping these layers separate, the library can compare formulations without
silently identifying "positive measure on `S'`" with "general QFT".
-/

namespace Common.QFT.Euclidean

universe uSpace uTest uComplex uNPoint uConfig

open MeasureTheory

/-- Shared low-level one-point data for a Euclidean formulation.

This base structure is intentionally minimal: it is enough to talk about
measure-level realizations and simple-tensor moments, but not yet about genuine
distributional Schwinger functions. The richer linear/topological data needed
for the latter lives in `SchwingerFormulation` below. -/
structure Formulation where
  SpaceTime : Type uSpace
  TestFunction : Type uTest
  ComplexTestFunction : Type uComplex
  positiveTimeTestFunctions : Set TestFunction

namespace Formulation

variable (F : Formulation)

/-- Positive-time test functions for a chosen Euclidean formulation. -/
abbrev PositiveTimeTestFunction :=
  { f : F.TestFunction // f ∈ F.positiveTimeTestFunctions }

end Formulation

/-- Additional linear/topological structure needed to talk about genuine
distributional Schwinger functions and reconstruction input.

The point of separating this from `Formulation` is that the measure and
simple-tensor layers should not be forced to carry the full nuclear/Schwartz
infrastructure needed later. -/
structure SchwingerFormulation extends Formulation where
  NPointTestFunction : ℕ → Type uNPoint
  instAddCommGroupTestFunction : AddCommGroup TestFunction
  instModuleTestFunction : Module ℝ TestFunction
  instTopologicalSpaceTestFunction : TopologicalSpace TestFunction
  instIsTopologicalAddGroupTestFunction : IsTopologicalAddGroup TestFunction
  instContinuousSMulTestFunction : ContinuousSMul ℝ TestFunction
  instAddCommGroupComplexTestFunction : AddCommGroup ComplexTestFunction
  instModuleComplexTestFunction : Module ℂ ComplexTestFunction
  instTopologicalSpaceComplexTestFunction : TopologicalSpace ComplexTestFunction
  instIsTopologicalAddGroupComplexTestFunction : IsTopologicalAddGroup ComplexTestFunction
  instContinuousSMulComplexTestFunction : ContinuousSMul ℂ ComplexTestFunction
  realToComplex : TestFunction → ComplexTestFunction
  realToComplex_add :
    ∀ f g, realToComplex (f + g) = realToComplex f + realToComplex g
  realToComplex_smul :
    ∀ (r : ℝ) (f : TestFunction),
      realToComplex (r • f) = (r : ℂ) • realToComplex f
  realToComplex_continuous : Continuous realToComplex
  positiveTimeSubmodule : Submodule ℝ TestFunction
  positiveTimeSubmodule_eq :
    positiveTimeSubmodule.carrier = positiveTimeTestFunctions
  instAddCommGroupNPointTestFunction :
    ∀ n, AddCommGroup (NPointTestFunction n)
  instModuleNPointTestFunction :
    ∀ n, Module ℂ (NPointTestFunction n)
  instTopologicalSpaceNPointTestFunction :
    ∀ n, TopologicalSpace (NPointTestFunction n)
  instIsTopologicalAddGroupNPointTestFunction :
    ∀ n, IsTopologicalAddGroup (NPointTestFunction n)
  instContinuousSMulNPointTestFunction :
    ∀ n, ContinuousSMul ℂ (NPointTestFunction n)

attribute [instance] SchwingerFormulation.instAddCommGroupTestFunction
attribute [instance] SchwingerFormulation.instModuleTestFunction
attribute [instance] SchwingerFormulation.instTopologicalSpaceTestFunction
attribute [instance] SchwingerFormulation.instIsTopologicalAddGroupTestFunction
attribute [instance] SchwingerFormulation.instContinuousSMulTestFunction
attribute [instance] SchwingerFormulation.instAddCommGroupComplexTestFunction
attribute [instance] SchwingerFormulation.instModuleComplexTestFunction
attribute [instance] SchwingerFormulation.instTopologicalSpaceComplexTestFunction
attribute [instance] SchwingerFormulation.instIsTopologicalAddGroupComplexTestFunction
attribute [instance] SchwingerFormulation.instContinuousSMulComplexTestFunction
attribute [instance] SchwingerFormulation.instAddCommGroupNPointTestFunction
attribute [instance] SchwingerFormulation.instModuleNPointTestFunction
attribute [instance] SchwingerFormulation.instTopologicalSpaceNPointTestFunction
attribute [instance] SchwingerFormulation.instIsTopologicalAddGroupNPointTestFunction
attribute [instance] SchwingerFormulation.instContinuousSMulNPointTestFunction

/-- Generating-functional data abstracted away from any concrete realization by
a positive probability measure. Some Euclidean theories are naturally presented
at this level even when no positive measure model is available. -/
structure GeneratingFunctionalModel (F : Formulation) where
  generatingFunctional : F.TestFunction → ℂ
  complexGeneratingFunctional : F.ComplexTestFunction → ℂ

/-- Positive measure representation with evaluation pairing against real test
functions. This is the amount of concrete measure-theoretic data needed to talk
about moments on simple tensors. -/
structure PairingMeasureModel (F : Formulation) (FieldConfig : Type uConfig) where
  instMeasurableSpaceFieldConfig : MeasurableSpace FieldConfig
  measure : @Measure FieldConfig instMeasurableSpaceFieldConfig
  isProbability : IsProbabilityMeasure measure
  pairing : FieldConfig → F.TestFunction → ℝ

attribute [instance] PairingMeasureModel.instMeasurableSpaceFieldConfig

/-- Strongest, most concrete Euclidean layer: a positive probability measure on
a configuration space together with generating-function data and the evaluation
pairing against test functions. This is the Glimm-Jaffe/Nelson style interface
used by `Pphi2`. -/
structure MeasureModel (F : Formulation) (FieldConfig : Type uConfig)
    extends GeneratingFunctionalModel F, PairingMeasureModel F FieldConfig

/-- Intermediate Schwinger layer on simple tensors `f₁ ⊗ ... ⊗ fₙ`, encoded as
tuples of one-point test functions. This is weaker than a genuine OS Schwinger
theory on `n`-point Schwartz functions. -/
structure TensorSchwingerModel (F : Formulation) where
  schwinger : (n : ℕ) → (Fin n → F.TestFunction) → ℂ

@[ext] theorem TensorSchwingerModel.ext
    {F : Formulation} {T₁ T₂ : TensorSchwingerModel F}
    (h : ∀ (n : ℕ) (f : Fin n → F.TestFunction),
      T₁.schwinger n f = T₂.schwinger n f) :
    T₁ = T₂ := by
  cases T₁
  cases T₂
  simp only at h
  congr
  funext n f
  exact h n f

/-- Original-OS-style Schwinger data: `n`-point functions as continuous linear
functionals on genuine `n`-point test-function spaces.

This is where the linear/topological structure missing from the bare
measure/tensor layers becomes mandatory. -/
structure DistributionalSchwingerModel (F : SchwingerFormulation) where
  tensorLift : (n : ℕ) → (Fin n → F.TestFunction) → F.NPointTestFunction n
  schwinger : (n : ℕ) → F.NPointTestFunction n →ₗ[ℂ] ℂ
  schwingerContinuous : ∀ n, Continuous (schwinger n)

/-- Bridge from a concrete measure model to simple-tensor moments. The actual
formula is canonical, but we keep the bridge separate from the bare
`PairingMeasureModel` interface so the comparison with moment packages stays
explicit in downstream developments.

No generic constructor is provided at this level: measurability and
integrability of the moment observables are genuine mathematical content, and
should be proved in concrete theories rather than hidden in a definitional
wrapper. -/
structure MeasureToTensorBridge (F : Formulation) {FieldConfig : Type uConfig}
    (M : PairingMeasureModel F FieldConfig) where
  tensorSchwinger : TensorSchwingerModel F
  compatible :
    ∀ (n : ℕ) (f : Fin n → F.TestFunction),
      tensorSchwinger.schwinger n f =
        ∫ ω, ∏ i, (M.pairing ω (f i) : ℂ) ∂M.measure

/-- Bridge from simple-tensor moments to genuine distributional Schwinger
functions. This is where one proves continuity and extension from tensors to the
full `n`-point Schwartz space. -/
structure TensorToDistributionalBridge
    (F : SchwingerFormulation) (T : TensorSchwingerModel F.toFormulation) where
  distributionalSchwinger : DistributionalSchwingerModel F
  compatible :
    ∀ (n : ℕ) (f : Fin n → F.TestFunction),
      distributionalSchwinger.schwinger n
          (distributionalSchwinger.tensorLift n f) =
        T.schwinger n f

/-- A named family of extra reconstruction hypotheses on distributional
Schwinger data.

The key point is that the specific analytic condition should be explicit in the
type, rather than hidden behind a bare anonymous `Prop` field. Later
instantiations can use predicates such as OS 1975 linear-growth conditions or
stronger route-specific substitutes. -/
abbrev ReconstructionHypothesis (F : SchwingerFormulation) :=
  DistributionalSchwingerModel F → Prop

/-- Additional input beyond bare Schwinger functions required to run an OS-style
reconstruction theorem. -/
structure ReconstructionInput (F : SchwingerFormulation)
    (Hypothesis : ReconstructionHypothesis F) where
  schwingerModel : DistributionalSchwingerModel F
  hypothesis : Hypothesis schwingerModel

end Common.QFT.Euclidean
