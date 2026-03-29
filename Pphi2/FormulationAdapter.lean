import Common.QFT.Euclidean.Formulations
import Pphi2.OSAxioms

/-!
# `Pphi2` as a concrete Euclidean measure model

This file exports the current `Pphi2` construction into the shared
formulation-layer interfaces.

At present, `Pphi2` naturally lives at the concrete positive-measure level:
its primary objects are probability measures on `S'(ℝ²)` together with their
generating functionals. The associated simple-tensor Schwinger moments are
canonical and are recorded here explicitly. A genuine distributional
Schwinger-function interface is intentionally left for a later bridge.
-/

noncomputable section

open GaussianField MeasureTheory
open Common.QFT.Euclidean

namespace Pphi2

/-- The one-point Euclidean test-function data used by the `Pphi2` scalar
construction. -/
def pphi2Formulation : Formulation where
  SpaceTime := SpaceTime2
  TestFunction := TestFunction2
  ComplexTestFunction := TestFunction2ℂ
  positiveTimeTestFunctions := positiveTimeSubmodule2.carrier

/-- Any `Pphi2` probability measure on `S'(ℝ²)` gives a concrete
`MeasureModel` in the shared formulation layer. -/
def pphi2MeasureModel
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] :
    MeasureModel pphi2Formulation FieldConfig2 where
  generatingFunctional := generatingFunctional μ
  complexGeneratingFunctional := generatingFunctionalℂ μ
  instMeasurableSpaceFieldConfig := instMeasurableSpaceConfiguration
  measure := μ
  isProbability := inferInstance
  pairing := distribPairing

/-- The underlying pairing-based measure model carried by a `Pphi2` measure. -/
abbrev pphi2PairingMeasureModel
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] :
    PairingMeasureModel pphi2Formulation FieldConfig2 :=
  (pphi2MeasureModel μ).toPairingMeasureModel

/-- The simple-tensor Schwinger moments associated to a `Pphi2` measure.

This remains an explicit theory-level construction rather than a generic
definition from `PairingMeasureModel`: moment finiteness is genuine content and
should stay visible in concrete adapters. -/
def pphi2TensorSchwingerModel
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] :
    TensorSchwingerModel pphi2Formulation where
  schwinger _n f := ∫ ω : FieldConfig2, ∏ i, (ω (f i) : ℂ) ∂μ

/-- The canonical bridge from a concrete `Pphi2` measure to its simple-tensor
Schwinger moments. -/
def pphi2MeasureToTensorBridge
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] :
    MeasureToTensorBridge pphi2Formulation (pphi2PairingMeasureModel μ) where
  tensorSchwinger := pphi2TensorSchwingerModel μ
  compatible := by
    intro _n f
    rfl

end Pphi2
