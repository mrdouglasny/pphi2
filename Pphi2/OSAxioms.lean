/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Osterwalder-Schrader Axioms for `P(Φ)₂`

This file is the canonical 2D specialization of the generic Euclidean
OS/QFT layer in `Pphi2.EuclideanOS`, for probability measures on
`S'(ℝ²) = Configuration (ContinuumTestFunction 2)`.

The public surface remains the same: `generatingFunctional`,
`OS0_Analyticity`, `SatisfiesFullOS`, and the other standard names are still
exported here for the distinguished plane background used by `P(Φ)₂`.

The concrete formulas match those in `OSforGFF/OS_Axioms.lean`, adapted from
`d = 4` to `d = 2`, while factoring through the shared abstraction layer in
`Common.QFT.*`.

## P vs X (layering)

- **P:** `EuclideanSpace`, `SchwartzMap`, `MeasureTheory`, and the `Backgrounds/EuclideanPlane`
  abbreviations — see `ContinuumSpaceTime_eq` and companion lemmas (definitional equality to Mathlib).
- **X:** this file’s **OS0–OS4 bundles** for `FieldConfig2` / `TestFunction2`, i.e. the
  Osterwalder–Schrader (1973, 1975) axiom pattern specialized to the `P(Φ)₂` plane background.

Reference map: `docs/mathlib_prerequisite_layering.md`.
-/

import Pphi2.EuclideanOS
import Pphi2.Backgrounds.EuclideanPlane2D
import Pphi2.ContinuumLimit.AxiomInheritance

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

/-! ## Canonical 2D Specialization -/

/-- The distribution pairing ⟨ω, f⟩ for ω ∈ S'(ℝ²), f ∈ S(ℝ²). -/
abbrev distribPairing (ω : FieldConfig2) (f : TestFunction2) : ℝ :=
  EuclideanOS.distribPairing (B := plane2Background) ω f

/-- The generating functional `Z[f] = ∫ exp(i⟨ω, f⟩) dμ(ω)`. -/
abbrev generatingFunctional
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (f : TestFunction2) : ℂ :=
  EuclideanOS.generatingFunctional (B := plane2Background) μ f

abbrev schwartzRe (J : TestFunction2ℂ) : TestFunction2 :=
  EuclideanOS.schwartzRe (B := plane2Background) J

abbrev schwartzIm (J : TestFunction2ℂ) : TestFunction2 :=
  EuclideanOS.schwartzIm (B := plane2Background) J

abbrev generatingFunctionalℂ
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (J : TestFunction2ℂ) : ℂ :=
  EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ J

/-- **OS0 (Analyticity):** `Z[Σ zᵢJᵢ]` is entire analytic in the coefficients. -/
abbrev OS0_Analyticity
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] : Prop :=
  EuclideanOS.OS0_Analyticity (B := plane2Background) μ

abbrev OS1_Regularity
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] : Prop :=
  EuclideanOS.OS1_Regularity (B := plane2Background) μ

abbrev OS2_EuclideanInvariance
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] : Prop :=
  EuclideanOS.OS2_EuclideanInvariance (B := plane2Background) μ

abbrev OS3_ReflectionPositivity
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] : Prop :=
  EuclideanOS.OS3_ReflectionPositivity plane2TimeStructure μ

abbrev OS4_Clustering
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] : Prop :=
  EuclideanOS.OS4_Clustering (B := plane2Background) μ

abbrev OS4_Ergodicity
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] : Prop :=
  EuclideanOS.OS4_Ergodicity plane2TimeStructure μ

abbrev SatisfiesFullOS
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ] : Prop :=
  EuclideanOS.SatisfiesFullOS plane2TimeStructure μ

end Pphi2

end
