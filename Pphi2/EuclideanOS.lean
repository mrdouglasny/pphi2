/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Generic Euclidean Osterwalder-Schrader Surface

This file defines the generating functional and Osterwalder-Schrader axioms
for an arbitrary Euclidean background, with reflection-positivity data carried
by a `EuclideanTimeStructure`.

The canonical `P(Φ)₂` surface in `Pphi2/OSAxioms.lean` is then just the
specialization to the distinguished 2D background.
-/

import Pphi2.Backgrounds.EuclideanTime
import Pphi2.GeneralResults.FunctionalAnalysis
import Mathlib.Analysis.Analytic.Basic

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

namespace EuclideanOS

/-- The distribution pairing `⟨ω, f⟩` between a tempered distribution and a real
Schwartz test function. -/
def distribPairing {B : EuclideanPlaneBackground}
    (ω : EuclideanPlaneBackground.Distribution B)
    (f : EuclideanPlaneBackground.RealTestFunction B) : ℝ :=
  ω f

/-- The generating functional `Z[f] = ∫ exp(i⟨ω, f⟩) dμ(ω)`. -/
def generatingFunctional {B : EuclideanPlaneBackground}
    (μ : Measure (EuclideanPlaneBackground.Distribution B)) [IsProbabilityMeasure μ]
    (f : EuclideanPlaneBackground.RealTestFunction B) : ℂ :=
  ∫ ω : EuclideanPlaneBackground.Distribution B, Complex.exp (Complex.I * ↑(ω f)) ∂μ

/-- `Re(Z[f]) = ∫ cos(⟨ω, f⟩) dμ`. This is Euler's formula plus commutation of
`Complex.reCLM` with the Bochner integral. -/
theorem generatingFunctional_re_eq_integral_cos {B : EuclideanPlaneBackground}
    (μ : Measure (EuclideanPlaneBackground.Distribution B)) [IsProbabilityMeasure μ]
    (f : EuclideanPlaneBackground.RealTestFunction B) :
    (generatingFunctional μ f).re =
      ∫ ω : EuclideanPlaneBackground.Distribution B, Real.cos (ω f) ∂μ := by
  simpa [generatingFunctional, EuclideanPlaneBackground.RealTestFunction,
    EuclideanPlaneBackground.Distribution] using
    (configuration_expIntegral_re_eq_integral_cos
      (E := SchwartzMap (EuclideanPlaneBackground.SpaceTime B) ℝ)
      (μ := (show Measure (Configuration (SchwartzMap (EuclideanPlaneBackground.SpaceTime B) ℝ))
        from μ))
      f)

/-- `Im(Z[f]) = ∫ sin(⟨ω, f⟩) dμ`. This is Euler's formula plus commutation of
`Complex.imCLM` with the Bochner integral. -/
theorem generatingFunctional_im_eq_integral_sin {B : EuclideanPlaneBackground}
    (μ : Measure (EuclideanPlaneBackground.Distribution B)) [IsProbabilityMeasure μ]
    (f : EuclideanPlaneBackground.RealTestFunction B) :
    (generatingFunctional μ f).im =
      ∫ ω : EuclideanPlaneBackground.Distribution B, Real.sin (ω f) ∂μ := by
  simpa [generatingFunctional, EuclideanPlaneBackground.RealTestFunction,
    EuclideanPlaneBackground.Distribution] using
    (configuration_expIntegral_im_eq_integral_sin
      (E := SchwartzMap (EuclideanPlaneBackground.SpaceTime B) ℝ)
      (μ := (show Measure (Configuration (SchwartzMap (EuclideanPlaneBackground.SpaceTime B) ℝ))
        from μ))
      f)

/-- Extract the real part of a complex Schwartz function as a real Schwartz
function. -/
def schwartzRe {B : EuclideanPlaneBackground}
    (J : EuclideanPlaneBackground.ComplexTestFunction B) :
    EuclideanPlaneBackground.RealTestFunction B :=
  J.postcompCLM Complex.reCLM

/-- Extract the imaginary part of a complex Schwartz function as a real
Schwartz function. -/
def schwartzIm {B : EuclideanPlaneBackground}
    (J : EuclideanPlaneBackground.ComplexTestFunction B) :
    EuclideanPlaneBackground.RealTestFunction B :=
  J.postcompCLM Complex.imCLM

/-- The complex generating functional `Z[J]` for a complex Schwartz source. -/
def generatingFunctionalℂ {B : EuclideanPlaneBackground}
    (μ : Measure (EuclideanPlaneBackground.Distribution B)) [IsProbabilityMeasure μ]
    (J : EuclideanPlaneBackground.ComplexTestFunction B) : ℂ :=
  let f_re := schwartzRe J
  let f_im := schwartzIm J
  ∫ ω : EuclideanPlaneBackground.Distribution B,
      Complex.exp (Complex.I * ((ω f_re : ℂ) + Complex.I * (ω f_im : ℂ))) ∂μ

/-- **OS0 (Analyticity):** `Z[Σ zᵢJᵢ]` is entire analytic in the coefficients. -/
def OS0_Analyticity {B : EuclideanPlaneBackground}
    (μ : Measure (EuclideanPlaneBackground.Distribution B)) [IsProbabilityMeasure μ] :
    Prop :=
  ∀ (n : ℕ) (J : Fin n → EuclideanPlaneBackground.ComplexTestFunction B),
    AnalyticOn ℂ
      (fun z : Fin n → ℂ => generatingFunctionalℂ μ (∑ i, z i • J i))
      Set.univ

/-- **OS1 (Regularity):** the complex generating functional satisfies an
exponential Schwartz-norm bound. -/
def OS1_Regularity {B : EuclideanPlaneBackground}
    (μ : Measure (EuclideanPlaneBackground.Distribution B)) [IsProbabilityMeasure μ] :
    Prop :=
  ∃ (p : ℝ) (c : ℝ), 1 ≤ p ∧ p ≤ 2 ∧ c > 0 ∧
    ∀ (f : EuclideanPlaneBackground.ComplexTestFunction B),
      ‖generatingFunctionalℂ μ f‖ ≤
        Real.exp (c * (∫ x, ‖f x‖ ∂volume + ∫ x, ‖f x‖ ^ p ∂volume))

/-- **OS2 (Euclidean invariance):** the generating functional is invariant
under Euclidean motions of the background. -/
def OS2_EuclideanInvariance {B : EuclideanPlaneBackground}
    (μ : Measure (EuclideanPlaneBackground.Distribution B)) [IsProbabilityMeasure μ] :
    Prop :=
  ∀ (g : EuclideanPlaneBackground.Motion B)
    (f : EuclideanPlaneBackground.ComplexTestFunction B),
    generatingFunctionalℂ μ f =
      generatingFunctionalℂ μ (EuclideanPlaneBackground.actionComplex g f)

/-- **OS3 (Reflection positivity):** the reflection-positivity matrix from the
positive-time region is positive semidefinite. -/
def OS3_ReflectionPositivity {B : EuclideanPlaneBackground}
    (T : EuclideanTimeStructure B)
    (μ : Measure (EuclideanPlaneBackground.Distribution B)) [IsProbabilityMeasure μ] :
    Prop :=
  ∀ (n : ℕ) (f : Fin n → T.positiveTimeSubmodule) (c : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j *
      (generatingFunctional μ
        ((f i).val - T.reflectOnRealTestFunctions ((f j).val))).re

/-- **OS4 (Clustering):** correlations factor at large spacelike separation. -/
def OS4_Clustering {B : EuclideanPlaneBackground}
    (μ : Measure (EuclideanPlaneBackground.Distribution B)) [IsProbabilityMeasure μ] :
    Prop :=
  ∀ (f g : EuclideanPlaneBackground.RealTestFunction B) (ε : ℝ), ε > 0 →
    ∃ (R : ℝ), R > 0 ∧
      ∀ (a : EuclideanPlaneBackground.SpaceTime B), ‖a‖ > R →
        ‖generatingFunctional μ (f + EuclideanPlaneBackground.translate B a g)
          - generatingFunctional μ f * generatingFunctional μ g‖ < ε

/-- **OS4 (Ergodicity):** time averages along the distinguished time axis
converge to factorized expectations. -/
def OS4_Ergodicity {B : EuclideanPlaneBackground}
    (T : EuclideanTimeStructure B)
    (μ : Measure (EuclideanPlaneBackground.Distribution B)) [IsProbabilityMeasure μ] :
    Prop :=
  ∀ (f g : EuclideanPlaneBackground.RealTestFunction B),
    Filter.Tendsto
      (fun Tmax : ℝ => (1 / Tmax) * ∫ t in Set.Icc (0 : ℝ) Tmax,
        (generatingFunctional μ
          (f + EuclideanPlaneBackground.translate B (T.timeTranslation t) g)).re)
      Filter.atTop
      (nhds ((generatingFunctional μ f).re * (generatingFunctional μ g).re))

/-- Full Osterwalder-Schrader axiom bundle for a Euclidean background equipped
with time-structure data. -/
structure SatisfiesFullOS {B : EuclideanPlaneBackground}
    (T : EuclideanTimeStructure B)
    (μ : Measure (EuclideanPlaneBackground.Distribution B)) [IsProbabilityMeasure μ] :
    Prop where
  os0 : OS0_Analyticity (B := B) μ
  os1 : OS1_Regularity (B := B) μ
  os2 : OS2_EuclideanInvariance (B := B) μ
  os3 : OS3_ReflectionPositivity T μ
  os4_clustering : OS4_Clustering (B := B) μ
  os4_ergodicity : OS4_Ergodicity T μ

end EuclideanOS

end Pphi2
