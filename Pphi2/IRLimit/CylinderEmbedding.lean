/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder → Torus Embedding for Route B' IR Limit

Defines the embedding of cylinder test functions into asymmetric torus
test functions via periodization of the temporal factor, and the induced
pullback on configurations and measures.

`CylinderTestFunction Ls = NTP(SMC_Ls, SchwartzMap ℝ ℝ)` — spatial × temporal
`AsymTorusTestFunction Lt Ls = NTP(SMC_Lt, SMC_Ls)` — temporal × spatial

The embedding periodizes the temporal factor and swaps to match conventions.

## References

- Glimm-Jaffe, *Quantum Physics*, §19 (finite → infinite volume)
-/

import Pphi2.IRLimit.Periodization
import Pphi2.AsymTorus.AsymTorusEmbedding
import Nuclear.GeneralMapCLM
import Cylinder.Basic

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-! ## Cylinder → Torus Embedding

`CylinderTestFunction Ls = NTP(SMC_Ls, SchwartzMap ℝ ℝ)` — spatial × temporal
`AsymTorusTestFunction Lt Ls = NTP(SMC_Lt, SMC_Ls)` — temporal × spatial

The embedding:
1. Map via `id ⊗ periodize`: `NTP(SMC_Ls, Schwartz ℝ) → NTP(SMC_Ls, SMC_Lt)`
2. Swap: `NTP(SMC_Ls, SMC_Lt) → NTP(SMC_Lt, SMC_Ls)`

Uses `nuclearTensorProduct_mapCLM_general` (from gaussian-field) for step 1
and `nuclearTensorProduct_swapCLM` for step 2. -/

/-- Embed cylinder test functions into asymmetric torus test functions.
Periodizes the temporal (Schwartz) factor and swaps factor order. -/
def cylinderToTorusEmbed :
    CylinderTestFunction Ls →L[ℝ] AsymTorusTestFunction Lt Ls :=
  (nuclearTensorProduct_swapCLM
    (E₁ := SmoothMap_Circle Ls ℝ) (E₂ := SmoothMap_Circle Lt ℝ)).comp
  (nuclearTensorProduct_mapCLM_general
    (ContinuousLinearMap.id ℝ (SmoothMap_Circle Ls ℝ))
    (periodizeCLM Lt))

/-- On pure tensors, `cylinderToTorusEmbed` is exactly "periodize time and swap". -/
@[simp] theorem cylinderToTorusEmbed_pure
    (g : SmoothMap_Circle Ls ℝ) (h : SchwartzMap ℝ ℝ) :
    cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g h) =
      NuclearTensorProduct.pure (periodizeCLM Lt h) g := by
  simp [cylinderToTorusEmbed, ContinuousLinearMap.comp_apply,
    nuclearTensorProduct_mapCLM_general_pure, nuclearTensorProduct_swapCLM_pure]

/-- The pullback on configurations: given a torus configuration ω,
produce a cylinder configuration by precomposing with the embedding. -/
def cylinderPullback
    (ω : Configuration (AsymTorusTestFunction Lt Ls)) :
    Configuration (CylinderTestFunction Ls) where
  toFun f := ω (cylinderToTorusEmbed Lt Ls f)
  map_add' f g := by simp [map_add]
  map_smul' r f := by simp [map_smul]
  cont := ω.cont.comp (cylinderToTorusEmbed Lt Ls).cont

/-- The pushforward measure on cylinder configurations. -/
def cylinderPullbackMeasure
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls))) :
    Measure (Configuration (CylinderTestFunction Ls)) :=
  Measure.map (cylinderPullback Lt Ls) μ

/-- Evaluation formula. -/
@[simp] theorem cylinderPullback_eval
    (ω : Configuration (AsymTorusTestFunction Lt Ls))
    (f : CylinderTestFunction Ls) :
    (cylinderPullback Lt Ls ω) f = ω (cylinderToTorusEmbed Lt Ls f) :=
  rfl

/-- Second moments on the pulled-back measure equal torus second moments for the embedded
test function (`MeasureTheory.integral_map` and `cylinderPullback_eval`). -/
theorem cylinderPullbackMeasure_integral_sq
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (f : CylinderTestFunction Ls) :
    ∫ ω, (ω f) ^ 2 ∂(cylinderPullbackMeasure Lt Ls μ) =
    ∫ ω, (ω (cylinderToTorusEmbed Lt Ls f)) ^ 2 ∂μ := by
  unfold cylinderPullbackMeasure
  have hmeas : Measurable (cylinderPullback Lt Ls) :=
    configuration_measurable_of_eval_measurable _
      (fun φ => configuration_eval_measurable _)
  have hf_sq_sm : StronglyMeasurable
      (fun ω : Configuration (CylinderTestFunction Ls) => (ω f) ^ 2) :=
    ((configuration_eval_measurable f).pow_const 2).stronglyMeasurable
  rw [integral_map_of_stronglyMeasurable hmeas hf_sq_sm]
  simp_rw [cylinderPullback_eval]

/-- The pullback is continuous, hence measurable. -/
theorem cylinderPullback_continuous :
    Continuous (cylinderPullback Lt Ls) := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  exact WeakDual.eval_continuous (cylinderToTorusEmbed Lt Ls f)

-- Note: Measurability of cylinderPullback follows from continuity
-- once OpensMeasurableSpace is available for the configuration space.

/-! ## Intertwining with symmetries

The embedding commutes with time translation and time reflection.
Proved from `periodizeCLM_comp_schwartzTranslation` and
`periodizeCLM_comp_schwartzReflection` (in gaussian-field) combined
with the NTP functor axioms `nuclearTensorProduct_mapCLM_general_pure`
and `nuclearTensorProduct_swapCLM_pure`, extended to all elements via
the DyninMityaginSpace expansion (pure tensor density). -/

/-- Helper: two CLMs from a CylinderTestFunction NTP that agree on all pure tensors
produce equal results on every element.

Strategy: for `T, S : NTP(E₁, E₂) →L[ℝ] NTP(F₁, F₂)`, to show `T x = S x`,
use NTP ext to reduce to `.val n`, then `coeffCLM n ∘ T` is a CLM to ℝ so we can use
`rapidDecay_expansion` on the input, reducing to `basisVec m = pure(ψ_a, ψ_b)`. -/
private theorem cylinderToTorus_clm_ext_of_pure
    (T S : CylinderTestFunction Ls →L[ℝ] AsymTorusTestFunction Lt Ls)
    (h : ∀ (g : SmoothMap_Circle Ls ℝ) (f : SchwartzMap ℝ ℝ),
      T (NuclearTensorProduct.pure g f) = S (NuclearTensorProduct.pure g f)) :
    T = S := by
  ext x n
  -- (T x).val n = coeffCLM n (T x), expand via rapidDecay_expansion
  change (T x).val n = (S x).val n
  have hT := RapidDecaySeq.rapidDecay_expansion
    ((RapidDecaySeq.coeffCLM n).comp T) x
  have hS := RapidDecaySeq.rapidDecay_expansion
    ((RapidDecaySeq.coeffCLM n).comp S) x
  simp only [ContinuousLinearMap.comp_apply] at hT hS
  change (T x).val n = _ at hT
  change (S x).val n = _ at hS
  rw [hT, hS]
  congr 1; ext m; congr 1
  -- basisVec m = pure(ψ_a, ψ_b) under biorthogonality
  have hbv := NuclearTensorProduct.basisVec_eq_pure
    (DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis (E := SmoothMap_Circle Ls ℝ))
    (DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis (E := SchwartzMap ℝ ℝ))
    m
  rw [hbv]
  exact congrArg (fun y => y.val n) (h _ _)

/-- The embedding intertwines cylinder time translation with torus time translation:
`embed(T_{0,τ} f) = T_{τ,0}(embed f)`. -/
theorem cylinderToTorusEmbed_comp_timeTranslation (τ : ℝ)
    (f : CylinderTestFunction Ls) :
    cylinderToTorusEmbed Lt Ls (cylinderTranslation Ls 0 τ f) =
    asymTorusTranslation Lt Ls (τ, 0) (cylinderToTorusEmbed Lt Ls f) := by
  -- Both sides are CLMs in f. Show they agree on all pure tensors and extend by density.
  have key : cylinderToTorusEmbed Lt Ls ∘L cylinderTranslation Ls 0 τ =
      asymTorusTranslation Lt Ls (τ, 0) ∘L cylinderToTorusEmbed Lt Ls := by
    apply cylinderToTorus_clm_ext_of_pure
    intro g h
    -- LHS: embed(T_{0,τ}(pure g h))
    simp only [ContinuousLinearMap.comp_apply]
    -- Unfold cylinderTranslation to mapCLM and compute on pure tensor
    have hdef : cylinderTranslation Ls 0 τ = nuclearTensorProduct_mapCLM
      (circleTranslation Ls 0) (schwartzTranslation τ) := rfl
    rw [hdef, nuclearTensorProduct_mapCLM_pure]
    -- Unfold cylinderToTorusEmbed and compute on pure tensors
    change cylinderToTorusEmbed Lt Ls
        (NuclearTensorProduct.pure
          (circleTranslation Ls 0 g) (schwartzTranslation τ h)) =
      asymTorusTranslation Lt Ls (τ, 0)
        (cylinderToTorusEmbed Lt Ls
          (NuclearTensorProduct.pure g h))
    simp only [cylinderToTorusEmbed, ContinuousLinearMap.comp_apply]
    rw [nuclearTensorProduct_mapCLM_general_pure, nuclearTensorProduct_swapCLM_pure,
        nuclearTensorProduct_mapCLM_general_pure, nuclearTensorProduct_swapCLM_pure,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.id_apply]
    -- LHS: pure (periodize (schwartzTranslation τ h)) (circleTranslation Ls 0 g)
    -- RHS: asymTorusTranslation (τ,0) (pure (periodize h) g)
    --     = mapCLM (circleTranslation Lt τ) (circleTranslation Ls 0) (pure (periodize h) g)
    --     = pure (circleTranslation Lt τ (periodize h)) (circleTranslation Ls 0 g)
    change NuclearTensorProduct.pure
        (periodizeCLM Lt (schwartzTranslation τ h))
        (circleTranslation Ls 0 g) =
      asymTorusTranslation Lt Ls (τ, 0)
        (NuclearTensorProduct.pure (periodizeCLM Lt h) g)
    rw [periodizeCLM_comp_schwartzTranslation]
    simp only [asymTorusTranslation]
    rw [nuclearTensorProduct_mapCLM_pure]
  exact ContinuousLinearMap.ext_iff.mp key f

/-- The embedding intertwines cylinder time reflection with torus time reflection:
`embed(Θ f) = Θ_torus(embed f)`. -/
theorem cylinderToTorusEmbed_comp_timeReflection
    (f : CylinderTestFunction Ls) :
    cylinderToTorusEmbed Lt Ls (cylinderTimeReflection Ls f) =
    asymTorusTimeReflection Lt Ls (cylinderToTorusEmbed Lt Ls f) := by
  have key : cylinderToTorusEmbed Lt Ls ∘L cylinderTimeReflection Ls =
      asymTorusTimeReflection Lt Ls ∘L cylinderToTorusEmbed Lt Ls := by
    apply cylinderToTorus_clm_ext_of_pure
    intro g h
    simp only [ContinuousLinearMap.comp_apply]
    -- cylinderTimeReflection Ls (pure g h)
    rw [show cylinderTimeReflection Ls = nuclearTensorProduct_mapCLM
      (ContinuousLinearMap.id ℝ (SmoothMap_Circle Ls ℝ)) schwartzReflection from rfl,
      nuclearTensorProduct_mapCLM_pure, ContinuousLinearMap.id_apply]
    -- embed(pure g (Θh))
    show cylinderToTorusEmbed Lt Ls
        (NuclearTensorProduct.pure g (schwartzReflection h)) =
      asymTorusTimeReflection Lt Ls (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g h))
    simp only [cylinderToTorusEmbed, ContinuousLinearMap.comp_apply]
    rw [nuclearTensorProduct_mapCLM_general_pure, nuclearTensorProduct_swapCLM_pure,
        nuclearTensorProduct_mapCLM_general_pure, nuclearTensorProduct_swapCLM_pure,
        ContinuousLinearMap.id_apply, periodizeCLM_comp_schwartzReflection]
    -- Goal: pure (circleReflection Lt (periodize h)) g =
    --       asymTorusTimeReflection Lt Ls (pure (periodize h) g)
    simp only [asymTorusTimeReflection]
    rw [nuclearTensorProduct_mapCLM_pure, ContinuousLinearMap.id_apply]
  exact ContinuousLinearMap.ext_iff.mp key f

end Pphi2
