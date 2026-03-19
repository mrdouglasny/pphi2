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
These follow from `periodizeCLM_comp_schwartzTranslation` and
`periodizeCLM_comp_schwartzReflection` (in gaussian-field) combined
with the NTP functor properties of `nuclearTensorProduct_mapCLM_general`.
Axiomatized because the NTP functor is also axiomatized. -/

/-- The embedding intertwines cylinder time translation with torus time translation:
`embed(T_{0,τ} f) = T_{τ,0}(embed f)`. -/
axiom cylinderToTorusEmbed_comp_timeTranslation (τ : ℝ)
    (f : CylinderTestFunction Ls) :
    cylinderToTorusEmbed Lt Ls (cylinderTranslation Ls 0 τ f) =
    asymTorusTranslation Lt Ls (τ, 0) (cylinderToTorusEmbed Lt Ls f)

/-- The embedding intertwines cylinder time reflection with torus time reflection:
`embed(Θ f) = Θ_torus(embed f)`. -/
axiom cylinderToTorusEmbed_comp_timeReflection
    (f : CylinderTestFunction Ls) :
    cylinderToTorusEmbed Lt Ls (cylinderTimeReflection Ls f) =
    asymTorusTimeReflection Lt Ls (cylinderToTorusEmbed Lt Ls f)

end Pphi2
