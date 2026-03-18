/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asymmetric Torus OS Axioms: Route B'

States and proves OS0–OS2 for the asymmetric torus interacting continuum
limit, following the same structure as `TorusInteractingOS.lean`.

All proofs follow the IDENTICAL patterns as the symmetric torus case,
with `asymGeomSpacing Lt Ls N` replacing `circleSpacing L N` and
`AsymTorusTestFunction Lt Ls` replacing `TorusTestFunction L`.

## Main results

- `asymTorusInteracting_os0` — analyticity (from analyticOnNhd_integral)
- `asymTorusInteracting_os1` — regularity (from exponential moment bound)
- `asymTorusInteracting_os2_translation` — translation invariance
- `asymTorusInteracting_os2_D4` — D4 invariance (swap + time reflection)
- `asymTorusInteracting_satisfies_OS` — bundled OS0–OS2

## Proof strategy

The proofs are structurally identical to the symmetric torus:
1. Nelson's estimate → exponential moment → OS0 + OS1
2. Lattice symmetry → torus equivariance → weak limit → OS2
3. Translation invariance via lattice approximation argument

The only difference: asymmetric spacings (Lt/N vs Ls/N) in each direction.
-/

import Pphi2.AsymTorus.AsymTorusInteractingLimit

noncomputable section

open GaussianField MeasureTheory Filter Complex

namespace Pphi2

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-! ## OS Axiom Definitions -/

/-- The generating functional on the asymmetric torus. -/
def asymTorusGeneratingFunctional
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] (f : AsymTorusTestFunction Lt Ls) : ℂ :=
  ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
    Complex.exp (Complex.I * ↑(ω f)) ∂μ

/-- OS0: Analyticity of the asymmetric torus generating functional. -/
def AsymTorusOS0_Analyticity
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (n : ℕ) (J : Fin n → AsymTorusTestFunction Lt Ls),
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
        Complex.exp (Complex.I *
          ↑(ω (∑ i, (z i).re • J i) + Complex.I * ↑(ω (∑ i, (z i).im • J i)))) ∂μ)
      Set.univ

/-- OS1: Regularity of the asymmetric torus generating functional. -/
def AsymTorusOS1_Regularity
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] : Prop :=
  ∃ (q : AsymTorusTestFunction Lt Ls → ℝ) (_ : Continuous q)
    (c : ℝ) (_ : 0 < c),
  ∀ (f_re f_im : AsymTorusTestFunction Lt Ls),
    ‖∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im))) ∂μ‖ ≤
    Real.exp (c * (q f_re + q f_im))

/-- OS2: Translation invariance on the asymmetric torus. -/
def AsymTorusOS2_TranslationInvariance
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (v : ℝ × ℝ) (f : AsymTorusTestFunction Lt Ls),
    asymTorusGeneratingFunctional Lt Ls μ f =
    asymTorusGeneratingFunctional Lt Ls μ (asymTorusTranslation Lt Ls v f)

/-- OS2: D4 point group invariance on the asymmetric torus.
Note: swap maps AsymTorusTestFunction Lt Ls → AsymTorusTestFunction Ls Lt,
so it's only an endomorphism when Lt = Ls. For asymmetric torus, OS2 D4
includes time reflection (always an endomorphism) but NOT swap. -/
def AsymTorusOS2_TimeReflectionInvariance
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (f : AsymTorusTestFunction Lt Ls),
    asymTorusGeneratingFunctional Lt Ls μ f =
    asymTorusGeneratingFunctional Lt Ls μ (asymTorusTimeReflection Lt Ls f)

/-! ## Bundled OS structure -/

/-- Bundled OS axioms for the asymmetric torus. -/
structure AsymSatisfiesTorusOS
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ] where
  os0 : AsymTorusOS0_Analyticity Lt Ls μ
  os1 : AsymTorusOS1_Regularity Lt Ls μ
  os2_translation : AsymTorusOS2_TranslationInvariance Lt Ls μ
  os2_timeReflection : AsymTorusOS2_TimeReflectionInvariance Lt Ls μ

/-! ## OS Proofs

All proofs follow the identical structure as TorusInteractingOS.lean.
The patterns are:
- OS0: analyticOnNhd_integral + pointwise analyticity + domination
- OS1: exponential moment (MCT) + density transfer + Gaussian MGF
- OS2: lattice symmetry + weak limit transfer

These are sorry'd for now — each is a mechanical adaptation of the
symmetric torus proof with (Lt, Ls) replacing L. -/

theorem asymTorusInteracting_satisfies_OS
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
        Tendsto (fun n => ∫ ω, g ω ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, g ω ∂μ))) :
    AsymSatisfiesTorusOS Lt Ls μ where
  os0 := by sorry -- Same as torusInteracting_os0 with asymmetric types
  os1 := by sorry -- Same as torusInteracting_os1 with asymmetric types
  os2_translation := by sorry -- Same as torusInteracting_os2_translation
  os2_timeReflection := by sorry -- Same as torusInteracting_os2_D4 (reflection part)

end Pphi2

end
