/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.TorusContinuumLimit.TorusInteractingLimit

/-!
# Nontriviality and interaction of the T² P(φ)₂ theory

The compact-torus T² theory **genuinely exists**: `torusInteractingLimit_exists`
(`TorusInteractingLimit.lean:441`, PROVED via Nelson tightness + Prokhorov) produces a real
subsequential weak limit `μ` of the interacting family `torusInteractingMeasure L N P mass`. This
file formulates non-triviality **against that genuine measure** — unlike the ℝ²/cylinder predicate
`IsPphi2Limit` (which is witnessed by `δ₀`, see the memory `pphi2-existence-vacuous-delta0`) and
unlike the free-floating `∃μ` of `pphi2_nontriviality`.

## Two distinct properties (do not conflate)
* **Non-degeneracy** `TorusIsNondegenerate` — `S₂(f,f) = ∫(ωf)² dμ > 0` for `f ≠ 0`: the limit is
  not concentrated at the zero field. **The free field also has this** — it is *not* the interacting
  criterion.
* **Interaction = non-Gaussianity** `TorusIsInteracting` — the **connected four-point function**
  (fourth cumulant) `u₄(f) = ∫(ωf)⁴ dμ − 3(∫(ωf)² dμ)² ≠ 0` for some `f`. For a Gaussian measure all
  `n ≥ 3` cumulants vanish, so `u₄ ≠ 0` is exactly what distinguishes an **interacting** theory from
  a free one. **This — the 4-point function — is the interacting criterion**, not `S₂`.

## Status
`IsTorusPphi2Limit` (the honest limit predicate) and `torusPphi2Limit_exists` (a genuine witness)
are **PROVED** here. `TorusIsNondegenerate` (route: free lower bound `‖f‖²_{H⁻¹} > 0` + Griffiths/FKG
domination) and `TorusIsInteracting` (route: Lebowitz 4-point inequality + uniform strict lattice
`u₄` bound, `d=2` super-renormalizable) are the genuine remaining content — the honest, correctly-
stated replacements for the broken ℝ² axioms `pphi2_nontriviality` and `continuumLimit_nonGaussian`.
-/

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-- **Honest T² limit predicate.** `μ` is a subsequential weak limit of the genuine interacting
torus family `torusInteractingMeasure L (φ n + 1) P mass`. Tying `μ` to the actual φ⁴ construction
(via `torusInteractingMeasure`) is what makes the statements below meaningful: neither `δ₀` nor the
free field is such a limit (for `P ≠ 0`). Witnessed by `torusInteractingLimit_exists`. -/
def IsTorusPphi2Limit (μ : Measure (Configuration (TorusTestFunction L)))
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∀ (f : Configuration (TorusTestFunction L) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
      Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass))
        atTop (nhds (∫ ω, f ω ∂μ))

/-- **Existence of a genuine T² P(φ)₂ limit measure.** Immediate from the proved
`torusInteractingLimit_exists`. This is the honest analogue of `pphi2_limit_exists`, but here the
witness is a real interacting limit, not `δ₀`. -/
theorem torusPphi2Limit_exists (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (μ : Measure (Configuration (TorusTestFunction L))) (_ : IsProbabilityMeasure μ),
      IsTorusPphi2Limit L μ P mass hmass := by
  obtain ⟨φ, μ, hmono, hprob, hconv⟩ := torusInteractingLimit_exists L P mass hmass
  exact ⟨μ, hprob, φ, hmono, hconv⟩

/-- The two-point Schwinger function `S₂(f,f) = ∫ (ωf)² dμ`. -/
noncomputable def torusTwoPoint (μ : Measure (Configuration (TorusTestFunction L)))
    (f : TorusTestFunction L) : ℝ :=
  ∫ ω, (ω f) ^ 2 ∂μ

/-- The **connected four-point function** (fourth cumulant) `u₄(f) = ∫(ωf)⁴ − 3(∫(ωf)²)²`. For a
Gaussian measure `∫(ωf)⁴ = 3(∫(ωf)²)²`, so `u₄ ≠ 0` witnesses non-Gaussianity (interaction). -/
noncomputable def torusConnectedFourPoint (μ : Measure (Configuration (TorusTestFunction L)))
    (f : TorusTestFunction L) : ℝ :=
  (∫ ω, (ω f) ^ 4 ∂μ) - 3 * (∫ ω, (ω f) ^ 2 ∂μ) ^ 2

/-- **Non-degeneracy** of `μ`: `S₂(f,f) > 0` for every `f ≠ 0` (the limit is not `δ₀`). NOTE: the
free field satisfies this too — it is *not* the interacting criterion. -/
def TorusIsNondegenerate (μ : Measure (Configuration (TorusTestFunction L))) : Prop :=
  ∀ f : TorusTestFunction L, f ≠ 0 → 0 < torusTwoPoint L μ f

/-- **Interaction (non-Gaussianity)** of `μ`: the connected four-point function is nonzero for some
test function. This — the **4-point** — is the criterion that the theory is genuinely interacting
(not free/Gaussian). -/
def TorusIsInteracting (μ : Measure (Configuration (TorusTestFunction L))) : Prop :=
  ∃ f : TorusTestFunction L, torusConnectedFourPoint L μ f ≠ 0

/-- **The honest headline: an interacting P(φ)₂ theory exists on T².** A probability measure that
(i) IS a genuine subsequential limit of the interacting torus family, (ii) is non-degenerate
(`S₂ > 0`), and (iii) is interacting (connected 4-point `≠ 0`). Neither `δ₀` (fails ii) nor the free
field (fails iii) can witness it.

Discharged here: (i) existence + the limit predicate (`torusPphi2Limit_exists`). Remaining genuine
content: (ii) `TorusIsNondegenerate` (free lower bound + Griffiths/FKG domination), and (iii)
`TorusIsInteracting` (the 4-point — Lebowitz inequality + uniform strict lattice `u₄` bound). These
replace the ill-posed ℝ² axioms `pphi2_nontriviality` (`∃μ`, free-field-satisfiable) and
`continuumLimit_nonGaussian` (`∃μ` on the δ₀-vacuous ℝ² predicate). -/
def TorusInteractingTheoryExists (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) : Prop :=
  ∃ (μ : Measure (Configuration (TorusTestFunction L))) (_ : IsProbabilityMeasure μ),
    IsTorusPphi2Limit L μ P mass hmass ∧ TorusIsNondegenerate L μ ∧ TorusIsInteracting L μ

end Pphi2
