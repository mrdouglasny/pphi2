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

/-- The **general connected four-point (Ursell) function**
`u₄(f₁,f₂,f₃,f₄) = ⟨φ₁φ₂φ₃φ₄⟩ − ⟨φ₁φ₂⟩⟨φ₃φ₄⟩ − ⟨φ₁φ₃⟩⟨φ₂φ₄⟩ − ⟨φ₁φ₄⟩⟨φ₂φ₃⟩`, the fourth
joint cumulant. It vanishes identically iff the four-point Schwinger function factorizes into
two-point functions — the defining property of a **Gaussian (free)** field (Isserlis/Wick). So
`u₄ ≠ 0` for some arguments is *exactly* non-Gaussianity, i.e. interaction. -/
noncomputable def torusUrsell4 (μ : Measure (Configuration (TorusTestFunction L)))
    (f₁ f₂ f₃ f₄ : TorusTestFunction L) : ℝ :=
  (∫ ω, (ω f₁) * (ω f₂) * (ω f₃) * (ω f₄) ∂μ)
    - (∫ ω, (ω f₁) * (ω f₂) ∂μ) * (∫ ω, (ω f₃) * (ω f₄) ∂μ)
    - (∫ ω, (ω f₁) * (ω f₃) ∂μ) * (∫ ω, (ω f₂) * (ω f₄) ∂μ)
    - (∫ ω, (ω f₁) * (ω f₄) ∂μ) * (∫ ω, (ω f₂) * (ω f₃) ∂μ)

/-- The **diagonal** connected four-point / fourth cumulant `u₄(f) = ∫(ωf)⁴ − 3(∫(ωf)²)²`. The
computable special case of `torusUrsell4` used by the interacting test (`torusUrsell4_diag`). For a
Gaussian measure `∫(ωf)⁴ = 3(∫(ωf)²)²`, so `u₄(f) ≠ 0` witnesses non-Gaussianity. It is
scale-homogeneous of degree 4 (`u₄(c·f) = c⁴ u₄(f)`), and vanishes at `δ₀` (all moments zero), so
the test below excludes both the free field (`u₄ = 0`) and the trivial measure. -/
noncomputable def torusConnectedFourPoint (μ : Measure (Configuration (TorusTestFunction L)))
    (f : TorusTestFunction L) : ℝ :=
  (∫ ω, (ω f) ^ 4 ∂μ) - 3 * (∫ ω, (ω f) ^ 2 ∂μ) ^ 2

/-- The diagonal cumulant is the diagonal restriction of the general Ursell function: the three
Wick pairings all collapse to `⟨(ωf)²⟩²`. So the simple `torusConnectedFourPoint` test is genuinely
a test of the full fourth-cumulant tensor (by polarization, `u₄ ≢ 0 ↔ ∃ f, u₄(f,f,f,f) ≠ 0`). -/
theorem torusUrsell4_diag (μ : Measure (Configuration (TorusTestFunction L)))
    (f : TorusTestFunction L) :
    torusUrsell4 L μ f f f f = torusConnectedFourPoint L μ f := by
  simp only [torusUrsell4, torusConnectedFourPoint]
  have h4 : ∀ ω : Configuration (TorusTestFunction L),
      (ω f) * (ω f) * (ω f) * (ω f) = (ω f) ^ 4 := fun ω => by ring
  have h2 : ∀ ω : Configuration (TorusTestFunction L), (ω f) * (ω f) = (ω f) ^ 2 := fun ω => by ring
  simp_rw [h4, h2]
  ring

/-- **Non-degeneracy** of `μ`: `S₂(f,f) > 0` for every `f ≠ 0` (the limit is not `δ₀`). NOTE: the
free field satisfies this too — it is *not* the interacting criterion. -/
def TorusIsNondegenerate (μ : Measure (Configuration (TorusTestFunction L))) : Prop :=
  ∀ f : TorusTestFunction L, f ≠ 0 → 0 < torusTwoPoint L μ f

/-- **Interacting test (non-Gaussianity).** `μ` is interacting iff its connected four-point function
is nonzero for some test function — equivalently (`torusUrsell4_diag` + polarization), the
four-point Schwinger function does not factorize, so `μ` is not Gaussian. This — the **4-point** —
is the criterion for genuine interaction; `S₂ > 0` (which the free field also has) is not. -/
def TorusIsInteracting (μ : Measure (Configuration (TorusTestFunction L))) : Prop :=
  ∃ f : TorusTestFunction L, torusConnectedFourPoint L μ f ≠ 0

/-- **Interacting test, sharp (Lebowitz sign).** For the repulsive (ferromagnetic, even) `φ⁴`
interaction the **Lebowitz inequality** forces `u₄ ≤ 0`, so the genuine physical statement is
strict negativity of the connected four-point for some test function. This is the form the proof
plan delivers (a uniform strict lattice bound surviving `a → 0`); it implies `TorusIsInteracting`
via `ne_of_lt`. -/
def TorusIsInteractingStrict (μ : Measure (Configuration (TorusTestFunction L))) : Prop :=
  ∃ f : TorusTestFunction L, torusConnectedFourPoint L μ f < 0

/-- The sharp (Lebowitz) interacting test implies the bare non-Gaussianity test. -/
theorem TorusIsInteractingStrict.toInteracting
    {μ : Measure (Configuration (TorusTestFunction L))}
    (h : TorusIsInteractingStrict L μ) : TorusIsInteracting L μ :=
  let ⟨f, hf⟩ := h; ⟨f, ne_of_lt hf⟩

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
