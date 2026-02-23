/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Existence of the Continuum Limit

Applies Prokhorov's theorem to extract a weakly convergent subsequence
from the tight family of continuum-embedded measures.

## Main results

- `prokhorov` — tightness implies sequential compactness (axiomatized)
- `continuumLimit` — existence of the P(Φ)₂ continuum measure
- `schwinger_convergence` — Schwinger functions converge

## Mathematical background

### Prokhorov's theorem

On a Polish space (complete separable metrizable), a family of probability
measures is tight if and only if it is relatively sequentially compact in
the topology of weak convergence.

S'(ℝ^d) with its weak-* topology is a Polish space (it is the dual of a
nuclear Fréchet space, hence metrizable and complete).

### Application

From `continuumMeasures_tight`, the family {ν_a}_{a>0} is tight.
By Prokhorov, any sequence ν_{a_n} with a_n → 0 has a weakly convergent
subsequence ν_{a_{n_k}} ⇀ ν.

The limit ν is the P(Φ)₂ Euclidean measure on S'(ℝ²).

### Schwinger functions

The n-point Schwinger functions converge:

  `S_a^{(n)}(f₁,...,fₙ) = ∫ Φ(f₁)···Φ(fₙ) dν_a → S^{(n)}(f₁,...,fₙ)`

This follows from:
1. Weak convergence: ∫ F dν_a → ∫ F dν for bounded continuous F.
2. The function Φ ↦ Φ(f₁)···Φ(fₙ) is not bounded, but uniform
   moment bounds justify the convergence.

## References

- Prokhorov (1956), "Convergence of random processes and limit theorems
  in probability theory"
- Billingsley, *Convergence of Probability Measures* (2nd ed.)
- Simon, *The P(φ)₂ Euclidean QFT*, §V.2
-/

import Pphi2.ContinuumLimit.Tightness

noncomputable section

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! ## Prokhorov's theorem (axiomatized)

Prokhorov's theorem for Polish spaces. Mathlib has partial support
(`MeasureTheory.tight_iff_isRelativelyCompact`); we axiomatize the
sequential version needed here. -/

/-- **Prokhorov's theorem** (sequential version).

On a Polish space X, if a sequence of probability measures {μₙ} is tight,
then it has a weakly convergent subsequence.

This is partially available in Mathlib but we axiomatize the sequential
extraction for convenience. -/
axiom prokhorov_sequential {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [PolishSpace X] [OpensMeasurableSpace X]
    (μ : ℕ → Measure X)
    (hμ_prob : ∀ n, IsProbabilityMeasure (μ n))
    (hμ_tight : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set X, IsCompact K ∧ ∀ n, 1 - ε ≤ (μ n K).toReal) :
    ∃ (φ : ℕ → ℕ) (ν : Measure X),
      StrictMono φ ∧ IsProbabilityMeasure ν ∧
      -- Weak convergence: ∫ f dμ_{φ(n)} → ∫ f dν for bounded continuous f
      ∀ (f : X → ℝ), Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ x, f x ∂(μ (φ n))) atTop (nhds (∫ x, f x ∂ν))

/-! ## The continuum limit -/

/-- **Existence of the P(Φ)₂ continuum limit.**

For any sequence of lattice spacings aₙ → 0, there exists a subsequence
aₙₖ and a probability measure μ on S'(ℝ^d) such that:

  `ν_{aₙₖ} ⇀ μ` weakly

where `ν_a = (ι_a)_* μ_a` is the continuum-embedded interacting measure.

The limit μ is the P(Φ)₂ Euclidean quantum field theory measure. -/
theorem continuumLimit (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    -- A sequence of lattice spacings converging to 0
    (a : ℕ → ℝ) (ha_pos : ∀ n, 0 < a n) (ha_le : ∀ n, a n ≤ 1)
    (ha_lim : Tendsto a atTop (nhds 0)) :
    ∃ (φ : ℕ → ℕ) (μ : Measure (Configuration (ContinuumTestFunction d))),
      StrictMono φ ∧
      IsProbabilityMeasure μ ∧
      -- Weak convergence of the subsequence
      ∀ (f : Configuration (ContinuumTestFunction d) → ℝ),
        Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(continuumMeasure d N P (a (φ n)) mass
          (ha_pos (φ n)) hmass))
          atTop (nhds (∫ ω, f ω ∂μ)) := by
  -- Apply Prokhorov's theorem to the tight family
  sorry

/-! ## Schwinger function convergence -/

/-- **Convergence of the two-point Schwinger function.**

For Schwartz functions f, g ∈ S(ℝ^d):

  `S₂^{(a)}(f, g) = ∫ Φ(f) · Φ(g) dν_a → S₂(f, g) = ∫ Φ(f) · Φ(g) dμ`

as a → 0 (along the convergent subsequence).

This follows from weak convergence plus uniform integrability
(from the uniform moment bounds). -/
axiom schwinger2_convergence (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d) :
    -- Along the convergent subsequence, the two-point functions converge.
    -- The full statement requires the subsequence from continuumLimit.
    True -- Placeholder

/-- **Convergence of general n-point Schwinger functions.**

  `S_n^{(a)}(f₁,...,fₙ) → S_n(f₁,...,fₙ)`

for all n and all test functions f₁,...,fₙ ∈ S(ℝ^d).

The connected parts decay according to the mass gap
(from `clustering_uniform`). -/
axiom schwinger_n_convergence (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ)
    (f : Fin n → ContinuumTestFunction d) :
    True -- Placeholder

/-! ## Properties of the continuum limit -/

/-- The continuum limit measure is non-trivial (not the delta measure at 0).

This follows from the two-point function being nonzero:
  `S₂(f, f) = ∫ Φ(f)² dμ > 0` for f ≠ 0

The Gaussian two-point function provides a lower bound. -/
axiom continuumLimit_nontrivial (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    True -- Placeholder: μ is not δ₀

/-- The continuum limit is non-Gaussian (for nontrivial P).

This follows from the four-point Schwinger function:
  `S₄(f,f,f,f) - 3 · S₂(f,f)² ≠ 0`

i.e., the connected four-point function (fourth cumulant) is nonzero.
For a Gaussian measure, all connected n-point functions with n ≥ 3 vanish,
so a nonzero fourth cumulant proves non-Gaussianity. -/
axiom continuumLimit_nonGaussian (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    True -- Placeholder: μ is not Gaussian

end Pphi2

end
