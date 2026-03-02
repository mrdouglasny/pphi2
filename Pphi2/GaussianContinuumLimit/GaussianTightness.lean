/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tightness of Embedded Gaussian Measures

Shows that the family of continuum-embedded Gaussian measures
`{ν_{GFF,a}}_{a ∈ (0,1]}` is tight in S'(ℝ^d).

## Main results

- `gaussian_second_moment_uniform` — `∫ (ω f)² dν_{GFF,a} ≤ C` uniformly
- `gaussianContinuumMeasures_tight` — (axiom) tightness via Mitoma criterion

## Mathematical background

### Uniform moment bounds

The embedded two-point function satisfies `E[Φ_a(f)²] ≤ C(f,m)` uniformly
in a (from `embeddedTwoPoint_uniform_bound`). This is the Gaussian core
that the interacting case builds on via Cauchy-Schwarz density transfer.

### Mitoma criterion for tightness on S'

Mitoma's theorem (1983) reduces tightness of measures on S'(ℝ^d) to
tightness of the 1D projections: a family {ν_α} on S' is tight iff
for each f ∈ S, the pushforward measures {(ev_f)_* ν_α} are tight on ℝ.

For the Gaussian measures, the 1D marginals are N(0, σ²_α) with
σ²_α = E[Φ_α(f)²] ≤ C uniformly. A Gaussian N(0, σ²) with σ² ≤ C
satisfies P(|X| > R) ≤ 2e^{-R²/2C}, so tightness on ℝ is immediate.

Equicontinuity in f follows from the Schwartz seminorm bound on the
discretized L² norm.

## References

- Mitoma (1983), "Tightness of probabilities on C([0,1]; S') and D([0,1]; S')"
- Simon, *The P(φ)₂ Euclidean QFT*, §V.1
-/

import Pphi2.GaussianContinuumLimit.PropagatorConvergence

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! ## Uniform second moment bounds -/

/-- **Uniform bound on Gaussian second moments.**

  `∫ (ω f)² dν_{GFF,a} ≤ C(f, m)` uniformly in a ∈ (0, 1] and N

This is a direct consequence of `embeddedTwoPoint_uniform_bound`:
the embedded two-point function `E[Φ_a(f)²]` is uniformly bounded.

This provides the Gaussian core for the interacting tightness:
the Cauchy-Schwarz density transfer in `Hypercontractivity.lean`
reduces the interacting second moment to this Gaussian bound. -/
theorem gaussian_second_moment_uniform (mass : ℝ) (hmass : 0 < mass)
    (f : ContinuumTestFunction d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∫ ω : Configuration (ContinuumTestFunction d),
      (ω f) ^ 2 ∂(gaussianContinuumMeasure d N a mass ha hmass) ≤ C := by
  -- Rewrite the integral as embeddedTwoPoint d N a mass ha hmass f f,
  -- then apply the uniform bound.
  obtain ⟨C, hC_pos, hC_bound⟩ := embeddedTwoPoint_uniform_bound d N mass hmass f
  refine ⟨C, hC_pos, fun a ha ha_le => ?_⟩
  -- ∫ (ω f)² = ∫ ω(f) * ω(f) = embeddedTwoPoint ... f f
  have : ∫ ω : Configuration (ContinuumTestFunction d),
      (ω f) ^ 2 ∂(gaussianContinuumMeasure d N a mass ha hmass) =
    embeddedTwoPoint d N a mass ha hmass f f := by
    congr 1; ext ω; ring
  rw [this]
  exact hC_bound a ha ha_le

/-! ## Tightness of Gaussian continuum measures -/

/-- **Tightness of the embedded Gaussian measures.**

The family `{ν_{GFF,a}}_{a ∈ (0,1]}` is tight on S'(ℝ^d).

Proof outline:
1. **1D marginals**: For each f ∈ S(ℝ^d), the pushforward `(ev_f)_* ν_{GFF,a}`
   is a centered Gaussian N(0, σ²_a) on ℝ. By `gaussian_second_moment_uniform`,
   σ²_a ≤ C(f) uniformly. Chebyshev gives `P(|Φ_a(f)| > R) ≤ C/R²` for all a.

2. **Equicontinuity**: For f, g ∈ S, `E[|Φ_a(f) - Φ_a(g)|²]` is controlled
   by Schwartz seminorms of f - g, uniformly in a. This follows from the
   operator bound `C_a ≤ m⁻²·I` and Schwartz seminorm estimates.

3. **Mitoma criterion**: 1D tightness + equicontinuity ⟹ tightness on S'.

Reference: Mitoma (1983), Simon §V.1. -/
axiom gaussianContinuumMeasures_tight
    (mass : ℝ) (hmass : 0 < mass) :
    ∀ ε : ℝ, 0 < ε →
    ∃ (K : Set (Configuration (ContinuumTestFunction d))),
      IsCompact K ∧
      ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
      1 - ε ≤ (gaussianContinuumMeasure d N a mass ha hmass K).toReal

end Pphi2

end
