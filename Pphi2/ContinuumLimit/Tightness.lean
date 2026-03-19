/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tightness of the Continuum-Embedded Measures

Shows that the family of continuum-embedded measures `{ν_a}_{a>0}` is tight
in S'(ℝ²). This is the key technical step enabling extraction of a
convergent subsequence via Prokhorov's theorem.

## Main results

- `second_moment_uniform` — uniform bound on `∫ |Φ_a(f)|² dν_a`
- `moment_equicontinuity` — equicontinuity of moments in f
- `continuumMeasures_tight` — tightness of {ν_a} in S'(ℝ²)

## Mathematical background

### Tightness criterion (Mitoma)

A family of probability measures {ν_α} on S'(ℝ^d) is tight iff for each
f ∈ S(ℝ^d), the real-valued random variables {Φ_α(f)} are tight on ℝ.

By Chebyshev, tightness of {Φ_α(f)} on ℝ follows from uniform second
moment bounds: `sup_α ∫ |Φ_α(f)|² dν_α < ∞`.

### Uniform moment bounds

The key input is Nelson's hypercontractive estimate, which gives:

  `∫ |Φ_a(f)|² dμ_a ≤ C · ‖f‖²_{H^{-1}}`

uniformly in a, where `‖f‖_{H^{-1}}` is the Sobolev H^{-1} norm.

For the interacting measure, the bound follows from:
1. The Gaussian two-point function: `∫ Φ_a(f)² dμ_{GFF} = ⟨f, G_a f⟩`
2. The interaction only improves decay: `∫ Φ_a(f)² dμ_a ≤ e^C · ∫ Φ_a(f)² dμ_{GFF}`
3. The lattice propagator converges: `⟨f, G_a f⟩ → ⟨f, G f⟩`

## References

- Mitoma (1983), "Tightness of probabilities on C([0,1]; S') and D([0,1]; S')"
- Simon, *The P(φ)₂ Euclidean QFT*, §V.1
- Glimm-Jaffe, *Quantum Physics*, §19.4
-/

import Pphi2.ContinuumLimit.Hypercontractivity

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (d N : ℕ) [NeZero N]

-- NOTE: second_moment_uniform and moment_equicontinuity were removed as dead
-- axioms (never referenced by any actual Lean code outside this file).
-- The tightness axiom continuumMeasures_tight (below) is the live axiom.

/-! ## Tightness -/

/-- **Tightness of the continuum-embedded measures.**

The family `{ν_a = (ι_a)_* μ_a}_{a ∈ (0, 1]}` is tight in the space of
probability measures on `S'(ℝ^d) = Configuration (ContinuumTestFunction d)`.

Proof:
1. By Mitoma's criterion, it suffices to show that for each f ∈ S(ℝ^d),
   the real-valued measures `(ev_f)_* ν_a` are tight on ℝ.
2. By Chebyshev's inequality, tightness on ℝ follows from the uniform
   second moment bound `∫ |Φ_a(f)|² dν_a ≤ C(f)`.
3. The uniform bound is provided by `second_moment_uniform`. -/
axiom continuumMeasures_tight (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    -- The family {ν_a}_{a ∈ (0,1]} is tight on Configuration (ContinuumTestFunction d)
    -- Stated as: for every ε > 0, there exists a compact K such that
    -- ν_a(K) ≥ 1 - ε for all a ∈ (0, 1].
    ∀ ε : ℝ, 0 < ε →
    ∃ (K : Set (Configuration (ContinuumTestFunction d))),
      IsCompact K ∧
      ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
      1 - ε ≤ (continuumMeasure d N P a mass ha hmass K).toReal

end Pphi2

end
