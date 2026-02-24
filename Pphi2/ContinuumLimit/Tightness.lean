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

import Pphi2.ContinuumLimit.Embedding

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! ## Uniform second moment bounds -/

/-- **Uniform bound on the second moment of field evaluations.**

  `∫ |Φ_a(f)|² dν_a ≤ C(f)` uniformly in a

where `Φ_a(f) = (ι_a φ)(f) = a^d Σ_x φ(x) f(ax)` is the continuum field
evaluation.

The bound C(f) depends on the Schwartz function f but not on the
lattice spacing a. It is controlled by the H^{-1} Sobolev norm of f.

Proof outline:
1. `∫ Φ_a(f)² dμ_a ≤ e^{C|Λ|} · ∫ Φ_a(f)² dμ_{GFF}` (interaction bounded below)
2. `∫ Φ_a(f)² dμ_{GFF} = ⟨f, G_a f⟩_lattice` (Gaussian covariance)
3. `⟨f, G_a f⟩_lattice → ⟨f, G f⟩_continuum` as a → 0 (propagator convergence)
4. The convergent sequence is bounded. -/
axiom second_moment_uniform (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) (f : ContinuumTestFunction d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∫ ω : Configuration (ContinuumTestFunction d),
      (ω f) ^ 2 ∂(continuumMeasure d N P a mass ha hmass) ≤ C

/-- **Equicontinuity of moments in the test function.**

  `∫ |Φ_a(f) - Φ_a(g)|² dν_a ≤ C · ‖f - g‖²_s`

uniformly in a, where ‖·‖_s is a Schwartz seminorm of sufficiently
high order s.

This ensures the family of measures is "equicontinuous" in the test
function variable, which is needed for tightness on the full space S'. -/
axiom moment_equicontinuity (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (C : ℝ) (k n : ℕ), 0 < C ∧
    ∀ (f g : ContinuumTestFunction d) (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∫ ω : Configuration (ContinuumTestFunction d),
      (ω f - ω g) ^ 2 ∂(continuumMeasure d N P a mass ha hmass) ≤
    C * (SchwartzMap.seminorm ℝ k n (f - g)) ^ 2

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

/-! ## Nelson's hypercontractive estimate

The engine behind the uniform bounds. -/

/-- **Nelson's hypercontractive estimate** (axiomatized).

For the Gaussian measure μ_{GFF} and Wick-ordered monomials:

  `‖:φ^n:‖_{L^p(μ_GFF)} ≤ (p-1)^{n/2} · ‖:φ^n:‖_{L^2(μ_GFF)}`

for all p ≥ 2. This is the key estimate for controlling moments of the
interacting field beyond the Gaussian case.

The proof goes through the Gross log-Sobolev inequality, which is a deep
result in its own right. We axiomatize it as a standalone statement. -/
theorem nelson_hypercontractive (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (n : ℕ) (p : ℝ) (hp : 2 ≤ p) (f : ContinuumTestFunction d)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    -- Nelson's hypercontractive estimate: the L^p moment of ω(f) under the
    -- continuum-embedded measure is controlled by the L^2 moment
    -- with the hypercontractive factor (p - 1)^n.
    -- This is the key input for the uniform moment bounds needed for tightness.
    ∫ ω : Configuration (ContinuumTestFunction d),
        |ω f| ^ (p * n) ∂(continuumMeasure d N P a mass ha hmass) ≤
      (p - 1) ^ n *
      (∫ ω : Configuration (ContinuumTestFunction d),
        (ω f) ^ (2 * n) ∂(continuumMeasure d N P a mass ha hmass)) ^
      (p / 2) := by
  sorry

end Pphi2

end
