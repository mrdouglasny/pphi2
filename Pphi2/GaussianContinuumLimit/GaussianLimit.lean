/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gaussian Free Field Continuum Limit

Assembles the Gaussian continuum limit: existence of a subsequential
weak limit, identification as Gaussian with continuum covariance,
and the bridge to the interacting case.

## Main results

- `gaussianContinuumLimit_exists` — existence of a subsequential weak limit
- `gaussianContinuumLimit_nontrivial` — `∫ (ω f)² dμ > 0` for f ≠ 0
- `gaussianLimit_isGaussian` — (axiom) weak limits of Gaussians are Gaussian
- `IsGaussianContinuumLimit` — predicate for the Gaussian continuum limit

## Mathematical background

### Existence

From `gaussianContinuumMeasures_tight`, the family {ν_{GFF,a}} is tight.
Prokhorov's theorem extracts a weakly convergent subsequence. The limit
is a probability measure on S'(ℝ^d).

### Identification

The characteristic functional of ν_{GFF,a} is:

  `E[e^{iω(f)}] = exp(-½ · embeddedTwoPoint(f, f))`

By `propagator_convergence`, the exponent converges to `-½ G(f, f)`.
Hence the limit measure has characteristic functional `exp(-½ G(f, f))`,
identifying it as the Gaussian with covariance = continuum Green's function.

### Gaussianity of the limit

Weak limits of Gaussian measures are Gaussian (Bochner-Minlos): if the
characteristic functionals `exp(-½ σ²_n(f))` converge pointwise to
`exp(-½ σ²(f))`, then the limit is Gaussian with variance σ²(f).

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I (Free field)
- Glimm-Jaffe, *Quantum Physics*, §6.2 (Gaussian measures)
-/

import Pphi2.GaussianContinuumLimit.GaussianTightness
import Pphi2.ContinuumLimit.Convergence

noncomputable section

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (d N : ℕ) [NeZero N] [Fact (0 < d)]

/-! ## Existence of the Gaussian continuum limit -/

/-- **Existence of a Gaussian free field continuum limit.**

For any sequence of lattice spacings a_n → 0 (with N fixed), the
embedded Gaussian measures `ν_{GFF,a_n}` have a weakly convergent
subsequence. The limit is a probability measure on S'(ℝ^d).

This parallels `continuumLimit` from `Convergence.lean` but for the
free (Gaussian) case, where the proof is simpler. -/
theorem gaussianContinuumLimit_exists
    (mass : ℝ) (hmass : 0 < mass)
    (a : ℕ → ℝ) (ha_pos : ∀ n, 0 < a n) (ha_le : ∀ n, a n ≤ 1)
    (_ha_lim : Tendsto a atTop (nhds 0)) :
    ∃ (φ : ℕ → ℕ) (μ : Measure (Configuration (ContinuumTestFunction d))),
      StrictMono φ ∧
      IsProbabilityMeasure μ ∧
      ∀ (f : Configuration (ContinuumTestFunction d) → ℝ),
        Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(gaussianContinuumMeasure d N (a (φ n)) mass
          (ha_pos (φ n)) hmass))
          atTop (nhds (∫ ω, f ω ∂μ)) := by
  -- Apply Prokhorov extraction to the Gaussian measures
  let ν : ℕ → Measure (Configuration (ContinuumTestFunction d)) :=
    fun n => gaussianContinuumMeasure d N (a n) mass (ha_pos n) hmass
  exact prokhorov_configuration_sequential (d := d) ν
    (fun n => gaussianContinuumMeasure_isProbability d N (a n) mass (ha_pos n) hmass)
    (fun ε hε => by
      obtain ⟨K, hK_compact, hK_bound⟩ :=
        gaussianContinuumMeasures_tight d N mass hmass ε hε
      exact ⟨K, hK_compact, fun n => hK_bound (a n) (ha_pos n) (ha_le n)⟩)

/-- **Nontriviality of the Gaussian continuum limit.**

For any nonzero test function f ∈ S(ℝ^d), the two-point function of the
continuum limit is strictly positive: `∫ (ω f)² dμ > 0`.

Proof:
- On each lattice, `E[Φ_a(f)²] > 0` (lattice covariance is positive definite).
- By `propagator_convergence`, `E[Φ_a(f)²] → G(f,f) > 0`.
- The limit measure inherits the two-point function by moment convergence. -/
theorem gaussianContinuumLimit_nontrivial
    (mass : ℝ) (hmass : 0 < mass)
    (f : ContinuumTestFunction d) (hf : f ≠ 0)
    (μ : Measure (Configuration (ContinuumTestFunction d)))
    [IsProbabilityMeasure μ]
    -- μ has the correct two-point function (from propagator convergence)
    (h2pt : ∫ ω : Configuration (ContinuumTestFunction d),
        (ω f) ^ 2 ∂μ = continuumGreenBilinear d mass f f) :
    0 < ∫ ω : Configuration (ContinuumTestFunction d), (ω f) ^ 2 ∂μ := by
  rw [h2pt]
  exact continuumGreenBilinear_pos d mass hmass f hf

/-! ## Gaussianity of the limit -/

/-- **Weak limits of Gaussian measures are Gaussian.**

If {μ_n} is a sequence of centered Gaussian measures on S'(ℝ^d) that
converges weakly to μ, then μ is also a centered Gaussian measure.

The characteristic functional of μ_n is `exp(-½ σ²_n(f))` where σ²_n(f)
is the variance. Weak convergence implies pointwise convergence of
characteristic functionals:

  `exp(-½ σ²_n(f)) → E_μ[e^{iω(f)}]`

Since σ²_n(f) → σ²(f) (a finite limit, by the uniform bound), the limit
characteristic functional is `exp(-½ σ²(f))`, which is Gaussian by
the Bochner-Minlos theorem.

Reference: Fernique (1975), §III.4; Simon, *The P(φ)₂ Euclidean QFT* Ch. I. -/
axiom gaussianLimit_isGaussian
    (μ_seq : ℕ → Measure (Configuration (ContinuumTestFunction d)))
    (hμ_prob : ∀ n, IsProbabilityMeasure (μ_seq n))
    -- Each μ_n is Gaussian: the characteristic functional is exp(-½ σ²_n(f))
    (hμ_gauss : ∀ n (f : ContinuumTestFunction d),
      ∫ ω : Configuration (ContinuumTestFunction d),
        Real.exp (ω f) ∂(μ_seq n) =
      Real.exp ((1/2) * ∫ ω, (ω f) ^ 2 ∂(μ_seq n)))
    -- Weak convergence to μ
    (μ : Measure (Configuration (ContinuumTestFunction d)))
    [IsProbabilityMeasure μ]
    (hconv : ∀ (g : Configuration (ContinuumTestFunction d) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n => ∫ ω, g ω ∂(μ_seq n)) atTop (nhds (∫ ω, g ω ∂μ))) :
    -- The limit is Gaussian: its characteristic functional has Gaussian form
    ∀ (f : ContinuumTestFunction d),
      ∫ ω : Configuration (ContinuumTestFunction d),
        Real.exp (ω f) ∂μ =
      Real.exp ((1/2) * ∫ ω, (ω f) ^ 2 ∂μ)

/-! ## Gaussian continuum limit predicate -/

/-- **Predicate for the Gaussian continuum limit measure.**

A probability measure μ on S'(ℝ^d) is a Gaussian continuum limit if:
1. It is a probability measure.
2. It is Gaussian (characteristic functional is `exp(-½ σ²(f))`).
3. Its covariance equals the continuum Green's function:
   `∫ (ω f)² dμ = G(f, f)` for all f ∈ S(ℝ^d).
4. It is Z₂-symmetric: `μ ∘ (-) = μ`. -/
structure IsGaussianContinuumLimit
    (μ : Measure (Configuration (ContinuumTestFunction d)))
    (mass : ℝ) : Prop where
  /-- μ is a probability measure -/
  isProbability : IsProbabilityMeasure μ
  /-- Gaussian: characteristic functional has exp(-½σ²) form -/
  isGaussian : ∀ (f : ContinuumTestFunction d),
    ∫ ω : Configuration (ContinuumTestFunction d),
      Real.exp (ω f) ∂μ =
    Real.exp ((1/2) * ∫ ω, (ω f) ^ 2 ∂μ)
  /-- Covariance = continuum Green's function -/
  covariance_eq : ∀ (f : ContinuumTestFunction d),
    ∫ ω : Configuration (ContinuumTestFunction d), (ω f) ^ 2 ∂μ =
    continuumGreenBilinear d mass f f
  /-- Z₂ symmetry: μ is invariant under field negation -/
  z2_symmetric : Measure.map
    (Neg.neg : Configuration (ContinuumTestFunction d) →
      Configuration (ContinuumTestFunction d)) μ = μ

/-! ## Bridge to the interacting case -/

/-- **The Gaussian uniform moment bound feeds the interacting tightness.**

The key connection: the uniform bound `E_{GFF}[Φ_a(f)²] ≤ C` from
`gaussian_second_moment_uniform` provides the Gaussian core for the
Cauchy-Schwarz density transfer in `Hypercontractivity.lean`.

Specifically, for the interacting measure `dμ_a = (1/Z_a) e^{-V_a} dμ_{GFF}`:

  `∫ (ω f)² dμ_a ≤ (1/Z_a) · (∫ (ω f)⁴ dμ_{GFF})^{1/2} · (∫ e^{-2V_a} dμ_{GFF})^{1/2}`

The first factor is controlled by Gaussian hypercontractivity (bounded by
the second moment), and the second by Nelson's exponential estimate.
Both inherit the uniform-in-a property from the Gaussian bound. -/
theorem gaussian_feeds_interacting_tightness
    (mass : ℝ) (hmass : 0 < mass)
    (f : ContinuumTestFunction d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∫ ω : Configuration (ContinuumTestFunction d),
      (ω f) ^ 2 ∂(gaussianContinuumMeasure d N a mass ha hmass) ≤ C :=
  gaussian_second_moment_uniform d N mass hmass f

end Pphi2

end
