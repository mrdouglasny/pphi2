/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice Propagator Convergence

The main analytical content of the Gaussian continuum limit: the lattice
Green's function converges to the continuum Green's function as a → 0.

## Main results

- `propagator_convergence` — (axiom) lattice Riemann sum → continuum integral
- `embeddedTwoPoint_uniform_bound` — `E[Φ_a(f)²] ≤ C · ‖f‖²` uniformly in a, N
- `continuumGreenBilinear_pos` — `G(f,f) > 0` for nonzero f

## Mathematical background

### Propagator convergence

The lattice propagator in Fourier space is:

  `Ĉ_a(k) = 1 / ((4/a²) Σ_i sin²(πk_i a/L) + m²)`

For k in any compact set, as a → 0 with L = Na → ∞:

  `Ĉ_a(k) → 1 / (|k|² + m²)`

since `(2/a) sin(πk_i a/L) → 2πk_i/L → k_i` (with appropriate scaling).

The rapid decay of f̂, ĝ controls the contribution from large k, giving:

  `a^{2d} Σ_{x,y} C_a(x,y) f(ax) g(ay) → ∫ f̂(k) ĝ(k) / (|k|²+m²) dk/(2π)^d`

### Uniform bound

All eigenvalues of `-Δ_a + m²` satisfy `λ ≥ m²`, so:

  `E[Φ_a(f)²] = ⟨f_a, C_a f_a⟩ ≤ (1/m²) · ‖f_a‖²_{L²(Λ_a)}`

The discretized L² norm `a^d Σ_x |f(ax)|²` converges to `‖f‖²_{L²(ℝ^d)}` and is
uniformly bounded for Schwartz f, giving `E[Φ_a(f)²] ≤ C/m²`.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Pphi2.GaussianContinuumLimit.EmbeddedCovariance

noncomputable section

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! ## Propagator convergence -/

/-- **Lattice propagator converges to continuum Green's function.**

For Schwartz test functions f, g and lattice parameters a → 0 with Na → ∞:

  `embeddedTwoPoint d N a mass f g → continuumGreenBilinear d mass f g`

Mathematically, this says the Riemann sum:

  `a^{2d} Σ_{x,y ∈ Λ} C_a(x,y) f(ax) g(ay)`

converges to:

  `∫ f̂(k) ĝ(k) / (|k|² + m²) dk / (2π)^d`

The proof has three ingredients:
1. In Fourier space, the lattice eigenvalues `(4/a²)sin²(πk/N) + m²`
   approximate `|k|² + m²` for each mode k.
2. The Riemann sum over lattice momenta approximates the Fourier integral.
3. Schwartz decay of f̂, ĝ provides dominated convergence (the tails
   are uniformly bounded by `C · |k|^{-M}` for any M).

Reference: Glimm-Jaffe §6.1, Simon Ch. I. -/
axiom propagator_convergence
    (mass : ℝ) (hmass : 0 < mass)
    (f g : ContinuumTestFunction d)
    -- Sequence of lattice spacings tending to 0
    (a_seq : ℕ → ℝ) (ha_pos : ∀ n, 0 < a_seq n)
    (ha_lim : Tendsto a_seq atTop (nhds 0))
    -- Sequence of lattice sizes with N_n · a_n → ∞
    (N_seq : ℕ → ℕ) [∀ n, NeZero (N_seq n)]
    (hNa : Tendsto (fun n => (N_seq n : ℝ) * a_seq n) atTop atTop) :
    Tendsto
      (fun n => embeddedTwoPoint d (N_seq n) (a_seq n) mass (ha_pos n) hmass f g)
      atTop
      (nhds (continuumGreenBilinear d mass f g))

/-! ## Uniform bound on the embedded two-point function -/

/-- **Uniform bound on the Gaussian two-point function.**

  `E[Φ_a(f)²] ≤ C(f, m)` uniformly in a ∈ (0, 1] and N

The constant depends on f and mass but NOT on the lattice parameters.

Proof sketch:
1. `E[Φ_a(f)²] = ⟨f_a, C_a f_a⟩_lattice` where `f_a(x) = a^d · f(ax)`.
2. All eigenvalues of Q = -Δ_a + m² satisfy `λ ≥ m²`, so `C_a ≤ m⁻²·I`.
3. Therefore `E[Φ_a(f)²] ≤ m⁻² · ‖f_a‖²_{ℓ²}`.
4. The discrete norm `‖f_a‖²_{ℓ²} = a^{2d} Σ_x |f(ax)|² ≤ a^d · Σ_x a^d |f(ax)|²`
   and the Riemann sum `a^d Σ_x |f(ax)|²` converges to `‖f‖²_{L²}` (bounded). -/
theorem embeddedTwoPoint_uniform_bound (mass : ℝ) (hmass : 0 < mass)
    (f : ContinuumTestFunction d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    embeddedTwoPoint d N a mass ha hmass f f ≤ C := by
  -- The Riemann sum a^d Σ_x |f(ax)|² is bounded for Schwartz f.
  -- Combined with the operator bound C_a ≤ m⁻²·I, this gives a uniform bound.
  sorry

/-- **Positivity of the continuum Green's function.**

  `G(f, f) > 0` for nonzero f ∈ S(ℝ^d)

The Fourier-space integrand `|f̂(k)|² / (|k|² + m²)` is nonneg, and
strictly positive on a set of positive measure (since f̂ ≠ 0 for f ≠ 0
in Schwartz space — the Fourier transform is injective on S). -/
theorem continuumGreenBilinear_pos (mass : ℝ) (hmass : 0 < mass)
    (f : ContinuumTestFunction d) (hf : f ≠ 0) :
    0 < continuumGreenBilinear d mass f f := by
  -- The integrand |f̂(k)|²/(|k|²+m²) is nonneg and strictly positive
  -- on the support of f̂, which has positive Lebesgue measure since f ≠ 0
  -- and the Fourier transform is injective on Schwartz space.
  sorry

end Pphi2

end
