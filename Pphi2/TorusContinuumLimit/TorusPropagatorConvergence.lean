/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Torus Propagator Convergence

The main analytical content of the torus Gaussian continuum limit: the lattice
Green's function on T²_L converges to the continuum Green's function as N → ∞.

## Main results

- `torus_propagator_convergence` — (axiom) lattice eigenvalues → continuum eigenvalues
- `torusEmbeddedTwoPoint_uniform_bound` — (axiom) `E[Φ_N(f)²] ≤ C/m²·‖f‖²` uniformly in N
- `torusContinuumGreen_pos` — `G_L(f,f) > 0` for f ≠ 0

## Mathematical background

On the torus T²_L with lattice spacing a = L/N, the lattice eigenvalues are:

  `λ_{n}^{lat} = (4N²/L²) sin²(πn₁/N) + (4N²/L²) sin²(πn₂/N) + m²`

for n ∈ (ℤ/Nℤ)². As N → ∞ (pure UV limit, L fixed):

  `λ_{n}^{lat} → (2πn₁/L)² + (2πn₂/L)² + m² = λ_{n}^{cont}`

This is a **pure UV limit** — no IR tail issues since the volume L is fixed.
The convergence is mode-by-mode and the smooth test function Fourier coefficients
f̂(n) decay rapidly, providing dominated convergence.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Pphi2.TorusContinuumLimit.TorusEmbedding

noncomputable section

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Propagator convergence on the torus -/

/-- **Lattice propagator on the torus converges to the continuum Green's function.**

For smooth torus test functions f, g ∈ C∞(T²_L):

  `torusEmbeddedTwoPoint L N mass f g → torusContinuumGreen L mass f g`

as N → ∞ (with L fixed, a = L/N → 0).

Mathematically: the lattice eigenvalues `(4N²/L²) sin²(πn/N) + m²` converge
to the continuum eigenvalues `(2πn/L)² + m²` for each mode n. The sum over
n ∈ (ℤ/Nℤ)² with rapidly decaying f̂(n) converges to the ℤ²-sum by dominated
convergence.

This is a **pure UV limit**: L is fixed, only N → ∞. There is no IR tail
issue because the torus has finite volume.

Reference: Glimm-Jaffe §6.1, Simon Ch. I. -/
axiom torus_propagator_convergence
    (mass : ℝ) (hmass : 0 < mass)
    (f g : TorusTestFunction L) :
    Tendsto
      (fun N : ℕ => torusEmbeddedTwoPoint L (N + 1) mass hmass f g)
      atTop
      (nhds (torusContinuumGreen L mass hmass f g))

/-! ## Uniform bound on the embedded two-point function -/

/-- **Uniform bound on torus second moments.**

  `E[Φ_N(f)²] ≤ C(f, L, m)` uniformly in N ≥ 1

This follows from:
1. **Eigenvalue lower bound:** All eigenvalues of `-Δ_{lat} + m²` satisfy `λ_k ≥ m²`
   (since the discrete Laplacian is nonneg-definite), so `λ_k⁻¹ ≤ 1/m²`.
2. **Parseval:** `Σ_k ⟨e_k, ι*f⟩² = ‖ι*f‖²` (lattice eigenvectors are orthonormal).
3. **Riemann sum bound:** `‖ι*f‖² = (L/N)² Σ_x |f(xL/N)|²` is a Riemann sum for
   `‖f‖²_{L²(T²_L)}` of a continuous function on the compact torus, hence bounded
   uniformly in N.
4. **Combined:** `E[Φ_N(f)²] = Σ_k λ_k⁻¹ ⟨e_k, ι*f⟩² ≤ (1/m²) · C_f`.

The key advantage over S'(ℝ^d): finite volume means the Riemann sum is over
a finite domain, eliminating any IR contribution.

Reference: Glimm-Jaffe §6.1 (lattice propagator bounds). -/
axiom torusEmbeddedTwoPoint_uniform_bound (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N],
    torusEmbeddedTwoPoint L N mass hmass f f ≤ C

/-! ## Positivity of the continuum Green's function -/

/-- **Positivity of the torus continuum Green's function.**

  `G_L(f, f) > 0` for nonzero f ∈ C∞(T²_L)

The Fourier-space representation has integrand
`|f̂(n)|² / ((2πn/L)² + m²)` which is nonneg, and strictly positive for
at least one n since f̂ ≠ 0 (Fourier transform is injective on C∞(T²)). -/
theorem torusContinuumGreen_pos (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) (hf : f ≠ 0) :
    0 < torusContinuumGreen L mass hmass f f := by
  unfold torusContinuumGreen
  exact greenFunctionBilinear_pos mass hmass f hf

end Pphi2

end
