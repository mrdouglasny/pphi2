/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Spectral Gap of the Lattice Hamiltonian

The transfer matrix T = e^{-aH} defines a lattice Hamiltonian H with
discrete spectrum. The spectral gap `E₁ - E₀ > 0` controls the
exponential decay of correlations (mass gap / clustering).

## Main results

- `spectral_gap_pos` — E₁ - E₀ > 0 (strict gap, from `massGap_pos`)
- `spectral_gap_uniform` — the gap is bounded below uniformly in a
- `spectral_gap_lower_bound` — m_phys ≥ c·m_bare

## Mathematical background

The lattice Hamiltonian for P(Φ)₂ in d=2 on a spatial lattice of Ns sites is:

  `H = -½ Σ_x ∂²/∂ψ(x)² + V(ψ)`

where the potential is:

  `V(ψ) = Σ_{<xy>} ½ a⁻² (ψ(x) - ψ(y))² + Σ_x (½ m² ψ(x)² + :P(ψ(x)):_c)`

This is a Schrödinger operator on L²(ℝ^Ns) with a confining potential
(V(ψ) → ∞ as |ψ| → ∞ since P has even degree ≥ 4).

The Hamiltonian properties (self-adjointness, compact resolvent, simple ground
state, ground state positivity and smoothness) all follow from the transfer
operator being compact and self-adjoint with a strictly positive kernel
(see L2Operator.lean for the operator axioms and spectral decomposition).

## References

- Glimm-Jaffe, *Quantum Physics*, §6.2, §19.3
- Simon, *The P(φ)₂ Euclidean QFT*, §III.2 (Spectral properties)
- Reed-Simon, *Methods of Mathematical Physics II*, §X.2 (Schrödinger operators)
-/

import Pphi2.TransferMatrix.Positivity

noncomputable section

open GaussianField Real

namespace Pphi2

/-! ## Spectral gap

The spectral gap `m_phys = E₁ - E₀` is the physical mass of the theory.
It controls the exponential decay of connected correlation functions. -/

/-- **The spectral gap is strictly positive**: `E₁ - E₀ > 0`.

This is equivalent to `transferEigenvalue 0 > transferEigenvalue 1`
(already stated as `transferEigenvalue_ground_simple`), since
`Eₙ = -(1/a) log λₙ`.

Physical interpretation: the theory has a nonzero mass gap. There is
a gap between the vacuum and the first excited state. -/
theorem spectral_gap_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    0 < massGap P a mass ha hmass :=
  massGap_pos P a mass ha hmass

/-! ## Uniform lower bound on the spectral gap

The mass gap is bounded below uniformly in the lattice spacing a.
This is crucial for transferring OS4 (clustering) to the continuum limit. -/

/-- The spectral gap is bounded below uniformly in the lattice spacing.

  `∃ m₀ > 0, ∀ a ∈ (0, a₀], massGap P a mass ≥ m₀`

Proof outline: The confining potential V(ψ) grows as |ψ|^{2p} where
p = deg(P)/2 ≥ 2. As a → 0:
- The spatial kinetic term `a⁻² Σ (ψ(x+1) - ψ(x))²` grows, which
  increases the gap (stronger confinement in the field space directions
  transverse to the constant mode).
- The on-site potential `Σ :P(ψ(x)):` provides a uniform lower bound
  on the gap for the zero mode.

The rigorous proof uses cluster expansion techniques
(Glimm-Jaffe-Spencer) to control the perturbative corrections. -/
axiom spectral_gap_uniform (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∃ a₀ : ℝ, 0 < a₀ ∧
    ∀ (a : ℝ) (ha : 0 < a), a ≤ a₀ →
    m₀ ≤ massGap P a mass ha hmass

/-- The spectral gap has an explicit lower bound in terms of the bare mass.

For the free field (P = 0), the mass gap equals the bare mass m.
For the interacting theory, the physical mass is shifted but remains
positive: `m_phys ≥ c · m` for some constant c depending on P. -/
axiom spectral_gap_lower_bound (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    c * mass ≤ massGap P a mass ha hmass

end Pphi2

end
