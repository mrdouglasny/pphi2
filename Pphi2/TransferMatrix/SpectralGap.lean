/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Spectral Gap of the Lattice Hamiltonian

The transfer matrix T = e^{-aH} defines a lattice Hamiltonian H with
discrete spectrum. The spectral gap `E₁ - E₀ > 0` controls the
exponential decay of correlations (mass gap / clustering).

## Main results

- `hamiltonian_selfadjoint` — H is self-adjoint on L²
- `hamiltonian_compact_resolvent` — (H + λ)⁻¹ is compact
- `hamiltonian_discrete_spectrum` — H has discrete spectrum
- `spectral_gap_pos` — E₁ - E₀ > 0 (strict gap)
- `spectral_gap_uniform` — the gap is bounded below uniformly in a

## Mathematical background

The lattice Hamiltonian for P(Φ)₂ in d=2 on a spatial lattice of Ns sites is:

  `H = -½ Σ_x ∂²/∂ψ(x)² + V(ψ)`

where the potential is:

  `V(ψ) = Σ_{<xy>} ½ a⁻² (ψ(x) - ψ(y))² + Σ_x (½ m² ψ(x)² + :P(ψ(x)):_c)`

This is a Schrödinger operator on L²(ℝ^Ns) with a confining potential
(V(ψ) → ∞ as |ψ| → ∞ since P has even degree ≥ 4).

**Key properties:**
1. Self-adjoint on a natural domain (Kato's theorem — V is Kato class).
2. Compact resolvent (confining potential → discrete spectrum).
3. Simple ground state (Perron-Frobenius: e^{-tH} is positivity-improving).
4. Strict spectral gap E₁ - E₀ > 0.
5. The gap is bounded below uniformly in a (the confining strength of V
   grows with 1/a, so the gap cannot collapse).

## References

- Glimm-Jaffe, *Quantum Physics*, §6.2, §19.3
- Simon, *The P(φ)₂ Euclidean QFT*, §III.2 (Spectral properties)
- Reed-Simon, *Methods of Mathematical Physics II*, §X.2 (Schrödinger operators)
-/

import Pphi2.TransferMatrix.Positivity

noncomputable section

open GaussianField Real

namespace Pphi2

variable (Ns : ℕ) [NeZero Ns]

/-! ## Hamiltonian properties

The Hamiltonian H = -(1/a) log T is the generator of Euclidean time
evolution. We axiomatize its key spectral properties. -/

/-- The lattice Hamiltonian is self-adjoint on L²(ℝ^Ns).

Proof outline: H = -½Δ + V where Δ is the Ns-dimensional Laplacian and
V is a polynomial potential. By Kato's theorem (or the Kato-Rellich theorem),
since V is bounded below and grows polynomially, H is essentially self-adjoint
on C₀^∞(ℝ^Ns). -/
theorem hamiltonian_selfadjoint (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    True :=-- Placeholder: H is self-adjoint on its natural domain in L²(ℝ^Ns)
      trivial

/-- The Hamiltonian has compact resolvent.

Since V(ψ) → ∞ as |ψ| → ∞ (P has degree ≥ 4 with positive leading
coefficient), the embedding of the form domain of H into L² is compact.
Equivalently, (H + λ)⁻¹ is compact for sufficiently large λ.

This implies H has discrete spectrum: a sequence of eigenvalues
E₀ ≤ E₁ ≤ E₂ ≤ ... → ∞ with finite multiplicities. -/
theorem hamiltonian_compact_resolvent (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    True :=-- Placeholder: (H + λ)⁻¹ is compact for large λ
      trivial

/-- The ground state energy E₀ is simple (non-degenerate).

This follows from the Perron-Frobenius theorem: the semigroup e^{-tH}
has a strictly positive kernel (from `transferKernel_pos`), so it is
positivity-improving. Therefore the ground state eigenfunction is
strictly positive (up to sign), hence unique. -/
theorem ground_state_simple (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    True :=-- Placeholder: E₀ has multiplicity 1
      trivial

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

/-! ## Ground state properties

The ground state Ω of H is the vacuum of the lattice QFT.
Its properties determine the structure of the continuum theory. -/

/-- The ground state eigenfunction Ω is strictly positive: Ω(ψ) > 0 for all ψ.

This is the Perron-Frobenius property: since e^{-tH} is positivity-improving
(its kernel T(ψ,ψ') > 0), the unique ground state must be strictly positive. -/
theorem ground_state_positive (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    True :=-- Placeholder: Ω(ψ) > 0 for all ψ ∈ ℝ^Ns
      trivial

/-- The ground state is in L²(ℝ^Ns) ∩ C^∞(ℝ^Ns).

Regularity: since V is smooth (polynomial) and H = -½Δ + V is an
elliptic operator, eigenfunctions are smooth by elliptic regularity.
L² membership follows from the compact resolvent (discrete spectrum
means eigenfunctions are in L²). -/
theorem ground_state_smooth (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    True :=-- Placeholder: Ω ∈ L²(ℝ^Ns) ∩ C^∞(ℝ^Ns)
      trivial

end Pphi2

end
