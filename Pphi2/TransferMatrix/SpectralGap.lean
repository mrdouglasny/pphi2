/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Spectral Gap of the Lattice Hamiltonian

The transfer matrix T = e^{-aH} defines a lattice Hamiltonian H with
discrete spectrum. The spectral gap `E₁ - E₀ > 0` controls the
exponential decay of correlations (mass gap / clustering).

## Main results

- `spectral_gap_pos` — E₁ - E₀ > 0 (strict gap, from `massGap_pos`)

## Removed axioms (2026-07-12)

The former axioms `spectral_gap_uniform` and `spectral_gap_lower_bound` asserted a
lower bound on `massGap Ns P a mass` **uniform in `a → 0` at fixed `Ns`**. That
regime has shrinking physical volume `Ns·a → 0`, where the hard-coded 2D Wick
constant is the wrong counterterm: its zero-mode contribution `(a²Ns²m²)⁻¹`
diverges like `a⁻²`, the over-subtraction gives the spatial zero mode a symmetric
double well (minima `~ a⁻¹`, barrier `~ a⁻³`), and the gap closes as a tunneling
splitting `massGap ~ (1/a)·exp(−c/a²) → 0` — at every coupling. Both axioms were
therefore **false as stated** and have been removed (they had no proof-term
consumers; Main's OS4 rests on `continuum_exponential_clustering`). The corrected
statement — the gap along a *coupled* sequence (fixed `L = N·a`, or `N·a → ∞`
under weak coupling) — is recorded with its discharge route in
`planning/cyl-2a-volume-scaling-addendum.md` and will be introduced only with its
consumer (the OS4 campaign). See `AXIOM_AUDIT.md` (2026-07-12 entry).

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

variable (Ns : ℕ) [NeZero Ns]

/-! ## Spectral gap

The spectral gap `m_phys = E₁ - E₀` is the physical mass of the theory.
It controls the exponential decay of connected correlation functions. -/

/-- **The spectral gap is strictly positive**: `E₁ - E₀ > 0`.

This follows from strict Perron-Frobenius separation on the spectral data
(`transferOperator_ground_simple`) and positivity of eigenvalues, since
`E = -(1/a) log λ`.

Physical interpretation: the theory has a nonzero mass gap. There is
a gap between the vacuum and the first excited state. -/
theorem spectral_gap_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    0 < massGap Ns P a mass ha hmass :=
  massGap_pos Ns P a mass ha hmass

end Pphi2

end
