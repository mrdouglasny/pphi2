/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Transfer Matrix: Hamiltonian and Energy Levels

Defines the lattice Hamiltonian H = -(1/a) log T and its spectral properties
(energy levels, mass gap) from the transfer matrix eigenvalues.

## Main results

- `energyLevel` — Energy levels Eₙ = -(1/a) log λₙ
- `energyLevel_gap` — E₀ < E₁ (strict gap, from Perron-Frobenius)
- `massGap` — Physical mass gap m = E₁ - E₀
- `massGap_pos` — The mass gap is strictly positive

## Mathematical background

The transfer matrix T = e^{-aH} is a compact self-adjoint operator on L²(ℝ^Ns)
with strictly positive eigenvalues λ₀ > λ₁ ≥ λ₂ ≥ ... > 0 (see L2Operator.lean).

The lattice Hamiltonian H = -(1/a) log T has discrete spectrum with energy
levels Eₙ = -(1/a) log λₙ, satisfying E₀ < E₁ ≤ E₂ ≤ ...

The mass gap m = E₁ - E₀ > 0 is the fundamental physical quantity controlling
exponential decay of correlations.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1 (Transfer matrix)
- Simon, *The P(φ)₂ Euclidean QFT*, §III.2 (Positivity)
- Reed-Simon, *Methods of Modern Mathematical Physics IV*, §XIII.12
-/

import Pphi2.TransferMatrix.L2Operator

noncomputable section

open GaussianField Real MeasureTheory

namespace Pphi2

/-! ## Hamiltonian

The transfer matrix is T = e^{-aH} where H is the lattice Hamiltonian.
The eigenvalues of H are Eₙ = -(1/a) log λₙ. -/

/-- Energy levels of the lattice Hamiltonian: `Eₙ = -(1/a) log λₙ`.

Since λₙ > 0 and decreasing, the energies are increasing: E₀ ≤ E₁ ≤ ... -/
def energyLevel (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (n : ℕ) : ℝ :=
  -(1 / a) * Real.log (transferEigenvalue P a mass ha hmass n)

/-- The ground state energy E₀ < E₁ (strict gap).

This is equivalent to `λ₀ > λ₁`, which is the Perron-Frobenius property. -/
theorem energyLevel_gap (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    energyLevel P a mass ha hmass 0 < energyLevel P a mass ha hmass 1 := by
  unfold energyLevel
  have h := transferEigenvalue_ground_simple P a mass ha hmass
  have hlam0 := transferEigenvalue_pos P a mass ha hmass 0
  have hlam1 := transferEigenvalue_pos P a mass ha hmass 1
  -- -(1/a) log λ₀ < -(1/a) log λ₁ because λ₀ > λ₁ > 0 and -(1/a) < 0
  have ha_neg : -(1 / a) < 0 := by linarith [div_pos one_pos ha]
  have hlog : Real.log (transferEigenvalue P a mass ha hmass 1) <
      Real.log (transferEigenvalue P a mass ha hmass 0) :=
    Real.log_lt_log hlam1 h
  exact mul_lt_mul_of_neg_left hlog ha_neg

/-- The mass gap: `m_phys = E₁ - E₀ > 0`. -/
def massGap (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) : ℝ :=
  energyLevel P a mass ha hmass 1 - energyLevel P a mass ha hmass 0

/-- The mass gap is strictly positive. -/
theorem massGap_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    0 < massGap P a mass ha hmass := by
  unfold massGap
  linarith [energyLevel_gap P a mass ha hmass]

end Pphi2

end
