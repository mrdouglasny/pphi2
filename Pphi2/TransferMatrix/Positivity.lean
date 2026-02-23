/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Transfer Matrix: Self-Adjointness and Positivity

The transfer matrix kernel T(ψ, ψ') defines a positive, self-adjoint,
trace-class operator on L²(ℝ^Ns). Its positivity (in both the operator
and kernel senses) is the foundation for reflection positivity.

## Main results

- `transferKernel_symmetric` — T(ψ, ψ') = T(ψ', ψ) (proved in TransferMatrix.lean)
- `transferOperator_selfAdjoint` — T is self-adjoint on L²
- `transferOperator_positiveDefinite` — ⟨f, Tf⟩ ≥ 0
- `transferOperator_traceClass` — T is trace class (compact with summable eigenvalues)

## Mathematical background

Since T(ψ, ψ') > 0 for all ψ, ψ' (strictly positive kernel), the transfer
operator T is:

1. **Self-adjoint** on L²(ℝ^Ns): because T(ψ,ψ') = T(ψ',ψ).

2. **Positive** (as an operator): ⟨f, Tf⟩ = ∫∫ f(ψ) T(ψ,ψ') f(ψ') dψ dψ' ≥ 0
   because the kernel is positive.

3. **Hilbert-Schmidt** (hence compact): ∫∫ T(ψ,ψ')² dψ dψ' < ∞
   because T(ψ,ψ') ≤ exp(C) · exp(-½ Σ(ψ-ψ')²) which is L².

4. **Trace class**: T = T^{1/2} · T^{1/2} and T^{1/2} is Hilbert-Schmidt
   (because T^{1/2} also has a Gaussian-bounded kernel).

By the spectral theorem, T has eigenvalues λ₀ ≥ λ₁ ≥ ... > 0 with
eigenfunctions forming an orthonormal basis of L².

Writing T = e^{-aH}, the Hamiltonian H = -(1/a) log T has discrete
spectrum E₀ ≤ E₁ ≤ ..., where Eₙ = -(1/a) log λₙ.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1 (Transfer matrix)
- Simon, *The P(φ)₂ Euclidean QFT*, §III.2 (Positivity)
- Reed-Simon, *Methods of Modern Mathematical Physics IV*, §XIII.12
-/

import Pphi2.TransferMatrix.TransferMatrix

noncomputable section

open GaussianField Real MeasureTheory

namespace Pphi2

variable (Ns : ℕ) [NeZero Ns]

/-! ## Operator properties of the transfer matrix

The transfer kernel T(ψ, ψ') defines an integral operator on L²(ℝ^Ns).
We state key operator-theoretic properties as axioms, since the L² operator
theory needed to formalize them is beyond current Mathlib. -/

/-- The transfer operator is self-adjoint on L²(ℝ^Ns).

This follows from `transferKernel_symmetric`: T(ψ,ψ') = T(ψ',ψ),
so `⟨f, Tg⟩ = ∫∫ f(ψ) T(ψ,ψ') g(ψ') = ∫∫ g(ψ') T(ψ',ψ) f(ψ) = ⟨g, Tf⟩`. -/
axiom transferOperator_selfAdjoint (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    True -- Placeholder: T = T* on L²(ℝ^Ns)
    -- Full statement needs L² operator formalism

/-- The transfer operator is positive definite:

  `⟨f, Tf⟩ = ∫∫ f(ψ) T(ψ,ψ') f(ψ') dψ dψ' ≥ 0`

for all f ∈ L²(ℝ^Ns). This follows from the kernel being strictly positive:
T(ψ,ψ') > 0 everywhere. -/
axiom transferOperator_positiveDefinite (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    True -- Placeholder: ⟨f, Tf⟩ ≥ 0 for all f ∈ L²

/-- The transfer operator is Hilbert-Schmidt (hence compact).

  `∫∫ |T(ψ,ψ')|² dψ dψ' < ∞`

Proof outline: The kernel satisfies
  `T(ψ,ψ') ≤ exp(C) · exp(-½ Σ_x (ψ_x - ψ'_x)²)`
where C comes from the lower bound on the spatial action (bounded below).
The Gaussian factor makes the double integral converge. -/
axiom transferOperator_hilbertSchmidt (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    True -- Placeholder: T is Hilbert-Schmidt on L²(ℝ^Ns)

/-- The transfer operator is trace class.

Since T = T^{1/2} · T^{1/2} (positive self-adjoint), and T^{1/2} is
Hilbert-Schmidt (its kernel is also Gaussian-bounded), T is the product
of two Hilbert-Schmidt operators, hence trace class. -/
axiom transferOperator_traceClass (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    True -- Placeholder: T is trace class on L²(ℝ^Ns)

/-! ## Spectral decomposition

By the spectral theorem for compact self-adjoint operators, the transfer
matrix has discrete spectrum. -/

/-- Eigenvalues of the transfer matrix, in decreasing order:
`λ₀ ≥ λ₁ ≥ λ₂ ≥ ... > 0`.

These are strictly positive because T has a strictly positive kernel
(Perron-Frobenius for positivity-preserving operators). -/
axiom transferEigenvalue (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (n : ℕ) : ℝ

/-- All eigenvalues are strictly positive. -/
axiom transferEigenvalue_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (n : ℕ) :
    0 < transferEigenvalue P a mass ha hmass n

/-- The eigenvalues are decreasing. -/
axiom transferEigenvalue_antitone (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    Antitone (transferEigenvalue P a mass ha hmass)

/-- The largest eigenvalue λ₀ is simple (non-degenerate).

This is the Perron-Frobenius theorem for the transfer matrix: since the
kernel T(ψ,ψ') > 0 everywhere, the operator is positivity-improving,
so the ground state eigenvalue is simple and the ground state
eigenfunction is strictly positive. -/
axiom transferEigenvalue_ground_simple (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    transferEigenvalue P a mass ha hmass 0 >
    transferEigenvalue P a mass ha hmass 1

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
  sorry

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
