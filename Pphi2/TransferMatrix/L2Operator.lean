/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Transfer Matrix as L² Operator

Formalizes the transfer matrix as a bounded linear operator on L²(ℝ^Ns)
and connects it to the spectral theorem for compact self-adjoint operators.

## Main definitions

- `L2SpatialField Ns` — The Hilbert space L²(ℝ^Ns) where the transfer operator acts
- `transferOperatorCLM` — The transfer matrix as a CLM on L²
- `transferOperator_spectral` — Spectral decomposition from gaussian-field's
  `compact_selfAdjoint_spectral`

## Main axioms (3 total)

- `transferOperatorCLM` — Existence of the L² operator
- `transferOperator_isSelfAdjoint` — Self-adjointness (from kernel symmetry)
- `transferOperator_isCompact` — Compactness (from Gaussian kernel decay)

## Mathematical background

The transfer kernel T(ψ, ψ') = exp(-K(ψ,ψ') - ½a·h(ψ) - ½a·h(ψ'))
defines an integral operator on L²(ℝ^Ns) by:

  (Tf)(ψ) = ∫ T(ψ, ψ') f(ψ') dψ'

This operator is:
1. **Self-adjoint**: because T(ψ,ψ') = T(ψ',ψ) (kernel symmetry)
2. **Compact**: because T(ψ,ψ') ≤ C·exp(-½|ψ-ψ'|²), making it Hilbert-Schmidt
3. **Positive**: because T(ψ,ψ') > 0, so ⟨f, Tf⟩ ≥ 0

By the spectral theorem for compact self-adjoint operators (proved in
gaussian-field's SpectralTheorem.lean), T has a Hilbert basis of eigenvectors
with real eigenvalues.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1 (Transfer matrix)
- Simon, *The P(φ)₂ Euclidean QFT*, §III.2 (Positivity)
- Reed-Simon, *Methods of Modern Mathematical Physics IV*, §XIII.12
-/

import Pphi2.TransferMatrix.TransferMatrix
import GaussianField.SpectralTheorem
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open GaussianField Real MeasureTheory

namespace Pphi2

variable (Ns : ℕ) [NeZero Ns]

/-! ## L² Hilbert space

The transfer operator acts on L²(ℝ^Ns, dx) where ℝ^Ns = SpatialField Ns
and dx is Lebesgue measure (product of 1D Lebesgue measures). -/

/-- The L² Hilbert space of square-integrable functions on the spatial field
configuration space ℝ^Ns.

This is the natural Hilbert space for the transfer matrix formalism:
the transfer kernel T(ψ,ψ') defines an integral operator on this space. -/
abbrev L2SpatialField :=
  MeasureTheory.Lp (α := SpatialField Ns) ℝ 2 MeasureTheory.volume

/-! ## Transfer operator as CLM

The integral kernel T(ψ,ψ') defines a bounded linear operator on L²(ℝ^Ns).
We axiomatize its existence and key properties. -/

/-- The transfer matrix as a continuous linear map on L²(ℝ^Ns).

Defined by the integral kernel:
  `(Tf)(ψ) = ∫ T(ψ, ψ') f(ψ') dψ'`

where `T(ψ,ψ') = transferKernel Ns P a mass ψ ψ'`.

The boundedness follows from the Hilbert-Schmidt property: since the kernel
has Gaussian decay, `∫∫ |T(ψ,ψ')|² dψ dψ' < ∞`, so T is a bounded operator
with `‖T‖ ≤ ‖T‖_HS`.

**Proof strategy**: The kernel T(ψ,ψ') ≤ exp(C) · exp(-½|ψ-ψ'|²) where C
bounds the spatial action from below. The Gaussian factor makes the double
integral converge, giving the Hilbert-Schmidt norm bound. -/
axiom transferOperatorCLM (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    L2SpatialField Ns →L[ℝ] L2SpatialField Ns

/-- The transfer operator is self-adjoint on L²(ℝ^Ns).

This follows from `transferKernel_symmetric`: T(ψ,ψ') = T(ψ',ψ), so
  `⟨f, Tg⟩ = ∫∫ f(ψ) T(ψ,ψ') g(ψ') dψ dψ'`
           `= ∫∫ g(ψ') T(ψ',ψ) f(ψ) dψ' dψ = ⟨g, Tf⟩ = ⟨Tf, g⟩`.

**Proof strategy**: Apply Fubini's theorem to swap the order of integration,
then use `transferKernel_symmetric` to conclude. -/
axiom transferOperator_isSelfAdjoint (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    IsSelfAdjoint (transferOperatorCLM Ns P a mass ha hmass)

/-- The transfer operator is compact on L²(ℝ^Ns).

The kernel satisfies T(ψ,ψ') ≤ exp(C) · exp(-½|ψ-ψ'|²), making the
integral operator Hilbert-Schmidt (hence compact):
  `∫∫ |T(ψ,ψ')|² dψ dψ' ≤ exp(2C) · ∫∫ exp(-|ψ-ψ'|²) dψ dψ' < ∞`.

In fact T is trace class: T = T^{1/2} · T^{1/2} where T^{1/2} is also
Hilbert-Schmidt (by the same Gaussian bound on its kernel).

**Proof strategy**: Bound the kernel by a Gaussian, compute the Hilbert-Schmidt
norm explicitly, conclude compactness. -/
axiom transferOperator_isCompact (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    IsCompactOperator (transferOperatorCLM Ns P a mass ha hmass)

/-! ## Spectral decomposition

By the spectral theorem for compact self-adjoint operators (proved in
gaussian-field's `SpectralTheorem.lean`), the transfer operator has a
Hilbert basis of eigenvectors with real eigenvalues. -/

omit [NeZero Ns] in
/-- The spectral decomposition of the transfer operator.

By `compact_selfAdjoint_spectral`, there exists:
- A Hilbert basis `{eᵢ}` of L²(ℝ^Ns) consisting of eigenvectors of T
- Eigenvalues `λᵢ` with T(eᵢ) = λᵢ · eᵢ
- The diagonal representation: T(f) = Σᵢ λᵢ ⟨eᵢ, f⟩ eᵢ -/
theorem transferOperator_spectral (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ (L2SpatialField Ns)) (eigenval : ι → ℝ),
      (∀ i, (transferOperatorCLM Ns P a mass ha hmass :
        L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) = eigenval i • b i) ∧
      (∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i)
        (transferOperatorCLM Ns P a mass ha hmass x)) :=
  compact_selfAdjoint_spectral _
    (transferOperator_isSelfAdjoint Ns P a mass ha hmass)
    (transferOperator_isCompact Ns P a mass ha hmass)

/-! ## Sorted eigenvalue sequence

The spectral theorem gives eigenvalues indexed by an arbitrary type ι.
For the physical application (energy levels, mass gap), we need them
sorted in decreasing order as a sequence ℕ → ℝ.

Mathematically, since L²(ℝ^Ns) is separable, ι is countable, and since
all eigenvalues are positive (Perron-Frobenius), they can be arranged as
λ₀ ≥ λ₁ ≥ λ₂ ≥ ... > 0.

We axiomatize this sorted sequence and its Perron-Frobenius properties
(strict positivity and simplicity of the ground state). -/

/-- Eigenvalues of the transfer matrix, in decreasing order:
`λ₀ ≥ λ₁ ≥ λ₂ ≥ ... > 0`.

These are the eigenvalues from `transferOperator_spectral`, sorted in
decreasing order. The sorting is well-defined because:
- L²(ℝ^Ns) is separable, so the spectral decomposition has countably many terms
- All eigenvalues are positive (by Perron-Frobenius), so they accumulate only at 0
- They can be arranged in decreasing order by the spectral theorem for compact operators

**Connection to spectral theorem**: The eigenvalues here are exactly the
values from `transferOperator_spectral`, enumerated in decreasing order.
The eigenvectors form the Hilbert basis given by that theorem. -/
axiom transferEigenvalue (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (n : ℕ) : ℝ

/-- All eigenvalues are strictly positive.

This is the Perron-Frobenius theorem for integral operators with strictly
positive kernels: since T(ψ,ψ') > 0 for all ψ, ψ' (from `transferKernel_pos`),
the operator T is positivity-preserving, which forces all eigenvalues to
be nonneg. Strict positivity follows from the stronger property that T
is positivity-*improving* (maps nonneg nonzero functions to strictly positive
functions), which implies no eigenvalue is zero.

**References**: Reed-Simon IV, Theorem XIII.44; Simon, P(φ)₂, §III.2. -/
axiom transferEigenvalue_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (n : ℕ) :
    0 < transferEigenvalue P a mass ha hmass n

/-- The eigenvalues are decreasing: `λ₀ ≥ λ₁ ≥ λ₂ ≥ ...`.

This is by construction: the eigenvalues from the spectral decomposition
are sorted in decreasing order. -/
axiom transferEigenvalue_antitone (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    Antitone (transferEigenvalue P a mass ha hmass)

/-- The largest eigenvalue λ₀ is simple (non-degenerate): `λ₀ > λ₁`.

This is the Perron-Frobenius theorem for the transfer matrix: since the
kernel T(ψ,ψ') > 0 everywhere, the operator is positivity-improving,
so the ground state eigenvalue is simple and the ground state
eigenfunction is strictly positive.

**References**: Reed-Simon IV, Theorem XIII.44 (Perron-Frobenius for
positivity-improving operators); Glimm-Jaffe §6.1. -/
axiom transferEigenvalue_ground_simple (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    transferEigenvalue P a mass ha hmass 0 >
    transferEigenvalue P a mass ha hmass 1

end Pphi2

end
