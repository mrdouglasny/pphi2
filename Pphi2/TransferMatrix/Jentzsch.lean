/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Jentzsch's Theorem and Kernel Positivity (Axiomatized)

This file axiomatizes spectral-theoretic facts about the transfer operator
and derives the Perron-Frobenius properties needed for the P(Φ)₂ construction.

## Axiom 1: Jentzsch's theorem (Reed-Simon IV, XIII.43–44)

For a compact, self-adjoint, positivity-improving operator T on L² with
eigenbasis indexed by a type with ≥ 2 elements:
- The spectral radius r is a simple eigenvalue with strictly positive value.
- All other eigenvalues λ satisfy |λ| < r.

**Important**: Jentzsch does NOT imply all eigenvalues are positive.
Counterexample: [[1,2],[2,1]] is positivity-improving with eigenvalues 3,-1.

## Axiom 2: Transfer operator positivity-improving

The kernel T(ψ,ψ') = w(ψ)·G(ψ-ψ')·w(ψ') > 0 is strictly positive.

## Axiom 3: Gaussian kernel is strictly positive definite

⟨f, Tf⟩ > 0 for nonzero f, since the Gaussian kernel exp(-½‖·‖²) has
strictly positive Fourier transform (Bochner), and w > 0 preserves this.

## Axiom 4: L²(ℝ^Ns) Hilbert basis nontriviality

Any Hilbert basis of L²(ℝ^Ns) has at least 2 elements.

## Derived theorems

From axioms 1-4 we derive:
- `transferOperator_inner_nonneg`: ⟨f, Tf⟩ ≥ 0
- `transferOperator_eigenvalues_pos`: all λᵢ > 0
- `transferOperator_ground_simple`: unique leading eigenvalue with strict gap
- `transferOperator_ground_simple_spectral`: packaged spectral data

## References

- Reed-Simon IV, Theorems XIII.43–44
- Simon, *The P(φ)₂ Euclidean QFT*, §III.2
- Glimm-Jaffe, *Quantum Physics*, §6.1
-/

import Pphi2.TransferMatrix.L2Operator

noncomputable section

open MeasureTheory

/-! ## Positivity-improving operators -/

/-- An operator on L²(ℝ^n) is positivity-improving if it maps nonneg
nonzero functions to a.e. strictly positive functions. -/
def IsPositivityImproving {n : ℕ}
    (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ))) : Prop :=
  ∀ f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)),
    (∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), 0 ≤ (f : (Fin n → ℝ) → ℝ) x) →
    (¬ (f : (Fin n → ℝ) → ℝ) =ᵐ[volume] 0) →
    (∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), 0 < (T f : (Fin n → ℝ) → ℝ) x)

/-! ## Axiom 1: Jentzsch's theorem -/

/-- **Jentzsch's theorem** for compact self-adjoint positivity-improving
operators on L²(ℝ^n).

Given a nontrivial eigenbasis (|ι| ≥ 2), there exists a distinguished index
i₀ (ground) such that:
(a) λ(i₀) > 0 (the leading eigenvalue is strictly positive).
(b) λ(i₀) is simple: it is the unique index with this eigenvalue.
(c) |λ(i)| < λ(i₀) for all i ≠ i₀ (strict spectral gap).

This is Reed-Simon IV, Theorems XIII.43–44. -/
axiom jentzsch_theorem {n : ℕ}
    (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hT_compact : IsCompactOperator T)
    (hT_sa : IsSelfAdjoint T)
    (hT_pi : IsPositivityImproving T) :
    ∀ {ι : Type}
      (b : HilbertBasis ι ℝ (Lp ℝ 2 (volume : Measure (Fin n → ℝ))))
      (eigenval : ι → ℝ)
      (h_eigen : ∀ i,
        (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →ₗ[ℝ]
          Lp ℝ 2 (volume : Measure (Fin n → ℝ))) (b i) = eigenval i • b i)
      (h_sum : ∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i) (T x))
      (h_nt : ∃ j k : ι, j ≠ k),
    ∃ i₀ : ι,
      (0 < eigenval i₀) ∧
      (∀ i, eigenval i = eigenval i₀ → i = i₀) ∧
      (∀ i, i ≠ i₀ → |eigenval i| < eigenval i₀)

namespace Pphi2

variable (Ns : ℕ) [NeZero Ns]

/-! ## Axiom 2: Transfer operator is positivity-improving -/

/-- The transfer operator is positivity-improving.

The kernel `T(ψ,ψ') = exp(-(a/2)h(ψ)) · exp(-½‖ψ-ψ'‖²) · exp(-(a/2)h(ψ')) > 0`
is strictly positive for all ψ, ψ'. For f ≥ 0, f ≠ 0, the set
S = {ψ' : f(ψ') > 0} has positive measure, so
(Tf)(ψ) = ∫ T(ψ,ψ') f(ψ') dψ' ≥ ∫_S T(ψ,ψ') f(ψ') dψ' > 0. -/
axiom transferOperator_positivityImproving (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    IsPositivityImproving (transferOperatorCLM Ns P a mass ha hmass)

/-! ## Axiom 3: Strictly positive definite kernel

The Gaussian kernel exp(-½‖x-y‖²) is strictly positive definite: its Fourier
transform is (2π)^{n/2} exp(-½‖k‖²) > 0 everywhere, so by Bochner's theorem
G is strictly PD on L². The full kernel K(x,y) = w(x)G(x-y)w(y) with
w = exp(-(a/2)h) > 0 preserves strict PD (Schur product with w⊗w), giving
⟨f, Tf⟩ = ∫∫ K(x,y) f(x) f(y) dx dy > 0 for all nonzero f ∈ L². -/

/-- The transfer operator is strictly positive definite: ⟨f, Tf⟩ > 0 for
all nonzero f ∈ L².

This follows from:
1. The Gaussian kernel G(x-y) = exp(-½‖x-y‖²) is strictly PD
   (Bochner's theorem: Fourier transform is strictly positive).
2. K(x,y) = w(x)·G(x-y)·w(y) with w > 0 is strictly PD.
3. ⟨f, Tf⟩ = ∫∫ K(x,y) f(x) f(y) dx dy > 0 for f ≠ 0.

**References**: Reed-Simon I, §VI.5; Stein-Shakarchi, *Real Analysis*, Ch. 6. -/
axiom transferOperator_strictly_positive_definite (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∀ (f : L2SpatialField Ns), f ≠ 0 →
      0 < @inner ℝ _ _ f (transferOperatorCLM Ns P a mass ha hmass f)

/-! ## Axiom 4: L²(ℝ^Ns) Hilbert basis nontriviality

L²(ℝ^Ns, Lebesgue) is infinite-dimensional (it contains orthogonal Hermite
functions, indicator functions of disjoint sets, etc.), so any Hilbert basis
has at least 2 elements. -/

/-- Any Hilbert basis of L²(ℝ^Ns) has at least 2 elements.

L²(ℝ^Ns) with Lebesgue measure is infinite-dimensional (it contains
the countably many orthogonal Hermite functions), so any orthonormal
basis must be infinite. -/
axiom l2SpatialField_hilbertBasis_nontrivial
    {ι : Type} (b : HilbertBasis ι ℝ (L2SpatialField Ns)) :
    ∃ j k : ι, j ≠ k

/-! ## Derived theorems

We now derive the Perron-Frobenius properties of the transfer
operator from the axioms above. These have the same signatures as the
former axioms in L2Operator.lean, ensuring downstream compatibility. -/

/-- ⟨f, Tf⟩ ≥ 0 for all f. Immediate from strict PD (which gives > 0 for f ≠ 0,
and ⟨0, T0⟩ = 0 for f = 0). -/
theorem transferOperator_inner_nonneg (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∀ (f : L2SpatialField Ns),
      0 ≤ @inner ℝ _ _ f (transferOperatorCLM Ns P a mass ha hmass f) := by
  intro f
  by_cases hf : f = 0
  · rw [hf, map_zero, inner_self_eq_zero.mpr rfl]
  · exact le_of_lt (transferOperator_strictly_positive_definite Ns P a mass ha hmass f hf)

/-- All eigenvalues of the transfer operator are strictly positive.

Proof: ⟨bᵢ, T(bᵢ)⟩ = λᵢ · ‖bᵢ‖² = λᵢ > 0 by strict positive definiteness,
since bᵢ ≠ 0 (it has norm 1). -/
theorem transferOperator_eigenvalues_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    {ι : Type} (b : HilbertBasis ι ℝ (L2SpatialField Ns)) (eigenval : ι → ℝ)
    (h_eigen : ∀ i, (transferOperatorCLM Ns P a mass ha hmass :
        L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) = eigenval i • b i)
    (i : ι) : 0 < eigenval i := by
  -- bᵢ ≠ 0 since ‖bᵢ‖ = 1
  have hbi_ne : (b i : L2SpatialField Ns) ≠ 0 := by
    intro h
    have := b.orthonormal.norm_eq_one i
    rw [h, norm_zero] at this
    exact one_ne_zero this.symm
  -- ⟨bᵢ, Tbᵢ⟩ > 0 by strict PD
  have hpd := transferOperator_strictly_positive_definite Ns P a mass ha hmass (b i) hbi_ne
  -- Rewrite ⟨bᵢ, Tbᵢ⟩ = λᵢ · ‖bᵢ‖² = λᵢ
  have h_eigen_i := h_eigen i
  have hconv : (transferOperatorCLM Ns P a mass ha hmass :
    L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) =
    transferOperatorCLM Ns P a mass ha hmass (b i) := rfl
  rw [← hconv, h_eigen_i] at hpd
  rw [@inner_smul_right ℝ, @real_inner_self_eq_norm_sq] at hpd
  have hnorm : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  rw [hnorm, one_pow, mul_one] at hpd
  exact hpd

/-- Ground-state simplicity and existence of first excited level.

Derived from Jentzsch (which gives i₀ with spectral gap) combined with
nontriviality (to pick some i₁ ≠ i₀) and eigenvalue positivity
(to convert |λᵢ| < λ₀ to λᵢ < λ₀). -/
theorem transferOperator_ground_simple (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∀ {ι : Type} (b : HilbertBasis ι ℝ (L2SpatialField Ns)) (eigenval : ι → ℝ)
      (h_eigen : ∀ i, (transferOperatorCLM Ns P a mass ha hmass :
          L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) = eigenval i • b i)
      (h_sum : ∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i)
          (transferOperatorCLM Ns P a mass ha hmass x)),
      ∃ i₀ i₁ : ι, i₁ ≠ i₀ ∧ eigenval i₁ < eigenval i₀ := by
  intro ι b eigenval h_eigen h_sum
  -- Nontriviality: L²(ℝ^Ns) is infinite-dimensional
  have h_nt := l2SpatialField_hilbertBasis_nontrivial Ns b
  -- Jentzsch gives i₀ with positivity, simplicity, and spectral gap
  obtain ⟨i₀, hpos, _hsimple, hgap⟩ := jentzsch_theorem
    (transferOperatorCLM Ns P a mass ha hmass)
    (transferOperator_isCompact Ns P a mass ha hmass)
    (transferOperator_isSelfAdjoint Ns P a mass ha hmass)
    (transferOperator_positivityImproving Ns P a mass ha hmass)
    b eigenval h_eigen h_sum h_nt
  -- Pick any i₁ ≠ i₀ from nontriviality
  obtain ⟨j, k, hjk⟩ := h_nt
  have h_exists_ne : ∃ i₁, i₁ ≠ i₀ := by
    by_cases hj : j = i₀
    · exact ⟨k, fun hk => hjk (hj.trans hk.symm)⟩
    · exact ⟨j, hj⟩
  obtain ⟨i₁, hi₁_ne⟩ := h_exists_ne
  -- All eigenvalues positive, so |λᵢ| = λᵢ → gap gives λ(i₁) < λ(i₀)
  have hall_pos : ∀ i, 0 < eigenval i :=
    fun i => transferOperator_eigenvalues_pos Ns P a mass ha hmass b eigenval h_eigen i
  have hlt : eigenval i₁ < eigenval i₀ := by
    have := hgap i₁ hi₁_ne
    rwa [abs_of_pos (hall_pos i₁)] at this
  exact ⟨i₀, i₁, hi₁_ne, hlt⟩

/-- Spectral data with distinguished ground and first excited levels. -/
theorem transferOperator_ground_simple_spectral (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ (L2SpatialField Ns)) (eigenval : ι → ℝ)
      (i₀ i₁ : ι),
      (∀ i, (transferOperatorCLM Ns P a mass ha hmass :
          L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) = eigenval i • b i) ∧
      (∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i)
          (transferOperatorCLM Ns P a mass ha hmass x)) ∧
      i₁ ≠ i₀ ∧ eigenval i₁ < eigenval i₀ := by
  rcases transferOperator_spectral Ns P a mass ha hmass with ⟨ι, b, eigenval, h_eigen, h_sum⟩
  rcases transferOperator_ground_simple Ns P a mass ha hmass b eigenval h_eigen h_sum
    with ⟨i₀, i₁, hi_ne, hlt⟩
  exact ⟨ι, b, eigenval, i₀, i₁, h_eigen, h_sum, hi_ne, hlt⟩

end Pphi2

end
