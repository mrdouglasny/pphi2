/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Jentzsch's Theorem (Axiomatized)

Jentzsch's theorem is the infinite-dimensional L² extension of the
Perron-Frobenius theorem for matrices with positive entries. It applies
to compact, self-adjoint, positivity-improving integral operators on L²
spaces, giving:

1. The spectral radius r = ‖T‖ is a simple eigenvalue.
2. The corresponding eigenfunction is strictly positive a.e.
3. All other eigenvalues λ satisfy |λ| < r.

**Important**: Jentzsch does NOT imply all eigenvalues are positive.
A compact self-adjoint positivity-improving operator can have negative
eigenvalues (e.g. the matrix [[1,2],[2,1]] has eigenvalues 3 and -1).

For the P(Φ)₂ transfer operator specifically, all eigenvalues ARE positive
because the Gaussian kernel exp(-½‖ψ-ψ'‖²) is a positive definite kernel,
making T a positive operator (⟨f,Tf⟩ ≥ 0). This is axiomatized separately
as `transferOperator_inner_nonneg` in L2Operator.lean.

## References

- Reed-Simon IV, *Methods of Modern Mathematical Physics*, Theorems XIII.43–44
- Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, §III.2
- Glimm-Jaffe, *Quantum Physics*, §6.1 (Perron-Frobenius for transfer matrices)
- R. Jentzsch, "Über Integralgleichungen mit positivem Kern" (1912)
-/

import Pphi2.TransferMatrix.L2Operator

noncomputable section

open MeasureTheory

/-! ## Positivity-improving operators

An operator T on L²(X, μ) is positivity-improving if it maps nonneg
nonzero functions to strictly positive functions.

For our transfer operator T = M_w ∘ Conv_G ∘ M_w, this holds because
the kernel T(ψ,ψ') = w(ψ) · G(ψ-ψ') · w(ψ') > 0 is strictly positive
everywhere (each factor is exp(−something), hence > 0). -/

/-- An operator on L²(ℝ^n) is positivity-improving if it maps nonneg
nonzero functions to a.e. strictly positive functions.

For the transfer operator, this follows from the strict positivity of
the kernel: `T(ψ,ψ') = exp(-timeCoupling - (a/2)h(ψ) - (a/2)h(ψ')) > 0`
for all ψ, ψ'. -/
def IsPositivityImproving {n : ℕ}
    (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ))) : Prop :=
  ∀ f : Lp ℝ 2 (volume : Measure (Fin n → ℝ)),
    (∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), 0 ≤ (f : (Fin n → ℝ) → ℝ) x) →
    (¬ (f : (Fin n → ℝ) → ℝ) =ᵐ[volume] 0) →
    (∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), 0 < (T f : (Fin n → ℝ) → ℝ) x)

/-! ## Jentzsch's Theorem (axiomatized)

We axiomatize the spectral consequences of Jentzsch's theorem for
compact, self-adjoint, positivity-improving operators on L²(ℝ^n).

Given a spectral decomposition T(eᵢ) = λᵢ·eᵢ from the compact
self-adjoint spectral theorem, Jentzsch's theorem implies:

1. There exists a unique ground state index i₀ with eigenvalue
   λ(i₀) = ‖T‖ (the spectral radius).
2. This eigenvalue is simple: no other basis vector shares it.
3. All other eigenvalues satisfy |λ(i)| < λ(i₀).

Note: The theorem does NOT claim all eigenvalues are positive.
A positivity-improving operator can have negative eigenvalues. -/

/-- **Jentzsch's theorem** for compact self-adjoint positivity-improving
operators on L²(ℝ^n).

Given:
- T is compact and self-adjoint on L²(ℝ^n)
- T is positivity-improving (maps nonneg nonzero functions to a.e. positive)
- {eᵢ, λᵢ} is a spectral decomposition (T eᵢ = λᵢ eᵢ)

Then there exists a unique ground state index i₀ such that:
(a) λ(i₀) > 0 (the leading eigenvalue is strictly positive).
(b) λ(i₀) is simple: it is the unique index with this eigenvalue.
(c) |λ(i)| < λ(i₀) for all i ≠ i₀ (strict spectral gap in magnitude).

This is Reed-Simon IV, Theorems XIII.43–44.

**Proof sketch**:
1. By Krein-Rutman, the spectral radius r = ‖T‖ > 0 is an eigenvalue
   with a nonneg eigenfunction φ. T positivity-improving gives φ > 0 a.e.
2. If r had multiplicity > 1, there would exist an eigenfunction ψ
   orthogonal to φ with Tψ = rψ. But ψ ⊥ φ with φ > 0 forces ψ to
   change sign. Then T|ψ| ≥ T(ψ⁺) > 0 but ⟨φ, T|ψ|⟩ = r⟨φ,|ψ|⟩ and
   ⟨φ, Tψ⟩ = r⟨φ,ψ⟩ = 0, giving a contradiction.
3. If |λ| = r for some other eigenvalue, a similar argument using the
   eigenfunction and its positive/negative parts gives a contradiction. -/
axiom jentzsch_theorem {n : ℕ}
    (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (hT_compact : IsCompactOperator T)
    (hT_sa : IsSelfAdjoint T)
    (hT_pi : IsPositivityImproving T) :
    -- For any spectral decomposition from the compact self-adjoint theorem:
    ∀ {ι : Type}
      (b : HilbertBasis ι ℝ (Lp ℝ 2 (volume : Measure (Fin n → ℝ))))
      (eigenval : ι → ℝ)
      (h_eigen : ∀ i,
        (T : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →ₗ[ℝ]
          Lp ℝ 2 (volume : Measure (Fin n → ℝ))) (b i) = eigenval i • b i)
      (h_sum : ∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i) (T x)),
    -- There exists a unique ground state index:
    ∃ i₀ : ι,
      -- (a) The leading eigenvalue is strictly positive:
      (0 < eigenval i₀) ∧
      -- (b) Simplicity: i₀ is the unique index with the maximal eigenvalue:
      (∀ i, eigenval i = eigenval i₀ → i = i₀) ∧
      -- (c) All other eigenvalues are strictly smaller in magnitude:
      (∀ i, i ≠ i₀ → |eigenval i| < eigenval i₀)

namespace Pphi2

variable (Ns : ℕ) [NeZero Ns]

/-! ## Transfer operator is positivity-improving

The transfer kernel T(ψ,ψ') = w(ψ) · G(ψ-ψ') · w(ψ') is strictly
positive everywhere since w(ψ) = exp(-(a/2)·h(ψ)) > 0 and
G(x) = exp(-½‖x‖²) > 0. This makes the operator positivity-improving:
for any f ≥ 0, f ≠ 0,
  (Tf)(ψ) = ∫ T(ψ,ψ') f(ψ') dψ' > 0
since the integrand T(ψ,ψ')·f(ψ') ≥ 0 with strict positivity on a
set of positive measure. -/

/-- The transfer operator is positivity-improving.

This is a direct consequence of the strict positivity of the kernel:
`T(ψ,ψ') = exp(-(a/2)h(ψ)) · exp(-½‖ψ-ψ'‖²) · exp(-(a/2)h(ψ')) > 0`
for all ψ, ψ', combined with the integral formula for (Tf)(ψ).

**Proof strategy**: For f ≥ 0 a.e. with f ≠ 0 a.e., the set
S = {ψ' : f(ψ') > 0} has positive measure. For any ψ:
  (Tf)(ψ) = ∫ T(ψ,ψ') f(ψ') dψ' ≥ ∫_S T(ψ,ψ') f(ψ') dψ' > 0
since T(ψ,ψ') > 0 on S and f > 0 on S with μ(S) > 0. -/
axiom transferOperator_positivityImproving (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    IsPositivityImproving (transferOperatorCLM Ns P a mass ha hmass)

/-! ## Deriving ground state simplicity from Jentzsch

We derive `transferOperator_ground_simple` from `jentzsch_theorem`
combined with `transferOperator_eigenvalues_pos` (which is axiomatized
separately in L2Operator.lean, justified by the positive definite
Gaussian kernel making T a positive operator).

The key step: Jentzsch gives |λᵢ| < λ₀ for i ≠ i₀. Since all
eigenvalues are positive (from eigenvalues_pos), this simplifies to
λᵢ < λ₀, and we can find the second-largest eigenvalue i₁. -/

/-- Ground-state simplicity derived from Jentzsch's theorem.

Combines:
- `jentzsch_theorem`: leading eigenvalue is simple, |λ| < λ₀ for others
- `transferOperator_eigenvalues_pos`: all eigenvalues > 0 (from positive
  definite kernel, axiomatized separately)

Together these give: ∃ i₀ i₁ with λ(i₁) < λ(i₀) and
∀ i ≠ i₀, eigenval i ≤ eigenval i₁. -/
theorem transferOperator_ground_simple' (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∀ {ι : Type} (b : HilbertBasis ι ℝ (L2SpatialField Ns)) (eigenval : ι → ℝ)
      (h_eigen : ∀ i, (transferOperatorCLM Ns P a mass ha hmass :
          L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) = eigenval i • b i)
      (h_sum : ∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i)
          (transferOperatorCLM Ns P a mass ha hmass x)),
      ∃ i₀ i₁ : ι, i₁ ≠ i₀ ∧ eigenval i₁ < eigenval i₀ ∧
        (∀ i : ι, i ≠ i₀ → eigenval i ≤ eigenval i₁) := by
  intro ι b eigenval h_eigen h_sum
  -- Step 1: Apply Jentzsch to get i₀ with |λᵢ| < λ(i₀) for i ≠ i₀
  obtain ⟨i₀, hpos, _hsimple, hgap⟩ := jentzsch_theorem
    (transferOperatorCLM Ns P a mass ha hmass)
    (transferOperator_isCompact Ns P a mass ha hmass)
    (transferOperator_isSelfAdjoint Ns P a mass ha hmass)
    (transferOperator_positivityImproving Ns P a mass ha hmass)
    b eigenval h_eigen h_sum
  -- Step 2: All eigenvalues are positive (separate axiom from positive definite kernel)
  have hall_pos : ∀ i, 0 < eigenval i :=
    fun i => transferOperator_eigenvalues_pos Ns P a mass ha hmass b eigenval h_eigen i
  -- Step 3: |λᵢ| < λ(i₀) + λᵢ > 0 gives λᵢ < λ(i₀)
  -- Step 4: Find i₁ = argmax {eigenval i : i ≠ i₀} (exists since L² is
  -- infinite-dimensional, so ι has more than one element)
  -- This requires some classical choice to extract the second-largest.
  sorry

end Pphi2

end
