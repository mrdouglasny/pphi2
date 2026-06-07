/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.InteractionFourPoint

/-!
# Leading-term lower bound (uniform-discharge leaf `s`)

The covariance-inverts-precision identity and its consequences toward the uniform leading-slope bound
`a²·∑_z(C_a f)(z)⁴ ≥ s > 0`. The key spectral fact:
`⟨T(Q f), T g⟩ = ⟨f, g⟩` where `T = spectralLatticeCovariance`, `Q = massOperator = −Δ_a + m²` — i.e.
the covariance inverts the precision. Proved from `spectralLatticeCovariance_inner`
(`⟨Tf,Tg⟩ = ∑_k λ_k⁻¹⟨e_k,f⟩⟨e_k,g⟩`), the eigenvector relation
`massOperator_eigenCoeff_eq_eigenvalues_mul_eigenCoeff`, and Parseval/completeness
`eigenbasis_completeness`.
-/

namespace Pphi2

open MeasureTheory GaussianField

variable (d N : ℕ) [NeZero N]

/-- **Covariance inverts precision.** `⟨T(Q f), T g⟩ = ∑_x f(x)·g(x)`, with
`T = spectralLatticeCovariance`, `Q = massOperator`. -/
theorem spectralCov_massOperator_inner (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeField d N) :
    (inner ℝ (spectralLatticeCovariance d N a mass ha hmass (massOperator d N a mass f))
      (spectralLatticeCovariance d N a mass ha hmass g) : ℝ) = ∑ x, f x * g x := by
  rw [spectralLatticeCovariance_inner]
  -- cancel `λ_k⁻¹ · λ_k` using the eigenvector relation on the `Q f` factor
  have step1 : ∀ k : FinLatticeSites d N,
      (massEigenvalues d N a mass k)⁻¹ *
          (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
            (massOperator d N a mass f) x) *
          (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x) =
        (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
          (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x) := by
    intro k
    rw [massOperator_eigenCoeff_eq_eigenvalues_mul_eigenCoeff]
    have hk : massEigenvalues d N a mass k ≠ 0 :=
      (massOperatorMatrix_eigenvalues_pos d N a mass ha hmass k).ne'
    field_simp
  rw [Finset.sum_congr rfl (fun k _ => step1 k)]
  -- Parseval collapse via eigenbasis_completeness
  calc ∑ k, (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
          (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x)
      = ∑ k, ∑ x, ∑ y, ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
          ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y * g y) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_mul_sum _ _ _ _
    _ = ∑ x, ∑ y, ∑ k, ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
          ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y * g y) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x, f x * g x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have hcol : ∀ y, (∑ k, ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
              ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y * g y)) =
            f x * g y * (if y = x then (1 : ℝ) else 0) := by
          intro y
          rw [← eigenbasis_completeness d N a mass x y, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
        simp_rw [hcol]
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Pphi2
