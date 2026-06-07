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

/-- The discrete Laplacian annihilates constant fields. -/
lemma finiteLaplacian_const (a c : ℝ) :
    finiteLaplacian d N a (fun _ => c) = 0 := by
  ext x
  change finiteLaplacianFun d N a (fun _ => c) x = (0 : FinLatticeField d N) x
  simp only [finiteLaplacianFun, Pi.zero_apply]
  rw [Finset.sum_eq_zero (fun i _ => by show c + c - 2 * c = (0 : ℝ); ring)]
  ring

/-- The mass operator acts on constants by `m²`: `(−Δ_a + m²)·c = m²·c`. -/
lemma massOperator_const (a mass c : ℝ) :
    massOperator d N a mass (fun _ => c) = (fun _ => mass ^ 2 * c) := by
  ext x
  simp only [massOperator, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, finiteLaplacian_const d N a c,
    Pi.add_apply, Pi.neg_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, neg_zero, zero_add]

/-- **Covariance inverts precision (GJ-normalised).**
`covariance(latticeCovarianceGJ)(Q f, g) = (a^d)⁻¹·∑_x f(x)g(x)`. -/
lemma covarianceGJ_massOperator (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeField d N) :
    GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass)
        (massOperator d N a mass f) g = (a ^ d : ℝ)⁻¹ * ∑ x, f x * g x := by
  rw [latticeCovariance_GJ_eq_inv_smul_bare]
  congr 1
  unfold GaussianField.covariance latticeCovariance
  exact spectralCov_massOperator_inner d N a mass ha hmass f g

/-- **Covariance row-sum (zero mode).** `∑_x C(x,z) = 1/(a^d m²)` — the constant is the zero mode of
`−Δ_a`, eigenvalue `m²`. -/
lemma gffPositionCovariance_row_sum (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (z : FinLatticeSites d N) :
    ∑ x, gffPositionCovariance d N a mass x z = (a ^ d : ℝ)⁻¹ * (mass ^ 2)⁻¹ := by
  have hmsq : (mass ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hmass.ne'
  have hsum_single : (∑ x : FinLatticeSites d N, (Pi.single x (1 : ℝ) : FinLatticeField d N))
      = (fun _ => 1) := by
    funext y; simp [Finset.sum_apply, Finset.sum_pi_single']
  have hconst : (fun _ : FinLatticeSites d N => (1 : ℝ))
      = massOperator d N a mass (fun _ => (mass ^ 2)⁻¹) := by
    rw [massOperator_const]; funext x; field_simp
  calc ∑ x, gffPositionCovariance d N a mass x z
      = ∑ x, GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass)
          (Pi.single x 1) (Pi.single z 1) := by
        simp_rw [gffPositionCovariance_eq_covarianceGJ d N a mass ha hmass]
    _ = GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass)
          (fun _ => 1) (Pi.single z 1) := by
        unfold GaussianField.covariance
        rw [← hsum_single, map_sum]
        exact (sum_inner _ _ _).symm
    _ = GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass)
          (massOperator d N a mass (fun _ => (mass ^ 2)⁻¹)) (Pi.single z 1) := by rw [hconst]
    _ = (a ^ d : ℝ)⁻¹ * (mass ^ 2)⁻¹ := by
        rw [covarianceGJ_massOperator]
        congr 1
        simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]

/-- **Leading-term closed form (`s` leaf, uniform-ready).** For the normalised-constant test
function `f = (#sites)⁻¹·1`, the `u₄` leading coefficient evaluates to
`a^d·∑_z(C_a f)(z)⁴ = ((a^d·#sites)³·m⁸)⁻¹`. On the torus `a^d·#sites = L^d` (`lattice_volume_eq`),
so this equals `(L^{3d} m⁸)⁻¹` — manifestly independent of `N`, i.e. the uniform lower bound `s`
consumed by `deriv_affine_bound_neg`. -/
lemma leadingTerm_const_eq (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    a ^ d * ∑ z : FinLatticeSites d N,
        (∑ x, (fun _ : FinLatticeSites d N => (Fintype.card (FinLatticeSites d N) : ℝ)⁻¹) x *
          gffPositionCovariance d N a mass x z) ^ 4
      = ((a ^ d * (Fintype.card (FinLatticeSites d N) : ℝ)) ^ 3 * (mass ^ 2) ^ 4)⁻¹ := by
  have hcard : (Fintype.card (FinLatticeSites d N) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  have had : (a ^ d : ℝ) ≠ 0 := (pow_pos ha d).ne'
  have hmsq : (mass ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hmass.ne'
  have hval : ∀ z : FinLatticeSites d N,
      (∑ x, (Fintype.card (FinLatticeSites d N) : ℝ)⁻¹ * gffPositionCovariance d N a mass x z)
        = (Fintype.card (FinLatticeSites d N) : ℝ)⁻¹ * ((a ^ d : ℝ)⁻¹ * (mass ^ 2)⁻¹) := by
    intro z; rw [← Finset.mul_sum, gffPositionCovariance_row_sum d N a mass ha hmass z]
  rw [Finset.sum_congr rfl (fun z _ => by rw [hval z]), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp

/-- **Leading-term positivity (`s` leaf).** For the normalised-constant test function
`f = (#sites)⁻¹·1`, the `u₄` leading coefficient `a^d·∑_z(C_a f)(z)⁴` is strictly positive. -/
lemma leadingTerm_const_pos (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    0 < a ^ d * ∑ z : FinLatticeSites d N,
      (∑ x, (fun _ : FinLatticeSites d N => (Fintype.card (FinLatticeSites d N) : ℝ)⁻¹) x *
        gffPositionCovariance d N a mass x z) ^ 4 := by
  have hcard : (0 : ℝ) < Fintype.card (FinLatticeSites d N) := by exact_mod_cast Fintype.card_pos
  rw [leadingTerm_const_eq d N a mass ha hmass]
  positivity

end Pphi2
