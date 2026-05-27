/- 
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heterogeneous lattice Wick-variance identity

Supporting translation-invariance and spectral lemmas for the asymmetric-torus Wick constant.
-/

import Pphi2.AsymTorus.AsymLatticeMeasure
import GaussianField.Properties

noncomputable section

open GaussianField

namespace Pphi2

/-- Translation by `v` on asymmetric lattice fields. -/
def asymShift (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (v : AsymLatticeSites Nt Ns) (f : AsymLatticeField Nt Ns) : AsymLatticeField Nt Ns :=
  fun y => f (y - v)

theorem finiteLaplacianAsym_translation_commute (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (v : AsymLatticeSites Nt Ns) (f : AsymLatticeField Nt Ns) :
    finiteLaplacianAsym Nt Ns a (asymShift Nt Ns v f) =
      asymShift Nt Ns v (finiteLaplacianAsym Nt Ns a f) := by
  ext x
  change finiteLaplacianAsymFun Nt Ns a (fun y => f (y - v)) x =
    finiteLaplacianAsymFun Nt Ns a f (x - v)
  simp only [finiteLaplacianAsymFun]
  have h1 : ((x.1 + 1, x.2) : AsymLatticeSites Nt Ns) - v = ((x - v).1 + 1, (x - v).2) := by
    ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have h2 : ((x.1 - 1, x.2) : AsymLatticeSites Nt Ns) - v = ((x - v).1 - 1, (x - v).2) := by
    ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have h3 : ((x.1, x.2 + 1) : AsymLatticeSites Nt Ns) - v = ((x - v).1, (x - v).2 + 1) := by
    ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have h4 : ((x.1, x.2 - 1) : AsymLatticeSites Nt Ns) - v = ((x - v).1, (x - v).2 - 1) := by
    ext <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [h1, h2, h3, h4]

theorem massOperatorAsym_translation_commute (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (v : AsymLatticeSites Nt Ns) (f : AsymLatticeField Nt Ns) :
    massOperatorAsym Nt Ns a mass (asymShift Nt Ns v f) =
      asymShift Nt Ns v (massOperatorAsym Nt Ns a mass f) := by
  have hΔ := finiteLaplacianAsym_translation_commute Nt Ns a v f
  ext x
  simp only [massOperatorAsym, ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, asymShift]
  exact congrArg (fun t => -t + mass ^ 2 * f (x - v)) (congr_fun hΔ x)

theorem spectralCovAsym_massOperator_eq (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f h : AsymLatticeField Nt Ns) :
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) f
      (massOperatorAsym Nt Ns a mass h) =
    ∑ x : AsymLatticeSites Nt Ns, f x * h x := by
  rw [covariance_spectralLatticeCovarianceAsym_eq]
  simp_rw [massOperatorAsym_eigenCoeff_eq_eigenvalues_mul_eigenCoeff Nt Ns a mass h]
  refine Eq.trans ?_ (massEigenbasisAsym_sum_mul_sum_eq_site_inner Nt Ns a mass f h)
  refine Finset.sum_congr rfl fun k _ => ?_
  have hne : massEigenvaluesAsym Nt Ns a mass k ≠ 0 :=
    ne_of_gt (massOperatorMatrixAsym_eigenvalues_pos Nt Ns a mass ha hmass k)
  field_simp [hne]

theorem asymShift_sum_mul_eq (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (v : AsymLatticeSites Nt Ns) (f h : AsymLatticeField Nt Ns) :
    ∑ x : AsymLatticeSites Nt Ns, asymShift Nt Ns v f x * asymShift Nt Ns v h x =
      ∑ x : AsymLatticeSites Nt Ns, f x * h x := by
  symm
  exact Fintype.sum_equiv (Equiv.addRight v)
    (fun x : AsymLatticeSites Nt Ns => f x * h x)
    (fun x : AsymLatticeSites Nt Ns =>
      asymShift Nt Ns v f x * asymShift Nt Ns v h x)
    (fun x => by simp [asymShift, sub_eq_add_neg, add_assoc, add_comm])

theorem asymShift_delta (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (v x : AsymLatticeSites Nt Ns) :
    asymShift Nt Ns v (asymLatticeDelta Nt Ns x) = asymLatticeDelta Nt Ns (x + v) := by
  funext y
  change (if y - v = x then 1 else 0) = (if y = x + v then 1 else 0)
  by_cases h : y = x + v
  · have h' : y - v = x := (sub_eq_iff_eq_add.mpr h)
    simp [h]
  · have h' : y - v ≠ x := by
      intro hy
      exact h (sub_eq_iff_eq_add.mp hy)
    simp [h, h']

theorem covariance_spectralLatticeCovarianceAsym_translation_invariant
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (v : AsymLatticeSites Nt Ns) (f g : AsymLatticeField Nt Ns) :
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
      (asymShift Nt Ns v f) (asymShift Nt Ns v g) =
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) f g := by
  obtain ⟨h, rfl⟩ := massOperatorAsym_surjective Nt Ns a mass ha hmass g
  rw [← massOperatorAsym_translation_commute Nt Ns a mass v h]
  calc
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
        (asymShift Nt Ns v f) (massOperatorAsym Nt Ns a mass (asymShift Nt Ns v h))
      = ∑ x : AsymLatticeSites Nt Ns, asymShift Nt Ns v f x * asymShift Nt Ns v h x :=
          spectralCovAsym_massOperator_eq Nt Ns a mass ha hmass _ _
    _ = ∑ x : AsymLatticeSites Nt Ns, f x * h x :=
          asymShift_sum_mul_eq Nt Ns v f h
    _ = covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) f
        (massOperatorAsym Nt Ns a mass h) :=
          (spectralCovAsym_massOperator_eq Nt Ns a mass ha hmass f h).symm

theorem delta_massEigenvectorCoeff_asym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (k x : AsymLatticeSites Nt Ns) :
    (∑ y : AsymLatticeSites Nt Ns,
      (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) y *
        asymLatticeDelta Nt Ns x y) =
      (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x := by
  simp [asymLatticeDelta]

theorem massEigenvectorBasisAsym_norm_sq_eq_one (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (k : AsymLatticeSites Nt Ns) :
    ∑ x : AsymLatticeSites Nt Ns,
      (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x ^ 2 = 1 := by
  have h_norm1 := (massEigenvectorBasisAsym Nt Ns a mass).orthonormal.1 k
  simp only [EuclideanSpace.norm_eq] at h_norm1
  have hsq :
      ∑ x : AsymLatticeSites Nt Ns,
          (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x ^ 2 =
        ∑ x : AsymLatticeSites Nt Ns,
          ‖(massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x‖ ^ 2 := by
    congr 1
    ext x
    rw [Real.norm_eq_abs, sq_abs]
  rw [hsq]
  have hnonneg :
      0 ≤ ∑ x : AsymLatticeSites Nt Ns,
        ‖(massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [Real.sq_sqrt hnonneg]

theorem spectralVarianceAsym_delta_eq (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (x y : AsymLatticeSites Nt Ns) :
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
      (asymLatticeDelta Nt Ns x) (asymLatticeDelta Nt Ns x) =
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
      (asymLatticeDelta Nt Ns y) (asymLatticeDelta Nt Ns y) := by
  let v : AsymLatticeSites Nt Ns := x - y
  have h :=
    covariance_spectralLatticeCovarianceAsym_translation_invariant
      Nt Ns a mass ha hmass v
      (asymLatticeDelta Nt Ns y) (asymLatticeDelta Nt Ns y)
  have hyx : y + v = x := by
    simp [v, sub_eq_add_neg, add_left_comm]
  simpa [asymShift_delta, v, hyx] using h

theorem spectralVarianceAsym_sum_eq_massEigenvalue_trace
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    ∑ x : AsymLatticeSites Nt Ns,
      covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
        (asymLatticeDelta Nt Ns x) (asymLatticeDelta Nt Ns x) =
      ∑ k : AsymLatticeSites Nt Ns, (massEigenvaluesAsym Nt Ns a mass k)⁻¹ := by
  calc
    ∑ x : AsymLatticeSites Nt Ns,
        covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
          (asymLatticeDelta Nt Ns x) (asymLatticeDelta Nt Ns x)
      = ∑ x : AsymLatticeSites Nt Ns,
          ∑ k : AsymLatticeSites Nt Ns,
            (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
              (∑ y : AsymLatticeSites Nt Ns,
                (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) y *
                  asymLatticeDelta Nt Ns x y) *
              (∑ y : AsymLatticeSites Nt Ns,
                (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) y *
                  asymLatticeDelta Nt Ns x y) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            exact covariance_spectralLatticeCovarianceAsym_eq Nt Ns a mass ha hmass
              (asymLatticeDelta Nt Ns x) (asymLatticeDelta Nt Ns x)
    _ = ∑ x : AsymLatticeSites Nt Ns,
          ∑ k : AsymLatticeSites Nt Ns,
            (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
              ((massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x) ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [delta_massEigenvectorCoeff_asym Nt Ns a mass k x]
            ring
    _ = ∑ k : AsymLatticeSites Nt Ns,
          (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
            ∑ x : AsymLatticeSites Nt Ns,
              ((massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x) ^ 2 := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [← Finset.mul_sum]
    _ = ∑ k : AsymLatticeSites Nt Ns, (massEigenvaluesAsym Nt Ns a mass k)⁻¹ := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            rw [massEigenvectorBasisAsym_norm_sq_eq_one Nt Ns a mass k]
            simp

theorem spectralVarianceAsym_eq_massEigenvalue_average
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (x : AsymLatticeSites Nt Ns) :
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
      (asymLatticeDelta Nt Ns x) (asymLatticeDelta Nt Ns x) =
      (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
        ∑ k : AsymLatticeSites Nt Ns, (massEigenvaluesAsym Nt Ns a mass k)⁻¹ := by
  have hconst : ∀ y : AsymLatticeSites Nt Ns,
      covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
        (asymLatticeDelta Nt Ns y) (asymLatticeDelta Nt Ns y) =
      covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
        (asymLatticeDelta Nt Ns x) (asymLatticeDelta Nt Ns x) := by
    intro y
    exact spectralVarianceAsym_delta_eq Nt Ns a mass ha hmass y x
  have hsum := spectralVarianceAsym_sum_eq_massEigenvalue_trace Nt Ns a mass ha hmass
  have hcard_pos : (0 : ℝ) < Fintype.card (AsymLatticeSites Nt Ns) := by
    exact_mod_cast Fintype.card_pos
  have hconst_sum :
      ∑ y : AsymLatticeSites Nt Ns,
        covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
          (asymLatticeDelta Nt Ns y) (asymLatticeDelta Nt Ns y) =
      (Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
        covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
          (asymLatticeDelta Nt Ns x) (asymLatticeDelta Nt Ns x) := by
    calc
      ∑ y : AsymLatticeSites Nt Ns,
          covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
            (asymLatticeDelta Nt Ns y) (asymLatticeDelta Nt Ns y)
        = ∑ _y : AsymLatticeSites Nt Ns,
            covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
              (asymLatticeDelta Nt Ns x) (asymLatticeDelta Nt Ns x) := by
                refine Finset.sum_congr rfl ?_
                intro y hy
                exact hconst y
      _ = (Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
            covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
              (asymLatticeDelta Nt Ns x) (asymLatticeDelta Nt Ns x) := by
                simp
  calc
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
        (asymLatticeDelta Nt Ns x) (asymLatticeDelta Nt Ns x)
      = (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
          ((Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
            covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
              (asymLatticeDelta Nt Ns x) (asymLatticeDelta Nt Ns x)) := by
            field_simp [ne_of_gt hcard_pos]
    _ = (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
          ∑ k : AsymLatticeSites Nt Ns, (massEigenvaluesAsym Nt Ns a mass k)⁻¹ := by
            rw [← hconst_sum, hsum]

theorem spectralVarianceAsym_inner_eq_massEigenvalue_average
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (x : AsymLatticeSites Nt Ns) :
    @inner ℝ ell2' _
      (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass (asymLatticeDelta Nt Ns x))
      (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass (asymLatticeDelta Nt Ns x)) =
      (1 / Fintype.card (AsymLatticeSites Nt Ns) : ℝ) *
        ∑ k : AsymLatticeSites Nt Ns, (massEigenvaluesAsym Nt Ns a mass k)⁻¹ := by
  simpa [GaussianField.covariance] using
    spectralVarianceAsym_eq_massEigenvalue_average Nt Ns a mass ha hmass x

theorem latticeCovarianceAsymGJ_inner_eq_inv_a_sq_spectral
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymLatticeField Nt Ns) :
    @inner ℝ ell2' _
      (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)
      (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f) =
      (a ^ 2 : ℝ)⁻¹ *
        @inner ℝ ell2' _
          (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass f)
          (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass f) := by
  have hsqrt : Real.sqrt (a ^ 2) = a := Real.sqrt_sq ha.le
  unfold latticeCovarianceAsymGJ
  change @inner ℝ ell2' _
      ((Real.sqrt (a ^ 2))⁻¹ • spectralLatticeCovarianceAsym Nt Ns a mass ha hmass f)
      ((Real.sqrt (a ^ 2))⁻¹ • spectralLatticeCovarianceAsym Nt Ns a mass ha hmass f) =
      (a ^ 2 : ℝ)⁻¹ *
        @inner ℝ ell2' _
          (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass f)
          (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass f)
  rw [real_inner_smul_left, real_inner_smul_right]
  field_simp [hsqrt, ne_of_gt ha]
  simp [hsqrt]

end Pphi2
