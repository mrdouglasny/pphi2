/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymGappedTransfer

/-!
# Operator-norm spectral gap for the asym cylinder transfer operator (Layer B2, Part A)

`asymTransferNormalized_gap`: the transfer operator normalised to ground
eigenvalue `1` is a strict contraction (factor `γ < 1`) on the orthogonal
complement of the Perron-Frobenius ground vector. The proof restricts the
operator to `(ℝ ∙ ground)ᗮ`, uses that a compact self-adjoint operator
attains its norm as `|eigenvalue|`, and closes `‖T|_⊥‖ < λ₀` via the
ground-state dominance `asymTransferGroundExcitedData.htop`.

`asymGappedTransfer'` packages it as a `ReflectionPositivity.GappedTransfer`
with no hypotheses, so `GappedTransfer.susceptibility_le` (the Lt-uniform
two-point-sum bound) applies off the shelf.
-/

open GaussianField Real MeasureTheory ReflectionPositivity

namespace Pphi2

/-- The normalized asym transfer operator is a strict contraction on the
orthogonal complement of the Perron-Frobenius ground vector. -/
theorem asymTransferNormalized_gap
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    ∃ γ : ℝ, 0 ≤ γ ∧ γ < 1 ∧ ∀ v : L2SpatialField Ns,
      (@inner ℝ _ _ (asymGroundVector Nt Ns P a mass ha hmass) v = 0) →
      ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ ≤ γ * ‖v‖ := by
  classical
  let d := asymTransferGroundExcitedData Nt Ns P a mass ha hmass
  let A : L2SpatialField Ns →L[ℝ] L2SpatialField Ns :=
    asymTransferOperatorCLM Nt Ns P a mass ha hmass
  let lam0 : ℝ := asymTransferGroundEigenvalue Nt Ns P a mass ha hmass
  let g : L2SpatialField Ns := asymGroundVector Nt Ns P a mass ha hmass
  have hlam0_pos : 0 < lam0 := asymTransferGroundEigenvalue_pos Nt Ns P a mass ha hmass
  have hg_eigen :
      (A : L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) g = lam0 • g := by
    simpa [A, g, lam0, asymGroundVector, asymTransferGroundEigenvalue, d]
      using d.h_eigen d.i₀
  have hA_sa : IsSelfAdjoint A :=
    asymTransferOperator_isSelfAdjoint Nt Ns P a mass ha hmass
  have hA_sym : (A : L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA_sa
  let W : Submodule ℝ (L2SpatialField Ns) := (ℝ ∙ g)ᗮ
  have hW_inv :
      ∀ w ∈ W, (A : L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) w ∈ W := by
    intro w hw
    have hw_inner : @inner ℝ (L2SpatialField Ns) _ g w = 0 := by
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (by simpa [W] using hw)
    change (A : L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) w ∈ (ℝ ∙ g)ᗮ
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    calc
      @inner ℝ (L2SpatialField Ns) _ g
          ((A : L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) w)
          = @inner ℝ (L2SpatialField Ns) _
              ((A : L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) g) w :=
            (hA_sym g w).symm
      _ = @inner ℝ (L2SpatialField Ns) _ (lam0 • g) w := by rw [hg_eigen]
      _ = 0 := by rw [real_inner_smul_left, hw_inner, mul_zero]
  let A_W : W →L[ℝ] W :=
    (A.comp W.subtypeL).codRestrict W (fun w => hW_inv w.1 w.2)
  have instCS_W : CompleteSpace ↥W :=
    Submodule.instOrthogonalCompleteSpace (ℝ ∙ g)
  have hA_W_sym : (A_W : ↥W →ₗ[ℝ] ↥W).IsSymmetric := by
    intro x y
    rcases x with ⟨x, _⟩
    rcases y with ⟨y, _⟩
    simp only [Submodule.coe_inner]
    change @inner ℝ (L2SpatialField Ns) _ (A x) y =
      @inner ℝ (L2SpatialField Ns) _ x (A y)
    exact hA_sym x y
  have hA_W_sa : @IsSelfAdjoint (↥W →L[ℝ] ↥W)
      (@ContinuousLinearMap.instStarId ℝ ↥W _ _ _ instCS_W) A_W :=
    (@ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric ℝ ↥W _ _ _ instCS_W).mpr
      hA_W_sym
  have hA_compact : IsCompactOperator A :=
    asymTransferOperator_isCompact Nt Ns P a mass ha hmass
  have hA_W_compact : IsCompactOperator A_W :=
    (hA_compact.comp_clm W.subtypeL).codRestrict _ (Submodule.isClosed_orthogonal _)
  have hAW_lt : ‖A_W‖ < lam0 := by
    by_cases hzero : A_W = 0
    · rw [hzero]
      calc
        ‖(0 : ↥W →L[ℝ] ↥W)‖ = (0 : ℝ) := ContinuousLinearMap.opNorm_zero
        _ < lam0 := hlam0_pos
    · obtain ⟨v, hv_ne⟩ : ∃ v : ↥W, A_W v ≠ 0 := by
        by_contra h
        push Not at h
        exact hzero (ContinuousLinearMap.ext h)
      haveI : Nontrivial ↥W := by
        refine ⟨⟨v, 0, ?_⟩⟩
        intro hv
        exact hv_ne (by rw [hv]; simp)
      obtain ⟨μ, hμ_eig, hμ_norm⟩ :=
        GaussianField.compact_selfAdjoint_hasEigenvector (T := A_W)
          hA_W_sa hA_W_compact hzero
      obtain ⟨eW, heW_mem, heW_ne⟩ :=
        (Submodule.ne_bot_iff
          (Module.End.eigenspace (A_W : ↥W →ₗ[ℝ] ↥W) μ)).mp hμ_eig
      have heW_eig : (A_W : ↥W →ₗ[ℝ] ↥W) eW = μ • eW :=
        Module.End.mem_eigenspace_iff.mp heW_mem
      have heW_eig_E :
          (A : L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns)
              (eW : L2SpatialField Ns) = μ • (eW : L2SpatialField Ns) := by
        have h := congr_arg Subtype.val heW_eig
        simpa [A_W] using h
      have hcoeff_exists :
          ∃ i, @inner ℝ (L2SpatialField Ns) _ (d.b i) (eW : L2SpatialField Ns) ≠ 0 := by
        by_contra h
        push Not at h
        have hre : d.b.repr (eW : L2SpatialField Ns) = 0 := by
          ext i
          rw [HilbertBasis.repr_apply_apply, h i]
          rfl
        have he_zero_E : (eW : L2SpatialField Ns) = 0 := by
          exact d.b.repr.injective (by simp [hre])
        exact heW_ne (Subtype.ext he_zero_E)
      obtain ⟨i, hcoeff_ne⟩ := hcoeff_exists
      have h_eigen_i :
          (A : L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (d.b i) =
            d.eigenval i • d.b i := by
        simpa [A] using d.h_eigen i
      have h_eval_eq : d.eigenval i = μ := by
        have hsym := hA_sym (d.b i) (eW : L2SpatialField Ns)
        rw [h_eigen_i, heW_eig_E, real_inner_smul_left, real_inner_smul_right] at hsym
        exact mul_right_cancel₀ hcoeff_ne hsym
      have heW_orth : @inner ℝ (L2SpatialField Ns) _ g (eW : L2SpatialField Ns) = 0 := by
        exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (by simpa [W] using eW.2)
      have hi_ne : i ≠ d.i₀ := by
        intro hi
        apply hcoeff_ne
        simpa [hi, g, asymGroundVector, d] using heW_orth
      have htop_i : |d.eigenval i| < d.eigenval d.i₀ := d.htop i hi_ne
      have hμ_lt : |μ| < lam0 := by
        simpa [h_eval_eq, lam0, asymTransferGroundEigenvalue, d] using htop_i
      exact hμ_norm ▸ hμ_lt
  refine ⟨‖A_W‖ / lam0, ?_, ?_, ?_⟩
  · exact div_nonneg A_W.opNorm_nonneg hlam0_pos.le
  · rw [div_lt_iff₀ hlam0_pos]
    simpa using hAW_lt
  · intro v hv
    have hvW : v ∈ W := by
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (by simpa [g] using hv)
    have hAv_le : ‖A v‖ ≤ ‖A_W‖ * ‖v‖ := by
      have h := A_W.le_opNorm ⟨v, hvW⟩
      simpa [A_W] using h
    calc
      ‖asymTransferNormalized Nt Ns P a mass ha hmass v‖ = lam0⁻¹ * ‖A v‖ := by
        change ‖((lam0⁻¹ • A) : L2SpatialField Ns →L[ℝ] L2SpatialField Ns) v‖ =
          lam0⁻¹ * ‖A v‖
        rw [ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hlam0_pos)]
      _ ≤ lam0⁻¹ * (‖A_W‖ * ‖v‖) := by
        exact mul_le_mul_of_nonneg_left hAv_le (inv_nonneg.mpr hlam0_pos.le)
      _ = (‖A_W‖ / lam0) * ‖v‖ := by
        rw [div_eq_mul_inv]
        ring

/-- The asym transfer operator packaged as a gapped transfer, with the
operator-norm gap supplied by `asymTransferNormalized_gap`. -/
noncomputable def asymGappedTransfer'
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    ReflectionPositivity.GappedTransfer (L2SpatialField Ns) :=
  let hgap := asymTransferNormalized_gap Nt Ns P a mass ha hmass
  let gamma := Exists.choose hgap
  let hgamma := Exists.choose_spec hgap
  asymGappedTransfer Nt Ns P a mass ha hmass gamma hgamma.1 hgamma.2.1 hgamma.2.2

end Pphi2
