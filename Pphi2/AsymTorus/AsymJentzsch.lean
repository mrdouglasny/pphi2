/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asym cylinder transfer operator: Jentzsch / Perron-Frobenius (Layer B1, Phase 2)

Asym analogues of the square Jentzsch / Perron-Frobenius theorems
(`Pphi2/TransferMatrix/Jentzsch.lean`), specialized to the asym cylinder
transfer operator defined in `Pphi2/AsymTorus/AsymL2Operator.lean`.

The generic `jentzsch_theorem` (proved over any Hilbert space in
`JentzschProof.lean`) is reused directly; we supply only the
asym-specific hypotheses (compact + self-adjoint, both from Phase 1;
positivity-improving + strictly positive definite, proved here).

`l2SpatialField_hilbertBasis_nontrivial` and
`convolution_gaussian_strictly_positive_definite` are about the same
underlying Hilbert space `L2SpatialField Ns` and the same Gaussian
kernel as the square — they are **reused as-is**, no port needed.

## Main declarations

* `asymTransferOperator_positivityImproving`
* `asymTransferOperator_strictly_positive_definite`
* `asymTransferOperator_spectral`
* `asymTransferOperator_inner_nonneg`
* `asymTransferOperator_eigenvalues_pos`
* `asymTransferOperator_ground_simple`
* `asymTransferOperator_ground_simple_spectral`

## References

* `Pphi2/TransferMatrix/Jentzsch.lean` — the square analogue. Proofs
  mirror line-by-line.
* `Pphi2/TransferMatrix/JentzschProof.lean` — generic Jentzsch
  theorem (reused).
-/

import Pphi2.AsymTorus.AsymL2Operator
import Pphi2.TransferMatrix.Jentzsch
import GaussianField.SpectralTheorem

noncomputable section

open MeasureTheory

namespace Pphi2

variable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]

/-! ## Positivity improving -/

/-- The asym transfer operator is positivity-improving.

Same proof structure as the square's `transferOperator_positivityImproving`:
factor as `M_w ∘ Conv_G ∘ M_w` and chain (1) `g = M_w f` is ae nonneg + nonzero;
(2) `h = Conv_G g` is ae strictly positive (since `G > 0` everywhere and `g ≥ 0`
ae with positive support); (3) `T f = M_w h` is ae strictly positive. The only
difference from the square is the Wick constant inside `w`. -/
theorem asymTransferOperator_positivityImproving (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    IsPositivityImproving (asymTransferOperatorCLM Nt Ns P a mass ha hmass) := by
  intro f hf_nonneg hf_nonzero
  set w := asymTransferWeight Nt Ns P a mass
  set G := transferGaussian Ns
  set hw_meas := asymTransferWeight_measurable Nt Ns P a mass
  set C := (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose
  set hC := (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose_spec.1
  set hw_bound := (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose_spec.2
  set hG := transferGaussian_memLp Ns
  have hw_pos : ∀ ψ, 0 < w ψ := asymTransferWeight_pos Nt Ns P a mass
  have hG_pos : ∀ ψ, 0 < G ψ := transferGaussian_pos Ns
  -- Step 1: g := M_w f satisfies g ≥ 0 ae, g ≢ 0 ae
  set g := mulCLM w hw_meas C hC hw_bound f with hg_def
  have hg_spec := mulCLM_spec w hw_meas C hC hw_bound f
  have hg_nonneg : ∀ᵐ x ∂(volume : Measure (SpatialField Ns)),
      0 ≤ (g : SpatialField Ns → ℝ) x := by
    filter_upwards [hg_spec, hf_nonneg] with x hx hfx
    rw [hx]; exact mul_nonneg (le_of_lt (hw_pos x)) hfx
  have hg_nonzero : ¬ (g : SpatialField Ns → ℝ) =ᵐ[volume] 0 := by
    intro h_absurd
    apply hf_nonzero
    have h_wf_zero :
        (fun x => w x * (f : SpatialField Ns → ℝ) x) =ᵐ[volume] 0 := by
      filter_upwards [h_absurd, hg_spec] with x hx1 hx2
      rwa [← hx2]
    filter_upwards [h_wf_zero] with x hx
    exact (mul_eq_zero.mp hx).resolve_left (ne_of_gt (hw_pos x))
  -- Step 2: h := Conv_G g satisfies h > 0 ae
  set h := convCLM G hG g with hh_def
  have hh_spec := convCLM_spec G hG g
  have hh_pos : ∀ᵐ x ∂(volume : Measure (SpatialField Ns)),
      0 < (h : SpatialField Ns → ℝ) x := by
    filter_upwards [hh_spec] with x hx
    rw [hx]
    have h_mp : MeasurePreserving (fun t : SpatialField Ns => x - t) volume volume :=
      (measurePreserving_add_left volume x).comp (Measure.measurePreserving_neg volume)
    have h_integrand_nonneg : ∀ᵐ t ∂(volume : Measure (SpatialField Ns)),
        0 ≤ G t * (g : SpatialField Ns → ℝ) (x - t) := by
      have h_trans : ∀ᵐ t ∂volume, 0 ≤ (g : SpatialField Ns → ℝ) (x - t) := by
        rw [ae_iff] at hg_nonneg ⊢
        exact le_antisymm (hg_nonneg ▸ h_mp.measure_preimage_le _) (zero_le _)
      filter_upwards [h_trans] with t ht
      exact mul_nonneg (le_of_lt (hG_pos t)) ht
    have h_integrand_int :
        Integrable (fun t => G t * (g : SpatialField Ns → ℝ) (x - t))
          (volume : Measure (SpatialField Ns)) := by
      have hG2 : MemLp G 2 volume := transferGaussian_memLp_two Ns
      have hgx : MemLp ((↑↑g : SpatialField Ns → ℝ) ∘ (x - ·)) 2 volume :=
        (Lp.memLp g).comp_measurePreserving h_mp
      set G' := hG2.toLp G
      set gx' := hgx.toLp _
      refine (L2.integrable_inner (𝕜 := ℝ) G' gx').congr ?_
      filter_upwards [hG2.coeFn_toLp, hgx.coeFn_toLp] with t hGt hgxt
      simp only [inner, Inner.inner, starRingEnd_apply, star_trivial, RCLike.re_to_real]
      simp only [Function.comp_apply] at hgxt
      rw [hGt, hgxt, mul_comm]
    have h_support_pos : 0 < (volume : Measure (SpatialField Ns))
        (Function.support (fun t => G t * (g : SpatialField Ns → ℝ) (x - t))) := by
      have h_subset : (fun t => x - t) ⁻¹'
            (Function.support (g : SpatialField Ns → ℝ)) ⊆
          Function.support (fun t => G t * (g : SpatialField Ns → ℝ) (x - t)) := by
        intro t ht
        simp only [Function.mem_support, Set.mem_preimage] at ht ⊢
        exact mul_ne_zero (ne_of_gt (hG_pos t)) ht
      have h_g_support : 0 < volume (Function.support (g : SpatialField Ns → ℝ)) := by
        rw [pos_iff_ne_zero]
        intro h_eq
        exact hg_nonzero (ae_iff.mpr h_eq)
      calc volume (Function.support fun t => G t * (g : SpatialField Ns → ℝ) (x - t))
          ≥ volume ((fun t => x - t) ⁻¹'
              Function.support (g : SpatialField Ns → ℝ)) :=
            measure_mono h_subset
        _ = volume (Function.support (g : SpatialField Ns → ℝ)) :=
            h_mp.measure_preimage
              (measurableSet_support
                (Lp.stronglyMeasurable g).measurable).nullMeasurableSet
        _ > 0 := h_g_support
    rw [show realConv volume G (⇑g) x =
        ∫ t, G t * (g : SpatialField Ns → ℝ) (x - t) ∂volume from by
      simp [realConv, convolution, ContinuousLinearMap.lsmul_apply]]
    exact (integral_pos_iff_support_of_nonneg_ae h_integrand_nonneg h_integrand_int).mpr
      h_support_pos
  -- Step 3: T f = M_w h, M_w maps ae positive to ae positive
  have hTf_coercion :
      (asymTransferOperatorCLM Nt Ns P a mass ha hmass f : SpatialField Ns → ℝ) =
        (mulCLM w hw_meas C hC hw_bound h : SpatialField Ns → ℝ) :=
    congr_arg (fun e : L2SpatialField Ns => (e : SpatialField Ns → ℝ))
      (show asymTransferOperatorCLM Nt Ns P a mass ha hmass f =
        mulCLM w hw_meas C hC hw_bound h from rfl)
  have hresult_spec := mulCLM_spec w hw_meas C hC hw_bound h
  simp only [hTf_coercion]
  filter_upwards [hresult_spec, hh_pos] with x hx hhx
  rw [hx]; exact mul_pos (hw_pos x) hhx

/-! ## Strictly positive definite -/

/-- The asym transfer operator is strictly positive definite: ⟨f, Tf⟩ > 0 for
all nonzero `f`. Same proof structure as the square; reuses the Gaussian
convolution strict PD result `convolution_gaussian_strictly_positive_definite`
verbatim (kernel is asym-agnostic). -/
theorem asymTransferOperator_strictly_positive_definite
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∀ (f : L2SpatialField Ns), f ≠ 0 →
      0 < @inner ℝ _ _ f (asymTransferOperatorCLM Nt Ns P a mass ha hmass f) := by
  intro f hf
  set w := asymTransferWeight Nt Ns P a mass
  set G := transferGaussian Ns
  set hw_meas := asymTransferWeight_measurable Nt Ns P a mass
  set C := (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose
  set hC := (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose_spec.1
  set hw_bound := (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose_spec.2
  set hG := transferGaussian_memLp Ns
  set A := mulCLM w hw_meas C hC hw_bound
  set B := convCLM G hG
  have hA_sa : IsSelfAdjoint A := mulCLM_isSelfAdjoint w hw_meas C hC hw_bound
  have hT_eq : asymTransferOperatorCLM Nt Ns P a mass ha hmass f = A (B (A f)) := rfl
  rw [hT_eq, show @inner ℝ _ _ f (A (B (A f))) = @inner ℝ _ _ (A f) (B (A f))
    from (hA_sa.isSymmetric f (B (A f))).symm]
  have hw_pos : ∀ ψ, 0 < w ψ := asymTransferWeight_pos Nt Ns P a mass
  have hAf_ne : A f ≠ 0 := by
    intro h_absurd
    apply hf
    have hAf_spec := mulCLM_spec w hw_meas C hC hw_bound f
    have hAf_zero : (A f : SpatialField Ns → ℝ) =ᵐ[volume] 0 := by
      rw [h_absurd]; exact Lp.coeFn_zero _ _ _
    have hf_ae_zero : (f : SpatialField Ns → ℝ) =ᵐ[volume] 0 := by
      filter_upwards [hAf_spec, hAf_zero] with x hx1 hx2
      have : w x * (f : SpatialField Ns → ℝ) x = 0 := by rwa [← hx1]
      exact (mul_eq_zero.mp this).resolve_left (ne_of_gt (hw_pos x))
    exact Lp.eq_zero_iff_ae_eq_zero.mpr hf_ae_zero
  exact convolution_gaussian_strictly_positive_definite Ns (A f) hAf_ne

/-! ## Spectral decomposition and Perron-Frobenius derivatives -/

/-- The asym transfer operator admits a spectral decomposition. -/
theorem asymTransferOperator_spectral (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ (L2SpatialField Ns)) (eigenval : ι → ℝ),
      (∀ i, (asymTransferOperatorCLM Nt Ns P a mass ha hmass :
        L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) = eigenval i • b i) ∧
      (∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i)
        (asymTransferOperatorCLM Nt Ns P a mass ha hmass x)) :=
  GaussianField.compact_selfAdjoint_spectral _
    (asymTransferOperator_isSelfAdjoint Nt Ns P a mass ha hmass)
    (asymTransferOperator_isCompact Nt Ns P a mass ha hmass)

/-- ⟨f, Tf⟩ ≥ 0 for all `f`. -/
theorem asymTransferOperator_inner_nonneg (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∀ (f : L2SpatialField Ns),
      0 ≤ @inner ℝ _ _ f (asymTransferOperatorCLM Nt Ns P a mass ha hmass f) := by
  intro f
  by_cases hf : f = 0
  · rw [hf, map_zero, inner_self_eq_zero.mpr rfl]
  · exact le_of_lt
      (asymTransferOperator_strictly_positive_definite Nt Ns P a mass ha hmass f hf)

/-- All eigenvalues of the asym transfer operator are strictly positive. -/
theorem asymTransferOperator_eigenvalues_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    {ι : Type} (b : HilbertBasis ι ℝ (L2SpatialField Ns)) (eigenval : ι → ℝ)
    (h_eigen : ∀ i, (asymTransferOperatorCLM Nt Ns P a mass ha hmass :
        L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) = eigenval i • b i)
    (i : ι) : 0 < eigenval i := by
  have hbi_ne : (b i : L2SpatialField Ns) ≠ 0 := by
    intro h
    have := b.orthonormal.norm_eq_one i
    rw [h, norm_zero] at this
    exact one_ne_zero this.symm
  have hpd :=
    asymTransferOperator_strictly_positive_definite Nt Ns P a mass ha hmass (b i) hbi_ne
  have hconv : (asymTransferOperatorCLM Nt Ns P a mass ha hmass :
      L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) =
        asymTransferOperatorCLM Nt Ns P a mass ha hmass (b i) := rfl
  rw [← hconv, h_eigen i] at hpd
  rw [@inner_smul_right ℝ, @real_inner_self_eq_norm_sq] at hpd
  have hnorm : ‖b i‖ = 1 := b.orthonormal.norm_eq_one i
  rw [hnorm, one_pow, mul_one] at hpd
  exact hpd

/-- Ground-state simplicity for the asym transfer operator. -/
theorem asymTransferOperator_ground_simple (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∀ {ι : Type} (b : HilbertBasis ι ℝ (L2SpatialField Ns)) (eigenval : ι → ℝ)
      (_h_eigen : ∀ i, (asymTransferOperatorCLM Nt Ns P a mass ha hmass :
          L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) = eigenval i • b i)
      (_h_sum : ∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i)
          (asymTransferOperatorCLM Nt Ns P a mass ha hmass x)),
      ∃ i₀ i₁ : ι, i₁ ≠ i₀ ∧ eigenval i₁ < eigenval i₀ := by
  intro ι b eigenval h_eigen h_sum
  -- Reuse the square's nontriviality lemma — same underlying Hilbert space.
  have h_nt := l2SpatialField_hilbertBasis_nontrivial Ns b
  obtain ⟨i₀, hpos, _hsimple, hgap⟩ := jentzsch_theorem
    (asymTransferOperatorCLM Nt Ns P a mass ha hmass)
    (asymTransferOperator_isCompact Nt Ns P a mass ha hmass)
    (asymTransferOperator_isSelfAdjoint Nt Ns P a mass ha hmass)
    (asymTransferOperator_positivityImproving Nt Ns P a mass ha hmass)
    b eigenval h_eigen h_sum h_nt
  obtain ⟨j, k, hjk⟩ := h_nt
  have h_exists_ne : ∃ i₁, i₁ ≠ i₀ := by
    by_cases hj : j = i₀
    · exact ⟨k, fun hk => hjk (hj.trans hk.symm)⟩
    · exact ⟨j, hj⟩
  obtain ⟨i₁, hi₁_ne⟩ := h_exists_ne
  have hall_pos : ∀ i, 0 < eigenval i :=
    fun i => asymTransferOperator_eigenvalues_pos Nt Ns P a mass ha hmass b eigenval h_eigen i
  have hlt : eigenval i₁ < eigenval i₀ := by
    have := hgap i₁ hi₁_ne
    rwa [abs_of_pos (hall_pos i₁)] at this
  exact ⟨i₀, i₁, hi₁_ne, hlt⟩

/-- Spectral data with distinguished ground and first excited levels for the
asym transfer operator. -/
theorem asymTransferOperator_ground_simple_spectral
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ (L2SpatialField Ns)) (eigenval : ι → ℝ)
      (i₀ i₁ : ι),
      (∀ i, (asymTransferOperatorCLM Nt Ns P a mass ha hmass :
          L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) = eigenval i • b i) ∧
      (∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i)
          (asymTransferOperatorCLM Nt Ns P a mass ha hmass x)) ∧
      i₁ ≠ i₀ ∧ eigenval i₁ < eigenval i₀ := by
  rcases asymTransferOperator_spectral Nt Ns P a mass ha hmass with
    ⟨ι, b, eigenval, h_eigen, h_sum⟩
  rcases asymTransferOperator_ground_simple Nt Ns P a mass ha hmass b eigenval h_eigen h_sum
    with ⟨i₀, i₁, hi_ne, hlt⟩
  exact ⟨ι, b, eigenval, i₀, i₁, h_eigen, h_sum, hi_ne, hlt⟩

end Pphi2

end
