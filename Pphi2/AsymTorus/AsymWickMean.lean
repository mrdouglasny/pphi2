/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wick-ordering mean and partition-function lower bound (heterogeneous lattice)

For the P(φ)₂ interacting measure on the isotropic heterogeneous lattice `Z_Nt × Z_Ns`, the
Wick-ordered interaction has nonpositive mean under the free field, so the partition function
`Z_a = ∫ exp(-V_a) dμ_{GFF}` satisfies `Z_a ≥ 1` (Jensen). This is the heterogeneous analogue of
the square chain in `ContinuumLimit/Hypercontractivity.lean`.

The genuine analytic input — that the site variance `Var[ω(δ_x)]` of the heterogeneous GFF equals
`wickConstantAsym` at every site `x` (translation invariance of the circulant covariance's
diagonal) — is isolated as the vetted axiom `wickConstantAsym_eq_variance`. Everything else is
derived from it via the *generic* Gaussian-field API (`pairing_is_gaussian`,
`gaussian_hermite_zero_mean`).

## Main results

- `wickConstantAsym_eq_variance` — **axiom**: site variance equals the Wick constant.
- `wickMonomialAsym_latticeGaussian` — Wick monomials of order `n ≥ 1` have zero GFF mean.
- `interactionFunctionalAsym_mean_nonpos` — `∫ V_a dμ_{GFF} ≤ 0`.
- `partitionFunctionAsym_ge_one` — `Z_a ≥ 1`.

## Reference

Glimm–Jaffe, *Quantum Physics*, §I.3, §9; Simon, *P(φ)₂* (1974), §I.
-/

import Pphi2.AsymTorus.AsymLatticeMeasure
import Pphi2.GeneralResults.GaussianHermiteMean
import GaussianField.Properties
import Mathlib.Analysis.Convex.Integral

noncomputable section

open MeasureTheory ProbabilityTheory GaussianField

namespace Pphi2

/-- **Site variance of the heterogeneous lattice GFF equals the Wick constant** (textbook axiom).

For the P(φ)₂ Gaussian free field on the isotropic heterogeneous lattice `Z_Nt × Z_Ns`, the
variance of the site evaluation `ω ↦ ω(δ_x)` is the same at every site `x` and equals
`wickConstantAsym`:

  `wickConstantAsym Nt Ns a mass = ⟪T_GJ δ_x, T_GJ δ_x⟫`,    where `T_GJ = latticeCovarianceAsymGJ`.

Equivalently the diagonal `C(δ_x, δ_x)` of the GJ covariance is the spatial average
`(a²)⁻¹·(1/|Λ|)·Σ_k λ_k⁻¹` of the inverse mass-operator eigenvalues, independent of `x`.

The spatial **average** of `⟪T_GJ δ_x, T_GJ δ_x⟫` over `x` already equals `wickConstantAsym` by
orthonormality of the eigenbasis (`Σ_x e_k(x)² = ‖e_k‖² = 1`); the only content is the
site-**independence** of the diagonal, which holds because `massOperatorAsym = −Δ_a + m²` is
circulant on the finite abelian group `Z_Nt × Z_Ns`, so it commutes with the group-shift
representation, hence so does its inverse square root, hence `C(δ_x, δ_x) = C(δ_0, δ_0)`.

This is the heterogeneous analogue of the *proved* square `wickConstant_eq_variance`
(`ContinuumLimit/Hypercontractivity.lean`), whose proof routes through the finite-dimensional
Lebesgue density representation of the lattice GFF and translation-volume-preservation.

Reference: Glimm–Jaffe, *Quantum Physics*, §I.3 / §9 (Wick ordering = covariance subtraction).
Strategy: port the square translation-invariance (Lebesgue density representation
`latticeGaussianMeasureAsym_density_integral` + volume-preserving shift on the Euclidean
configuration space `Z_Nt × Z_Ns → ℝ`), OR derive the diagonal site-independence algebraically
from the DFT shift identities (`cos_shift_sum`, `sin_shift_sum`) on the product lattice.

✅ Vetted: deep-think-gemini (Likely correct / Standard) — circulant-matrix diagonal independence
is unconditionally true; the `(a²)⁻¹` GJ normalization matches the `d = 2` lattice action; the
statement is exactly what Wick ordering requires (marginal `ω(δ_x) ∼ N(0, wickConstantAsym)`). -/
axiom wickConstantAsym_eq_variance (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (x : AsymLatticeSites Nt Ns) :
    (wickConstantAsym Nt Ns a mass : ℝ) =
    @inner ℝ ell2' _
      (latticeCovarianceAsymGJ Nt Ns a mass ha hmass (asymLatticeDelta Nt Ns x))
      (latticeCovarianceAsymGJ Nt Ns a mass ha hmass (asymLatticeDelta Nt Ns x))

/-- **Hermite orthogonality for the heterogeneous lattice Gaussian measure.** Wick monomials
`:x^n:_c` of order `n ≥ 1` have zero mean under the GFF, with `c = wickConstantAsym` matching the
site variance. Also states integrability.

Mirror of the square `wickMonomial_latticeGaussian`, via `pairing_is_gaussian` (marginal of
`ω(δ_x)` is `N(0, c)`, using `wickConstantAsym_eq_variance`) and `gaussian_hermite_zero_mean`. -/
theorem wickMonomialAsym_latticeGaussian (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (n : ℕ) (hn : 1 ≤ n) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (x : AsymLatticeSites Nt Ns) :
    Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        wickMonomial n (wickConstantAsym Nt Ns a mass) (ω (asymLatticeDelta Nt Ns x)))
      (latticeGaussianMeasureAsym Nt Ns a mass ha hmass) ∧
    ∫ ω, wickMonomial n (wickConstantAsym Nt Ns a mass) (ω (asymLatticeDelta Nt Ns x))
      ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) = 0 := by
  set μ := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  set T := latticeCovarianceAsymGJ Nt Ns a mass ha hmass
  set δx := asymLatticeDelta Nt Ns x
  set c := wickConstantAsym Nt Ns a mass
  have hc_pos : 0 < c := wickConstantAsym_pos Nt Ns a mass ha hmass
  -- The marginal of ω(δ_x) under μ is N(0, c)
  have h_gauss : μ.map (fun ω : Configuration (AsymLatticeField Nt Ns) => ω δx) =
      gaussianReal 0 (c : ℝ).toNNReal := by
    have := GaussianField.pairing_is_gaussian T δx
    rwa [show @inner ℝ ell2' _ (T δx) (T δx) = c from
      (wickConstantAsym_eq_variance Nt Ns a mass ha hmass x).symm] at this
  have h_meas_eval : Measurable (fun ω : Configuration (AsymLatticeField Nt Ns) => ω δx) :=
    configuration_eval_measurable δx
  obtain ⟨h_int_1d, h_zero_1d⟩ := gaussian_hermite_zero_mean c hc_pos n hn
  set g := fun t : ℝ => wickMonomial n c t
  have hg_comp : (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      wickMonomial n c (ω δx)) = g ∘ (fun ω => ω δx) := rfl
  have h_int_push : Integrable g (μ.map (fun ω => ω δx)) := h_gauss ▸ h_int_1d
  refine ⟨?_, ?_⟩
  · rw [hg_comp]; exact h_int_push.comp_measurable h_meas_eval
  · rw [hg_comp]
    rw [show ∫ x_1, (g ∘ fun ω => ω δx) x_1 ∂μ =
      ∫ t, g t ∂(μ.map (fun ω => ω δx)) from
      (integral_map h_meas_eval.aemeasurable h_int_push.aestronglyMeasurable).symm]
    rw [h_gauss, h_zero_1d]

/-- The Wick polynomial `:P(ω(δ_x)):` has GFF mean equal to the constant coefficient `P.coeff 0`
(all higher Wick monomials integrate to zero). Mirror of `wickPolynomial_integral_eq_coeff_zero`. -/
theorem wickPolynomialAsym_integral_eq_coeff_zero (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (x : AsymLatticeSites Nt Ns) :
    Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        wickPolynomial P (wickConstantAsym Nt Ns a mass) (ω (asymLatticeDelta Nt Ns x)))
      (latticeGaussianMeasureAsym Nt Ns a mass ha hmass) ∧
    ∫ ω, wickPolynomial P (wickConstantAsym Nt Ns a mass) (ω (asymLatticeDelta Nt Ns x))
      ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) =
      P.coeff ⟨0, by have := P.hn_ge; omega⟩ := by
  set μ := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  set c := wickConstantAsym Nt Ns a mass
  set δx := asymLatticeDelta Nt Ns x
  have h_lead_int : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      (1 / P.n : ℝ) * wickMonomial P.n c (ω δx)) μ :=
    (wickMonomialAsym_latticeGaussian Nt Ns P.n (by have := P.hn_ge; omega)
      a mass ha hmass x).1.const_mul _
  have h_term_int : ∀ m : Fin P.n, Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      P.coeff m * wickMonomial (m : ℕ) c (ω δx)) μ := by
    intro m
    by_cases hm : (m : ℕ) = 0
    · have : (fun ω : Configuration (AsymLatticeField Nt Ns) =>
          P.coeff m * wickMonomial (m : ℕ) c (ω δx)) = fun _ => P.coeff m := by
        ext ω; simp [hm]
      rw [this]; exact integrable_const _
    · exact ((wickMonomialAsym_latticeGaussian Nt Ns m (by omega) a mass ha hmass x).1).const_mul _
  have h_sum_int : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      ∑ m : Fin P.n, P.coeff m * wickMonomial (m : ℕ) c (ω δx)) μ :=
    integrable_finset_sum _ fun m _ => h_term_int m
  refine ⟨?_, ?_⟩
  · change Integrable (fun ω => (1 / P.n : ℝ) * wickMonomial P.n c (ω δx) +
      ∑ m : Fin P.n, P.coeff m * wickMonomial (m : ℕ) c (ω δx)) μ
    exact h_lead_int.add h_sum_int
  · change ∫ ω, ((1 / P.n : ℝ) * wickMonomial P.n c (ω δx) +
      ∑ m : Fin P.n, P.coeff m * wickMonomial (m : ℕ) c (ω δx)) ∂μ = _
    rw [integral_add h_lead_int h_sum_int,
        integral_const_mul,
        (wickMonomialAsym_latticeGaussian Nt Ns P.n (by have := P.hn_ge; omega)
          a mass ha hmass x).2,
        mul_zero, zero_add,
        integral_finset_sum _ (fun m _ => h_term_int m)]
    simp_rw [integral_const_mul]
    have h_wm_eval : ∀ m : Fin P.n,
        ∫ ω, wickMonomial (↑m) c (ω δx) ∂μ = if (m : ℕ) = 0 then 1 else 0 := by
      intro m
      by_cases hm : (m : ℕ) = 0
      · simp_rw [if_pos hm, hm, wickMonomial_zero]
        simp [integral_const]
      · rw [if_neg hm, (wickMonomialAsym_latticeGaussian Nt Ns m (by omega) a mass ha hmass x).2]
    simp_rw [h_wm_eval, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have : Finset.univ.filter (fun m : Fin P.n => (m : ℕ) = 0) =
        {⟨0, by have := P.hn_ge; omega⟩} := by
      ext m; simp [Fin.ext_iff]
    rw [this, Finset.sum_singleton]

/-- **Wick-ordering mean property** (heterogeneous lattice): `∫ V_a dμ_{GFF} ≤ 0`.

`∫ V_a = a² · |Λ| · P.coeff₀ ≤ 0` since `P.coeff₀ ≤ 0`. Mirror of
`interactionFunctional_mean_nonpos`. -/
theorem interactionFunctionalAsym_mean_nonpos (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Integrable (interactionFunctionalAsym Nt Ns P a mass)
      (latticeGaussianMeasureAsym Nt Ns a mass ha hmass) ∧
    ∫ ω, interactionFunctionalAsym Nt Ns P a mass ω
      ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) ≤ 0 := by
  set μ := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  have h_site : ∀ x : AsymLatticeSites Nt Ns,
      Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        wickPolynomial P (wickConstantAsym Nt Ns a mass) (ω (asymLatticeDelta Nt Ns x))) μ ∧
      ∫ ω, wickPolynomial P (wickConstantAsym Nt Ns a mass) (ω (asymLatticeDelta Nt Ns x)) ∂μ =
        P.coeff ⟨0, by have := P.hn_ge; omega⟩ :=
    fun x => wickPolynomialAsym_integral_eq_coeff_zero Nt Ns P a mass ha hmass x
  have h_wp_int : ∀ x : AsymLatticeSites Nt Ns,
      Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        wickPolynomial P (wickConstantAsym Nt Ns a mass) (ω (asymLatticeDelta Nt Ns x))) μ :=
    fun x => (h_site x).1
  refine ⟨?_, ?_⟩
  · unfold interactionFunctionalAsym
    exact (integrable_finset_sum _ fun x _ => h_wp_int x).const_mul _
  · unfold interactionFunctionalAsym
    rw [integral_const_mul, integral_finset_sum _ (fun x _ => h_wp_int x)]
    simp_rw [(h_site _).2, Finset.sum_const, nsmul_eq_mul]
    apply mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (le_of_lt ha) 2)
    exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast Fintype.card_pos.le)
      P.coeff_zero_nonpos

/-- **Partition-function lower bound** (heterogeneous lattice): `Z_a ≥ 1` for all `(Nt, Ns, a)`.

Jensen's inequality applied to `exp` and `f = -V_a`:
`Z = ∫ exp(-V) dμ_{GFF} ≥ exp(-∫ V dμ_{GFF}) ≥ exp(0) = 1`, using
`interactionFunctionalAsym_mean_nonpos`. Mirror of `partitionFunction_ge_one`. -/
theorem partitionFunctionAsym_ge_one (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    1 ≤ partitionFunctionAsym Nt Ns P a mass ha hmass := by
  set μ := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  set V := interactionFunctionalAsym Nt Ns P a mass
  obtain ⟨hV_int, hV_mean⟩ := interactionFunctionalAsym_mean_nonpos Nt Ns P a mass ha hmass
  have h_jensen : Real.exp (∫ ω, (-V ω) ∂μ) ≤ ∫ ω, Real.exp (-V ω) ∂μ := by
    have h_conv : ConvexOn ℝ Set.univ Real.exp := convexOn_exp
    have h_cont := Real.continuous_exp.continuousOn (s := Set.univ)
    have h_closed := isClosed_univ (X := ℝ)
    have h_mem : ∀ᵐ ω ∂μ, (-V ω) ∈ Set.univ := ae_of_all _ (fun _ => Set.mem_univ _)
    have h_neg_int : Integrable (fun ω => -V ω) μ := hV_int.neg
    have h_exp_int : Integrable (fun ω => Real.exp (-V ω)) μ :=
      boltzmannWeightAsym_integrable Nt Ns P a mass ha hmass
    exact ConvexOn.map_integral_le h_conv h_cont h_closed h_mem h_neg_int h_exp_int
  have h_neg_mean : 0 ≤ ∫ ω, (-V ω) ∂μ := by
    rw [integral_neg]; linarith
  calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
    _ ≤ Real.exp (∫ ω, (-V ω) ∂μ) := Real.exp_le_exp_of_le h_neg_mean
    _ ≤ ∫ ω, Real.exp (-V ω) ∂μ := h_jensen
    _ = partitionFunctionAsym Nt Ns P a mass ha hmass := rfl

/-- **Cauchy–Schwarz density transfer bound** (heterogeneous lattice): any nonnegative `F` with
finite Gaussian `L²` norm satisfies

  `∫ F dμ_int ≤ K^{1/2} · (∫ F² dμ_{GFF})^{1/2}`,

where `K` bounds the Nelson `L²` exp-moment `∫ (exp(-V))² dμ_{GFF}`. Combines density transfer
`∫ F dμ_int = Z⁻¹ ∫ F·bw dμ_{GFF}`, Cauchy–Schwarz, `Z ≥ 1`, and `∫ bw² ≤ K`. Mirror of the
square `density_transfer_bound`. -/
theorem density_transfer_bound_iso (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (K : ℝ) (_hK_pos : 0 < K)
    (hK : ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (Real.exp (-interactionFunctionalAsym Nt Ns P a mass ω)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) ≤ K)
    (hZ : 1 ≤ partitionFunctionAsym Nt Ns P a mass ha hmass)
    (F : Configuration (AsymLatticeField Nt Ns) → ℝ)
    (hF_nn : ∀ ω, 0 ≤ F ω)
    (hF_meas : AEStronglyMeasurable F (latticeGaussianMeasureAsym Nt Ns a mass ha hmass))
    (hF_sq_int : Integrable (fun ω => F ω ^ 2)
      (latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) :
    ∫ ω, F ω ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
    K ^ (1 / 2 : ℝ) *
    (∫ ω, F ω ^ (2 : ℝ) ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) ^ (1 / 2 : ℝ) := by
  set μ_GFF := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  set bw := boltzmannWeightAsym Nt Ns P a mass
  set V := interactionFunctionalAsym Nt Ns P a mass
  set Z := partitionFunctionAsym Nt Ns P a mass ha hmass
  have hZ_pos : 0 < Z := partitionFunctionAsym_pos Nt Ns P a mass ha hmass
  have hZ_ennreal_ne_zero : ENNReal.ofReal Z ≠ 0 := (ENNReal.ofReal_pos.mpr hZ_pos).ne'
  have hbw_meas : Measurable bw :=
    (interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp
  set bw_nn := fun ω : Configuration (AsymLatticeField Nt Ns) => Real.toNNReal (bw ω)
  have hbw_nn_meas : Measurable bw_nn := Measurable.real_toNNReal hbw_meas
  -- Step 1: Unfold interacting measure to a weighted Gaussian integral
  unfold interactingLatticeMeasureAsym
  rw [integral_smul_measure]
  have wd_eq : ∫ ω, F ω ∂(μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) =
      ∫ ω, bw ω * F ω ∂μ_GFF := by
    change ∫ ω, F ω ∂(μ_GFF.withDensity (fun ω => ↑(bw_nn ω))) =
      ∫ ω, bw ω * F ω ∂μ_GFF
    rw [integral_withDensity_eq_integral_smul hbw_nn_meas]
    congr 1; ext ω
    simp only [bw_nn, NNReal.smul_def, smul_eq_mul]
    rw [Real.coe_toNNReal _ (le_of_lt (boltzmannWeightAsym_pos Nt Ns P a mass ω))]
  rw [wd_eq]
  have hc_real : ((ENNReal.ofReal Z)⁻¹).toReal = Z⁻¹ := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal (le_of_lt hZ_pos)]
  rw [hc_real]
  -- Step 2: Cauchy–Schwarz + bounds
  obtain ⟨B, hB⟩ := interactionFunctionalAsym_bounded_below Nt Ns P a mass ha hmass
  have hbw_bound : ∀ ω, bw ω ≤ Real.exp B := fun ω =>
    Real.exp_le_exp_of_le (by linarith [hB ω])
  haveI : IsProbabilityMeasure μ_GFF :=
    latticeGaussianMeasureAsym_isProbability Nt Ns a mass ha hmass
  have hbw_sq_int : Integrable (fun ω => bw ω ^ 2) μ_GFF :=
    Integrable.of_bound (hbw_meas.pow_const 2).aestronglyMeasurable (Real.exp B ^ 2)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq'
          (by linarith [boltzmannWeightAsym_pos Nt Ns P a mass ω, Real.exp_pos B])
          (hbw_bound ω))
  have hbw_memLp : MemLp bw 2 μ_GFF :=
    (memLp_two_iff_integrable_sq hbw_meas.aestronglyMeasurable).mpr hbw_sq_int
  have hF_memLp : MemLp F 2 μ_GFF :=
    (memLp_two_iff_integrable_sq hF_meas).mpr hF_sq_int
  have h_cs : ∫ ω, bw ω * F ω ∂μ_GFF ≤
      (∫ ω, bw ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2 : ℝ) *
      (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2 : ℝ) := by
    have h_ofReal : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_num
    have hbw' : MemLp bw (ENNReal.ofReal 2) μ_GFF := h_ofReal ▸ hbw_memLp
    have hF' : MemLp F (ENNReal.ofReal 2) μ_GFF := h_ofReal ▸ hF_memLp
    exact integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ (fun ω => le_of_lt (boltzmannWeightAsym_pos Nt Ns P a mass ω)))
      (ae_of_all _ hF_nn) hbw' hF'
  have hZinv_le : Z⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hZ
  have hbw_sq_le : (∫ ω, bw ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2 : ℝ) ≤ K ^ (1/2 : ℝ) := by
    apply Real.rpow_le_rpow (integral_nonneg (fun ω =>
      Real.rpow_nonneg (le_of_lt (boltzmannWeightAsym_pos Nt Ns P a mass ω)) _))
    · have : ∫ ω, bw ω ^ (2:ℝ) ∂μ_GFF = ∫ ω, (Real.exp (-V ω)) ^ 2 ∂μ_GFF := by
        congr 1; ext ω; exact Real.rpow_natCast _ 2
      linarith
    · linarith
  calc Z⁻¹ * ∫ ω, bw ω * F ω ∂μ_GFF
      ≤ Z⁻¹ * ((∫ ω, bw ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) *
          (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ)) :=
        mul_le_mul_of_nonneg_left h_cs (le_of_lt (inv_pos.mpr hZ_pos))
    _ ≤ 1 * (K ^ (1/2:ℝ) * (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ)) := by
        have hF_int_nn : 0 ≤ (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) :=
          Real.rpow_nonneg (integral_nonneg (fun ω => Real.rpow_nonneg (hF_nn ω) _)) _
        have hbw_int_nn : 0 ≤ (∫ ω, bw ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) :=
          Real.rpow_nonneg (integral_nonneg (fun ω =>
            Real.rpow_nonneg (le_of_lt (boltzmannWeightAsym_pos Nt Ns P a mass ω)) _)) _
        apply mul_le_mul hZinv_le _ (mul_nonneg hbw_int_nn hF_int_nn) (by linarith)
        exact mul_le_mul_of_nonneg_right hbw_sq_le hF_int_nn
    _ = K ^ (1/2:ℝ) * (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) := one_mul _

end Pphi2

end
