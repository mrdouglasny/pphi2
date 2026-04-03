/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniqueness of Gaussian Measures from Covariance

Proves that two centered Gaussian probability measures on `Configuration E`
with the same covariance must be equal. This is a general result for any
DyninMityaginSpace.

## Main results

- `gaussian_measure_unique_of_covariance`: If μ₁ and μ₂ are centered Gaussian
  probability measures on `Configuration E` with the same covariance, then μ₁ = μ₂.

## Proof strategy

From the hypotheses, one derives that for all f : E,
  ∫ exp(ω f) dμ₁ = exp(½ ∫(ω f)² dμ₁) = exp(½ ∫(ω f)² dμ₂) = ∫ exp(ω f) dμ₂.

Applying this to `t • f` yields that the moment generating function `t ↦ exp(t² σ²/2)`
of the 1D marginal `(eval_f)_* μ` agrees for both measures, for every test function f.
Since the MGF of a centered Gaussian N(0, σ²) is `exp(t² σ²/2)`, and MGFs determine
distributions, both 1D marginals equal `gaussianReal 0 σ²` for the same σ².

This extends to finite-dimensional marginals by linearity: the joint distribution of
(ω f₁, ..., ω f_k) is determined by its characteristic function, which at (t₁,...,t_k)
equals the 1D characteristic function of ω(∑ tⱼ fⱼ), hence agrees for both measures.

By Dynkin's pi-lambda theorem, measures agreeing on all finite-dimensional cylinder
sets agree on the cylindrical σ-algebra.

## Sorry status

No sorries. All proofs complete.

## Proved results

- `mgf_eq_of_covariance`: Same covariance implies same MGF for all test functions.
- `mgf_at_scaled`: The Gaussian MGF identity applied to `t • f` gives
  `∫ exp(t ωf) = exp(t²σ²/2)`.
- `eval_map_eq_of_covariance`: 1D marginals agree for all test functions. Uses
  analytic continuation from real to complex MGF (via Mathlib's
  `eqOn_complexMGF_of_mgf` + `integrableExpSet_id_gaussianReal`) and
  `ext_of_complexMGF_eq`.
- `pushforward_eq_of_eval_eq`: Equal 1D marginals for all f : E imply equal
  pushforward measures on `ℝ^ℕ` via `configBasisEval`. Uses Cramer-Wold
  (`ext_of_charFunDual` for finite-dim marginals) + Kolmogorov uniqueness
  (`IsProjectiveLimit.unique` for the product sigma-algebra).
- `gaussian_measure_unique_of_covariance`: The main theorem. The pullback
  from `ℝ^ℕ` uses `instMeasurableSpaceConfiguration_eq_comap`.
-/

import GaussianField.ConfigurationEmbedding
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

noncomputable section

namespace GaussianField

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [hDM : DyninMityaginSpace E]

/-! ## Step 1: MGF equality from hypotheses -/

omit hDM in
/-- If two centered Gaussian measures have the same covariance, their moment
    generating functions agree on all test functions. -/
theorem mgf_eq_of_covariance
    (μ₁ μ₂ : @Measure (Configuration E) instMeasurableSpaceConfiguration)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁_gauss : ∀ (f : E),
      ∫ ω : Configuration E, Real.exp (ω f) ∂μ₁ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ₁))
    (hμ₂_gauss : ∀ (f : E),
      ∫ ω : Configuration E, Real.exp (ω f) ∂μ₂ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ₂))
    (hcov : ∀ (f : E),
      ∫ ω : Configuration E, (ω f) ^ 2 ∂μ₁ =
      ∫ ω : Configuration E, (ω f) ^ 2 ∂μ₂)
    (f : E) :
    ∫ ω : Configuration E, Real.exp (ω f) ∂μ₁ =
    ∫ ω : Configuration E, Real.exp (ω f) ∂μ₂ := by
  rw [hμ₁_gauss f, hμ₂_gauss f, hcov f]

/-! ## Step 2: Scaled MGF identity -/

omit hDM in
/-- For a centered Gaussian measure satisfying the MGF identity, the MGF
    at `t • f` gives `exp(t² σ²(f) / 2)` where `σ²(f) = ∫ (ω f)² dμ`.
    This follows from linearity of ω and the hypothesis. -/
theorem mgf_at_scaled
    (μ : @Measure (Configuration E) instMeasurableSpaceConfiguration)
    [IsProbabilityMeasure μ]
    (hμ_gauss : ∀ (f : E),
      ∫ ω : Configuration E, Real.exp (ω f) ∂μ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ))
    (f : E) (t : ℝ) :
    ∫ ω : Configuration E, Real.exp (t * ω f) ∂μ =
    Real.exp (t ^ 2 / 2 * ∫ ω, (ω f) ^ 2 ∂μ) := by
  have h := hμ_gauss (t • f)
  -- ω(t • f) = t * ω(f) by linearity
  simp_rw [show ∀ ω : Configuration E, ω (t • f) = t * ω f from
    fun ω => map_smul ω t f] at h
  -- (t * ω f) ^ 2 = t ^ 2 * (ω f) ^ 2
  simp_rw [show ∀ ω : Configuration E, (t * ω f) ^ 2 = t ^ 2 * (ω f) ^ 2 from
    fun ω => by ring] at h
  rw [h, integral_const_mul]
  congr 1; ring

omit hDM in
/-- A centered Gaussian measure on `Configuration E` has Gaussian 1D marginals.

For each test function `f`, the pushforward of `μ` by evaluation `ω ↦ ω f`
is the centered real Gaussian with variance
`σ² = ∫ (ω f)^2 dμ`. This is the one-measure analogue of
`eval_map_eq_of_covariance`. -/
theorem eval_map_eq_gaussianReal
    (μ : @Measure (Configuration E) instMeasurableSpaceConfiguration)
    [IsProbabilityMeasure μ]
    (hμ_gauss : ∀ (f : E),
      ∫ ω : Configuration E, Real.exp (ω f) ∂μ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ))
    (f : E) :
    μ.map (fun ω : Configuration E => ω f) =
    gaussianReal 0 (∫ ω : Configuration E, (ω f) ^ 2 ∂μ).toNNReal := by
  set σ_sq : ℝ := ∫ ω : Configuration E, (ω f) ^ 2 ∂μ
  set σ : NNReal := σ_sq.toNNReal
  have hσ_nonneg : 0 ≤ σ_sq := integral_nonneg (fun _ => sq_nonneg _)
  have hσ_cast : (σ : ℝ) = σ_sq := Real.coe_toNNReal _ hσ_nonneg
  have h_meas : @Measurable _ _ instMeasurableSpaceConfiguration _
      (fun ω : Configuration E => ω f) := configuration_eval_measurable f
  have hmgf : ProbabilityTheory.mgf (fun ω : Configuration E => ω f) μ =
      ProbabilityTheory.mgf id (gaussianReal 0 σ) := by
    ext t
    simp only [ProbabilityTheory.mgf, id]
    rw [mgf_at_scaled μ hμ_gauss f t]
    rw [show ∫ x, Real.exp (t * x) ∂gaussianReal 0 σ =
        Real.exp (0 * t + ↑σ * t ^ 2 / 2) from
      ProbabilityTheory.mgf_gaussianReal (by simp) t]
    congr 1
    simp only [zero_mul, zero_add, hσ_cast]
    ring
  have h_eqOn := ProbabilityTheory.eqOn_complexMGF_of_mgf hmgf
  have h_strip :
      ProbabilityTheory.integrableExpSet (fun ω : Configuration E => ω f) μ = Set.univ := by
    rw [ProbabilityTheory.integrableExpSet_eq_of_mgf hmgf,
      ProbabilityTheory.integrableExpSet_id_gaussianReal]
  rw [h_strip, interior_univ] at h_eqOn
  have h_cmgf : ProbabilityTheory.complexMGF (fun ω : Configuration E => ω f) μ =
      ProbabilityTheory.complexMGF id (gaussianReal 0 σ) :=
    funext (fun z => h_eqOn (Set.mem_univ z))
  have h_map_eq := Measure.ext_of_complexMGF_eq
    h_meas.aemeasurable aemeasurable_id h_cmgf
  simpa only [Measure.map_id] using h_map_eq

/-- Along a weakly convergent sequence of centered real Gaussians, the cosine
transform converges to the cosine transform of the weak limit. -/
private theorem weakLimit_cos_conv
    (ν_seq : ℕ → Measure ℝ) (v_seq : ℕ → NNReal)
    (hν_prob : ∀ n, IsProbabilityMeasure (ν_seq n))
    (hν_gauss : ∀ n, ν_seq n = gaussianReal 0 (v_seq n))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hconv : ∀ (g : ℝ → ℝ), Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n => ∫ x, g x ∂(ν_seq n)) atTop (nhds (∫ x, g x ∂ν)))
    (t : ℝ) :
    Tendsto (fun n => Real.exp (-(↑(v_seq n : ℝ) * t ^ 2 / 2)))
      atTop (nhds (∫ x, Real.cos (t * x) ∂ν)) := by
  have h_cos_conv : Tendsto (fun n => ∫ x, Real.cos (t * x) ∂(ν_seq n))
      atTop (nhds (∫ x, Real.cos (t * x) ∂ν)) :=
    hconv _ (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      ⟨1, fun x => abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩⟩
  suffices h_eq : ∀ n, ∫ x, Real.cos (t * x) ∂(ν_seq n) =
      Real.exp (-(↑(v_seq n : ℝ) * t ^ 2 / 2)) from
    h_cos_conv.congr (fun n => h_eq n)
  intro n
  haveI h_prob_n : IsProbabilityMeasure (ν_seq n) := hν_prob n
  have h_cf : MeasureTheory.charFun (ν_seq n) t =
      Complex.exp (-(↑(v_seq n : ℝ) * ↑t ^ 2 / 2)) := by
    rw [hν_gauss n, ProbabilityTheory.charFun_gaussianReal]
    congr 1
    push_cast
    ring
  have h_cast_eq : -(↑↑(v_seq n) * (↑t : ℂ) ^ 2 / 2) =
      ↑(-(↑(v_seq n : ℝ) * t ^ 2 / 2) : ℝ) := by
    simp only [ofReal_neg, ofReal_div, ofReal_mul, ofReal_pow]
    push_cast
    ring
  have h_cf_real : MeasureTheory.charFun (ν_seq n) t =
      ↑(Real.exp (-(↑(v_seq n : ℝ) * t ^ 2 / 2))) := by
    rw [h_cf, h_cast_eq, ofReal_exp]
  have h_re_cf : (MeasureTheory.charFun (ν_seq n) t).re =
      Real.exp (-(↑(v_seq n : ℝ) * t ^ 2 / 2)) := by
    rw [h_cf_real, ofReal_re]
  rw [MeasureTheory.charFun_apply_real] at h_re_cf
  have h_int : Integrable (fun x : ℝ => Complex.exp (↑t * ↑x * I)) (ν_seq n) :=
    (integrable_const (1 : ℝ)).mono'
      ((by fun_prop :
        Continuous fun (x : ℝ) => Complex.exp (↑t * ↑x * I)).aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [show (↑t : ℂ) * ↑x * I = ↑(t * x) * I from by
          push_cast
          ring, Complex.norm_exp_ofReal_mul_I])
  rw [← h_re_cf]
  trans ∫ x : ℝ, (Complex.exp (↑t * ↑x * I)).re ∂(ν_seq n)
  · exact integral_congr_ae (ae_of_all _ fun x => by
      change Real.cos (t * x) = (Complex.exp (↑t * ↑x * I)).re
      rw [show (↑t : ℂ) * ↑x * I = ↑(t * x) * I from by
        push_cast
        ring]
      exact (exp_ofReal_mul_I_re _).symm)
  · have h := integral_re h_int
    simp only [RCLike.re_to_complex] at h
    exact h

/-- Centered real Gaussians have vanishing sine transform, and that property
passes to weak limits tested against bounded continuous observables. -/
private theorem weakLimit_sin_zero
    (ν_seq : ℕ → Measure ℝ) (v_seq : ℕ → NNReal)
    (hν_prob : ∀ n, IsProbabilityMeasure (ν_seq n))
    (hν_gauss : ∀ n, ν_seq n = gaussianReal 0 (v_seq n))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hconv : ∀ (g : ℝ → ℝ), Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n => ∫ x, g x ∂(ν_seq n)) atTop (nhds (∫ x, g x ∂ν)))
    (t : ℝ) :
    ∫ x, Real.sin (t * x) ∂ν = 0 := by
  have h_sin_conv : Tendsto (fun n => ∫ x, Real.sin (t * x) ∂(ν_seq n))
      atTop (nhds (∫ x, Real.sin (t * x) ∂ν)) :=
    hconv _ (Real.continuous_sin.comp (continuous_const.mul continuous_id))
      ⟨1, fun x => abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩⟩
  suffices h_eq : ∀ n, ∫ x, Real.sin (t * x) ∂(ν_seq n) = 0 from
    tendsto_nhds_unique (h_sin_conv.congr h_eq) tendsto_const_nhds
  intro n
  haveI h_prob_n : IsProbabilityMeasure (ν_seq n) := hν_prob n
  have h_cf : MeasureTheory.charFun (ν_seq n) t =
      Complex.exp (-(↑(v_seq n : ℝ) * ↑t ^ 2 / 2)) := by
    rw [hν_gauss n, ProbabilityTheory.charFun_gaussianReal]
    congr 1
    push_cast
    ring
  have h_cast_eq : -(↑↑(v_seq n) * (↑t : ℂ) ^ 2 / 2) =
      ↑(-(↑(v_seq n : ℝ) * t ^ 2 / 2) : ℝ) := by
    simp only [ofReal_neg, ofReal_div, ofReal_mul, ofReal_pow]
    push_cast
    ring
  have h_cf_real : MeasureTheory.charFun (ν_seq n) t =
      ↑(Real.exp (-(↑(v_seq n : ℝ) * t ^ 2 / 2))) := by
    rw [h_cf, h_cast_eq, ofReal_exp]
  have h_im_cf : (MeasureTheory.charFun (ν_seq n) t).im = 0 := by
    rw [h_cf_real, ofReal_im]
  rw [MeasureTheory.charFun_apply_real] at h_im_cf
  have h_int : Integrable (fun x : ℝ => Complex.exp (↑t * ↑x * I)) (ν_seq n) :=
    (integrable_const (1 : ℝ)).mono'
      ((by fun_prop :
        Continuous fun (x : ℝ) => Complex.exp (↑t * ↑x * I)).aestronglyMeasurable)
      (ae_of_all _ fun x => by
        rw [show (↑t : ℂ) * ↑x * I = ↑(t * x) * I from by
          push_cast
          ring, Complex.norm_exp_ofReal_mul_I])
  rw [← h_im_cf]
  trans ∫ x : ℝ, (Complex.exp (↑t * ↑x * I)).im ∂(ν_seq n)
  · exact integral_congr_ae (ae_of_all _ fun x => by
      change Real.sin (t * x) = (Complex.exp (↑t * ↑x * I)).im
      rw [show (↑t : ℂ) * ↑x * I = ↑(t * x) * I from by
        push_cast
        ring]
      exact (exp_ofReal_mul_I_im _).symm)
  · have h := integral_im h_int
    simp only [RCLike.im_to_complex] at h
    exact h

/-- Weak limits of centered real Gaussian measures are again centered real
Gaussian measures. -/
theorem weakLimit_centered_gaussianReal
    (ν_seq : ℕ → Measure ℝ) (v_seq : ℕ → NNReal)
    (hν_prob : ∀ n, IsProbabilityMeasure (ν_seq n))
    (hν_gauss : ∀ n, ν_seq n = gaussianReal 0 (v_seq n))
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hconv : ∀ (g : ℝ → ℝ), Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n => ∫ x, g x ∂(ν_seq n)) atTop (nhds (∫ x, g x ∂ν))) :
    ∃ v : NNReal, ν = gaussianReal 0 v := by
  have h_cos_limit := weakLimit_cos_conv ν_seq v_seq hν_prob hν_gauss ν hconv
  have h_sin_zero := weakLimit_sin_zero ν_seq v_seq hν_prob hν_gauss ν hconv
  have h_cos_int_cts : Continuous (fun t : ℝ => ∫ x, Real.cos (t * x) ∂ν) := by
    exact continuous_of_dominated
      (fun t => (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).aestronglyMeasurable)
      (fun t => ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one _)
      (integrable_const 1)
      (ae_of_all _ fun x =>
        Real.continuous_cos.comp (continuous_id.mul continuous_const))
  have h_cos_zero : (fun t : ℝ => ∫ x, Real.cos (t * x) ∂ν) 0 = 1 := by
    simp
  have h_at_one : Tendsto (fun n => Real.exp (-(↑(v_seq n : ℝ) / 2)))
      atTop (nhds (∫ x, Real.cos (1 * x) ∂ν)) := by
    convert h_cos_limit 1 using 2
    congr 1
    ring
  have h_limit_nonneg : 0 ≤ ∫ x, Real.cos (1 * x) ∂ν :=
    ge_of_tendsto' h_at_one (fun n => le_of_lt (Real.exp_pos _))
  have h_limit_pos : 0 < ∫ x, Real.cos (1 * x) ∂ν := by
    by_contra h_not_pos
    push Not at h_not_pos
    have h_zero : ∫ x, Real.cos (1 * x) ∂ν = 0 :=
      le_antisymm h_not_pos h_limit_nonneg
    have h_vn_infty : Tendsto (fun n => (v_seq n : ℝ)) atTop atTop := by
      rw [Filter.tendsto_atTop]
      intro b
      have h0 : Tendsto (fun n => Real.exp (-(↑(v_seq n : ℝ) / 2))) atTop (nhds 0) := by
        rwa [h_zero] at h_at_one
      exact (h0.eventually (Iio_mem_nhds (Real.exp_pos (-(b / 2))))).mono
        (fun n hn => by
          rw [Real.exp_lt_exp, neg_lt_neg_iff] at hn
          linarith)
    have h_all_zero : ∀ t : ℝ, t ≠ 0 → ∫ x, Real.cos (t * x) ∂ν = 0 := by
      intro t ht
      apply tendsto_nhds_unique (h_cos_limit t)
      apply Real.tendsto_exp_atBot.comp
      show Tendsto (fun n => -(↑(v_seq n : ℝ) * t ^ 2 / 2)) atTop atBot
      rw [show (fun n => -(↑(v_seq n : ℝ) * t ^ 2 / 2)) =
          fun n => -(t ^ 2 / 2) * (v_seq n : ℝ) from
        funext (fun _ => by ring)]
      exact (tendsto_const_mul_atBot_of_neg
        (neg_lt_zero.mpr (div_pos (sq_pos_of_ne_zero ht) two_pos))).mpr h_vn_infty
    have h_ext : (fun t : ℝ => ∫ x, Real.cos (t * x) ∂ν) = fun _ => (0 : ℝ) :=
      h_cos_int_cts.ext_on (dense_compl_singleton 0) continuous_const
        (fun t ht => h_all_zero t ht)
    have := congr_fun h_ext 0
    simp at this
  set L := ∫ x, Real.cos (1 * x) ∂ν
  have hL_le : L ≤ 1 := by
    apply le_of_tendsto' (h_cos_limit 1)
    intro n
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (by positivity)
  have h_neg2logL_nonneg : 0 ≤ -2 * Real.log L := by
    have := Real.log_nonpos h_limit_pos.le hL_le
    nlinarith
  set v_lim : NNReal := (-2 * Real.log L).toNNReal
  have h_vlim_cast : (v_lim : ℝ) = -2 * Real.log L :=
    Real.coe_toNNReal _ h_neg2logL_nonneg
  have h_vseq_conv : Tendsto (fun n => (v_seq n : ℝ)) atTop (nhds (v_lim : ℝ)) := by
    rw [h_vlim_cast]
    have h_neg_half : Tendsto (fun n => -(↑(v_seq n : ℝ) / 2))
        atTop (nhds (Real.log L)) :=
      (h_at_one.log (ne_of_gt h_limit_pos)).congr (fun n => Real.log_exp _)
    convert h_neg_half.const_mul (-2) using 1
    ext n
    ring
  have h_cos_eq : ∀ t, ∫ x, Real.cos (t * x) ∂ν =
      Real.exp (-(↑(v_lim : ℝ) * t ^ 2 / 2)) := by
    intro t
    apply tendsto_nhds_unique (h_cos_limit t)
    exact (Real.continuous_exp.tendsto _).comp
      (((h_vseq_conv.mul_const _).div_const 2).neg)
  have h_cf_eq : MeasureTheory.charFun ν =
      MeasureTheory.charFun (gaussianReal 0 v_lim) := by
    ext t
    have h_int : Integrable (fun x : ℝ => Complex.exp (↑t * ↑x * I)) ν :=
      (integrable_const (1 : ℝ)).mono'
        ((by fun_prop :
          Continuous fun (x : ℝ) => Complex.exp (↑t * ↑x * I)).aestronglyMeasurable)
        (ae_of_all _ fun x => by
          rw [show (↑t : ℂ) * ↑x * I = ↑(t * x) * I from by
            push_cast
            ring, Complex.norm_exp_ofReal_mul_I])
    rw [MeasureTheory.charFun_apply_real]
    have h_re : (∫ x : ℝ, Complex.exp (↑t * ↑x * I) ∂ν).re =
        Real.exp (-(↑(v_lim : ℝ) * t ^ 2 / 2)) := by
      trans ∫ x : ℝ, (Complex.exp (↑t * ↑x * I)).re ∂ν
      · have h := integral_re h_int
        simp only [RCLike.re_to_complex] at h
        exact h.symm
      · rw [show (fun x : ℝ => (Complex.exp (↑t * ↑x * I)).re) =
            fun x => Real.cos (t * x) from
          funext (fun x => by
            rw [show (↑t : ℂ) * ↑x * I = ↑(t * x) * I from by
              push_cast
              ring]
            exact exp_ofReal_mul_I_re _)]
        exact h_cos_eq t
    have h_im : (∫ x : ℝ, Complex.exp (↑t * ↑x * I) ∂ν).im = 0 := by
      trans ∫ x : ℝ, (Complex.exp (↑t * ↑x * I)).im ∂ν
      · have h := integral_im h_int
        simp only [RCLike.im_to_complex] at h
        exact h.symm
      · rw [show (fun x : ℝ => (Complex.exp (↑t * ↑x * I)).im) =
            fun x => Real.sin (t * x) from
          funext (fun x => by
            rw [show (↑t : ℂ) * ↑x * I = ↑(t * x) * I from by
              push_cast
              ring]
            exact exp_ofReal_mul_I_im _)]
        exact h_sin_zero t
    have h_lhs : (∫ x : ℝ, Complex.exp (↑t * ↑x * I) ∂ν) =
        ↑(Real.exp (-(↑(v_lim : ℝ) * t ^ 2 / 2))) := by
      exact Complex.ext h_re (by rw [h_im, ofReal_im])
    rw [h_lhs, ProbabilityTheory.charFun_gaussianReal]
    push_cast
    ring_nf
  exact ⟨v_lim, Measure.ext_of_charFun h_cf_eq⟩

/-! ## Step 3: Equal 1D marginals for all test functions -/

omit hDM in
/-- Two centered Gaussian measures with the same covariance have the same
    1D marginal for every test function f.

    Both 1D marginals are `gaussianReal 0 σ²` where `σ² = ∫(ω f)²dμ`.
    The proof requires showing that the real MGF `t ↦ exp(t²σ²/2)` uniquely
    determines the distribution. This follows from analytic continuation to
    the complex MGF `z ↦ exp(z²σ²/2)` and `Measure.ext_of_complexMGF_eq`. -/
theorem eval_map_eq_of_covariance
    (μ₁ μ₂ : @Measure (Configuration E) instMeasurableSpaceConfiguration)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁_gauss : ∀ (f : E),
      ∫ ω : Configuration E, Real.exp (ω f) ∂μ₁ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ₁))
    (hμ₂_gauss : ∀ (f : E),
      ∫ ω : Configuration E, Real.exp (ω f) ∂μ₂ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ₂))
    (hcov : ∀ (f : E),
      ∫ ω : Configuration E, (ω f) ^ 2 ∂μ₁ =
      ∫ ω : Configuration E, (ω f) ^ 2 ∂μ₂)
    (f : E) :
    μ₁.map (fun ω : Configuration E => ω f) =
    μ₂.map (fun ω : Configuration E => ω f) := by
  set σ := (∫ ω : Configuration E, (ω f) ^ 2 ∂μ₁).toNNReal with hσ_def
  have h_meas : @Measurable _ _ instMeasurableSpaceConfiguration _
      (fun ω : Configuration E => ω f) := configuration_eval_measurable f
  -- Show both measures have the same real MGF as gaussianReal 0 σ
  have hmgf₁ : ProbabilityTheory.mgf (fun ω : Configuration E => ω f) μ₁ =
      ProbabilityTheory.mgf id (gaussianReal 0 σ) := by
    ext t
    simp only [ProbabilityTheory.mgf, id]
    rw [mgf_at_scaled μ₁ hμ₁_gauss f t]
    rw [show ∫ x, Real.exp (t * x) ∂gaussianReal 0 σ =
        Real.exp (0 * t + ↑σ * t ^ 2 / 2) from
      ProbabilityTheory.mgf_gaussianReal (by simp) t]
    congr 1
    simp only [zero_mul, zero_add, hσ_def,
      Real.coe_toNNReal _ (integral_nonneg (fun _ => sq_nonneg _))]
    ring
  have hmgf₂ : ProbabilityTheory.mgf (fun ω : Configuration E => ω f) μ₂ =
      ProbabilityTheory.mgf id (gaussianReal 0 σ) := by
    -- Reuse hmgf₁ and the fact that the real MGF of μ₂ matches μ₁ (via hcov)
    have hmgf₂_eq_₁ : ProbabilityTheory.mgf (fun ω : Configuration E => ω f) μ₂ =
        ProbabilityTheory.mgf (fun ω : Configuration E => ω f) μ₁ := by
      ext t
      simp only [ProbabilityTheory.mgf]
      rw [mgf_at_scaled μ₁ hμ₁_gauss f t, mgf_at_scaled μ₂ hμ₂_gauss f t, hcov f]
    rw [hmgf₂_eq_₁, hmgf₁]
  -- From equal real MGFs, derive equal complexMGFs via analytic continuation.
  -- The integrableExpSet for gaussianReal is all of ℝ, so the strip is all of ℂ.
  have h_eqOn₁ := ProbabilityTheory.eqOn_complexMGF_of_mgf hmgf₁
  have h_eqOn₂ := ProbabilityTheory.eqOn_complexMGF_of_mgf hmgf₂
  -- The strip = ℂ because integrableExpSet = univ for our X
  have h_strip :
      ProbabilityTheory.integrableExpSet (fun ω : Configuration E => ω f) μ₁ = Set.univ := by
    rw [ProbabilityTheory.integrableExpSet_eq_of_mgf hmgf₁,
        ProbabilityTheory.integrableExpSet_id_gaussianReal]
  rw [h_strip, interior_univ] at h_eqOn₁
  have h_strip₂ :
      ProbabilityTheory.integrableExpSet (fun ω : Configuration E => ω f) μ₂ = Set.univ := by
    rw [ProbabilityTheory.integrableExpSet_eq_of_mgf hmgf₂,
        ProbabilityTheory.integrableExpSet_id_gaussianReal]
  rw [h_strip₂, interior_univ] at h_eqOn₂
  -- Now h_eqOn₁ : EqOn (complexMGF eval_f μ₁) (complexMGF id gaussianReal) univ
  -- and h_eqOn₂ : EqOn (complexMGF eval_f μ₂) (complexMGF id gaussianReal) univ
  have h_cmgf₁ : ProbabilityTheory.complexMGF (fun ω : Configuration E => ω f) μ₁ =
      ProbabilityTheory.complexMGF id (gaussianReal 0 σ) :=
    funext (fun z => h_eqOn₁ (Set.mem_univ z))
  have h_cmgf₂ : ProbabilityTheory.complexMGF (fun ω : Configuration E => ω f) μ₂ =
      ProbabilityTheory.complexMGF id (gaussianReal 0 σ) :=
    funext (fun z => h_eqOn₂ (Set.mem_univ z))
  -- Equal complexMGFs → equal distributions
  have h₁ := Measure.ext_of_complexMGF_eq h_meas.aemeasurable aemeasurable_id h_cmgf₁
  have h₂ := Measure.ext_of_complexMGF_eq h_meas.aemeasurable aemeasurable_id h_cmgf₂
  -- h₁ : μ₁.map eval_f = gaussianReal 0 σ (via map id = id)
  simp only [Measure.map_id] at h₁ h₂
  rw [h₁, h₂]

/-! ## Step 4: Pushforward equality on ℝ^ℕ -/

/-- If two probability measures on `Configuration E` have the same 1D marginal
    for every test function f : E, then their pushforwards to ℝ^ℕ via
    `configBasisEval` agree.

    This is the combination of the Cramér-Wold theorem (equal 1D marginals on
    all linear combinations determine finite-dimensional joint distributions)
    and Kolmogorov's extension uniqueness (equal finite-dimensional marginals
    determine measures on the product σ-algebra of a Polish space). -/
theorem pushforward_eq_of_eval_eq
    (μ₁ μ₂ : @Measure (Configuration E) instMeasurableSpaceConfiguration)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h_eval : ∀ f : E,
      μ₁.map (fun ω : Configuration E => ω f) =
      μ₂.map (fun ω : Configuration E => ω f)) :
    @Measure.map _ _ instMeasurableSpaceConfiguration _
      (configBasisEval (E := E)) μ₁ =
    @Measure.map _ _ instMeasurableSpaceConfiguration _
      (configBasisEval (E := E)) μ₂ := by
  set ν₁ := @Measure.map _ _ instMeasurableSpaceConfiguration _
    (configBasisEval (E := E)) μ₁
  set ν₂ := @Measure.map _ _ instMeasurableSpaceConfiguration _
    (configBasisEval (E := E)) μ₂
  haveI : IsProbabilityMeasure ν₁ :=
    Measure.isProbabilityMeasure_map
      configBasisEval_measurable.aemeasurable
  haveI : IsProbabilityMeasure ν₂ :=
    Measure.isProbabilityMeasure_map
      configBasisEval_measurable.aemeasurable
  -- Step 1: Finite-dimensional marginals agree (Cramer-Wold)
  have h_marginals :
      ∀ I : Finset ℕ, ν₁.map I.restrict = ν₂.map I.restrict := by
    intro I
    have h_mr : Measurable (Finset.restrict
        (π := fun _ : ℕ => ℝ) I) :=
      measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
    rw [Measure.map_map h_mr configBasisEval_measurable,
        Measure.map_map h_mr configBasisEval_measurable]
    have h_cm : @Measurable _ _
        instMeasurableSpaceConfiguration _
        (I.restrict ∘ configBasisEval (E := E)) :=
      h_mr.comp configBasisEval_measurable
    apply Measure.ext_of_charFunDual
    ext L
    simp only [charFunDual_apply]
    have h_asm : ∀ (ν : Measure (↑I → ℝ)),
        AEStronglyMeasurable
        (fun x : ↑I → ℝ =>
          Complex.exp (↑(L x) * Complex.I)) ν :=
      fun _ => (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.comp L.continuous
          |>.mul continuous_const)).aestronglyMeasurable
    rw [integral_map h_cm.aemeasurable (h_asm _),
        integral_map h_cm.aemeasurable (h_asm _)]
    -- Define f = sum of L(e_n) * basis_n
    set f : E := I.sum (fun n =>
      (L (fun j => if (j : ℕ) = n then 1 else 0)) •
      DyninMityaginSpace.basis n) with hf_def
    -- Key: L(I.restrict(configBasisEval w)) = w f
    suffices h_key : ∀ ω : Configuration E,
        L (I.restrict (configBasisEval ω)) = ω f by
      -- Goal: ∫ x, exp(L(restrict ∘ cBE)(x) * I) dμ₁ =
      --       ∫ x, exp(L(restrict ∘ cBE)(x) * I) dμ₂
      -- Unfold ∘ and apply h_key to rewrite integrand
      simp_rw [Function.comp_apply, h_key]
      -- Goal: ∫ ω, exp(↑(ω f) * I) dμ₁ =
      --       ∫ ω, exp(↑(ω f) * I) dμ₂
      have h_em : ∀ (μ : @Measure (Configuration E)
          instMeasurableSpaceConfiguration),
          AEMeasurable (fun ω : Configuration E => ω f) μ :=
        fun _ =>
          (configuration_eval_measurable f).aemeasurable
      have h_gsm : ∀ (ν : Measure ℝ),
          AEStronglyMeasurable
          (fun x : ℝ =>
            Complex.exp (↑x * Complex.I)) ν :=
        fun _ => (Complex.continuous_exp.comp
          (Complex.continuous_ofReal.mul
            continuous_const)).aestronglyMeasurable
      calc ∫ ω : Configuration E,
              Complex.exp (↑(ω f) * Complex.I) ∂μ₁
          = ∫ x, Complex.exp (↑x * Complex.I)
              ∂(μ₁.map (fun ω => ω f)) :=
            (integral_map (h_em μ₁) (h_gsm _)).symm
        _ = ∫ x, Complex.exp (↑x * Complex.I)
              ∂(μ₂.map (fun ω => ω f)) := by
            rw [h_eval f]
        _ = ∫ ω : Configuration E,
              Complex.exp (↑(ω f) * Complex.I) ∂μ₂ :=
            integral_map (h_em μ₂) (h_gsm _)
    -- Prove L(I.restrict(configBasisEval w)) = w f
    intro ω
    have h_decomp :
        I.restrict (configBasisEval (E := E) ω) =
        I.sum (fun n => (configBasisEval ω n) •
          (fun j : ↑I =>
            if (j : ℕ) = n then (1 : ℝ) else 0)) := by
      ext ⟨j, hj⟩
      simp only [Finset.restrict, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single_of_mem j hj]
      · simp [configBasisEval]
      · intro k _ hkj
        split_ifs with h
        · exact absurd h.symm hkj
        · ring
    rw [h_decomp, map_sum]
    simp only [ContinuousLinearMap.map_smul, smul_eq_mul]
    rw [hf_def, map_sum]
    simp only [map_smul, smul_eq_mul, configBasisEval]
    apply Finset.sum_congr rfl
    intro n _
    ring
  -- Step 2: Kolmogorov uniqueness (projective limit)
  let P : ∀ J : Finset ℕ, Measure (∀ j : ↑J, ℝ) :=
    fun J => ν₁.map J.restrict
  have h₁ : MeasureTheory.IsProjectiveLimit ν₁ P :=
    fun _ => rfl
  have h₂ : MeasureTheory.IsProjectiveLimit ν₂ P :=
    fun J => (h_marginals J).symm
  haveI : ∀ J, IsProbabilityMeasure (P J) := fun J =>
    Measure.isProbabilityMeasure_map
      (measurable_pi_lambda _
        (fun _ => measurable_pi_apply _)).aemeasurable
  exact h₁.unique h₂

/-! ## Main theorem -/

/-- **Uniqueness of Gaussian measures from covariance.**

Two centered Gaussian probability measures on `Configuration E` with the same
covariance (second moment structure) must be equal.

The proof combines three ingredients:
1. **MGF matching**: From the hypotheses, for all `f : E`,
   `∫ exp(ω f) dμ₁ = ∫ exp(ω f) dμ₂` (via same covariance).
2. **1D marginals agree**: The MGF equality for all `t • f` shows the 1D marginal
   `(eval_f)_* μ` is `gaussianReal 0 σ²` with `σ² = ∫(ω f)²dμ`, the same for both.
3. **Measure extension**: Equal 1D marginals for all f implies equal finite-dim
   marginals (Cramer-Wold), which determines the pushforward to ℝ^ℕ (Kolmogorov
   uniqueness on Polish space), which pulls back to Configuration E via the
   σ-algebra identity `instMeasurableSpaceConfiguration_eq_comap`. -/
theorem gaussian_measure_unique_of_covariance
    (μ₁ μ₂ : @Measure (Configuration E) instMeasurableSpaceConfiguration)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁_gauss : ∀ (f : E),
      ∫ ω : Configuration E, Real.exp (ω f) ∂μ₁ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ₁))
    (hμ₂_gauss : ∀ (f : E),
      ∫ ω : Configuration E, Real.exp (ω f) ∂μ₂ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ₂))
    (hcov : ∀ (f : E),
      ∫ ω : Configuration E, (ω f) ^ 2 ∂μ₁ =
      ∫ ω : Configuration E, (ω f) ^ 2 ∂μ₂) :
    μ₁ = μ₂ := by
  -- Step 1: All 1D marginals agree (PROVED)
  have h_eval : ∀ f : E,
      μ₁.map (fun ω : Configuration E => ω f) =
      μ₂.map (fun ω : Configuration E => ω f) :=
    eval_map_eq_of_covariance μ₁ μ₂ hμ₁_gauss hμ₂_gauss hcov
  -- Step 2: Pushforward measures to ℝ^ℕ agree
  have h_push_eq := pushforward_eq_of_eval_eq μ₁ μ₂ h_eval
  -- Step 3: Pull back from ℝ^ℕ to Configuration E
  ext s hs
  rw [instMeasurableSpaceConfiguration_eq_comap] at hs
  obtain ⟨T, hT, hpre⟩ := hs
  calc μ₁ s = (μ₁.map configBasisEval) T := by
        rw [Measure.map_apply configBasisEval_measurable hT, ← hpre]
    _ = (μ₂.map configBasisEval) T := by rw [h_push_eq]
    _ = μ₂ s := by
        rw [Measure.map_apply configBasisEval_measurable hT, ← hpre]

end GaussianField

end
