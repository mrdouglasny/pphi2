/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas

# General Results: Functional Analysis

Shared analytic lemmas used across the project.

The Cesàro, Schwartz-integrability, and logarithmic-decay results are close to
Mathlib-facing material. The characteristic-functional lemmas below are more
project-local: they are stated for `Measure (Configuration E)` and therefore
depend on gaussian-field's tempered-distribution configuration space.

## Main results

- `cesaro_set_integral_tendsto` — continuous Cesàro mean convergence
- `schwartz_integrable_norm_rpow` — Schwartz functions have integrable `‖f x‖^p`
- `configuration_expIntegral_re_eq_integral_cos` — real part of `∫ exp(i⟨ω,f⟩)`
- `configuration_expIntegral_im_eq_integral_sin` — imaginary part of `∫ exp(i⟨ω,f⟩)`
- `rp_matrix_trig_identity` — double sum identity for `cos(aᵢ - bⱼ)`
-/

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field
import GaussianField.Construction

open GaussianField
open MeasureTheory

/-! ## Cesàro mean convergence -/

/-- **Continuous Cesàro convergence.**

If h : ℝ → ℝ is measurable, bounded, and h(t) → L as t → +∞, then
the Cesàro average (1/T) ∫₀ᵀ h(t) dt → L as T → +∞.

This is the continuous analogue of Mathlib's `Filter.Tendsto.cesaro`
(for discrete sequences). The proof splits [0,T] = [0,R] ∪ (R,T]
where R is chosen so that |h(t) - L| < ε/2 for t ≥ R. The initial
segment contributes O(R/T) → 0, and the tail contributes ≤ ε/2.

Reference: Rudin, *Real and Complex Analysis*, Exercise 3.14;
Folland, *Real Analysis*, §3.4. -/
theorem cesaro_set_integral_tendsto (h : ℝ → ℝ) (L : ℝ)
    (hm : Measurable h)
    (hb : ∃ M : ℝ, ∀ t, |h t| ≤ M)
    (htend : Filter.Tendsto h Filter.atTop (nhds L)) :
    Filter.Tendsto
      (fun T : ℝ => (1 / T) * ∫ t in Set.Icc (0 : ℝ) T, h t)
      Filter.atTop (nhds L) := by
  obtain ⟨M, hM⟩ := hb
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  -- Integrability on any Icc
  have hint : ∀ a b : ℝ, IntegrableOn h (Set.Icc a b) :=
    fun a b => MeasureTheory.Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
      hm.aestronglyMeasurable (ae_of_all _ fun x => (Real.norm_eq_abs _).symm ▸ hM x)
  have hintg : ∀ a b : ℝ, IntegrableOn (fun t => h t - L) (Set.Icc a b) := by
    intro a b
    exact (hint a b).sub (integrableOn_const (hs := measure_Icc_lt_top.ne))
  rw [Metric.tendsto_atTop] at htend ⊢
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := htend (ε / 2) (half_pos hε)
  set R := max T₀ 0 with hR_def
  have hR_nn : 0 ≤ R := le_max_right _ _
  have hR_T₀ : T₀ ≤ R := le_max_left _ _
  have htail : ∀ t, R ≤ t → |h t - L| < ε / 2 := fun t ht => by
    rw [← Real.dist_eq]; exact hT₀ t (hR_T₀.trans ht)
  have hhl : ∀ t, |h t - L| ≤ M + |L| := fun t =>
    (abs_sub _ _).trans (add_le_add (hM t) le_rfl)
  -- Choose N large enough: max(1, R, 2*(M+|L|)*R/ε + 1)
  set B := 2 * (M + |L|) * R / ε + 1 with hB_def
  refine ⟨max (max 1 R) B, fun T hT => ?_⟩
  have hT_pos : (0 : ℝ) < T := by
    calc (0:ℝ) < 1 := one_pos
      _ ≤ max 1 R := le_max_left _ _
      _ ≤ max (max 1 R) B := le_max_left _ _
      _ ≤ T := hT
  have hT_ne : T ≠ 0 := ne_of_gt hT_pos
  have hB_le_T : B ≤ T := le_max_right _ _ |>.trans hT
  have hT_ge_R : R ≤ T := (le_max_right 1 R |>.trans (le_max_left _ B)).trans hT
  rw [Real.dist_eq]
  -- Key algebraic step: (1/T) * ∫ h - L = (1/T) * ∫ (h - L)
  have hvol : (volume (Set.Icc (0 : ℝ) T)).toReal = T := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ T - 0)]; ring
  -- ∫ h = ∫ (h - L) + L * T
  have hint_split : ∫ t in Set.Icc (0:ℝ) T, h t =
      (∫ t in Set.Icc (0:ℝ) T, (fun t => h t - L) t) + L * T := by
    have heq : ∫ t in Set.Icc (0:ℝ) T, h t =
        (∫ t in Set.Icc (0:ℝ) T, (fun t => h t - L) t) +
        (∫ t in Set.Icc (0:ℝ) T, (fun _ => L) t) := by
      rw [← integral_add (hintg 0 T) (integrableOn_const (hs := measure_Icc_lt_top.ne))]
      congr 1; ext t; ring
    rw [heq, MeasureTheory.setIntegral_const, Measure.real, hvol, smul_eq_mul, mul_comm L T]
  have hrewrite : (1 / T * ∫ t in Set.Icc (0:ℝ) T, h t) - L =
      1 / T * (∫ t in Set.Icc (0:ℝ) T, (fun t => h t - L) t) := by
    rw [hint_split, mul_add, mul_comm (1/T) (L * T)]
    have : 1 / T * (L * T) = L := by field_simp
    linarith
  rw [hrewrite, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / T)]
  -- Now bound |∫ (h - L)| by splitting [0,T] = [0,R] ∪ (R,T]
  -- First bound: |∫ (h - L)| ≤ ∫ |h - L|
  have norm_bound : |∫ t in Set.Icc (0:ℝ) T, (fun t => h t - L) t| ≤
      ∫ t in Set.Icc (0:ℝ) T, |h t - L| := by
    have h1 := MeasureTheory.norm_integral_le_integral_norm
      (f := fun t => h t - L) (μ := volume.restrict (Set.Icc 0 T))
    simp only [Real.norm_eq_abs] at h1
    exact h1
  -- Split the integral of |h - L|
  have hsplit : Set.Icc (0:ℝ) T = Set.Icc 0 R ∪ Set.Ioc R T := by
    ext x; simp only [Set.mem_Icc, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro ⟨hx0, hxT⟩
      by_cases hxR : x ≤ R
      · exact Or.inl ⟨hx0, hxR⟩
      · exact Or.inr ⟨lt_of_not_ge hxR, hxT⟩
    · rintro (⟨hx0, hxR⟩ | ⟨hxR, hxT⟩)
      · exact ⟨hx0, hxR.trans hT_ge_R⟩
      · exact ⟨hR_nn.trans hxR.le, hxT⟩
  have hd : Disjoint (Set.Icc 0 R) (Set.Ioc R T) :=
    Set.disjoint_left.mpr fun x ⟨_, hxR⟩ ⟨hRx, _⟩ => not_lt.mpr hxR hRx
  have hint_abs1 : IntegrableOn (fun t => |h t - L|) (Set.Icc 0 R) :=
    MeasureTheory.Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
      (((hm.sub measurable_const).norm.aestronglyMeasurable))
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_abs]; exact hhl x)
  have hint_abs2 : IntegrableOn (fun t => |h t - L|) (Set.Ioc R T) :=
    MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (((hm.sub measurable_const).norm.aestronglyMeasurable))
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_abs]; exact hhl x)
  have integral_split : ∫ t in Set.Icc (0:ℝ) T, |h t - L| =
      (∫ t in Set.Icc 0 R, |h t - L|) + (∫ t in Set.Ioc R T, |h t - L|) := by
    rw [hsplit]; exact MeasureTheory.setIntegral_union hd measurableSet_Ioc hint_abs1 hint_abs2
  -- Bound part 1: ∫₀ᴿ |h - L| ≤ (M + |L|) * R
  have part1 : ∫ t in Set.Icc 0 R, |h t - L| ≤ (M + |L|) * R := by
    have hR_vol : (volume (Set.Icc (0:ℝ) R)).toReal = R := by
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ R - 0)]; ring
    calc ∫ t in Set.Icc 0 R, |h t - L|
        ≤ ‖∫ t in Set.Icc 0 R, |h t - L|‖ := le_abs_self _
      _ ≤ (M + |L|) * (volume (Set.Icc (0:ℝ) R)).toReal :=
          MeasureTheory.norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top
            fun x _ => by rw [Real.norm_eq_abs, abs_abs]; exact hhl x
      _ = (M + |L|) * R := by rw [hR_vol]
  -- Bound part 2: ∫ᴿᵀ |h - L| ≤ (ε/2) * T
  have part2 : ∫ t in Set.Ioc R T, |h t - L| ≤ ε / 2 * T := by
    calc ∫ t in Set.Ioc R T, |h t - L|
        ≤ ∫ t in Set.Ioc R T, (ε / 2) := by
          apply MeasureTheory.setIntegral_mono_on hint_abs2
            (integrableOn_const (hs := measure_Ioc_lt_top.ne))
            measurableSet_Ioc fun t ht => (htail t ht.1.le).le
      _ = ε / 2 * (volume (Set.Ioc R T)).toReal := by
          rw [MeasureTheory.setIntegral_const, Measure.real, smul_eq_mul, mul_comm]
      _ ≤ ε / 2 * T := by
          gcongr
          rw [Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : 0 ≤ T - R)]
          linarith
  -- Combine
  have integral_bound : ∫ t in Set.Icc (0:ℝ) T, |h t - L| ≤ (M + |L|) * R + ε / 2 * T := by
    rw [integral_split]; linarith
  -- Final estimate
  have head_small : (M + |L|) * R / T < ε / 2 := by
    rw [div_lt_iff₀ hT_pos]
    have hBT := hB_le_T
    have : 2 * (M + |L|) * R / ε ≤ T - 1 := by linarith
    have : 2 * (M + |L|) * R ≤ (T - 1) * ε := by
      rwa [div_le_iff₀ hε] at this
    linarith
  calc 1 / T * |∫ t in Set.Icc (0:ℝ) T, (fun t => h t - L) t|
      ≤ 1 / T * ∫ t in Set.Icc (0:ℝ) T, |h t - L| := by gcongr
    _ ≤ 1 / T * ((M + |L|) * R + ε / 2 * T) := by gcongr
    _ < ε := by
        have heq : 1 / T * ((M + |L|) * R + ε / 2 * T) = (M + |L|) * R / T + ε / 2 := by
          field_simp
        linarith

/-! ## Logarithmic decay near zero -/

/-- If `aₙ > 0`, `aₙ ≤ 1`, and `aₙ → 0`, then
`aₙ (1 + |log aₙ|)^p → 0` for every natural `p`.

This packages the standard fact that polynomial decay at `0⁺` dominates any
fixed power of `|log a|`. It is useful when RG-irrelevant factors `a^m`
(`m > 0`) are accompanied by at most polynomial logarithmic corrections. -/
theorem tendsto_zero_mul_one_add_abs_log_pow
    (a : ℕ → ℝ) (ha_tend : Filter.Tendsto a Filter.atTop (nhds 0))
    (ha_pos : ∀ n, 0 < a n) (ha_le : ∀ n, a n ≤ 1) (p : ℕ) :
    Filter.Tendsto
      (fun n => a n * (1 + |Real.log (a n)|) ^ p)
      Filter.atTop (nhds 0) := by
  have ha_within : Filter.Tendsto a Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ha_tend ?_
    exact Filter.Eventually.of_forall fun n => ha_pos n
  have h_inv_fun :
      Filter.Tendsto (fun x : ℝ => x⁻¹) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
    apply tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop
    simpa using
      (Filter.tendsto_id : Filter.Tendsto (fun x : ℝ => x) Filter.atTop Filter.atTop)
  have h_inv : Filter.Tendsto (fun n => (a n)⁻¹) Filter.atTop Filter.atTop :=
    h_inv_fun.comp ha_within
  have h_log_div :
      Filter.Tendsto (fun x : ℝ => Real.log x ^ p / (1 * x + 0)) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 p one_ne_zero
  have h_a_logpow :
      Filter.Tendsto (fun n => a n * |Real.log (a n)| ^ p) Filter.atTop (nhds 0) := by
    have h_raw :
        Filter.Tendsto
          (fun n => Real.log ((a n)⁻¹) ^ p / (1 * (a n)⁻¹ + 0))
          Filter.atTop (nhds 0) :=
      h_log_div.comp h_inv
    refine h_raw.congr' (Filter.Eventually.of_forall fun n => ?_)
    have hlog_abs : Real.log ((a n)⁻¹) = |Real.log (a n)| := by
      rw [Real.log_inv]
      have hnonpos : Real.log (a n) ≤ 0 :=
        Real.log_nonpos (le_of_lt (ha_pos n)) (ha_le n)
      rw [abs_of_nonpos hnonpos]
    calc
      Real.log ((a n)⁻¹) ^ p / (1 * (a n)⁻¹ + 0)
          = Real.log ((a n)⁻¹) ^ p / (a n)⁻¹ := by ring
      _ = a n * Real.log ((a n)⁻¹) ^ p := by
          rw [div_eq_mul_inv, inv_inv, mul_comm]
      _ = a n * |Real.log (a n)| ^ p := by rw [hlog_abs]
  have h_log_atTop : Filter.Tendsto (fun n => Real.log ((a n)⁻¹)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp h_inv
  have h_log_large : ∀ᶠ n in Filter.atTop, 1 ≤ |Real.log (a n)| := by
    filter_upwards [Filter.tendsto_atTop.1 h_log_atTop 1] with n hn
    have hlog_abs : Real.log ((a n)⁻¹) = |Real.log (a n)| := by
      rw [Real.log_inv]
      have hnonpos : Real.log (a n) ≤ 0 :=
        Real.log_nonpos (le_of_lt (ha_pos n)) (ha_le n)
      rw [abs_of_nonpos hnonpos]
    simpa [hlog_abs] using hn
  have h_upper :
      Filter.Tendsto
        (fun n => (2 : ℝ) ^ p * (a n * |Real.log (a n)| ^ p))
        Filter.atTop (nhds 0) := by
    simpa [zero_mul] using h_a_logpow.const_mul ((2 : ℝ) ^ p)
  have h_bound :
      ∀ᶠ n in Filter.atTop,
        a n * (1 + |Real.log (a n)|) ^ p ≤
          (2 : ℝ) ^ p * (a n * |Real.log (a n)| ^ p) := by
    filter_upwards [h_log_large] with n hn
    have ha_nonneg : 0 ≤ a n := le_of_lt (ha_pos n)
    have hpow :
        (1 + |Real.log (a n)|) ^ p ≤ (2 * |Real.log (a n)|) ^ p := by
      gcongr
      nlinarith
    calc
      a n * (1 + |Real.log (a n)|) ^ p
          ≤ a n * (2 * |Real.log (a n)|) ^ p := by
            gcongr
      _ = (2 : ℝ) ^ p * (a n * |Real.log (a n)| ^ p) := by
            ring_nf
  have h_nonneg : ∀ᶠ n in Filter.atTop, 0 ≤ a n * (1 + |Real.log (a n)|) ^ p := by
    exact Filter.Eventually.of_forall fun n => by
      refine mul_nonneg (le_of_lt (ha_pos n)) ?_
      positivity
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_upper h_nonneg h_bound

/-- If `aₙ > 0`, `aₙ ≤ 1`, and `aₙ → 0`, then
`aₙ^m (1 + |log aₙ|)^p → 0` for every natural `p` and every `m ≥ 1`. -/
theorem tendsto_zero_pow_mul_one_add_abs_log_pow
    (a : ℕ → ℝ) (ha_tend : Filter.Tendsto a Filter.atTop (nhds 0))
    (ha_pos : ∀ n, 0 < a n) (ha_le : ∀ n, a n ≤ 1)
    (m p : ℕ) (hm : 1 ≤ m) :
    Filter.Tendsto
      (fun n => a n ^ m * (1 + |Real.log (a n)|) ^ p)
      Filter.atTop (nhds 0) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  cases k with
  | zero =>
      simpa using tendsto_zero_mul_one_add_abs_log_pow a ha_tend ha_pos ha_le p
  | succ k =>
      have hpow :
          Filter.Tendsto (fun n => a n ^ Nat.succ k) Filter.atTop (nhds 0) := by
        simpa using ha_tend.pow (Nat.succ k)
      have hone := tendsto_zero_mul_one_add_abs_log_pow a ha_tend ha_pos ha_le p
      have hmul :
          Filter.Tendsto
            (fun x => a x ^ Nat.succ k * (a x * (1 + |Real.log (a x)|) ^ p))
            Filter.atTop (nhds 0) := by
        simpa [zero_mul] using hpow.mul hone
      have hmul' :
          Filter.Tendsto
            (fun n => a n ^ Nat.succ (Nat.succ k) * (1 + |Real.log (a n)|) ^ p)
            Filter.atTop (nhds 0) := by
        convert hmul using 1
        ext n
        rw [pow_succ, mul_assoc]
      simpa [Nat.add_comm, Nat.add_left_comm] using hmul'

/-- Square-case corollary of `tendsto_zero_pow_mul_one_add_abs_log_pow`. -/
theorem tendsto_zero_sq_mul_one_add_abs_log_pow
    (a : ℕ → ℝ) (ha_tend : Filter.Tendsto a Filter.atTop (nhds 0))
    (ha_pos : ∀ n, 0 < a n) (ha_le : ∀ n, a n ≤ 1) (p : ℕ) :
    Filter.Tendsto
      (fun n => a n ^ 2 * (1 + |Real.log (a n)|) ^ p)
      Filter.atTop (nhds 0) := by
  simpa using tendsto_zero_pow_mul_one_add_abs_log_pow a ha_tend ha_pos ha_le 2 p (by norm_num)

/-! ## Schwartz integrability -/

/-- Schwartz functions have integrable `‖f x‖ ^ p` for any `p > 0`.

This is a consequence of `SchwartzMap.eLpNorm_lt_top` and `integrable_norm_rpow_iff`.
Useful for showing that Schwartz functions lie in all Lᵖ spaces. -/
lemma schwartz_integrable_norm_rpow {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    [OpensMeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [SecondCountableTopologyEither E F]
    [Measure.HasTemperateGrowth (volume : Measure E)]
    (f : SchwartzMap E F) {p : ℝ} (hp : 0 < p) :
    Integrable (fun x => ‖f x‖ ^ p) volume := by
  have hq : ENNReal.ofReal p ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le.mpr hp]
  have hq' : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have key : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (le_of_lt hp)
  have := (MeasureTheory.integrable_norm_rpow_iff
    (SchwartzMap.continuous f).aestronglyMeasurable hq hq').mpr
    ⟨(SchwartzMap.continuous f).aestronglyMeasurable, SchwartzMap.eLpNorm_lt_top _ _⟩
  simp only [key] at this
  exact this

/-! ## Characteristic-functional trigonometric decompositions -/

/-- The oscillatory characteristic integrand `exp(i⟨ω,f⟩)` is integrable for any finite
measure on configurations, since its norm is identically `1`. -/
theorem configuration_cexp_eval_integrable {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (μ : Measure (Configuration E)) [IsFiniteMeasure μ] (f : E) :
    Integrable (fun ω : Configuration E => Complex.exp (Complex.I * ↑(ω f))) μ := by
  apply (integrable_const (1 : ℂ)).mono
  · exact ((Complex.measurable_ofReal.comp (configuration_eval_measurable f)).const_mul Complex.I
      |>.cexp).aestronglyMeasurable
  · apply ae_of_all
    intro ω
    simp only [norm_one]
    rw [show Complex.I * ↑(ω f) = ↑(ω f) * Complex.I from mul_comm _ _]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I (ω f))

/-- The real part of the characteristic integral is the cosine moment. -/
theorem configuration_expIntegral_re_eq_integral_cos {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (μ : Measure (Configuration E)) [IsFiniteMeasure μ] (f : E) :
    (∫ ω : Configuration E, Complex.exp (Complex.I * ↑(ω f)) ∂μ).re =
      ∫ ω : Configuration E, Real.cos (ω f) ∂μ := by
  rw [show (∫ ω : Configuration E, Complex.exp (Complex.I * ↑(ω f)) ∂μ).re =
    Complex.reCLM (∫ ω : Configuration E, Complex.exp (Complex.I * ↑(ω f)) ∂μ) from rfl]
  rw [← ContinuousLinearMap.integral_comp_comm Complex.reCLM
    (configuration_cexp_eval_integrable μ f)]
  congr 1 with ω
  simp only [Complex.reCLM_apply, mul_comm Complex.I, Complex.exp_mul_I,
    Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.sin_ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  exact Complex.cos_ofReal_re (ω f)

/-- The imaginary part of the characteristic integral is the sine moment. -/
theorem configuration_expIntegral_im_eq_integral_sin {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (μ : Measure (Configuration E)) [IsFiniteMeasure μ] (f : E) :
    (∫ ω : Configuration E, Complex.exp (Complex.I * ↑(ω f)) ∂μ).im =
      ∫ ω : Configuration E, Real.sin (ω f) ∂μ := by
  rw [show (∫ ω : Configuration E, Complex.exp (Complex.I * ↑(ω f)) ∂μ).im =
    Complex.imCLM (∫ ω : Configuration E, Complex.exp (Complex.I * ↑(ω f)) ∂μ) from rfl]
  rw [← ContinuousLinearMap.integral_comp_comm Complex.imCLM
    (configuration_cexp_eval_integrable μ f)]
  congr 1 with ω
  simp only [Complex.imCLM_apply, mul_comm Complex.I, Complex.exp_mul_I,
    Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  ring

/-- The pointwise difference of characteristic-function integrands attached to two sources. -/
noncomputable def configuration_cexp_eval_sub_integrand {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (f g : E) : Configuration E → ℂ :=
  fun ω => Complex.exp (Complex.I * ↑(ω g)) - Complex.exp (Complex.I * ↑(ω f))

/-- The pointwise norm of the characteristic-function integrand difference attached to two
sources. -/
noncomputable def configuration_cexp_eval_dist {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (f g : E) : Configuration E → ℝ :=
  fun ω => ‖configuration_cexp_eval_sub_integrand f g ω‖

/-- The difference of characteristic integrals is controlled by the integral of the pointwise
norm defect. -/
theorem norm_configuration_expIntegral_sub_le_integral_cexp_eval_dist {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (μ : Measure (Configuration E)) [IsFiniteMeasure μ] (f g : E) :
    ‖(∫ ω : Configuration E, Complex.exp (Complex.I * ↑(ω g)) ∂μ) -
        (∫ ω : Configuration E, Complex.exp (Complex.I * ↑(ω f)) ∂μ)‖
      ≤ ∫ ω : Configuration E, configuration_cexp_eval_dist f g ω ∂μ := by
  have hg :
      Integrable (fun ω : Configuration E => Complex.exp (Complex.I * ↑(ω g))) μ :=
    configuration_cexp_eval_integrable μ g
  have hf :
      Integrable (fun ω : Configuration E => Complex.exp (Complex.I * ↑(ω f))) μ :=
    configuration_cexp_eval_integrable μ f
  have hsub :
      ∫ ω : Configuration E, configuration_cexp_eval_sub_integrand f g ω ∂μ =
        (∫ ω : Configuration E, Complex.exp (Complex.I * ↑(ω g)) ∂μ) -
          (∫ ω : Configuration E, Complex.exp (Complex.I * ↑(ω f)) ∂μ) := by
    simp [configuration_cexp_eval_sub_integrand, integral_sub hg hf]
  calc
    ‖(∫ ω : Configuration E, Complex.exp (Complex.I * ↑(ω g)) ∂μ) -
        (∫ ω : Configuration E, Complex.exp (Complex.I * ↑(ω f)) ∂μ)‖
        = ‖∫ ω : Configuration E, configuration_cexp_eval_sub_integrand f g ω ∂μ‖ := by
          rw [hsub]
    _ ≤ ∫ ω : Configuration E, ‖configuration_cexp_eval_sub_integrand f g ω‖ ∂μ :=
          norm_integral_le_integral_norm _
    _ = ∫ ω : Configuration E, configuration_cexp_eval_dist f g ω ∂μ := rfl

/-! ## Trigonometric identities -/

/-- **Double-sum trigonometric identity for reflection positivity.**

For any reals `aᵢ`, `bⱼ` and coefficients `cᵢ`, `cⱼ`:
`Σᵢⱼ cᵢ cⱼ cos(aᵢ - bⱼ) = (Σ cᵢ cos aᵢ)(Σ cⱼ cos bⱼ) + (Σ cᵢ sin aᵢ)(Σ cⱼ sin bⱼ)`

This follows from `cos(a - b) = cos a · cos b + sin a · sin b`
and bilinearity of the double sum. -/
theorem rp_matrix_trig_identity {n : ℕ} (c : Fin n → ℝ)
    (a b : Fin n → ℝ) :
    ∑ i, ∑ j, c i * c j * Real.cos (a i - b j) =
    (∑ i, c i * Real.cos (a i)) * (∑ j, c j * Real.cos (b j)) +
    (∑ i, c i * Real.sin (a i)) * (∑ j, c j * Real.sin (b j)) := by
  -- Step 1: Expand cos(a - b) = cos(a)cos(b) + sin(a)sin(b) in each term
  have key : ∀ i j, c i * c j * Real.cos (a i - b j) =
      c i * Real.cos (a i) * (c j * Real.cos (b j)) +
      c i * Real.sin (a i) * (c j * Real.sin (b j)) := by
    intros; rw [Real.cos_sub]; ring
  simp_rw [key]
  -- Step 2: Split double sum of (A + B) into double sum of A + double sum of B
  simp_rw [Finset.sum_add_distrib]
  congr 1
  · -- cos·cos part: collapse double sum into product of sums
    simp_rw [← Finset.mul_sum (f := fun j => c j * Real.cos (b j))]
    exact (Finset.sum_mul ..).symm
  · -- sin·sin part: collapse double sum into product of sums
    simp_rw [← Finset.mul_sum (f := fun j => c j * Real.sin (b j))]
    exact (Finset.sum_mul ..).symm
