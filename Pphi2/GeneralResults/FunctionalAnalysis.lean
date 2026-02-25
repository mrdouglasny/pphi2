/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# General Results: Functional Analysis

Pure functional analysis results not specific to the P(Φ)₂ project.
Candidates for upstreaming to Mathlib.

## Main results

- `cesaro_set_integral_tendsto` — continuous Cesàro mean convergence
- `schwartz_integrable_norm_rpow` — Schwartz functions have integrable `‖f x‖^p`
- `rp_matrix_trig_identity` — double sum identity for `cos(aᵢ - bⱼ)`
-/

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

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
