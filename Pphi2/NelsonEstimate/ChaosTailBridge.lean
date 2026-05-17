/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chaos → One-Sided Tail Bridge

`polynomial_chaos_concentration` (Janson 5.10, in gaussian-hilbert)
gives a two-sided tail bound:
`μ{|F| > λ‖F‖_2} ≤ 2 exp(-c_d · λ^{2/d})`.

The bridge derivation needs a **one-sided** tail bound on `{F ≤ -t}`,
parametrized by an `L²`-norm upper bound `K` on `F` (rather than the
intrinsic `‖F‖_2`). This file provides that translation.

## Main result

* `chaos_neg_tail_bound`: from `F ∈ wienerChaosLE n d` and `‖F‖_2 ≤ K`,
  conclude
  `μ{ω | F ω ≤ -t} ≤ 2 · ENNReal.ofReal (exp (-c_d · (t/(2K))^{2/d}))`
  for a universal `c_d > 0` (depending only on `d`).

This is the key lemma between gaussian-hilbert's
`polynomial_chaos_concentration` and the abstract bridge in
`BridgeFromTail.lean`.

## References

- pphi2/docs/polynomial-chaos-exp-moment-bridge-proof-plan.md.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import GaussianHilbert.PolynomialChaosConcentration

noncomputable section

namespace Pphi2.ChaosTailBridge

open MeasureTheory GaussianHilbert

/-- **One-sided tail bound from `polynomial_chaos_concentration` plus
an `L²` upper bound.**

For `F ∈ wienerChaosLE n d` with `‖F‖_2 ≤ K`, the negative tail
satisfies
$$
\mu\{\omega \mid F(\omega) \le -t\} \;\le\;
  2 \exp\bigl(-c_d \cdot (t/(2K))^{2/d}\bigr)
$$
for `t > 0`, with `c_d` the universal constant from
`polynomial_chaos_concentration`.

**Proof:** `{F ≤ -t} ⊆ {|F| > t/2}` (since `F ≤ -t < 0` and
`t > 0` imply `|F| ≥ t > t/2`). Applying
`polynomial_chaos_concentration` with `λ = t/(2‖F‖_2)`:
* `λ · ‖F‖_2 = t/2`,
* `λ ≥ t/(2K)` (since `‖F‖_2 ≤ K`),
* `exp(-c_d λ^{2/d}) ≤ exp(-c_d (t/(2K))^{2/d})` (`exp` monotone,
  `-λ^{2/d}` decreasing in `λ`).

Edge case: if `‖F‖_2 = 0`, then `F =ᵐ 0`, so the set is null. -/
theorem chaos_neg_tail_bound (n d : ℕ) (hd : 1 ≤ d) :
    ∃ c_d : ℝ, 0 < c_d ∧
      ∀ (F : Lp ℝ 2 (stdGaussianFin n)), F ∈ wienerChaosLE n d →
      ∀ (K : ℝ), 0 < K → ‖F‖ ≤ K →
      ∀ (t : ℝ), 0 < t →
        (stdGaussianFin n) {ω | (F : (Fin n → ℝ) → ℝ) ω ≤ -t} ≤
          2 * ENNReal.ofReal
            (Real.exp (-c_d * (t / (2 * K)) ^ ((2 : ℝ) / d))) := by
  obtain ⟨c_d, hc_d_pos, h_conc⟩ := polynomial_chaos_concentration n d hd
  refine ⟨c_d, hc_d_pos, ?_⟩
  intro F hF K hK_pos hF_norm_le t ht
  -- Step 1: F ≤ -t ⇒ |F| > t/2 (since t > 0 and F ≤ -t < 0).
  have h_subset :
      {ω | (F : (Fin n → ℝ) → ℝ) ω ≤ -t} ⊆
        {ω | t/2 < |((F : (Fin n → ℝ) → ℝ) ω)|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have h_neg : (F : (Fin n → ℝ) → ℝ) ω ≤ -t := hω
    have h_abs : t ≤ |((F : (Fin n → ℝ) → ℝ) ω)| := by
      rw [abs_of_nonpos (by linarith : (F : (Fin n → ℝ) → ℝ) ω ≤ 0)]
      linarith
    linarith
  refine le_trans (measure_mono h_subset) ?_
  -- Step 2: Apply concentration.
  by_cases hF_norm_zero : ‖F‖ = 0
  · -- F = 0 in Lp ⇒ F =ᵐ 0 ⇒ {|F| > t/2} is null.
    have h_two_pos : (0 : ENNReal) < 2 := by norm_num
    have hF_zero : F = 0 := (Lp.norm_eq_zero_iff h_two_pos).mp hF_norm_zero
    have hF_ae : (F : (Fin n → ℝ) → ℝ) =ᵐ[stdGaussianFin n] 0 := by
      rw [hF_zero]; exact Lp.coeFn_zero ℝ 2 _
    have h_set_null :
        (stdGaussianFin n)
            {ω | t/2 < |((F : (Fin n → ℝ) → ℝ) ω)|} = 0 := by
      apply measure_mono_null _ (ae_iff.mp hF_ae)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have : (F : (Fin n → ℝ) → ℝ) ω ≠ 0 := by
        intro h_eq
        rw [h_eq, abs_zero] at hω
        linarith
      exact this
    rw [h_set_null]; exact bot_le
  have hF_norm_ne : ‖F‖ ≠ 0 := hF_norm_zero
  have hF_norm_pos : 0 < ‖F‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hF_norm_ne)
  -- Set λ = t/(2‖F‖) so that λ · ‖F‖ = t/2.
  set lam : ℝ := t / (2 * ‖F‖) with hlam_def
  have hlam_pos : 0 < lam := by
    apply div_pos ht
    linarith [hF_norm_pos]
  have h_lam_norm_eq : lam * ‖F‖ = t / 2 := by
    rw [hlam_def]
    field_simp
  -- Apply concentration at this λ.
  have h_conc_F := h_conc F hF lam hlam_pos
  -- Rewrite the set: {lam·‖F‖ < |F|} = {t/2 < |F|}.
  have h_set_eq :
      {ω | lam * ‖F‖ < |((F : (Fin n → ℝ) → ℝ) ω)|} =
        {ω | t / 2 < |((F : (Fin n → ℝ) → ℝ) ω)|} := by
    ext ω
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, h_lam_norm_eq]
  rw [h_set_eq] at h_conc_F
  refine le_trans h_conc_F ?_
  -- Final step: c_d · λ^{2/d} ≥ c_d · (t/(2K))^{2/d}, so the bound
  -- gets weaker (RHS larger).
  refine mul_le_mul_right ?_ _
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  -- -c_d · λ^{2/d} ≤ -c_d · (t/(2K))^{2/d} ⟺ c_d · (t/(2K))^{2/d} ≤ c_d · λ^{2/d}.
  have h_lam_lb : t / (2 * K) ≤ lam := by
    rw [hlam_def]
    apply div_le_div_of_nonneg_left ht.le (by positivity)
    linarith
  have h_pow_le :
      (t / (2 * K)) ^ ((2 : ℝ) / d) ≤ lam ^ ((2 : ℝ) / d) := by
    apply Real.rpow_le_rpow
    · positivity
    · exact h_lam_lb
    · have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
      positivity
  nlinarith [hc_d_pos]

/-- The explicit dimension-only constant used in the Janson/Bonami-Nelson
tail bound. This is the same witness as in
`GaussianHilbert.polynomial_chaos_concentration`; it depends only on the
chaos degree `d`, not on the ambient Gaussian dimension `n`. -/
def chaosTailConstant (d : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (1 / (Real.exp 1 * ((d : ℝ) + 1))) ^ ((2 : ℝ) / d)

theorem chaosTailConstant_pos (d : ℕ) (hd : 1 ≤ d) :
    0 < chaosTailConstant d := by
  dsimp [chaosTailConstant]
  have hd_pos : (0 : ℝ) < d := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hd)
  positivity

private theorem eLpNorm_two_eq_ofReal_norm {n : ℕ}
    (F : Lp ℝ 2 (stdGaussianFin n)) :
    eLpNorm (F : (Fin n → ℝ) → ℝ) 2 (stdGaussianFin n) = ENNReal.ofReal ‖F‖ := by
  rw [Lp.norm_def]
  exact (ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F)).symm

private theorem one_le_two_mul_exp_neg_half_ennreal {t : ℝ} (ht : t < 1) :
    (1 : ENNReal) ≤ 2 * ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) * t)) := by
  have hhalf_log_two : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have htlog : (1 / 2 : ℝ) * t < Real.log 2 := by
    have hhalf_t : (1 / 2 : ℝ) * t < 1 / 2 := by
      linarith
    exact lt_trans hhalf_t hhalf_log_two
  have hneg : -Real.log 2 < -((1 / 2 : ℝ) * t) := by
    linarith
  have hexp : Real.exp (-Real.log 2) < Real.exp (-((1 / 2 : ℝ) * t)) := by
    exact (Real.exp_lt_exp).2 hneg
  have hhalf : (1 / 2 : ℝ) < Real.exp (-((1 / 2 : ℝ) * t)) := by
    have hhalf_eq : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      rw [← Real.log_inv]
      norm_num
      rw [Real.exp_log]
      norm_num
    rw [hhalf_eq] at hexp
    exact hexp
  have hreal : (1 : ℝ) ≤ 2 * Real.exp (-(1 / 2 : ℝ) * t) := by
    have hmul : (1 : ℝ) < 2 * Real.exp (-(1 / 2 : ℝ) * t) := by
      have := mul_lt_mul_of_pos_left hhalf (show (0 : ℝ) < 2 by norm_num)
      simpa using this
    exact hmul.le
  rw [← ENNReal.ofReal_one, show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul' (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal hreal

private theorem exp_neg_one_add_le_two_mul_exp_neg_half {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-(1 + t)) ≤ 2 * Real.exp (-(1 / 2 : ℝ) * t) := by
  have hexp_one : Real.exp (-1 : ℝ) < 1 / 2 := Real.exp_neg_one_lt_half
  have hexp_t : Real.exp (-t) ≤ Real.exp (-(1 / 2 : ℝ) * t) := by
    apply (Real.exp_le_exp).2
    linarith
  calc
    Real.exp (-(1 + t)) = Real.exp (-1) * Real.exp (-t) := by
      rw [show -(1 + t) = -1 + -t by ring, Real.exp_add]
    _ ≤ (1 / 2) * Real.exp (-(1 / 2 : ℝ) * t) := by
      gcongr
    _ ≤ 2 * Real.exp (-(1 / 2 : ℝ) * t) := by
      have hpos : 0 < Real.exp (-(1 / 2 : ℝ) * t) := Real.exp_pos _
      nlinarith

private theorem markov_bonami_bound_explicit {n d : ℕ}
    (F : Lp ℝ 2 (stdGaussianFin n)) (hF : F ∈ wienerChaosLE n d)
    (lam p A : ℝ) (hlam : 0 < lam) (hFnorm : 0 < ‖F‖)
    (hA : A = ((d : ℝ) + 1) * (p - 1) ^ ((d : ℝ) / 2)) (hp : 2 ≤ p) :
    (stdGaussianFin n) {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|} ≤
      ENNReal.ofReal ((A / lam) ^ p) := by
  have hp_nonneg : 0 ≤ p := by
    linarith
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
    exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := by
    simp
  have hε_ne_zero : ENNReal.ofReal (lam * ‖F‖) ≠ 0 := by
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hmarkov :
      (stdGaussianFin n) {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|} ≤
        (ENNReal.ofReal (lam * ‖F‖))⁻¹ ^ p *
          eLpNorm (F : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n) ^ p := by
    calc
      (stdGaussianFin n) {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|}
        ≤ (stdGaussianFin n) {x | ENNReal.ofReal (lam * ‖F‖) ≤ ‖((F : (Fin n → ℝ) → ℝ) x)‖ₑ} := by
            refine measure_mono ?_
            intro x hx
            simp only [Set.mem_setOf_eq, Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal hx.le
      _ ≤ (ENNReal.ofReal (lam * ‖F‖))⁻¹ ^ p *
          eLpNorm (F : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n) ^ p := by
            simpa [ENNReal.toReal_ofReal hp_nonneg] using
              (MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm (stdGaussianFin n)
                hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable F) hε_ne_zero (by simp))
  have hbn := GaussianHilbert.bonami_nelson_chaosLE n d F hF p hp
  have hconst_nonneg : 0 ≤ A := by
    rw [hA]
    have hp1 : 0 ≤ p - 1 := by
      linarith
    positivity
  have hbn' :
      eLpNorm (F : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n) ≤
        ENNReal.ofReal (A * ‖F‖) := by
    rw [← hA] at hbn
    rw [eLpNorm_two_eq_ofReal_norm F, ← ENNReal.ofReal_mul hconst_nonneg] at hbn
    simpa [mul_assoc] using hbn
  have htail :
      (ENNReal.ofReal (lam * ‖F‖))⁻¹ ^ p *
        eLpNorm (F : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n) ^ p ≤
      ENNReal.ofReal ((A / lam) ^ p) := by
    calc
      (ENNReal.ofReal (lam * ‖F‖))⁻¹ ^ p *
          eLpNorm (F : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n) ^ p
        ≤ (ENNReal.ofReal (lam * ‖F‖))⁻¹ ^ p * (ENNReal.ofReal (A * ‖F‖)) ^ p := by
            gcongr
      _ = ENNReal.ofReal ((A / lam) ^ p) := by
        have hmul_pos : 0 < lam * ‖F‖ := mul_pos hlam hFnorm
        have hA_mul_nonneg : 0 ≤ A * ‖F‖ := mul_nonneg hconst_nonneg hFnorm.le
        have hinv_nonneg : 0 ≤ (lam * ‖F‖)⁻¹ := by positivity
        have hrpow_nonneg : 0 ≤ ((lam * ‖F‖)⁻¹) ^ p := by positivity
        rw [← ENNReal.ofReal_inv_of_pos hmul_pos,
          ENNReal.ofReal_rpow_of_nonneg hinv_nonneg hp_nonneg,
          ENNReal.ofReal_rpow_of_nonneg hA_mul_nonneg hp_nonneg,
          ← ENNReal.ofReal_mul hrpow_nonneg]
        congr 1
        rw [← Real.mul_rpow hinv_nonneg hA_mul_nonneg]
        congr 1
        have hcancel : lam * ‖F‖ ≠ 0 := by positivity
        field_simp [hcancel]
  exact hmarkov.trans htail

/-- Explicit Janson/Bonami-Nelson concentration with a dimension-only constant.

This repackages `GaussianHilbert.polynomial_chaos_concentration` in the form
needed by the rough-error bridge: the witness is fixed to
`chaosTailConstant d`, so downstream theorems can stay uniform in the ambient
finite Gaussian dimension. -/
theorem polynomial_chaos_concentration_explicit (n d : ℕ) (hd : 1 ≤ d) :
    ∀ (F : Lp ℝ 2 (stdGaussianFin n)),
      F ∈ wienerChaosLE n d →
      ∀ (lam : ℝ), 0 < lam →
        (stdGaussianFin n) {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|} ≤
          2 * ENNReal.ofReal
            (Real.exp (-(chaosTailConstant d) * lam ^ ((2 : ℝ) / d))) := by
  let L0 : ℝ := Real.exp 1 * ((d : ℝ) + 1)
  let c_d : ℝ := chaosTailConstant d
  intro F hF lam hlam
  have hd_pos : (0 : ℝ) < d := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hd)
  have hd_ne : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le zero_lt_one hd))
  have hL0_pos : 0 < L0 := by
    dsimp [L0]
    positivity
  by_cases hnorm_zero : ‖F‖ = 0
  · have hF_zero : F = 0 :=
      (MeasureTheory.Lp.norm_eq_zero_iff (by positivity : (0 : ENNReal) < 2)).1 hnorm_zero
    cases hF_zero
    have hzero :
        (stdGaussianFin n)
          {x | lam * ‖(0 : Lp ℝ 2 (stdGaussianFin n))‖ <
            |((0 : Lp ℝ 2 (stdGaussianFin n)) : (Fin n → ℝ) → ℝ) x|} = 0 := by
      rw [show ‖(0 : Lp ℝ 2 (stdGaussianFin n))‖ = 0 by simp, mul_zero]
      refine measure_mono_null ?_ (ae_iff.mp (Lp.coeFn_zero ℝ 2 (stdGaussianFin n)))
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      exact abs_pos.mp hx
    rw [hzero]
    exact bot_le
  · have hFnorm : 0 < ‖F‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnorm_zero)
    by_cases hlarge : L0 ≤ lam
    · set t : ℝ := (lam / L0) ^ ((2 : ℝ) / d)
      set p : ℝ := 1 + t
      have hratio_one : 1 ≤ lam / L0 := by
        rw [le_div_iff₀ hL0_pos]
        simpa using hlarge
      have hp_two_le : 2 ≤ p := by
        have ht_one : 1 ≤ t := by
          calc
            (1 : ℝ) = 1 ^ ((2 : ℝ) / d) := by simp
            _ ≤ (lam / L0) ^ ((2 : ℝ) / d) :=
              Real.rpow_le_rpow zero_le_one hratio_one (by positivity)
        linarith
      let A : ℝ := ((d : ℝ) + 1) * (p - 1) ^ ((d : ℝ) / 2)
      have htail :=
        markov_bonami_bound_explicit F hF lam p A hlam hFnorm rfl hp_two_le
      have hpminus :
          (p - 1) ^ ((d : ℝ) / 2) = lam / L0 := by
        dsimp [p, t]
        have hbase : 0 ≤ lam / L0 := by positivity
        have hsimp : 1 + (lam / L0) ^ ((2 : ℝ) / d) - 1 = (lam / L0) ^ ((2 : ℝ) / d) := by
          ring
        rw [hsimp, ← Real.rpow_mul hbase]
        have hm : ((2 : ℝ) / d) * ((d : ℝ) / 2) = 1 := by
          field_simp [hd_ne]
        rw [hm, Real.rpow_one]
      have hA_over_lam : A / lam = Real.exp (-1) := by
        dsimp [A]
        rw [hpminus]
        calc
          (((d : ℝ) + 1) * (lam / L0)) / lam = ((d : ℝ) + 1) / L0 := by
            field_simp [hlam.ne']
          _ = ((d : ℝ) + 1) / (Real.exp 1 * ((d : ℝ) + 1)) := by
            rfl
          _ = Real.exp (-1) := by
            calc
              ((d : ℝ) + 1) / (Real.exp 1 * ((d : ℝ) + 1)) = (Real.exp 1)⁻¹ := by
                field_simp [hL0_pos.ne']
              _ = Real.exp (-1) := by
                rw [Real.exp_neg]
      have hpow_exp : (A / lam) ^ p = Real.exp (-p) := by
        rw [hA_over_lam]
        calc
          (Real.exp (-1)) ^ p = Real.exp ((-1) * p) := by rw [← Real.exp_mul]
          _ = Real.exp (-p) := by congr 1; ring
      have hc_half :
          c_d * lam ^ ((2 : ℝ) / d) = t / 2 := by
        dsimp [c_d, chaosTailConstant, L0, t]
        have hlam_nonneg : 0 ≤ lam := hlam.le
        have hinv_nonneg : 0 ≤ 1 / (Real.exp 1 * ((d : ℝ) + 1)) := by positivity
        rw [mul_assoc, ← Real.mul_rpow hinv_nonneg hlam_nonneg]
        have hrewrite :
            (1 / (Real.exp 1 * ((d : ℝ) + 1))) * lam = lam / (Real.exp 1 * ((d : ℝ) + 1)) := by
          field_simp
        rw [hrewrite]
        ring
      have ht_ge_one : 1 ≤ t := by
        calc
          (1 : ℝ) = 1 ^ ((2 : ℝ) / d) := by simp
          _ ≤ (lam / L0) ^ ((2 : ℝ) / d) :=
            Real.rpow_le_rpow zero_le_one hratio_one (by positivity)
      have hreal :
          Real.exp (-p) ≤ 2 * Real.exp (-c_d * lam ^ ((2 : ℝ) / d)) := by
        have hp_neg : -p = -(1 + t) := by
          dsimp [p]
        rw [hp_neg]
        have haux := exp_neg_one_add_le_two_mul_exp_neg_half ht_ge_one
        have haux' : Real.exp (-t + -1) ≤ 2 * Real.exp (-(t / 2 : ℝ)) := by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using haux
        have hc_neg : -c_d * lam ^ ((2 : ℝ) / d) = -(t / 2 : ℝ) := by
          linarith [hc_half]
        simpa [show -(1 + t) = -t + -1 by ring, hc_neg] using haux'
      have henn :
          ENNReal.ofReal (Real.exp (-p)) ≤
            2 * ENNReal.ofReal (Real.exp (-c_d * lam ^ ((2 : ℝ) / d))) := by
        rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul' (Real.exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal hreal
      have htail_exp :
          (stdGaussianFin n) {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|} ≤
            ENNReal.ofReal (Real.exp (-p)) := by
        simpa [hpow_exp] using htail
      exact htail_exp.trans henn
    · have hsmall : lam < L0 := lt_of_not_ge hlarge
      set t : ℝ := (lam / L0) ^ ((2 : ℝ) / d)
      letI : IsProbabilityMeasure (stdGaussianFin n) := by
        refine ⟨?_⟩
        simp [stdGaussianFin]
      have ht_lt_one : t < 1 := by
        dsimp [t]
        have hratio : lam / L0 < 1 := by
          rw [div_lt_iff₀ hL0_pos]
          simpa using hsmall
        have hratio_nonneg : 0 ≤ lam / L0 := by positivity
        calc
          (lam / L0) ^ ((2 : ℝ) / d) < 1 ^ ((2 : ℝ) / d) :=
            Real.rpow_lt_rpow hratio_nonneg hratio (by positivity)
          _ = 1 := by simp
      have htriv :
          (stdGaussianFin n) {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|} ≤ 1 :=
        prob_le_one (μ := stdGaussianFin n)
          (s := {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|})
      have hsmall_bound :
          (1 : ENNReal) ≤ 2 * ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) * t)) :=
        one_le_two_mul_exp_neg_half_ennreal ht_lt_one
      have hc_half :
          c_d * lam ^ ((2 : ℝ) / d) = t / 2 := by
        dsimp [c_d, chaosTailConstant, L0, t]
        have hlam_nonneg : 0 ≤ lam := hlam.le
        have hinv_nonneg : 0 ≤ 1 / (Real.exp 1 * ((d : ℝ) + 1)) := by positivity
        rw [mul_assoc, ← Real.mul_rpow hinv_nonneg hlam_nonneg]
        have hrewrite :
            (1 / (Real.exp 1 * ((d : ℝ) + 1))) * lam = lam / (Real.exp 1 * ((d : ℝ) + 1)) := by
          field_simp
        rw [hrewrite]
        ring
      have hrewrite_rhs :
          2 * ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) * t)) =
            2 * ENNReal.ofReal (Real.exp (-c_d * lam ^ ((2 : ℝ) / d))) := by
        congr 2
        congr 1
        linarith [hc_half]
      exact htriv.trans (hsmall_bound.trans_eq hrewrite_rhs)

/-- Explicit one-sided chaos tail bound with dimension-only constant. -/
theorem chaos_neg_tail_bound_explicit (n d : ℕ) (hd : 1 ≤ d) :
    ∀ (F : Lp ℝ 2 (stdGaussianFin n)), F ∈ wienerChaosLE n d →
    ∀ (K : ℝ), 0 < K → ‖F‖ ≤ K →
    ∀ (t : ℝ), 0 < t →
      (stdGaussianFin n) {ω | (F : (Fin n → ℝ) → ℝ) ω ≤ -t} ≤
        2 * ENNReal.ofReal
          (Real.exp (-(chaosTailConstant d) * (t / (2 * K)) ^ ((2 : ℝ) / d))) := by
  intro F hF K hK_pos hF_norm_le t ht
  have h_subset :
      {ω | (F : (Fin n → ℝ) → ℝ) ω ≤ -t} ⊆
        {ω | t / 2 < |((F : (Fin n → ℝ) → ℝ) ω)|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have h_neg : (F : (Fin n → ℝ) → ℝ) ω ≤ -t := hω
    have h_abs : t ≤ |((F : (Fin n → ℝ) → ℝ) ω)| := by
      rw [abs_of_nonpos (by linarith : (F : (Fin n → ℝ) → ℝ) ω ≤ 0)]
      linarith
    linarith
  refine le_trans (measure_mono h_subset) ?_
  by_cases hF_norm_zero : ‖F‖ = 0
  · have h_two_pos : (0 : ENNReal) < 2 := by norm_num
    have hF_zero : F = 0 := (Lp.norm_eq_zero_iff h_two_pos).mp hF_norm_zero
    have hF_ae : (F : (Fin n → ℝ) → ℝ) =ᵐ[stdGaussianFin n] 0 := by
      rw [hF_zero]
      exact Lp.coeFn_zero ℝ 2 _
    have h_set_null :
        (stdGaussianFin n)
            {ω | t / 2 < |((F : (Fin n → ℝ) → ℝ) ω)|} = 0 := by
      apply measure_mono_null _ (ae_iff.mp hF_ae)
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      have : (F : (Fin n → ℝ) → ℝ) ω ≠ 0 := by
        intro h_eq
        rw [h_eq, abs_zero] at hω
        linarith
      exact this
    rw [h_set_null]
    exact bot_le
  have hF_norm_ne : ‖F‖ ≠ 0 := hF_norm_zero
  have hF_norm_pos : 0 < ‖F‖ :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hF_norm_ne)
  set lam : ℝ := t / (2 * ‖F‖) with hlam_def
  have hlam_pos : 0 < lam := by
    apply div_pos ht
    linarith [hF_norm_pos]
  have h_lam_norm_eq : lam * ‖F‖ = t / 2 := by
    rw [hlam_def]
    field_simp
  have h_conc_F :=
    polynomial_chaos_concentration_explicit n d hd F hF lam hlam_pos
  have h_set_eq :
      {ω | lam * ‖F‖ < |((F : (Fin n → ℝ) → ℝ) ω)|} =
        {ω | t / 2 < |((F : (Fin n → ℝ) → ℝ) ω)|} := by
    ext ω
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, h_lam_norm_eq]
  rw [h_set_eq] at h_conc_F
  refine le_trans h_conc_F ?_
  refine mul_le_mul_right ?_ _
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have h_lam_lb : t / (2 * K) ≤ lam := by
    rw [hlam_def]
    apply div_le_div_of_nonneg_left ht.le (by positivity)
    linarith
  have h_pow_le :
      (t / (2 * K)) ^ ((2 : ℝ) / d) ≤ lam ^ ((2 : ℝ) / d) := by
    apply Real.rpow_le_rpow
    · positivity
    · exact h_lam_lb
    · have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
      positivity
  nlinarith [chaosTailConstant_pos d hd]

end Pphi2.ChaosTailBridge
