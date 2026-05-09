/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Chaos → One-Sided Tail Bridge

`polynomial_chaos_concentration` (Janson 5.10, in markov-semigroups)
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

This is the key lemma between markov-semigroups's
`polynomial_chaos_concentration` and the abstract bridge in
`BridgeFromTail.lean`.

## References

- pphi2/docs/polynomial-chaos-exp-moment-bridge-proof-plan.md.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import MarkovSemigroups.Gaussian.PolynomialChaosConcentration

noncomputable section

namespace Pphi2.ChaosTailBridge

open MeasureTheory MarkovSemigroups.Gaussian

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

end Pphi2.ChaosTailBridge
