/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas
-/

/-
# Periodization: Re-export from gaussian-field

The periodization CLM `𝓢(ℝ) →L[ℝ] C∞(S¹_L)` is defined in
`SchwartzNuclear.Periodization` in the gaussian-field package.
This file re-exports it for use in pphi2's IR limit.
-/

import SchwartzNuclear.Periodization

namespace Pphi2

-- Re-export periodizeCLM from gaussian-field
open GaussianField Filter

section
variable (L : ℝ) [hL : Fact (0 < L)]

/-- Symmetric-window version of `GaussianField.periodizeCLM_eq_on_large_period`.

If a Schwartz function is supported in `[-T, T]`, then once the circle period is larger than
`4 * T`, its periodization agrees with the original function on the same symmetric interval.
The proof shifts `[-T, T]` to `[0, 2 * T]`, applies the one-sided large-period lemma there,
and then shifts back. -/
theorem periodizeCLM_eq_on_symmetric_large_period
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hL_large : L > 4 * T) :
    ∀ t ∈ Set.Icc (-T) T, (periodizeCLM L h).toFun t = h t := by
  let hshift := schwartzTranslation T h
  have hshift_supp : ∀ u, 2 * T < |u| → hshift u = 0 := by
    intro u hu
    have hu' : T < |u - T| := by
      by_cases hu_nonneg : 0 ≤ u
      · rw [abs_of_nonneg hu_nonneg] at hu
        by_cases hTu : T ≤ u
        · rw [abs_of_nonneg (sub_nonneg.mpr hTu)]
          linarith
        · have hu_lt : u < T := by
            linarith
          rw [abs_of_neg (sub_neg.mpr hu_lt)]
          linarith
      · have hu_neg : u < 0 := lt_of_not_ge hu_nonneg
        rw [abs_of_neg hu_neg] at hu
        have hsub_neg : u - T < 0 := by
          linarith
        rw [abs_of_neg hsub_neg]
        linarith
    simp [hshift, schwartzTranslation_apply, hsupp (u - T) hu']
  have hshift_eq :=
    periodizeCLM_eq_on_large_period (L := L) hshift (2 * T)
      (by positivity) hshift_supp (by linarith [hL_large])
  intro t ht
  have ht_shift : t + T ∈ Set.Icc 0 (L / 2) := by
    constructor
    · linarith [ht.1]
    · have hLT : 2 * T < L / 2 := by
        linarith [hL_large]
      linarith [ht.2, hLT]
  have hmain := hshift_eq (t + T) ht_shift
  change (periodizeCLM L hshift) (t + T) = hshift (t + T) at hmain
  change (periodizeCLM L h) t = h t
  have hcomm :
      (periodizeCLM L hshift) (t + T) = (periodizeCLM L h) t := by
    rw [show hshift = schwartzTranslation T h by rfl, periodizeCLM_comp_schwartzTranslation]
    simp [circleTranslation]
  calc
    (periodizeCLM L h) t = (periodizeCLM L hshift) (t + T) := by
      symm
      exact hcomm
    _ = hshift (t + T) := hmain
    _ = h t := by
      simp [hshift, schwartzTranslation_apply]

end

/-- For compactly supported Schwartz functions, periodization converges uniformly on the fixed
symmetric support window because it is eventually exactly equal there. -/
theorem periodizeCLM_tendsto_uniformlyOn_symmetricCompact
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun n t => (@periodizeCLM (Lt n) (hLt n) h).toFun t)
      h atTop (Set.Icc (-T) T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlarge : ∀ᶠ n in atTop, 4 * T + 1 ≤ Lt n :=
    (Filter.tendsto_atTop.mp hLt_tend) (4 * T + 1)
  filter_upwards [hlarge] with n hn t ht
  have heq :=
    periodizeCLM_eq_on_symmetric_large_period
      (L := Lt n) h T hT hsupp (by linarith) t ht
  rw [Real.dist_eq]
  simpa [heq] using hε

end Pphi2
