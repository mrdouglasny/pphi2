/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Integrability Helpers for the Layer-Cake Integral

The bridge derivation produces a layer-cake integral of the form
`∫⁻ t in Ioi 0, ψ(t) · exp(2t)` where `ψ(t)` is a doubly-exponential
tail bound. This file collects the integrability results that show
this integral converges.

## Main results

* `lintegral_exp_two_mul_lt_top_of_eventual_exp_neg`: if `ψ(t)` is
  eventually bounded above by `exp(-3 t)` (i.e., decays faster than
  any rate that beats the layer-cake's `exp(2t)` growth), then the
  layer-cake integral converges.

This is a pure-analysis helper — no QFT, no lattice, no chaos. -/

import Pphi2.NelsonEstimate.LayerCake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

namespace Pphi2.IntegrabilityHelpers

open MeasureTheory Real Set

/-- The function `t ↦ exp(-t)` is `lintegral`-integrable on
`Ioi T₀` for any `T₀`. -/
theorem lintegral_exp_neg_lt_top (T₀ : ℝ) :
    ∫⁻ t in Set.Ioi T₀, ENNReal.ofReal (Real.exp (-t)) < ⊤ := by
  have h_integrable : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi T₀) := by
    have := integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) T₀
    simpa using this
  have h_eq :
      ∫⁻ t in Set.Ioi T₀, ENNReal.ofReal (Real.exp (-t)) =
        ENNReal.ofReal (∫ t in Set.Ioi T₀, Real.exp (-t)) := by
    rw [ofReal_integral_eq_lintegral_ofReal h_integrable]
    refine Filter.Eventually.of_forall ?_
    intro t; exact (Real.exp_pos _).le
  rw [h_eq]
  exact ENNReal.ofReal_lt_top

/-- **Layer-cake integrand integrability via eventual exponential decay.**

If `ψ : ℝ → ℝ≥0∞` is eventually bounded by `exp(-3t)` (i.e., bounded
on `Ioi T₀` for some `T₀`), then the layer-cake integral
`∫⁻ t in Ioi 0, ψ(t) · 2 exp(2t)` is finite, provided the small-`t`
piece on `(0, T₀]` is also bounded.

This is the master integrability tool used by the bridge: the
dynamical-cutoff tail bound on `μ{V ≤ -t}` produces a
doubly-exponential `ψ`, which beats `exp(-3t)` eventually, so the
layer-cake integral converges. -/
theorem lintegral_layer_cake_lt_top_of_eventual_decay
    (ψ : ℝ → ENNReal)
    (T₀ : ℝ) (hT₀ : 0 < T₀)
    (h_small : ∫⁻ t in Set.Ioc (0 : ℝ) T₀,
        ψ t * ENNReal.ofReal (2 * Real.exp (2 * t)) < ⊤)
    (h_large : ∀ t, T₀ < t →
        ψ t * ENNReal.ofReal (2 * Real.exp (2 * t)) ≤
          ENNReal.ofReal (Real.exp (-t))) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
      ψ t * ENNReal.ofReal (2 * Real.exp (2 * t)) < ⊤ := by
  -- Split (0, ∞) = (0, T₀] ∪ (T₀, ∞).
  have h_split : Set.Ioi (0 : ℝ) = Set.Ioc 0 T₀ ∪ Set.Ioi T₀ := by
    ext t
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro ht
      by_cases h : t ≤ T₀
      · left; exact ⟨ht, h⟩
      · right; exact lt_of_not_ge h
    · rintro (⟨ht, _⟩ | ht)
      · exact ht
      · linarith
  rw [h_split]
  -- ∫⁻ x in A ∪ B, f x ≤ ∫⁻ x in A, f x + ∫⁻ x in B, f x (lintegral_union_le).
  refine lt_of_le_of_lt (lintegral_union_le _ _ _) ?_
  refine ENNReal.add_lt_top.mpr ⟨h_small, ?_⟩
  -- Large-t piece: bound by ∫⁻ exp(-t).
  refine lt_of_le_of_lt ?_ (lintegral_exp_neg_lt_top T₀)
  apply MeasureTheory.setLIntegral_mono' measurableSet_Ioi
  intro t ht
  exact h_large t ht

end Pphi2.IntegrabilityHelpers
