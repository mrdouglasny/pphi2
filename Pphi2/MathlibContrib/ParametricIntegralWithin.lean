/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# One-sided differentiation under the integral sign

A *one-sided* (right) version of `hasDerivAt_integral_of_dominated_loc_of_deriv_le`: the derivative of
`x ↦ ∫ a, F x a ∂μ` *within* `Set.Ici x₀` at `x₀` equals `∫ a, F' x₀ a ∂μ`, assuming the derivative
bound holds only on `Ici x₀ ∩ ball x₀ ε`.

This is what is needed when the integrand is dominated only on one side of `x₀` — e.g. Gibbs families
`g ↦ ∫ A e^{−gV}` in constructive QFT, where for `g < 0` the weight `e^{−gV}` is not integrable (the
Dyson instability), so the two-sided theorem does not apply.

## Implementation

We extend `F` across `x₀` by its affine first-order part below `x₀`,
`G x a = if x₀ ≤ x then F x a else F x₀ a + (x − x₀) • F' x₀ a`,
whose derivative bound is two-sided. The existing two-sided
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` gives `HasDerivAt (∫ G ·) (∫ F' x₀) x₀`, and since
`G = F` on `Ici x₀` this restricts to the desired `HasDerivWithinAt`. Intended for upstreaming to
`Mathlib/Analysis/Calculus/ParametricIntegral.lean`.
-/

open MeasureTheory Filter Metric Set
open scoped Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F F' : ℝ → α → E} {x₀ : ℝ} {bound : α → ℝ} {ε : ℝ}

/-- Derivative of the affine extension `x ↦ c + (x − p) • v`. -/
private theorem hasDerivAt_affine (p : ℝ) (c v : E) (x : ℝ) :
    HasDerivAt (fun y : ℝ => c + (y - p) • v) v x := by
  have h := (((hasDerivAt_id x).sub_const p).smul_const v).const_add c
  simpa using h

/-- **Right-derivative under the integral sign.** If `x ↦ F x a` is differentiable within `Ici x₀`
with derivative `F' x a` bounded by an integrable `bound a` on `Ici x₀ ∩ ball x₀ ε`, then
`x ↦ ∫ a, F x a ∂μ` is differentiable within `Ici x₀` at `x₀` with derivative `∫ a, F' x₀ a ∂μ`.

Unlike `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, the domination is required only on the
right of `x₀`, so this applies when `F` blows up for `x < x₀`. -/
theorem hasDerivWithinAt_Ici_integral_of_dominated_of_deriv_le (ε_pos : 0 < ε)
    (hF_meas : ∀ x ∈ Ici x₀ ∩ ball x₀ ε, AEStronglyMeasurable (F x) μ)
    (hF_int : Integrable (F x₀) μ) (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ Ici x₀ ∩ ball x₀ ε, ‖F' x a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ Ici x₀ ∩ ball x₀ ε, HasDerivWithinAt (F · a) (F' x a) (Ici x₀) x) :
    HasDerivWithinAt (fun x => ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) (Ici x₀) x₀ := by
  classical
  set G : ℝ → α → E := fun x a => if x₀ ≤ x then F x a else F x₀ a + (x - x₀) • F' x₀ a with hGdef
  set G' : ℝ → α → E := fun x a => if x₀ ≤ x then F' x a else F' x₀ a with hG'def
  have hx₀mem : x₀ ∈ Ici x₀ ∩ ball x₀ ε := ⟨mem_Ici.mpr le_rfl, mem_ball_self ε_pos⟩
  -- Pointwise identities for `G`, `G'` at and around `x₀`.
  have hG_ge : ∀ x a, x₀ ≤ x → G x a = F x a := fun x a h => by simp [hGdef, h]
  have hG_lt : ∀ x a, ¬ x₀ ≤ x → G x a = F x₀ a + (x - x₀) • F' x₀ a := fun x a h => by simp [hGdef, h]
  have hG'_ge : ∀ x a, x₀ ≤ x → G' x a = F' x a := fun x a h => by simp [hG'def, h]
  have hG'_lt : ∀ x a, ¬ x₀ ≤ x → G' x a = F' x₀ a := fun x a h => by simp [hG'def, h]
  have hGx₀ : G x₀ = F x₀ := by funext a; exact hG_ge x₀ a le_rfl
  have hG'x₀ : G' x₀ = F' x₀ := by funext a; exact hG'_ge x₀ a le_rfl
  -- Measurability of `G x` near `x₀`.
  have hG_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (G x) μ := by
    filter_upwards [ball_mem_nhds x₀ ε_pos] with x hx
    by_cases hle : x₀ ≤ x
    · simpa only [show G x = F x from funext fun a => hG_ge x a hle] using hF_meas x ⟨hle, hx⟩
    · have : G x = fun a => F x₀ a + (x - x₀) • F' x₀ a := funext fun a => hG_lt x a hle
      rw [this]; exact hF_int.aestronglyMeasurable.add (hF'_meas.const_smul _)
  -- Two-sided derivative bound for `G'`.
  have hG_bound : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ‖G' x a‖ ≤ bound a := by
    filter_upwards [h_bound] with a ha x hx
    by_cases hle : x₀ ≤ x
    · rw [hG'_ge x a hle]; exact ha x ⟨hle, hx⟩
    · rw [hG'_lt x a hle]; exact ha x₀ hx₀mem
  -- Two-sided differentiability of `G`.
  have hG_diff : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, HasDerivAt (G · a) (G' x a) x := by
    filter_upwards [h_diff] with a ha x hx
    rcases lt_trichotomy x₀ x with hlt | heq | hlt
    · -- `x > x₀`: `G = F` on a neighbourhood of `x`.
      have hIci : Ici x₀ ∈ 𝓝 x := Ici_mem_nhds hlt
      have hFx : HasDerivAt (F · a) (F' x a) x := (ha x ⟨le_of_lt hlt, hx⟩).hasDerivAt hIci
      rw [hG'_ge x a (le_of_lt hlt)]
      refine hFx.congr_of_eventuallyEq ?_
      filter_upwards [hIci] with y hy using hG_ge y a hy
    · -- `x = x₀`: glue the right (`Ici`) and left (`Iic`) derivatives.
      subst heq
      have hR : HasDerivWithinAt (G · a) (F' x₀ a) (Ici x₀) x₀ :=
        (ha x₀ hx₀mem).congr (fun y hy => hG_ge y a hy) (hG_ge x₀ a le_rfl)
      have haff : HasDerivAt (fun y : ℝ => F x₀ a + (y - x₀) • F' x₀ a) (F' x₀ a) x₀ :=
        hasDerivAt_affine x₀ (F x₀ a) (F' x₀ a) x₀
      have hL : HasDerivWithinAt (G · a) (F' x₀ a) (Iic x₀) x₀ := by
        refine haff.hasDerivWithinAt.congr (fun y hy => ?_) ?_
        · by_cases hxy : x₀ ≤ y
          · rw [hG_ge y a hxy, le_antisymm (mem_Iic.mp hy) hxy]; simp
          · exact hG_lt y a hxy
        · rw [hG_ge x₀ a le_rfl]; simp
      rw [hG'_ge x₀ a le_rfl]
      have := hR.union hL
      rwa [Ici_union_Iic, hasDerivWithinAt_univ] at this
    · -- `x < x₀`: `G` is affine on a neighbourhood of `x`.
      rw [hG'_lt x a (not_le.mpr hlt)]
      refine (hasDerivAt_affine x₀ (F x₀ a) (F' x₀ a) x).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hlt] with y hy using hG_lt y a (not_le.mpr hy)
  -- Two-sided theorem applied to `G`, then restricted to `Ici x₀`.
  have key : HasDerivAt (fun x => ∫ a, G x a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ := by
    have := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := ball x₀ ε)
      (ball_mem_nhds x₀ ε_pos) hG_meas (hGx₀ ▸ hF_int) (hG'x₀ ▸ hF'_meas) hG_bound
      bound_integrable hG_diff).2
    rwa [hG'x₀] at this
  refine (key.hasDerivWithinAt).congr (fun x hx => ?_) ?_
  · exact integral_congr_ae (Eventually.of_forall fun a => (hG_ge x a hx).symm)
  · exact integral_congr_ae (Eventually.of_forall fun a => (hG_ge x₀ a le_rfl).symm)

end MeasureTheory
