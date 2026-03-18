/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# General Results: Complex Analysis

Analyticity of parameter-dependent integrals (holomorphic dependence on
parameters). This is the several-complex-variables version of Morera's
theorem / differentiation under the integral sign.

## Main results

- `analyticOnNhd_integral` — if `z ↦ F(z, ω)` is entire for each ω
  and dominated by an integrable bound locally uniform in z, then
  `z ↦ ∫ F(z, ω) dμ` is entire.

## Proof structure

1. **One-variable analyticity** (`differentiable_one_var_integral`):
   For `G : ℂ → α → ℂ` with pointwise analyticity and compact domination,
   the integral `z ↦ ∫ G(z, ω) dμ` is differentiable on ℂ, hence analytic
   (by `Differentiable.analyticAt`).

2. **Separate analyticity**: For each coordinate `j`, fixing all other
   coordinates gives a one-variable problem, handled by step 1.

3. **Continuity** (`continuous_integral_of_compact_dom`): Dominated
   convergence gives continuity of the integral.

4. **Joint analyticity** (`osgood_separately_analytic`): Osgood's lemma
   upgrades separate analyticity + continuity to joint analyticity.

## References

- Reed-Simon I, Theorem VI.1 (analytic families of integrands)
- Fernique (1975), §III.4
- Stein-Shakarchi, *Complex Analysis*, Ch. 2 §5 (Morera + Fubini)
- Krantz, *Function Theory of Several Complex Variables*, Thm 7.2.1 (Osgood)
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Analytic.Basic

open MeasureTheory Complex Filter Topology Metric Set
open scoped ENNReal NNReal

/-! ### Osgood's Lemma

A continuous function on `ℂⁿ` that is separately analytic in each
coordinate is jointly analytic. This is a standard result in several
complex variables (weaker than Hartogs' theorem, which drops the
continuity hypothesis).

Reference: Krantz, *Function Theory of Several Complex Variables*,
Theorem 7.2.1. -/

namespace ComplexAnalysis

/-- **Osgood's lemma.** A continuous function `f : ℂⁿ → ℂ` that is
separately analytic in each complex coordinate is jointly analytic.

This is a classical result in several complex variables. The proof
proceeds by induction on `n`, using the Cauchy integral formula in
one variable and analyticity of the resulting coefficients by induction.

Axiomatized as a standard textbook fact (Krantz, Thm 7.2.1). -/
axiom osgood_separately_analytic {n : ℕ}
    {f : (Fin n → ℂ) → ℂ}
    (hf_cont : Continuous f)
    (hf_sep : ∀ (j : Fin n) (z₀ : Fin n → ℂ),
      AnalyticAt ℂ (fun t : ℂ => f (Function.update z₀ j t)) (z₀ j)) :
    AnalyticOnNhd ℂ f Set.univ

end ComplexAnalysis

/-! ### Helper: analyticity of coordinate update map -/

/-- The map `t ↦ Function.update z₀ j t` is analytic as a function `ℂ → (Fin n → ℂ)`.
This is an affine embedding of a coordinate line. -/
theorem analyticAt_update {n : ℕ} (z₀ : Fin n → ℂ) (j : Fin n) (t₀ : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => Function.update z₀ j t) t₀ := by
  rw [show (fun t => Function.update z₀ j t) =
    (fun t i => if i = j then t else z₀ i) from by ext t i; simp [Function.update_apply]]
  rw [analyticAt_pi_iff (f := fun i t => if i = j then t else z₀ i)]
  intro i
  by_cases hij : i = j
  · simp only [hij, ite_true]; exact analyticAt_id
  · simp only [hij, ite_false]; exact analyticAt_const

/-! ### One-variable integral analyticity

For `G : ℂ → α → ℂ` with pointwise analyticity and locally uniform
integrable domination, the integral `z ↦ ∫ G(z,ω) dμ` is differentiable
on all of ℂ, hence analytic (Goursat's theorem). -/

/-- The integral of a pointwise-analytic dominated family is differentiable
on ℂ. Uses Cauchy estimates for the derivative bound and
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` from Mathlib. -/
theorem differentiable_one_var_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {G : ℂ → α → ℂ}
    (hG_an : ∀ ω, AnalyticOnNhd ℂ (G · ω) Set.univ)
    (hG_meas : ∀ z, AEStronglyMeasurable (G z) μ)
    (hG_dom : ∀ K : Set ℂ, IsCompact K →
      ∃ bound : α → ℝ, Integrable bound μ ∧
        ∀ z ∈ K, ∀ᵐ ω ∂μ, ‖G z ω‖ ≤ bound ω) :
    Differentiable ℂ (fun z => ∫ ω, G z ω ∂μ) := by
  intro z₀
  -- Each G(·, ω) is differentiable (analytic ⟹ differentiable)
  have hG_diff : ∀ ω, Differentiable ℂ (G · ω) := fun ω z =>
    (hG_an ω).differentiableOn.differentiableAt (isOpen_univ.mem_nhds (mem_univ z))
  -- Get domination bound on closedBall z₀ 2
  obtain ⟨bound, h_int_bound, h_dom⟩ :=
    hG_dom (closedBall z₀ 2) (isCompact_closedBall z₀ 2)
  -- Work on the ball of radius 1 around z₀
  set s := ball z₀ 1 with hs_def
  -- G(z₀, ·) is integrable (dominated by bound)
  have hG_int : Integrable (G z₀) μ := by
    refine h_int_bound.mono (hG_meas z₀) ?_
    filter_upwards [h_dom z₀ (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 2))] with ω hω
    exact hω.trans (le_abs_self _)
  -- Swap quantifiers: from "∀ z, ae ω" to "ae ω, ∀ z" on closedBall z₀ 2
  -- Uses countable dense subset + continuity of G(·, ω)
  have h_uniform : ∀ᵐ ω ∂μ, ∀ z ∈ closedBall z₀ 2, ‖G z ω‖ ≤ bound ω := by
    -- Step 1: Get a countable dense subset D of closedBall z₀ 2
    obtain ⟨D, hD_sub, hD_count, hD_dense⟩ :=
      (isCompact_closedBall z₀ 2).isSeparable.exists_countable_dense_subset
    -- Step 2: Swap quantifiers on D using countable intersection
    have h_ae_D : ∀ᵐ ω ∂μ, ∀ d ∈ D, ‖G d ω‖ ≤ bound ω := by
      rw [ae_ball_iff hD_count]
      exact fun d hd => h_dom d (hD_sub hd)
    -- Step 3: Extend from D to all of closedBall z₀ 2 using continuity + closure
    filter_upwards [h_ae_D] with ω hω z hz
    -- The set S = {z | ‖G z ω‖ ≤ bound ω} is closed (G(·, ω) is continuous)
    have hS_closed : IsClosed {z | ‖G z ω‖ ≤ bound ω} :=
      isClosed_le (hG_diff ω).continuous.norm continuous_const
    -- D ⊆ S
    have hD_in_S : D ⊆ {z | ‖G z ω‖ ≤ bound ω} := fun d hd => hω d hd
    -- closedBall z₀ 2 ⊆ closure D ⊆ S (since S is closed and contains D)
    exact hS_closed.closure_subset (closure_mono hD_in_S (hD_dense hz))
  -- Derivative bound via Cauchy estimate
  set deriv_bound : α → ℝ := fun ω => bound ω
  -- Measurability of the derivative at z₀
  -- Standard: deriv is a pointwise limit of measurable difference quotients
  -- (aestronglyMeasurable_of_tendsto_ae with f_n(ω) = (n+1)·(G(z₀+1/(n+1))ω - G z₀ ω))
  have hG'_meas : AEStronglyMeasurable (fun ω => deriv (G · ω) z₀) μ := by
    -- The derivative is a pointwise limit of measurable difference quotients.
    -- Define h_n = (n+1)⁻¹ ∈ ℂ and f_n(ω) = h_n⁻¹ • (G(z₀ + h_n, ω) - G(z₀, ω)).
    -- Then f_n(ω) → deriv (G · ω) z₀ for all ω, and each f_n is AEStronglyMeasurable.
    apply aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun n ω => ((↑(n + 1 : ℕ) : ℂ)⁻¹)⁻¹ • (G (z₀ + (↑(n + 1 : ℕ) : ℂ)⁻¹) ω - G z₀ ω))
    · -- Each difference quotient is AEStronglyMeasurable
      intro n
      exact aestronglyMeasurable_const.smul ((hG_meas _).sub (hG_meas _))
    · -- Pointwise convergence: f_n(ω) → deriv (G · ω) z₀ for all ω
      apply ae_of_all μ
      intro ω
      have hda := (hG_diff ω z₀).hasDerivAt
      rw [hasDerivAt_iff_tendsto_slope_zero] at hda
      refine hda.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_)
      · -- (↑(n+1))⁻¹ → 0 in ℂ, shown via ‖·‖ → 0
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simp only [norm_inv, Complex.norm_natCast]
        have h_atTop : Tendsto (fun n : ℕ => (↑(n + 1 : ℕ) : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
        exact tendsto_inv_atTop_zero.comp h_atTop
      · -- (↑(n+1))⁻¹ ≠ 0 for all n
        apply Eventually.of_forall
        intro n
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        apply inv_ne_zero
        simp only [ne_eq, Nat.cast_eq_zero]
        exact Nat.succ_ne_zero n
  -- Derivative bound on ball z₀ 1: Cauchy estimate gives ‖deriv f w‖ ≤ M/R
  -- where M = bound(ω) on closedBall w 1 ⊂ closedBall z₀ 2 and R = 1
  have h_deriv_bound : ∀ᵐ ω ∂μ, ∀ w ∈ s, ‖deriv (G · ω) w‖ ≤ deriv_bound ω := by
    filter_upwards [h_uniform] with ω hω w hw
    -- sphere w 1 ⊂ closedBall z₀ 2 (triangle inequality: dist + dist ≤ 1 + 1)
    have h_sphere : ∀ z ∈ sphere w 1, ‖G z ω‖ ≤ bound ω := by
      intro z hz
      exact hω z (mem_closedBall.mpr (by
        calc dist z z₀ ≤ dist z w + dist w z₀ := dist_triangle _ _ _
          _ ≤ 1 + 1 := add_le_add (mem_sphere.mp hz ▸ le_refl _)
              (le_of_lt (mem_ball.mp hw))
          _ = 2 := by norm_num))
    -- DiffContOnCl for the Cauchy estimate
    have h_dcoc : DiffContOnCl ℂ (G · ω) (ball w 1) :=
      (hG_diff ω).differentiableOn.diffContOnCl
    -- Apply Cauchy: ‖iteratedDeriv 1 f w‖ ≤ 1! * bound(ω) / 1^1
    have h_cauchy := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1
      one_pos h_dcoc h_sphere
    rwa [Nat.factorial_one, Nat.cast_one, one_mul, pow_one, div_one,
      iteratedDeriv_one] at h_cauchy
  -- Integrability of derivative bound
  have h_int_deriv : Integrable deriv_bound μ := h_int_bound
  -- HasDerivAt for each ω (analytic ⟹ has derivative)
  have h_hasderiv : ∀ᵐ ω ∂μ, ∀ w ∈ s, HasDerivAt (G · ω) (deriv (G · ω) w) w :=
    ae_of_all μ fun ω w _ => (hG_diff ω w).hasDerivAt
  -- Apply parametric integral differentiation
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall hG_meas) hG_int hG'_meas
    h_deriv_bound h_int_deriv h_hasderiv).2.differentiableAt

/-! ### Continuity of the integral -/

/-- The integral `z ↦ ∫ F(z,ω) dμ` is continuous under pointwise
continuity and locally uniform integrable domination. -/
theorem continuous_integral_of_compact_dom {n : ℕ} {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : (Fin n → ℂ) → α → ℂ}
    (hF_an : ∀ ω, AnalyticOnNhd ℂ (F · ω) Set.univ)
    (hF_meas : ∀ z, AEStronglyMeasurable (F z) μ)
    (hF_dom : ∀ K : Set (Fin n → ℂ), IsCompact K →
      ∃ bound : α → ℝ, Integrable bound μ ∧
        ∀ z ∈ K, ∀ᵐ ω ∂μ, ‖F z ω‖ ≤ bound ω) :
    Continuous (fun z => ∫ ω, F z ω ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  obtain ⟨bound, h_int, h_bd⟩ := hF_dom (closedBall z₀ 1) (isCompact_closedBall z₀ 1)
  exact continuousAt_of_dominated
    (Eventually.of_forall hF_meas)
    (Filter.eventually_of_mem (closedBall_mem_nhds z₀ one_pos) h_bd)
    h_int
    (ae_of_all μ fun ω =>
      ((hF_an ω).differentiableOn.differentiableAt
        (isOpen_univ.mem_nhds (mem_univ z₀))).continuousAt)

/-! ### Main theorem -/

/-- **Analyticity of parameter-dependent integrals (Morera).**

If for each fixed `ω`, the map `z ↦ F(z, ω)` is entire analytic on `ℂⁿ`,
and the family is dominated by an integrable bound that is locally uniform
in `z`, then the integral `z ↦ ∫ F(z, ω) dμ` is entire analytic.

**Proof.** By Osgood's lemma, it suffices to show continuity and separate
analyticity. Continuity follows from dominated convergence. For each
coordinate `j`, fixing all other coordinates reduces to the one-variable
case, where differentiability under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) combined with
Goursat's theorem (`Differentiable.analyticAt`) gives analyticity. -/
theorem analyticOnNhd_integral {n : ℕ} {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : (Fin n → ℂ) → α → ℂ}
    (hF_an : ∀ ω, AnalyticOnNhd ℂ (F · ω) Set.univ)
    (hF_meas : ∀ z, AEStronglyMeasurable (F z) μ)
    (hF_dom : ∀ K : Set (Fin n → ℂ), IsCompact K →
      ∃ bound : α → ℝ, Integrable bound μ ∧
        ∀ z ∈ K, ∀ᵐ ω ∂μ, ‖F z ω‖ ≤ bound ω) :
    AnalyticOnNhd ℂ (fun z => ∫ ω, F z ω ∂μ) Set.univ := by
  -- Step 1: The integral is continuous (dominated convergence)
  have hI_cont : Continuous (fun z => ∫ ω, F z ω ∂μ) :=
    continuous_integral_of_compact_dom hF_an hF_meas hF_dom
  -- Step 2: The integral is separately analytic in each coordinate
  have hI_sep : ∀ (j : Fin n) (z₀ : Fin n → ℂ),
      AnalyticAt ℂ (fun t : ℂ => ∫ ω, F (Function.update z₀ j t) ω ∂μ) (z₀ j) := by
    intro j z₀
    -- The one-variable restriction G(t, ω) = F(update z₀ j t, ω) satisfies the hypotheses
    set G : ℂ → α → ℂ := fun t ω => F (Function.update z₀ j t) ω with hG_def
    -- G(·, ω) is analytic (composition of F(·,ω) with the affine update map)
    have hG_an : ∀ ω, AnalyticOnNhd ℂ (G · ω) Set.univ := by
      intro ω t _
      exact (hF_an ω _ (mem_univ _)).comp (analyticAt_update z₀ j t)
    -- G(t, ·) is measurable
    have hG_meas : ∀ t, AEStronglyMeasurable (G t) μ := fun t => hF_meas _
    -- Domination: compact K ⊂ ℂ maps to compact K' ⊂ ℂⁿ
    have hG_dom : ∀ K : Set ℂ, IsCompact K →
        ∃ bound : α → ℝ, Integrable bound μ ∧
          ∀ t ∈ K, ∀ᵐ ω ∂μ, ‖G t ω‖ ≤ bound ω := by
      intro K hK
      have hK' : IsCompact ((fun t => Function.update z₀ j t) '' K) :=
        hK.image (continuous_const.update j continuous_id)
      obtain ⟨bound, h_int, h_bd⟩ := hF_dom _ hK'
      exact ⟨bound, h_int, fun t ht => h_bd _ (mem_image_of_mem _ ht)⟩
    -- Apply the one-variable result
    have hG_diff : Differentiable ℂ (fun t => ∫ ω, G t ω ∂μ) :=
      differentiable_one_var_integral hG_an hG_meas hG_dom
    exact hG_diff.analyticAt (z₀ j)
  -- Step 3: Apply Osgood's lemma
  exact ComplexAnalysis.osgood_separately_analytic hI_cont hI_sep
