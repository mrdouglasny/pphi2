/-
Copyright (c) 2025 Geoffrey Irving, Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

## Osgood's lemma for n complex variables

We generalize Osgood's lemma from `ℂ × ℂ` (proved in `Osgood2.lean`) to
`Fin n → ℂ`:  a continuous, separately analytic function of `n` complex
variables is jointly analytic.

The proof is by induction on `n` using the two-variable `osgood` from
`Osgood2.lean` and a "block Osgood" lemma for the inductive step.

The block Osgood lemma shows that `g : ℂ × (Fin m → ℂ) → ℂ`, analytic
in the ℂ-variable for each fixed `Fin m → ℂ` and jointly analytic in
`Fin m → ℂ` for each fixed ℂ, is jointly analytic. The mathematical
proof expands the 1D Cauchy series in `w`, shows the coefficients are
analytic in `v` (via the inductive hypothesis), and builds the joint
power series on `ℂ × (Fin m → ℂ)` via antidiagonal sums of multilinear
maps. The joint power series construction is axiomatized here;
the infrastructure (`jointTerm`, `prependFst`, etc.) is in place for
the eventual proof.
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Pphi2.GeneralResults.Osgood.Osgood2

open Complex (I)
open Set Function Filter Topology Metric
open scoped Real NNReal ENNReal

noncomputable section

/-! ### Helper: update is analytic -/

/-- `update z₀ j ·` is analytic as a function `ℂ → (Fin n → ℂ)`. -/
theorem analyticAt_update' {n : ℕ} (z₀ : Fin n → ℂ) (j : Fin n) (t₀ : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => update z₀ j t) t₀ := by
  rw [show (fun t => update z₀ j t) =
    (fun t i => if i = j then t else z₀ i) from by ext t i; simp [update_apply]]
  rw [analyticAt_pi_iff]
  intro i
  by_cases hij : i = j
  · simp only [hij, ite_true]; exact analyticAt_id
  · simp only [hij, ite_false]; exact analyticAt_const

/-! ### Splitting equivalence -/

abbrev splitCLE (n : ℕ) : (ℂ × (Fin n → ℂ)) ≃L[ℂ] (Fin (n + 1) → ℂ) :=
  Fin.consEquivL ℂ (fun _ : Fin (n + 1) => ℂ)

theorem fin_cons_eta {n : ℕ} (z : Fin (n + 1) → ℂ) :
    Fin.cons (z 0) (z ∘ Fin.succ) = z :=
  Fin.cons_self_tail z

/-! ### Base cases -/

theorem osgood_n0 {f : (Fin 0 → ℂ) → ℂ} :
    AnalyticOnNhd ℂ f Set.univ := by
  intro z _
  have : f = fun _ => f z := by ext w; congr 1; ext i; exact i.elim0
  rw [this]; exact analyticAt_const

theorem osgood_n1 {f : (Fin 1 → ℂ) → ℂ}
    (hf_sep : ∀ (j : Fin 1) (z₀ : Fin 1 → ℂ),
      AnalyticAt ℂ (fun t : ℂ => f (update z₀ j t)) (z₀ j)) :
    AnalyticOnNhd ℂ f Set.univ := by
  intro z _
  have h0 := hf_sep 0 z
  have hfact : f = (fun t => f (update z 0 t)) ∘ (fun v : Fin 1 → ℂ => v 0) := by
    ext v; simp only [comp_def]; congr 1; ext i
    rw [show i = (0 : Fin 1) from Subsingleton.elim i 0]; simp
  rw [hfact]
  exact h0.comp_of_eq ((ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).analyticAt z) (by simp)

/-! ### Inductive step helpers -/

theorem sep_analytic_tail {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℂ}
    (hf_sep : ∀ (j : Fin (n + 1)) (z₀ : Fin (n + 1) → ℂ),
      AnalyticAt ℂ (fun t : ℂ => f (update z₀ j t)) (z₀ j))
    (w : ℂ) (j : Fin n) (v₀ : Fin n → ℂ) :
    AnalyticAt ℂ (fun t : ℂ => f (Fin.cons w (update v₀ j t))) (v₀ j) := by
  suffices key : (fun t => f (Fin.cons w (update v₀ j t))) =
      fun t => f (update (Fin.cons w v₀) j.succ t) by
    rw [key]; exact hf_sep j.succ (Fin.cons w v₀)
  ext t; congr 1; ext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
  · simp [update_of_ne (Ne.symm (Fin.succ_ne_zero j))]
  · simp only [Fin.cons_succ]
    by_cases hj : i' = j
    · subst hj; simp
    · rw [update_of_ne hj, update_of_ne (fun h => hj (Fin.succ_injective _ h))]; simp

theorem sep_analytic_head {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℂ}
    (hf_sep : ∀ (j : Fin (n + 1)) (z₀ : Fin (n + 1) → ℂ),
      AnalyticAt ℂ (fun t : ℂ => f (update z₀ j t)) (z₀ j))
    (v : Fin n → ℂ) (w₀ : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => f (Fin.cons w v)) w₀ := by
  set z₀ : Fin (n + 1) → ℂ := Fin.cons w₀ v
  suffices key : ∀ w, Fin.cons w v = update z₀ 0 w by
    simp_rw [key]; exact hf_sep 0 z₀
  intro w; ext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
  · simp [z₀]
  · rw [update_of_ne (Fin.succ_ne_zero i')]; simp [z₀]

theorem continuous_fin_cons_tail {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℂ}
    (hf_cont : Continuous f) (w : ℂ) :
    Continuous (fun v : Fin n → ℂ => f (Fin.cons w v)) :=
  hf_cont.comp (continuous_const.finCons continuous_id)

/-! ### Block Osgood for n = 1 (two-variable case)

We transfer to `ℂ × ℂ` and apply the two-variable `osgood` from `Osgood2.lean`. -/

private theorem block_osgood_1
    {g : ℂ × (Fin 1 → ℂ) → ℂ}
    (g_cont : Continuous g)
    (g_an_w : ∀ v w, AnalyticAt ℂ (fun w => g (w, v)) w)
    (g_an_v : ∀ w v, AnalyticAt ℂ (fun v => g (w, v)) v) :
    AnalyticOnNhd ℂ g Set.univ := by
  let e₁ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  set g' : ℂ × ℂ → ℂ := fun p => g (p.1, e₁.symm p.2) with hg'_def
  have g'_cont : Continuous g' :=
    g_cont.comp (Continuous.prodMk continuous_fst (e₁.symm.continuous.comp continuous_snd))
  have g'_an : AnalyticOnNhd ℂ g' Set.univ :=
    osgood isOpen_univ g'_cont.continuousOn
      (fun z0 z1 _ => g_an_w (e₁.symm z1) z0)
      (fun z0 z1 _ => (g_an_v z0 (e₁.symm z1)).comp_of_eq (e₁.symm.analyticAt z1) rfl)
  intro p _
  have key : g = fun p => g' (p.1, e₁ p.2) := by ext ⟨w, v⟩; simp [hg'_def]
  rw [key]
  exact (g'_an _ (mem_univ _)).comp₂ analyticAt_fst ((e₁.analyticAt _).comp analyticAt_snd)

/-! ### Block Osgood: general case

For `g : ℂ × (Fin (m+2) → ℂ) → ℂ`, we split the second block as
`ℂ × (Fin (m+1) → ℂ)` and use two-variable Osgood on the first coordinate
of the block together with `w`. This merges one coordinate, reducing the
block size.

The key is that after this merge, we get a function on
`(ℂ × ℂ) × (Fin (m+1) → ℂ)` that is analytic in `ℂ × ℂ` (jointly, by
two-variable Osgood) and analytic in `Fin (m+1) → ℂ`. Using the CLE
`ℂ × ℂ ≅ Fin 2 → ℂ` and then `(Fin 2 → ℂ) × (Fin (m+1) → ℂ) ≅ Fin (m+3) → ℂ`,
the function is separately analytic in all `m+3` scalar coordinates,
continuous, and we can apply `osgood_separately_analytic (m+3)`.

But we need `osgood_separately_analytic` at `m+3 = (m+2) + 1 = n + 1`,
which is the inductive hypothesis! -/

/-! ### Parametric circle integrals: continuity and analyticity -/

/-- Circle integrals are continuous when the integrand varies continuously in a parameter
from any topological space. -/
private theorem continuous_circleIntegral_param {X : Type} [TopologicalSpace X]
    {f : X → ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : Continuous (uncurry f)) :
    Continuous (fun x => ∮ z in C(c, R), f x z) := by
  -- The circle integral = ∫ θ in 0..2π, (deriv circleMap θ) • f(x, circleMap θ)
  -- We need the uncurried (x, θ) ↦ integrand to be continuous.
  have hcont : Continuous (uncurry (fun (x : X) (θ : ℝ) =>
      deriv (circleMap c R) θ • f x (circleMap c R θ))) := by
    apply Continuous.smul
    · show Continuous (fun p : X × ℝ => deriv (circleMap c R) p.2)
      simp_rw [deriv_circleMap]
      exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
    · exact hf.comp (continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont 0 (2 * π)

/-- Parametric differentiability of an interval integral:
if the integrand `h(t, θ)` is jointly continuous and differentiable in `t` for each `θ`,
then `t ↦ ∫ θ in a..b, h(t, θ)` is differentiable. -/
private theorem differentiable_intervalIntegral_param
    {h : ℂ → ℝ → ℂ} {a b : ℝ}
    (hh_cont : Continuous (uncurry h))
    (hh_diff : ∀ θ, Differentiable ℂ (h · θ)) :
    Differentiable ℂ (fun t => ∫ θ in a..b, h t θ) := by
  intro t₀
  set s := ball t₀ 1 with hs_def
  -- Step 1: Measurability of h(t, ·) on Ι a b
  have h_meas : ∀ t, MeasureTheory.AEStronglyMeasurable (h t)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) := fun t =>
    (hh_cont.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  -- Step 2: h(t₀, ·) is interval integrable
  have h_int : IntervalIntegrable (h t₀) MeasureTheory.volume a b :=
    (hh_cont.comp (Continuous.prodMk continuous_const continuous_id)).continuousOn.intervalIntegrable
  -- Step 3: Measurability of the derivative at t₀ via difference quotient limit
  have h'_meas : MeasureTheory.AEStronglyMeasurable (fun θ => deriv (h · θ) t₀)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) := by
    apply aestronglyMeasurable_of_tendsto_ae (u := Filter.atTop)
      (f := fun n θ => ((↑(n + 1 : ℕ) : ℂ)⁻¹)⁻¹ • (h (t₀ + (↑(n + 1 : ℕ) : ℂ)⁻¹) θ - h t₀ θ))
    · intro n
      exact MeasureTheory.aestronglyMeasurable_const.smul
        ((hh_cont.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable.sub
         (hh_cont.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable)
    · apply MeasureTheory.ae_of_all
      intro θ
      have hda := (hh_diff θ t₀).hasDerivAt
      rw [hasDerivAt_iff_tendsto_slope_zero] at hda
      refine hda.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_)
      · rw [tendsto_zero_iff_norm_tendsto_zero]
        simp only [norm_inv, Complex.norm_natCast]
        exact tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      · exact Filter.Eventually.of_forall fun n =>
          inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
  -- Step 4: Derivative bound via Cauchy estimate on ball t₀ 1
  -- For t ∈ ball t₀ 1, sphere t 1 ⊂ closedBall t₀ 2, so Cauchy gives
  -- ‖deriv (h · θ) t‖ ≤ sup_{z ∈ closedBall t₀ 2} ‖h z θ‖ =: bound θ
  set bound : ℝ → ℝ := fun θ => sSup ((fun z => ‖h z θ‖) '' closedBall t₀ 2) with hbound_def
  have h_deriv_bound : ∀ᵐ (θ : ℝ) ∂MeasureTheory.volume,
      θ ∈ Set.uIoc a b → ∀ t ∈ s, ‖deriv (h · θ) t‖ ≤ bound θ := by
    apply MeasureTheory.ae_of_all
    intro θ _ t ht
    have h_sphere : ∀ z ∈ sphere t 1, ‖h z θ‖ ≤ bound θ := by
      intro z hz
      apply le_csSup
      · exact (IsCompact.image (isCompact_closedBall t₀ 2)
            (hh_cont.comp (Continuous.prodMk continuous_id continuous_const)).norm).bddAbove
      · exact ⟨z, mem_closedBall.mpr (by
          calc dist z t₀ ≤ dist z t + dist t t₀ := dist_triangle _ _ _
            _ ≤ 1 + 1 := add_le_add (mem_sphere.mp hz ▸ le_refl _)
                (le_of_lt (mem_ball.mp ht))
            _ = 2 := by norm_num), rfl⟩
    have h_cauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1
      one_pos (hh_diff θ).differentiableOn.diffContOnCl h_sphere
    rwa [Nat.factorial_one, Nat.cast_one, one_mul, pow_one, div_one,
      iteratedDeriv_one] at h_cauchy
  -- Step 5: The bound is integrable (it's continuous)
  have h_bound_int : IntervalIntegrable bound MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    suffices Continuous bound from this.continuousOn
    -- bound θ = sSup of ‖h z θ‖ over compact closedBall t₀ 2
    -- Use IsCompact.continuous_sSup: need (θ, z) ↦ ‖h z θ‖ continuous
    rw [hbound_def]
    exact IsCompact.continuous_sSup (isCompact_closedBall t₀ 2)
      (hh_cont.comp (continuous_snd.prodMk continuous_fst)).norm
  -- Step 6: HasDerivAt for h(·, θ) at each t
  have h_hasderiv : ∀ᵐ (θ : ℝ) ∂MeasureTheory.volume,
      θ ∈ Set.uIoc a b → ∀ t ∈ s, HasDerivAt (h · θ) (deriv (h · θ) t) t :=
    MeasureTheory.ae_of_all _ fun θ _ t _ => (hh_diff θ t).hasDerivAt
  -- Step 7: Apply the parametric differentiation theorem
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds t₀ one_pos)
    (Filter.Eventually.of_forall h_meas) h_int h'_meas
    h_deriv_bound h_bound_int h_hasderiv).2.differentiableAt

/-! ### Block Osgood: Cauchy coefficient construction -/

/-- Prepend `k` scalar multiplications: extract the `ℂ`-component from the first
`k` inputs and multiply, then apply `q` to the remaining `l` inputs. -/
private def prependFst {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ (k : ℕ) {l : ℕ}, ContinuousMultilinearMap ℂ (fun _ : Fin l ↦ ℂ × E) ℂ →
      ContinuousMultilinearMap ℂ (fun _ : Fin (l + k) ↦ ℂ × E) ℂ
  | 0, _, q => q
  | k + 1, _l, q => smulCmmap ℂ (ℂ × E) ℂ (fstCmmap ℂ ℂ E) (prependFst k q)

/-- Diagonal evaluation of `prependFst`: all inputs equal to `(u, s)`. -/
private theorem prependFst_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (k : ℕ) {l : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin l ↦ ℂ × E) ℂ)
    (u : ℂ) (s : E) :
    (prependFst k q) (fun _ => (u, s)) = u ^ k * q (fun _ => (u, s)) := by
  induction k with
  | zero => simp [prependFst, one_mul]
  | succ k ih =>
    simp only [prependFst, smulCmmap_apply, fstCmmap_apply, smul_eq_mul]
    -- After simp, the LHS applies prependFst k q to (fun i => (u, s))
    -- ih says (prependFst k q) (fun _ => (u, s)) = u^k * q (fun _ => (u, s))
    -- The function argument is alpha-equivalent, so we convert:
    change u * (prependFst k q) (fun _ => (u, s)) = u ^ (k + 1) * q (fun _ => (u, s))
    rw [ih]; ring

/-- Norm bound for `prependFst`: it does not inflate the operator norm. -/
private theorem prependFst_norm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (k : ℕ) {l : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin l ↦ ℂ × E) ℂ) :
    ‖prependFst k q‖ ≤ ‖q‖ := by
  induction k with
  | zero => simp only [prependFst]; exact le_refl _
  | succ k ih =>
    simp only [prependFst]
    have h1 := smulCmmap_norm (fstCmmap ℂ ℂ E) (prependFst k q)
    have h2 : ‖fstCmmap ℂ ℂ E‖ ≤ 1 := by
      apply ContinuousMultilinearMap.opNorm_le_bound (M := 1) zero_le_one
      intro z
      simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton, one_mul]
      conv_lhs => rw [show z = (fun _ : Fin 1 ↦ z 0) from by
        funext i; rw [show i = (0 : Fin 1) from Subsingleton.elim i 0]]
      rw [fstCmmap_apply]
      exact norm_fst_le (z 0)
    calc ‖smulCmmap ℂ (ℂ × E) ℂ (fstCmmap ℂ ℂ E) (prependFst k q)‖
        ≤ ‖fstCmmap ℂ ℂ E‖ * ‖prependFst k q‖ := h1
      _ ≤ 1 * ‖q‖ := by nlinarith [norm_nonneg (prependFst k q)]
      _ = ‖q‖ := one_mul _

/-- Compose a multilinear map with the `snd` projection on each input. -/
private def sndComp {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {l : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin l ↦ E) ℂ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin l ↦ ℂ × E) ℂ :=
  q.compContinuousLinearMap (fun _ => ContinuousLinearMap.snd ℂ ℂ E)

/-- `sndComp` extracts the `E`-components from all inputs. -/
private theorem sndComp_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {l : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin l ↦ E) ℂ)
    (u : ℂ) (s : E) :
    sndComp q (fun _ => (u, s)) = q (fun _ => s) := by
  simp [sndComp, ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- Norm bound for `sndComp`: it does not inflate the operator norm. -/
private theorem sndComp_norm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {l : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin l ↦ E) ℂ) :
    ‖sndComp q‖ ≤ ‖q‖ := by
  simp only [sndComp]
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg q)
  intro z
  have hsnd : ‖ContinuousLinearMap.snd ℂ ℂ E‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun ⟨_, f⟩ => by simp only [ContinuousLinearMap.coe_snd', one_mul]; exact le_max_right _ _)
  calc ‖(q.compContinuousLinearMap fun _ => ContinuousLinearMap.snd ℂ ℂ E) z‖
      = ‖q (fun i => (ContinuousLinearMap.snd ℂ ℂ E) (z i))‖ := by
        simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    _ ≤ ‖q‖ * ∏ i, ‖(ContinuousLinearMap.snd ℂ ℂ E) (z i)‖ :=
        q.le_opNorm _
    _ ≤ ‖q‖ * ∏ i, ‖z i‖ := by
        gcongr with i _
        calc ‖(ContinuousLinearMap.snd ℂ ℂ E) (z i)‖
            ≤ ‖ContinuousLinearMap.snd ℂ ℂ E‖ * ‖z i‖ :=
              (ContinuousLinearMap.snd ℂ ℂ E).le_opNorm (z i)
          _ ≤ 1 * ‖z i‖ := by nlinarith [norm_nonneg (z i)]
          _ = ‖z i‖ := one_mul _

/-- The `(k, l)`-th joint term: prepend `k` fst-extractions, then compose with snd. -/
private def jointTerm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {l : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin l ↦ E) ℂ) (k : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (l + k) ↦ ℂ × E) ℂ :=
  prependFst k (sndComp q)

/-- Diagonal evaluation: `jointTerm q k` at constant `(u, s)` gives `u^k * q(s, …, s)`. -/
private theorem jointTerm_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {l : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin l ↦ E) ℂ) (k : ℕ)
    (u : ℂ) (s : E) :
    jointTerm q k (fun _ => (u, s)) = u ^ k * q (fun _ => s) := by
  simp [jointTerm, prependFst_apply, sndComp_apply]

/-- Norm bound for `jointTerm`: it does not inflate the operator norm. -/
private theorem jointTerm_norm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {l : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin l ↦ E) ℂ) (k : ℕ) :
    ‖jointTerm q k‖ ≤ ‖q‖ := by
  exact (prependFst_norm k (sndComp q)).trans (sndComp_norm q)

/-- Cast a jointTerm to the correct arity for the N-th coefficient of the joint series.
    For k ≤ N, `jointTerm (q k (N-k)) k` has arity `(N-k) + k`; this casts to arity `N`.
    For k > N, returns 0. -/
private def jointEntry' {m : ℕ} (q : ℕ → FormalMultilinearSeries ℂ (Fin m → ℂ) ℂ)
    (N k : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin N ↦ ℂ × (Fin m → ℂ)) ℂ :=
  if hk : k ≤ N then
    (jointTerm (q k (N - k)) k).domDomCongr (finCongr (Nat.sub_add_cancel hk))
  else 0

/-- Diagonal evaluation of `jointEntry'`: at constant `(u, s)` gives `u^k * (q k (N-k))(s,...,s)`
    when `k ≤ N`. -/
private theorem jointEntry'_apply {m : ℕ} (q : ℕ → FormalMultilinearSeries ℂ (Fin m → ℂ) ℂ)
    (N k : ℕ) (hk : k ≤ N) (u : ℂ) (s : Fin m → ℂ) :
    jointEntry' q N k (fun _ => (u, s)) = u ^ k * (q k (N - k)) (fun _ => s) := by
  simp only [jointEntry', dif_pos hk, ContinuousMultilinearMap.domDomCongr_apply]
  exact jointTerm_apply (q k (N - k)) k u s

/-- Norm bound for `jointEntry'` when `k ≤ N`. -/
private theorem jointEntry'_norm {m : ℕ} (q : ℕ → FormalMultilinearSeries ℂ (Fin m → ℂ) ℂ)
    (N k : ℕ) (hk : k ≤ N) : ‖jointEntry' q N k‖ ≤ ‖q k (N - k)‖ := by
  simp only [jointEntry', dif_pos hk]
  rw [ContinuousMultilinearMap.norm_domDomCongr]
  exact jointTerm_norm (q k (N - k)) k

/-- The joint power series: the N-th coefficient is the antidiagonal sum of `jointEntry'`s. -/
private def jointSeries {m : ℕ} (q : ℕ → FormalMultilinearSeries ℂ (Fin m → ℂ) ℂ) :
    FormalMultilinearSeries ℂ (ℂ × (Fin m → ℂ)) ℂ := fun N =>
  ∑ k ∈ Finset.range (N + 1), jointEntry' q N k

set_option maxHeartbeats 800000 in
-- Prove block_osgood_series by constructing a joint FormalMultilinearSeries and showing
-- it has the right radius and sums to g via antidiagonal rearrangement of a 2D sum.
theorem block_osgood_series {m : ℕ}
    (g : ℂ × (Fin m → ℂ) → ℂ)
    (c : ℕ → (Fin m → ℂ) → ℂ)
    (w₀ : ℂ) (v₀ : Fin m → ℂ)
    (r : ℝ) (hr : 0 < r) (M : ℝ) (hM_nonneg : 0 ≤ M)
    (cauchy_bound : ∀ k, ∀ v ∈ Metric.closedBall v₀ r, ‖c k v‖ ≤ M * r⁻¹ ^ k)
    (cauchy_hasSum : ∀ v ∈ Metric.closedBall v₀ r, ∀ u ∈ Metric.ball (0 : ℂ) r,
      HasSum (fun k => u ^ k * c k v) (g (w₀ + u, v)))
    (q : ℕ → FormalMultilinearSeries ℂ (Fin m → ℂ) ℂ)
    (hq_series : ∀ k, HasFPowerSeriesOnBall (c k) (q k) v₀ (ENNReal.ofReal r))
    (hq_bound : ∀ k l, ‖q k l‖ ≤ M * r⁻¹ ^ (k + l)) :
    AnalyticAt ℂ g (w₀, v₀) := by
  -- We construct a HasFPowerSeriesOnBall for g at (w₀, v₀) with the joint series.
  let p := jointSeries q
  -- The result follows from HasFPowerSeriesOnBall g p (w₀, v₀) (ofReal r).
  suffices h : HasFPowerSeriesOnBall g p (w₀, v₀) (ENNReal.ofReal r) from h.analyticAt
  -- Phase 2: Bound the coefficients ‖p N‖ ≤ (N + 1) * M * r⁻¹ ^ N
  have p_norm : ∀ N, ‖p N‖ ≤ (↑N + 1) * M * r⁻¹ ^ N := by
    intro N
    change ‖∑ k ∈ Finset.range (N + 1), jointEntry' q N k‖ ≤ _
    calc ‖∑ k ∈ Finset.range (N + 1), jointEntry' q N k‖
        ≤ ∑ k ∈ Finset.range (N + 1), ‖jointEntry' q N k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (N + 1), ‖q k (N - k)‖ := by
          gcongr with k hk
          exact jointEntry'_norm q N k (by simp [Finset.mem_range] at hk; omega)
      _ ≤ ∑ k ∈ Finset.range (N + 1), (M * r⁻¹ ^ N) := by
          gcongr with k hk
          have hkN : k ≤ N := by simp [Finset.mem_range] at hk; omega
          calc ‖q k (N - k)‖ ≤ M * r⁻¹ ^ (k + (N - k)) := hq_bound k (N - k)
            _ = M * r⁻¹ ^ N := by rw [Nat.add_sub_cancel' hkN]
      _ = (↑N + 1) * M * r⁻¹ ^ N := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
  -- Phase 3: Show the radius of p is at least r
  have p_radius : ENNReal.ofReal r ≤ p.radius := by
    apply ENNReal.le_of_forall_nnreal_lt
    intro t tr
    rw [← ENNReal.toReal_lt_toReal ENNReal.coe_ne_top ENNReal.ofReal_ne_top] at tr
    rw [ENNReal.coe_toReal, ENNReal.toReal_ofReal hr.le] at tr
    have trn : ‖(t : ℝ) / r‖ < 1 := by
      simp [abs_of_pos hr, div_lt_one hr]; exact tr
    have h_bound_summable : Summable (fun n : ℕ => (↑n + 1) * M * ((t : ℝ) / r) ^ n) := by
      simp_rw [mul_comm _ M, mul_assoc M _ _]
      apply Summable.mul_left M
      simp_rw [right_distrib _ _ _, one_mul]
      exact Summable.add (hasSum_coe_mul_geometric_of_norm_lt_one trn).summable
        (hasSum_geometric_of_norm_lt_one trn).summable
    have h_summable : Summable (fun n : ℕ => ‖p n‖ * (t : ℝ) ^ n) := by
      apply Summable.of_nonneg_of_le (fun n => by positivity)
      · intro n
        calc ‖p n‖ * (t : ℝ) ^ n ≤ (↑n + 1) * M * r⁻¹ ^ n * (t : ℝ) ^ n := by
              gcongr; exact p_norm n
          _ = (↑n + 1) * M * ((t : ℝ) / r) ^ n := by
              rw [mul_assoc ((↑n + 1) * M), ← mul_pow, inv_mul_eq_div]
      · exact h_bound_summable
    exact p.le_radius_of_summable h_summable
  -- Phase 4: Show the series sums to g((w₀, v₀) + y)
  have p_hasSum : ∀ {y : ℂ × (Fin m → ℂ)}, y ∈ EMetric.ball (0 : ℂ × (Fin m → ℂ))
      (ENNReal.ofReal r) →
      HasSum (fun n => p n fun _ => y) (g ((w₀, v₀) + y)) := by
    intro ⟨u, s⟩ hus
    -- Simplify Prod.mk_add_mk in the goal
    change HasSum (fun n => (p n) fun _ => (u, s)) (g (w₀ + u, v₀ + s))
    -- Step 1: Compute (p N)(fun _ => (u,s)) = ∑_{k ≤ N} u^k * (q k (N-k))(fun _ => s)
    have p_apply : ∀ N, (p N) (fun _ => (u, s)) =
        ∑ k ∈ Finset.range (N + 1), u ^ k * (q k (N - k)) (fun _ => s) := by
      intro N
      change (∑ k ∈ Finset.range (N + 1), jointEntry' q N k) (fun _ => (u, s)) = _
      rw [ContinuousMultilinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro k hk
      simp [Finset.mem_range] at hk
      exact jointEntry'_apply q N k (by omega) u s
    -- Step 2: Show v₀ + s ∈ closedBall v₀ r and u ∈ ball 0 r
    have hus_norm : ‖(u, s)‖ < r := by
      have : edist (u, s) 0 < ENNReal.ofReal r := hus
      rwa [edist_eq_enorm_sub, sub_zero, ← ofReal_norm_eq_enorm,
        ENNReal.ofReal_lt_ofReal_iff hr] at this
    rw [Prod.norm_def] at hus_norm
    have hu_lt : ‖u‖ < r := lt_of_le_of_lt (le_max_left _ _) hus_norm
    have hs_lt : ‖s‖ < r := lt_of_le_of_lt (le_max_right _ _) hus_norm
    have hu_ball : u ∈ Metric.ball (0 : ℂ) r := by rwa [Metric.mem_ball, dist_zero_right]
    have hs_closedBall : v₀ + s ∈ Metric.closedBall v₀ r := by
      rw [Metric.mem_closedBall, dist_comm]; simp [dist_eq_norm]; linarith
    -- Step 3: The inner and outer HasSum
    have inner_hasSum : ∀ k, HasSum (fun l => (q k l) (fun _ => s)) (c k (v₀ + s)) := by
      intro k
      have hs_eball : s ∈ Metric.eball (0 : Fin m → ℂ) (ENNReal.ofReal r) := by
        rw [Metric.mem_eball, edist_eq_enorm_sub, sub_zero,
          ← ofReal_norm_eq_enorm, ENNReal.ofReal_lt_ofReal_iff hr]
        exact hs_lt
      exact (hq_series k).hasSum hs_eball
    have outer_hasSum : HasSum (fun k => u ^ k * c k (v₀ + s)) (g (w₀ + u, v₀ + s)) :=
      cauchy_hasSum (v₀ + s) hs_closedBall u hu_ball
    -- Step 4: Absolute convergence of the 2D sum
    have h_summable : Summable (fun (kl : ℕ × ℕ) => u ^ kl.1 * (q kl.1 kl.2) (fun _ => s)) := by
      apply Summable.of_norm
      have h_le_opNorm : ∀ k l, ‖(q k l) (fun _ => s)‖ ≤ ‖q k l‖ * ‖s‖ ^ l := by
        intro k l
        calc ‖(q k l) (fun _ => s)‖ ≤ ‖q k l‖ * ∏ i : Fin l, ‖s‖ :=
              (q k l).le_opNorm _
          _ = ‖q k l‖ * ‖s‖ ^ l := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have h_norm_bound : ∀ kl : ℕ × ℕ, ‖u ^ kl.1 * (q kl.1 kl.2) (fun _ => s)‖ ≤
          M * (‖u‖ * r⁻¹) ^ kl.1 * (‖s‖ * r⁻¹) ^ kl.2 := by
        intro ⟨k, l⟩
        calc ‖u ^ k * (q k l) (fun _ => s)‖
            ≤ ‖u‖ ^ k * ‖(q k l) (fun _ => s)‖ := by rw [norm_mul, norm_pow]
          _ ≤ ‖u‖ ^ k * (‖q k l‖ * ‖s‖ ^ l) := by gcongr; exact h_le_opNorm k l
          _ ≤ ‖u‖ ^ k * (M * r⁻¹ ^ (k + l) * ‖s‖ ^ l) := by gcongr; exact hq_bound k l
          _ = M * (‖u‖ * r⁻¹) ^ k * (‖s‖ * r⁻¹) ^ l := by rw [pow_add]; ring
      have hα : ‖u‖ * r⁻¹ < 1 := by rwa [mul_inv_lt_iff₀ hr, one_mul]
      have hβ : ‖s‖ * r⁻¹ < 1 := by rwa [mul_inv_lt_iff₀ hr, one_mul]
      -- The bound M * α^k * β^l = (M * α^k) * β^l is summable as a product
      -- of separately summable series (over k and l).
      have h_bound_summable : Summable (fun kl : ℕ × ℕ =>
          M * (‖u‖ * r⁻¹) ^ kl.1 * (‖s‖ * r⁻¹) ^ kl.2) := by
        -- Rewrite as (fun (k,l) => f(k) * g(l)) where f, g are geometric
        let f : ℕ → ℝ := fun k => M * (‖u‖ * r⁻¹) ^ k
        let g' : ℕ → ℝ := fun l => (‖s‖ * r⁻¹) ^ l
        have hfg : (fun kl : ℕ × ℕ => M * (‖u‖ * r⁻¹) ^ kl.1 * (‖s‖ * r⁻¹) ^ kl.2) =
            (fun kl : ℕ × ℕ => f kl.1 * g' kl.2) := by ext; ring
        rw [hfg]
        exact Summable.mul_of_nonneg
          ((summable_geometric_of_lt_one (by positivity) hα).mul_left M)
          (summable_geometric_of_lt_one (by positivity) hβ)
          (fun _ => by positivity) (fun _ => by positivity)
      exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_norm_bound h_bound_summable
    -- Step 5: Construct 2D HasSum from summability + fiber sums + uniqueness
    have h_fiber : ∀ k, HasSum (fun l => u ^ k * (q k l) (fun _ => s))
        (u ^ k * c k (v₀ + s)) := fun k => (inner_hasSum k).mul_left (u ^ k)
    have h_outer := h_summable.hasSum.prod_fiberwise h_fiber
    have h_eq := h_outer.unique outer_hasSum
    have two_d_hasSum : HasSum (fun (kl : ℕ × ℕ) => u ^ kl.1 * (q kl.1 kl.2) (fun _ => s))
        (g (w₀ + u, v₀ + s)) := h_eq ▸ h_summable.hasSum
    -- Step 6: Rearrange to antidiagonal form
    have antidiag := two_d_hasSum.antidiagonal_of_2d
    simp only at antidiag
    simp_rw [p_apply]
    exact antidiag
  exact { r_le := p_radius, r_pos := by simp [hr], hasSum := p_hasSum }

/-- Cauchy estimate for the first Fréchet derivative: if `G : E → F` is differentiable
and `‖G(x)‖ ≤ C` on `Metric.closedBall x₀ r`, then `‖fderiv ℂ G x₀‖ ≤ C / r`.
Proved by reducing to the 1D Cauchy estimate along each direction. -/
private theorem norm_fderiv_le_of_forall_closedBall_norm_le
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {G : E → F} {x₀ : E} {r C : ℝ} (hr : 0 < r)
    (hG_diff : Differentiable ℂ G)
    (hG_bound : ∀ x ∈ Metric.closedBall x₀ r, ‖G x‖ ≤ C) :
    ‖fderiv ℂ G x₀‖ ≤ C / r := by
  rw [ContinuousLinearMap.opNorm_le_iff (div_nonneg
    (le_trans (norm_nonneg _) (hG_bound x₀ (Metric.mem_closedBall_self hr.le))) hr.le)]
  intro v
  -- For v = 0, the bound is trivial
  by_cases hv : v = 0
  · simp [hv, div_nonneg (le_trans (norm_nonneg _)
      (hG_bound x₀ (Metric.mem_closedBall_self hr.le))) hr.le]
  -- For v ≠ 0, reduce to the 1D Cauchy estimate along the direction v/‖v‖
  -- Consider the 1D slice g(z) = G(x₀ + z • v) for z ∈ ℂ
  -- g'(0) = (fderiv ℂ G x₀) v
  set g : ℂ → F := fun z => G (x₀ + z • v) with hg_def
  have hg_diff : Differentiable ℂ g :=
    hG_diff.comp ((differentiable_const x₀).add ((differentiable_id).smul_const v))
  have hg_deriv : deriv g 0 = fderiv ℂ G x₀ v := by
    have hι : HasDerivAt (fun z : ℂ => x₀ + z • v) v 0 := by
      have h1 : HasDerivAt (fun z : ℂ => z • v) ((1 : ℂ) • v) 0 :=
        (hasDerivAt_id (0 : ℂ)).smul_const v
      simp only [one_smul] at h1
      have h2 := (hasDerivAt_const 0 x₀).add h1
      simp only [zero_add] at h2; exact h2
    have hcomp := (hG_diff (x₀ + 0 • v)).hasFDerivAt.comp_hasDerivAt 0 hι
    simp only [zero_smul, add_zero] at hcomp
    exact hcomp.deriv
  -- Bound: |g'(0)| ≤ C/r * ‖v‖ via the 1D Cauchy estimate on the disk of radius r/‖v‖
  -- Actually, we use the disk of radius r/‖v‖ so that ‖z•v‖ = |z|*‖v‖ ≤ r when |z| ≤ r/‖v‖
  set R' := r / ‖v‖ with hR'_def
  have hR' : 0 < R' := div_pos hr (norm_pos_iff.mpr hv)
  have hg_sphere : ∀ z ∈ Metric.sphere (0 : ℂ) R', ‖g z‖ ≤ C := by
    intro z hz
    apply hG_bound
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
    calc ‖z • v‖ = ‖z‖ * ‖v‖ := norm_smul z v
      _ = R' * ‖v‖ := by rw [hz]
      _ ≤ r := by rw [hR'_def, div_mul_cancel₀ r (norm_ne_zero_iff.mpr hv)]
  have : ‖deriv g 0‖ ≤ C / R' :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR' hg_diff.diffContOnCl hg_sphere
  rw [hg_deriv] at this
  calc ‖(fderiv ℂ G x₀) v‖ ≤ C / R' := this
    _ = C / (r / ‖v‖) := rfl
    _ = C * ‖v‖ / r := by rw [div_div_eq_mul_div]
    _ = C / r * ‖v‖ := by ring

/-- Iterated multivariate Cauchy estimate: if `f : E → ℂ` is smooth and `‖f(x)‖ ≤ B` on
`Metric.closedBall x₀ R`, then `(n!)⁻¹ * ‖iteratedFDeriv ℂ n f x₀‖ ≤ B * (e/R)^n`.
Proved by induction: at each step the 1D Cauchy estimate for fderiv gives
`‖D^{k+1}f(x)‖ ≤ sup ‖D^k f‖ / (R/n)`, yielding `‖D^n f(x₀)‖ ≤ B * (n/R)^n`.
Then `(n!)⁻¹ * B * (n/R)^n = B * n^n/(n! R^n) ≤ B * e^n/R^n` by `pow_div_factorial_le_exp`. -/
private theorem norm_iteratedFDeriv_div_factorial_le
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : E → ℂ} {x₀ : E}
    (hf_smooth : ContDiff ℂ ⊤ f)
    {R : ℝ} (hR : 0 < R) {B : ℝ}
    (hB : ∀ x ∈ Metric.closedBall x₀ R, ‖f x‖ ≤ B)
    (n : ℕ) :
    (↑(n.factorial) : ℝ)⁻¹ * ‖iteratedFDeriv ℂ n f x₀‖ ≤ B * (R / Real.exp 1)⁻¹ ^ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [iteratedFDeriv_zero_apply, hB x₀ (Metric.mem_closedBall_self hR.le)]
  have hB_nn : 0 ≤ B := le_trans (norm_nonneg _) (hB x₀ (Metric.mem_closedBall_self hR.le))
  have hRn : (0 : ℝ) < R / n := div_pos hR (Nat.cast_pos.mpr hn)
  -- Key: ∀ k ≤ n, ∀ x ∈ closedBall x₀ (R - k*(R/n)),
  --   ‖iteratedFDeriv ℂ k f x‖ ≤ B * (n/R)^k
  -- Note: NO k! factor. The operator norm bound at each step only introduces n/R.
  suffices key : ∀ k : ℕ, k ≤ n →
      ∀ x ∈ Metric.closedBall x₀ (R - ↑k * (R / ↑n)),
        ‖iteratedFDeriv ℂ k f x‖ ≤ B * (↑n / R) ^ k by
    have h_at_x₀ := key n le_rfl x₀ (by
      rw [Metric.mem_closedBall, dist_self]
      have : (↑n : ℝ) * (R / ↑n) = R :=
        mul_div_cancel₀ R (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn))
      linarith)
    -- Now: (n!)⁻¹ * ‖D^n f(x₀)‖ ≤ (n!)⁻¹ * B * (n/R)^n = B * n^n / (n! * R^n)
    -- And n^n / n! ≤ e^n by pow_div_factorial_le_exp
    -- (n!)⁻¹ * B * (n/R)^n = B * n^n / (n! * R^n) ≤ B * exp(n) / R^n
    --   = B * (exp 1)^n / R^n = B * (exp 1 / R)^n = B * ρ⁻¹^n
    have hfact_pos : (0 : ℝ) < ↑(n.factorial) := Nat.cast_pos.mpr n.factorial_pos
    have hRn_pos : (0 : ℝ) < R ^ n := pow_pos hR n
    -- Key: n^n / n! ≤ exp n
    have h_key : (↑n : ℝ) ^ n / ↑(n.factorial) ≤ Real.exp ↑n :=
      Real.pow_div_factorial_le_exp (x := ↑n) (Nat.cast_nonneg n) n
    -- exp n = (exp 1)^n
    have h_exp : Real.exp (↑n : ℝ) = Real.exp 1 ^ n := by
      rw [← Real.exp_nat_mul, mul_one]
    calc (↑(n.factorial) : ℝ)⁻¹ * ‖iteratedFDeriv ℂ n f x₀‖
        ≤ (↑(n.factorial))⁻¹ * (B * (↑n / R) ^ n) := by gcongr
      _ = B * ((↑n) ^ n / (↑(n.factorial))) / R ^ n := by
          rw [div_pow]; ring
      _ ≤ B * Real.exp (↑n) / R ^ n := by
          gcongr
      _ = B * (Real.exp 1 ^ n / R ^ n) := by
          rw [h_exp, mul_div_assoc]
      _ = B * (R / Real.exp 1)⁻¹ ^ n := by
          rw [inv_div, div_pow]
  intro k hk
  induction k with
  | zero =>
    intro x hx
    simp only [Nat.zero_eq, CharP.cast_eq_zero, zero_mul, sub_zero, pow_zero, mul_one] at hx ⊢
    rw [norm_iteratedFDeriv_zero]; exact hB x hx
  | succ k ih =>
    intro x hx
    rw [← norm_fderiv_iteratedFDeriv]
    have h_ball_sub : Metric.closedBall x (R / ↑n) ⊆
        Metric.closedBall x₀ (R - ↑k * (R / ↑n)) := by
      intro y hy
      rw [Metric.mem_closedBall] at hx hy ⊢
      calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle y x x₀
        _ ≤ R / ↑n + (R - ↑(k + 1) * (R / ↑n)) := add_le_add hy hx
        _ = R - ↑k * (R / ↑n) := by push_cast; ring
    have ih_on_ball : ∀ y ∈ Metric.closedBall x (R / ↑n),
        ‖iteratedFDeriv ℂ k f y‖ ≤ B * (↑n / R) ^ k :=
      fun y hy => ih (Nat.le_of_succ_le hk) y (h_ball_sub hy)
    calc ‖fderiv ℂ (iteratedFDeriv ℂ k f) x‖
        ≤ (B * (↑n / R) ^ k) / (R / ↑n) := by
          exact norm_fderiv_le_of_forall_closedBall_norm_le hRn
            (hf_smooth.differentiable_iteratedFDeriv (m := k)
              (show ((k : ℕ) : WithTop ℕ∞) < ⊤ by simp))
            ih_on_ball
      _ = B * (↑n / R) ^ (k + 1) := by
          rw [pow_succ]; field_simp

set_option maxHeartbeats 1600000 in
/-- **Multivariate Cauchy estimate with polarization loss.**

If `f` is analytic on all of `E` and `‖f(x)‖ ≤ B` for all `x ∈ closedBall x₀ R` (with `R > 0`),
then there exists a power series for `f` at `x₀` with radius at least `R / e` and Cauchy
coefficient bound `‖p n‖ ≤ B * (R / e)⁻¹ ^ n`, where `e = Real.exp 1`.

The proof uses the symmetrized power series `q n = (1/n!) iteratedFDeriv ℂ n f x₀`, bounded
via the iterated 1D Cauchy estimate: for unit vectors `v₁,...,vₙ`, the mixed derivative
`∂ₜ₁...∂ₜₙ f(x₀ + Σ tⱼvⱼ)|₀` is bounded by `B (n/R)ⁿ` (using the polydisk of radius `R/n`),
giving `‖q n‖ ≤ B nⁿ/(n! Rⁿ) ≤ B (e/R)ⁿ`. -/
theorem analyticAt_hasFPowerSeriesOnBall_of_bound
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : E → ℂ} {x₀ : E}
    (hf : AnalyticOnNhd ℂ f Set.univ)
    {R : ℝ} (hR : 0 < R) {B : ℝ}
    (hB : ∀ x ∈ Metric.closedBall x₀ R, ‖f x‖ ≤ B) :
    ∃ p : FormalMultilinearSeries ℂ E ℂ,
      HasFPowerSeriesOnBall f p x₀ (ENNReal.ofReal (R / Real.exp 1)) ∧
      ∀ n, ‖p n‖ ≤ B * (R / Real.exp 1)⁻¹ ^ n := by
  -- Step 0: Basic setup
  have hf_at : AnalyticAt ℂ f x₀ := hf x₀ (Set.mem_univ _)
  obtain ⟨p₀, r₀, hfp₀⟩ := hf_at
  set ρ := R / Real.exp 1 with hρ_def
  have hρ : (0 : ℝ) < ρ := div_pos hR (Real.exp_pos 1)
  have hB_nn : 0 ≤ B := le_trans (norm_nonneg _) (hB x₀ (Metric.mem_closedBall_self hR.le))
  -- Step 1: Define the symmetrized power series q using iteratedFDeriv.
  -- q n = (↑(n !)⁻¹ : ℂ) • iteratedFDeriv ℂ n f x₀
  -- We need f to be ContDiff ℂ ⊤ for iteratedFDeriv to be well-defined.
  have hf_smooth : ContDiff ℂ ⊤ f := hf.contDiff
  -- Define the symmetrized series
  let q : FormalMultilinearSeries ℂ E ℂ :=
    fun n => ((Nat.factorial n : ℝ)⁻¹) • iteratedFDeriv ℂ n f x₀
  -- Step 2: q has the same diagonal as p₀, and q represents f.
  -- From iteratedFDeriv_eq_sum_of_completeSpace:
  -- iteratedFDeriv ℂ n f x₀ = Σ_σ (p₀ n) ∘ σ
  -- So for diagonal (y,...,y): iteratedFDeriv(y,...,y) = n! · (p₀ n)(y,...,y)
  -- Hence (q n)(y,...,y) = (1/n!) · n! · (p₀ n)(y,...,y) = (p₀ n)(y,...,y).
  --
  -- q represents f since Σ (q n)(y,...,y) = Σ (p₀ n)(y,...,y) = f(x₀ + y).
  -- Step 3: Coefficient bound via iterated 1D Cauchy estimate.
  -- For unit v₁,...,vₙ, the 1D restriction z ↦ f(x₀ + z·v) is bounded by B on |z| ≤ R.
  -- By the multivariate Cauchy estimate on the iterated derivative:
  -- ‖(iteratedFDeriv ℂ n f x₀)(v₁,...,vₙ)‖ ≤ B · (n/R)ⁿ
  -- Hence ‖q n‖ = (1/n!) ‖iteratedFDeriv ℂ n f x₀‖ ≤ B · nⁿ/(n! · Rⁿ) ≤ B · (e/R)ⁿ.
  --
  -- The bound B · (e/R)ⁿ = B · ρ⁻¹ⁿ follows from nⁿ/n! ≤ eⁿ (pow_div_factorial_le_exp).
  have coeff_bound : ∀ n, ‖q n‖ ≤ B * ρ⁻¹ ^ n := by
    intro n
    -- ‖q n‖ = (n!)⁻¹ * ‖iteratedFDeriv ℂ n f x₀‖
    show ‖((Nat.factorial n : ℝ)⁻¹) • iteratedFDeriv ℂ n f x₀‖ ≤ B * ρ⁻¹ ^ n
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
    exact norm_iteratedFDeriv_div_factorial_le hf_smooth hR hB n
  -- Step 4: q.radius ≥ ρ (from coeff_bound)
  have q_radius : ENNReal.ofReal ρ ≤ q.radius := by
    have h_bound : ∀ n, ‖q n‖ * ρ ^ n ≤ B := by
      intro n
      calc ‖q n‖ * ρ ^ n
          ≤ B * ρ⁻¹ ^ n * ρ ^ n := by gcongr; exact coeff_bound n
        _ = B := by rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hρ.ne', one_pow, mul_one]
    rw [ENNReal.ofReal_eq_coe_nnreal hρ.le]
    exact q.le_radius_of_bound B (fun n => h_bound n)
  -- Step 5: HasFPowerSeriesOnBall f q x₀ ρ
  -- The diagonal of q equals the diagonal of p₀, so q sums to f.
  -- We show hasSum by the identity theorem.
  have h_series : HasFPowerSeriesOnBall f q x₀ (ENNReal.ofReal ρ) := by
    have hq_pos : 0 < q.radius := lt_of_lt_of_le (by positivity : (0 : ℝ≥0∞) < ENNReal.ofReal ρ) q_radius
    -- q.sum represents q on eball 0 q.radius
    have hq_fps : HasFPowerSeriesOnBall q.sum q 0 q.radius := q.hasFPowerSeriesOnBall hq_pos
    -- On a neighborhood of 0, f(x₀ + y) = q.sum y
    -- This follows from hfp₀.hasSum_iteratedFDeriv:
    --   HasSum (fun n => (n!)⁻¹ • iteratedFDeriv ℂ n f x₀ (fun _ => y)) (f(x₀ + y))
    -- for y ∈ eball 0 r₀, and q n (fun _ => y) = (n!)⁻¹ • iteratedFDeriv(fun _ => y).
    have h_eq_near : ∀ y ∈ Metric.eball (0 : E) r₀, f (x₀ + y) = q.sum y := by
      intro y hy
      have h_hasSum := hfp₀.hasSum_iteratedFDeriv hy
      -- h_hasSum : HasSum (fun n => (↑n!)⁻¹ • iteratedFDeriv ℂ n f x₀ (fun _ => y)) (f(x₀ + y))
      -- q.sum y = tsum (fun n => q n (fun _ => y))
      -- q n (fun _ => y) = ((n! : ℝ)⁻¹ • iteratedFDeriv ℂ n f x₀) (fun _ => y)
      --                    = (n! : ℝ)⁻¹ • iteratedFDeriv ℂ n f x₀ (fun _ => y)
      -- and (↑n!)⁻¹ • v = ((n! : ℂ)⁻¹ : ℂ) • v for v : ℂ
      -- We need to match the ℝ-scalar and ℂ-scalar versions.
      have h_term_eq : ∀ n, q n (fun _ => y) = (↑(n.factorial) : ℂ)⁻¹ • iteratedFDeriv ℂ n f x₀ (fun _ => y) := by
        intro n
        -- q n = (↑(n!))⁻¹ • (iteratedFDeriv ℂ n f x₀) where scalar is ℝ
        -- Need: (r • M) v = (↑r : ℂ) • (M v) for r : ℝ, M : ContinuousMultilinearMap, v
        change ((Nat.factorial n : ℝ)⁻¹ • iteratedFDeriv ℂ n f x₀) (fun _ => y) =
          (↑(n.factorial) : ℂ)⁻¹ • iteratedFDeriv ℂ n f x₀ (fun _ => y)
        rw [show (((Nat.factorial n : ℝ)⁻¹ • iteratedFDeriv ℂ n f x₀) (fun _ => y)) =
          ((Nat.factorial n : ℝ)⁻¹ : ℝ) • (iteratedFDeriv ℂ n f x₀ (fun _ => y)) from rfl]
        rw [Complex.real_smul]
        congr 1
        simp [map_inv₀, map_natCast]
      rw [← h_hasSum.tsum_eq]
      congr 1; ext n; exact (h_term_eq n).symm
    -- Now use the identity theorem: f(x₀ + ·) and q.sum agree on eball 0 r₀,
    -- both are analytic on eball 0 (ofReal ρ), and this set is preconnected.
    refine ⟨q_radius, by positivity, fun {y} hy => ?_⟩
    -- We need HasSum (fun n => q n (fun _ => y)) (f (x₀ + y))
    -- equivalently f(x₀ + y) = q.sum y
    suffices h_eq : f (x₀ + y) = q.sum y by
      rw [h_eq]
      have := (hq_fps.mono (by positivity) q_radius).hasSum hy
      simpa [zero_add] using this
    -- Apply identity theorem
    -- Both f(x₀ + ·) and q.sum are analytic on the ball eball 0 q.radius
    have h_f_an : AnalyticOnNhd ℂ (fun y => f (x₀ + y)) (Metric.eball 0 q.radius) := by
      intro y _
      have : AnalyticAt ℂ (fun y => x₀ + y) y :=
        (analyticAt_const.add analyticAt_id)
      exact (hf (x₀ + y) (Set.mem_univ _)).comp_of_eq this rfl
    have h_q_an : AnalyticOnNhd ℂ q.sum (Metric.eball 0 q.radius) :=
      hq_fps.analyticOnNhd
    have h_agree : (fun y => f (x₀ + y)) =ᶠ[𝓝 0] q.sum := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      exact ⟨Metric.eball 0 r₀, Metric.eball_mem_nhds 0 hfp₀.r_pos, fun y hy => h_eq_near y hy⟩
    -- The ball eball 0 q.radius is preconnected
    have h_preconn : IsPreconnected (Metric.eball (0 : E) q.radius) :=
      (convex_eball (0 : E) q.radius).isPreconnected
    have h_0_mem : (0 : E) ∈ Metric.eball (0 : E) q.radius := Metric.mem_eball_self hq_pos
    have h_y_mem : y ∈ Metric.eball (0 : E) q.radius := Metric.eball_subset_eball q_radius hy
    exact h_f_an.eqOn_of_preconnected_of_eventuallyEq
      h_q_an h_preconn h_0_mem h_agree h_y_mem
  exact ⟨q, h_series, coeff_bound⟩

set_option maxHeartbeats 800000 in
/-- **Block Osgood lemma** using Cauchy coefficients.
Given `g : ℂ × (Fin m → ℂ) → ℂ` that is continuous, analytic in `w` for each
`v`, and jointly analytic in `v` for each `w`, `g` is jointly analytic.
Uses `osgood_m` (Osgood at dimension `m`) to show the Cauchy coefficients are
analytic. -/
private theorem block_osgood {m : ℕ}
    (osgood_m : ∀ {h : (Fin m → ℂ) → ℂ},
      Continuous h →
      (∀ (j : Fin m) (z₀ : Fin m → ℂ),
        AnalyticAt ℂ (fun t : ℂ => h (update z₀ j t)) (z₀ j)) →
      AnalyticOnNhd ℂ h Set.univ)
    {g : ℂ × (Fin m → ℂ) → ℂ}
    (g_cont : Continuous g)
    (g_an_w : ∀ v w, AnalyticAt ℂ (fun w => g (w, v)) w)
    (g_an_v : ∀ w v, AnalyticAt ℂ (fun v => g (w, v)) v) :
    AnalyticOnNhd ℂ g Set.univ := by
  intro ⟨w₀, v₀⟩ _
  -- The 1D Cauchy expansion in w, with coefficients that depend on v.
  -- The coefficients are analytic in v by osgood_m.
  -- We combine the 1D w-series with the multi-dimensional v-series.

  -- Step 1: Set up the 1D power series in w for each fixed v.
  -- For each v, w ↦ g(w, v) is analytic, so it has a power series at w₀.
  -- The Cauchy integral formula on a circle of radius r gives the coefficients.

  -- Step 2: Choose r > 0 with g bounded.
  obtain ⟨r, hr_pos, M, _, hM_bound⟩ : ∃ r > 0, ∃ M > 0,
      ∀ w v, w ∈ closedBall w₀ r → v ∈ closedBall v₀ r → ‖g (w, v)‖ ≤ M := by
    have hc : ContinuousAt g (w₀, v₀) := g_cont.continuousAt
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, hδ, hδ_bound⟩ := hc 1 one_pos
    refine ⟨δ / 2, by linarith, ‖g (w₀, v₀)‖ + 1, by positivity, ?_⟩
    intro w v hw hv
    have hdist : dist (w, v) (w₀, v₀) < δ := by
      rw [Prod.dist_eq]
      apply max_lt
      · exact lt_of_le_of_lt (mem_closedBall.mp hw) (by linarith)
      · exact lt_of_le_of_lt (mem_closedBall.mp hv) (by linarith)
    have := hδ_bound hdist
    calc ‖g (w, v)‖ = ‖g (w₀, v₀) + (g (w, v) - g (w₀, v₀))‖ := by ring_nf
      _ ≤ ‖g (w₀, v₀)‖ + ‖g (w, v) - g (w₀, v₀)‖ := norm_add_le _ _
      _ = ‖g (w₀, v₀)‖ + dist (g (w, v)) (g (w₀, v₀)) := by rw [dist_eq_norm]
      _ ≤ ‖g (w₀, v₀)‖ + 1 := by linarith

  -- Step 3: For each v, w ↦ g(w,v) is entire (analytic everywhere), hence differentiable.
  have g_diff_w : ∀ v, Differentiable ℂ (fun w => g (w, v)) :=
    fun v w => (g_an_w v w).differentiableAt
  -- Step 4: Each c_k is analytic in v. The Cauchy coefficient
  --   c_k(v) = (2πi)⁻¹ ∮ g(ζ,v) (ζ-w₀)^{-(k+1)} dζ
  -- is continuous (from joint continuity of g) and separately analytic in each v_j
  -- (differentiation under the integral sign: t ↦ g(ζ, update v₀' j t) is entire for
  -- each ζ, so the integral is differentiable in t, hence analytic).
  -- By osgood_m: continuous + separately analytic → jointly analytic.
  --
  -- Strategy: we show c_k is analytic at EVERY point, so AnalyticOnNhd on Set.univ.
  -- Then we assemble the joint power series from the 1D Cauchy series in w and
  -- the m-dimensional series of each c_k.

  -- We use osgood_at from Osgood2.lean: for each pair (w, v_j), the 2-variable
  -- restriction of g is jointly analytic. This gives separate analyticity
  -- in all m+1 scalar coordinates. With continuity, we need Osgood at dim m+1,
  -- which we don't have. Instead, we use the Cauchy coefficient route.

  -- For the coefficient analyticity, we note that for each ζ on the circle,
  -- v ↦ g(ζ, v) is analytic (given by g_an_v). The Cauchy coefficient is:
  --   c_k(v) = CLE applied to ∫ (analytic-in-v integrand) dθ
  -- We show this is analytic using osgood_m after proving continuity and
  -- separate analyticity via differentiation under the integral.

  -- Step 4a: Separate analyticity of the Cauchy coefficient c_k in each v_j.
  -- We show: for each j and v₀', the function t ↦ c_k(update v₀' j t)
  -- is differentiable on ℂ, hence analytic by Differentiable.analyticAt.
  -- This uses parametric differentiation (hasDerivAt_integral_of_dominated_loc_of_deriv_le).

  -- Define c_k(v) = (2πi)⁻¹ ∮ g(ζ,v) (ζ-w₀)^{-(k+1)} dζ
  let c : ℕ → (Fin m → ℂ) → ℂ := fun k v =>
    (2 * ↑π * I)⁻¹ • ∮ z in C(w₀, r), (z - w₀)⁻¹ ^ k • (z - w₀)⁻¹ • g (z, v)

  -- c_k is analytic at every point, by osgood_m (continuous + separately analytic)
  have c_an : ∀ k, AnalyticOnNhd ℂ (c k) Set.univ := by
    intro k
    apply osgood_m
    · -- Continuity of c_k: the circle integral is an interval integral
      -- ∫ θ in 0..2π, H(v, θ) dθ where H(v, θ) involves circleMap values (hence z-w₀ ≠ 0).
      show Continuous (c k)
      apply Continuous.smul continuous_const
      -- Rewrite as interval integral
      show Continuous (fun v => ∫ θ in (0 : ℝ)..(2 * π), deriv (circleMap w₀ r) θ •
        ((circleMap w₀ r θ - w₀)⁻¹ ^ k • (circleMap w₀ r θ - w₀)⁻¹ • g (circleMap w₀ r θ, v)))
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      -- Uncurried integrand (v, θ) ↦ ... is continuous
      show Continuous (fun p : (Fin m → ℂ) × ℝ => deriv (circleMap w₀ r) p.2 •
        ((circleMap w₀ r p.2 - w₀)⁻¹ ^ k • (circleMap w₀ r p.2 - w₀)⁻¹ •
          g (circleMap w₀ r p.2, p.1)))
      apply Continuous.smul
      · simp_rw [deriv_circleMap]
        exact ((continuous_circleMap 0 r).comp continuous_snd).mul continuous_const
      · -- The key: circleMap w₀ r θ - w₀ ≠ 0 since r > 0
        have hne : ∀ θ : ℝ, circleMap w₀ r θ - w₀ ≠ 0 :=
          fun θ => sub_ne_zero.mpr (circleMap_ne_center hr_pos.ne')
        have hcm_inv : Continuous (fun θ : ℝ => (circleMap w₀ r θ - w₀)⁻¹) :=
          ((continuous_circleMap w₀ r).sub continuous_const).inv₀ hne
        exact (hcm_inv.comp continuous_snd).pow _ |>.smul
          ((hcm_inv.comp continuous_snd).smul
            (g_cont.comp (((continuous_circleMap w₀ r).comp continuous_snd).prodMk
              continuous_fst)))
    · -- Separate analyticity in each coordinate of v
      intro j v₀'
      -- t ↦ c_k(update v₀' j t) is differentiable ⟹ analytic
      suffices h : Differentiable ℂ (fun t => c k (update v₀' j t)) from
        h.analyticAt (v₀' j)
      -- c_k(update v₀' j t) = (2πi)⁻¹ • ∮ (z-w₀)^{-(k+1)} g(z, update v₀' j t) dz
      -- Factor out the (2πi)⁻¹ scalar to avoid kernel isDefEq timeout
      -- Factor out (2πi)⁻¹ to avoid kernel isDefEq timeout
      change Differentiable ℂ (((2 * ↑π * I)⁻¹ : ℂ) • fun t =>
        ∮ z in C(w₀, r), (z - w₀)⁻¹ ^ k • (z - w₀)⁻¹ • g (z, update v₀' j t))
      apply Differentiable.const_smul
      -- The circle integral is ∫ θ in 0..2π, H(t, θ) dθ where H involves circleMap
      -- Use differentiable_intervalIntegral_param
      show Differentiable ℂ (fun t => ∫ θ in (0 : ℝ)..(2 * π),
        deriv (circleMap w₀ r) θ •
          ((circleMap w₀ r θ - w₀)⁻¹ ^ k • (circleMap w₀ r θ - w₀)⁻¹ •
            g (circleMap w₀ r θ, update v₀' j t)))
      have hne : ∀ θ : ℝ, circleMap w₀ r θ - w₀ ≠ 0 :=
        fun θ => sub_ne_zero.mpr (circleMap_ne_center hr_pos.ne')
      apply differentiable_intervalIntegral_param
      · -- Joint continuity of (t, θ) ↦ H(t, θ)
        apply Continuous.smul
        · show Continuous (fun p : ℂ × ℝ => deriv (circleMap w₀ r) p.2)
          simp_rw [deriv_circleMap]
          exact ((continuous_circleMap 0 r).comp continuous_snd).mul continuous_const
        · apply Continuous.smul
          · exact (((continuous_circleMap w₀ r).sub continuous_const).comp continuous_snd).inv₀
              (fun p => hne p.2) |>.pow _
          · exact ((((continuous_circleMap w₀ r).sub continuous_const).comp continuous_snd).inv₀
              (fun p => hne p.2)).smul
              (g_cont.comp (((continuous_circleMap w₀ r).comp continuous_snd).prodMk
                (continuous_const.update j continuous_fst)))
      · -- Differentiability in t for each θ (all θ-dependent factors are constant in t)
        intro θ t
        refine DifferentiableAt.const_smul (𝕜 := ℂ) ?_ (deriv (circleMap w₀ r) θ)
        refine DifferentiableAt.const_smul (𝕜 := ℂ) ?_ ((circleMap w₀ r θ - w₀)⁻¹ ^ k)
        refine DifferentiableAt.const_smul (𝕜 := ℂ) ?_ ((circleMap w₀ r θ - w₀)⁻¹)
        exact ((g_an_v (circleMap w₀ r θ) (update v₀' j t)).comp
          (analyticAt_update' v₀' j t)).differentiableAt

  -- Step 5: Assemble the joint power series.
  -- We use the Cauchy series g(w₀ + u, v) = Σ_k c_k(v) · u^k (convergent for |u| < r)
  -- together with analyticity of each c_k to build a HasFPowerSeriesOnBall for g.

  -- Step 5a: Establish the Cauchy bound on c_k.
  -- For v ∈ closedBall v₀ r: |c_k(v)| ≤ M / r^k
  have cauchy_bound : ∀ k, ∀ v ∈ closedBall v₀ r, ‖c k v‖ ≤ M * r⁻¹ ^ k := by
    intro k v hv
    -- c_k(v) = (2πi)⁻¹ ∮ (z-w₀)⁻¹^k (z-w₀)⁻¹ g(z,v) dz on circle |z-w₀| = r
    -- The integrand is bounded by M r⁻ᵏ r⁻¹ on the circle
    show ‖(2 * ↑π * I)⁻¹ • ∮ z in C(w₀, r), (z - w₀)⁻¹ ^ k • (z - w₀)⁻¹ • g (z, v)‖ ≤
      M * r⁻¹ ^ k
    -- Apply cauchy1_bound' from Osgood2
    have hcont_circle : ContinuousOn (fun z => g (z, v)) (sphere w₀ r) :=
      (g_cont.comp (Continuous.prodMk continuous_id continuous_const)).continuousOn.mono
        (fun z hz => by exact hz)
    have hbound_circle : ∀ z ∈ sphere w₀ r, ‖g (z, v)‖ ≤ M := by
      intro z hz
      exact hM_bound z v (Metric.sphere_subset_closedBall hz) hv
    exact cauchy1_bound' hr_pos M hcont_circle hbound_circle k

  -- Step 5b: The 1D Cauchy series converges: for |u| < r and any v,
  -- HasSum (fun k => u^k • c k v) (g(w₀ + u, v))
  -- This follows from cauchy1_hasSum applied to w ↦ g(w, v).
  have cauchy_hasSum : ∀ v, ∀ u ∈ ball (0 : ℂ) r,
      HasSum (fun k => u ^ k • c k v) (g (w₀ + u, v)) := by
    intro v u hu
    -- g(w₀ + u, v) = (2πi)⁻¹ ∮ g(z,v)/(z-(w₀+u)) dz (by Cauchy integral formula)
    -- The circle integral decomposes as a power series in u.
    have hcont_v : ContinuousOn (fun z => g (z, v)) (sphere w₀ r) :=
      (g_cont.comp (Continuous.prodMk continuous_id continuous_const)).continuousOn.mono
        (fun z hz => hz)
    have h1 := cauchy1_hasSum hr_pos hcont_v hu
    -- h1 : HasSum (fun n => u^n • (2πi)⁻¹ • ∮ (z-w₀)⁻¹^n • (z-w₀)⁻¹ • g(z,v) dz)
    --         ((2πi)⁻¹ • ∮ g(z,v)/(z-(w₀+u)) dz)
    -- The RHS = g(w₀+u, v) by the Cauchy integral formula.
    -- First, show the Cauchy formula holds.
    have hw : w₀ + u ∈ ball w₀ r := by
      rw [mem_ball]
      simp only [dist_self_add_left] at hu ⊢
      exact mem_ball_zero_iff.mp hu
    have hcont_cb : ContinuousOn (fun z => g (z, v)) (closedBall w₀ r) :=
      (g_cont.comp (Continuous.prodMk continuous_id continuous_const)).continuousOn.mono
        (fun z hz => hz)
    have hdiff : ∀ z, z ∈ ball w₀ r → DifferentiableAt ℂ (fun w => g (w, v)) z :=
      fun z _ => g_diff_w v z
    have cauchy_formula := cauchy1 hw hcont_cb hdiff
    -- cauchy_formula : (2πi)⁻¹ • ∮ (z-(w₀+u))⁻¹ • g(z,v) dz = g(w₀+u, v)
    rw [← cauchy_formula]
    -- Now the terms match: each summand is u^n • c_k(v)
    convert h1 using 1

  -- Step 5c: Assemble the joint power series via block_osgood_series.
  -- We adapt the Cauchy hasSum to the mul form localized to closedBall v₀ r,
  -- extract power series with the multivariate Cauchy estimate, and conclude.

  -- Adapt the Cauchy hasSum from smul to mul form, localized to closedBall v₀ r
  have cauchy_hasSum_local : ∀ v ∈ Metric.closedBall v₀ r, ∀ u ∈ ball (0 : ℂ) r,
      HasSum (fun k => u ^ k * c k v) (g (w₀ + u, v)) := by
    intro v hv u hu
    exact (cauchy_hasSum v u hu).congr (fun k => by simp [smul_eq_mul])

  -- First, recover 0 ≤ M from the bound
  have hM_nonneg : 0 ≤ M :=
    le_trans (norm_nonneg _) (hM_bound w₀ v₀ (mem_closedBall_self hr_pos.le)
      (mem_closedBall_self hr_pos.le))

  -- Set ρ = r / e (the effective radius after polarization loss)
  set ρ := r / Real.exp 1 with hρ_def
  have hρ_pos : 0 < ρ := div_pos hr_pos (Real.exp_pos 1)
  have hρ_le_r : ρ ≤ r := div_le_self hr_pos.le (Real.one_le_exp one_pos.le)
  have hρ_inv : ρ⁻¹ = Real.exp 1 / r := by rw [hρ_def, inv_div]
  have hr_inv_le : r⁻¹ ≤ ρ⁻¹ := inv_anti₀ hρ_pos hρ_le_r

  -- Apply the multivariate Cauchy estimate to each c_k
  have c_series_and_bound : ∀ k, ∃ p : FormalMultilinearSeries ℂ (Fin m → ℂ) ℂ,
      HasFPowerSeriesOnBall (c k) p v₀ (ENNReal.ofReal ρ) ∧
      ∀ l, ‖p l‖ ≤ M * ρ⁻¹ ^ (k + l) := by
    intro k
    -- c_k is bounded by M * r⁻¹^k on closedBall v₀ r
    have hbound_k : ∀ x ∈ Metric.closedBall v₀ r, ‖c k x‖ ≤ M * r⁻¹ ^ k :=
      cauchy_bound k
    -- Apply the multivariate Cauchy estimate (with polarization loss)
    obtain ⟨p, hp_series, hp_bound⟩ := analyticAt_hasFPowerSeriesOnBall_of_bound
      (c_an k) hr_pos hbound_k
    refine ⟨p, hp_series, fun l => ?_⟩
    -- hp_bound l : ‖p l‖ ≤ (M * r⁻¹ ^ k) * (r / exp 1)⁻¹ ^ l = (M * r⁻¹ ^ k) * ρ⁻¹ ^ l
    -- We need: ‖p l‖ ≤ M * ρ⁻¹ ^ (k + l)
    calc ‖p l‖ ≤ (M * r⁻¹ ^ k) * ρ⁻¹ ^ l := hp_bound l
      _ ≤ M * ρ⁻¹ ^ k * ρ⁻¹ ^ l := by gcongr
      _ = M * ρ⁻¹ ^ (k + l) := by rw [pow_add]; ring

  -- Choose q and extract the properties
  choose q hq_series_and_bound using c_series_and_bound
  have hq_series : ∀ k, HasFPowerSeriesOnBall (c k) (q k) v₀ (ENNReal.ofReal ρ) :=
    fun k => (hq_series_and_bound k).1
  have hq_bound : ∀ k l, ‖q k l‖ ≤ M * ρ⁻¹ ^ (k + l) :=
    fun k l => (hq_series_and_bound k).2 l

  -- Adapt cauchy_bound and cauchy_hasSum_local to the smaller radius ρ
  have cauchy_bound_ρ : ∀ k, ∀ v ∈ closedBall v₀ ρ, ‖c k v‖ ≤ M * ρ⁻¹ ^ k := by
    intro k v hv
    calc ‖c k v‖ ≤ M * r⁻¹ ^ k :=
          cauchy_bound k v (closedBall_subset_closedBall hρ_le_r hv)
      _ ≤ M * ρ⁻¹ ^ k := by gcongr

  have cauchy_hasSum_ρ : ∀ v ∈ Metric.closedBall v₀ ρ, ∀ u ∈ ball (0 : ℂ) ρ,
      HasSum (fun k => u ^ k * c k v) (g (w₀ + u, v)) := by
    intro v hv u hu
    exact cauchy_hasSum_local v (closedBall_subset_closedBall hρ_le_r hv) u
      (ball_subset_ball hρ_le_r hu)

  -- Apply block_osgood_series to conclude
  exact block_osgood_series g c w₀ v₀ ρ hρ_pos M hM_nonneg
    cauchy_bound_ρ cauchy_hasSum_ρ q hq_series hq_bound

/-! ### Main theorem -/

/-- **Osgood's lemma for n variables.**
A continuous function `f : ℂⁿ → ℂ` that is separately analytic in each
complex coordinate is jointly analytic. -/
theorem osgood_separately_analytic : ∀ (n : ℕ) {f : (Fin n → ℂ) → ℂ},
    Continuous f →
    (∀ (j : Fin n) (z₀ : Fin n → ℂ),
      AnalyticAt ℂ (fun t : ℂ => f (update z₀ j t)) (z₀ j)) →
    AnalyticOnNhd ℂ f Set.univ
  | 0, _, _, _ => osgood_n0
  | 1, _, _, hf_sep => osgood_n1 hf_sep
  | n + 2, f, hf_cont, hf_sep => by
    let e := splitCLE (n + 1)
    set g : ℂ × (Fin (n + 1) → ℂ) → ℂ := f ∘ e with hg_def
    have g_cont : Continuous g := hf_cont.comp e.continuous
    have g_an_w : ∀ v w, AnalyticAt ℂ (fun w => g (w, v)) w := by
      intro v w; simp only [hg_def, comp_def]
      exact sep_analytic_head hf_sep v w
    have g_an_v : ∀ w v, AnalyticAt ℂ (fun v => g (w, v)) v := by
      intro w v; simp only [hg_def, comp_def]
      exact osgood_separately_analytic (n + 1)
        (continuous_fin_cons_tail hf_cont w) (sep_analytic_tail hf_sep w) v (mem_univ v)
    have g_an : AnalyticOnNhd ℂ g Set.univ :=
      block_osgood (osgood_separately_analytic (n + 1)) g_cont g_an_w g_an_v
    have hfg : f = g ∘ e.symm := by
      ext z; simp [hg_def, comp_def, ContinuousLinearEquiv.apply_symm_apply]
    intro z _
    rw [show f = g ∘ e.symm from hfg]
    exact (g_an (e.symm z) (mem_univ _)).comp (e.symm.analyticAt z)
