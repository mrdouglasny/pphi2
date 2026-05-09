/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Layer-Cake Reformulation of the Boltzmann L² Norm

For the Nelson exponential moment bound `∫ exp(-V)² dμ ≤ K`, the
Glimm–Jaffe Ch. 8 dynamical-cutoff strategy reformulates the L² norm
as a tail-probability integral via the layer-cake formula:

  `∫⁻ exp(-V)² dμ ≤ μ(univ) + 2 ∫⁻ t in (0, ∞), μ{V ≤ -t} · e^(2t) dt`

The right-hand side is then bounded by the dynamical-cutoff
stretched-exponential probability bound `μ{V ≤ -t} ≤ 2 exp(-c g(t))`
(with `g(t)` doubly-exponential at large `t`), producing a finite
uniform-in-`N` exp moment bound.

## Main results

* `exp_neg_sq_le_exp_two_max`: pointwise `exp(-V)² ≤ exp(2·max(0,-V))`.
* `setOf_le_max_eq_setOf_le_neg`: set rewrite for the layer-cake
  domain.
* `lintegral_expSq_neg_le_layer_cake`: the master layer-cake bound.

## Status

`exp_neg_sq_le_exp_two_max` and `setOf_le_max_eq_setOf_le_neg` are
proved. The master theorem `lintegral_expSq_neg_le_layer_cake` is
stated with a structured proof outline + targeted `sorry`s for two
finishing steps (the antiderivative identity and the measurability of
the layer-cake integrand).

The existing helpers reduce the remaining work to
~20 lines of bookkeeping; the strategy is documented in the proof's
inline comments and follows directly from
`MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul`.

## References

- Glimm and Jaffe, *Quantum Physics*, Ch. 8 (the dynamical cutoff).
- Mathlib `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul`
  (the abstract layer-cake / Cavalieri's principle).
-/

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

namespace Pphi2.LayerCake

open MeasureTheory Real Set

/-- Pointwise bound: `exp(-V)² ≤ exp(2 · max(0, -V))`.

For `V ≥ 0`, RHS = `exp(0) = 1` and LHS = `exp(-2V) ≤ 1`; for `V < 0`,
both sides equal `exp(-2V)`. -/
theorem exp_neg_sq_le_exp_two_max (V : ℝ) :
    Real.exp (-V) ^ 2 ≤ Real.exp (2 * max 0 (-V)) := by
  have h_eq : Real.exp (-V) ^ 2 = Real.exp (-2 * V) := by
    rw [sq, ← Real.exp_add]; ring_nf
  rw [h_eq]
  apply Real.exp_le_exp.mpr
  have hmax : -V ≤ max 0 (-V) := le_max_right _ _
  linarith

/-- For `t > 0`, the level set `{ω | t ≤ max 0 (-V ω)}` equals
`{ω | V ω ≤ -t}`. (For `t ≤ 0` the LHS is the whole space.) -/
theorem setOf_le_max_eq_setOf_le_neg
    {α : Type*} (V : α → ℝ) {t : ℝ} (ht : 0 < t) :
    {a | t ≤ max 0 (-V a)} = {a | V a ≤ -t} := by
  ext a
  simp only [Set.mem_setOf_eq, le_max_iff]
  constructor
  · rintro (h | h)
    · linarith
    · linarith
  · intro h; right; linarith

/-- **Layer-cake reformulation of the Boltzmann L² norm.**

For any measure `μ` on `α` (with `SFinite μ` so the layer-cake applies)
and any measurable real-valued `V`:
$$
\int_\alpha (e^{-V(\omega)})^2 \, d\mu \;\le\; \mu(\alpha) +
  \int_0^\infty \mu\{\omega \mid V(\omega) \le -t\} \cdot 2 e^{2t} \, dt.
$$

This is the layer-cake reformulation needed by the dynamical-cutoff
discharge: combined with the stretched-exponential probability bound
`μ{V ≤ -t} ≤ 2 exp(-c g(t))` (with `g` doubly-exponential at large `t`),
it produces the finite uniform-in-`N` exp moment bound that the bridge
axiom asserts.

**Proof outline:**
1. Pointwise `exp(-V)² ≤ exp(2W)` where `W := max 0 (-V) ≥ 0`
   (`exp_neg_sq_le_exp_two_max`).
2. Split `exp(2W) = 1 + (exp(2W) - 1)` (both nonneg, `exp(2W) ≥ 1`),
   so `ofReal(exp(2W)) = 1 + ofReal(exp(2W) - 1)`.
3. The "+1" integrates to `μ(univ)`.
4. `(exp(2W) - 1) = ∫₀^W 2·exp(2t) dt` (antiderivative identity).
5. Apply Mathlib's `lintegral_comp_eq_lintegral_meas_le_mul` with
   `f := W` and `g := fun t => 2 * exp(2t)`:
   `∫⁻ ω, ofReal(∫₀^{W ω} 2·exp(2t) dt) dμ
      = ∫⁻ t in Ioi 0, μ{a | t ≤ W a} · ofReal(2·exp(2t))`.
6. Set rewrite `{t ≤ W a} = {V a ≤ -t}` for `t > 0`
   (`setOf_le_max_eq_setOf_le_neg`).

The two `sorry`s below correspond to (a) the antiderivative identity in
step 4 (a clean computation requiring `intervalIntegral` API) and (b)
the integrand-substitution rewrite in step 6 (a measurability /
`setLIntegral_congr_set` bookkeeping step). Both are localised and
mechanical once the right Mathlib lemmas are wired in. -/
theorem lintegral_expSq_neg_le_layer_cake
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (V : α → ℝ) (hV : Measurable V) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-V ω) ^ 2) ∂μ ≤
      μ Set.univ +
        ∫⁻ t in Set.Ioi (0 : ℝ),
          μ {a | V a ≤ -t} * ENNReal.ofReal (2 * Real.exp (2 * t)) := by
  set W : α → ℝ := fun ω => max 0 (-V ω) with hW_def
  have hW_nn : ∀ ω, 0 ≤ W ω := fun ω => le_max_left _ _
  have hW_meas : Measurable W := measurable_const.max hV.neg
  -- Step 1: pointwise inequality on `exp(-V)² ≤ exp(2W)`.
  have h_pointwise : ∀ ω,
      ENNReal.ofReal (Real.exp (-V ω) ^ 2) ≤
        ENNReal.ofReal (Real.exp (2 * W ω)) := fun ω =>
    ENNReal.ofReal_le_ofReal (exp_neg_sq_le_exp_two_max (V ω))
  refine (lintegral_mono h_pointwise).trans ?_
  -- Step 2-3: split `exp(2W) = 1 + (exp(2W) - 1)`, integrate, get
  --           `μ(univ) + ∫⁻ ofReal(exp(2W) - 1)`.
  have h_split :
      ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * W ω)) ∂μ =
        μ Set.univ +
          ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * W ω) - 1) ∂μ := by
    have h_eq : ∀ ω,
        ENNReal.ofReal (Real.exp (2 * W ω)) =
          1 + ENNReal.ofReal (Real.exp (2 * W ω) - 1) := by
      intro ω
      have h_exp_ge_one : 1 ≤ Real.exp (2 * W ω) :=
        Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * W ω)
      have h_sub_nn : (0 : ℝ) ≤ Real.exp (2 * W ω) - 1 := by linarith
      have h_calc :
          (1 : ENNReal) + ENNReal.ofReal (Real.exp (2 * W ω) - 1) =
            ENNReal.ofReal 1 + ENNReal.ofReal (Real.exp (2 * W ω) - 1) := by
        rw [ENNReal.ofReal_one]
      rw [h_calc, ← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) h_sub_nn]
      congr 1
      ring
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * W ω)) ∂μ
        = ∫⁻ ω, 1 + ENNReal.ofReal (Real.exp (2 * W ω) - 1) ∂μ := by
          apply lintegral_congr_ae; filter_upwards with ω; rw [h_eq ω]
      _ = ∫⁻ _ : α, 1 ∂μ +
          ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * W ω) - 1) ∂μ := by
            rw [lintegral_add_left measurable_const]
      _ = μ Set.univ +
          ∫⁻ ω, ENNReal.ofReal (Real.exp (2 * W ω) - 1) ∂μ := by
            rw [lintegral_one]
  rw [h_split]
  refine add_le_add le_rfl ?_
  -- Step 4-6: layer-cake on `(exp(2W) - 1) = ∫₀^W 2·exp(2t) dt`.
  -- The remaining steps:
  --   (4a) antiderivative `∫₀^s 2·exp(2t) dt = exp(2s) - 1`,
  --   (4b) `Real.exp (2 * W ω) - 1 = ∫₀^(W ω) 2·exp(2t) dt`,
  --   (5)  apply `MeasureTheory.lintegral_comp_eq_lintegral_meas_le_mul`,
  --   (6)  rewrite `{t ≤ W a} = {V a ≤ -t}` via
  --        `setOf_le_max_eq_setOf_le_neg`.
  -- These are mechanical given the proofs above; left as a localised
  -- `sorry` for follow-up.
  sorry

end Pphi2.LayerCake
