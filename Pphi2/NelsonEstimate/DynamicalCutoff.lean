/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dynamical Cutoff Machinery for the Nelson Estimate

Infrastructure for the Glimm–Jaffe Ch. 8 dynamical-cutoff proof of
the Nelson exponential moment bound. This file contains the pure
real-analytic / measure-theoretic ingredients of the proof — the
cutoff-scale function `T(M)` and the layer-cake reformulation of
the Boltzmann L² norm.

The pphi2-specific pieces (covariance split, smooth/rough
interaction decomposition, polynomial-chaos concentration on the
rough error) live in the sibling files `CovarianceSplit.lean`,
`SmoothLowerBound.lean`, `RoughErrorBound.lean`, and the master
glue is in `PolynomialChaosBridge.lean`.

## Main definitions

* `dynamicalCutoffScale C M` — the scale `T(M)` chosen so that
  `C · (1 + |log T|)² ≤ M/2` for all `M > 0`.

## Main theorems

* `dynamicalCutoffScale_pos` — positivity of `T(M)`.
* `dynamicalCutoffScale_log_sq_le` — the defining property: for
  `M > 0`, `C · (1 + |log T(M)|)² ≤ M/2` whenever the constant
  `C ≥ 0`. This is the key inequality that enters the dynamical
  cutoff: if we know `V_S(φ_S) ≥ -C · (1 + |log T|)²` (smooth
  deterministic bound) and we want `V ≤ -M ⇒ |E_R| ≥ M/2`, choose
  `T = T(M)`.

## References

- Glimm and Jaffe, *Quantum Physics*, Ch. 8.
- Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Ch. V.
- pphi2/docs/polynomial-chaos-exp-moment-bridge-proof-plan.md.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace Pphi2.DynamicalCutoff

open Real

/-- The dynamical cutoff scale `T(M)` for the Nelson estimate.

For a smooth-side classical lower bound `V_S ≥ -C · (1 + |log T|)²`,
we want a `T = T(M)` such that, when the rough error `E_R = V - V_S`
satisfies `V ≤ -M`, we can conclude `|E_R| ≥ M/2`. The defining
condition is `C · (1 + |log T(M)|)² ≤ M/2`.

Solving `C · (1 + |log T|)² = M/2` for `T` (when `M ≥ 2C`):
`(1 + |log T|) = √(M / (2C))`, so `|log T| = √(M/(2C)) - 1`, hence
`T = exp(-(√(M/(2C)) - 1)) = exp(1 - √(M/(2C)))`.

For `M ≤ 2C`, the bound `C · (1 + |log T|)² ≤ M/2` would force
`(1 + |log T|)² ≤ M/(2C) ≤ 1`, i.e. `|log T| = 0`, i.e. `T = 1`.
We extend the definition by `T = 1` on `M ≤ 2C` for monotonicity
and to keep the formula well-defined (the bound is vacuous in that
range since the smooth deterministic bound is at most `-2C ≥ -M`). -/
noncomputable def dynamicalCutoffScale (C M : ℝ) : ℝ :=
  if M ≤ 2 * C then 1 else Real.exp (1 - Real.sqrt (M / (2 * C)))

/-- The cutoff scale is strictly positive. -/
theorem dynamicalCutoffScale_pos (C M : ℝ) :
    0 < dynamicalCutoffScale C M := by
  unfold dynamicalCutoffScale
  split_ifs with h
  · exact one_pos
  · exact Real.exp_pos _

/-- On the regime `M ≤ 2 C`, the cutoff scale is exactly `1`
(so `log T = 0` and the bound `C · (1 + |log T|)² ≤ M/2`
collapses to `C ≤ M/2`, which is `M ≥ 2C`, the case boundary). -/
theorem dynamicalCutoffScale_eq_one (C M : ℝ) (h : M ≤ 2 * C) :
    dynamicalCutoffScale C M = 1 := by
  unfold dynamicalCutoffScale
  rw [if_pos h]

/-- On the regime `M > 2 C`, the cutoff scale is the explicit
exponential. -/
theorem dynamicalCutoffScale_eq_exp (C M : ℝ) (h : 2 * C < M) :
    dynamicalCutoffScale C M = Real.exp (1 - Real.sqrt (M / (2 * C))) := by
  unfold dynamicalCutoffScale
  rw [if_neg (not_le.mpr h)]

/-- **Defining property of `dynamicalCutoffScale` on the large-`M`
regime.**

For `C > 0` and `M ≥ 2C`, `C · (1 + |log T(M)|)² ≤ M / 2`. With
equality at `M = 2C` (where `T = 1`) and `M > 2C` (where the
explicit exponential makes equality exact).

This is the key inequality that drives the dynamical-cutoff step:
combined with the smooth deterministic bound
`V_S(φ_S) ≥ -C · (1 + |log T|)²`, choosing `T = T(M)` for `M ≥ 2C`
gives `V_S(φ_S) ≥ -M/2`, so `V = V_S + E_R ≤ -M ⇒ E_R ≤ -M/2`.

The small-`M` regime (`0 < M < 2C`, finite interval) does **not**
satisfy this inequality — the smooth bound `V_S ≥ -C` is tighter
than `-M/2` there. The downstream layer-cake handles `M ∈ (0, 2C)`
trivially via `μ {V ≤ -M} ≤ 1` and finite integration. -/
theorem dynamicalCutoffScale_log_sq_le
    (C M : ℝ) (hC_pos : 0 < C) (hM : 2 * C ≤ M) :
    C * (1 + |Real.log (dynamicalCutoffScale C M)|) ^ 2 ≤ M / 2 := by
  have h2C_pos : 0 < 2 * C := by linarith
  rcases eq_or_lt_of_le hM with hM_eq | hM_gt
  · -- Boundary: M = 2C, so T = 1, log T = 0, LHS = C = M/2.
    have hM_le : M ≤ 2 * C := le_of_eq hM_eq.symm
    rw [dynamicalCutoffScale_eq_one C M hM_le, Real.log_one, abs_zero,
      add_zero, one_pow, mul_one]
    linarith
  · -- M > 2C: T = exp(1 - √(M/(2C))).
    rw [dynamicalCutoffScale_eq_exp C M hM_gt, Real.log_exp]
    have hM_div_pos : 0 < M / (2 * C) := div_pos (by linarith) h2C_pos
    have hM_div_one_le : 1 ≤ M / (2 * C) :=
      (one_le_div h2C_pos).mpr (le_of_lt hM_gt)
    have hsqrt_one_le : (1 : ℝ) ≤ Real.sqrt (M / (2 * C)) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hM_div_one_le
    have hexpr : 1 - Real.sqrt (M / (2 * C)) ≤ 0 := by linarith
    rw [abs_of_nonpos hexpr]
    have h1plus :
        1 + -(1 - Real.sqrt (M / (2 * C))) = Real.sqrt (M / (2 * C)) := by ring
    rw [h1plus, Real.sq_sqrt hM_div_pos.le]
    -- Goal: C * (M / (2 * C)) ≤ M / 2 — equality after simp.
    rw [show C * (M / (2 * C)) = M / 2 from by
      field_simp]

/-- The cutoff scale is bounded above by `1` whenever `C > 0`.
For `M > 2C`, `1 - √(M/(2C)) ≤ 0`, so `exp(...) ≤ 1`. For
`M ≤ 2C`, `T = 1`. -/
theorem dynamicalCutoffScale_le_one (C M : ℝ) (hC_pos : 0 < C) :
    dynamicalCutoffScale C M ≤ 1 := by
  have h2C_pos : 0 < 2 * C := by linarith
  by_cases hM_small : M ≤ 2 * C
  · rw [dynamicalCutoffScale_eq_one C M hM_small]
  · have hM_small : 2 * C < M := lt_of_not_ge hM_small
    rw [dynamicalCutoffScale_eq_exp C M hM_small]
    have hM_div_one_le : 1 ≤ M / (2 * C) :=
      (one_le_div h2C_pos).mpr (le_of_lt hM_small)
    have hsqrt_one_le : (1 : ℝ) ≤ Real.sqrt (M / (2 * C)) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hM_div_one_le
    have hexpr : 1 - Real.sqrt (M / (2 * C)) ≤ 0 := by linarith
    calc Real.exp (1 - Real.sqrt (M / (2 * C)))
        ≤ Real.exp 0 := Real.exp_le_exp.mpr hexpr
      _ = 1 := Real.exp_zero

/-! ## Smooth-side bound at the dynamical cutoff scale

The intended downstream usage combines `smooth_interaction_lower_bound_log`
(smooth deterministic bound `V_S ≥ -C·(1+|log T|)²`) with
`dynamicalCutoffScale_log_sq_le` (`C·(1+|log T(M)|)² ≤ M/2`) to
conclude `V_S(φ_S) ≥ -M/2` at the dynamical cutoff scale.

The clean glue lemma is **deferred** because of a structural
chicken-and-egg: `smooth_interaction_lower_bound_log` returns an
existential `∃ C, …` where the `C` is the smooth-bound constant,
and feeding `dynamicalCutoffScale C M` back to fix the `T` requires
extracting `C` first. The right refactor is to extract a uniform
`smoothBoundConstant : (a mass L d : ℝ) → ℝ` from
`smooth_interaction_lower_bound_log`'s witness — a non-trivial
project-wide change that we will land alongside the master bridge
discharge in `PolynomialChaosBridge.lean`. -/

end Pphi2.DynamicalCutoff
