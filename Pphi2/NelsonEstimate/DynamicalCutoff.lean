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
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Pphi2.NelsonEstimate.SmoothLowerBound
import Pphi2.NelsonEstimate.CovarianceSplit
import Pphi2.InteractingMeasure.LatticeMeasure

noncomputable section

namespace Pphi2.DynamicalCutoff

open Real Pphi2 GaussianField MeasureTheory

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

/-- The degree-adapted logarithmic power in the Nelson cutoff:
`degreeCutoffPower P = P.n / 2`. Since `P.n` is even and at least `4`,
this is a positive natural number. -/
def degreeCutoffPower (P : InteractionPolynomial) : ℕ := P.n / 2

theorem degreeCutoffPower_pos (P : InteractionPolynomial) :
    0 < degreeCutoffPower P := by
  change 0 < P.n.div 2
  exact Nat.div_pos_iff.mpr ⟨by norm_num, le_trans (by norm_num) P.hn_ge⟩

/-- Degree-adapted dynamical cutoff.

If the smooth-side deterministic lower bound has the form
`V_S ≥ -C * (1 + |log T|)^(P.n / 2)`, then this chooses the cutoff
scale so that `C * (1 + |log T|)^(P.n / 2) ≤ M / 2` on the large-`M`
regime. -/
noncomputable def degreeDynamicalCutoffScale
    (P : InteractionPolynomial) (C M : ℝ) : ℝ :=
  if M ≤ 2 * C then 1 else
    Real.exp (1 - (M / (2 * C)) ^ (1 / (degreeCutoffPower P : ℝ)))

/-- The degree-adapted cutoff scale is strictly positive. -/
theorem degreeDynamicalCutoffScale_pos
    (P : InteractionPolynomial) (C M : ℝ) :
    0 < degreeDynamicalCutoffScale P C M := by
  unfold degreeDynamicalCutoffScale
  split_ifs with h
  · exact one_pos
  · exact Real.exp_pos _

/-- On the small-`M` regime, the degree-adapted cutoff scale is `1`. -/
theorem degreeDynamicalCutoffScale_eq_one
    (P : InteractionPolynomial) (C M : ℝ) (h : M ≤ 2 * C) :
    degreeDynamicalCutoffScale P C M = 1 := by
  unfold degreeDynamicalCutoffScale
  rw [if_pos h]

/-- On the large-`M` regime, the degree-adapted cutoff scale is the
explicit exponential formula. -/
theorem degreeDynamicalCutoffScale_eq_exp
    (P : InteractionPolynomial) (C M : ℝ) (h : 2 * C < M) :
    degreeDynamicalCutoffScale P C M =
      Real.exp (1 - (M / (2 * C)) ^ (1 / (degreeCutoffPower P : ℝ))) := by
  unfold degreeDynamicalCutoffScale
  rw [if_neg (not_le.mpr h)]

private lemma degreeCutoffParam_pow
    (P : InteractionPolynomial) {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / (degreeCutoffPower P : ℝ))) ^ degreeCutoffPower P = x := by
  have hk_pos : 0 < (degreeCutoffPower P : ℝ) := by
    exact_mod_cast degreeCutoffPower_pos P
  have hk_ne : (degreeCutoffPower P : ℝ) ≠ 0 := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have hmul : (1 / (degreeCutoffPower P : ℝ)) * (degreeCutoffPower P : ℝ) = 1 := by
    field_simp [hk_ne]
  rw [hmul, Real.rpow_one]

/-- On the large-`M` regime, the logarithmic factor of the
degree-adapted cutoff is the explicit `degreeCutoffPower`-root. -/
theorem one_add_abs_log_degreeDynamicalCutoff_eq_rpow
    (P : InteractionPolynomial) {C M : ℝ}
    (hC_pos : 0 < C) (hM : 2 * C < M) :
    1 + |Real.log (degreeDynamicalCutoffScale P C M)| =
      (M / (2 * C)) ^ (1 / (degreeCutoffPower P : ℝ)) := by
  rw [degreeDynamicalCutoffScale_eq_exp P C M hM, Real.log_exp]
  have hdiv_pos : 0 < M / (2 * C) := by
    refine div_pos ?_ ?_
    · linarith
    · positivity
  have hdiv_ge_one : 1 ≤ M / (2 * C) := by
    rw [one_le_div (by positivity)]
    linarith
  have hroot_ge_one :
      1 ≤ (M / (2 * C)) ^ (1 / (degreeCutoffPower P : ℝ)) := by
    have h_exp_nonneg : 0 ≤ 1 / (degreeCutoffPower P : ℝ) := by positivity
    calc
      (1 : ℝ) = (1 : ℝ) ^ (1 / (degreeCutoffPower P : ℝ)) := by
        symm
        rw [one_rpow]
      _ ≤ (M / (2 * C)) ^ (1 / (degreeCutoffPower P : ℝ)) :=
        Real.rpow_le_rpow (by positivity) hdiv_ge_one h_exp_nonneg
  have hnonpos :
      1 - (M / (2 * C)) ^ (1 / (degreeCutoffPower P : ℝ)) ≤ 0 := by
    linarith
  rw [abs_of_nonpos hnonpos]
  ring

/-- Defining property of the degree-adapted cutoff:
for `M ≥ 2C`, it makes `C * (1 + |log T|)^(P.n / 2) ≤ M / 2`. -/
theorem degreeDynamicalCutoffScale_log_pow_le
    (P : InteractionPolynomial) (C M : ℝ) (hC_pos : 0 < C) (hM : 2 * C ≤ M) :
    C * (1 + |Real.log (degreeDynamicalCutoffScale P C M)|) ^ degreeCutoffPower P ≤
      M / 2 := by
  rcases eq_or_lt_of_le hM with hM_eq | hM_gt
  · rw [degreeDynamicalCutoffScale_eq_one P C M (le_of_eq hM_eq.symm), Real.log_one,
      abs_zero, add_zero, one_pow, mul_one]
    linarith
  · rw [one_add_abs_log_degreeDynamicalCutoff_eq_rpow P hC_pos hM_gt]
    have hdiv_nonneg : 0 ≤ M / (2 * C) := by
      refine div_nonneg ?_ ?_
      · linarith
      · positivity
    rw [degreeCutoffParam_pow P hdiv_nonneg]
    rw [show C * (M / (2 * C)) = M / 2 by field_simp]

/-! ## Smooth-side bound at the dynamical cutoff scale

Combining `smooth_interaction_lower_bound_log_uniform` (smooth
deterministic bound `V_S ≥ -smoothBoundConstant · (1+|log T|)²` with
the explicit constant) with `dynamicalCutoffScale_log_sq_le`
(`smoothBoundConstant · (1+|log T(M)|)² ≤ M/2` for
`M ≥ 2 · smoothBoundConstant`) gives the master smooth-side
inequality `V_S(φ_S) ≥ -M/2` at the dynamical cutoff scale. -/

variable (d N : ℕ) [NeZero N] (a mass : ℝ)

/-- **Smooth-side classical bound at the dynamical cutoff scale.**

For `2 · smoothBoundConstant ≤ M`, choosing `T = T(M) :=
dynamicalCutoffScale (smoothBoundConstant d a mass L) M` gives the
deterministic inequality `V_S(φ_S) ≥ -M/2`, where `V_S` is the
smooth-side Wick-ordered interaction.

This is the smooth-side estimate for the dynamical cutoff: combined
with `V = V_S + E_R`, the inequality `V ≤ -M` forces `E_R ≤ -M/2`,
opening up the rough-side polynomial-chaos concentration. -/
theorem smooth_lower_bound_at_cutoff
    (ha : 0 < a) (hmass : 0 < mass)
    (hd : d = 2) (L : ℝ) (hL : 0 < L) (ha_eq : a = L / N)
    (φ_S : FinLatticeSites d N → ℝ)
    (M : ℝ) (hM : 2 * smoothBoundConstant d a mass L ≤ M) :
    -(M / 2) ≤
      a ^ d * ∑ x : FinLatticeSites d N,
        wickMonomial 4
          (smoothWickConstant d N a mass
            (dynamicalCutoffScale (smoothBoundConstant d a mass L) M))
          (φ_S x) := by
  have hC_pos : 0 < smoothBoundConstant d a mass L :=
    smoothBoundConstant_pos d a mass L ha hmass hL
  have hT_pos :
      0 < dynamicalCutoffScale (smoothBoundConstant d a mass L) M :=
    dynamicalCutoffScale_pos _ _
  have h_smooth :=
    smooth_interaction_lower_bound_log_uniform d N a mass ha hmass hd L hL ha_eq
      (dynamicalCutoffScale (smoothBoundConstant d a mass L) M)
      hT_pos φ_S
  have h_cutoff :=
    dynamicalCutoffScale_log_sq_le (smoothBoundConstant d a mass L) M hC_pos hM
  linarith

/-! ## Tail-bound transfer from smooth/rough decomposition

This is the abstract Glimm–Jaffe Ch. 8 step that converts a
deterministic smooth lower bound + a rough-error tail bound into a
tail bound on `V` itself. It's the algebraic core of the dynamical
cutoff: combined with the layer-cake and a doubly-exponential tail
on the rough error, it gives the uniform exp-moment bound. -/

/-- **Tail-bound transfer.**

Given an `M`-parameterised decomposition `V = V_S(M) + E_R(M)` with:
* deterministic smooth lower bound `V_S(M) ω ≥ -M/2` (pointwise),
* rough-error tail bound `μ {ω | E_R(M) ω ≤ -M/2} ≤ ψ M`,
the inequality `V ω ≤ -M` forces `E_R(M) ω ≤ -M/2` (since
`V_S(M) ω ≥ -M/2`), so the tail of `V` inherits the rough bound:
`μ {ω | V ω ≤ -M} ≤ ψ M`.

This is the Glimm-Jaffe Ch. 8 dynamical-cutoff transfer. The
decomposition is allowed to be `M`-dependent (the smooth/rough split
parameter `T = T(M)` changes with the depth `M`). -/
theorem measure_le_neg_of_smooth_rough_split
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (V : α → ℝ)
    (V_S E_R : ℝ → α → ℝ)
    (hdecomp : ∀ M ω, V ω = V_S M ω + E_R M ω)
    (hsmooth : ∀ M ω, -(M / 2) ≤ V_S M ω)
    (ψ : ℝ → ENNReal)
    (htail : ∀ M, 0 < M → μ {ω | E_R M ω ≤ -(M / 2)} ≤ ψ M)
    (M : ℝ) (hM : 0 < M) :
    μ {ω | V ω ≤ -M} ≤ ψ M := by
  refine le_trans (measure_mono ?_) (htail M hM)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have h_eq := hdecomp M ω
  have h_smooth := hsmooth M ω
  linarith

end Pphi2.DynamicalCutoff
