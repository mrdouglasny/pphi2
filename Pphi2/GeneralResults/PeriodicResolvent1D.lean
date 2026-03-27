/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas

# 1D periodic vs. free massive resolvent on the circle

This file isolates the scalar Green's function comparison used when comparing
a massive Laplacian on `ℝ / Ltℤ` to the infinite line.

## Mathematical content

For `ω > 0` (mass parameter of the temporal mode) and period `Lt > 0`, the
symmetric periodic kernel is

`G^per_ω(t) = cosh(ω(Lt/2 - |t|)) / (2ω sinh(ωLt/2))`,

whereas the free (whole-line) kernel is `G^free_ω(t) = e^{-ω|t|} / (2ω)`.

The difference admits the **method-of-images** (geometric series) form

`G^per - G^free = (e^{-ω(Lt-|t|)} + e^{-ω(Lt+|t|)}) / (2ω(1 - e^{-ωLt}))`,

which yields exponential bounds uniform in `|t| < Lt/2` with rate `e^{-ωLt/2}`.

These lemmas support IR/torus–to–cylinder covariance limits (see
`Pphi2.IRLimit.CovarianceConvergence`).

## References

- Glimm–Jaffe, *Quantum Physics*, method-of-images discussion for Green's functions
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII (operator / covariance limits)
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Basic

noncomputable section

open Filter

namespace PeriodicResolvent1D

/-! ## Definitions -/

/-- Periodic massive **1D resolvent / Green kernel** on `ℝ / Ltℤ` in symmetric form:
`cosh(ω(Lt/2 - |t|)) / (2ω sinh(ωLt/2))`.

Hypothesis `0 < ω` is required for the standard PDE normalization; the expression
is only used under that hypothesis in the lemmas below. -/
def periodicKernel (ω Lt t : ℝ) : ℝ :=
  Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2))

/-- Whole-line (free) massive resolvent kernel `e^{-ω|t|} / (2ω)`. -/
def freeKernel (ω t : ℝ) : ℝ :=
  Real.exp (-ω * |t|) / (2 * ω)

/-! ## Method-of-images identity -/

/-- **Exact wrap-around identity** (`G^per - G^free` as a two-image sum).

The periodic kernel differs from the infinite-line kernel by the sum of the two
nearest image contributions; equivalently, the first two terms of the
geometric series for reflections across the period. -/
theorem sub_free_eq_wrapAround
    (ω : ℝ) (hω : 0 < ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) :
    periodicKernel ω Lt t - freeKernel ω t =
      (Real.exp (-ω * (Lt - |t|)) + Real.exp (-ω * (Lt + |t|))) /
        (2 * ω * (1 - Real.exp (-ω * Lt))) := by
  simp_rw [periodicKernel, freeKernel]
  set a : ℝ := ω * Lt / 2
  set b : ℝ := ω * |t|
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have hsinh_pos : 0 < Real.sinh a := by
    rw [Real.sinh_eq]
    have hnum_pos : 0 < Real.exp a - Real.exp (-a) := by
      exact sub_pos.mpr <| (Real.exp_lt_exp).2 (by linarith [ha_pos])
    nlinarith
  have hsinh_ne : Real.sinh a ≠ 0 := ne_of_gt hsinh_pos
  have hω_ne : ω ≠ 0 := ne_of_gt hω
  have hLt_exp_lt : Real.exp (-ω * Lt) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hone_pos : 0 < 1 - Real.exp (-ω * Lt) := sub_pos.mpr hLt_exp_lt
  have hone_ne : 1 - Real.exp (-ω * Lt) ≠ 0 := ne_of_gt hone_pos
  have hsplit : Real.cosh (a - b) =
      Real.sinh a * Real.exp (-b) + Real.exp (-a) * Real.cosh b := by
    have hcosh_a : Real.cosh a = Real.sinh a + Real.exp (-a) := by
      linarith [Real.cosh_sub_sinh a]
    calc
      Real.cosh (a - b)
          = Real.cosh a * Real.cosh b - Real.sinh a * Real.sinh b := by
              rw [Real.cosh_sub]
      _ = (Real.sinh a + Real.exp (-a)) * Real.cosh b - Real.sinh a * Real.sinh b := by
            rw [hcosh_a]
      _ = Real.sinh a * (Real.cosh b - Real.sinh b) + Real.exp (-a) * Real.cosh b := by
            ring
      _ = Real.sinh a * Real.exp (-b) + Real.exp (-a) * Real.cosh b := by
            rw [Real.cosh_sub_sinh]
  have hdiff :
      Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
          Real.exp (-ω * |t|) / (2 * ω) =
        Real.exp (-a) * Real.cosh b / (2 * ω * Real.sinh a) := by
    have harg : ω * (Lt / 2 - |t|) = a - b := by
      dsimp [a, b]
      ring
    rw [harg, show ω * Lt / 2 = a by rfl, hsplit]
    field_simp [hω_ne, hsinh_ne]
    ring
  have hsinh_exp : 2 * Real.sinh a = Real.exp a - Real.exp (-a) := by
    rw [Real.sinh_eq]
    ring
  have hratio :
      Real.exp (-a) / (2 * Real.sinh a) =
        Real.exp (-ω * Lt) / (1 - Real.exp (-ω * Lt)) := by
    rw [hsinh_exp, Real.exp_neg]
    set u : ℝ := Real.exp a
    have hu_ne : u ≠ 0 := by
      dsimp [u]
      exact ne_of_gt (Real.exp_pos a)
    have hratio_u :
        u⁻¹ / (u - u⁻¹) = (u * u)⁻¹ / (1 - (u * u)⁻¹) := by
      field_simp [hu_ne]
    have hu_sq : Real.exp (-ω * Lt) = (u * u)⁻¹ := by
      rw [show -ω * Lt = -(a + a) by
        dsimp [a]
        ring, Real.exp_neg, Real.exp_add, show Real.exp a = u by rfl]
    rw [hu_sq]
    simpa [u] using hratio_u
  calc
    Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
        Real.exp (-ω * |t|) / (2 * ω)
      = Real.exp (-a) * Real.cosh b / (2 * ω * Real.sinh a) := hdiff
    _ = Real.cosh b * (Real.exp (-ω * Lt) / (ω * (1 - Real.exp (-ω * Lt)))) := by
          calc
            Real.exp (-a) * Real.cosh b / (2 * ω * Real.sinh a)
                = Real.cosh b * (Real.exp (-a) / (2 * Real.sinh a)) / ω := by
                    field_simp [hω_ne, hsinh_ne]
            _ = Real.cosh b * (Real.exp (-ω * Lt) / (1 - Real.exp (-ω * Lt))) / ω := by
                  rw [hratio]
            _ = Real.cosh b * (Real.exp (-ω * Lt) / (ω * (1 - Real.exp (-ω * Lt)))) := by
                  field_simp [hω_ne, hone_ne]
    _ = ((Real.exp b + Real.exp (-b)) / 2) *
          (Real.exp (-ω * Lt) / (ω * (1 - Real.exp (-ω * Lt)))) := by
          rw [Real.cosh_eq]
    _ = (Real.exp (-ω * (Lt - |t|)) + Real.exp (-ω * (Lt + |t|))) /
          (2 * ω * (1 - Real.exp (-ω * Lt))) := by
          have hb : b = ω * |t| := by rfl
          have h₁ : Real.exp b * Real.exp (-ω * Lt) = Real.exp (-ω * (Lt - |t|)) := by
            rw [hb, ← Real.exp_add]
            congr 1
            ring
          have h₂ : Real.exp (-b) * Real.exp (-ω * Lt) = Real.exp (-ω * (Lt + |t|)) := by
            rw [hb, ← Real.exp_add]
            congr 1
            ring
          have hExpLt : Real.exp (-(ω * Lt)) = Real.exp (-ω * Lt) := by
            congr 1
            ring
          field_simp [hω_ne, hone_ne]
          rw [hExpLt]
          rw [add_mul, h₁, h₂]
          ring_nf

/-! ## Exponential bounds -/

/-- Pointwise exponential bound on `|G^per - G^free|` in terms of the nearest image
distance `Lt - |t|`. -/
theorem abs_sub_free_le
    (ω : ℝ) (hω : 0 < ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) :
    |periodicKernel ω Lt t - freeKernel ω t| ≤
      Real.exp (-ω * (Lt - |t|)) /
        (ω * (1 - Real.exp (-ω * Lt))) := by
  have hLt_exp_lt : Real.exp (-ω * Lt) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hone_pos : 0 < 1 - Real.exp (-ω * Lt) := sub_pos.mpr hLt_exp_lt
  have hω_ne : ω ≠ 0 := ne_of_gt hω
  have hone_ne : 1 - Real.exp (-ω * Lt) ≠ 0 := ne_of_gt hone_pos
  rw [sub_free_eq_wrapAround ω hω t Lt hLt, abs_of_nonneg]
  · have _hterm_nonneg : 0 ≤ Real.exp (-ω * (Lt + |t|)) := le_of_lt (Real.exp_pos _)
    have hterm_le : Real.exp (-ω * (Lt + |t|)) ≤ Real.exp (-ω * (Lt - |t|)) := by
      exact (Real.exp_le_exp).2 (by nlinarith [abs_nonneg t, hω])
    have hsum_le :
        Real.exp (-ω * (Lt - |t|)) + Real.exp (-ω * (Lt + |t|)) ≤
          2 * Real.exp (-ω * (Lt - |t|)) := by
      nlinarith
    have hden_pos : 0 < 2 * ω * (1 - Real.exp (-ω * Lt)) := by
      positivity
    have hcancel :
        (2 * Real.exp (-ω * (Lt - |t|))) / (2 * ω * (1 - Real.exp (-ω * Lt))) =
          Real.exp (-ω * (Lt - |t|)) / (ω * (1 - Real.exp (-ω * Lt))) := by
      field_simp [hω_ne, hone_ne]
    exact (div_le_div_of_nonneg_right hsum_le hden_pos.le).trans_eq hcancel
  · positivity

/-- Uniform bound on the principal strip `|t| < Lt/2`: the nearest image is at
distance at least `Lt/2`, so the error is `O(e^{-ωLt/2})`. -/
theorem abs_sub_free_le_on_halfPeriodStrip
    (ω : ℝ) (hω : 0 < ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) (ht : |t| < Lt / 2) :
    |periodicKernel ω Lt t - freeKernel ω t| ≤
      Real.exp (-ω * Lt / 2) /
        (ω * (1 - Real.exp (-ω * Lt))) := by
  refine (abs_sub_free_le ω hω t Lt hLt).trans ?_
  have hden_pos : 0 < ω * (1 - Real.exp (-ω * Lt)) := by
    have hLt_exp_lt : Real.exp (-ω * Lt) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith
    exact mul_pos hω (sub_pos.mpr hLt_exp_lt)
  apply div_le_div_of_nonneg_right
  · apply (Real.exp_le_exp).2
    nlinarith
  · exact hden_pos.le

/-- Mass-gap envelope: if `mass ≤ ω`, replace the frequency in the exponent and
prefactor by the minimal mode `mass`. -/
theorem abs_sub_free_le_uniform_mass_gap
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) (ht : |t| < Lt / 2) :
    |periodicKernel ω Lt t - freeKernel ω t| ≤
      Real.exp (-mass * Lt / 2) /
        (mass * (1 - Real.exp (-mass * Lt))) := by
  have hω_pos : 0 < ω := lt_of_lt_of_le hmass hω
  have hmass_exp_lt : Real.exp (-mass * Lt) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hω_exp_lt : Real.exp (-ω * Lt) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hω_den_nonneg : 0 ≤ ω * (1 - Real.exp (-ω * Lt)) := by
    exact mul_nonneg hω_pos.le (sub_nonneg.mpr hω_exp_lt.le)
  have hmass_den_pos : 0 < mass * (1 - Real.exp (-mass * Lt)) := by
    exact mul_pos hmass (sub_pos.mpr hmass_exp_lt)
  have hnum_le :
      Real.exp (-ω * Lt / 2) ≤ Real.exp (-mass * Lt / 2) := by
    apply (Real.exp_le_exp).2
    nlinarith
  have hsub_le :
      1 - Real.exp (-mass * Lt) ≤ 1 - Real.exp (-ω * Lt) := by
    have hexp_le : Real.exp (-ω * Lt) ≤ Real.exp (-mass * Lt) := by
      apply (Real.exp_le_exp).2
      nlinarith
    linarith
  have hden_le :
      mass * (1 - Real.exp (-mass * Lt)) ≤
        ω * (1 - Real.exp (-ω * Lt)) := by
    exact mul_le_mul hω hsub_le (sub_nonneg.mpr hmass_exp_lt.le) hω_pos.le
  calc
    |periodicKernel ω Lt t - freeKernel ω t|
      ≤ Real.exp (-ω * Lt / 2) / (ω * (1 - Real.exp (-ω * Lt))) :=
        abs_sub_free_le_on_halfPeriodStrip ω hω_pos t Lt hLt ht
    _ ≤ Real.exp (-mass * Lt / 2) / (ω * (1 - Real.exp (-ω * Lt))) :=
        div_le_div_of_nonneg_right hnum_le hω_den_nonneg
    _ ≤ Real.exp (-mass * Lt / 2) / (mass * (1 - Real.exp (-mass * Lt))) :=
        div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos _)) hmass_den_pos hden_le

/-! ## Limits as `Lt → ∞` -/

/-- The explicit **wrap-around error majorant** tends to `0` as `Lt → ∞` along `ℕ`. -/
theorem wrapAroundErrorMajorant_tendsto_zero
    (ω : ℝ) (hω : 0 < ω) (t : ℝ)
    (Lt : ℕ → ℝ)
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto
      (fun n =>
        Real.exp (-ω * (Lt n - |t|)) /
          (ω * (1 - Real.exp (-ω * Lt n))))
      atTop (nhds 0) := by
  have hω_ne : ω ≠ 0 := ne_of_gt hω
  have hneg_tend : Tendsto (fun n => -ω * Lt n) atTop atBot := by
    refine Filter.tendsto_atBot.mpr ?_
    intro b
    filter_upwards [(Filter.tendsto_atTop.mp hLt_tend) (-b / ω)] with n hn
    have hmul : -b ≤ Lt n * ω := by
      rw [div_le_iff₀ hω] at hn
      simpa [mul_comm, mul_left_comm, mul_assoc] using hn
    nlinarith
  have hexp_tend : Tendsto (fun n => Real.exp (-ω * Lt n)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hneg_tend
  have hnum_tend :
      Tendsto (fun n => Real.exp (-ω * (Lt n - |t|))) atTop (nhds 0) := by
    have hscaled :
        Tendsto (fun n => Real.exp (ω * |t|) * Real.exp (-ω * Lt n))
          atTop (nhds (Real.exp (ω * |t|) * 0)) :=
      Filter.Tendsto.const_mul (Real.exp (ω * |t|)) hexp_tend
    have hfun :
        (fun n => Real.exp (-ω * (Lt n - |t|))) =
          fun n => Real.exp (ω * |t|) * Real.exp (-ω * Lt n) := by
      funext n
      rw [show -ω * (Lt n - |t|) = ω * |t| + (-ω * Lt n) by ring, Real.exp_add]
    rw [hfun]
    simpa using hscaled
  have hden_tend :
      Tendsto (fun n => ω * (1 - Real.exp (-ω * Lt n))) atTop (nhds ω) := by
    have hsub_tend : Tendsto (fun n => 1 - Real.exp (-ω * Lt n)) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hexp_tend
    simpa using Filter.Tendsto.const_mul ω hsub_tend
  simpa [hω_ne] using hnum_tend.div hden_tend hω_ne

/-- The **mass-gap envelope** from `abs_sub_free_le_uniform_mass_gap` tends to `0`. -/
theorem massGapEnvelope_tendsto_zero
    (mass : ℝ) (hmass : 0 < mass)
    (Lt : ℕ → ℝ)
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto
      (fun n =>
        Real.exp (-mass * Lt n / 2) /
          (mass * (1 - Real.exp (-mass * Lt n))))
      atTop (nhds 0) := by
  have hmass_ne : mass ≠ 0 := ne_of_gt hmass
  have hhalf_pos : 0 < mass / 2 := by positivity
  have hneg_tend : Tendsto (fun n => -(mass / 2) * Lt n) atTop atBot := by
    refine Filter.tendsto_atBot.mpr ?_
    intro b
    filter_upwards [(Filter.tendsto_atTop.mp hLt_tend) (-b / (mass / 2))] with n hn
    have hmul : -b ≤ Lt n * (mass / 2) := by
      rw [div_le_iff₀ hhalf_pos] at hn
      simpa [mul_comm, mul_left_comm, mul_assoc] using hn
    nlinarith
  have hnum_tend :
      Tendsto (fun n => Real.exp (-mass * Lt n / 2)) atTop (nhds 0) := by
    have hfun : (fun n => Real.exp (-mass * Lt n / 2)) =
        fun n => Real.exp (-(mass / 2) * Lt n) := by
      funext n
      congr 1
      ring
    rw [hfun]
    exact Real.tendsto_exp_atBot.comp hneg_tend
  have hden_tend :
      Tendsto (fun n => mass * (1 - Real.exp (-mass * Lt n))) atTop (nhds mass) := by
    have hneg_mass_tend : Tendsto (fun n => -mass * Lt n) atTop atBot := by
      refine Filter.tendsto_atBot.mpr ?_
      intro b
      filter_upwards [(Filter.tendsto_atTop.mp hLt_tend) (-b / mass)] with n hn
      have hmul : -b ≤ Lt n * mass := by
        rw [div_le_iff₀ hmass] at hn
        simpa [mul_comm, mul_left_comm, mul_assoc] using hn
      nlinarith
    have hexp_tend : Tendsto (fun n => Real.exp (-mass * Lt n)) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hneg_mass_tend
    have hsub_tend :
        Tendsto (fun n => 1 - Real.exp (-mass * Lt n)) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hexp_tend
    simpa using Filter.Tendsto.const_mul mass hsub_tend
  simpa [hmass_ne] using hnum_tend.div hden_tend hmass_ne

/-- Mode-wise convergence: for fixed `ω > 0` and `t`, the periodic kernel tends to the
free kernel as `Lt → ∞`. -/
theorem tendsto_periodicKernel_freeKernel
    (ω : ℝ) (hω : 0 < ω) (t : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto (fun n => periodicKernel ω (Lt n) t) atTop (nhds (freeKernel ω t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set kernel : ℕ → ℝ := fun n => periodicKernel ω (Lt n) t
  set free : ℝ := freeKernel ω t
  set err : ℕ → ℝ := fun n =>
    Real.exp (-ω * (Lt n - |t|)) /
      (ω * (1 - Real.exp (-ω * Lt n)))
  have herr_tend : Tendsto err atTop (nhds 0) :=
    wrapAroundErrorMajorant_tendsto_zero ω hω t Lt hLt_tend
  have hbound : ∀ n, |kernel n - free| ≤ err n := by
    intro n
    exact abs_sub_free_le ω hω t (Lt n) (hLt n).out
  have habs_tend : Tendsto (fun n => |kernel n - free|) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds herr_tend
      (fun _ => abs_nonneg _) hbound
  simpa [kernel, free, Real.norm_eq_abs] using habs_tend

end PeriodicResolvent1D

end
