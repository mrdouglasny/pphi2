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

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Basic

noncomputable section

open Filter
open scoped FourierTransform

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

/-- The periodic resolvent kernel is continuous in the time variable. -/
theorem continuous_periodicKernel (ω Lt : ℝ) :
    Continuous (fun t => periodicKernel ω Lt t) := by
  unfold periodicKernel
  fun_prop

/-- The free resolvent kernel is continuous in the time variable. -/
theorem continuous_freeKernel (ω : ℝ) : Continuous (fun t => freeKernel ω t) := by
  unfold freeKernel
  fun_prop

/-- Under Mathlib's analyst-normalized Fourier transform, the whole-line massive
resolvent kernel `e^{-ω|t|} / (2ω)` transforms to `(ω² + (2πξ)²)⁻¹`. -/
theorem fourier_freeKernel (ω : ℝ) (hω : 0 < ω) (ξ : ℝ) :
    FourierTransform.fourier (fun t : ℝ => ((freeKernel ω t : ℝ) : ℂ)) ξ =
      ((((ω ^ 2 + (2 * Real.pi * ξ) ^ 2)⁻¹ : ℝ)) : ℂ) := by
  let factor : ℂ := ((1 / (2 * ω : ℝ)) : ℂ)
  let aNeg : ℂ := (ω : ℂ) - (2 * Real.pi * ξ) * Complex.I
  let aPos : ℂ := (ω : ℂ) + (2 * Real.pi * ξ) * Complex.I
  let integrand : ℝ → ℂ := fun t => 𝐞 (-t * ξ) • (((freeKernel ω t : ℝ) : ℂ))
  have haNeg_re : 0 < aNeg.re := by
    simp [aNeg, hω]
  have hminus_aPos_re : (-aPos).re < 0 := by
    simp [aPos, hω]
  have h_left_eq : Set.EqOn integrand (fun t => factor * Complex.exp (aNeg * t)) (Set.Iic 0) := by
    intro t ht
    have ht' : t ≤ 0 := ht
    have habs : |t| = -t := abs_of_nonpos ht'
    rw [show integrand t =
        Complex.exp (↑(2 * Real.pi * (-t * ξ)) * Complex.I) * (((freeKernel ω t : ℝ) : ℂ)) by
      simp [integrand, Real.fourierChar_apply, Circle.smul_def]]
    rw [show (((freeKernel ω t : ℝ) : ℂ)) = factor * Complex.exp ((ω : ℂ) * t) by
      simp [freeKernel, factor, habs, Complex.ofReal_exp, div_eq_mul_inv]
      ring]
    rw [mul_assoc, mul_left_comm, ← Complex.exp_add]
    congr 1
    simp [aNeg]
    ring_nf
  have h_right_eq :
      Set.EqOn integrand (fun t => factor * Complex.exp ((-aPos) * t)) (Set.Ioi 0) := by
    intro t ht
    have ht' : 0 ≤ t := le_of_lt ht
    have habs : |t| = t := abs_of_nonneg ht'
    rw [show integrand t =
        Complex.exp (↑(2 * Real.pi * (-t * ξ)) * Complex.I) * (((freeKernel ω t : ℝ) : ℂ)) by
      simp [integrand, Real.fourierChar_apply, Circle.smul_def]]
    rw [show (((freeKernel ω t : ℝ) : ℂ)) = factor * Complex.exp ((-ω : ℂ) * t) by
      simp [freeKernel, factor, habs, Complex.ofReal_exp, div_eq_mul_inv]
      ring]
    rw [mul_assoc, mul_left_comm, ← Complex.exp_add]
    congr 1
    simp [aPos]
    ring_nf
  have h_left_model :
      MeasureTheory.IntegrableOn (fun t : ℝ => factor * Complex.exp (aNeg * t)) (Set.Iic 0) := by
    exact (integrableOn_exp_mul_complex_Iic haNeg_re 0).const_mul factor
  have h_right_model :
      MeasureTheory.IntegrableOn (fun t : ℝ => factor * Complex.exp ((-aPos) * t)) (Set.Ioi 0) := by
    exact (integrableOn_exp_mul_complex_Ioi hminus_aPos_re 0).const_mul factor
  have h_left_int :
      MeasureTheory.IntegrableOn integrand (Set.Iic 0) := by
    exact MeasureTheory.IntegrableOn.congr_fun h_left_model
      (fun t ht => (h_left_eq ht).symm) measurableSet_Iic
  have h_right_int :
      MeasureTheory.IntegrableOn integrand (Set.Ioi 0) := by
    exact MeasureTheory.IntegrableOn.congr_fun h_right_model
      (fun t ht => (h_right_eq ht).symm) measurableSet_Ioi
  rw [Real.fourier_eq]
  have hfourier_integrand :
      (∫ t : ℝ, 𝐞 (-inner ℝ t ξ) • (((freeKernel ω t : ℝ) : ℂ))) =
        ∫ t : ℝ, integrand t := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    have hinner' : inner ℝ t ξ = ξ * star t := by
      exact RCLike.inner_apply t ξ
    have hinner : inner ℝ t ξ = ξ * t := by
      simpa using hinner'
    rw [hinner]
    have hmul : -(ξ * t) = -t * ξ := by ring
    rw [hmul]
  rw [hfourier_integrand]
  have hsplit :
      ∫ t : ℝ, integrand t =
        (∫ t in Set.Iic 0, integrand t) + ∫ t in Set.Ioi 0, integrand t := by
    rw [← MeasureTheory.setIntegral_univ (f := integrand), ← Set.Iic_union_Ioi]
    exact MeasureTheory.setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      h_left_int h_right_int
  rw [hsplit]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Iic h_left_eq]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_right_eq]
  have hleft_const :
      (∫ x : ℝ in Set.Iic (0 : ℝ), factor * Complex.exp (aNeg * x) ∂MeasureTheory.volume) =
        factor * ∫ x : ℝ in Set.Iic (0 : ℝ), Complex.exp (aNeg * x) ∂MeasureTheory.volume := by
    simpa using
      (MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict (Set.Iic (0 : ℝ)))
        factor (fun x : ℝ => Complex.exp (aNeg * x)))
  have hright_const :
      (∫ x : ℝ in Set.Ioi (0 : ℝ), factor * Complex.exp (-aPos * x) ∂MeasureTheory.volume) =
        factor * ∫ x : ℝ in Set.Ioi (0 : ℝ), Complex.exp (-aPos * x) ∂MeasureTheory.volume := by
    simpa using
      (MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        factor (fun x : ℝ => Complex.exp (-aPos * x)))
  rw [hleft_const, hright_const]
  rw [integral_exp_mul_complex_Iic haNeg_re 0, integral_exp_mul_complex_Ioi hminus_aPos_re 0]
  change
    factor * (Complex.exp (aNeg * (0 : ℂ)) / aNeg) +
      factor * (-Complex.exp (-aPos * (0 : ℂ)) / -aPos) =
        ((((ω ^ 2 + (2 * Real.pi * ξ) ^ 2)⁻¹ : ℝ)) : ℂ)
  rw [mul_zero, mul_zero]
  rw [Complex.exp_zero]
  rw [show ((1 : ℂ) / aNeg) = (aNeg)⁻¹ by
    rw [one_div]]
  rw [show (-((1 : ℂ)) / (-aPos)) = (aPos)⁻¹ by
    rw [div_eq_mul_inv]
    ring_nf]
  have hfactor : factor = ((↑ω)⁻¹ * 2⁻¹ : ℂ) := by
    calc
      factor = ((((2 * ω : ℝ)) : ℂ))⁻¹ := by
        simp [factor, one_div]
      _ = (((2 : ℂ) * (ω : ℂ)))⁻¹ := by
        norm_num
      _ = (ω : ℂ)⁻¹ * (2 : ℂ)⁻¹ := by
        rw [mul_inv_rev]
      _ = ((↑ω)⁻¹ * 2⁻¹ : ℂ) := by
        norm_num
  have haNeg_ne : aNeg ≠ 0 := by
    intro h
    have : aNeg.re = 0 := by simp [h]
    linarith
  have haPos_ne : aPos ≠ 0 := by
    intro h
    have hRe : aPos.re = 0 := by simp [h]
    have hω_zero : ω = 0 := by
      simpa [aPos] using hRe
    exact hω.ne' hω_zero
  rw [hfactor]
  rw [show ((↑ω)⁻¹ * 2⁻¹ * (aNeg)⁻¹ + (↑ω)⁻¹ * 2⁻¹ * (aPos)⁻¹ : ℂ) =
      ((↑ω)⁻¹ * 2⁻¹ : ℂ) * (((aNeg)⁻¹ : ℂ) + (aPos)⁻¹) by ring]
  have hsum_num : aPos + aNeg = ((2 * ω : ℝ) : ℂ) := by
    simp [aPos, aNeg]
    ring
  have hprod : aPos * aNeg = (((ω ^ 2 + (2 * Real.pi * ξ) ^ 2) : ℝ) : ℂ) := by
    simp [aPos, aNeg]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
  have hsum_recip :
      (aNeg)⁻¹ + (aPos)⁻¹ = ((2 * ω : ℝ) : ℂ) *
        ((((ω ^ 2 + (2 * Real.pi * ξ) ^ 2)⁻¹ : ℝ)) : ℂ) := by
    calc
      (aNeg)⁻¹ + (aPos)⁻¹ = (aPos + aNeg) / (aPos * aNeg) := by
        field_simp [haNeg_ne, haPos_ne]
      _ = ((2 * ω : ℝ) : ℂ) / ((((ω ^ 2 + (2 * Real.pi * ξ) ^ 2) : ℝ) : ℂ)) := by
        rw [hsum_num, hprod]
      _ = ((2 * ω : ℝ) : ℂ) * ((((ω ^ 2 + (2 * Real.pi * ξ) ^ 2)⁻¹ : ℝ)) : ℂ) := by
        simp [div_eq_mul_inv]
  rw [hsum_recip]
  have hdenom :
      ((((ω ^ 2 + (2 * Real.pi * ξ) ^ 2) : ℝ)) : ℂ) =
        ↑ω ^ 2 + 2 ^ 2 * ↑Real.pi ^ 2 * ↑ξ ^ 2 := by
    norm_num
    ring
  rw [show ((((ω ^ 2 + (2 * Real.pi * ξ) ^ 2)⁻¹ : ℝ)) : ℂ) =
      ((((ω ^ 2 + (2 * Real.pi * ξ) ^ 2) : ℝ)) : ℂ)⁻¹ by
    simp]
  rw [hdenom]
  have hωc_ne : (ω : ℂ) ≠ 0 := by
    exact_mod_cast hω.ne'
  field_simp [hωc_ne]
  simp [mul_comm]

/-- Under Mathlib's analyst-normalized Fourier transform, the symbol
`(ξ² + ω²)⁻¹` corresponds to the scaled exponential kernel
`(π / ω) * exp (-(2π ω) |t|)`. Equivalently, it is `(2π)² * freeKernel (2π ω)`. -/
theorem fourier_mathlib_resolventKernel (ω : ℝ) (hω : 0 < ω) (ξ : ℝ) :
    FourierTransform.fourier
      (fun t : ℝ => (((Real.pi / ω * Real.exp (-(2 * Real.pi * ω) * |t|) : ℝ)) : ℂ)) ξ =
        ((((ξ ^ 2 + ω ^ 2)⁻¹ : ℝ)) : ℂ) := by
  let c : ℂ := ((((2 * Real.pi) ^ 2 : ℝ)) : ℂ)
  let k : ℝ → ℂ := fun t : ℝ => ((freeKernel (2 * Real.pi * ω) t : ℝ) : ℂ)
  have hk : (fun t : ℝ => (((Real.pi / ω * Real.exp (-(2 * Real.pi * ω) * |t|) : ℝ)) : ℂ))
      = c • k := by
    ext t
    simp [c, k, freeKernel, div_eq_mul_inv]
    have hω_ne : ω ≠ 0 := hω.ne'
    field_simp [hω_ne, Real.pi_ne_zero]
  rw [hk, Real.fourier_eq]
  simp only [Pi.smul_apply, Circle.smul_def, smul_eq_mul]
  rw [show (fun v : ℝ => ↑(Real.fourierChar (-inner ℝ v ξ)) * (c * k v)) =
      fun v : ℝ => c * (↑(Real.fourierChar (-inner ℝ v ξ)) * k v) by
    ext v
    ring]
  rw [show (∫ v : ℝ, c * (↑(Real.fourierChar (-inner ℝ v ξ)) * k v)) =
      c * ∫ v : ℝ, ↑(Real.fourierChar (-inner ℝ v ξ)) * k v by
    simpa using
      (MeasureTheory.integral_const_mul (μ := MeasureTheory.volume) c
        (fun v : ℝ => ↑(Real.fourierChar (-inner ℝ v ξ)) * k v))]
  rw [show (∫ v : ℝ, ↑(Real.fourierChar (-inner ℝ v ξ)) * k v) =
      FourierTransform.fourier k ξ by
    rw [Real.fourier_eq]
    simp [Circle.smul_def]]
  rw [show FourierTransform.fourier k ξ =
      (((( (2 * Real.pi * ω) ^ 2 + (2 * Real.pi * ξ) ^ 2)⁻¹ : ℝ)) : ℂ) by
    simpa [k] using fourier_freeKernel (2 * Real.pi * ω) (by positivity) ξ]
  have hA_ne : (((2 * Real.pi) ^ 2 : ℝ)) ≠ 0 := by positivity
  have hS_ne : (ω ^ 2 + ξ ^ 2 : ℝ) ≠ 0 := by positivity
  have hreal :
      (((2 * Real.pi) ^ 2 : ℝ)) *
          (((((2 * Real.pi * ω) ^ 2 + (2 * Real.pi * ξ) ^ 2)⁻¹ : ℝ))) =
        (ξ ^ 2 + ω ^ 2)⁻¹ := by
    calc
      (((2 * Real.pi) ^ 2 : ℝ)) *
          (((((2 * Real.pi * ω) ^ 2 + (2 * Real.pi * ξ) ^ 2)⁻¹ : ℝ)))
        = (((2 * Real.pi) ^ 2 : ℝ)) *
            ((((((2 * Real.pi) ^ 2) * (ω ^ 2 + ξ ^ 2))⁻¹ : ℝ))) := by
              congr 1
              ring
      _ = (ξ ^ 2 + ω ^ 2)⁻¹ := by
            field_simp [hA_ne, hS_ne]
            ring
  change ((((2 * Real.pi) ^ 2 : ℝ)) : ℂ) *
      ((((((2 * Real.pi * ω) ^ 2 + (2 * Real.pi * ξ) ^ 2)⁻¹ : ℝ)) : ℂ)) =
        (((((ξ ^ 2 + ω ^ 2)⁻¹ : ℝ)) : ℂ))
  exact_mod_cast hreal

/-- The Mathlib-normalized resolvent kernel is exactly a scaled physical free resolvent kernel,
with both amplitude and frequency rescaled by `2π`. -/
theorem mathlibResolventKernel_eq_scaled_freeKernel
    (ω : ℝ) (hω : 0 < ω) (t : ℝ) :
    Real.pi / ω * Real.exp (-(2 * Real.pi * ω) * |t|) =
      ((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) t := by
  have hω_ne : ω ≠ 0 := hω.ne'
  simp [freeKernel, div_eq_mul_inv]
  field_simp [hω_ne, Real.pi_ne_zero]

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

/-- Compact-window form of `abs_sub_free_le_uniform_mass_gap`.

On a fixed window `[-R, R]`, once the period satisfies `2 * R + 1 ≤ Lt`, every
point in the window lies in the half-period strip `|t| < Lt / 2`, so the
mass-gap envelope controls the periodic/free resolvent error uniformly there. -/
theorem abs_sub_free_le_on_compact_of_mass_gap
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω)
    (t R Lt : ℝ) (hLt : 0 < Lt)
    (ht : t ∈ Set.Icc (-R) R) (hLt_large : 2 * R + 1 ≤ Lt) :
    |periodicKernel ω Lt t - freeKernel ω t| ≤
      Real.exp (-mass * Lt / 2) /
        (mass * (1 - Real.exp (-mass * Lt))) := by
  have ht_bounds : -R ≤ t ∧ t ≤ R := by
    simpa [Set.mem_Icc] using ht
  have ht_abs : |t| ≤ R := by
    rw [abs_le]
    exact ht_bounds
  have ht_strip : |t| < Lt / 2 := by
    nlinarith
  exact abs_sub_free_le_uniform_mass_gap ω mass hmass hω t Lt hLt ht_strip

/-- Uniform convergence of the periodic resolvent kernel to the free resolvent on any fixed
compact time window, using only the mass gap `mass ≤ ω`. -/
theorem tendstoUniformlyOn_periodicKernel_freeKernel_compact_of_mass_gap
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω)
    (R : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn (fun n t => periodicKernel ω (Lt n) t) (fun t => freeKernel ω t)
      atTop (Set.Icc (-R) R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have h_env_tend :
      Tendsto
        (fun n =>
          Real.exp (-mass * Lt n / 2) /
            (mass * (1 - Real.exp (-mass * Lt n))))
        atTop (nhds 0) :=
    massGapEnvelope_tendsto_zero mass hmass Lt hLt_tend
  have h_env_small :
      ∀ᶠ n in atTop,
        dist
          (Real.exp (-mass * Lt n / 2) /
            (mass * (1 - Real.exp (-mass * Lt n))))
          0 < ε :=
    Metric.tendsto_nhds.mp h_env_tend ε hε
  have h_period_large : ∀ᶠ n in atTop, 2 * R + 1 ≤ Lt n :=
    (Filter.tendsto_atTop.mp hLt_tend) (2 * R + 1)
  filter_upwards [h_env_small, h_period_large] with n hsmall hlarge t ht
  have hLt_exp_lt : Real.exp (-mass * Lt n) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [hmass, (hLt n).out]
  have hden_pos : 0 < mass * (1 - Real.exp (-mass * Lt n)) := by
    exact mul_pos hmass (sub_pos.mpr hLt_exp_lt)
  have henv_nonneg :
      0 ≤
        Real.exp (-mass * Lt n / 2) /
          (mass * (1 - Real.exp (-mass * Lt n))) := by
    exact div_nonneg (by positivity) hden_pos.le
  have hsmall_sub :
      |(Real.exp (-mass * Lt n / 2) /
        (mass * (1 - Real.exp (-mass * Lt n)))) - 0| < ε := by
    have hsmall' := hsmall
    rw [Real.dist_eq] at hsmall'
    exact hsmall'
  have hsmall' :
      Real.exp (-mass * Lt n / 2) /
        (mass * (1 - Real.exp (-mass * Lt n))) < ε := by
    have hsmall_abs :
        |Real.exp (-mass * Lt n / 2) /
          (mass * (1 - Real.exp (-mass * Lt n)))| < ε := by
      simpa using hsmall_sub
    rwa [abs_of_nonneg henv_nonneg] at hsmall_abs
  simpa [Real.dist_eq, abs_sub_comm] using
    (abs_sub_free_le_on_compact_of_mass_gap ω mass hmass hω t R (Lt n)
      (hLt n).out ht hlarge).trans_lt hsmall'

/-- Fixed-frequency compact-window uniform convergence, obtained by specializing the
mass-gap version to `mass = ω`. -/
theorem tendstoUniformlyOn_periodicKernel_freeKernel_compact
    (ω : ℝ) (hω : 0 < ω)
    (R : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn (fun n t => periodicKernel ω (Lt n) t) (fun t => freeKernel ω t)
      atTop (Set.Icc (-R) R) := by
  simpa using
    tendstoUniformlyOn_periodicKernel_freeKernel_compact_of_mass_gap
      (ω := ω) (mass := ω) hω (le_rfl : ω ≤ ω) R Lt hLt hLt_tend

/-- Two-variable compact-box version of
`tendstoUniformlyOn_periodicKernel_freeKernel_compact_of_mass_gap`.

On `[-R, R] × [-R, R]`, the difference variable `t - s` ranges over `[-2R, 2R]`, so the
one-variable compact convergence theorem pulls back directly to the bilinear kernel
`(t, s) ↦ periodicKernel ω (Lt n) (t - s)`. -/
theorem tendstoUniformlyOn_periodicKernel_freeKernel_compactDiffBox_of_mass_gap
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω)
    (R : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun n (p : ℝ × ℝ) => periodicKernel ω (Lt n) (p.1 - p.2))
      (fun p => freeKernel ω (p.1 - p.2))
      atTop (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hcompact :=
    Metric.tendstoUniformlyOn_iff.mp
      (tendstoUniformlyOn_periodicKernel_freeKernel_compact_of_mass_gap
        ω mass hmass hω (2 * R) Lt hLt hLt_tend) ε hε
  filter_upwards [hcompact] with n hn p hp
  rcases hp with ⟨hp1, hp2⟩
  rcases hp1 with ⟨hp1l, hp1u⟩
  rcases hp2 with ⟨hp2l, hp2u⟩
  have hdiff : p.1 - p.2 ∈ Set.Icc (-(2 * R)) (2 * R) := by
    rw [Set.mem_Icc]
    constructor <;> nlinarith
  simpa using hn (p.1 - p.2) hdiff

/-- Fixed-frequency specialization of
`tendstoUniformlyOn_periodicKernel_freeKernel_compactDiffBox_of_mass_gap`. -/
theorem tendstoUniformlyOn_periodicKernel_freeKernel_compactDiffBox
    (ω : ℝ) (hω : 0 < ω)
    (R : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun n (p : ℝ × ℝ) => periodicKernel ω (Lt n) (p.1 - p.2))
      (fun p => freeKernel ω (p.1 - p.2))
      atTop (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) := by
  simpa using
    tendstoUniformlyOn_periodicKernel_freeKernel_compactDiffBox_of_mass_gap
      (ω := ω) (mass := ω) hω (le_rfl : ω ≤ ω) R Lt hLt hLt_tend

end PeriodicResolvent1D

end
