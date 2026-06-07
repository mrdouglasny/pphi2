/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import GaussianHilbert.PolynomialChaosConcentration

/-!
# Bonami–Nelson moment form (L2-for-V glue G1)

`bonami_nelson_chaosLE` is stated in `eLpNorm` form. This file repackages it as a Bochner-integral
moment bound: for a degree-≤`d` Wiener-chaos element `F` on `stdGaussianFin n`,
`∫ |F|^p ≤ ((d+1)(p-1)^{d/2})^p · (∫ |F|²)^{p/2}` for `p ≥ 2` (rpow exponents). The reusable bridge
the `V`-moment bounds consume after chaos membership is established.
-/

namespace Pphi2

open MeasureTheory GaussianHilbert

/-- **G1 — Bonami–Nelson, moment form.** For `F` in the degree-≤`d` Wiener chaos on the standard
Gaussian, `∫ |F|^p ≤ ((d+1)(p-1)^{d/2})^p · (∫ |F|^2)^{p/2}` (`p ≥ 2`, rpow exponents). -/
theorem chaosLE_moment_le {n d : ℕ} (F : Lp ℝ 2 (stdGaussianFin n))
    (hF : F ∈ wienerChaosLE n d) (p : ℝ) (hp : 2 ≤ p) :
    ∫ ξ, |(F : (Fin n → ℝ) → ℝ) ξ| ^ p ∂(stdGaussianFin n)
      ≤ (((d : ℝ) + 1) * (p - 1) ^ ((d : ℝ) / 2)) ^ p
        * (∫ ξ, |(F : (Fin n → ℝ) → ℝ) ξ| ^ (2 : ℝ) ∂(stdGaussianFin n)) ^ (p / 2) := by
  classical
  set f : (Fin n → ℝ) → ℝ := (F : (Fin n → ℝ) → ℝ) with hf
  set C : ℝ := ((d : ℝ) + 1) * (p - 1) ^ ((d : ℝ) / 2) with hC
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) ≤ p - 1 := by linarith
  have hCnn : 0 ≤ C := by rw [hC]; positivity
  have hpne : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hp0
  have hb := bonami_nelson_chaosLE n d F hF p hp
  have hfm2 : MemLp f 2 (stdGaussianFin n) := Lp.memLp F
  have hfae : AEStronglyMeasurable f (stdGaussianFin n) := hfm2.aestronglyMeasurable
  have h2ne : eLpNorm f 2 (stdGaussianFin n) ≠ ⊤ := hfm2.eLpNorm_ne_top
  have hptop : eLpNorm f (ENNReal.ofReal p) (stdGaussianFin n) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2ne) hb
  have hfmp : MemLp f (ENNReal.ofReal p) (stdGaussianFin n) :=
    ⟨hfae, lt_top_iff_ne_top.mpr hptop⟩
  have hcp := hfmp.eLpNorm_eq_integral_rpow_norm hpne ENNReal.ofReal_ne_top
  have hc2 := hfm2.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  rw [ENNReal.toReal_ofReal hp0.le] at hcp
  rw [(by norm_num : ((2 : ENNReal).toReal) = (2 : ℝ))] at hc2
  simp only [Real.norm_eq_abs] at hcp hc2
  have hIp_nn : 0 ≤ ∫ ξ, |f ξ| ^ p ∂(stdGaussianFin n) :=
    integral_nonneg fun ξ => Real.rpow_nonneg (abs_nonneg _) _
  have hI2_nn : 0 ≤ ∫ ξ, |f ξ| ^ (2 : ℝ) ∂(stdGaussianFin n) :=
    integral_nonneg fun ξ => Real.rpow_nonneg (abs_nonneg _) _
  have hbR : (∫ ξ, |f ξ| ^ p ∂(stdGaussianFin n)) ^ p⁻¹
      ≤ C * (∫ ξ, |f ξ| ^ (2 : ℝ) ∂(stdGaussianFin n)) ^ (2 : ℝ)⁻¹ := by
    have hmono := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2ne) hb
    rw [hcp, hc2, ENNReal.toReal_ofReal (Real.rpow_nonneg hIp_nn _), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hCnn, ENNReal.toReal_ofReal (Real.rpow_nonneg hI2_nn _)] at hmono
    exact hmono
  have hkey := Real.rpow_le_rpow (Real.rpow_nonneg hIp_nn _) hbR hp0.le
  have hLHS : ((∫ ξ, |f ξ| ^ p ∂(stdGaussianFin n)) ^ p⁻¹) ^ p
      = ∫ ξ, |f ξ| ^ p ∂(stdGaussianFin n) := by
    rw [← Real.rpow_mul hIp_nn, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  have hRHS : (C * (∫ ξ, |f ξ| ^ (2 : ℝ) ∂(stdGaussianFin n)) ^ (2 : ℝ)⁻¹) ^ p
      = C ^ p * (∫ ξ, |f ξ| ^ (2 : ℝ) ∂(stdGaussianFin n)) ^ (p / 2) := by
    rw [Real.mul_rpow hCnn (Real.rpow_nonneg hI2_nn _), ← Real.rpow_mul hI2_nn,
      show (2 : ℝ)⁻¹ * p = p / 2 by ring]
  rw [hLHS, hRHS] at hkey
  exact hkey

end Pphi2
