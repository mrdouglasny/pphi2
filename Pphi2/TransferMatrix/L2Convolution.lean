/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L² Convolution Operators via Young's Inequality

Convolution with an L¹ function defines a continuous linear map on L².
This is Young's inequality for exponents (1, 2, 2), a standard result
not yet in Mathlib (listed as a "To do" in Analysis/Convolution.lean).

We axiomatize Young's inequality and construct the convolution CLM.
This is used to build the transfer operator from its kernel factorization
T = M_w ∘ Conv_G ∘ M_w.

## Main definitions

- `young_convolution_bound` — Axiom: `‖g ⋆ f‖₂ ≤ ‖g‖₁ · ‖f‖₂` (Young's inequality)
- `convCLM` — Given `g ∈ L¹`, convolution with `g` as a CLM on L²
- `convCLM_spec` — Pointwise specification via the integral formula

## References

- Reed-Simon II, §IX.4 (Young's inequality)
- Stein-Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Theorem 1.2
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped ENNReal Convolution

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace G] [BorelSpace G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]

/-- Shorthand for real-valued convolution with explicit measure:
`realConv μ g f x = ∫ t, g t * f (x - t) ∂μ`. -/
def realConv (μ : Measure G) (g f : G → ℝ) : G → ℝ :=
  convolution g f (lsmul ℝ ℝ) μ

/-! ## Young's inequality (axiomatized)

Young's inequality for exponents (1, 2, 2): if `g ∈ L¹` and `f ∈ L²`,
then `g ⋆ f ∈ L²` with `‖g ⋆ f‖₂ ≤ ‖g‖₁ · ‖f‖₂`.

This is a standard result (Reed-Simon II, §IX.4; Stein-Weiss, Thm 1.2)
that requires Minkowski's integral inequality for its proof. It is listed
as a "To do" in Mathlib's `Analysis/Convolution.lean`.

The measure `μ` must be a Haar measure (translation-invariant) for the
inequality to hold. -/

/-- Young's inequality: convolution of `g ∈ L¹` with `f ∈ L²` is in `L²`. -/
axiom young_convolution_memLp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (g : G → ℝ) (f : G → ℝ)
    (hg : MemLp g 1 μ) (hf : MemLp f 2 μ) :
    MemLp (realConv μ g f) 2 μ

/-- Young's inequality norm bound: `‖g ⋆ f‖₂ ≤ ‖g‖₁ · ‖f‖₂`.

Proof sketch: By Minkowski's integral inequality,
  `‖g ⋆ f‖₂ = ‖∫ g(t) · f(· - t) dt‖₂ ≤ ∫ |g(t)| · ‖f(· - t)‖₂ dt`
and `‖f(· - t)‖₂ = ‖f‖₂` by translation invariance of Haar measure,
so `≤ ‖f‖₂ · ∫ |g(t)| dt = ‖f‖₂ · ‖g‖₁`. -/
axiom young_convolution_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (g : G → ℝ) (f : G → ℝ)
    (hg : MemLp g 1 μ) (hf : MemLp f 2 μ) :
    eLpNorm (realConv μ g f) 2 μ ≤ eLpNorm g 1 μ * eLpNorm f 2 μ

/-- Convolution is additive in the second argument a.e.: `g ⋆ (f₁ + f₂) =ᵐ g ⋆ f₁ + g ⋆ f₂`.

Proof: By Fubini/Tonelli, the convolution integrand `t ↦ g(t) · fᵢ(x-t)` is
integrable for a.e. `x` (using the bound `ab ≤ a + ab²` and the L¹×L¹ Fubini
theorem on `|g|` and `fᵢ²`). At such points, `integral_add` gives pointwise
equality via `ConvolutionExistsAt.distrib_add`. -/
theorem young_convolution_ae_add {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (g : G → ℝ) (f1 f2 : G → ℝ)
    (hg : MemLp g 1 μ) (hf1 : MemLp f1 2 μ) (hf2 : MemLp f2 2 μ) :
    realConv μ g (f1 + f2) =ᵐ[μ] realConv μ g f1 + realConv μ g f2 := by
  -- Step 1: Basic integrability from MemLp hypotheses
  have hg_int : Integrable g μ := memLp_one_iff_integrable.mp hg
  have hg_norm : Integrable (fun t => ‖g t‖) μ := hg_int.norm
  have hf1_sq : Integrable (fun x => f1 x ^ 2) μ := hf1.integrable_sq
  have hf2_sq : Integrable (fun x => f2 x ^ 2) μ := hf2.integrable_sq
  -- Step 2: By Fubini (L¹ × L¹), ∫ ‖g(t)‖ · fᵢ(x-t)² dt < ∞ for a.e. x
  have hae_sq1 : ∀ᵐ x ∂μ, ConvolutionExistsAt (fun t => ‖g t‖) (fun x => f1 x ^ 2) x
      (mul ℝ ℝ) μ :=
    Integrable.ae_convolution_exists (mul ℝ ℝ) hg_norm hf1_sq
  have hae_sq2 : ∀ᵐ x ∂μ, ConvolutionExistsAt (fun t => ‖g t‖) (fun x => f2 x ^ 2) x
      (mul ℝ ℝ) μ :=
    Integrable.ae_convolution_exists (mul ℝ ℝ) hg_norm hf2_sq
  -- Step 3: ConvolutionExistsAt g fᵢ x for a.e. x
  -- Using: ‖g(t)‖ * ‖fᵢ(x-t)‖ ≤ ‖g(t)‖ + ‖g(t)‖ * fᵢ(x-t)² (since b ≤ 1 + b²)
  have hab : ∀ (a b : ℝ), 0 ≤ a → a * ‖b‖ ≤ a + a * b ^ 2 := by
    intro a b ha
    rw [Real.norm_eq_abs]
    have hb : |b| ≤ 1 + b ^ 2 := by nlinarith [abs_nonneg b, sq_abs b, sq_nonneg (|b| - 1)]
    nlinarith [mul_nonneg ha (abs_nonneg b)]
  -- Measurability of convolution integrands
  have hg_meas := hg.aestronglyMeasurable
  have hf1_meas := hf1.aestronglyMeasurable
  have hf2_meas := hf2.aestronglyMeasurable
  have hae_conv1 : ∀ᵐ x ∂μ, ConvolutionExistsAt g f1 x (lsmul ℝ ℝ) μ := by
    filter_upwards [hae_sq1] with x hx_sq
    apply ConvolutionExistsAt.of_norm (L := lsmul ℝ ℝ)
    · -- Show ∫ ‖g(t)‖ * ‖f1(x-t)‖ dt < ∞
      apply Integrable.mono (hg_norm.add hx_sq)
      · exact hg_meas.norm.mul
          (hf1_meas.norm.comp_quasiMeasurePreserving
            (quasiMeasurePreserving_sub_left_of_right_invariant μ x))
      · apply ae_of_all; intro t
        simp only [ContinuousLinearMap.mul_apply', Pi.add_apply]
        rw [norm_mul, norm_norm, norm_norm]
        calc ‖g t‖ * ‖f1 (x - t)‖
            ≤ ‖g t‖ + ‖g t‖ * f1 (x - t) ^ 2 := hab ‖g t‖ (f1 (x - t)) (norm_nonneg _)
          _ = ‖‖g t‖ + ‖g t‖ * f1 (x - t) ^ 2‖ :=
            (Real.norm_of_nonneg (by positivity)).symm
    · exact hg_meas
    · exact hf1_meas
  have hae_conv2 : ∀ᵐ x ∂μ, ConvolutionExistsAt g f2 x (lsmul ℝ ℝ) μ := by
    filter_upwards [hae_sq2] with x hx_sq
    apply ConvolutionExistsAt.of_norm (L := lsmul ℝ ℝ)
    · apply Integrable.mono (hg_norm.add hx_sq)
      · exact hg_meas.norm.mul
          (hf2_meas.norm.comp_quasiMeasurePreserving
            (quasiMeasurePreserving_sub_left_of_right_invariant μ x))
      · apply ae_of_all; intro t
        simp only [ContinuousLinearMap.mul_apply', Pi.add_apply]
        rw [norm_mul, norm_norm, norm_norm]
        calc ‖g t‖ * ‖f2 (x - t)‖
            ≤ ‖g t‖ + ‖g t‖ * f2 (x - t) ^ 2 := hab ‖g t‖ (f2 (x - t)) (norm_nonneg _)
          _ = ‖‖g t‖ + ‖g t‖ * f2 (x - t) ^ 2‖ :=
            (Real.norm_of_nonneg (by positivity)).symm
    · exact hg_meas
    · exact hf2_meas
  -- Step 4: Apply ConvolutionExistsAt.distrib_add pointwise a.e.
  filter_upwards [hae_conv1, hae_conv2] with x h1 h2
  exact h1.distrib_add h2


/-! ## Convolution CLM construction

Given `g ∈ L¹(μ)`, we construct convolution with `g` as a continuous
linear map on `L²(μ)`, using Young's inequality for the norm bound. -/

/-- Convolution with a fixed `g ∈ L¹` as a continuous linear map on `L²`.

Construction: The map `f ↦ g ⋆ f` is linear (convolution is linear in the
second argument) and bounded by `‖g‖₁` via Young's inequality. We use
`LinearMap.mkContinuous` to package this. -/
noncomputable def convCLM {μ : Measure G} [μ.IsAddHaarMeasure]
    (g : G → ℝ) (hg : MemLp g 1 μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := by
  refine LinearMap.mkContinuous
    { toFun := fun f =>
        (young_convolution_memLp g (⇑f) hg (Lp.memLp f)).toLp (realConv μ g ⇑f)
      map_add' := fun f1 f2 => by
        -- Use toLp_congr to reduce to ae equality, then toLp_add
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        -- Step 1: ↑↑(f1+f2) =ᵐ ↑↑f1 + ↑↑f2, so by convolution_congr:
        have hcongr : realConv μ g (↑↑f1 + ↑↑f2) = realConv μ g ↑↑(f1 + f2) :=
          convolution_congr (lsmul ℝ ℝ) (ae_eq_refl g) (Lp.coeFn_add f1 f2).symm
        -- Step 2: linearity of convolution in second argument (axiom)
        have hlin := young_convolution_ae_add g (⇑f1) (⇑f2) hg (Lp.memLp f1) (Lp.memLp f2)
        -- Combine: realConv μ g ↑↑(f1+f2) = realConv μ g (↑↑f1+↑↑f2) =ᵐ ...
        calc realConv μ g ↑↑(f1 + f2)
            = realConv μ g (↑↑f1 + ↑↑f2) := hcongr.symm
          _ =ᵐ[μ] realConv μ g ↑↑f1 + realConv μ g ↑↑f2 := hlin
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        rw [← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        -- Step 1: ↑↑(c • f) =ᵐ c • ↑↑f, so by convolution_congr:
        have hcongr : realConv μ g (c • ↑↑f) = realConv μ g ↑↑(c • f) :=
          convolution_congr (lsmul ℝ ℝ) (ae_eq_refl g) (Lp.coeFn_smul c f).symm
        -- Step 2: convolution_smul gives pointwise: g ⋆ (c • f) = c • (g ⋆ f)
        have hsmul : realConv μ g (c • ↑↑f) = c • realConv μ g ↑↑f :=
          convolution_smul
        -- Combine: pointwise equality implies ae equality
        exact ae_of_all _ (fun x => by rw [← hsmul, ← hcongr])
    }
    (eLpNorm g 1 μ).toReal
    (fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [Lp.norm_toLp, Lp.norm_def]
      have hbound := young_convolution_bound g (⇑f) hg (Lp.memLp f)
      have h1 : eLpNorm g 1 μ ≠ ⊤ := hg.eLpNorm_ne_top
      have h2 : eLpNorm f 2 μ ≠ ⊤ := (Lp.memLp f).eLpNorm_ne_top
      calc (eLpNorm (realConv μ g ⇑f) 2 μ).toReal
          ≤ (eLpNorm g 1 μ * eLpNorm (⇑f) 2 μ).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top h1 h2) hbound
        _ = _ := ENNReal.toReal_mul)

/-- The convolution CLM acts pointwise as the integral:
`(Conv_g f)(x) = ∫ g(t) · f(x - t) dt` a.e. -/
lemma convCLM_spec {μ : Measure G} [μ.IsAddHaarMeasure]
    (g : G → ℝ) (hg : MemLp g 1 μ)
    (f : Lp ℝ 2 μ) :
    (convCLM g hg f : G → ℝ) =ᵐ[μ] realConv μ g ⇑f := by
  simp only [convCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact MemLp.coeFn_toLp _

/-- Convolution by an even kernel is self-adjoint on `L²`.

For additive Haar measure and `g(-x) = g(x)`, one has
`⟨f, convCLM g hg h⟩ = ⟨convCLM g hg f, h⟩`.

This is the standard Fubini + kernel-symmetry argument. We keep it axiomatic
here to isolate the current integration API gap in the `L²`-level proof. -/
axiom convCLM_isSelfAdjoint_of_even {μ : Measure G} [μ.IsAddHaarMeasure]
    (g : G → ℝ) (hg : MemLp g 1 μ)
    (heven : ∀ x : G, g (-x) = g x) :
    IsSelfAdjoint (convCLM g hg)

end
