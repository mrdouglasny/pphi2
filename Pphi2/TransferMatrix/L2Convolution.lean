/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L² Convolution Operators via Young's Inequality

Convolution with an L¹ function defines a continuous linear map on L².
This is Young's inequality for exponents (1, 2, 2), a standard result
not yet in Mathlib (listed as a "To do" in Analysis/Convolution.lean).

We prove Young's inequality and construct the convolution CLM.
This is used to build the transfer operator from its kernel factorization
T = M_w ∘ Conv_G ∘ M_w.

## Main definitions

- `young_convolution_bound` — `‖g ⋆ f‖₂ ≤ ‖g‖₁ · ‖f‖₂` (Young's inequality)
- `convCLM` — Given `g ∈ L¹`, convolution with `g` as a CLM on L²
- `convCLM_spec` — Pointwise specification via the integral formula

## References

- Reed-Simon II, §IX.4 (Young's inequality)
- Stein-Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Theorem 1.2
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Group.LIntegral

noncomputable section

open MeasureTheory ContinuousLinearMap
open scoped ENNReal Convolution

set_option linter.unusedSectionVars false

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace G] [BorelSpace G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]

/-- Shorthand for real-valued convolution with explicit measure:
`realConv μ g f x = ∫ t, g t * f (x - t) ∂μ`. -/
def realConv (μ : Measure G) (g f : G → ℝ) : G → ℝ :=
  convolution g f (lsmul ℝ ℝ) μ

/-! ## Young's inequality

Young's inequality for exponents (1, 2, 2): if `g ∈ L¹` and `f ∈ L²`,
then `g ⋆ f ∈ L²` with `‖g ⋆ f‖₂ ≤ ‖g‖₁ · ‖f‖₂`.

This is a standard result (Reed-Simon II, §IX.4; Stein-Weiss, Thm 1.2).
The proof uses the Cauchy-Schwarz inequality applied to the convolution
integrand, Fubini's theorem, and translation invariance of Haar measure.

The measure `μ` must be a Haar measure (translation-invariant) for the
inequality to hold. -/

/-- Weighted Cauchy-Schwarz for lintegral: `(∫⁻ w·a)² ≤ (∫⁻ w)·(∫⁻ w·a²)`.

Proved via Hölder's inequality with p = q = 2 applied to
`u = w^{1/2}` and `v = w^{1/2}·a`. -/
private lemma lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w a : α → ℝ≥0∞} (hw : AEMeasurable w μ) (ha : AEMeasurable a μ) :
    (∫⁻ x, w x * a x ∂μ) ^ (2 : ℕ) ≤
    (∫⁻ x, w x ∂μ) * ∫⁻ x, w x * a x ^ (2 : ℝ) ∂μ := by
  -- Helper: (x ^ (2⁻¹ : ℝ)) ^ (2 : ℝ) = x for ENNReal
  have rpow_half_sq : ∀ (x : ℝ≥0∞), (x ^ ((2 : ℝ)⁻¹)) ^ (2 : ℝ) = x := by
    intro x
    rw [ENNReal.rpow_two, sq,
        ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity),
        show (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = (1 : ℝ) from by norm_num, ENNReal.rpow_one]
  -- Measurability of u = w^{1/2} and v = w^{1/2}·a
  have hu : AEMeasurable (fun x => w x ^ ((2 : ℝ)⁻¹)) μ := hw.pow_const _
  have hv : AEMeasurable (fun x => w x ^ ((2 : ℝ)⁻¹) * a x) μ := hu.mul ha
  -- Key identities: u·v = w·a, u² = w, v² = w·a²
  have huv : ∀ x, w x ^ ((2 : ℝ)⁻¹) * (w x ^ ((2 : ℝ)⁻¹) * a x) = w x * a x := by
    intro x; rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity),
        show (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = (1 : ℝ) from by norm_num, ENNReal.rpow_one]
  -- Apply Hölder's inequality with p = q = 2
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hu hv
  -- Simplify the Hölder bound using the key identities
  simp_rw [Pi.mul_apply, huv] at hH
  -- After simp_rw, we have:
  -- hH : ∫⁻ w·a ≤ (∫⁻ (w^{1/2})^2)^(1/2) · (∫⁻ (w^{1/2}·a)^2)^(1/2)
  -- We need to simplify (w^{1/2})^2 = w and (w^{1/2}·a)^2 = w·a²
  conv at hH => rhs; rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ from by norm_num]
  simp_rw [rpow_half_sq] at hH
  -- Now simplify (w^{1/2}·a)^2 = w·a^2
  have hv_sq : ∀ x, (w x ^ ((2 : ℝ)⁻¹) * a x) ^ (2 : ℝ) = w x * a x ^ (2 : ℝ) := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 2)]
    congr 1; exact rpow_half_sq (w x)
  simp_rw [hv_sq] at hH
  -- hH : ∫⁻ w·a ≤ (∫⁻ w)^(2⁻¹) · (∫⁻ w·a²)^(2⁻¹)
  -- Square both sides
  calc (∫⁻ x, w x * a x ∂μ) ^ (2 : ℕ)
      ≤ ((∫⁻ x, w x ∂μ) ^ ((2 : ℝ)⁻¹) *
         (∫⁻ x, w x * a x ^ (2 : ℝ) ∂μ) ^ ((2 : ℝ)⁻¹)) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (zero_le _) hH 2
    _ = (∫⁻ x, w x ∂μ) * ∫⁻ x, w x * a x ^ (2 : ℝ) ∂μ := by
        rw [mul_pow]
        congr 1 <;> {
          rw [sq, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity),
              show (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = (1 : ℝ) from by norm_num, ENNReal.rpow_one]
        }

/-- Core inequality: `eLpNorm (g⋆f) 2 μ ≤ eLpNorm g 1 μ * eLpNorm f 2 μ`.

The proof uses:
- Triangle inequality: `‖(g⋆f)(x)‖ₑ ≤ ∫⁻ ‖g(t)‖ₑ · ‖f(x-t)‖ₑ dt`
- Cauchy-Schwarz: `(∫⁻ w·a)² ≤ (∫⁻ w)·(∫⁻ w·a²)`
- Tonelli: swap the order of integration
- Translation invariance: `∫⁻ ‖f(x-t)‖ₑ² dx = ∫⁻ ‖f‖ₑ² dx` -/
private theorem young_eLpNorm_bound
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (g : G → ℝ) (f : G → ℝ)
    (hg : MemLp g 1 μ) (hf : MemLp f 2 μ) :
    eLpNorm (realConv μ g f) 2 μ ≤ eLpNorm g 1 μ * eLpNorm f 2 μ := by
  -- Work with strongly measurable representatives for measurability
  set g' := hg.aestronglyMeasurable.mk g
  set f' := hf.aestronglyMeasurable.mk f
  have hg'_meas : StronglyMeasurable g' := hg.aestronglyMeasurable.stronglyMeasurable_mk
  have hf'_meas : StronglyMeasurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hg'_ae : g =ᵐ[μ] g' := hg.aestronglyMeasurable.ae_eq_mk
  have hf'_ae : f =ᵐ[μ] f' := hf.aestronglyMeasurable.ae_eq_mk
  -- convolution_congr gives pointwise equality (not just ae) for Haar measures
  have hconv_eq : realConv μ g f = realConv μ g' f' :=
    convolution_congr (lsmul ℝ ℝ) hg'_ae hf'_ae
  rw [hconv_eq, eLpNorm_congr_ae hg'_ae, eLpNorm_congr_ae hf'_ae]
  -- Abbreviations for the key integrals
  set I₁ : ℝ≥0∞ := ∫⁻ t, ‖g' t‖ₑ ∂μ
  set I₂ : ℝ≥0∞ := ∫⁻ y, ‖f' y‖ₑ ^ (2 : ℝ) ∂μ
  -- Measurability of g', f'
  have hg'_m : Measurable g' := hg'_meas.measurable
  have hf'_m : Measurable f' := hf'_meas.measurable
  have henorm_g : Measurable (fun t => ‖g' t‖ₑ) := hg'_m.enorm
  have henorm_f : Measurable (fun y => ‖f' y‖ₑ) := hf'_m.enorm
  -- It suffices to prove the squared bound: ∫⁻ ‖g'⋆f'‖ₑ² ≤ I₁² · I₂
  suffices hsq : ∫⁻ x, ‖realConv μ g' f' x‖ₑ ^ (2 : ℝ) ∂μ ≤ I₁ ^ (2 : ℕ) * I₂ by
    -- Convert eLpNorm to lintegral and use rpow monotonicity
    rw [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0) ENNReal.coe_ne_top,
        eLpNorm_one_eq_lintegral_enorm,
        eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0) ENNReal.coe_ne_top]
    unfold eLpNorm'; simp only [ENNReal.toReal_ofNat, one_div]
    calc (∫⁻ x, ‖realConv μ g' f' x‖ₑ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹
        ≤ (I₁ ^ (2 : ℕ) * I₂) ^ (2 : ℝ)⁻¹ :=
          ENNReal.rpow_le_rpow hsq (by positivity)
      _ = I₁ * I₂ ^ (2 : ℝ)⁻¹ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
          congr 1
          -- (I₁ ^ 2) ^ 2⁻¹ = (I₁ * I₁) ^ 2⁻¹ = I₁^2⁻¹ * I₁^2⁻¹ = I₁^(2⁻¹+2⁻¹) = I₁^1 = I₁
          rw [sq, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
              ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity),
              show (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = (1 : ℝ) from by norm_num, ENNReal.rpow_one]
  -- ===== Main proof of the squared bound =====
  -- Step 1: Pointwise triangle inequality
  have h_triangle : ∀ x, ‖realConv μ g' f' x‖ₑ ≤
      ∫⁻ t, ‖g' t‖ₑ * ‖f' (x - t)‖ₑ ∂μ := by
    intro x
    calc ‖realConv μ g' f' x‖ₑ
        = ‖∫ t, (lsmul ℝ ℝ) (g' t) (f' (x - t)) ∂μ‖ₑ := rfl
      _ ≤ ∫⁻ t, ‖(lsmul ℝ ℝ) (g' t) (f' (x - t))‖ₑ ∂μ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ t, ‖g' t‖ₑ * ‖f' (x - t)‖ₑ ∂μ := by
          congr 1; ext t; simp [lsmul_apply, enorm_mul]
  -- Step 2: Pointwise Cauchy-Schwarz bound
  have h_cs : ∀ x, ‖realConv μ g' f' x‖ₑ ^ (2 : ℕ) ≤
      I₁ * ∫⁻ t, ‖g' t‖ₑ * ‖f' (x - t)‖ₑ ^ (2 : ℝ) ∂μ := by
    intro x
    calc ‖realConv μ g' f' x‖ₑ ^ (2 : ℕ)
        ≤ (∫⁻ t, ‖g' t‖ₑ * ‖f' (x - t)‖ₑ ∂μ) ^ (2 : ℕ) :=
          pow_le_pow_left₀ (zero_le _) (h_triangle x) 2
      _ ≤ (∫⁻ t, ‖g' t‖ₑ ∂μ) *
          ∫⁻ t, ‖g' t‖ₑ * ‖f' (x - t)‖ₑ ^ (2 : ℝ) ∂μ :=
          lintegral_mul_sq_le henorm_g.aemeasurable
            ((henorm_f.comp (measurable_const.sub measurable_id)).aemeasurable)
  -- Step 3: Integrate, convert rpow ↔ npow, pull out constant
  have h_pow_conv : ∀ (x : ℝ≥0∞), x ^ (2 : ℕ) = x ^ (2 : ℝ) := by
    intro x; rw [show (2 : ℝ) = ↑(2 : ℕ) from by norm_cast, ENNReal.rpow_natCast]
  calc ∫⁻ x, ‖realConv μ g' f' x‖ₑ ^ (2 : ℝ) ∂μ
      = ∫⁻ x, ‖realConv μ g' f' x‖ₑ ^ (2 : ℕ) ∂μ := by
        congr 1; ext x; exact (h_pow_conv _).symm
    _ ≤ ∫⁻ x, I₁ * ∫⁻ t, ‖g' t‖ₑ * ‖f' (x - t)‖ₑ ^ (2 : ℝ) ∂μ ∂μ :=
        lintegral_mono (h_cs ·)
    _ = I₁ * ∫⁻ x, ∫⁻ t, ‖g' t‖ₑ * ‖f' (x - t)‖ₑ ^ (2 : ℝ) ∂μ ∂μ := by
        have hmeas : Measurable (fun x => ∫⁻ t, ‖g' t‖ₑ * ‖f' (x - t)‖ₑ ^ (2 : ℝ) ∂μ) :=
          (henorm_g.comp measurable_snd).mul
            ((henorm_f.comp (measurable_fst.sub measurable_snd)).pow_const _)
            |>.lintegral_prod_right'
        rw [lintegral_const_mul _ hmeas]
    -- Step 4: Tonelli — swap order of integration
    _ = I₁ * ∫⁻ t, ∫⁻ x, ‖g' t‖ₑ * ‖f' (x - t)‖ₑ ^ (2 : ℝ) ∂μ ∂μ := by
        congr 1
        apply lintegral_lintegral_swap
        exact ((henorm_g.comp measurable_snd).mul
          ((henorm_f.comp (measurable_fst.sub measurable_snd)).pow_const _)).aemeasurable
    -- Step 5: Pull out ‖g'(t)‖ₑ from inner integral
    _ = I₁ * ∫⁻ t, ‖g' t‖ₑ * ∫⁻ x, ‖f' (x - t)‖ₑ ^ (2 : ℝ) ∂μ ∂μ := by
        congr 1; exact lintegral_congr fun t =>
          lintegral_const_mul _
            ((henorm_f.comp (measurable_sub_const t)).pow_const _)
    -- Step 6: Translation invariance: ∫ ‖f'(x-t)‖ₑ² dx = ∫ ‖f'(y)‖ₑ² dy
    _ = I₁ * ∫⁻ t, ‖g' t‖ₑ * I₂ ∂μ := by
        congr 1; exact lintegral_congr fun t => by
          congr 1; exact lintegral_sub_right_eq_self (fun y => ‖f' y‖ₑ ^ (2 : ℝ)) t
    -- Step 7: Pull out I₂ and rearrange
    _ = I₁ ^ (2 : ℕ) * I₂ := by
        simp_rw [mul_comm (‖g' _‖ₑ) I₂]
        rw [lintegral_const_mul _ henorm_g, sq]; ring

/-- AEStronglyMeasurable of convolution, from Fubini on the product. -/
private lemma aestronglyMeasurable_realConv
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (g : G → ℝ) (f : G → ℝ)
    (hg : MemLp g 1 μ) (hf : MemLp f 2 μ) :
    AEStronglyMeasurable (realConv μ g f) μ := by
  -- Replace by strongly measurable versions
  set g' := hg.aestronglyMeasurable.mk g
  set f' := hf.aestronglyMeasurable.mk f
  have hg'_meas : StronglyMeasurable g' := hg.aestronglyMeasurable.stronglyMeasurable_mk
  have hf'_meas : StronglyMeasurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hg'_ae : g =ᵐ[μ] g' := hg.aestronglyMeasurable.ae_eq_mk
  have hf'_ae : f =ᵐ[μ] f' := hf.aestronglyMeasurable.ae_eq_mk
  -- convolution_congr gives pointwise equality, so suffices for g', f'
  have hconv_eq : realConv μ g f = realConv μ g' f' :=
    convolution_congr (lsmul ℝ ℝ) hg'_ae hf'_ae
  rw [hconv_eq]
  -- The integrand (x, t) ↦ g'(t) * f'(x - t) is strongly measurable on the product
  have hF : StronglyMeasurable (fun p : G × G => g' p.2 * f' (p.1 - p.2)) :=
    (hg'_meas.comp_measurable measurable_snd).mul
      (hf'_meas.comp_measurable (measurable_fst.sub measurable_snd))
  -- By Fubini, x ↦ ∫ g'(t) f'(x-t) dt is AEStronglyMeasurable
  have := hF.aestronglyMeasurable.integral_prod_right' (μ := μ) (ν := μ)
  -- The integral form matches realConv
  convert this using 1

/-- Young's inequality: convolution of `g ∈ L¹` with `f ∈ L²` is in `L²`. -/
theorem young_convolution_memLp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (g : G → ℝ) (f : G → ℝ)
    (hg : MemLp g 1 μ) (hf : MemLp f 2 μ) :
    MemLp (realConv μ g f) 2 μ := by
  constructor
  · exact aestronglyMeasurable_realConv g f hg hf
  · calc eLpNorm (realConv μ g f) 2 μ
        ≤ eLpNorm g 1 μ * eLpNorm f 2 μ := young_eLpNorm_bound g f hg hf
      _ < ⊤ := ENNReal.mul_lt_top hg.eLpNorm_ne_top.lt_top hf.eLpNorm_ne_top.lt_top

/-- Young's inequality norm bound: `‖g ⋆ f‖₂ ≤ ‖g‖₁ · ‖f‖₂`.

Proof: By Cauchy-Schwarz, `|(g⋆f)(x)|² ≤ ‖g‖₁ · ∫ |g(t)| |f(x-t)|² dt`.
Integrating over x and using Fubini + translation invariance of Haar measure
gives `‖g⋆f‖₂² ≤ ‖g‖₁² · ‖f‖₂²`. Taking square roots yields the result. -/
theorem young_convolution_bound {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (g : G → ℝ) (f : G → ℝ)
    (hg : MemLp g 1 μ) (hf : MemLp f 2 μ) :
    eLpNorm (realConv μ g f) 2 μ ≤ eLpNorm g 1 μ * eLpNorm f 2 μ :=
  young_eLpNorm_bound g f hg hf

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
