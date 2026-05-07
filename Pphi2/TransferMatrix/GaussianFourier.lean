/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gaussian Convolution Strict Positive Definiteness via Fourier Theory

## Overview

Proves `⟨f, G⋆f⟩ > 0` for nonzero `f ∈ L²(ℝⁿ)` by:
1. Proving `Ĝ(k) > 0` for all k (Gaussian FT is positive)
2. Using the Fourier representation `⟨f, G⋆f⟩ = ∫ Ĝ(k) ‖f̂(k)‖² dk`
3. Deriving strict positivity from (1) + (2) + Plancherel injectivity

The main theorem `inner_convCLM_pos_of_fourier_pos` is fully proved modulo
`fourier_representation_convolution` (the Fourier representation identity,
which requires the L² convolution theorem not yet in Mathlib).

## References

- Folland, *Real Analysis*, §8.3; Reed-Simon I, §IX.4
-/

import Pphi2.TransferMatrix.L2Operator
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

noncomputable section

open MeasureTheory Complex FourierTransform SchwartzMap

namespace Pphi2

variable (Ns : ℕ) [NeZero Ns]

/-! ## Fourier strictness helper on complex L² -/

set_option maxHeartbeats 800000 in
-- This proof can exceed the default heartbeat budget because elaborating
-- `Lp.fourierTransformₗᵢ` and related coercions is expensive.
/-- If `f ∈ L²(ℝⁿ, ℂ)` is nonzero, then its Fourier transform is not a.e. zero.

This is the strictness step used in positivity arguments:
Plancherel gives `𝓕` as a linear isometric equivalence on `L²`,
so `𝓕 f = 0` implies `f = 0`. -/
private theorem fourier_ae_nonzero_of_nonzero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : Lp (α := E) ℂ 2) (hf : f ≠ 0) :
    ¬ (∀ᵐ x, ((Lp.fourierTransformₗᵢ E ℂ f : Lp (α := E) ℂ 2) x) = 0) := by
  intro h_ae
  have hFzero : (Lp.fourierTransformₗᵢ E ℂ f : Lp (α := E) ℂ 2) = 0 := by
    exact Lp.eq_zero_iff_ae_eq_zero.mpr h_ae
  have hfzero : f = 0 := by
    have hInv :
        (Lp.fourierTransformₗᵢ E ℂ).symm (Lp.fourierTransformₗᵢ E ℂ f) =
        (0 : Lp (α := E) ℂ 2) := by
      simp [hFzero]
    simpa using hInv
  exact hf hfzero

/-! ## Transport from real `L²(SpatialField)` to complex `L²(EuclideanSpace)` -/

/-- Pullback along `WithLp.ofLp : EuclideanSpace → SpatialField` as a real `L²` isometry. -/
private noncomputable def toEuclideanRealL2 :
    L2SpatialField Ns →ₗᵢ[ℝ] Lp (α := EuclideanSpace ℝ (Fin Ns)) ℝ 2 :=
  Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (p := (2 : ENNReal))
    (WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns)
    (PiLp.volume_preserving_ofLp (ι := Fin Ns))

/-- Pullback along `WithLp.toLp : SpatialField → EuclideanSpace` as a real `L²` isometry. -/
private noncomputable def fromEuclideanRealL2 :
    Lp (α := EuclideanSpace ℝ (Fin Ns)) ℝ 2 →ₗᵢ[ℝ] L2SpatialField Ns :=
  Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (p := (2 : ENNReal))
    (WithLp.toLp 2 : SpatialField Ns → EuclideanSpace ℝ (Fin Ns))
    (PiLp.volume_preserving_toLp (ι := Fin Ns))

omit [NeZero Ns] in
private theorem fromEuclideanRealL2_toEuclideanRealL2
    (f : L2SpatialField Ns) :
    fromEuclideanRealL2 Ns (toEuclideanRealL2 Ns f) = f := by
  change
    MeasureTheory.Lp.compMeasurePreserving
      (WithLp.toLp 2 : SpatialField Ns → EuclideanSpace ℝ (Fin Ns))
      (PiLp.volume_preserving_toLp (ι := Fin Ns))
      (MeasureTheory.Lp.compMeasurePreserving
        (WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns)
        (PiLp.volume_preserving_ofLp (ι := Fin Ns)) f) = f
  rw [← MeasureTheory.Lp.compMeasurePreserving_comp_apply
    (g := f)
    (f := (WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns))
    (hf := PiLp.volume_preserving_ofLp (ι := Fin Ns))
    (f' := (WithLp.toLp 2 : SpatialField Ns → EuclideanSpace ℝ (Fin Ns)))
    (hf' := PiLp.volume_preserving_toLp (ι := Fin Ns))]
  have hfun :
      (WithLp.ofLp ∘ WithLp.toLp 2 : SpatialField Ns → SpatialField Ns) = id := by
    funext x
    rfl
  simpa [hfun] using
    (MeasureTheory.Lp.compMeasurePreserving_id_apply
      (E := ℝ) (p := (2 : ENNReal)) f)

omit [NeZero Ns] in
private theorem toEuclideanRealL2_fromEuclideanRealL2
    (f : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℝ 2) :
    toEuclideanRealL2 Ns (fromEuclideanRealL2 Ns f) = f := by
  change
    MeasureTheory.Lp.compMeasurePreserving
      (WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns)
      (PiLp.volume_preserving_ofLp (ι := Fin Ns))
      (MeasureTheory.Lp.compMeasurePreserving
        (WithLp.toLp 2 : SpatialField Ns → EuclideanSpace ℝ (Fin Ns))
        (PiLp.volume_preserving_toLp (ι := Fin Ns)) f) = f
  rw [← MeasureTheory.Lp.compMeasurePreserving_comp_apply
    (g := f)
    (f := (WithLp.toLp 2 : SpatialField Ns → EuclideanSpace ℝ (Fin Ns)))
    (hf := PiLp.volume_preserving_toLp (ι := Fin Ns))
    (f' := (WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns))
    (hf' := PiLp.volume_preserving_ofLp (ι := Fin Ns))]
  have hfun :
      (WithLp.toLp 2 ∘ WithLp.ofLp :
        EuclideanSpace ℝ (Fin Ns) → EuclideanSpace ℝ (Fin Ns)) = id := by
    funext x
    rfl
  simpa [hfun] using
    (MeasureTheory.Lp.compMeasurePreserving_id_apply
      (E := ℝ) (p := (2 : ENNReal)) f)

/-- Real-to-complex embedding on `L²(SpatialField Ns)`. -/
private noncomputable def toComplexSpatialL2CLM :
    L2SpatialField Ns →L[ℝ] Lp (α := SpatialField Ns) ℂ 2 :=
  ContinuousLinearMap.compLpL (p := (2 : ENNReal))
    (μ := (volume : Measure (SpatialField Ns))) (@RCLike.ofRealCLM ℂ _)

/-- Pullback along `WithLp.ofLp : EuclideanSpace → SpatialField` as an `L²` isometry. -/
private noncomputable def pullToEuclideanL2 :
    Lp (α := SpatialField Ns) ℂ 2 →ₗᵢ[ℝ] Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 :=
  Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (p := (2 : ENNReal))
    (WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns)
    (PiLp.volume_preserving_ofLp (ι := Fin Ns))

/-- The complex Euclidean `L²` representative associated to `f : L2SpatialField Ns`. -/
private noncomputable def toEuclideanComplexL2 (f : L2SpatialField Ns) :
    Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 :=
  (pullToEuclideanL2 Ns) ((toComplexSpatialL2CLM Ns) f)

omit [NeZero Ns] in
/-- The real-to-complex `L²` embedding is injective. -/
private theorem toComplexSpatialL2CLM_ne_zero
    (f : L2SpatialField Ns) (hf : f ≠ 0) :
    (toComplexSpatialL2CLM Ns f) ≠ 0 := by
  intro h0
  have h_ae0 : ∀ᵐ x : SpatialField Ns ∂volume, (toComplexSpatialL2CLM Ns f) x = 0 := by
    exact Lp.eq_zero_iff_ae_eq_zero.mp h0
  have hco :
      (toComplexSpatialL2CLM Ns f) =ᵐ[volume] fun x => ((f x : ℝ) : ℂ) := by
    simpa [toComplexSpatialL2CLM] using
      (ContinuousLinearMap.coeFn_compLpL (p := (2 : ENNReal))
        (μ := (volume : Measure (SpatialField Ns))) (@RCLike.ofRealCLM ℂ _) f)
  have hf_ae0 : ∀ᵐ x : SpatialField Ns ∂volume, f x = 0 := by
    filter_upwards [h_ae0, hco] with x hx0 hxc
    have : ((f x : ℝ) : ℂ) = 0 := by simpa [hxc] using hx0
    exact_mod_cast this
  exact hf (Lp.eq_zero_iff_ae_eq_zero.mpr hf_ae0)

omit [NeZero Ns] in
/-- The transported Euclidean complex `L²` function is nonzero if `f` is nonzero. -/
private theorem toEuclideanComplexL2_ne_zero
    (f : L2SpatialField Ns) (hf : f ≠ 0) :
    toEuclideanComplexL2 Ns f ≠ 0 := by
  intro h0
  have hnorm :
      ‖toEuclideanComplexL2 Ns f‖ = ‖toComplexSpatialL2CLM Ns f‖ :=
    Lp.norm_compMeasurePreserving (p := (2 : ENNReal)) (toComplexSpatialL2CLM Ns f)
      (PiLp.volume_preserving_ofLp (ι := Fin Ns))
  have hnorm0 : ‖toEuclideanComplexL2 Ns f‖ = 0 := by simp [h0]
  have hnorm0' : ‖toComplexSpatialL2CLM Ns f‖ = 0 := by simpa [hnorm] using hnorm0
  exact (toComplexSpatialL2CLM_ne_zero (Ns := Ns) f hf) (norm_eq_zero.mp hnorm0')

omit [NeZero Ns] in
/-- Nonzero `f : L2SpatialField Ns` has Fourier transform not a.e. zero after transport
to complex `L²(EuclideanSpace)`. -/
private theorem fourier_ae_nonzero_of_spatial_nonzero
    (f : L2SpatialField Ns) (hf : f ≠ 0) :
    ¬ ∀ᵐ w : EuclideanSpace ℝ (Fin Ns) ∂volume,
      ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin Ns)) ℂ
        (toEuclideanComplexL2 Ns f) : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w) = 0 := by
  exact fourier_ae_nonzero_of_nonzero
    (toEuclideanComplexL2 Ns f) (toEuclideanComplexL2_ne_zero (Ns := Ns) f hf)

/-! ## Gaussian Fourier transform is strictly positive -/

/-- The Fourier transform of `exp(-b‖x‖²)` is a positive real for `b > 0`. -/
theorem fourier_gaussian_pos {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {b : ℝ} (hb : 0 < b) (w : V) :
    0 < ((𝓕 (fun (v : V) => cexp (-(b : ℂ) * (‖v‖ : ℂ) ^ 2)) : V → ℂ) w).re := by
  rw [fourier_gaussian_innerProductSpace (by rwa [ofReal_re] : 0 < (b : ℂ).re)]
  have hπb : (0 : ℝ) < Real.pi / b := div_pos Real.pi_pos hb
  have h1 : ((↑Real.pi / ↑b) ^ ((↑(Module.finrank ℝ V) : ℂ) / 2) : ℂ) =
      ↑((Real.pi / b) ^ ((Module.finrank ℝ V : ℝ) / 2)) := by
    rw [ofReal_cpow hπb.le]; simp [ofReal_div]
  have h2 : cexp ((-↑Real.pi ^ 2 * ↑‖w‖ ^ 2 / ↑b : ℂ)) =
      ↑(Real.exp (-Real.pi ^ 2 * ‖w‖ ^ 2 / b)) := by
    have : (-↑Real.pi ^ 2 * ↑‖w‖ ^ 2 / ↑b : ℂ) =
        ↑(-Real.pi ^ 2 * ‖w‖ ^ 2 / b) := by push_cast; ring
    rw [this, ← ofReal_exp]
  rw [h1, h2, ← ofReal_mul, ofReal_re]
  exact mul_pos (Real.rpow_pos_of_pos hπb _) (Real.exp_pos _)

/-! ## Strict positive definiteness from Fourier positivity

This follows from the Fourier representation:
  `⟨f, g⋆f⟩ = ∫ Re(ĝ_ℂ(k)) · ‖f̂_ℂ(k)‖² dk`

The proof uses: R-to-C embedding, convolution theorem on Schwartz,
Parseval identity, density of Schwartz in L2, and Plancherel injectivity.

References: Folland, *Real Analysis*, 8.3; Reed-Simon I, IX.4. -/

-- Abbreviation for readability
private abbrev gHat (g : SpatialField Ns → ℝ) : EuclideanSpace ℝ (Fin Ns) → ℂ :=
  𝓕 (fun (v : EuclideanSpace ℝ (Fin Ns)) => (g ((WithLp.equiv 2 _) v) : ℂ))

private abbrev fHat (f : L2SpatialField Ns) :
    Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 :=
  Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin Ns)) ℂ (toEuclideanComplexL2 Ns f)

-- The convolution quadratic form is continuous
omit [NeZero Ns] in
private theorem convQuadForm_continuous
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) :
    Continuous (fun f : L2SpatialField Ns => @inner ℝ _ _ f (convCLM g hg f)) :=
  Continuous.inner continuous_id (convCLM g hg).continuous

-- The Fourier quadratic form is continuous.
-- Key bound: |∫ Re(ĝ) · ‖ĥ‖²| ≤ ‖g‖₁ · ‖h‖₂², so the quadratic form
-- is dominated by ‖g‖₁ · ‖f‖₂², giving continuity.
-- The map f ↦ fHat(f) is continuous (composition of CLM, isometry, isometry)
set_option maxHeartbeats 800000 in
-- Gaussian Fourier integral convergence
omit [NeZero Ns] in
private theorem fHat_continuous :
    Continuous (fun f : L2SpatialField Ns => fHat Ns f) :=
  (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin Ns)) ℂ).continuous.comp
    ((pullToEuclideanL2 Ns).continuous.comp (toComplexSpatialL2CLM Ns).continuous)

set_option maxHeartbeats 800000 in
-- Gaussian Fourier integral convergence
omit [NeZero Ns] in
/-- The Fourier transform of `g_ℂ` (the complex-valued lift of `g`) is continuous.
Needed for measurability of the Fourier representation integrand. -/
private theorem ghat_continuous
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) :
    Continuous (𝓕 (fun (v : EuclideanSpace ℝ (Fin Ns)) =>
      (g ((WithLp.equiv 2 _) v) : ℂ))) := by
  set g_ℂ : EuclideanSpace ℝ (Fin Ns) → ℂ := fun v => (g ((WithLp.equiv 2 _) v) : ℂ)
  have hg_int : Integrable g (volume : Measure (SpatialField Ns)) :=
    memLp_one_iff_integrable.mp hg
  have hmp : MeasurePreserving (WithLp.equiv 2 (SpatialField Ns))
      (volume : Measure (EuclideanSpace ℝ (Fin Ns)))
      (volume : Measure (SpatialField Ns)) :=
    PiLp.volume_preserving_ofLp (ι := Fin Ns)
  have h1 : Integrable (g ∘ (WithLp.equiv 2 _))
      (volume : Measure (EuclideanSpace ℝ (Fin Ns))) :=
    hmp.integrable_comp_of_integrable hg_int
  have h_g_int : Integrable g_ℂ volume := h1.ofReal
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    continuous_inner h_g_int

private abbrev gHatReC
    (g : SpatialField Ns → ℝ) :
    EuclideanSpace ℝ (Fin Ns) → ℂ :=
  fun w => ((gHat Ns g w).re : ℂ)

omit [NeZero Ns] in
private theorem gHatRe_bound
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) :
    ∀ w, ‖gHatReC Ns g w‖ ≤
      max 1 (∫ v : EuclideanSpace ℝ (Fin Ns),
        ‖(g ((WithLp.equiv 2 _) v) : ℂ)‖) := by
  intro w
  have hnorm :
      ‖gHat Ns g w‖ ≤
        ∫ v : EuclideanSpace ℝ (Fin Ns), ‖(g ((WithLp.equiv 2 _) v) : ℂ)‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ w
  calc
    ‖gHatReC Ns g w‖ = |(gHat Ns g w).re| := by
      simp [gHatReC, Real.norm_eq_abs]
    _ ≤ ‖gHat Ns g w‖ := abs_re_le_norm _
    _ ≤ max 1 (∫ v : EuclideanSpace ℝ (Fin Ns), ‖(g ((WithLp.equiv 2 _) v) : ℂ)‖) :=
      hnorm.trans (le_max_right _ _)

omit [NeZero Ns] in
private theorem gHatRe_memLp_top
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) :
    MemLp (gHatReC Ns g) ⊤
      (volume : Measure (EuclideanSpace ℝ (Fin Ns))) := by
  have hcont : Continuous (gHatReC Ns g) :=
    continuous_ofReal.comp (continuous_re.comp (ghat_continuous (Ns := Ns) g hg))
  refine memLp_top_of_bound
    hcont.aestronglyMeasurable
    (max 1 (∫ v : EuclideanSpace ℝ (Fin Ns), ‖(g ((WithLp.equiv 2 _) v) : ℂ)‖))
    (ae_of_all _ (gHatRe_bound (Ns := Ns) g hg))

private noncomputable def gHatReLp
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) :
    Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ ⊤ :=
  (gHatRe_memLp_top (Ns := Ns) g hg).toLp (gHatReC Ns g)

set_option maxHeartbeats 800000 in
-- Elaborating `holderL` and the induced `Lp`-multiplier can exceed the default budget.
private noncomputable def fourierWeightCLM
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) :
    Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 →L[ℂ]
      Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 := by
  let p : ENNReal := ⊤
  let q : ENNReal := 2
  let r : ENNReal := 2
  let T :
      Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ ⊤ →L[ℂ]
        (Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 →L[ℂ]
          Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) :=
    ContinuousLinearMap.holderL
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin Ns))))
      (p := p) (q := q) (r := r)
      (B := ContinuousLinearMap.lsmul ℂ ℂ)
  exact T (gHatReLp Ns g hg)

set_option maxHeartbeats 800000 in
omit [NeZero Ns] in
private theorem fourierWeightCLM_spec
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) :
    fourierWeightCLM Ns g hg h =ᵐ[volume]
      fun w => (gHatReC Ns g w) • h w := by
  have hholder :
      fourierWeightCLM Ns g hg h =ᵐ[volume]
        fun w =>
          (((gHatRe_memLp_top (Ns := Ns) g hg).toLp (gHatReC Ns g) :
            Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ ⊤) w) • h w := by
    simpa [fourierWeightCLM, gHatReLp] using
      (ContinuousLinearMap.coeFn_holder
        (B := ContinuousLinearMap.lsmul ℂ ℂ)
        (r := (2 : ENNReal))
        (gHatReLp Ns g hg) h)
  have hcoeff :
      (((gHatRe_memLp_top (Ns := Ns) g hg).toLp (gHatReC Ns g) :
        Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ ⊤)) =ᵐ[volume] gHatReC Ns g :=
    MemLp.coeFn_toLp (gHatRe_memLp_top (Ns := Ns) g hg)
  filter_upwards [hholder, hcoeff] with w hw hw'
  simpa [hw'] using hw

omit [NeZero Ns] in
private theorem fourierQuadForm_continuous
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) :
    Continuous (fun h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 =>
      (@inner ℂ _ _ h (fourierWeightCLM Ns g hg h)).re) :=
  continuous_re.comp <|
    Continuous.inner continuous_id ((fourierWeightCLM Ns g hg).continuous.comp continuous_id)

set_option maxHeartbeats 800000 in
omit [NeZero Ns] in
private theorem fourierQuadForm_eq_integral
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) :
    (@inner ℂ _ _ h (fourierWeightCLM Ns g hg h)).re =
      ∫ w : EuclideanSpace ℝ (Fin Ns),
        (gHat Ns g w).re * ‖(h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w‖ ^ 2 := by
  rw [MeasureTheory.L2.inner_def]
  change RCLike.re (∫ a : EuclideanSpace ℝ (Fin Ns),
    inner ℂ (h a) ((fourierWeightCLM Ns g hg h) a) ∂volume) =
      ∫ w : EuclideanSpace ℝ (Fin Ns),
        (gHat Ns g w).re * ‖(h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w‖ ^ 2
  have hre :
      ∫ a : EuclideanSpace ℝ (Fin Ns),
        RCLike.re (inner ℂ (h a) ((fourierWeightCLM Ns g hg h) a)) ∂volume =
      RCLike.re (∫ a : EuclideanSpace ℝ (Fin Ns),
        inner ℂ (h a) ((fourierWeightCLM Ns g hg h) a) ∂volume) :=
    integral_re (MeasureTheory.L2.integrable_inner h (fourierWeightCLM Ns g hg h))
  rw [← hre]
  apply integral_congr_ae
  filter_upwards [fourierWeightCLM_spec (Ns := Ns) g hg h] with w hw
  rw [hw]
  have hnorm :
      ‖(h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w‖ ^ 2 =
        ((h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w).re ^ 2 +
        ((h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w).im ^ 2 := by
    simpa [Complex.sq_norm, Complex.normSq_apply, sq, add_comm, add_left_comm, add_assoc] using
      (Complex.sq_norm ((h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w))
  rw [hnorm]
  simp [gHatReC]
  ring

omit [NeZero Ns] in
private theorem fourierIntegralQuadForm_continuous
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) :
    Continuous (fun f : L2SpatialField Ns =>
      ∫ w : EuclideanSpace ℝ (Fin Ns),
        (gHat Ns g w).re *
        ‖(fHat Ns f : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w‖ ^ 2) := by
  have hEq :
      (fun f : L2SpatialField Ns =>
        (@inner ℂ _ _ (fHat Ns f) (fourierWeightCLM Ns g hg (fHat Ns f))).re) =
      (fun f : L2SpatialField Ns =>
        ∫ w : EuclideanSpace ℝ (Fin Ns),
          (gHat Ns g w).re *
          ‖(fHat Ns f : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w‖ ^ 2) := by
    funext f
    exact fourierQuadForm_eq_integral (Ns := Ns) g hg (fHat Ns f)
  exact hEq ▸ ((fourierQuadForm_continuous (Ns := Ns) g hg).comp (fHat_continuous (Ns := Ns)))

/-- **L¹∩L² Plancherel agreement** (textbook).

For `h : ℝⁿ → ℂ` that is both in `L¹(volume)` and in `L²(volume)`, the L²
Fourier transform of the `Lp ℂ 2` representative of `h` agrees a.e. with the
classical Fourier integral `𝓕 h` (defined for L¹ inputs by
`MeasureTheory.fourierIntegral`).

This is the standard density-and-isometry extension that defines
`Lp.fourierTransformₗᵢ` in the first place: the L² transform is constructed
as the unique continuous extension of the classical Fourier integral from
the Schwartz subspace, and the resulting extension automatically agrees with
the L¹ classical Fourier integral on the overlap `L¹ ∩ L²`.

Mathlib has the **Schwartz** form of this identification as
`SchwartzMap.toLp_fourier_eq`, but no direct `L¹ ∩ L²` form. The general
form is needed in this file because `g ⋆ s` (for `g ∈ L¹` and `s` Schwartz)
is in `L¹ ∩ L²` but not Schwartz.

**Reference**: Folland, *Real Analysis*, §8.3, Theorem 8.22 (Plancherel);
Reed-Simon I §IX.4, Theorem IX.13.

**Proof strategy** (Gemini deep-think 2026-04-30, one-line sketch): take a
Schwartz sequence `(sₙ)` with `sₙ → h` in both `L¹` and `L²`; the
`L²`-continuity of `Lp.fourierTransformₗᵢ` makes `𝓕 sₙ` converge in `L²` to
the L²-side LHS, while the `L¹ → L^∞` continuity of the classical Fourier
integral makes `𝓕 sₙ` converge uniformly (hence a.e.) to the RHS — both
limits must therefore agree a.e.

**Audit (Gemini deep-think 2026-04-30)**: PASS on (a) type correctness,
(b) strength vs Folland 8.22 / Reed-Simon IX.13, (c) non-vacuity (LHS is the
abstract Plancherel limit, RHS the concrete L¹ integral — the equality is
the substantive content of the theorem), (d) hypothesis sufficiency
(`MemLp h 1` + `MemLp h 2` is exactly what the references use; works for
`Ns = 0` as a trivial case via Dirac measure on a one-point space), (e)
`=ᵐ[volume]` is the natural formulation. -/
private axiom fourierTransform_lp_eq_fourierIntegral
    {h : EuclideanSpace ℝ (Fin Ns) → ℂ}
    (hL1 : MemLp h 1 (volume : Measure (EuclideanSpace ℝ (Fin Ns))))
    (hL2 : MemLp h 2 (volume : Measure (EuclideanSpace ℝ (Fin Ns)))) :
    Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin Ns)) ℂ (hL2.toLp h)
      =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin Ns)))] 𝓕 h

private abbrev gEuclidean
    (g : SpatialField Ns → ℝ) :
    EuclideanSpace ℝ (Fin Ns) → ℝ :=
  fun v => g ((WithLp.equiv 2 _) v)

omit [NeZero Ns] in
private theorem gEuclidean_memLp
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) :
    MemLp (gEuclidean Ns g) 1
      (volume : Measure (EuclideanSpace ℝ (Fin Ns))) := by
  simpa [gEuclidean] using
    hg.comp_measurePreserving (PiLp.volume_preserving_ofLp (ι := Fin Ns))

/-- The real-to-complex lift on Euclidean `L²`. -/
private noncomputable def liftL2_ℝC :
    Lp (α := EuclideanSpace ℝ (Fin Ns)) ℝ 2 →L[ℝ]
      Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 :=
  ContinuousLinearMap.compLpL (p := (2 : ENNReal))
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin Ns))))
    Complex.ofRealCLM

omit [NeZero Ns] in
private theorem liftL2_ℝC_spec
    (f : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℝ 2) :
    liftL2_ℝC Ns f =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin Ns)))]
      fun w => ((f w : ℝ) : ℂ) := by
  simpa [liftL2_ℝC] using
    (ContinuousLinearMap.coeFn_compLpL
      (p := (2 : ENNReal))
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin Ns))))
      Complex.ofRealCLM f)

omit [NeZero Ns] in
/-- The transported complex Euclidean representative is exactly the lifted
transported real representative. -/
private theorem toEuclideanComplexL2_eq_lift
    (f : L2SpatialField Ns) :
    toEuclideanComplexL2 Ns f = liftL2_ℝC Ns (toEuclideanRealL2 Ns f) := by
  apply Subtype.coe_injective
  apply MeasureTheory.AEEqFun.ext
  have h_complex :
      (toEuclideanComplexL2 Ns f : EuclideanSpace ℝ (Fin Ns) → ℂ) =ᵐ[volume]
      fun w => ((f ((WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns) w) : ℝ) : ℂ) := by
    have h_pull :
        (toEuclideanComplexL2 Ns f : EuclideanSpace ℝ (Fin Ns) → ℂ) =ᵐ[volume]
        fun w =>
          (toComplexSpatialL2CLM Ns f : SpatialField Ns → ℂ)
            ((WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns) w) := by
      simpa [toEuclideanComplexL2, pullToEuclideanL2] using
        (MeasureTheory.Lp.coeFn_compMeasurePreserving
          (g := (toComplexSpatialL2CLM Ns f))
          (hf := PiLp.volume_preserving_ofLp (ι := Fin Ns)))
    have h_spatial :
        (toComplexSpatialL2CLM Ns f : SpatialField Ns → ℂ) =ᵐ[volume]
        fun x => ((f x : ℝ) : ℂ) := by
      simpa [toComplexSpatialL2CLM] using
        (ContinuousLinearMap.coeFn_compLpL
          (p := (2 : ENNReal))
          (μ := (volume : Measure (SpatialField Ns)))
          (@RCLike.ofRealCLM ℂ _) f)
    exact h_pull.trans <|
      (PiLp.volume_preserving_ofLp (ι := Fin Ns)).quasiMeasurePreserving.ae_eq_comp h_spatial
  have h_real :
      (toEuclideanRealL2 Ns f : EuclideanSpace ℝ (Fin Ns) → ℝ) =ᵐ[volume]
      fun w => f ((WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns) w) := by
    simpa [toEuclideanRealL2] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving
        (g := f)
        (hf := PiLp.volume_preserving_ofLp (ι := Fin Ns)))
  have h_lift := liftL2_ℝC_spec (Ns := Ns) (toEuclideanRealL2 Ns f)
  filter_upwards [h_complex, h_real, h_lift] with w hwc hwr hwl
  simp [hwl, hwr, hwc]

/-- The Euclidean `L²` Fourier transform viewed as a real continuous linear map. -/
private noncomputable def fourierRealCLM :
    Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 →L[ℝ]
      Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 :=
  LinearMap.mkContinuous
    { toFun := fun f => Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin Ns)) ℂ f
      map_add' := by intro f h; simp
      map_smul' := by
        intro c f
        simpa using
          (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin Ns)) ℂ).map_smul (c : ℂ) f }
    1
    (by
      intro f
      simp [MeasureTheory.Lp.norm_fourier_eq (E := EuclideanSpace ℝ (Fin Ns)) (F := ℂ) f])

omit [NeZero Ns] in
private theorem gHat_memLp_top
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) :
    MemLp (gHat Ns g) ⊤
      (volume : Measure (EuclideanSpace ℝ (Fin Ns))) := by
  have hcont : Continuous (gHat Ns g) := ghat_continuous (Ns := Ns) g hg
  refine memLp_top_of_bound
    hcont.aestronglyMeasurable
    (max 1 (∫ v : EuclideanSpace ℝ (Fin Ns), ‖(g ((WithLp.equiv 2 _) v) : ℂ)‖))
    (ae_of_all _ fun w => ?_)
  exact
    (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ w).trans (le_max_right _ _)

private noncomputable def gHatLp
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) :
    Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ ⊤ :=
  (gHat_memLp_top (Ns := Ns) g hg).toLp (gHat Ns g)

set_option maxHeartbeats 800000 in
-- Elaborating the complex-valued L∞ multiplier follows the same heavy Holder path
-- as `fourierWeightCLM`.
private noncomputable def fourierWeightComplexCLM
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) :
    Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 →L[ℂ]
      Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 := by
  let p : ENNReal := ⊤
  let q : ENNReal := 2
  let r : ENNReal := 2
  let T :
      Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ ⊤ →L[ℂ]
        (Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 →L[ℂ]
          Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) :=
    ContinuousLinearMap.holderL
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin Ns))))
      (p := p) (q := q) (r := r)
      (B := ContinuousLinearMap.lsmul ℂ ℂ)
  exact T (gHatLp Ns g hg)

omit [NeZero Ns] in
private theorem fourierWeightComplexCLM_spec
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) :
    fourierWeightComplexCLM Ns g hg h =ᵐ[volume]
      fun w => (gHat Ns g w) * h w := by
  have hholder :
      fourierWeightComplexCLM Ns g hg h =ᵐ[volume]
        fun w =>
          (((gHat_memLp_top (Ns := Ns) g hg).toLp (gHat Ns g) :
            Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ ⊤) w) • h w := by
    simpa [fourierWeightComplexCLM, gHatLp] using
      (ContinuousLinearMap.coeFn_holder
        (B := ContinuousLinearMap.lsmul ℂ ℂ)
        (r := (2 : ENNReal))
        (gHatLp Ns g hg) h)
  have hcoeff :
      (((gHat_memLp_top (Ns := Ns) g hg).toLp (gHat Ns g) :
        Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ ⊤)) =ᵐ[volume] gHat Ns g :=
    MemLp.coeFn_toLp (gHat_memLp_top (Ns := Ns) g hg)
  filter_upwards [hholder, hcoeff] with w hw hw'
  simpa [hw', smul_eq_mul] using hw

omit [NeZero Ns] in
/-- Real `L²` inner products are the real parts of the corresponding complex
inner products after `liftL2_ℝC`. -/
private theorem inner_eq_re_inner_liftL2
    (f h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℝ 2) :
    @inner ℝ _ _ f h = (@inner ℂ _ _ (liftL2_ℝC Ns f) (liftL2_ℝC Ns h)).re := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc
    ∫ a : EuclideanSpace ℝ (Fin Ns), inner ℝ (f a) (h a) ∂volume
      = ∫ a : EuclideanSpace ℝ (Fin Ns),
          RCLike.re (inner ℂ ((liftL2_ℝC Ns f) a) ((liftL2_ℝC Ns h) a)) ∂volume := by
            apply integral_congr_ae
            have hf := liftL2_ℝC_spec (Ns := Ns) f
            have hh := liftL2_ℝC_spec (Ns := Ns) h
            filter_upwards [hf, hh] with a hfa hha
            rw [hfa, hha]
            calc
              inner ℝ (f a) (h a) = (h a) * (f a) := by
                have h_inner : inner ℝ (f a) (h a) = (h a : ℝ) * star (f a) :=
                  RCLike.inner_apply (f a) (h a)
                simpa using h_inner
              _ = RCLike.re (inner ℂ ((f a : ℂ)) ((h a : ℂ))) := by
                simp [RCLike.inner_apply, Complex.conj_ofReal, mul_comm]
    _ = (@inner ℂ _ _ (liftL2_ℝC Ns f) (liftL2_ℝC Ns h)).re := by
          rw [MeasureTheory.L2.inner_def]
          exact integral_re
            (MeasureTheory.L2.integrable_inner (liftL2_ℝC Ns f) (liftL2_ℝC Ns h))

/-- Complex Fourier weight multiplication, regarded as a real continuous linear map. -/
private noncomputable def fourierWeightComplexRealCLM
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) :
    Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 →L[ℝ]
      Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 :=
  LinearMap.mkContinuous
    { toFun := fun h => fourierWeightComplexCLM Ns g hg h
      map_add' := by intro h₁ h₂; simp
      map_smul' := by
        intro c h
        simpa using (fourierWeightComplexCLM Ns g hg).map_smul (c : ℂ) h }
    ‖fourierWeightComplexCLM Ns g hg‖
    (fun h => (fourierWeightComplexCLM Ns g hg).le_opNorm h)

/-- Fourier-side convolution operator on Euclidean real `L²`. -/
private noncomputable def T_conv
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) :
    Lp (α := EuclideanSpace ℝ (Fin Ns)) ℝ 2 →L[ℝ]
      Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 :=
  (fourierRealCLM Ns).comp <|
    (liftL2_ℝC Ns).comp <|
      convCLM (gEuclidean Ns g) (gEuclidean_memLp (Ns := Ns) g hg)

/-- Fourier-side multiplication operator on Euclidean real `L²`. -/
private noncomputable def T_mul
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) :
    Lp (α := EuclideanSpace ℝ (Fin Ns)) ℝ 2 →L[ℝ]
      Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 :=
  (fourierWeightComplexRealCLM Ns g hg).comp <|
    (fourierRealCLM Ns).comp <|
      liftL2_ℝC Ns

omit [NeZero Ns] in
private theorem T_conv_apply_schwartz
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (s : 𝓢(EuclideanSpace ℝ (Fin Ns), ℝ)) :
    T_conv Ns g hg (s.toLp 2) =
      Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin Ns)) ℂ
        (liftL2_ℝC Ns
          (convCLM (gEuclidean Ns g) (gEuclidean_memLp (Ns := Ns) g hg) (s.toLp 2))) := by
  rfl

omit [NeZero Ns] in
private theorem T_mul_apply_schwartz
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (s : 𝓢(EuclideanSpace ℝ (Fin Ns), ℝ)) :
    T_mul Ns g hg (s.toLp 2) =
      fourierWeightComplexCLM Ns g hg
        (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin Ns)) ℂ
          (liftL2_ℝC Ns (s.toLp 2))) := by
  rfl

/-! ### Step 6 helpers: Schwartz base-case packaging

The next-and-final analytic step in the
`fourier_representation_convolution` proof is the equality
`T_conv s = T_mul s` for Schwartz `s` (the "Schwartz base case" of the
CLM-firewall density argument). The helpers below are the Schwartz-side
packaging that the codex attempts kept stalling on. -/

/-- The complex Schwartz lift of a real Schwartz function: post-compose with
the real-to-complex CLM. -/
private noncomputable def schwartzComplexLift
    (s : 𝓢(EuclideanSpace ℝ (Fin Ns), ℝ)) :
    𝓢(EuclideanSpace ℝ (Fin Ns), ℂ) :=
  s.postcompCLM (Complex.ofRealCLM)

omit [NeZero Ns] in
/-- Pointwise: the complex Schwartz lift evaluates to `(s w : ℂ)`. -/
private theorem schwartzComplexLift_apply
    (s : 𝓢(EuclideanSpace ℝ (Fin Ns), ℝ))
    (w : EuclideanSpace ℝ (Fin Ns)) :
    (schwartzComplexLift Ns s : EuclideanSpace ℝ (Fin Ns) → ℂ) w = (s w : ℂ) := rfl

omit [NeZero Ns] in
/-- The Schwartz-side `liftL2_ℝC` identification. As elements of `Lp ℂ 2`:

    `liftL2_ℝC (s.toLp 2) = (schwartzComplexLift s).toLp 2`.

This is one of the two Schwartz-base-case Lp identifications that the
previous codex attempts could not push through smoothly. With this lemma in
hand, the convolution-side analogue plus
`SchwartzMap.toLp_fourier_eq` and the textbook bridge axiom
`fourierTransform_lp_eq_fourierIntegral` close the Schwartz base case. -/
private theorem liftL2_ℝC_schwartz_eq
    (s : 𝓢(EuclideanSpace ℝ (Fin Ns), ℝ)) :
    liftL2_ℝC Ns (s.toLp 2) = (schwartzComplexLift Ns s).toLp 2 := by
  apply Subtype.coe_injective
  apply MeasureTheory.AEEqFun.ext
  have h_lift := liftL2_ℝC_spec (Ns := Ns) (s.toLp 2)
  have h_s : (s.toLp 2 : EuclideanSpace ℝ (Fin Ns) → ℝ) =ᵐ[volume] s :=
    SchwartzMap.coeFn_toLp s 2 _
  have h_sC :
      ((schwartzComplexLift Ns s).toLp 2 : EuclideanSpace ℝ (Fin Ns) → ℂ)
        =ᵐ[volume] schwartzComplexLift Ns s :=
    SchwartzMap.coeFn_toLp (schwartzComplexLift Ns s) 2 _
  filter_upwards [h_lift, h_s, h_sC] with w hw hsw hsCw
  change (liftL2_ℝC Ns (s.toLp 2) : EuclideanSpace ℝ (Fin Ns) → ℂ) w =
       ((schwartzComplexLift Ns s).toLp 2 : EuclideanSpace ℝ (Fin Ns) → ℂ) w
  rw [hw, hsCw, schwartzComplexLift_apply, hsw]

/-- Convolution-side coercion: the Lp ℂ 2 element
`liftL2_ℝC (convCLM g_E hg_E (s.toLp 2))` agrees a.e. with the explicit
function `w ↦ ((realConv volume g_E s w : ℝ) : ℂ)`. This is the convolution
analogue of `liftL2_ℝC_schwartz_eq` (but only as an a.e. coercion identity,
since the RHS isn't constructed via `MemLp.toLp` here). -/
private theorem liftL2_ℝC_convCLM_schwartz_coeFn
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (s : 𝓢(EuclideanSpace ℝ (Fin Ns), ℝ)) :
    (liftL2_ℝC Ns
        (convCLM (gEuclidean Ns g) (gEuclidean_memLp (Ns := Ns) g hg) (s.toLp 2))
      : EuclideanSpace ℝ (Fin Ns) → ℂ) =ᵐ[volume]
      fun w => ((realConv volume (gEuclidean Ns g) s w : ℝ) : ℂ) := by
  have h_lift := liftL2_ℝC_spec (Ns := Ns)
    (convCLM (gEuclidean Ns g) (gEuclidean_memLp (Ns := Ns) g hg) (s.toLp 2))
  have h_conv := convCLM_spec (gEuclidean Ns g)
    (gEuclidean_memLp (Ns := Ns) g hg) (s.toLp 2)
  have h_s : (s.toLp 2 : EuclideanSpace ℝ (Fin Ns) → ℝ) =ᵐ[volume] s :=
    SchwartzMap.coeFn_toLp s 2 _
  -- swap `s.toLp 2` for `s` inside `realConv` via `convolution_congr`
  have h_realConv_eq :
      realConv volume (gEuclidean Ns g) (s.toLp 2 : EuclideanSpace ℝ (Fin Ns) → ℝ) =
      realConv volume (gEuclidean Ns g) s := by
    unfold realConv
    exact MeasureTheory.convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
      Filter.EventuallyEq.rfl h_s
  filter_upwards [h_lift, h_conv] with w hw hcw
  rw [hw, hcw]
  exact congrArg (Complex.ofReal) (congrFun h_realConv_eq w)

/-- The complex-lifted real convolution `w ↦ ((realConv volume g_E s w : ℝ) : ℂ)`
is in `L²` (deduced from the L² membership of the underlying real Lp element
`liftL2_ℝC (convCLM g_E hg_E (s.toLp 2))` plus the a.e. identity above). -/
private theorem realConvComplexLift_memLp_two
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (s : 𝓢(EuclideanSpace ℝ (Fin Ns), ℝ)) :
    MemLp (fun w => ((realConv volume (gEuclidean Ns g) s w : ℝ) : ℂ))
      2 (volume : Measure (EuclideanSpace ℝ (Fin Ns))) := by
  -- Use the `liftL2_ℝC ∘ convCLM` Lp element's L² membership, then transport
  -- via the a.e. coercion identity proved above.
  set f := liftL2_ℝC Ns
    (convCLM (gEuclidean Ns g) (gEuclidean_memLp (Ns := Ns) g hg) (s.toLp 2))
  have hf_memLp : MemLp (f : EuclideanSpace ℝ (Fin Ns) → ℂ) 2 volume := Lp.memLp f
  have h_ae := liftL2_ℝC_convCLM_schwartz_coeFn (Ns := Ns) g hg s
  exact MemLp.ae_eq h_ae hf_memLp

/-- The Lp ℂ 2 element on the convolution side equals the explicit `MemLp.toLp`. -/
private theorem liftL2_ℝC_convCLM_schwartz_eq_toLp
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (s : 𝓢(EuclideanSpace ℝ (Fin Ns), ℝ)) :
    liftL2_ℝC Ns
        (convCLM (gEuclidean Ns g) (gEuclidean_memLp (Ns := Ns) g hg) (s.toLp 2))
      = (realConvComplexLift_memLp_two (Ns := Ns) g hg s).toLp
        (fun w => ((realConv volume (gEuclidean Ns g) s w : ℝ) : ℂ)) := by
  apply Subtype.coe_injective
  apply MeasureTheory.AEEqFun.ext
  have h_lhs := liftL2_ℝC_convCLM_schwartz_coeFn (Ns := Ns) g hg s
  have h_rhs :
      ((realConvComplexLift_memLp_two (Ns := Ns) g hg s).toLp
          (fun w => ((realConv volume (gEuclidean Ns g) s w : ℝ) : ℂ))
        : EuclideanSpace ℝ (Fin Ns) → ℂ)
      =ᵐ[volume] fun w => ((realConv volume (gEuclidean Ns g) s w : ℝ) : ℂ) :=
    MemLp.coeFn_toLp _
  filter_upwards [h_lhs, h_rhs] with w hl hr
  exact hl.trans hr.symm

/-- The complex lift of the Euclidean function `g_E`, used as the `f₁` argument
in `Real.fourier_smul_convolution_eq`. -/
private noncomputable def gEuclideanComplex (g : SpatialField Ns → ℝ) :
    EuclideanSpace ℝ (Fin Ns) → ℂ :=
  fun w => ((gEuclidean Ns g w : ℝ) : ℂ)

omit [NeZero Ns] in
/-- The complex-lifted Euclidean `g` is integrable. -/
private theorem gEuclideanComplex_integrable
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) :
    Integrable (gEuclideanComplex Ns g) volume := by
  unfold gEuclideanComplex
  -- gEuclidean Ns g is integrable (transported via measure-preserving map)
  have hg_E_int : Integrable (gEuclidean Ns g) volume := by
    have := (gEuclidean_memLp (Ns := Ns) g hg)
    exact memLp_one_iff_integrable.mp this
  -- complex lift preserves integrability
  exact hg_E_int.ofReal

omit [NeZero Ns] in
/-- The complex-lifted Euclidean `g` is continuous, given `g` continuous. -/
private theorem gEuclideanComplex_continuous
    (g : SpatialField Ns → ℝ) (hg_cont : Continuous g) :
    Continuous (gEuclideanComplex Ns g) := by
  unfold gEuclideanComplex gEuclidean
  exact Complex.continuous_ofReal.comp (hg_cont.comp (PiLp.continuous_ofLp 2 _))

omit [NeZero Ns] in
/-- The complex Schwartz lift is integrable. -/
private theorem schwartzComplexLift_integrable
    (s : 𝓢(EuclideanSpace ℝ (Fin Ns), ℝ)) :
    Integrable
      (schwartzComplexLift Ns s : EuclideanSpace ℝ (Fin Ns) → ℂ) volume :=
  (schwartzComplexLift Ns s).integrable

omit [NeZero Ns] in
/-- The complex convolution `g_C ⋆ s_C` is integrable (Young L¹×L¹→L¹). -/
private theorem complex_convolution_integrable
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (s : 𝓢(EuclideanSpace ℝ (Fin Ns), ℝ)) :
    Integrable (MeasureTheory.convolution (gEuclideanComplex Ns g)
        (schwartzComplexLift Ns s : EuclideanSpace ℝ (Fin Ns) → ℂ)
        (ContinuousLinearMap.lsmul ℂ ℂ) volume) volume :=
  (gEuclideanComplex_integrable (Ns := Ns) g hg).integrable_convolution
    (ContinuousLinearMap.lsmul ℂ ℂ)
    (schwartzComplexLift_integrable (Ns := Ns) s)

omit [NeZero Ns] in
/-- Pointwise: the lifted real convolution equals the complex convolution of the
real-to-complex lifts. -/
private theorem realConvComplexLift_eq_complex_convolution
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (s : 𝓢(EuclideanSpace ℝ (Fin Ns), ℝ)) (w : EuclideanSpace ℝ (Fin Ns)) :
    ((realConv volume (gEuclidean Ns g) s w : ℝ) : ℂ) =
      MeasureTheory.convolution (gEuclideanComplex Ns g)
        (schwartzComplexLift Ns s : EuclideanSpace ℝ (Fin Ns) → ℂ)
        (ContinuousLinearMap.lsmul ℂ ℂ) volume w := by
  -- Both sides equal `∫ t, (g_E t : ℂ) * (s (w - t) : ℂ) dt`.
  unfold realConv MeasureTheory.convolution
  -- Use `integral_ofReal` to push `(· : ℂ)` inside the LHS integral.
  rw [show (((∫ (t : EuclideanSpace ℝ (Fin Ns)),
              ((ContinuousLinearMap.lsmul ℝ ℝ) (gEuclidean Ns g t))
                ((s : EuclideanSpace ℝ (Fin Ns) → ℝ) (w - t))) : ℝ) : ℂ) =
        ∫ (t : EuclideanSpace ℝ (Fin Ns)),
          (((((ContinuousLinearMap.lsmul ℝ ℝ) (gEuclidean Ns g t))
            ((s : EuclideanSpace ℝ (Fin Ns) → ℝ) (w - t))) : ℝ) : ℂ)
        from (integral_ofReal (𝕜 := ℂ)).symm]
  apply integral_congr_ae
  filter_upwards with t
  -- Pointwise:
  -- LHS: ((g_E t * s (w - t) : ℝ) : ℂ) = (g_E t : ℂ) * (s (w - t) : ℂ)
  -- RHS: (lsmul ℂ ℂ) (gEuclideanComplex Ns g t) (schwartzComplexLift Ns s (w - t))
  --      = (g_E t : ℂ) * (s (w - t) : ℂ)
  simp [ContinuousLinearMap.lsmul_apply, gEuclideanComplex,
    schwartzComplexLift, Complex.ofReal_mul]

omit [NeZero Ns] in
/-- The complex-lifted real convolution is in `L¹(volume)`. -/
private theorem realConvComplexLift_memLp_one
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (s : 𝓢(EuclideanSpace ℝ (Fin Ns), ℝ)) :
    MemLp (fun w => ((realConv volume (gEuclidean Ns g) s w : ℝ) : ℂ))
      1 (volume : Measure (EuclideanSpace ℝ (Fin Ns))) := by
  -- Pointwise = complex convolution, which is L¹.
  have h_int : Integrable (MeasureTheory.convolution (gEuclideanComplex Ns g)
      (schwartzComplexLift Ns s : EuclideanSpace ℝ (Fin Ns) → ℂ)
      (ContinuousLinearMap.lsmul ℂ ℂ) volume) volume :=
    complex_convolution_integrable (Ns := Ns) g hg s
  have h_eq : (fun w => ((realConv volume (gEuclidean Ns g) s w : ℝ) : ℂ))
              = MeasureTheory.convolution (gEuclideanComplex Ns g)
                  (schwartzComplexLift Ns s : EuclideanSpace ℝ (Fin Ns) → ℂ)
                  (ContinuousLinearMap.lsmul ℂ ℂ) volume :=
    funext fun w => realConvComplexLift_eq_complex_convolution (Ns := Ns) g hg s w
  rw [h_eq]
  exact memLp_one_iff_integrable.mpr h_int

set_option maxHeartbeats 800000 in
-- LHS coercion identification (heavy elaboration: chains 5 a.e. equalities).
/-- LHS coercion: `(T_conv s.toLp 2 : ℝⁿ → ℂ) =ᵐ fun ξ => 𝓕 g_C ξ * 𝓕 s_C ξ`. -/
private theorem T_conv_apply_schwartz_coeFn_ae
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) (hg_cont : Continuous g)
    (s : 𝓢(EuclideanSpace ℝ (Fin Ns), ℝ)) :
    (T_conv Ns g hg (s.toLp 2) : EuclideanSpace ℝ (Fin Ns) → ℂ) =ᵐ[volume]
    fun ξ => (𝓕 (gEuclideanComplex Ns g)) ξ *
      (𝓕 (schwartzComplexLift Ns s : EuclideanSpace ℝ (Fin Ns) → ℂ)) ξ := by
  rw [T_conv_apply_schwartz Ns g hg s,
      liftL2_ℝC_convCLM_schwartz_eq_toLp (Ns := Ns) g hg s]
  refine (fourierTransform_lp_eq_fourierIntegral Ns
    (realConvComplexLift_memLp_one (Ns := Ns) g hg s)
    (realConvComplexLift_memLp_two (Ns := Ns) g hg s)).trans ?_
  apply Filter.Eventually.of_forall
  intro ξ
  have h_eq : (fun w => ((realConv volume (gEuclidean Ns g) s w : ℝ) : ℂ))
              = MeasureTheory.convolution (gEuclideanComplex Ns g)
                  (schwartzComplexLift Ns s : EuclideanSpace ℝ (Fin Ns) → ℂ)
                  (ContinuousLinearMap.lsmul ℂ ℂ) volume :=
    funext fun w => realConvComplexLift_eq_complex_convolution (Ns := Ns) g hg s w
  rw [h_eq]
  have hg_C_int := gEuclideanComplex_integrable (Ns := Ns) g hg
  have hg_C_cont := gEuclideanComplex_continuous (Ns := Ns) g hg_cont
  have hs_C_int := schwartzComplexLift_integrable (Ns := Ns) s
  have hs_C_cont : Continuous
      (schwartzComplexLift Ns s : EuclideanSpace ℝ (Fin Ns) → ℂ) :=
    (schwartzComplexLift Ns s).continuous
  have := Real.fourier_smul_convolution_eq (E := EuclideanSpace ℝ (Fin Ns))
    (F₁ := ℂ) hg_C_int hs_C_int hg_C_cont hs_C_cont ξ
  simpa [smul_eq_mul] using this

set_option maxHeartbeats 800000 in
-- RHS coercion identification.
/-- RHS coercion: `(T_mul s.toLp 2 : ℝⁿ → ℂ) =ᵐ fun ξ => 𝓕 g_C ξ * 𝓕 s_C ξ`. -/
private theorem T_mul_apply_schwartz_coeFn_ae
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (s : 𝓢(EuclideanSpace ℝ (Fin Ns), ℝ)) :
    (T_mul Ns g hg (s.toLp 2) : EuclideanSpace ℝ (Fin Ns) → ℂ) =ᵐ[volume]
    fun ξ => (𝓕 (gEuclideanComplex Ns g)) ξ *
      (𝓕 (schwartzComplexLift Ns s : EuclideanSpace ℝ (Fin Ns) → ℂ)) ξ := by
  -- Define the Schwartz Fourier `s_C^ : 𝓢(_, ℂ)` explicitly so the
  -- final equality of underlying ℂ-functions has a clean Schwartz form.
  set s_C_hat : 𝓢(EuclideanSpace ℝ (Fin Ns), ℂ) := 𝓕 (schwartzComplexLift Ns s)
  have h_fourier : Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin Ns)) ℂ
              ((schwartzComplexLift Ns s).toLp 2)
            = s_C_hat.toLp 2 := SchwartzMap.toLp_fourier_eq _
  rw [T_mul_apply_schwartz Ns g hg s, liftL2_ℝC_schwartz_eq Ns s, h_fourier]
  -- Now: fourierWeightComplexCLM g hg (s_C_hat.toLp 2)
  have h_spec := fourierWeightComplexCLM_spec (Ns := Ns) g hg (s_C_hat.toLp 2)
  have h_inner :
      ((s_C_hat.toLp 2 : EuclideanSpace ℝ (Fin Ns) → ℂ))
        =ᵐ[volume] s_C_hat :=
    SchwartzMap.coeFn_toLp s_C_hat 2 _
  filter_upwards [h_spec, h_inner] with w hw hwc
  rw [hw, hwc]
  -- gHat Ns g w = 𝓕 (gEuclideanComplex Ns g) w  (rfl, since the casts agree).
  rfl

/-- **Step 6**: the Schwartz base case `T_conv s = T_mul s` for the
CLM-firewall density argument. -/
private theorem T_conv_eq_T_mul_schwartz
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) (hg_cont : Continuous g)
    (s : 𝓢(EuclideanSpace ℝ (Fin Ns), ℝ)) :
    T_conv Ns g hg (s.toLp 2) = T_mul Ns g hg (s.toLp 2) := by
  apply Subtype.coe_injective
  apply MeasureTheory.AEEqFun.ext
  filter_upwards [T_conv_apply_schwartz_coeFn_ae (Ns := Ns) g hg hg_cont s,
                  T_mul_apply_schwartz_coeFn_ae (Ns := Ns) g hg s]
    with w hL hR
  rw [hL]; exact hR.symm

/-- **Step 7**: extend from Schwartz to all of `Lp ℝ 2` via Schwartz density.
The CLMs `T_conv g hg` and `T_mul g hg` agree on the dense Schwartz subset
(by step 6) and are both continuous, so `DenseRange.equalizer` gives the
full equality of functions. Since both are CLMs, that lifts to CLM equality. -/
private theorem T_conv_eq_T_mul
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) (hg_cont : Continuous g) :
    T_conv Ns g hg = T_mul Ns g hg := by
  -- Function equality of the underlying maps via DenseRange.equalizer
  have h_dense :
      DenseRange (SchwartzMap.toLpCLM ℝ ℝ 2
        (volume : Measure (EuclideanSpace ℝ (Fin Ns)))) :=
    SchwartzMap.denseRange_toLpCLM (E := EuclideanSpace ℝ (Fin Ns))
      (F := ℝ) (p := 2)
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin Ns))))
      (ENNReal.ofNat_ne_top)
  have h_eq_fun :
      (T_conv Ns g hg :
        Lp (α := EuclideanSpace ℝ (Fin Ns)) ℝ 2 →
        Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) =
      (T_mul Ns g hg :
        Lp (α := EuclideanSpace ℝ (Fin Ns)) ℝ 2 →
        Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) := by
    refine h_dense.equalizer (T_conv Ns g hg).continuous (T_mul Ns g hg).continuous ?_
    funext s
    exact T_conv_eq_T_mul_schwartz Ns g hg hg_cont s
  -- Lift function equality to CLM equality
  exact DFunLike.coe_injective h_eq_fun

omit [NeZero Ns] in
/-- Transport the spatial convolution operator to Euclidean `L²`. -/
private theorem toEuclideanRealL2_convCLM
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume) (f : L2SpatialField Ns) :
    toEuclideanRealL2 Ns (convCLM g hg f) =
      convCLM (gEuclidean Ns g) (gEuclidean_memLp (Ns := Ns) g hg) (toEuclideanRealL2 Ns f) := by
  apply Subtype.coe_injective
  apply MeasureTheory.AEEqFun.ext
  have h_lhs :
      (toEuclideanRealL2 Ns (convCLM g hg f) : EuclideanSpace ℝ (Fin Ns) → ℝ) =ᵐ[volume]
      fun w =>
        (convCLM g hg f : SpatialField Ns → ℝ)
          ((WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns) w) := by
    simpa [toEuclideanRealL2] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving
        (g := convCLM g hg f)
        (hf := PiLp.volume_preserving_ofLp (ι := Fin Ns)))
  have h_lhs_conv :
      (fun w =>
        (convCLM g hg f : SpatialField Ns → ℝ)
          ((WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns) w)) =ᵐ[volume]
      fun w =>
        realConv volume g f
          ((WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns) w) := by
    exact (PiLp.volume_preserving_ofLp (ι := Fin Ns)).quasiMeasurePreserving.ae_eq_comp
      (convCLM_spec g hg f)
  have h_rhs_input :
      (toEuclideanRealL2 Ns f : EuclideanSpace ℝ (Fin Ns) → ℝ) =ᵐ[volume]
      fun w => f ((WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns) w) := by
    simpa [toEuclideanRealL2] using
      (MeasureTheory.Lp.coeFn_compMeasurePreserving
        (g := f)
        (hf := PiLp.volume_preserving_ofLp (ι := Fin Ns)))
  have h_realConv_transport :
      realConv volume (gEuclidean Ns g)
          (fun w => f ((WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns) w)) =
        fun w =>
          realConv volume g f
            ((WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns) w) := by
    funext w
    unfold realConv MeasureTheory.convolution gEuclidean
    simpa using
      (MeasurePreserving.integral_comp
        (PiLp.volume_preserving_ofLp (ι := Fin Ns))
        (MeasurableEquiv.toLp 2 (SpatialField Ns)).symm.measurableEmbedding
        (fun x : SpatialField Ns =>
          g x * f (((WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns) w) - x)))
  have h_rhs_conv :
      realConv volume (gEuclidean Ns g) (toEuclideanRealL2 Ns f : EuclideanSpace ℝ (Fin Ns) → ℝ) =
        fun w =>
          realConv volume g f
            ((WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns) w) := by
    calc
      realConv volume (gEuclidean Ns g) (toEuclideanRealL2 Ns f : EuclideanSpace ℝ (Fin Ns) → ℝ)
          = realConv volume (gEuclidean Ns g)
              (fun w => f ((WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns) w)) := by
              unfold realConv
              exact MeasureTheory.convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
                Filter.EventuallyEq.rfl h_rhs_input
      _ = fun w =>
            realConv volume g f
              ((WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns) w) :=
        h_realConv_transport
  have h_rhs :
      (convCLM (gEuclidean Ns g) (gEuclidean_memLp (Ns := Ns) g hg) (toEuclideanRealL2 Ns f) :
          EuclideanSpace ℝ (Fin Ns) → ℝ) =ᵐ[volume]
      fun w =>
        realConv volume g f
          ((WithLp.ofLp : EuclideanSpace ℝ (Fin Ns) → SpatialField Ns) w) := by
    have h_spec := convCLM_spec (gEuclidean Ns g) (gEuclidean_memLp (Ns := Ns) g hg)
      (toEuclideanRealL2 Ns f)
    filter_upwards [h_spec] with w hw
    rw [hw, h_rhs_conv]
  exact h_lhs.trans (h_lhs_conv.trans h_rhs.symm)

set_option maxHeartbeats 800000 in
-- Elaborating the complex-weight quadratic form follows the same heavy L² coercion
-- path as the already-proved real-part-weight version above.
omit [NeZero Ns] in
/-- Expanding the real part of the complex-weight Fourier quadratic form. -/
private theorem fourierQuadFormComplex_eq_integral
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) :
    (@inner ℂ _ _ h (fourierWeightComplexCLM Ns g hg h)).re =
      ∫ w : EuclideanSpace ℝ (Fin Ns),
        (gHat Ns g w).re * ‖(h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w‖ ^ 2 := by
  rw [MeasureTheory.L2.inner_def]
  change RCLike.re (∫ a : EuclideanSpace ℝ (Fin Ns),
    inner ℂ (h a) ((fourierWeightComplexCLM Ns g hg h) a) ∂volume) =
      ∫ w : EuclideanSpace ℝ (Fin Ns),
        (gHat Ns g w).re * ‖(h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w‖ ^ 2
  have hre :
      ∫ a : EuclideanSpace ℝ (Fin Ns),
        RCLike.re (inner ℂ (h a) ((fourierWeightComplexCLM Ns g hg h) a)) ∂volume =
      RCLike.re (∫ a : EuclideanSpace ℝ (Fin Ns),
        inner ℂ (h a) ((fourierWeightComplexCLM Ns g hg h) a) ∂volume) :=
    integral_re (MeasureTheory.L2.integrable_inner h (fourierWeightComplexCLM Ns g hg h))
  rw [← hre]
  apply integral_congr_ae
  filter_upwards [fourierWeightComplexCLM_spec (Ns := Ns) g hg h] with w hw
  rw [hw]
  have hnorm :
      ‖(h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w‖ ^ 2 =
        ((h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w).re ^ 2 +
        ((h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w).im ^ 2 := by
    simpa [Complex.sq_norm, Complex.normSq_apply, sq, add_comm, add_left_comm, add_assoc] using
      (Complex.sq_norm ((h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w))
  rw [hnorm]
  simp [RCLike.inner_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

set_option maxHeartbeats 800000 in
-- Gaussian Fourier integral convergence
/-- The Fourier representation of the convolution quadratic form:
  `⟨f, g⋆f⟩_ℝ = ∫ Re(ĝ_ℂ(w)) · ‖f̂_ℂ(w)‖² dw`

This is the L² generalization of the standard identity that, for Schwartz functions,
follows from the convolution theorem (`Real.fourier_smul_convolution_eq`) and
Parseval's identity (`SchwartzMap.integral_sesq_fourier_fourier`).

**Proof strategy** (CLM firewall + Schwartz density, *Gemini deep-think 2026-04-30*):
The identity is best proved as an equality of continuous linear maps from
`Lp ℝ 2 → Lp ℂ 2`, **not** as an equality of integral expressions:

  T_conv f := 𝓕 (liftL2 (convCLM g hg f))            (real → complex → conv → 𝓕)
  T_mul  f := gHat_ℂ • 𝓕 (liftL2 f)                   (real → complex → 𝓕 → multiply)

By `ContinuousLinearMap.ext_of_denseRange` on `SchwartzMap.denseRange_toLpCLM`
(Schwartz dense in L²), it suffices to verify `T_conv s = T_mul s` for Schwartz
`s`. For such `s`, `g ⋆ s ∈ L¹ ∩ L²` and Mathlib's
`Real.fourier_smul_convolution_eq` gives `𝓕_{L¹}(g ⋆ s) = ĝ · ŝ` a.e.
Combined with `fourierTransform_lp_eq_fourierIntegral` (the textbook axiom
above) and `SchwartzMap.toLp_fourier_eq`, this yields `T_conv s = T_mul s`.

After the CLM equality, Plancherel-via-`Lp.inner_fourier_eq` reduces the
identity `⟨f, convCLM g hg f⟩_ℝ = ∫ Re(ĝ)·|f̂|²` to expanding the inner
product `⟨𝓕 (liftL2 f), gHat_ℂ • 𝓕 (liftL2 f)⟩_ℂ` as an integral and taking
real parts via `MeasureTheory.integral_re`.

**Status (2026-04-30)**: stated as axiom; the supporting helpers
(`liftL2`-style real↔complex L² isometry, `gHatRe_*`, `fourierWeightCLM`,
both-sides-continuous lemmas, `integrand_integrable`) are all proved above.
The remaining gap is the Lp-coercion gymnastics in the Schwartz-base-case
chain — four codex attempts stalled on elaboration time around `Lp.ext` /
multiplier packaging there.

References: Folland, *Real Analysis*, §8.3; Reed-Simon I, §IX.4. -/
private theorem fourier_representation_convolution
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (hg_cont : Continuous g) (f : L2SpatialField Ns) :
    @inner ℝ _ _ f (convCLM g hg f) =
    ∫ w : EuclideanSpace ℝ (Fin Ns),
      (gHat Ns g w).re *
      ‖(fHat Ns f : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w‖ ^ 2 := by
  let fE := toEuclideanRealL2 Ns f
  let hE := convCLM (gEuclidean Ns g) (gEuclidean_memLp (Ns := Ns) g hg) fE
  let Ff : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 :=
    Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin Ns)) ℂ (liftL2_ℝC Ns fE)
  have h0 :
      @inner ℝ _ _ f (convCLM g hg f) =
      @inner ℝ _ _ fE (toEuclideanRealL2 Ns (convCLM g hg f)) := by
    simpa [fE] using ((toEuclideanRealL2 Ns).inner_map_map f (convCLM g hg f)).symm
  have h1 :
      @inner ℝ _ _ fE (toEuclideanRealL2 Ns (convCLM g hg f)) =
      @inner ℝ _ _ fE hE := by
    simpa [fE, hE] using congrArg (fun h => @inner ℝ _ _ fE h)
      (toEuclideanRealL2_convCLM (Ns := Ns) g hg f)
  have h2 :
      @inner ℝ _ _ fE hE =
      (@inner ℂ _ _ (liftL2_ℝC Ns fE) (liftL2_ℝC Ns hE)).re := by
    simpa [fE, hE] using inner_eq_re_inner_liftL2 (Ns := Ns) fE hE
  have h3 :
      (@inner ℂ _ _ (liftL2_ℝC Ns fE) (liftL2_ℝC Ns hE)).re =
      (@inner ℂ _ _ Ff
        (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin Ns)) ℂ
          (liftL2_ℝC Ns hE))).re := by
    simpa [Ff] using congrArg Complex.re
      (Lp.inner_fourier_eq (liftL2_ℝC Ns fE) (liftL2_ℝC Ns hE)).symm
  have h4 :
      (@inner ℂ _ _ Ff
        (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin Ns)) ℂ
          (liftL2_ℝC Ns hE))).re =
      (@inner ℂ _ _ Ff (T_conv Ns g hg fE)).re := by
    rfl
  have h5 :
      (@inner ℂ _ _ Ff (T_conv Ns g hg fE)).re =
      (@inner ℂ _ _ Ff (T_mul Ns g hg fE)).re := by
    rw [T_conv_eq_T_mul (Ns := Ns) g hg hg_cont]
  have h6 :
      (@inner ℂ _ _ Ff (T_mul Ns g hg fE)).re =
      (@inner ℂ _ _ Ff (fourierWeightComplexCLM Ns g hg Ff)).re := by
    rfl
  have h7 :
      (@inner ℂ _ _ Ff (fourierWeightComplexCLM Ns g hg Ff)).re =
      ∫ w : EuclideanSpace ℝ (Fin Ns),
        (gHat Ns g w).re * ‖(Ff : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w‖ ^ 2 := by
    simpa [Ff] using fourierQuadFormComplex_eq_integral (Ns := Ns) g hg Ff
  have h8 :
      (∫ w : EuclideanSpace ℝ (Fin Ns),
        (gHat Ns g w).re * ‖(Ff : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w‖ ^ 2) =
      ∫ w : EuclideanSpace ℝ (Fin Ns),
        (gHat Ns g w).re * ‖(fHat Ns f : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w‖ ^ 2 := by
    have h_ft : Ff = fHat Ns f := by
      simpa [Ff, fE, fHat] using congrArg
        (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin Ns)) ℂ)
        (toEuclideanComplexL2_eq_lift (Ns := Ns) f).symm
    simpa [h_ft]
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans h8)))))))

omit [NeZero Ns] in
/-- The integrand `Re(ĝ(w)) * ‖f̂(w)‖²` in the Fourier representation is integrable.

Since `g ∈ L¹` implies `|Re(ĝ(w))| ≤ ‖ĝ(w)‖ ≤ ‖g‖₁` (bounded pointwise),
and `f̂ ∈ L²` implies `‖f̂(w)‖²` is integrable, the product is dominated by
`‖g‖₁ · ‖f̂(w)‖²` and hence integrable. -/
private theorem integrand_integrable
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (f : L2SpatialField Ns) :
    Integrable (fun w : EuclideanSpace ℝ (Fin Ns) =>
      (𝓕 (fun (v : EuclideanSpace ℝ (Fin Ns)) =>
        (g ((WithLp.equiv 2 _) v) : ℂ)) w).re *
      ‖(Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin Ns)) ℂ
        (toEuclideanComplexL2 Ns f) : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w‖ ^ 2) := by
  exact integrand_integrable_aux g hg _
where
  /-- Helper: for any h in L2(C) on EuclideanSpace, Re(g-hat) * ||h||^2 is integrable. -/
  integrand_integrable_aux
      (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
      (h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2
          (volume : Measure (EuclideanSpace ℝ (Fin Ns)))) :
      Integrable (fun w : EuclideanSpace ℝ (Fin Ns) =>
        (𝓕 (fun (v : EuclideanSpace ℝ (Fin Ns)) =>
          (g ((WithLp.equiv 2 _) v) : ℂ)) w).re *
        ‖(h : EuclideanSpace ℝ (Fin Ns) → ℂ) w‖ ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin Ns))) := by
    set g_ℂ : EuclideanSpace ℝ (Fin Ns) → ℂ := fun v => (g ((WithLp.equiv 2 _) v) : ℂ)
    -- ‖h(w)‖² is integrable since h ∈ L²
    have h_normsq_int : Integrable (fun w => ‖(h : EuclideanSpace ℝ (Fin Ns) → ℂ) w‖ ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin Ns))) :=
      (memLp_two_iff_integrable_sq_norm (Lp.memLp h).1).mp (Lp.memLp h)
    -- |Re(ĝ(w))| ≤ ∫ ‖g_ℂ‖
    set C := ∫ v : EuclideanSpace ℝ (Fin Ns), ‖g_ℂ v‖
    have h_bound : ∀ w, |(𝓕 g_ℂ w).re| ≤ C := fun w =>
      (abs_re_le_norm _).trans (VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ w)
    -- Measurability
    have h_ghat_cont := ghat_continuous Ns g hg
    have h_meas : AEStronglyMeasurable
        (fun w => (𝓕 g_ℂ w).re * ‖(h : EuclideanSpace ℝ (Fin Ns) → ℂ) w‖ ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin Ns))) :=
      (continuous_re.comp h_ghat_cont).aestronglyMeasurable.mul
        ((Lp.memLp h).1.norm.pow 2)
    -- Domination by C * ‖h(w)‖²
    refine (h_normsq_int.const_mul C).mono' h_meas (ae_of_all _ fun w => ?_)
    have h2 : (0 : ℝ) ≤ ‖(h : EuclideanSpace ℝ (Fin Ns) → ℂ) w‖ ^ 2 := sq_nonneg _
    calc ‖(𝓕 g_ℂ w).re * ‖(h : EuclideanSpace ℝ (Fin Ns) → ℂ) w‖ ^ 2‖
        = |(𝓕 g_ℂ w).re| * ‖(h : EuclideanSpace ℝ (Fin Ns) → ℂ) w‖ ^ 2 := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
      _ ≤ C * ‖(h : EuclideanSpace ℝ (Fin Ns) → ℂ) w‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (h_bound w) h2

set_option maxHeartbeats 400000 in
-- Plancherel support measure positivity
omit [NeZero Ns] in
private theorem support_pos_of_ae_nonzero
    (h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2)
    (h_nz : ¬ ∀ᵐ w : EuclideanSpace ℝ (Fin Ns) ∂volume,
      (h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w = 0) :
    0 < volume (Function.support fun w =>
      (h : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w) := by
  rw [pos_iff_ne_zero]
  intro h_zero
  apply h_nz
  rw [ae_iff]
  exact h_zero

theorem inner_convCLM_pos_of_fourier_pos
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    (hg_cont : Continuous g)
    -- ĝ_ℂ has positive real part everywhere, where ĝ is computed on
    -- EuclideanSpace ℝ (Fin Ns) (which has the inner product structure
    -- needed for the Fourier transform)
    (hĝ_pos : ∀ w : EuclideanSpace ℝ (Fin Ns),
      0 < (𝓕 (fun (v : EuclideanSpace ℝ (Fin Ns)) =>
        (g ((WithLp.equiv 2 _) v) : ℂ)) w).re)
    (f : L2SpatialField Ns) (hf : f ≠ 0) :
    0 < @inner ℝ _ _ f (convCLM g hg f) := by
  -- Step 1: Use the Fourier representation identity
  rw [fourier_representation_convolution Ns g hg hg_cont f]
  -- Abbreviations for readability
  let ghat_re : EuclideanSpace ℝ (Fin Ns) → ℝ := fun w =>
    (𝓕 (fun (v : EuclideanSpace ℝ (Fin Ns)) =>
      (g ((WithLp.equiv 2 _) v) : ℂ)) w).re
  let fhat : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2 :=
    Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin Ns)) ℂ (toEuclideanComplexL2 Ns f)
  -- The integrand
  let integrand : EuclideanSpace ℝ (Fin Ns) → ℝ := fun w =>
    ghat_re w * ‖(fhat : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w‖ ^ 2
  -- Step 2: The integrand is nonneg
  have h_nonneg : ∀ w, 0 ≤ integrand w :=
    fun w => mul_nonneg (hĝ_pos w).le (sq_nonneg _)
  -- Step 3: f != 0 implies f-hat not ae zero (Plancherel injectivity)
  have h_ft_nz := fourier_ae_nonzero_of_spatial_nonzero Ns f hf
  -- Convert "not ae zero" to "support has positive measure"
  have h_support_pos :
      0 < volume (Function.support fun w =>
        (fhat : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w) :=
    support_pos_of_ae_nonzero Ns fhat h_ft_nz
  -- Step 4: The support of the integrand equals the support of f-hat
  -- (since Re(g-hat(w)) > 0, the product vanishes iff ||f-hat(w)||^2 = 0)
  have h_support_eq : Function.support integrand =
      Function.support fun w =>
        (fhat : Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2) w := by
    ext w
    simp only [Function.mem_support, ne_eq, integrand, ghat_re]
    constructor
    · intro h hfw; exact h (by simp [hfw])
    · intro h hprod
      rcases mul_eq_zero.mp hprod with h1 | h1
      · exact absurd h1 (ne_of_gt (hĝ_pos w))
      · exact h (by rwa [sq_eq_zero_iff, norm_eq_zero] at h1)
  -- Step 5: Conclude positivity
  change 0 < ∫ w, integrand w
  rw [integral_pos_iff_support_of_nonneg_ae (ae_of_all _ h_nonneg)]
  · rwa [h_support_eq]
  · -- Integrability of integrand
    exact integrand_integrable Ns g hg f

/-! ## Gaussian convolution is strictly PD -/

/-- **Gaussian convolution is strictly positive definite on L²(ℝⁿ, ℝ)**.

**Proof**: The transfer Gaussian `G(ψ) = exp(-½ Σᵢ ψᵢ²)` has
`G(v) = exp(-½‖v‖²)` on EuclideanSpace, so its Fourier transform
`Ĝ(k) = (2π)^{n/2} exp(-2π²‖k‖²) > 0` by `fourier_gaussian_pos`.
Apply `inner_convCLM_pos_of_fourier_pos`. -/
theorem gaussian_conv_strictlyPD :
    ∀ (f : L2SpatialField Ns), f ≠ 0 →
      0 < @inner ℝ _ _ f (convCLM (transferGaussian Ns) (transferGaussian_memLp Ns) f) := by
  let _ := (inferInstance : NeZero Ns)
  intro f hf
  apply inner_convCLM_pos_of_fourier_pos Ns
      (transferGaussian Ns) (transferGaussian_memLp Ns) (continuous_transferGaussian Ns) _ f hf
  -- Need: ∀ w, 0 < Re(𝓕(G_ℂ)(w))
  -- transferGaussian Ns ψ = exp(- timeCoupling Ns 0 ψ) = exp(-½ Σᵢ ψᵢ²)
  -- On EuclideanSpace: G(v) = exp(-½‖v‖²) = exp(-(1/2)‖v‖²)
  intro w
  -- Show the FT integrand matches exp(-b‖v‖²) with b = 1/2
  have hG_eq : (fun (v : EuclideanSpace ℝ (Fin Ns)) =>
      (transferGaussian Ns ((WithLp.equiv 2 _) v) : ℂ)) =
      (fun v => cexp (-(1/2 : ℂ) * (‖v‖ : ℂ) ^ 2)) := by
    ext v
    simp only [transferGaussian, timeCoupling]
    -- Goal: ↑(exp(-(1/2 * ∑ x, (0 x - equiv v x)²))) = cexp(-(1/2) * ↑‖v‖²)
    rw [ofReal_exp]
    congr 1
    -- ↑(-(1/2 * ∑ x, (0 x - equiv v x)²)) = -(1/2) * ↑‖v‖²
    -- First show the ℝ equality, then cast
    have : (-(1 / 2 * ∑ x : Fin Ns,
        ((0 : SpatialField Ns) x - (WithLp.equiv 2 (SpatialField Ns)) v x) ^ 2) : ℝ) =
        -(1/2) * ‖v‖ ^ 2 := by
      simp only [Pi.zero_apply, zero_sub, neg_sq]
      rw [EuclideanSpace.norm_sq_eq v]
      simp only [Real.norm_eq_abs, sq_abs]
      have : ∀ i, (WithLp.equiv 2 (SpatialField Ns)) v i = v.1 i := fun i => rfl
      simp_rw [this]; ring
    rw [this]; push_cast; ring
  rw [hG_eq]
  convert fourier_gaussian_pos (by norm_num : (0 : ℝ) < 1/2) w using 3
  simp [ofReal_ofNat]

/-!
Status note for `fourier_representation_convolution` (2026-04-30):

Proved helpers left in this file:
- `gEuclidean_memLp`
- `liftL2_ℝC`
- `liftL2_ℝC_spec`
- `fourierRealCLM`
- `gHat_memLp_top`
- `gHatLp`
- `fourierWeightComplexCLM`
- `fourierWeightComplexCLM_spec`
- `fourierWeightComplexRealCLM`
- `T_conv`
- `T_mul`
- `T_conv_apply_schwartz`
- `T_mul_apply_schwartz`

Remaining gap:
The file still needs the Schwartz base-case equality
`T_conv_eq_T_mul_schwartz`, then the dense-range extension
`T_conv_eq_T_mul`, and finally the Plancherel scalar identity that replaces
the axiom `fourier_representation_convolution`. The obstruction is the
Lp-representative comparison step that combines
`fourierTransform_lp_eq_fourierIntegral`,
`Real.fourier_smul_convolution_eq`, and `SchwartzMap.toLp_fourier_eq`
into a single equality in `Lp (α := EuclideanSpace ℝ (Fin Ns)) ℂ 2`.
Concretely, the missing API-level bridge is an ergonomic way to turn the
a.e. pointwise identity from `fourierTransform_lp_eq_fourierIntegral`
together with `fourierWeightComplexCLM_spec` into equality of `Lp`
elements without redoing the `MemLp.toLp_congr`/multiplier packaging by hand.
-/

end Pphi2

end
