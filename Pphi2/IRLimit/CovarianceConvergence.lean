/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas

# Covariance Convergence: Torus → Cylinder as Lt → ∞

States and proves (modulo the remaining IR-limit axioms unrelated to covariance)
that the torus Green's function of embedded cylinder test functions converges
to the physically normalized cylinder Green function as the temporal period
Lt → ∞.

## Mathematical content

On the asymmetric torus T_{Lt,Ls}, the Green's function in the
mixed spectral representation (Fourier in x, position in t) is:

  `G_{Lt,Ls}((t,x),(t',x')) = (1/Ls) Σ_n e^{2πin(x-x')/Ls}
      · cosh(ω_n(Lt/2 - |t-t'|)) / (2ω_n sinh(ω_n Lt/2))`

where `ω_n = √((2πn/Ls)² + m²)` is the dispersion relation.

As Lt → ∞, `coth(ω_n Lt/2) → 1`, so each mode's 1D Green's function
converges:

  `cosh(ω_n(Lt/2 - |t|)) / (2ω_n sinh(ω_n Lt/2)) → e^{-ω_n|t|} / (2ω_n)`

The convergence is exponentially fast: the error is O(e^{-m Lt})
since `ω_n ≥ m > 0` for all n (mass gap).

At the level of test functions (bilinear forms), this gives:

  `asymTorusContinuumGreen Lt Ls mass (embed f) (embed g)
    → physicalCylinderGreen Ls mass f g`

as Lt → ∞, where `embed = cylinderToTorusEmbed Lt Ls`.

## Main results

- `asymTorusGreen_tendsto_physicalCylinderGreen` — covariance convergence
- `cylinderIRLimit_covariance_eq` — the IR limit measure has the correct
  physically normalized cylinder covariance
- `cylinderPullbackGFF_secondMoment_eq_torus` — pullback second moment equals
  torus second moment on `cylinderToTorusEmbed` (via `cylinderPullbackMeasure_integral_sq`)
- Scalar 1D periodic/free kernel comparison — `Pphi2.GeneralResults.PeriodicResolvent1D`
  (definitions `periodicKernel`, `freeKernel`; this file keeps expanded `Pphi2.periodicResolvent_*` aliases)

## References

- Glimm-Jaffe, *Quantum Physics*, §19.1 (infinite volume limit)
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII
-/

import Pphi2.IRLimit.CylinderOS
import Pphi2.AsymTorus.AsymTorusEmbedding
import Pphi2.GeneralResults.PeriodicResolvent1D
import Pphi2.TorusContinuumLimit.MeasureUniqueness
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory Filter ProbabilityTheory Complex PeriodicResolvent1D

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]

/-! ## Green's function convergence

The key analytical fact: the asymmetric torus Green's function of
embedded cylinder test functions converges to the cylinder Green's
function as the temporal period Lt → ∞.

### Proof sketch (not yet formalized)

For pure tensors `f = g ⊗ h` where `g ∈ C∞(S¹_{Ls})` and `h ∈ 𝓢(ℝ)`:

1. `cylinderToTorusEmbed` maps `g ⊗ h ↦ (periodize h) ⊗ g` (periodize
   temporal factor, swap order).

2. The torus Green's function in the spatial Fourier basis is:
     `G_{Lt,Ls}(f,f) = (1/Ls) Σ_n |ĉ_n(g)|² · ∫∫ h̃_n(t) h̃_n(t')
        · cosh(ω_n(Lt/2-|t-t'|)) / (2ω_n sinh(ω_n Lt/2)) dt dt'`
   where `h̃_n` is the periodization of h restricted to mode n.

3. As Lt → ∞, `periodize(h)` converges to `h` on any compact set
   (the wrap-around terms decay like `e^{-m Lt}`), and the 1D periodic
   Green's function converges to the non-periodic one:
     `cosh(ω(Lt/2-|t|))/(2ω sinh(ωLt/2)) → e^{-ω|t|}/(2ω)`

4. Dominated convergence: the uniform bound from `torusGreen_uniform_bound`
   provides the dominating function. The series over spatial modes n
   converges uniformly because `ω_n → ∞` and Schwartz coefficients
   decay rapidly.

5. The limit equals `cylinderGreen Ls mass f g` by the spectral
   representation of the cylinder covariance. -/

private theorem schwartz_l2InnerProduct_eq_integral_mul
    (f g : SchwartzMap ℝ ℝ) :
    l2InnerProduct f g = ∫ t, f t * g t := by
  let φ : SchwartzMap ℝ ℝ →L[ℝ] ℝ :=
    (SchwartzMap.integralCLM (𝕜 := ℝ) (μ := MeasureTheory.volume)).comp
      (SchwartzMap.smulLeftCLM ℝ (fun t : ℝ => g t))
  calc
    l2InnerProduct f g = ∑' n, hermiteCoeff1D n f * hermiteCoeff1D n g := by
      rfl
    _ = ∑' n, hermiteCoeff1D n f * φ (schwartzHermiteBasis1D n) := by
      congr with n
      congr 1
      calc
        hermiteCoeff1D n g = ∫ t, g t * hermiteFunction n t := rfl
        _ = φ (schwartzHermiteBasis1D n) := by
          unfold φ
          rw [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply]
          congr 1
          ext t
          rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth]
          rw [schwartzHermiteBasis1D_apply, smul_eq_mul]
    _ = φ f := by
      symm
      exact schwartz_hermite_expansion_CLF φ f
    _ = ∫ t, f t * g t := by
      unfold φ
      rw [ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply]
      congr 1
      ext t
      rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth, smul_eq_mul]
      ring

private theorem resolventSymbol_mul_self
    (ω : ℝ) (hω : 0 < ω) (ξ : ℝ) :
    resolventSymbol ω ξ * resolventSymbol ω ξ = (ξ ^ 2 + ω ^ 2)⁻¹ := by
  have hpos : 0 < ξ ^ 2 + ω ^ 2 := by positivity
  unfold resolventSymbol
  rw [← Real.rpow_add hpos]
  have hsum : -(1 : ℝ) / 2 + -(1 : ℝ) / 2 = ((-1 : ℤ) : ℝ) := by
    norm_num
  rw [hsum]
  simpa using (Real.rpow_intCast (ξ ^ 2 + ω ^ 2) (-1 : ℤ))

private theorem resolventMultiplierCLM_comp_eq_squaredSymbol
    (ω : ℝ) (hω : 0 < ω) :
    (resolventMultiplierCLM hω).comp (resolventMultiplierCLM hω) =
      realFourierMultiplierCLM
        (fun ξ : ℝ => resolventSymbol ω ξ * resolventSymbol ω ξ)
        ((resolventSymbol_hasTemperateGrowth ω hω).mul
          (resolventSymbol_hasTemperateGrowth ω hω)) := by
  simpa [resolventMultiplierCLM] using
    (realFourierMultiplierCLM_comp
      (σ₁ := resolventSymbol ω) (σ₂ := resolventSymbol ω)
      (hσ₁ := resolventSymbol_hasTemperateGrowth ω hω)
      (hσ₂ := resolventSymbol_hasTemperateGrowth ω hω)
      (hσ₂_even := resolventSymbol_even ω))

private theorem resolventInverseSymbol_hasTemperateGrowth
    (ω : ℝ) (hω : 0 < ω) :
    Function.HasTemperateGrowth (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹) := by
  convert
    (resolventSymbol_hasTemperateGrowth ω hω).mul
      (resolventSymbol_hasTemperateGrowth ω hω) using 1
  ext ξ
  exact (resolventSymbol_mul_self ω hω ξ).symm

private theorem resolventMultiplierCLM_comp_apply_eq_inverseSymbol
    (ω : ℝ) (hω : 0 < ω) (h : SchwartzMap ℝ ℝ) :
    resolventMultiplierCLM hω (resolventMultiplierCLM hω h) =
      realFourierMultiplierCLM
        (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
        (resolventInverseSymbol_hasTemperateGrowth ω hω)
        h := by
  have happly :=
    congr_fun (congr_arg DFunLike.coe (resolventMultiplierCLM_comp_eq_squaredSymbol ω hω)) h
  simpa [resolventSymbol_mul_self ω hω] using happly

attribute [local instance] SMulCommClass.symm in
private theorem schwartzToComplex_realFourierMultiplier_eq
    (σ : ℝ → ℝ) (hσ : σ.HasTemperateGrowth)
    (heven : ∀ ξ, σ (-ξ) = σ ξ) (f : SchwartzMap ℝ ℝ) :
    schwartzToComplex (realFourierMultiplierCLM σ hσ f) =
      SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ (schwartzToComplex f) := by
  have preserves := fourierMultiplier_preserves_real σ hσ heven
  have happly := ContinuousLinearMap.ext_iff.mp preserves f
  simp only [ContinuousLinearMap.comp_apply] at happly
  simpa [realFourierMultiplierCLM] using happly

private theorem schwartzToComplex_integral_inner_eq_ofReal_integral_mul
    (f g : SchwartzMap ℝ ℝ) :
    (∫ x, @inner ℂ ℂ _ (schwartzToComplex f x) (schwartzToComplex g x)) =
      ((∫ x, f x * g x : ℝ) : ℂ) := by
  have hfg :
      (fun x => @inner ℂ ℂ _ (schwartzToComplex f x) (schwartzToComplex g x)) =
        fun x => ((f x * g x : ℝ) : ℂ) := by
    funext x
    simp [schwartzToComplex, RCLike.inner_apply, mul_comm]
  rw [hfg]
  simpa using
    (integral_complex_ofReal (f := fun x : ℝ => f x * g x) (μ := MeasureTheory.volume))

private theorem resolventInverseSymbol_even
    (ω : ℝ) (ξ : ℝ) :
    ((-ξ) ^ 2 + ω ^ 2)⁻¹ = (ξ ^ 2 + ω ^ 2)⁻¹ := by
  ring_nf

private def mathlibResolventKernelReal (ω t : ℝ) : ℝ :=
  Real.pi / ω * Real.exp (-(2 * Real.pi * ω) * |t|)

private def mathlibResolventKernelC (ω : ℝ) : ℝ → ℂ :=
  fun t => (mathlibResolventKernelReal ω t : ℂ)

private theorem continuous_mathlibResolventKernelReal (ω : ℝ) :
    Continuous (mathlibResolventKernelReal ω) := by
  change Continuous (fun t : ℝ =>
    Real.pi / ω * Real.exp (-(2 * Real.pi * ω) * |t|))
  fun_prop

private theorem continuous_mathlibResolventKernelC (ω : ℝ) :
    Continuous (mathlibResolventKernelC ω) := by
  change Continuous (fun t : ℝ =>
    (((Real.pi / ω * Real.exp (-(2 * Real.pi * ω) * |t|) : ℝ)) : ℂ))
  fun_prop

private theorem integrable_mathlibResolventKernelC
    (ω : ℝ) (hω : 0 < ω) :
    Integrable (mathlibResolventKernelC ω) := by
  rw [← MeasureTheory.integrableOn_univ, ← Set.Iic_union_Ioi, MeasureTheory.integrableOn_union]
  constructor
  · let c : ℂ := ((Real.pi / ω : ℝ) : ℂ)
    let a : ℂ := ((2 * Real.pi * ω : ℝ) : ℂ)
    have ha : 0 < a.re := by
      change 0 < 2 * Real.pi * ω
      positivity
    have hmodel :
        MeasureTheory.IntegrableOn (fun t : ℝ => c * Complex.exp (a * t)) (Set.Iic 0) := by
      exact (integrableOn_exp_mul_complex_Iic ha 0).const_mul c
    refine MeasureTheory.IntegrableOn.congr_fun hmodel ?_ measurableSet_Iic
    intro t ht
    have habs : |t| = -t := abs_of_nonpos ht
    simp [mathlibResolventKernelC, mathlibResolventKernelReal, c, a, habs, Complex.ofReal_exp,
      div_eq_mul_inv]
  · let c : ℂ := ((Real.pi / ω : ℝ) : ℂ)
    let a : ℂ := ((-(2 * Real.pi * ω : ℝ)) : ℂ)
    have ha : a.re < 0 := by
      change -(2 * Real.pi * ω) < 0
      nlinarith [Real.pi_pos, hω]
    have hmodel :
        MeasureTheory.IntegrableOn (fun t : ℝ => c * Complex.exp (a * t)) (Set.Ioi 0) := by
      exact (integrableOn_exp_mul_complex_Ioi ha 0).const_mul c
    refine MeasureTheory.IntegrableOn.congr_fun hmodel ?_ measurableSet_Ioi
    intro t ht
    have habs : |t| = t := abs_of_nonneg (le_of_lt ht)
    simp [mathlibResolventKernelC, mathlibResolventKernelReal, c, a, habs, Complex.ofReal_exp,
      div_eq_mul_inv]

private theorem bddAbove_norm_mathlibResolventKernelC
    (ω : ℝ) (hω : 0 < ω) :
    BddAbove (Set.range fun t => ‖mathlibResolventKernelC ω t‖) := by
  refine ⟨Real.pi / ω, ?_⟩
  rintro y ⟨t, rfl⟩
  have hcoef_nonneg : 0 ≤ Real.pi / ω := by positivity
  have hexp_nonneg : 0 ≤ Real.exp (-(2 * Real.pi * ω) * |t|) := by positivity
  have hexp_le_one : Real.exp (-(2 * Real.pi * ω) * |t|) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (2 * Real.pi * ω) * |t| := by positivity
    linarith
  have hbound :
      (Real.pi / ω) * Real.exp (-(2 * Real.pi * ω) * |t|) ≤ Real.pi / ω := by
    calc
      (Real.pi / ω) * Real.exp (-(2 * Real.pi * ω) * |t|)
        ≤ (Real.pi / ω) * 1 := by
            exact mul_le_mul_of_nonneg_left hexp_le_one hcoef_nonneg
      _ = Real.pi / ω := by ring
  have hnorm :
      ‖mathlibResolventKernelC ω t‖ =
        (Real.pi / ω) * Real.exp (-(2 * Real.pi * ω) * |t|) := by
    rw [mathlibResolventKernelC, mathlibResolventKernelReal, Complex.norm_real]
    apply abs_of_nonneg
    positivity
  change ‖mathlibResolventKernelC ω t‖ ≤ Real.pi / ω
  rw [hnorm]
  exact hbound

private theorem fourier_mathlibResolventKernelC
    (ω : ℝ) (hω : 0 < ω) :
    FourierTransform.fourier (mathlibResolventKernelC ω) =
      fun ξ : ℝ => ((((ξ ^ 2 + ω ^ 2)⁻¹ : ℝ)) : ℂ) := by
  ext ξ
  change FourierTransform.fourier
      (fun t : ℝ => (((Real.pi / ω * Real.exp (-(2 * Real.pi * ω) * |t|) : ℝ)) : ℂ)) ξ =
    ((((ξ ^ 2 + ω ^ 2)⁻¹ : ℝ)) : ℂ)
  simpa using
    fourier_mathlib_resolventKernel ω hω ξ

private def mathlibResolventConvolution (ω : ℝ) (h : SchwartzMap ℝ ℝ) : ℝ → ℂ :=
  MeasureTheory.convolution (mathlibResolventKernelC ω) (schwartzToComplex h)
    (ContinuousLinearMap.mul ℂ ℂ) MeasureTheory.volume

attribute [local instance] SMulCommClass.symm in
private theorem realFourierMultiplier_inverseSymbol_eq_convolution
    (ω : ℝ) (hω : 0 < ω) (h : SchwartzMap ℝ ℝ) :
    schwartzToComplex
      (realFourierMultiplierCLM
        (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
        (resolventInverseSymbol_hasTemperateGrowth ω hω) h) =
      mathlibResolventConvolution ω h := by
  let lhs : SchwartzMap ℝ ℂ :=
    schwartzToComplex
      (realFourierMultiplierCLM
        (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
        (resolventInverseSymbol_hasTemperateGrowth ω hω) h)
  let rhs : ℝ → ℂ := mathlibResolventConvolution ω h
  have hk_cont : Continuous (mathlibResolventKernelC ω) :=
    continuous_mathlibResolventKernelC ω
  have hk_int : Integrable (mathlibResolventKernelC ω) :=
    integrable_mathlibResolventKernelC ω hω
  have hg_cont : Continuous (schwartzToComplex h) := (schwartzToComplex h).continuous
  have hg_int : Integrable (schwartzToComplex h) := (schwartzToComplex h).integrable
  have hrhs_cont : Continuous rhs :=
    (bddAbove_norm_mathlibResolventKernelC ω hω).continuous_convolution_left_of_integrable
      (L := ContinuousLinearMap.mul ℂ ℂ) hk_cont hg_int
  have hrhs_int : Integrable rhs :=
    hk_int.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hg_int
  have hlhs_fourier_eq :
      FourierTransform.fourier (lhs : ℝ → ℂ) =
        FourierTransform.fourier rhs := by
    ext ξ
    unfold rhs mathlibResolventConvolution
    rw [Real.fourier_mul_convolution_eq hk_int hg_int hk_cont hg_cont]
    rw [show FourierTransform.fourier (lhs : ℝ → ℂ) ξ =
        FourierTransform.fourier
          (schwartzToComplex
            (realFourierMultiplierCLM
              (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
              (resolventInverseSymbol_hasTemperateGrowth ω hω) h)) ξ by
      rw [SchwartzMap.fourier_coe]]
    rw [schwartzToComplex_realFourierMultiplier_eq
      (σ := fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
      (hσ := resolventInverseSymbol_hasTemperateGrowth ω hω)
      (heven := resolventInverseSymbol_even ω) h]
    rw [SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq]
    rw [SchwartzMap.smulLeftCLM_apply_apply (resolventInverseSymbol_hasTemperateGrowth ω hω)]
    rw [SchwartzMap.fourier_coe, fourier_mathlibResolventKernelC ω hω]
    change
      ((((ξ ^ 2 + ω ^ 2)⁻¹ : ℝ) : ℂ) *
          FourierTransform.fourier (⇑(schwartzToComplex h)) ξ) =
        (((((ξ ^ 2 + ω ^ 2)⁻¹ : ℝ) : ℂ)) *
          FourierTransform.fourier (⇑(schwartzToComplex h)) ξ)
    rfl
  have hlhs_int : Integrable lhs := lhs.integrable
  have hlhs_fourier_int : Integrable (FourierTransform.fourier (lhs : ℝ → ℂ)) := by
    simpa [SchwartzMap.fourier_coe] using (FourierTransform.fourier lhs).integrable
  have hrhs_fourier_int : Integrable (FourierTransform.fourier rhs) := by
    rw [← hlhs_fourier_eq]
    exact hlhs_fourier_int
  ext t
  have hlhs_inv :
      FourierTransform.fourierInv (FourierTransform.fourier (lhs : ℝ → ℂ)) = (lhs : ℝ → ℂ) :=
    lhs.continuous.fourierInv_fourier_eq hlhs_int hlhs_fourier_int
  have hrhs_inv :
      FourierTransform.fourierInv (FourierTransform.fourier rhs) = rhs :=
    hrhs_cont.fourierInv_fourier_eq hrhs_int hrhs_fourier_int
  calc
    lhs t = FourierTransform.fourierInv (FourierTransform.fourier (lhs : ℝ → ℂ)) t := by
      symm
      exact congrArg (fun f : ℝ → ℂ => f t) hlhs_inv
    _ = FourierTransform.fourierInv (FourierTransform.fourier rhs) t := by
      rw [hlhs_fourier_eq]
    _ = rhs t := by
      exact congrArg (fun f : ℝ → ℂ => f t) hrhs_inv

private theorem realFourierMultiplier_inverseSymbol_apply_eq_integral
    (ω : ℝ) (hω : 0 < ω) (h : SchwartzMap ℝ ℝ) (t : ℝ) :
    realFourierMultiplierCLM
      (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
      (resolventInverseSymbol_hasTemperateGrowth ω hω) h t =
    ∫ s, mathlibResolventKernelReal ω (t - s) * h s := by
  have hconv :=
    congrArg (fun f : ℝ → ℂ => f t)
      (realFourierMultiplier_inverseSymbol_eq_convolution ω hω h)
  change
    ↑((realFourierMultiplierCLM
      (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
      (resolventInverseSymbol_hasTemperateGrowth ω hω) h) t) =
      mathlibResolventConvolution ω h t at hconv
  unfold mathlibResolventConvolution at hconv
  rw [convolution_mul_swap] at hconv
  apply Complex.ofReal_injective
  have hreal :
      ∫ s, mathlibResolventKernelC ω (t - s) * (schwartzToComplex h) s =
        ((∫ s, mathlibResolventKernelReal ω (t - s) * h s : ℝ) : ℂ) := by
    simpa [mathlibResolventKernelC, mathlibResolventKernelReal, schwartzToComplex,
      Complex.ofReal_exp, mul_assoc] using
      (integral_complex_ofReal
        (f := fun s : ℝ => mathlibResolventKernelReal ω (t - s) * h s)
        (μ := MeasureTheory.volume))
  exact hconv.trans hreal

attribute [local instance] SMulCommClass.symm in
private theorem resolventMultiplier_l2Inner_eq_inverseSymbol
    (ω : ℝ) (hω : 0 < ω) (h₁ h₂ : SchwartzMap ℝ ℝ) :
    l2InnerProduct (resolventMultiplierCLM hω h₁)
      (resolventMultiplierCLM hω h₂) =
    l2InnerProduct h₁
      (realFourierMultiplierCLM
        (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
        (resolventInverseSymbol_hasTemperateGrowth ω hω) h₂) := by
  apply Complex.ofRealLI.injective
  let σ : ℝ → ℝ := resolventSymbol ω
  let σInv : ℝ → ℝ := fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹
  let F : SchwartzMap ℝ ℂ := schwartzToComplex h₁
  let G : SchwartzMap ℝ ℂ := schwartzToComplex h₂
  have hMσ_h₁ :
      schwartzToComplex (resolventMultiplierCLM hω h₁) =
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ F := by
    simpa [σ, F, resolventMultiplierCLM] using
      schwartzToComplex_realFourierMultiplier_eq
        (σ := resolventSymbol ω)
        (hσ := resolventSymbol_hasTemperateGrowth ω hω)
        (heven := resolventSymbol_even ω) h₁
  have hMσ_h₂ :
      schwartzToComplex (resolventMultiplierCLM hω h₂) =
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ G := by
    simpa [σ, G, resolventMultiplierCLM] using
      schwartzToComplex_realFourierMultiplier_eq
        (σ := resolventSymbol ω)
        (hσ := resolventSymbol_hasTemperateGrowth ω hω)
        (heven := resolventSymbol_even ω) h₂
  have hMσInv_h₂ :
      schwartzToComplex
          (realFourierMultiplierCLM σInv
            (resolventInverseSymbol_hasTemperateGrowth ω hω) h₂) =
        SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σInv G := by
    simpa [σInv, G] using
      schwartzToComplex_realFourierMultiplier_eq
        (σ := fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
        (hσ := resolventInverseSymbol_hasTemperateGrowth ω hω)
        (heven := resolventInverseSymbol_even ω) h₂
  have hMσ_fourier (f : SchwartzMap ℝ ℂ) :
      FourierTransform.fourier
          (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ f) =
        SchwartzMap.smulLeftCLM ℂ σ (FourierTransform.fourier f) := by
    rw [SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq]
  have hMσInv_fourier (f : SchwartzMap ℝ ℂ) :
      FourierTransform.fourier
          (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σInv f) =
        SchwartzMap.smulLeftCLM ℂ σInv (FourierTransform.fourier f) := by
    rw [SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq]
  calc
    ((l2InnerProduct (resolventMultiplierCLM hω h₁)
        (resolventMultiplierCLM hω h₂) : ℝ) : ℂ)
      =
        (∫ x,
          @inner ℂ ℂ _
            ((SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ F) x)
            ((SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ G) x)) := by
          rw [schwartz_l2InnerProduct_eq_integral_mul]
          rw [← hMσ_h₁, ← hMσ_h₂]
          exact (schwartzToComplex_integral_inner_eq_ofReal_integral_mul
            (resolventMultiplierCLM hω h₁)
            (resolventMultiplierCLM hω h₂)).symm
    _ =
        (∫ ξ,
          @inner ℂ ℂ _
            (FourierTransform.fourier
              (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ F) ξ)
            (FourierTransform.fourier
              (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ G) ξ)) := by
          symm
          simpa using
            SchwartzMap.integral_inner_fourier_fourier
              (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ F)
              (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ G)
    _ =
        (∫ ξ,
          @inner ℂ ℂ _
            (FourierTransform.fourier F ξ)
            (FourierTransform.fourier
              (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σInv G) ξ)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with ξ
          rw [hMσ_fourier, hMσ_fourier, hMσInv_fourier]
          rw [SchwartzMap.smulLeftCLM_apply_apply
              (resolventSymbol_hasTemperateGrowth ω hω)]
          rw [SchwartzMap.smulLeftCLM_apply_apply
              (resolventSymbol_hasTemperateGrowth ω hω)]
          rw [SchwartzMap.smulLeftCLM_apply_apply
              (resolventInverseSymbol_hasTemperateGrowth ω hω)]
          rw [RCLike.inner_apply, RCLike.inner_apply]
          have hs :
              (((resolventSymbol ω ξ : ℝ) : ℂ) * (resolventSymbol ω ξ : ℂ)) =
                ((((ξ ^ 2 + ω ^ 2)⁻¹ : ℝ)) : ℂ) := by
            exact_mod_cast resolventSymbol_mul_self ω hω ξ
          calc
            resolventSymbol ω ξ • (FourierTransform.fourier G ξ) *
                (starRingEnd ℂ) (resolventSymbol ω ξ • (FourierTransform.fourier F ξ))
              = (((resolventSymbol ω ξ : ℝ) : ℂ) *
                    FourierTransform.fourier G ξ) *
                  (((resolventSymbol ω ξ : ℝ) : ℂ) *
                    (starRingEnd ℂ) (FourierTransform.fourier F ξ)) := by
                      simp [mul_comm, mul_left_comm]
            _ = ((((ξ ^ 2 + ω ^ 2)⁻¹ : ℝ)) : ℂ) *
                  (FourierTransform.fourier G ξ *
                    (starRingEnd ℂ) (FourierTransform.fourier F ξ)) := by
                      rw [← hs]
                      ring
            _ = ((((ξ ^ 2 + ω ^ 2)⁻¹ : ℝ)) : ℂ) *
                  FourierTransform.fourier G ξ *
                    (starRingEnd ℂ) (FourierTransform.fourier F ξ) := by
                      ring
            _ = (ξ ^ 2 + ω ^ 2)⁻¹ • (FourierTransform.fourier G) ξ *
                  (starRingEnd ℂ) ((FourierTransform.fourier F) ξ) := by
                      simp
    _ =
        (∫ x,
          @inner ℂ ℂ _ (F x)
            ((SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σInv G) x)) := by
          simpa using
            SchwartzMap.integral_inner_fourier_fourier F
              (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σInv G)
    _ = ((l2InnerProduct h₁
          (realFourierMultiplierCLM σInv
            (resolventInverseSymbol_hasTemperateGrowth ω hω) h₂) : ℝ) : ℂ) := by
          rw [schwartz_l2InnerProduct_eq_integral_mul]
          rw [← hMσInv_h₂]
          simpa [F] using
            schwartzToComplex_integral_inner_eq_ofReal_integral_mul h₁
              (realFourierMultiplierCLM σInv
                (resolventInverseSymbol_hasTemperateGrowth ω hω) h₂)

private theorem resolventMultiplier_l2Inner_eq_inverseSymbol_integral
    (ω : ℝ) (hω : 0 < ω) (h₁ h₂ : SchwartzMap ℝ ℝ) :
    l2InnerProduct (resolventMultiplierCLM hω h₁)
      (resolventMultiplierCLM hω h₂) =
    ∫ t, h₁ t *
      realFourierMultiplierCLM
        (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
        (resolventInverseSymbol_hasTemperateGrowth ω hω) h₂ t := by
  rw [resolventMultiplier_l2Inner_eq_inverseSymbol]
  exact schwartz_l2InnerProduct_eq_integral_mul h₁
    (realFourierMultiplierCLM
      (fun ξ : ℝ => (ξ ^ 2 + ω ^ 2)⁻¹)
      (resolventInverseSymbol_hasTemperateGrowth ω hω) h₂)

private theorem resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integral
    (ω : ℝ) (hω : 0 < ω) (h₁ h₂ : SchwartzMap ℝ ℝ) :
    l2InnerProduct (resolventMultiplierCLM hω h₁)
      (resolventMultiplierCLM hω h₂) =
    ∫ t, h₁ t * (∫ s, mathlibResolventKernelReal ω (t - s) * h₂ s) := by
  rw [resolventMultiplier_l2Inner_eq_inverseSymbol_integral]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [realFourierMultiplier_inverseSymbol_apply_eq_integral ω hω h₂ t]

private theorem schwartz_l2InnerProduct_smul_smul
    (c : ℝ) (f g : SchwartzMap ℝ ℝ) :
    l2InnerProduct (c • f) (c • g) = c ^ 2 * l2InnerProduct f g := by
  rw [schwartz_l2InnerProduct_eq_integral_mul, schwartz_l2InnerProduct_eq_integral_mul]
  have hfg :
      (fun t : ℝ => (c • f) t * (c • g) t) = fun t => c ^ 2 * (f t * g t) := by
    funext t
    simp [smul_eq_mul]
    ring
  rw [hfg, integral_const_mul]

private theorem inv_two_pi_sq_mul_two_pi_sq
    (x : ℝ) :
    (((2 * Real.pi : ℝ)⁻¹) ^ 2) * (((2 * Real.pi) ^ 2) * x) = x := by
  have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp [h2pi_ne]

private def twoPiUnit : ℝˣ :=
  Units.mk0 (2 * Real.pi) (by positivity)

/-- Temporal rescaling `h(t) ↦ √(2π) h(2π t)` converting the analyst-normalized cylinder
resolvent into the physicist-normalized one. -/
private def schwartzTwoPiRescaleCLM :
    SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ :=
  (Real.sqrt (2 * Real.pi : ℝ)) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      ((ContinuousLinearEquiv.unitsEquivAut ℝ) twoPiUnit)

@[simp] private theorem schwartzTwoPiRescaleCLM_apply
    (h : SchwartzMap ℝ ℝ) (t : ℝ) :
    schwartzTwoPiRescaleCLM h t =
      Real.sqrt (2 * Real.pi) * h (2 * Real.pi * t) := by
  simp [schwartzTwoPiRescaleCLM, twoPiUnit, mul_comm, mul_assoc]

private theorem sq_mul_freeKernel_mul_eq_mul_freeKernel_comp_mul
    {a ω x : ℝ} (ha : 0 < a) (hω : 0 < ω) :
    a ^ 2 * freeKernel (a * ω) x = a * freeKernel ω (a * x) := by
  unfold freeKernel
  rw [abs_mul, abs_of_nonneg ha.le]
  rw [show -ω * (a * |x|) = -(a * ω) * |x| by ring]
  calc
    a ^ 2 * (Real.exp (-(a * ω) * |x|) / (2 * (a * ω)))
      = (a ^ 2 / (2 * (a * ω))) * Real.exp (-(a * ω) * |x|) := by ring
    _ = (a / (2 * ω)) * Real.exp (-(a * ω) * |x|) := by
          field_simp [ha.ne', hω.ne']
    _ = a * (Real.exp (-(a * ω) * |x|) / (2 * ω)) := by ring

private theorem scaledFreeKernel_integral_eq_freeKernel_integral_of_twoPiRescale
    (ω : ℝ) (hω : 0 < ω) (h₁ h₂ : SchwartzMap ℝ ℝ) :
    ∫ t, schwartzTwoPiRescaleCLM h₁ t *
      (∫ s, (((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s)) *
        schwartzTwoPiRescaleCLM h₂ s) =
    ∫ t, h₁ t * (∫ s, freeKernel ω (t - s) * h₂ s) := by
  let a : ℝ := 2 * Real.pi
  let c : ℝ := Real.sqrt a
  let J : ℝ → ℝ := fun u => ∫ s, freeKernel ω (u - s) * h₂ s
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have ha_ne : a ≠ 0 := ha_pos.ne'
  have hc_sq : c ^ 2 = a := by
    dsimp [c]
    nlinarith [Real.sq_sqrt (show 0 ≤ a by positivity)]
  have hinner : ∀ t,
      (∫ s, (((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s)) *
          schwartzTwoPiRescaleCLM h₂ s) =
        c * J (a * t) := by
    intro t
    have hstep1 :
        ∫ s, (((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s)) *
            schwartzTwoPiRescaleCLM h₂ s =
          ∫ s, (a * freeKernel ω (a * (t - s))) * (c * h₂ (a * s)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with s
      rw [schwartzTwoPiRescaleCLM_apply]
      rw [show ((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s) =
        a * freeKernel ω (a * (t - s)) by
        simpa [a] using
          sq_mul_freeKernel_mul_eq_mul_freeKernel_comp_mul
            (a := a) (ω := ω) (x := t - s) ha_pos hω]
    have hstep2 :
        ∫ s, (a * freeKernel ω (a * (t - s))) * (c * h₂ (a * s)) =
          ∫ s, a * c * (freeKernel ω (a * t - a * s) * h₂ (a * s)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with s
      rw [show a * (t - s) = a * t - a * s by ring]
      ring_nf
    have hstep3 :
        ∫ s, a * c * (freeKernel ω (a * t - a * s) * h₂ (a * s)) =
          a * c * ∫ s, (fun u : ℝ => freeKernel ω (a * t - u) * h₂ u) (a * s) := by
      rw [MeasureTheory.integral_const_mul]
    have hcomp :
        ∫ s, (fun u : ℝ => freeKernel ω (a * t - u) * h₂ u) (a * s) =
          |a⁻¹| * ∫ u, freeKernel ω (a * t - u) * h₂ u := by
      simpa [smul_eq_mul] using
        (Measure.integral_comp_mul_left
          (g := fun u : ℝ => freeKernel ω (a * t - u) * h₂ u) (a := a))
    calc
      ∫ s, (((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s)) *
          schwartzTwoPiRescaleCLM h₂ s
        = ∫ s, (a * freeKernel ω (a * (t - s))) * (c * h₂ (a * s)) := hstep1
      _ = ∫ s, a * c * (freeKernel ω (a * t - a * s) * h₂ (a * s)) := by
            exact hstep2
      _ = a * c * ∫ s, (fun u : ℝ => freeKernel ω (a * t - u) * h₂ u) (a * s) := hstep3
      _ = a * c * (|a⁻¹| * ∫ u, freeKernel ω (a * t - u) * h₂ u) := by rw [hcomp]
      _ = c * J (a * t) := by
            dsimp [J]
            rw [abs_of_pos (inv_pos.mpr ha_pos)]
            rw [show a * c * (a⁻¹ * ∫ u, freeKernel ω (a * t - u) * h₂ u) =
              c * (a * a⁻¹) * ∫ u, freeKernel ω (a * t - u) * h₂ u by ring]
            simp [ha_ne]
  have hout1 :
      ∫ t, schwartzTwoPiRescaleCLM h₁ t *
        (∫ s, (((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s)) *
          schwartzTwoPiRescaleCLM h₂ s) =
      ∫ t, (c * h₁ (a * t)) * (c * J (a * t)) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [schwartzTwoPiRescaleCLM_apply, hinner t]
  have hmul :
      (fun t : ℝ => (c * h₁ (a * t)) * (c * J (a * t))) =
        fun t : ℝ => c ^ 2 * ((fun u : ℝ => h₁ u * J u) (a * t)) := by
    funext t
    ring_nf
  have hout2 :
      ∫ t, (c * h₁ (a * t)) * (c * J (a * t)) =
        c ^ 2 * ∫ t, (fun u : ℝ => h₁ u * J u) (a * t) := by
    rw [hmul, MeasureTheory.integral_const_mul]
  have houtComp :
      ∫ t, (fun u : ℝ => h₁ u * J u) (a * t) =
        |a⁻¹| * ∫ u, h₁ u * J u := by
    simpa [smul_eq_mul] using
      (Measure.integral_comp_mul_left (g := fun u : ℝ => h₁ u * J u) (a := a))
  calc
    ∫ t, schwartzTwoPiRescaleCLM h₁ t *
      (∫ s, (((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s)) *
        schwartzTwoPiRescaleCLM h₂ s)
      = ∫ t, (c * h₁ (a * t)) * (c * J (a * t)) := hout1
    _ = c ^ 2 * ∫ t, (fun u : ℝ => h₁ u * J u) (a * t) := hout2
    _ = c ^ 2 * (|a⁻¹| * ∫ u, h₁ u * J u) := by rw [houtComp]
    _ = ∫ u, h₁ u * J u := by
          rw [hc_sq, abs_of_pos (inv_pos.mpr ha_pos)]
          rw [show a * (a⁻¹ * ∫ u, h₁ u * J u) = (a * a⁻¹) * ∫ u, h₁ u * J u by ring]
          simp [ha_ne]
    _ = ∫ t, h₁ t * (∫ s, freeKernel ω (t - s) * h₂ s) := by
          rfl

private def physicalResolventMultiplierCLM
    (ω : ℝ) (hω : 0 < ω) :
    SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ :=
  let hω' : 0 < ω / (2 * Real.pi) := by
    have h2pi_pos : 0 < (2 * Real.pi : ℝ) := by positivity
    exact div_pos hω h2pi_pos
  ((2 * Real.pi : ℝ)⁻¹) • resolventMultiplierCLM hω'

private theorem physicalResolventMultiplier_l2Inner_eq_freeKernel_integral
    (ω : ℝ) (hω : 0 < ω) (h₁ h₂ : SchwartzMap ℝ ℝ) :
    l2InnerProduct (physicalResolventMultiplierCLM ω hω h₁)
      (physicalResolventMultiplierCLM ω hω h₂) =
    ∫ t, h₁ t * (∫ s, freeKernel ω (t - s) * h₂ s) := by
  let c : ℝ := (2 * Real.pi : ℝ)⁻¹
  let ω' : ℝ := ω / (2 * Real.pi)
  have hω' : 0 < ω' := by
    dsimp [ω']
    have h2pi_pos : 0 < (2 * Real.pi : ℝ) := by positivity
    exact div_pos hω h2pi_pos
  have hfreq : 2 * Real.pi * ω' = ω := by
    dsimp [ω']
    field_simp [Real.pi_ne_zero]
  calc
    l2InnerProduct (physicalResolventMultiplierCLM ω hω h₁)
        (physicalResolventMultiplierCLM ω hω h₂)
      = c ^ 2 * l2InnerProduct (resolventMultiplierCLM hω' h₁)
          (resolventMultiplierCLM hω' h₂) := by
            simpa [physicalResolventMultiplierCLM, c, ω', hω'] using
              schwartz_l2InnerProduct_smul_smul c
                (resolventMultiplierCLM hω' h₁)
                (resolventMultiplierCLM hω' h₂)
    _ = c ^ 2 * ∫ t, h₁ t *
          (∫ s, mathlibResolventKernelReal ω' (t - s) * h₂ s) := by
            rw [resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integral]
    _ = ∫ t, h₁ t * (∫ s, freeKernel ω (t - s) * h₂ s) := by
          rw [← integral_const_mul]
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          calc
            c ^ 2 * (h₁ t * ∫ s, mathlibResolventKernelReal ω' (t - s) * h₂ s)
              = h₁ t * (c ^ 2 * ∫ s, mathlibResolventKernelReal ω' (t - s) * h₂ s) := by
                  ring
            _ = h₁ t * (∫ s, c ^ 2 *
                  (mathlibResolventKernelReal ω' (t - s) * h₂ s)) := by
                  rw [← integral_const_mul]
            _ = h₁ t * (∫ s, freeKernel ω (t - s) * h₂ s) := by
                  congr 1
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards with s
                  rw [show c ^ 2 *
                    (mathlibResolventKernelReal ω' (t - s) * h₂ s) =
                      (c ^ 2 * mathlibResolventKernelReal ω' (t - s)) * h₂ s by
                    ring]
                  rw [show mathlibResolventKernelReal ω' (t - s) =
                    ((2 * Real.pi) ^ 2) * freeKernel ω (t - s) by
                    simpa [mathlibResolventKernelReal, hfreq] using
                      PeriodicResolvent1D.mathlibResolventKernel_eq_scaled_freeKernel
                        ω' hω' (t - s)]
                  rw [inv_two_pi_sq_mul_two_pi_sq]

private theorem resolventMultiplier_l2Inner_eq_scaledFreeKernel_integral
    (ω : ℝ) (hω : 0 < ω) (h₁ h₂ : SchwartzMap ℝ ℝ) :
    l2InnerProduct (resolventMultiplierCLM hω h₁)
      (resolventMultiplierCLM hω h₂) =
    ∫ t, h₁ t *
      (∫ s, (((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s)) * h₂ s) := by
  rw [resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integral]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  refine congrArg (fun z : ℝ => h₁ t * z) ?_
  apply MeasureTheory.integral_congr_ae
  filter_upwards with s
  rw [show
    mathlibResolventKernelReal ω (t - s) =
      ((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (t - s) by
    simpa [mathlibResolventKernelReal] using
      PeriodicResolvent1D.mathlibResolventKernel_eq_scaled_freeKernel ω hω (t - s)]

private theorem resolventMultiplier_l2Inner_eq_physical_after_twoPiRescale
    (ω : ℝ) (hω : 0 < ω) (h₁ h₂ : SchwartzMap ℝ ℝ) :
    l2InnerProduct (resolventMultiplierCLM hω (schwartzTwoPiRescaleCLM h₁))
      (resolventMultiplierCLM hω (schwartzTwoPiRescaleCLM h₂)) =
    l2InnerProduct (physicalResolventMultiplierCLM ω hω h₁)
      (physicalResolventMultiplierCLM ω hω h₂) := by
  rw [resolventMultiplier_l2Inner_eq_scaledFreeKernel_integral,
    physicalResolventMultiplier_l2Inner_eq_freeKernel_integral]
  exact scaledFreeKernel_integral_eq_freeKernel_integral_of_twoPiRescale ω hω h₁ h₂

private theorem resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integralOn_compactDiffBox
    (ω : ℝ) (hω : 0 < ω)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0) :
    l2InnerProduct (resolventMultiplierCLM hω h₁)
      (resolventMultiplierCLM hω h₂) =
    ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
      (h₁ p.1 * h₂ p.2) * mathlibResolventKernelReal ω (p.1 - p.2) ∂volume := by
  let I : Set ℝ := Set.Icc (-T) T
  let K : Set (ℝ × ℝ) := I ×ˢ I
  let F : ℝ → ℝ := fun t => ∫ s, mathlibResolventKernelReal ω (t - s) * h₂ s
  let G : ℝ × ℝ → ℝ := fun p =>
    (h₁ p.1 * h₂ p.2) * mathlibResolventKernelReal ω (p.1 - p.2)
  have houter :
      ∫ t, h₁ t * F t = ∫ t in I, h₁ t * F t := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ I
    · simp [I, ht]
    · have hTlt : T < |t| := by
        apply lt_of_not_ge
        intro ht'
        apply ht
        simpa [I, Set.mem_Icc, abs_le] using ht'
      have hz : h₁ t = 0 := hsupp₁ t hTlt
      simp [I, ht, hz]
  have hinner :
      ∀ t, F t = ∫ s in I, mathlibResolventKernelReal ω (t - s) * h₂ s := by
    intro t
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with s
    by_cases hs : s ∈ I
    · simp [I, hs]
    · have hTlt : T < |s| := by
        apply lt_of_not_ge
        intro hs'
        apply hs
        simpa [I, Set.mem_Icc, abs_le] using hs'
      have hz : h₂ s = 0 := hsupp₂ s hTlt
      simp [I, hs, hz]
  have hiter :
      ∫ t in I, h₁ t * F t =
        ∫ t in I, ∫ s in I, (h₁ t * h₂ s) * mathlibResolventKernelReal ω (t - s) ∂volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hinner t, ← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    ring
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hG_cont : ContinuousOn G K := by
    have hh₁ : ContinuousOn (fun p : ℝ × ℝ => h₁ p.1) K := by
      exact (h₁.continuous.comp continuous_fst).continuousOn
    have hh₂ : ContinuousOn (fun p : ℝ × ℝ => h₂ p.2) K := by
      exact (h₂.continuous.comp continuous_snd).continuousOn
    have hk : ContinuousOn (fun p : ℝ × ℝ => mathlibResolventKernelReal ω (p.1 - p.2)) K := by
      exact ((continuous_mathlibResolventKernelReal ω).comp
        (continuous_fst.sub continuous_snd)).continuousOn
    simpa [G] using (hh₁.mul hh₂).mul hk
  have hG_int :
      Integrable G ((volume.restrict I).prod (volume.restrict I)) := by
    rw [Measure.prod_restrict I I]
    simpa [K] using hG_cont.integrableOn_compact hK_compact
  calc
    l2InnerProduct (resolventMultiplierCLM hω h₁)
        (resolventMultiplierCLM hω h₂)
      = ∫ t, h₁ t * F t := by
          simpa [F] using
            resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integral ω hω h₁ h₂
    _ = ∫ t in I, h₁ t * F t := houter
    _ = ∫ t in I, ∫ s in I, (h₁ t * h₂ s) * mathlibResolventKernelReal ω (t - s) ∂volume := hiter
    _ = ∫ p, G p ∂((volume.restrict I).prod (volume.restrict I)) := by
          simpa [G] using (MeasureTheory.integral_prod G hG_int).symm
    _ = ∫ p in K, G p ∂volume := by
          rw [Measure.prod_restrict I I]
          have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume := rfl
          simp [K, hvol]
    _ = ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          (h₁ p.1 * h₂ p.2) * mathlibResolventKernelReal ω (p.1 - p.2) ∂volume := by
          simp [I, K, G]

private theorem resolventMultiplier_l2Inner_eq_scaledFreeKernel_integralOn_compactDiffBox
    (ω : ℝ) (hω : 0 < ω)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0) :
    l2InnerProduct (resolventMultiplierCLM hω h₁)
      (resolventMultiplierCLM hω h₂) =
    ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
      (h₁ p.1 * h₂ p.2) *
        (((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (p.1 - p.2)) ∂volume := by
  rw [resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integralOn_compactDiffBox
    (ω := ω) (hω := hω) (h₁ := h₁) (h₂ := h₂) (T := T) hsupp₁ hsupp₂]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with p
  rw [show
    mathlibResolventKernelReal ω (p.1 - p.2) =
      ((2 * Real.pi) ^ 2) * freeKernel (2 * Real.pi * ω) (p.1 - p.2) by
    simpa [mathlibResolventKernelReal] using
      PeriodicResolvent1D.mathlibResolventKernel_eq_scaled_freeKernel ω hω (p.1 - p.2)]

private theorem physicalResolventMultiplier_l2Inner_eq_freeKernel_integralOn_compactDiffBox
    (ω : ℝ) (hω : 0 < ω)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0) :
    l2InnerProduct (physicalResolventMultiplierCLM ω hω h₁)
      (physicalResolventMultiplierCLM ω hω h₂) =
    ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
      (h₁ p.1 * h₂ p.2) * freeKernel ω (p.1 - p.2) ∂volume := by
  let c : ℝ := (2 * Real.pi : ℝ)⁻¹
  let ω' : ℝ := ω / (2 * Real.pi)
  let K : Set (ℝ × ℝ) := Set.Icc (-T) T ×ˢ Set.Icc (-T) T
  have hω' : 0 < ω' := by
    dsimp [ω']
    have h2pi_pos : 0 < (2 * Real.pi : ℝ) := by positivity
    exact div_pos hω h2pi_pos
  have hfreq : 2 * Real.pi * ω' = ω := by
    dsimp [ω']
    field_simp [Real.pi_ne_zero]
  calc
    l2InnerProduct (physicalResolventMultiplierCLM ω hω h₁)
        (physicalResolventMultiplierCLM ω hω h₂)
      = c ^ 2 * l2InnerProduct (resolventMultiplierCLM hω' h₁)
          (resolventMultiplierCLM hω' h₂) := by
            simpa [physicalResolventMultiplierCLM, c, ω', hω'] using
              schwartz_l2InnerProduct_smul_smul c
                (resolventMultiplierCLM hω' h₁)
                (resolventMultiplierCLM hω' h₂)
    _ = c ^ 2 * ∫ p in K,
          (h₁ p.1 * h₂ p.2) *
            (((2 * Real.pi) ^ 2) * freeKernel ω (p.1 - p.2)) ∂volume := by
            simpa [c, ω', hfreq, K] using
              resolventMultiplier_l2Inner_eq_scaledFreeKernel_integralOn_compactDiffBox
                (ω := ω') (hω := hω') (h₁ := h₁) (h₂ := h₂)
                (T := T) hsupp₁ hsupp₂
    _ = ∫ p in K, (h₁ p.1 * h₂ p.2) * freeKernel ω (p.1 - p.2) ∂volume := by
          rw [← integral_const_mul]
          apply MeasureTheory.integral_congr_ae
          filter_upwards with p
          rw [show c ^ 2 *
            ((h₁ p.1 * h₂ p.2) * (((2 * Real.pi) ^ 2) * freeKernel ω (p.1 - p.2))) =
              (h₁ p.1 * h₂ p.2) * (c ^ 2 * (((2 * Real.pi) ^ 2) * freeKernel ω (p.1 - p.2))) by
            ring]
          rw [inv_two_pi_sq_mul_two_pi_sq]
    _ = ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          (h₁ p.1 * h₂ p.2) * freeKernel ω (p.1 - p.2) ∂volume := by
          simp [K]

private theorem resolventMultiplier_l2Inner_eq_comp_apply
    (ω : ℝ) (hω : 0 < ω) (h₁ h₂ : SchwartzMap ℝ ℝ) :
    l2InnerProduct (resolventMultiplierCLM hω h₁)
      (resolventMultiplierCLM hω h₂) =
    ∫ t, h₁ t * resolventMultiplierCLM hω (resolventMultiplierCLM hω h₂) t := by
  rw [resolventMultiplier_l2Inner_eq_inverseSymbol_integral]
  congr with t
  rw [congrArg (fun f : SchwartzMap ℝ ℝ => f t)
    (resolventMultiplierCLM_comp_apply_eq_inverseSymbol ω hω h₂)]

/-- The asymmetric torus Green form on pure tensors is the expected double mode sum. -/
theorem asymTorusContinuumGreen_pure_eq_tsum
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (fₜ gₜ : SmoothMap_Circle Lt ℝ)
    (fₓ gₓ : SmoothMap_Circle Ls ℝ) :
    asymTorusContinuumGreen Lt Ls mass hmass
      (NuclearTensorProduct.pure fₜ fₓ)
      (NuclearTensorProduct.pure gₜ gₓ) =
    ∑' p : ℕ × ℕ,
      DyninMityaginSpace.coeff p.1 fₜ *
        DyninMityaginSpace.coeff p.1 gₜ *
        DyninMityaginSpace.coeff p.2 fₓ *
        DyninMityaginSpace.coeff p.2 gₓ /
        (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) p.1 +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) p.2 +
          mass ^ 2) := by
  change ∑' m, DyninMityaginSpace.coeff m (NuclearTensorProduct.pure fₜ fₓ) *
        DyninMityaginSpace.coeff m (NuclearTensorProduct.pure gₜ gₓ) /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle Lt ℝ) (SmoothMap_Circle Ls ℝ)) m +
          mass ^ 2) =
      ∑' p : ℕ × ℕ,
        DyninMityaginSpace.coeff p.1 fₜ *
          DyninMityaginSpace.coeff p.1 gₜ *
          DyninMityaginSpace.coeff p.2 fₓ *
          DyninMityaginSpace.coeff p.2 gₓ /
          (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) p.1 +
            HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) p.2 +
            mass ^ 2)
  have h_term : ∀ m : ℕ,
      DyninMityaginSpace.coeff m (NuclearTensorProduct.pure fₜ fₓ) *
        DyninMityaginSpace.coeff m (NuclearTensorProduct.pure gₜ gₓ) /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle Lt ℝ) (SmoothMap_Circle Ls ℝ)) m +
          mass ^ 2) =
      DyninMityaginSpace.coeff (Nat.unpair m).1 fₜ *
        DyninMityaginSpace.coeff (Nat.unpair m).1 gₜ *
        DyninMityaginSpace.coeff (Nat.unpair m).2 fₓ *
        DyninMityaginSpace.coeff (Nat.unpair m).2 gₓ /
        (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (Nat.unpair m).1 +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) (Nat.unpair m).2 +
          mass ^ 2) := by
    intro m
    change (NuclearTensorProduct.pure fₜ fₓ).val m *
        (NuclearTensorProduct.pure gₜ gₓ).val m /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle Lt ℝ) (SmoothMap_Circle Ls ℝ)) m +
          mass ^ 2) =
      DyninMityaginSpace.coeff (Nat.unpair m).1 fₜ *
        DyninMityaginSpace.coeff (Nat.unpair m).1 gₜ *
        DyninMityaginSpace.coeff (Nat.unpair m).2 fₓ *
        DyninMityaginSpace.coeff (Nat.unpair m).2 gₓ /
        (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (Nat.unpair m).1 +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) (Nat.unpair m).2 +
          mass ^ 2)
    have ev_ntp := fun (n : ℕ) =>
      show HasLaplacianEigenvalues.eigenvalue
        (E := NuclearTensorProduct (SmoothMap_Circle Lt ℝ) (SmoothMap_Circle Ls ℝ)) n =
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (Nat.unpair n).1 +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) (Nat.unpair n).2 from
        rfl
    simp only [NuclearTensorProduct.pure_val, ev_ntp]
    ring
  simp_rw [h_term, ← Nat.pairEquiv_symm_apply]
  exact Nat.pairEquiv.symm.tsum_eq
    (fun p : ℕ × ℕ =>
      DyninMityaginSpace.coeff p.1 fₜ *
        DyninMityaginSpace.coeff p.1 gₜ *
        DyninMityaginSpace.coeff p.2 fₓ *
        DyninMityaginSpace.coeff p.2 gₓ /
        (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) p.1 +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) p.2 +
          mass ^ 2))

/-- For pure cylinder tensors, the torus Green form of the embedded test functions is exactly
the asymmetric-torus spectral sum with periodized temporal factor. -/
theorem asymTorusContinuumGreen_embed_pure_eq_tsum
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) :
    asymTorusContinuumGreen Lt Ls mass hmass
      (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₁ h₁))
      (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₂ h₂)) =
    ∑' p : ℕ × ℕ,
      DyninMityaginSpace.coeff p.1 (periodizeCLM Lt h₁) *
        DyninMityaginSpace.coeff p.1 (periodizeCLM Lt h₂) *
        DyninMityaginSpace.coeff p.2 g₁ *
        DyninMityaginSpace.coeff p.2 g₂ /
        (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) p.1 +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) p.2 +
          mass ^ 2) := by
  rw [cylinderToTorusEmbed_pure, cylinderToTorusEmbed_pure]
  simpa using
    asymTorusContinuumGreen_pure_eq_tsum (Ls := Ls) (Lt := Lt) mass hmass
      (periodizeCLM Lt h₁) (periodizeCLM Lt h₂) g₁ g₂

/-- The embedded pure torus covariance decomposes into a spatial mode sum whose temporal factor is
the one-dimensional circle Green form with mass `ω_a = resolventFreq Ls mass a`. This is the torus
counterpart of `cylinderGreen_pure_eq_tsum_l2Inner` and isolates the remaining genuinely 1D bridge
to the explicit periodic kernel. -/
private theorem asymTorusContinuumGreen_embed_pure_eq_tsum_temporalGreen
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) :
    asymTorusContinuumGreen Lt Ls mass hmass
      (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₁ h₁))
      (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₂ h₂)) =
    ∑' a : ℕ,
      DyninMityaginSpace.coeff a g₁ *
        DyninMityaginSpace.coeff a g₂ *
        greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ)
          (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a)
          (periodizeCLM Lt h₁) (periodizeCLM Lt h₂) := by
  let ht₁ : SmoothMap_Circle Lt ℝ := periodizeCLM Lt h₁
  let ht₂ : SmoothMap_Circle Lt ℝ := periodizeCLM Lt h₂
  let raw : ℕ → ℕ → ℝ := fun b a =>
    DyninMityaginSpace.coeff b ht₁ *
      DyninMityaginSpace.coeff b ht₂ *
      (DyninMityaginSpace.coeff a g₁ *
          DyninMityaginSpace.coeff a g₂ /
        (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) b +
          resolventFreq Ls mass a ^ 2))
  have hraw_eq :
      asymTorusContinuumGreen Lt Ls mass hmass
        (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₁ h₁))
        (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₂ h₂)) =
      ∑' p : ℕ × ℕ, Function.uncurry raw p := by
    rw [asymTorusContinuumGreen_embed_pure_eq_tsum (Ls := Ls) (Lt := Lt)
      (mass := mass) (hmass := hmass) (g₁ := g₁) (g₂ := g₂) (h₁ := h₁) (h₂ := h₂)]
    apply tsum_congr
    rintro ⟨b, a⟩
    simp only [raw, ht₁, ht₂, Function.uncurry_apply_pair]
    have hden :
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) b +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) a + mass ^ 2 =
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) b +
          resolventFreq Ls mass a ^ 2 := by
      rw [resolventFreq_sq (L := Ls) mass a]
      simp [HasLaplacianEigenvalues.eigenvalue, add_left_comm, add_comm]
    rw [hden]
    ring_nf
  have hraw_nat :
      Summable (fun m : ℕ => Function.uncurry raw (Nat.pairEquiv.symm m)) := by
    let f : AsymTorusTestFunction Lt Ls :=
      cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₁ h₁)
    let g : AsymTorusTestFunction Lt Ls :=
      cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₂ h₂)
    have hsum :
        Summable (fun m : ℕ =>
          DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g /
            (HasLaplacianEigenvalues.eigenvalue
              (E := AsymTorusTestFunction Lt Ls) m + mass ^ 2)) := by
      refine
        (greenFunctionBilinear_summable (E := AsymTorusTestFunction Lt Ls) mass hmass f g).congr ?_
      intro m
      symm
      exact greenFunctionBilinear_eq_heatKernel
        (E := AsymTorusTestFunction Lt Ls) mass hmass f g m
    refine hsum.congr ?_
    intro m
    have ev_ntp :
        HasLaplacianEigenvalues.eigenvalue
          (E := AsymTorusTestFunction Lt Ls) m =
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (Nat.unpair m).1 +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) (Nat.unpair m).2 := rfl
    have hden :
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (Nat.unpair m).1 +
          HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) (Nat.unpair m).2 +
          mass ^ 2 =
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (Nat.unpair m).1 +
          resolventFreq Ls mass (Nat.unpair m).2 ^ 2 := by
      rw [resolventFreq_sq (L := Ls) mass (Nat.unpair m).2]
      simp [HasLaplacianEigenvalues.eigenvalue, add_left_comm, add_comm]
    simp only [f, g, Nat.pairEquiv_symm_apply, cylinderToTorusEmbed_pure, ev_ntp]
    rw [hden]
    change (NuclearTensorProduct.pure ht₁ g₁).val m *
        (NuclearTensorProduct.pure ht₂ g₂).val m *
        (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (Nat.unpair m).1 +
          resolventFreq Ls mass (Nat.unpair m).2 ^ 2)⁻¹ =
      Function.uncurry raw (Nat.unpair m)
    simp [raw, ht₁, ht₂, Function.uncurry, NuclearTensorProduct.pure_val]
    ring_nf
  have hraw_summable : Summable (Function.uncurry raw) :=
    Nat.pairEquiv.symm.summable_iff.mp hraw_nat
  calc
    asymTorusContinuumGreen Lt Ls mass hmass
        (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₁ h₁))
        (cylinderToTorusEmbed Lt Ls (NuclearTensorProduct.pure g₂ h₂))
      = ∑' p : ℕ × ℕ, Function.uncurry raw p := hraw_eq
    _ = ∑' b : ℕ, ∑' a : ℕ, raw b a := by
          exact hraw_summable.tsum_prod_uncurry (fun b => hraw_summable.prod_factor b)
    _ = ∑' a : ℕ, ∑' b : ℕ, raw b a := by
          symm
          exact hraw_summable.tsum_comm
    _ = ∑' a : ℕ,
          DyninMityaginSpace.coeff a g₁ *
            DyninMityaginSpace.coeff a g₂ *
            greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ)
              (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a)
              (periodizeCLM Lt h₁) (periodizeCLM Lt h₂) := by
          apply tsum_congr
          intro a
          let c : ℝ := DyninMityaginSpace.coeff a g₁ * DyninMityaginSpace.coeff a g₂
          let temp : ℕ → ℝ := fun b =>
            DyninMityaginSpace.coeff b ht₁ *
              DyninMityaginSpace.coeff b ht₂ /
              (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) b +
                resolventFreq Ls mass a ^ 2)
          have htemp_summable : Summable temp := by
            refine
              (greenFunctionBilinear_summable (E := SmoothMap_Circle Lt ℝ)
                (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a) ht₁ ht₂).congr ?_
            intro b
            symm
            exact greenFunctionBilinear_eq_heatKernel
              (E := SmoothMap_Circle Lt ℝ) (resolventFreq Ls mass a)
              (resolventFreq_pos Ls mass hmass a) ht₁ ht₂ b
          have htemp_eq :
              greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ)
                (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a) ht₁ ht₂ =
              ∑' b : ℕ, temp b := by
            unfold greenFunctionBilinear
            apply tsum_congr
            intro b
            exact greenFunctionBilinear_eq_heatKernel
              (E := SmoothMap_Circle Lt ℝ) (resolventFreq Ls mass a)
              (resolventFreq_pos Ls mass hmass a) ht₁ ht₂ b
          calc
            (∑' b : ℕ, raw b a)
              = ∑' b : ℕ, c * temp b := by
                  apply tsum_congr
                  intro b
                  simp [raw, c, temp]
                  ring_nf
            _ = c * ∑' b : ℕ, temp b := by
                  exact htemp_summable.tsum_mul_left c
            _ = c * greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ)
                  (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a) ht₁ ht₂ := by
                  rw [htemp_eq]
            _ = DyninMityaginSpace.coeff a g₁ *
                  DyninMityaginSpace.coeff a g₂ *
                  greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ)
                    (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a) ht₁ ht₂ := by
                  simp [c]

/-- The cylinder Green form on pure tensors expands as a double sum of spatial coefficients
and transformed temporal coefficients. This isolates the remaining bridge to the explicit
free resolvent kernel in the pure-tensor case. -/
theorem cylinderGreen_pure_eq_tsum
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) :
    cylinderGreen Ls mass hmass
      (NuclearTensorProduct.pure g₁ h₁)
      (NuclearTensorProduct.pure g₂ h₂) =
    ∑' p : ℕ × ℕ,
      (DyninMityaginSpace.coeff p.1 g₁ *
          DyninMityaginSpace.coeff p.2
            (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass p.1) h₁)) *
        (DyninMityaginSpace.coeff p.1 g₂ *
          DyninMityaginSpace.coeff p.2
            (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass p.1) h₂)) := by
  rw [cylinderMassOperator_inner, ell2_inner_eq_tsum]
  have h_term : ∀ m : ℕ,
      @inner ℝ ℝ _
          (((cylinderMassOperator Ls mass hmass
              (NuclearTensorProduct.pure g₁ h₁)) : ell2') m)
          (((cylinderMassOperator Ls mass hmass
              (NuclearTensorProduct.pure g₂ h₂)) : ell2') m) =
      (DyninMityaginSpace.coeff (Nat.unpair m).1 g₁ *
          DyninMityaginSpace.coeff (Nat.unpair m).2
            (resolventMultiplierCLM
              (resolventFreq_pos Ls mass hmass (Nat.unpair m).1) h₁)) *
        (DyninMityaginSpace.coeff (Nat.unpair m).1 g₂ *
          DyninMityaginSpace.coeff (Nat.unpair m).2
            (resolventMultiplierCLM
              (resolventFreq_pos Ls mass hmass (Nat.unpair m).1) h₂)) := by
    intro m
    rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
    rw [cylinderMassOperator_formula, cylinderMassOperator_formula]
    simp only [ntpSliceSchwartz_pure, map_smul, smul_eq_mul]
    ring
  simp_rw [h_term, ← Nat.pairEquiv_symm_apply]
  exact Nat.pairEquiv.symm.tsum_eq
    (fun p : ℕ × ℕ =>
      (DyninMityaginSpace.coeff p.1 g₁ *
          DyninMityaginSpace.coeff p.2
            (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass p.1) h₁)) *
        (DyninMityaginSpace.coeff p.1 g₂ *
          DyninMityaginSpace.coeff p.2
            (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass p.1) h₂)))

/-- The pure-tensor cylinder Green form decomposes into a spatial mode sum whose temporal factor
is the `l2InnerProduct` of the corresponding resolvent-transformed Schwartz functions. -/
theorem cylinderGreen_pure_eq_tsum_l2Inner
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) :
    cylinderGreen Ls mass hmass
      (NuclearTensorProduct.pure g₁ h₁)
      (NuclearTensorProduct.pure g₂ h₂) =
    ∑' a : ℕ,
      DyninMityaginSpace.coeff a g₁ *
        DyninMityaginSpace.coeff a g₂ *
        l2InnerProduct
          (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass a) h₁)
          (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass a) h₂) := by
  let pure₁ : CylinderTestFunction Ls := NuclearTensorProduct.pure g₁ h₁
  let pure₂ : CylinderTestFunction Ls := NuclearTensorProduct.pure g₂ h₂
  let fpair : ℕ × ℕ → ℝ := fun p =>
    (DyninMityaginSpace.coeff p.1 g₁ *
        DyninMityaginSpace.coeff p.2
          (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass p.1) h₁)) *
      (DyninMityaginSpace.coeff p.1 g₂ *
        DyninMityaginSpace.coeff p.2
          (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass p.1) h₂))
  have hpair_eq :
      cylinderGreen Ls mass hmass pure₁ pure₂ = ∑' p : ℕ × ℕ, fpair p := by
    simpa [pure₁, pure₂, fpair] using
      cylinderGreen_pure_eq_tsum (Ls := Ls) mass hmass g₁ g₂ h₁ h₂
  have hpair_summable : Summable fpair := by
    let x : ell2' := cylinderMassOperator Ls mass hmass pure₁
    let y : ell2' := cylinderMassOperator Ls mass hmass pure₂
    have hxy : Summable (fun m : ℕ => @inner ℝ _ _ (x m) (y m)) := by
      simpa [x, y] using lp.summable_inner x y
    have hpair_nat :
        Summable (fun m : ℕ => fpair (Nat.pairEquiv.symm m)) := by
      refine hxy.congr ?_
      intro m
      simp only [fpair, x, y, pure₁, pure₂, cylinderMassOperator_formula,
        ntpSliceSchwartz_pure, Nat.pairEquiv_symm_apply, map_smul, smul_eq_mul]
      rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
      ring
    exact Nat.pairEquiv.symm.summable_iff.mp hpair_nat
  calc
    cylinderGreen Ls mass hmass pure₁ pure₂ = ∑' p : ℕ × ℕ, fpair p := hpair_eq
    _ = ∑' a : ℕ, ∑' b : ℕ, fpair (a, b) := hpair_summable.tsum_prod
    _ = ∑' a : ℕ,
          DyninMityaginSpace.coeff a g₁ *
            DyninMityaginSpace.coeff a g₂ *
            l2InnerProduct
              (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass a) h₁)
              (resolventMultiplierCLM (resolventFreq_pos Ls mass hmass a) h₂) := by
          apply tsum_congr
          intro a
          let c : ℝ := DyninMityaginSpace.coeff a g₁ * DyninMityaginSpace.coeff a g₂
          let A : SchwartzMap ℝ ℝ :=
            resolventMultiplierCLM (resolventFreq_pos Ls mass hmass a) h₁
          let B : SchwartzMap ℝ ℝ :=
            resolventMultiplierCLM (resolventFreq_pos Ls mass hmass a) h₂
          have hAB : Summable (fun b : ℕ =>
              DyninMityaginSpace.coeff b A * DyninMityaginSpace.coeff b B) :=
            l2InnerProduct_summable A B
          calc
            (∑' b : ℕ, fpair (a, b))
              = ∑' b : ℕ, c * (DyninMityaginSpace.coeff b A * DyninMityaginSpace.coeff b B) := by
                  apply tsum_congr
                  intro b
                  simp [fpair, c, A, B]
                  ring
            _ = c * ∑' b : ℕ, DyninMityaginSpace.coeff b A * DyninMityaginSpace.coeff b B := by
                  exact hAB.tsum_mul_left c
            _ = c * l2InnerProduct A B := by
                  rfl
            _ = DyninMityaginSpace.coeff a g₁ *
                  DyninMityaginSpace.coeff a g₂ *
                  l2InnerProduct A B := by
                  simp [c]

/-- The pure-tensor cylinder Green form decomposes into a spatial mode sum whose temporal factor
is the bilinear form induced by the Mathlib-normalized inverse-symbol resolvent kernel. -/
theorem cylinderGreen_pure_eq_tsum_mathlibResolventKernel_integral
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) :
    cylinderGreen Ls mass hmass
      (NuclearTensorProduct.pure g₁ h₁)
      (NuclearTensorProduct.pure g₂ h₂) =
    ∑' a : ℕ,
      DyninMityaginSpace.coeff a g₁ *
        DyninMityaginSpace.coeff a g₂ *
        (∫ t, h₁ t *
          (∫ s,
            mathlibResolventKernelReal (resolventFreq Ls mass a) (t - s) * h₂ s)) := by
  rw [cylinderGreen_pure_eq_tsum_l2Inner]
  apply tsum_congr
  intro a
  rw [resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integral
    (ω := resolventFreq Ls mass a)
    (hω := resolventFreq_pos Ls mass hmass a)]

/-- For temporally compactly supported pure tensors, the cylinder Green form is a spatial mode sum
of compact-box bilinear integrals against the Mathlib-normalized inverse-symbol kernel. This is the
box-integral cylinder analogue of
`periodizedSchwartz_mul_resolventFreq_tendsto_free_integralOn_compactDiffBox`. -/
theorem cylinderGreen_pure_eq_tsum_mathlibResolventKernel_integralOn_compactDiffBox
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0) :
    cylinderGreen Ls mass hmass
      (NuclearTensorProduct.pure g₁ h₁)
      (NuclearTensorProduct.pure g₂ h₂) =
    ∑' a : ℕ,
      DyninMityaginSpace.coeff a g₁ *
        DyninMityaginSpace.coeff a g₂ *
        (∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          (h₁ p.1 * h₂ p.2) *
            mathlibResolventKernelReal (resolventFreq Ls mass a) (p.1 - p.2) ∂volume) := by
  rw [cylinderGreen_pure_eq_tsum_l2Inner]
  apply tsum_congr
  intro a
  rw [resolventMultiplier_l2Inner_eq_mathlibResolventKernel_integralOn_compactDiffBox
    (ω := resolventFreq Ls mass a)
    (hω := resolventFreq_pos Ls mass hmass a)
    (h₁ := h₁) (h₂ := h₂)
    (T := T) (hsupp₁ := hsupp₁) (hsupp₂ := hsupp₂)]

/-- Rewriting the cylinder temporal kernel using the physical free resolvent makes the Fourier
normalization discrepancy explicit: each mode involves a factor `(2π)²` and the rescaled frequency
`2π · ω_n`. -/
theorem cylinderGreen_pure_eq_tsum_scaledFreeKernel_integral
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) :
    cylinderGreen Ls mass hmass
      (NuclearTensorProduct.pure g₁ h₁)
      (NuclearTensorProduct.pure g₂ h₂) =
    ∑' a : ℕ,
      DyninMityaginSpace.coeff a g₁ *
        DyninMityaginSpace.coeff a g₂ *
        (∫ t, h₁ t *
          (∫ s,
            (((2 * Real.pi) ^ 2) *
              freeKernel (2 * Real.pi * resolventFreq Ls mass a) (t - s)) * h₂ s)) := by
  rw [cylinderGreen_pure_eq_tsum_l2Inner]
  apply tsum_congr
  intro a
  rw [resolventMultiplier_l2Inner_eq_scaledFreeKernel_integral
    (ω := resolventFreq Ls mass a)
    (hω := resolventFreq_pos Ls mass hmass a)]

/-- Compact-support version of `cylinderGreen_pure_eq_tsum_scaledFreeKernel_integral`.

This puts the cylinder-side pure-tensor covariance in the same compact-box integral format as the
torus-side Lt→∞ theorem, while exposing the exact normalization mismatch. -/
theorem cylinderGreen_pure_eq_tsum_scaledFreeKernel_integralOn_compactDiffBox
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0) :
    cylinderGreen Ls mass hmass
      (NuclearTensorProduct.pure g₁ h₁)
      (NuclearTensorProduct.pure g₂ h₂) =
    ∑' a : ℕ,
      DyninMityaginSpace.coeff a g₁ *
        DyninMityaginSpace.coeff a g₂ *
        (∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          (h₁ p.1 * h₂ p.2) *
            (((2 * Real.pi) ^ 2) *
              freeKernel (2 * Real.pi * resolventFreq Ls mass a) (p.1 - p.2)) ∂volume) := by
  rw [cylinderGreen_pure_eq_tsum_l2Inner]
  apply tsum_congr
  intro a
  rw [resolventMultiplier_l2Inner_eq_scaledFreeKernel_integralOn_compactDiffBox
    (ω := resolventFreq Ls mass a)
    (hω := resolventFreq_pos Ls mass hmass a)
    (h₁ := h₁) (h₂ := h₂)
    (T := T) (hsupp₁ := hsupp₁) (hsupp₂ := hsupp₂)]

/-- The physically normalized pure-cylinder bilinear form obtained by replacing the temporal
resolvent multiplier with the locally corrected version `physicalResolventMultiplierCLM`. -/
private def physicalCylinderGreen_pure
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) : ℝ :=
  ∑' a : ℕ,
    DyninMityaginSpace.coeff a g₁ *
      DyninMityaginSpace.coeff a g₂ *
      l2InnerProduct
        (physicalResolventMultiplierCLM
          (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a) h₁)
        (physicalResolventMultiplierCLM
          (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a) h₂)

/-- The corrected pure-cylinder bilinear form has the expected physical free-kernel expansion. -/
private theorem physicalCylinderGreen_pure_eq_tsum_freeKernel_integral
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) :
    physicalCylinderGreen_pure (Ls := Ls) mass hmass g₁ g₂ h₁ h₂ =
    ∑' a : ℕ,
      DyninMityaginSpace.coeff a g₁ *
        DyninMityaginSpace.coeff a g₂ *
        (∫ t, h₁ t * (∫ s,
          freeKernel (resolventFreq Ls mass a) (t - s) * h₂ s)) := by
  unfold physicalCylinderGreen_pure
  apply tsum_congr
  intro a
  rw [physicalResolventMultiplier_l2Inner_eq_freeKernel_integral
    (ω := resolventFreq Ls mass a)
    (hω := resolventFreq_pos Ls mass hmass a)]

/-- Compact-support version of `physicalCylinderGreen_pure_eq_tsum_freeKernel_integral`. -/
private theorem physicalCylinderGreen_pure_eq_tsum_freeKernel_integralOn_compactDiffBox
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0) :
    physicalCylinderGreen_pure (Ls := Ls) mass hmass g₁ g₂ h₁ h₂ =
    ∑' a : ℕ,
      DyninMityaginSpace.coeff a g₁ *
        DyninMityaginSpace.coeff a g₂ *
        (∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          (h₁ p.1 * h₂ p.2) *
            freeKernel (resolventFreq Ls mass a) (p.1 - p.2) ∂volume) := by
  unfold physicalCylinderGreen_pure
  apply tsum_congr
  intro a
  rw [physicalResolventMultiplier_l2Inner_eq_freeKernel_integralOn_compactDiffBox
    (ω := resolventFreq Ls mass a)
    (hω := resolventFreq_pos Ls mass hmass a)
    (h₁ := h₁) (h₂ := h₂)
    (T := T) (hsupp₁ := hsupp₁) (hsupp₂ := hsupp₂)]

/-- Rescale the temporal Schwartz factor by `h(t) ↦ √(2π) h(2π t)`. -/
private def cylinderTwoPiRescale :
    CylinderTestFunction Ls →L[ℝ] CylinderTestFunction Ls :=
  nuclearTensorProduct_mapCLM
    (ContinuousLinearMap.id ℝ (SmoothMap_Circle Ls ℝ))
    schwartzTwoPiRescaleCLM

@[simp] private theorem cylinderTwoPiRescale_pure
    (g : SmoothMap_Circle Ls ℝ) (h : SchwartzMap ℝ ℝ) :
    cylinderTwoPiRescale Ls (NuclearTensorProduct.pure g h) =
      NuclearTensorProduct.pure g (schwartzTwoPiRescaleCLM h) := by
  rw [show cylinderTwoPiRescale Ls = nuclearTensorProduct_mapCLM
      (ContinuousLinearMap.id ℝ (SmoothMap_Circle Ls ℝ))
      schwartzTwoPiRescaleCLM from rfl,
    nuclearTensorProduct_mapCLM_pure, ContinuousLinearMap.id_apply]

/-- Global physically normalized cylinder covariance, obtained by pulling back `cylinderGreen`
along the explicit temporal normalization rescaling. -/
private def physicalCylinderGreen
    (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction Ls) : ℝ :=
  cylinderGreen Ls mass hmass
    (cylinderTwoPiRescale Ls f)
    (cylinderTwoPiRescale Ls g)

private theorem physicalCylinderGreen_apply_pure_eq
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ) :
    physicalCylinderGreen (Ls := Ls) mass hmass
      (NuclearTensorProduct.pure g₁ h₁)
      (NuclearTensorProduct.pure g₂ h₂) =
    physicalCylinderGreen_pure (Ls := Ls) mass hmass g₁ g₂ h₁ h₂ := by
  unfold physicalCylinderGreen physicalCylinderGreen_pure
  rw [cylinderTwoPiRescale_pure, cylinderTwoPiRescale_pure,
    cylinderGreen_pure_eq_tsum_l2Inner]
  apply tsum_congr
  intro a
  rw [resolventMultiplier_l2Inner_eq_physical_after_twoPiRescale
    (ω := resolventFreq Ls mass a)
    (hω := resolventFreq_pos Ls mass hmass a)]

/-- The cylinder Green form distributes over finite sums in the first argument. -/
theorem cylinderGreen_finset_sum_left
    {ι : Type*}
    (mass : ℝ) (hmass : 0 < mass) (s : Finset ι)
    (a : ι → ℝ) (f : ι → CylinderTestFunction Ls) (g : CylinderTestFunction Ls) :
    cylinderGreen Ls mass hmass (∑ i ∈ s, a i • f i) g =
      ∑ i ∈ s, a i * cylinderGreen Ls mass hmass (f i) g := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp [cylinderGreen]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, cylinderGreen_bilinear, ih, Finset.sum_insert hi]

/-- The cylinder Green form distributes over finite sums in both arguments. -/
theorem cylinderGreen_finset_sum
    {ι₁ ι₂ : Type*}
    (mass : ℝ) (hmass : 0 < mass) (s₁ : Finset ι₁) (s₂ : Finset ι₂)
    (a : ι₁ → ℝ) (b : ι₂ → ℝ)
    (f : ι₁ → CylinderTestFunction Ls) (g : ι₂ → CylinderTestFunction Ls) :
    cylinderGreen Ls mass hmass (∑ i ∈ s₁, a i • f i) (∑ j ∈ s₂, b j • g j) =
      ∑ i ∈ s₁, ∑ j ∈ s₂, a i * b j * cylinderGreen Ls mass hmass (f i) (g j) := by
  classical
  rw [cylinderGreen_finset_sum_left (Ls := Ls) mass hmass s₁ a f]
  congr 1
  ext i
  rw [cylinderGreen_symm, cylinderGreen_finset_sum_left (Ls := Ls) mass hmass s₂ b g]
  rw [Finset.mul_sum]
  congr 1
  ext j
  rw [cylinderGreen_symm]
  ring

private theorem physicalCylinderGreen_finset_sum
    (mass : ℝ) (hmass : 0 < mass)
    {ι₁ ι₂ : Type*}
    (s₁ : Finset ι₁) (s₂ : Finset ι₂)
    (a : ι₁ → ℝ) (b : ι₂ → ℝ)
    (f : ι₁ → CylinderTestFunction Ls) (g : ι₂ → CylinderTestFunction Ls) :
    physicalCylinderGreen (Ls := Ls) mass hmass
      (∑ i ∈ s₁, a i • f i) (∑ j ∈ s₂, b j • g j) =
    ∑ i ∈ s₁, ∑ j ∈ s₂, a i * b j * physicalCylinderGreen (Ls := Ls) mass hmass (f i) (g j) := by
  unfold physicalCylinderGreen
  simpa [map_sum, map_smul, mul_assoc, mul_left_comm, mul_comm] using
    (cylinderGreen_finset_sum (Ls := Ls) mass hmass s₁ s₂ a b
      (fun i => cylinderTwoPiRescale Ls (f i))
      (fun j => cylinderTwoPiRescale Ls (g j)))

/-- Once torus-to-cylinder covariance convergence is known for pure tensors, bilinearity
upgrades it to finite sums of pure tensors. This isolates the remaining extension step
to passing from finite-rank tensors to general cylinder test functions. -/
theorem asymTorusGreen_tendsto_cylinderGreen_finset_sum_of_pure
    (mass : ℝ) (hmass : 0 < mass)
    {ι₁ ι₂ : Type*}
    (s₁ : Finset ι₁) (s₂ : Finset ι₂)
    (a : ι₁ → ℝ) (b : ι₂ → ℝ)
    (g₁ : ι₁ → SmoothMap_Circle Ls ℝ)
    (h₁ : ι₁ → SchwartzMap ℝ ℝ)
    (g₂ : ι₂ → SmoothMap_Circle Ls ℝ)
    (h₂ : ι₂ → SchwartzMap ℝ ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hpure : ∀ i j,
      Tendsto (fun n =>
        @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
          (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
            (NuclearTensorProduct.pure (g₁ i) (h₁ i)))
          (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
            (NuclearTensorProduct.pure (g₂ j) (h₂ j))))
        atTop
        (nhds (cylinderGreen Ls mass hmass
          (NuclearTensorProduct.pure (g₁ i) (h₁ i))
          (NuclearTensorProduct.pure (g₂ j) (h₂ j))))) :
    Tendsto (fun n =>
      @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
          (∑ i ∈ s₁, a i • NuclearTensorProduct.pure (g₁ i) (h₁ i)))
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
          (∑ j ∈ s₂, b j • NuclearTensorProduct.pure (g₂ j) (h₂ j))))
      atTop
      (nhds (cylinderGreen Ls mass hmass
        (∑ i ∈ s₁, a i • NuclearTensorProduct.pure (g₁ i) (h₁ i))
        (∑ j ∈ s₂, b j • NuclearTensorProduct.pure (g₂ j) (h₂ j)))) := by
  classical
  set f : CylinderTestFunction Ls :=
    ∑ i ∈ s₁, a i • NuclearTensorProduct.pure (g₁ i) (h₁ i)
  set g : CylinderTestFunction Ls :=
    ∑ j ∈ s₂, b j • NuclearTensorProduct.pure (g₂ j) (h₂ j)
  have hsum :
      Tendsto
        (fun n =>
          ∑ i ∈ s₁, ∑ j ∈ s₂,
            a i * b j *
              @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
                (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
                  (NuclearTensorProduct.pure (g₁ i) (h₁ i)))
                (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
                  (NuclearTensorProduct.pure (g₂ j) (h₂ j))))
        atTop
        (nhds
          (∑ i ∈ s₁, ∑ j ∈ s₂,
            a i * b j *
              cylinderGreen Ls mass hmass
                (NuclearTensorProduct.pure (g₁ i) (h₁ i))
                (NuclearTensorProduct.pure (g₂ j) (h₂ j)))) := by
    apply tendsto_finset_sum
    intro i hi
    apply tendsto_finset_sum
    intro j hj
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Filter.Tendsto.const_mul (a i * b j) (hpure i j)
  have hleft :
      (fun n =>
        @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
          (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ f)
          (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ g)) =
      (fun n =>
        ∑ i ∈ s₁, ∑ j ∈ s₂,
          a i * b j *
            @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
              (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
                (NuclearTensorProduct.pure (g₁ i) (h₁ i)))
              (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
                (NuclearTensorProduct.pure (g₂ j) (h₂ j)))) := by
    funext n
    simpa [f, g, asymTorusContinuumGreen, mul_assoc, mul_left_comm, mul_comm] using
      (GaussianField.greenFunctionBilinear_finset_sum
        (E := AsymTorusTestFunction (Lt n) Ls) mass hmass s₁ s₂ a b
        (fun i =>
          @cylinderToTorusEmbed (Lt n) Ls (hLt n) _
            (NuclearTensorProduct.pure (g₁ i) (h₁ i)))
        (fun j =>
          @cylinderToTorusEmbed (Lt n) Ls (hLt n) _
            (NuclearTensorProduct.pure (g₂ j) (h₂ j))))
  have hright :
      cylinderGreen Ls mass hmass f g =
        ∑ i ∈ s₁, ∑ j ∈ s₂,
          a i * b j *
            cylinderGreen Ls mass hmass
              (NuclearTensorProduct.pure (g₁ i) (h₁ i))
              (NuclearTensorProduct.pure (g₂ j) (h₂ j)) := by
    simpa [f, g, mul_assoc, mul_left_comm, mul_comm] using
      (cylinderGreen_finset_sum (Ls := Ls) mass hmass s₁ s₂ a b
        (fun i => NuclearTensorProduct.pure (g₁ i) (h₁ i))
        (fun j => NuclearTensorProduct.pure (g₂ j) (h₂ j)))
  rw [hleft, hright]
  exact hsum

private theorem physicalCylinderGreen_product_seminorm_bound
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ q : Seminorm ℝ (CylinderTestFunction Ls),
      Continuous q ∧
      ∀ f g : CylinderTestFunction Ls,
        |physicalCylinderGreen (Ls := Ls) mass hmass f g| ≤ q f * q g := by
  let Tphys : CylinderTestFunction Ls →L[ℝ] ell2' :=
    (GaussianField.cylinderMassOperator Ls mass hmass).comp (cylinderTwoPiRescale Ls)
  let q : Seminorm ℝ (CylinderTestFunction Ls) :=
    (normSeminorm ℝ ell2').comp Tphys.toLinearMap
  refine ⟨q, ((norm_withSeminorms ℝ ell2').continuous_seminorm 0).comp Tphys.continuous, ?_⟩
  intro f g
  simpa [physicalCylinderGreen, q, Tphys, cylinderGreen] using
    abs_real_inner_le_norm (Tphys f) (Tphys g)

private def schwartzCutoffBump (N : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨(N : ℝ) + 1, 2 * ((N : ℝ) + 1), by positivity, by linarith⟩

private def schwartzCutoff (N : ℕ) : ℝ → ℝ :=
  schwartzCutoffBump N

private theorem schwartzCutoff_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ schwartzCutoff N x := by
  simpa [schwartzCutoff] using (schwartzCutoffBump N).nonneg' x

private theorem schwartzCutoff_le_one (N : ℕ) (x : ℝ) :
    schwartzCutoff N x ≤ 1 := by
  simpa [schwartzCutoff] using (schwartzCutoffBump N).le_one

private theorem schwartzCutoff_eq_one_of_abs_le (N : ℕ) {x : ℝ}
    (hx : |x| ≤ (N : ℝ) + 1) :
    schwartzCutoff N x = 1 := by
  exact (schwartzCutoffBump N).one_of_mem_closedBall <| by
    simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hx

private theorem schwartzCutoff_eq_zero_of_two_mul_lt_abs (N : ℕ) {x : ℝ}
    (hx : 2 * ((N : ℝ) + 1) < |x|) :
    schwartzCutoff N x = 0 := by
  exact (schwartzCutoffBump N).zero_of_le_dist <| by
    simpa [dist_eq_norm, Real.norm_eq_abs] using hx.le

private theorem schwartzCutoff_smooth (N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (schwartzCutoff N) := by
  simpa [schwartzCutoff] using (schwartzCutoffBump N).contDiff

private def schwartzCutoffProfileSchwartz : SchwartzMap ℝ ℝ :=
  (schwartzCutoffBump 0).hasCompactSupport.toSchwartzMap
    ((schwartzCutoffBump 0).contDiff)

private theorem schwartzCutoff_eq_profile_scaled (N : ℕ) :
    schwartzCutoff N =
      fun x => schwartzCutoffProfileSchwartz ((((N : ℝ) + 1)⁻¹) * x) := by
  funext x
  have hNp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  simp [schwartzCutoff, schwartzCutoffBump, schwartzCutoffProfileSchwartz,
    ContDiffBump.apply, div_eq_mul_inv, sub_eq_add_neg, mul_left_comm, mul_comm,
    hNp.ne']

private theorem schwartzCutoff_hasTemperateGrowth (N : ℕ) :
    (schwartzCutoff N).HasTemperateGrowth := by
  have hscale : (fun x : ℝ => (((N : ℝ) + 1)⁻¹) * x).HasTemperateGrowth := by
    fun_prop
  simpa [schwartzCutoff_eq_profile_scaled (N := N)] using
    schwartzCutoffProfileSchwartz.hasTemperateGrowth.comp hscale

private theorem abs_iteratedDeriv_schwartzCutoff_le
    (i N : ℕ) (x : ℝ) :
    |iteratedDeriv i (schwartzCutoff N) x| ≤
      (((N : ℝ) + 1)⁻¹) ^ i *
        SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz := by
  have hscale :
      iteratedDeriv i (schwartzCutoff N) x =
        (((N : ℝ) + 1)⁻¹) ^ i *
          iteratedDeriv i schwartzCutoffProfileSchwartz ((((N : ℝ) + 1)⁻¹) * x) := by
    rw [schwartzCutoff_eq_profile_scaled (N := N)]
    simpa using
      congrFun
        (iteratedDeriv_comp_const_mul
          (n := i) (h := schwartzCutoffProfileSchwartz.smooth i) (((N : ℝ) + 1)⁻¹)) x
  have hsemi :
      |iteratedDeriv i schwartzCutoffProfileSchwartz ((((N : ℝ) + 1)⁻¹) * x)| ≤
        SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz := by
    simpa [pow_zero, Real.norm_eq_abs] using
      (SchwartzMap.le_seminorm' (𝕜 := ℝ) (k := 0) (n := i)
        schwartzCutoffProfileSchwartz ((((N : ℝ) + 1)⁻¹) * x))
  have hinv_nonneg : 0 ≤ (((N : ℝ) + 1)⁻¹) ^ i := by positivity
  calc
    |iteratedDeriv i (schwartzCutoff N) x|
      = |((((N : ℝ) + 1)⁻¹) ^ i *
          iteratedDeriv i schwartzCutoffProfileSchwartz ((((N : ℝ) + 1)⁻¹) * x))| := by
          rw [hscale]
    _ = (((N : ℝ) + 1)⁻¹) ^ i *
          |iteratedDeriv i schwartzCutoffProfileSchwartz ((((N : ℝ) + 1)⁻¹) * x)| := by
          rw [abs_mul, abs_of_nonneg hinv_nonneg]
    _ ≤ (((N : ℝ) + 1)⁻¹) ^ i *
          SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz := by
          gcongr

private def schwartzCutoffCLM (N : ℕ) : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ :=
  SchwartzMap.smulLeftCLM ℝ (schwartzCutoff N)

private theorem schwartzCutoffCLM_apply (N : ℕ) (h : SchwartzMap ℝ ℝ) :
    schwartzCutoffCLM N h = fun x => schwartzCutoff N x * h x := by
  simpa [schwartzCutoffCLM, smul_eq_mul] using
    (SchwartzMap.smulLeftCLM_apply (F := ℝ) (g := schwartzCutoff N)
      (hg := schwartzCutoff_hasTemperateGrowth N) h)

@[simp] private theorem schwartzCutoffCLM_apply_apply
    (N : ℕ) (h : SchwartzMap ℝ ℝ) (x : ℝ) :
    schwartzCutoffCLM N h x = schwartzCutoff N x * h x := by
  simpa [schwartzCutoffCLM, smul_eq_mul] using
    (SchwartzMap.smulLeftCLM_apply_apply (F := ℝ) (g := schwartzCutoff N)
      (hg := schwartzCutoff_hasTemperateGrowth N) h x)

private theorem schwartzCutoffCLM_eq_zero_of_two_mul_lt_abs
    (N : ℕ) (h : SchwartzMap ℝ ℝ) {x : ℝ}
    (hx : 2 * ((N : ℝ) + 1) < |x|) :
    schwartzCutoffCLM N h x = 0 := by
  rw [schwartzCutoffCLM_apply_apply, schwartzCutoff_eq_zero_of_two_mul_lt_abs N hx]
  simp

private theorem schwartzCutoff_error_seminorm_le
    (h : SchwartzMap ℝ ℝ) (k n N : ℕ) :
    SchwartzMap.seminorm ℝ k n (h - schwartzCutoffCLM N h) ≤
      (Finset.sum (Finset.range (n + 1)) fun i =>
        if i = 0 then
          SchwartzMap.seminorm ℝ (k + 1) n h
        else
          (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz *
            SchwartzMap.seminorm ℝ k (n - i) h) *
        (((N : ℝ) + 1)⁻¹) := by
  let Cterm : ℕ → ℝ := fun i =>
    if i = 0 then
      SchwartzMap.seminorm ℝ (k + 1) n h
    else
      (n.choose i : ℝ) *
        SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz *
        SchwartzMap.seminorm ℝ k (n - i) h
  have hCterm_nonneg : ∀ i, 0 ≤ Cterm i := by
    intro i
    by_cases hi : i = 0
    · simp only [Cterm, hi, if_true]
      exact apply_nonneg _ _
    · simp only [Cterm, hi, if_false]
      positivity
  refine SchwartzMap.seminorm_le_bound' (𝕜 := ℝ) (F := ℝ)
    (k := k) (n := n) (f := h - schwartzCutoffCLM N h) ?_ ?_
  · have hsum_nonneg : 0 ≤ Finset.sum (Finset.range (n + 1)) Cterm := by
      exact Finset.sum_nonneg fun i _ => hCterm_nonneg i
    positivity
  · intro x
    have hcut : ContDiffAt ℝ n (fun t => 1 - schwartzCutoff N t) x := by
      have hsmooth :
          ContDiff ℝ n (fun t => 1 - schwartzCutoff N t) :=
        contDiff_const.add
          (((schwartzCutoff_smooth N).of_le (by exact_mod_cast le_top)).neg)
      simpa [sub_eq_add_neg] using
        hsmooth.contDiffAt
    have hh : ContDiffAt ℝ n h x := by
      simpa using (h.smooth n).contDiffAt
    have hderiv :
        iteratedDeriv n (h - schwartzCutoffCLM N h) x =
          Finset.sum (Finset.range (n + 1)) fun i =>
            (n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
              iteratedDeriv (n - i) h x := by
      have hmul := iteratedDeriv_fun_mul (f := fun t => 1 - schwartzCutoff N t) (g := h) hcut hh
      have hEq : ((h - schwartzCutoffCLM N h : SchwartzMap ℝ ℝ) : ℝ → ℝ) =
          fun t => (1 - schwartzCutoff N t) * h t := by
        funext t
        simp [sub_eq_add_neg, schwartzCutoffCLM_apply_apply]
        ring
      change iteratedDeriv n (((h - schwartzCutoffCLM N h : SchwartzMap ℝ ℝ) : ℝ → ℝ)) x = _
      rw [hEq]
      simpa using hmul
    calc
      |x| ^ k * ‖iteratedDeriv n (h - schwartzCutoffCLM N h) x‖
        = |x| ^ k * ‖Finset.sum (Finset.range (n + 1)) fun i =>
            (n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
              iteratedDeriv (n - i) h x‖ := by
              rw [hderiv]
      _ ≤ Finset.sum (Finset.range (n + 1)) fun i =>
            |x| ^ k * ‖(n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
              iteratedDeriv (n - i) h x‖ := by
              have hx_nonneg : 0 ≤ |x| ^ k := by positivity
              have hsum_norm :
                  ‖Finset.sum (Finset.range (n + 1)) (fun i =>
                      (n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
                        iteratedDeriv (n - i) h x)‖ ≤
                    Finset.sum (Finset.range (n + 1)) (fun i =>
                      ‖(n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
                        iteratedDeriv (n - i) h x‖) := by
                exact norm_sum_le _ _
              calc
                |x| ^ k *
                    ‖Finset.sum (Finset.range (n + 1)) (fun i =>
                        (n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
                          iteratedDeriv (n - i) h x)‖
                  ≤ |x| ^ k *
                      Finset.sum (Finset.range (n + 1)) (fun i =>
                        ‖(n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
                          iteratedDeriv (n - i) h x‖) :=
                    mul_le_mul_of_nonneg_left hsum_norm hx_nonneg
                _ = Finset.sum (Finset.range (n + 1)) (fun i =>
                      |x| ^ k *
                        ‖(n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
                          iteratedDeriv (n - i) h x‖) := by
                    rw [Finset.mul_sum]
      _ ≤ Finset.sum (Finset.range (n + 1)) fun i => Cterm i * (((N : ℝ) + 1)⁻¹) := by
              apply Finset.sum_le_sum
              intro i hi
              by_cases hi0 : i = 0
              · subst hi0
                by_cases hx : |x| ≤ (N : ℝ) + 1
                · have hnonneg : 0 ≤ Cterm 0 * (((N : ℝ) + 1)⁻¹) := by
                    positivity
                  simpa [Cterm, schwartzCutoff_eq_one_of_abs_le N hx] using hnonneg
                · have hlarge : (N : ℝ) + 1 < |x| := lt_of_not_ge hx
                  have hfactor :
                      |1 - schwartzCutoff N x| ≤ 1 := by
                    have hnonneg : 0 ≤ 1 - schwartzCutoff N x := by
                      linarith [schwartzCutoff_le_one N x]
                    rw [abs_of_nonneg hnonneg]
                    linarith [schwartzCutoff_nonneg N x]
                  have hsemi :
                      |x| ^ (k + 1) * |iteratedDeriv n h x| ≤
                        SchwartzMap.seminorm ℝ (k + 1) n h := by
                    simpa [Real.norm_eq_abs] using
                      (SchwartzMap.le_seminorm' (𝕜 := ℝ) (k := k + 1) (n := n) h x)
                  have htail :
                      |x| ^ k * |iteratedDeriv n h x| ≤
                        SchwartzMap.seminorm ℝ (k + 1) n h * (((N : ℝ) + 1)⁻¹) := by
                    have hmul :
                        ((N : ℝ) + 1) * (|x| ^ k * |iteratedDeriv n h x|) ≤
                          SchwartzMap.seminorm ℝ (k + 1) n h := by
                      calc
                        ((N : ℝ) + 1) * (|x| ^ k * |iteratedDeriv n h x|)
                          ≤ |x| * (|x| ^ k * |iteratedDeriv n h x|) := by
                              gcongr
                        _ = |x| ^ (k + 1) * |iteratedDeriv n h x| := by ring
                        _ ≤ SchwartzMap.seminorm ℝ (k + 1) n h := hsemi
                    have hNp : 0 < (N : ℝ) + 1 := by positivity
                    have hunit : ((N : ℝ) + 1) * (((N : ℝ) + 1)⁻¹) = 1 := by
                      field_simp [hNp.ne']
                    calc
                      |x| ^ k * |iteratedDeriv n h x|
                        = (((N : ℝ) + 1) * (((N : ℝ) + 1)⁻¹)) *
                            (|x| ^ k * |iteratedDeriv n h x|) := by
                              rw [hunit, one_mul]
                      _ = (((N : ℝ) + 1) * (|x| ^ k * |iteratedDeriv n h x|)) *
                            (((N : ℝ) + 1)⁻¹) := by ring
                      _ ≤ SchwartzMap.seminorm ℝ (k + 1) n h * (((N : ℝ) + 1)⁻¹) := by
                              gcongr
                  calc
                    |x| ^ k *
                        ‖(n.choose 0 : ℝ) * iteratedDeriv 0 (fun t => 1 - schwartzCutoff N t) x *
                          iteratedDeriv (n - 0) h x‖
                      = |x| ^ k * (|1 - schwartzCutoff N x| * |iteratedDeriv n h x|) := by
                          simp [Real.norm_eq_abs]
                    _ ≤ |x| ^ k * (1 * |iteratedDeriv n h x|) := by
                          gcongr
                    _ = |x| ^ k * |iteratedDeriv n h x| := by ring
                    _ ≤ Cterm 0 * (((N : ℝ) + 1)⁻¹) := by
                          simpa [Cterm]
                            using htail
              · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
                have hcutBoundAbs :
                    |iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x| ≤
                      (((N : ℝ) + 1)⁻¹) ^ i *
                        SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz := by
                  rw [iteratedDeriv_const_sub hi_pos (1 : ℝ), iteratedDeriv_neg, abs_neg]
                  exact abs_iteratedDeriv_schwartzCutoff_le i N x
                have hcutBound :
                    ‖iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x‖ ≤
                      (((N : ℝ) + 1)⁻¹) ^ i *
                        SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz := by
                  simpa [Real.norm_eq_abs] using hcutBoundAbs
                have hhBoundAbs :
                    |x| ^ k * |iteratedDeriv (n - i) h x| ≤
                      SchwartzMap.seminorm ℝ k (n - i) h := by
                  simpa [Real.norm_eq_abs] using
                    (SchwartzMap.le_seminorm' (𝕜 := ℝ) (k := k) (n := n - i) h x)
                have hinv_nonneg : 0 ≤ ((N : ℝ) + 1)⁻¹ := by positivity
                have hinv_le_one : ((N : ℝ) + 1)⁻¹ ≤ 1 := by
                  have hone : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith
                  exact inv_le_one_of_one_le₀ hone
                have hpow_le :
                    (((N : ℝ) + 1)⁻¹) ^ i ≤ ((N : ℝ) + 1)⁻¹ := by
                  rcases Nat.exists_eq_succ_of_ne_zero hi0 with ⟨j, rfl⟩
                  have hpowj : (((N : ℝ) + 1)⁻¹) ^ j ≤ 1 := by
                    exact pow_le_one₀ hinv_nonneg hinv_le_one
                  calc
                    (((N : ℝ) + 1)⁻¹) ^ (j + 1)
                      = (((N : ℝ) + 1)⁻¹) ^ j * ((N : ℝ) + 1)⁻¹ := by
                          rw [pow_succ]
                    _ ≤ 1 * ((N : ℝ) + 1)⁻¹ := by
                          exact mul_le_mul_of_nonneg_right hpowj hinv_nonneg
                    _ = ((N : ℝ) + 1)⁻¹ := by ring
                calc
                  |x| ^ k *
                      ‖(n.choose i : ℝ) * iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x *
                        iteratedDeriv (n - i) h x‖
                    = (n.choose i : ℝ) *
                        (|iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x| *
                          (|x| ^ k * |iteratedDeriv (n - i) h x|)) := by
                            rw [Real.norm_eq_abs, abs_mul, abs_mul,
                              abs_of_nonneg (by positivity : 0 ≤ (n.choose i : ℝ))]
                            ring
                  _ ≤ (n.choose i : ℝ) *
                        ((((N : ℝ) + 1)⁻¹) ^ i *
                          SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz) *
                        SchwartzMap.seminorm ℝ k (n - i) h := by
                          have hchoose_nonneg : 0 ≤ (n.choose i : ℝ) := by positivity
                          have hrhs_nonneg :
                              0 ≤ (((N : ℝ) + 1)⁻¹) ^ i *
                                SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz := by
                            positivity
                          have htail_nonneg : 0 ≤ |x| ^ k * |iteratedDeriv (n - i) h x| := by
                            positivity
                          have hprod_bound :
                              |iteratedDeriv i (fun t => 1 - schwartzCutoff N t) x| *
                                  (|x| ^ k * |iteratedDeriv (n - i) h x|) ≤
                                ((((N : ℝ) + 1)⁻¹) ^ i *
                                  SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz) *
                                  SchwartzMap.seminorm ℝ k (n - i) h := by
                            exact mul_le_mul hcutBoundAbs hhBoundAbs htail_nonneg hrhs_nonneg
                          simpa [mul_assoc] using
                            (mul_le_mul_of_nonneg_left hprod_bound hchoose_nonneg)
                  _ ≤ (n.choose i : ℝ) *
                        ((((N : ℝ) + 1)⁻¹) *
                          SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz) *
                        SchwartzMap.seminorm ℝ k (n - i) h := by
                          have hsemi_nonneg :
                              0 ≤ SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz := by
                            exact apply_nonneg _ _
                          have hhsemi_nonneg :
                              0 ≤ SchwartzMap.seminorm ℝ k (n - i) h := by
                            exact apply_nonneg _ _
                          apply mul_le_mul_of_nonneg_right
                          · apply mul_le_mul_of_nonneg_left
                            · exact mul_le_mul_of_nonneg_right hpow_le hsemi_nonneg
                            · positivity
                          · exact hhsemi_nonneg
                  _ = Cterm i * (((N : ℝ) + 1)⁻¹) := by
                          simp [Cterm, hi0, mul_left_comm, mul_comm]
      _ = (Finset.sum (Finset.range (n + 1)) Cterm) * (((N : ℝ) + 1)⁻¹) := by
              rw [Finset.sum_mul]

private theorem schwartzCutoffCLM_tendsto
    (h : SchwartzMap ℝ ℝ) :
    Tendsto (fun N => schwartzCutoffCLM N h) atTop (nhds h) := by
  rw [(schwartz_withSeminorms ℝ ℝ ℝ).tendsto_nhds]
  intro m ε hε
  let C : ℝ :=
    Finset.sum (Finset.range (m.2 + 1)) fun i =>
      if i = 0 then
        SchwartzMap.seminorm ℝ (m.1 + 1) m.2 h
      else
        (m.2.choose i : ℝ) *
          SchwartzMap.seminorm ℝ 0 i schwartzCutoffProfileSchwartz *
          SchwartzMap.seminorm ℝ m.1 (m.2 - i) h
  have hC_nonneg : 0 ≤ C := by
    unfold C
    exact Finset.sum_nonneg fun i _ => by
      by_cases hi : i = 0
      · simp only [hi, if_true]
        exact apply_nonneg _ _
      · simp only [hi, if_false]
        positivity
  have h_inv :
      Tendsto (fun N : ℕ => (((N : ℝ) + 1)⁻¹)) atTop (nhds 0) := by
    simpa using
      (tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop))
  have h_bound_tend :
      Tendsto (fun N : ℕ => C * (((N : ℝ) + 1)⁻¹)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul h_inv)
  have h_bound_ev : ∀ᶠ N : ℕ in atTop, C * (((N : ℝ) + 1)⁻¹) < ε := by
    exact (Metric.tendsto_nhds.mp h_bound_tend) ε hε |>.mono fun N hN => by
      have hInv_nonneg : 0 ≤ (((N : ℝ) + 1)⁻¹) := by positivity
      have hNatAbs : |((N : ℝ) + 1)| = (N : ℝ) + 1 := by
        exact abs_of_nonneg (by positivity)
      have hCabs : |C| = C := abs_of_nonneg hC_nonneg
      have hInvabs : |(((N : ℝ) + 1)⁻¹)| = (((N : ℝ) + 1)⁻¹) := abs_of_nonneg hInv_nonneg
      simpa [Real.dist_eq, abs_mul, hCabs, hInvabs, hNatAbs] using hN
  filter_upwards [h_bound_ev] with N hN
  have hle :
      SchwartzMap.seminorm ℝ m.1 m.2 (schwartzCutoffCLM N h - h) ≤
        C * (((N : ℝ) + 1)⁻¹) := by
    have hsym : schwartzCutoffCLM N h - h = -(h - schwartzCutoffCLM N h) := by
      abel
    calc
      SchwartzMap.seminorm ℝ m.1 m.2 (schwartzCutoffCLM N h - h)
        = SchwartzMap.seminorm ℝ m.1 m.2 (h - schwartzCutoffCLM N h) := by
            rw [hsym, map_neg_eq_map]
      _ ≤ C * (((N : ℝ) + 1)⁻¹) := by
            unfold C
            exact schwartzCutoff_error_seminorm_le h m.1 m.2 N
  exact lt_of_le_of_lt hle hN

private def cylinderBasisSpatial (m : ℕ) : SmoothMap_Circle Ls ℝ :=
  DyninMityaginSpace.basis (E := SmoothMap_Circle Ls ℝ) (Nat.unpair m).1

private def cylinderBasisTemporal (m : ℕ) : SchwartzMap ℝ ℝ :=
  DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) (Nat.unpair m).2

private theorem cylinderBasis_eq_pure (m : ℕ) :
    (DyninMityaginSpace.basis (E := CylinderTestFunction Ls) m) =
      NuclearTensorProduct.pure
        (cylinderBasisSpatial (Ls := Ls) m)
        (cylinderBasisTemporal m) := by
  simpa [cylinderBasisSpatial, cylinderBasisTemporal] using
    (NuclearTensorProduct.basisVec_eq_pure
      (E₁ := SmoothMap_Circle Ls ℝ) (E₂ := SchwartzMap ℝ ℝ)
      (fun n m => by simp [DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis])
      (fun n m => by simp [DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis]) m)

private def basisPurePartial
    (f : CylinderTestFunction Ls) (s : Finset ℕ) : CylinderTestFunction Ls :=
  ∑ m ∈ s, DyninMityaginSpace.coeff m f •
    NuclearTensorProduct.pure
      (cylinderBasisSpatial (Ls := Ls) m)
      (cylinderBasisTemporal m)

private def basisCutoffPartial
    (f : CylinderTestFunction Ls) (s : Finset ℕ) (N : ℕ) : CylinderTestFunction Ls :=
  ∑ m ∈ s, DyninMityaginSpace.coeff m f •
    NuclearTensorProduct.pure
      (cylinderBasisSpatial (Ls := Ls) m)
      (schwartzCutoffCLM N (cylinderBasisTemporal m))

private theorem basisPurePartial_tendsto
    (f : CylinderTestFunction Ls) :
    Tendsto (fun s : Finset ℕ => basisPurePartial (Ls := Ls) f s) atTop (nhds f) := by
  have hsum :
      Tendsto
        (fun s : Finset ℕ =>
          ∑ m ∈ s, DyninMityaginSpace.coeff m f •
            (DyninMityaginSpace.basis (E := CylinderTestFunction Ls) m))
        atTop (nhds f) := by
    simpa [HasSum, SummationFilter.unconditional_filter] using
      (DyninMityaginSpace.hasSum_basis (E := CylinderTestFunction Ls) f)
  simpa [basisPurePartial, cylinderBasis_eq_pure] using hsum

private theorem basisCutoffPartial_tendsto
    (f : CylinderTestFunction Ls) (s : Finset ℕ) :
    Tendsto (fun N => basisCutoffPartial (Ls := Ls) f s N) atTop
      (nhds (basisPurePartial (Ls := Ls) f s)) := by
  unfold basisCutoffPartial basisPurePartial
  apply tendsto_finset_sum
  intro m hm
  have htemp :
      Tendsto
        (fun N => schwartzCutoffCLM N (cylinderBasisTemporal m))
        atTop
        (nhds (cylinderBasisTemporal m)) :=
    schwartzCutoffCLM_tendsto _
  have hpure :
      Tendsto
        (fun N =>
          NuclearTensorProduct.pure
            (cylinderBasisSpatial (Ls := Ls) m)
            (schwartzCutoffCLM N (cylinderBasisTemporal m)))
        atTop
        (nhds
          (NuclearTensorProduct.pure
            (cylinderBasisSpatial (Ls := Ls) m)
            (cylinderBasisTemporal m))) := by
    exact
      (NuclearTensorProduct.pureCLM_right
        (E₁ := SmoothMap_Circle Ls ℝ) (E₂ := SchwartzMap ℝ ℝ)
        (cylinderBasisSpatial (Ls := Ls) m)).continuous.continuousAt.tendsto.comp htemp
  simpa using hpure.const_smul (DyninMityaginSpace.coeff m f)

private theorem exists_compactSupport_basisApprox
    (q : Seminorm ℝ (CylinderTestFunction Ls)) (hq : Continuous q)
    (f : CylinderTestFunction Ls) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset ℕ, ∃ N : ℕ,
      q (f - basisCutoffPartial (Ls := Ls) f s N) < ε := by
  have hpure_tend := basisPurePartial_tendsto (Ls := Ls) f
  have hq0 : q (0 : CylinderTestFunction Ls) = 0 := map_zero q
  have hpure_zero :
      Tendsto (fun s : Finset ℕ => basisPurePartial (Ls := Ls) f s - f) atTop (nhds 0) := by
    simpa using
      (hpure_tend.sub
        (tendsto_const_nhds : Tendsto (fun _ : Finset ℕ => f) atTop (nhds f)))
  have hq_pure :
      Tendsto
        (fun s : Finset ℕ => q (basisPurePartial (Ls := Ls) f s - f))
        atTop (nhds 0) := by
    simpa [hq0] using
      ((hq.continuousAt : ContinuousAt q 0).tendsto.comp hpure_zero)
  have hε2 : 0 < ε / 2 := by linarith
  have hpure_ev :
      ∀ᶠ s : Finset ℕ in atTop, q (basisPurePartial (Ls := Ls) f s - f) < ε / 2 := by
    have hdist :
        ∀ᶠ s : Finset ℕ in atTop,
          dist (q (basisPurePartial (Ls := Ls) f s - f)) 0 < ε / 2 := by
      simpa [hq0] using (Metric.tendsto_nhds.mp hq_pure) (ε / 2) hε2
    filter_upwards [hdist] with s hs
    simpa [Real.dist_eq, hq0, sub_zero, abs_of_nonneg (apply_nonneg q _)] using hs
  rw [Filter.eventually_atTop] at hpure_ev
  obtain ⟨s, hs⟩ := hpure_ev
  have hcut_tend := basisCutoffPartial_tendsto (Ls := Ls) f s
  have hcut_zero :
      Tendsto
        (fun N => basisCutoffPartial (Ls := Ls) f s N - basisPurePartial (Ls := Ls) f s)
        atTop (nhds 0) := by
    simpa using
      (hcut_tend.sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => basisPurePartial (Ls := Ls) f s) atTop
            (nhds (basisPurePartial (Ls := Ls) f s))))
  have hq_cut :
      Tendsto
        (fun N => q (basisCutoffPartial (Ls := Ls) f s N -
          basisPurePartial (Ls := Ls) f s))
        atTop (nhds 0) := by
    simpa [hq0] using
      ((hq.continuousAt : ContinuousAt q 0).tendsto.comp hcut_zero)
  have hq_cut_ev :
      ∀ᶠ N : ℕ in atTop,
        q (basisCutoffPartial (Ls := Ls) f s N - basisPurePartial (Ls := Ls) f s) < ε / 2 := by
    have hdist :
        ∀ᶠ N : ℕ in atTop,
          dist (q (basisCutoffPartial (Ls := Ls) f s N - basisPurePartial (Ls := Ls) f s))
            0 < ε / 2 := by
      simpa [hq0] using (Metric.tendsto_nhds.mp hq_cut) (ε / 2) hε2
    filter_upwards [hdist] with N hN
    simpa [Real.dist_eq, hq0, sub_zero, abs_of_nonneg (apply_nonneg q _)] using hN
  rw [Filter.eventually_atTop] at hq_cut_ev
  obtain ⟨N, hN⟩ := hq_cut_ev
  refine ⟨s, N, ?_⟩
  have hs' : q (basisPurePartial (Ls := Ls) f s - f) < ε / 2 := hs s le_rfl
  have hN' :
      q (basisCutoffPartial (Ls := Ls) f s N - basisPurePartial (Ls := Ls) f s) < ε / 2 :=
    hN N le_rfl
  have hsym₁ :
      q (f - basisPurePartial (Ls := Ls) f s) < ε / 2 := by
    have hneg :
        f - basisPurePartial (Ls := Ls) f s =
          -(basisPurePartial (Ls := Ls) f s - f) := by
      abel
    rw [hneg, map_neg_eq_map]
    exact hs'
  have hsym₂ :
      q (basisPurePartial (Ls := Ls) f s - basisCutoffPartial (Ls := Ls) f s N) < ε / 2 := by
    have hneg :
        basisPurePartial (Ls := Ls) f s - basisCutoffPartial (Ls := Ls) f s N =
          -(basisCutoffPartial (Ls := Ls) f s N - basisPurePartial (Ls := Ls) f s) := by
      abel
    rw [hneg, map_neg_eq_map]
    exact hN'
  calc
    q (f - basisCutoffPartial (Ls := Ls) f s N)
      = q ((f - basisPurePartial (Ls := Ls) f s) +
          (basisPurePartial (Ls := Ls) f s - basisCutoffPartial (Ls := Ls) f s N)) := by
            congr 1
            abel
    _ ≤ q (f - basisPurePartial (Ls := Ls) f s) +
        q (basisPurePartial (Ls := Ls) f s - basisCutoffPartial (Ls := Ls) f s N) :=
          map_add_le_add q _ _
    _ < ε := by linarith

/-- Second moments for the pulled-back cylinder GFF equal torus second moments on embedded
test functions (`Pphi2.IRLimit.CylinderEmbedding.cylinderPullbackMeasure_integral_sq`). -/
theorem cylinderPullbackGFF_secondMoment_eq_torus
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction Ls) :
    ∫ ω, (ω f) ^ 2 ∂(cylinderPullbackMeasure Lt Ls
        (GaussianField.measure (GaussianField.cylinderMassOperator Ls mass hmass))) =
    ∫ ω, (ω (cylinderToTorusEmbed Lt Ls f)) ^ 2 ∂
        (GaussianField.measure (GaussianField.cylinderMassOperator Ls mass hmass)) :=
  cylinderPullbackMeasure_integral_sq Lt Ls _ f

/-- The free cylinder Gaussian has centered Gaussian 1D marginals with variance
`cylinderGreen Ls mass hmass f f`. -/
theorem cylinderFreeMeasure_eval_map_eq_gaussianReal
    (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction Ls) :
    (GaussianField.measure (GaussianField.cylinderMassOperator Ls mass hmass)).map
      (fun ω : Configuration (CylinderTestFunction Ls) => ω f) =
    ProbabilityTheory.gaussianReal 0 (cylinderGreen Ls mass hmass f f).toNNReal := by
  simpa [cylinderGreen] using
    (GaussianField.pairing_is_gaussian
      (GaussianField.cylinderMassOperator Ls mass hmass) f)

/-- The free cylinder Gaussian reproduces `cylinderGreen` as its second moment on the
diagonal. This is the cylinder analogue of the covariance identities used in the torus
continuum limit. -/
theorem cylinderFreeMeasure_secondMoment_eq_cylinderGreen
    (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction Ls) :
    ∫ ω, (ω f) ^ 2 ∂(GaussianField.measure
        (GaussianField.cylinderMassOperator Ls mass hmass)) =
    cylinderGreen Ls mass hmass f f := by
  rw [GaussianField.second_moment_eq_covariance
      (GaussianField.cylinderMassOperator Ls mass hmass) f]
  simp [cylinderGreen]

/-- If a torus measure is Gaussian in the MGF sense, then its cylinder pullback is also
Gaussian. -/
theorem cylinderPullback_isGaussian_of_torusGaussian
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (hμ_gauss : ∀ g : AsymTorusTestFunction Lt Ls,
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), Real.exp (ω g) ∂μ =
        Real.exp ((1 / 2) * ∫ ω, (ω g) ^ 2 ∂μ))
    (f : CylinderTestFunction Ls) :
    ∫ ω : Configuration (CylinderTestFunction Ls), Real.exp (ω f) ∂
        (cylinderPullbackMeasure Lt Ls μ) =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂(cylinderPullbackMeasure Lt Ls μ)) := by
  unfold cylinderPullbackMeasure
  have hmeas : Measurable (cylinderPullback Lt Ls) :=
    configuration_measurable_of_eval_measurable _
      (fun φ => configuration_eval_measurable _)
  have h_exp_sm : AEStronglyMeasurable
      (fun ω : Configuration (CylinderTestFunction Ls) => Real.exp (ω f))
      (Measure.map (cylinderPullback Lt Ls) μ) :=
    (Real.measurable_exp.comp (configuration_eval_measurable f)).aestronglyMeasurable
  rw [integral_map hmeas.aemeasurable h_exp_sm]
  simp_rw [cylinderPullback_eval]
  rw [hμ_gauss (cylinderToTorusEmbed Lt Ls f)]
  congr 1
  rw [← cylinderPullbackMeasure_integral_sq Lt Ls μ f]
  simp [cylinderPullbackMeasure]

/-- If a torus measure has diagonal covariance `asymTorusContinuumGreen`, then the pulled-back
cylinder measure has diagonal covariance given by the same torus Green form on embedded test
functions. -/
theorem cylinderPullback_secondMoment_eq_asymTorusGreen
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    (mass : ℝ) (hmass : 0 < mass)
    (hμ_cov : ∀ g : AsymTorusTestFunction Lt Ls,
      ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), (ω g) ^ 2 ∂μ =
        asymTorusContinuumGreen Lt Ls mass hmass g g)
    (f : CylinderTestFunction Ls) :
    ∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂
        (cylinderPullbackMeasure Lt Ls μ) =
      asymTorusContinuumGreen Lt Ls mass hmass
        (cylinderToTorusEmbed Lt Ls f) (cylinderToTorusEmbed Lt Ls f) := by
  rw [cylinderPullbackMeasure_integral_sq Lt Ls μ f,
    hμ_cov (cylinderToTorusEmbed Lt Ls f)]

/-! ## Exponential convergence rate

The mass gap `m > 0` gives exponential convergence of the periodic Green's
function to the non-periodic one. The scalar 1D estimates live in
`PeriodicResolvent1D` (`periodicKernel`, `freeKernel`, and lemmas such as
`PeriodicResolvent1D.abs_sub_free_le`).

The `Pphi2.periodicResolvent_*` theorems below restate the same bounds in
expanded form for compatibility with the mixed spectral representation
`cosh(ω(Lt/2-|t|))/(2ω sinh(ωLt/2))` used in the torus Green's function. -/

/-- The 1D periodic resolvent converges exponentially to the free resolvent.

For ω > 0:
  `|cosh(ω(Lt/2 - |t|))/(2ω sinh(ωLt/2)) - e^{-ω|t|}/(2ω)|
    ≤ e^{-ω(Lt - |t|)} / (ω(1 - e^{-ω Lt}))`

See `PeriodicResolvent1D.abs_sub_free_le`. -/
theorem periodicResolvent_convergence_rate
    (ω : ℝ) (hω : 0 < ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) :
    |Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
     Real.exp (-ω * |t|) / (2 * ω)| ≤
    Real.exp (-ω * (Lt - |t|)) /
      (ω * (1 - Real.exp (-ω * Lt))) := by
  simpa [periodicKernel, freeKernel] using abs_sub_free_le ω hω t Lt hLt

/-- Uniform half-period decay; see `PeriodicResolvent1D.abs_sub_free_le_on_halfPeriodStrip`. -/
theorem periodicResolvent_convergence_rate_uniform
    (ω : ℝ) (hω : 0 < ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) (ht : |t| < Lt / 2) :
    |Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
      Real.exp (-ω * |t|) / (2 * ω)| ≤
    Real.exp (-ω * Lt / 2) /
      (ω * (1 - Real.exp (-ω * Lt))) := by
  simpa [periodicKernel, freeKernel] using
    abs_sub_free_le_on_halfPeriodStrip ω hω t Lt hLt ht

/-- Uniform mass-gap control; see `PeriodicResolvent1D.abs_sub_free_le_uniform_mass_gap`. -/
theorem periodicResolvent_convergence_rate_uniform_mass_gap
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) (ht : |t| < Lt / 2) :
    |Real.cosh (ω * (Lt / 2 - |t|)) / (2 * ω * Real.sinh (ω * Lt / 2)) -
      Real.exp (-ω * |t|) / (2 * ω)| ≤
    Real.exp (-mass * Lt / 2) /
      (mass * (1 - Real.exp (-mass * Lt))) := by
  simpa [periodicKernel, freeKernel] using
    abs_sub_free_le_uniform_mass_gap ω mass hmass hω t Lt hLt ht

omit hLs in
/-- Specialization of the uniform mass-gap bound to cylinder frequencies
`ω_n = resolventFreq Ls mass n`. -/
theorem periodicResolvent_resolventFreq_convergence_rate_uniform
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ)
    (t : ℝ) (Lt : ℝ) (hLt : 0 < Lt) (ht : |t| < Lt / 2) :
    |Real.cosh (resolventFreq Ls mass n * (Lt / 2 - |t|)) /
        (2 * resolventFreq Ls mass n * Real.sinh (resolventFreq Ls mass n * Lt / 2)) -
      Real.exp (-resolventFreq Ls mass n * |t|) / (2 * resolventFreq Ls mass n)| ≤
    Real.exp (-mass * Lt / 2) /
      (mass * (1 - Real.exp (-mass * Lt))) := by
  simpa [periodicKernel, freeKernel] using
    abs_sub_free_le_uniform_mass_gap
      (ω := resolventFreq Ls mass n) (mass := mass) hmass
      (resolventFreq_mass_le Ls mass hmass.le n) t Lt hLt ht

/-- For fixed `ω > 0` and `t`, the periodic 1D resolvent kernel converges to the free resolvent
kernel as `Lt → ∞`. See `PeriodicResolvent1D.tendsto_periodicKernel_freeKernel`. -/
theorem periodicResolvent_tendsto_free
    (ω : ℝ) (hω : 0 < ω) (t : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto
      (fun n =>
        Real.cosh (ω * (Lt n / 2 - |t|)) /
          (2 * ω * Real.sinh (ω * Lt n / 2)))
      atTop (nhds (Real.exp (-ω * |t|) / (2 * ω))) := by
  simpa [periodicKernel, freeKernel] using
    tendsto_periodicKernel_freeKernel ω hω t Lt hLt hLt_tend

/-- Uniform-on-compact convergence of the periodic resolvent to the free resolvent, with
the compact-window control depending only on a mass gap `mass ≤ ω`. -/
theorem periodicResolvent_tendsto_free_uniformOn_compact_mass_gap
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω)
    (R : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun n t =>
        Real.cosh (ω * (Lt n / 2 - |t|)) /
          (2 * ω * Real.sinh (ω * Lt n / 2)))
      (fun t => Real.exp (-ω * |t|) / (2 * ω))
      atTop (Set.Icc (-R) R) := by
  simpa [periodicKernel, freeKernel] using
    tendstoUniformlyOn_periodicKernel_freeKernel_compact_of_mass_gap
      ω mass hmass hω R Lt hLt hLt_tend

/-- Fixed-frequency compact-window uniform convergence. -/
theorem periodicResolvent_tendsto_free_uniformOn_compact
    (ω : ℝ) (hω : 0 < ω)
    (R : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun n t =>
        Real.cosh (ω * (Lt n / 2 - |t|)) /
          (2 * ω * Real.sinh (ω * Lt n / 2)))
      (fun t => Real.exp (-ω * |t|) / (2 * ω))
      atTop (Set.Icc (-R) R) := by
  simpa [periodicKernel, freeKernel] using
    tendstoUniformlyOn_periodicKernel_freeKernel_compact
      ω hω R Lt hLt hLt_tend

omit hLs in
/-- Compact-window specialization of `periodicResolvent_tendsto_free_uniformOn_compact_mass_gap`
to the cylinder frequencies `ω_n = resolventFreq Ls mass n`. -/
theorem periodicResolvent_resolventFreq_tendsto_free_uniformOn_compact
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ)
    (R : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun k t =>
        Real.cosh (resolventFreq Ls mass n * (Lt k / 2 - |t|)) /
          (2 * resolventFreq Ls mass n * Real.sinh (resolventFreq Ls mass n * Lt k / 2)))
      (fun t => Real.exp (-resolventFreq Ls mass n * |t|) / (2 * resolventFreq Ls mass n))
      atTop (Set.Icc (-R) R) := by
  simpa [periodicKernel, freeKernel] using
    tendstoUniformlyOn_periodicKernel_freeKernel_compact_of_mass_gap
      (ω := resolventFreq Ls mass n) (mass := mass) hmass
      (resolventFreq_mass_le Ls mass hmass.le n) R Lt hLt hLt_tend

/-- Two-variable compact-box version of
`periodicResolvent_tendsto_free_uniformOn_compact_mass_gap`, pulled back along
`(t, s) ↦ t - s`. -/
theorem periodicResolvent_tendsto_free_uniformOn_compactDiffBox_mass_gap
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω)
    (R : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun k (p : ℝ × ℝ) =>
        Real.cosh (ω * (Lt k / 2 - |p.1 - p.2|)) /
          (2 * ω * Real.sinh (ω * Lt k / 2)))
      (fun p => Real.exp (-ω * |p.1 - p.2|) / (2 * ω))
      atTop (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) := by
  simpa [periodicKernel, freeKernel] using
    tendstoUniformlyOn_periodicKernel_freeKernel_compactDiffBox_of_mass_gap
      ω mass hmass hω R Lt hLt hLt_tend

omit hLs in
/-- Cylinder-frequency specialization of
`periodicResolvent_tendsto_free_uniformOn_compactDiffBox_mass_gap`. -/
theorem periodicResolvent_resolventFreq_tendsto_free_uniformOn_compactDiffBox
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ)
    (R : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun k (p : ℝ × ℝ) =>
        Real.cosh (resolventFreq Ls mass n * (Lt k / 2 - |p.1 - p.2|)) /
          (2 * resolventFreq Ls mass n * Real.sinh (resolventFreq Ls mass n * Lt k / 2)))
      (fun p =>
        Real.exp (-resolventFreq Ls mass n * |p.1 - p.2|) / (2 * resolventFreq Ls mass n))
      atTop (Set.Icc (-R) R ×ˢ Set.Icc (-R) R) := by
  simpa [periodicKernel, freeKernel] using
    tendstoUniformlyOn_periodicKernel_freeKernel_compactDiffBox_of_mass_gap
      (ω := resolventFreq Ls mass n) (mass := mass) hmass
      (resolventFreq_mass_le Ls mass hmass.le n) R Lt hLt hLt_tend

omit hLs in
/-- Compact-support pure-temporal convergence on the support box.

If `h₁, h₂ : 𝓢(ℝ)` vanish outside `[-T, T]`, then on the box `[-T, T]²` their periodizations are
eventually equal to the original functions, so the only remaining convergence is the periodic/free
kernel convergence in the difference variable. This is the temporal core of the pure-tensor
torus-to-cylinder Green convergence argument. -/
theorem periodizedSchwartz_mul_periodicKernel_tendsto_freeKernel_uniformOn_compactDiffBox
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun k (p : ℝ × ℝ) =>
        ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
          (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
          periodicKernel ω (Lt k) (p.1 - p.2))
      (fun p => (h₁ p.1 * h₂ p.2) * freeKernel ω (p.1 - p.2))
      atTop (Set.Icc (-T) T ×ˢ Set.Icc (-T) T) := by
  let K : Set (ℝ × ℝ) := Set.Icc (-T) T ×ˢ Set.Icc (-T) T
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hper₁ :
      TendstoUniformlyOn
        (fun k t => (@periodizeCLM (Lt k) (hLt k) h₁).toFun t)
        h₁ atTop (Set.Icc (-T) T) :=
    periodizeCLM_tendsto_uniformlyOn_symmetricCompact
      h₁ T hT hsupp₁ Lt hLt hLt_tend
  have hper₂ :
      TendstoUniformlyOn
        (fun k t => (@periodizeCLM (Lt k) (hLt k) h₂).toFun t)
        h₂ atTop (Set.Icc (-T) T) :=
    periodizeCLM_tendsto_uniformlyOn_symmetricCompact
      h₂ T hT hsupp₂ Lt hLt hLt_tend
  have hper₁_box :
      TendstoUniformlyOn
        (fun k (p : ℝ × ℝ) => (@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1)
        (fun p => h₁ p.1) atTop K := by
    refine (hper₁.comp Prod.fst).mono ?_
    intro p hp
    exact hp.1
  have hper₂_box :
      TendstoUniformlyOn
        (fun k (p : ℝ × ℝ) => (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2)
        (fun p => h₂ p.2) atTop K := by
    refine (hper₂.comp Prod.snd).mono ?_
    intro p hp
    exact hp.2
  have hkernel :
      TendstoUniformlyOn
        (fun k (p : ℝ × ℝ) => periodicKernel ω (Lt k) (p.1 - p.2))
        (fun p => freeKernel ω (p.1 - p.2))
        atTop K :=
    tendstoUniformlyOn_periodicKernel_freeKernel_compactDiffBox_of_mass_gap
      ω mass hmass hω T Lt hLt hLt_tend
  have hper₁_cont : ContinuousOn (fun p : ℝ × ℝ => h₁ p.1) K := by
    exact (h₁.continuous.comp continuous_fst).continuousOn
  have hper₂_cont : ContinuousOn (fun p : ℝ × ℝ => h₂ p.2) K := by
    exact (h₂.continuous.comp continuous_snd).continuousOn
  have hkernel_cont : ContinuousOn (fun p : ℝ × ℝ => freeKernel ω (p.1 - p.2)) K := by
    exact ((continuous_freeKernel ω).comp (continuous_fst.sub continuous_snd)).continuousOn
  have hprod_loc :
      TendstoLocallyUniformlyOn
        (fun k (p : ℝ × ℝ) =>
          (@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
            (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2)
        (fun p => h₁ p.1 * h₂ p.2)
        atTop K := by
    exact hper₁_box.tendstoLocallyUniformlyOn.mul₀
      hper₂_box.tendstoLocallyUniformlyOn hper₁_cont hper₂_cont
  have hfull_loc :
      TendstoLocallyUniformlyOn
        (fun k (p : ℝ × ℝ) =>
          ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
            (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
            periodicKernel ω (Lt k) (p.1 - p.2))
        (fun p => (h₁ p.1 * h₂ p.2) * freeKernel ω (p.1 - p.2))
        atTop K := by
    exact hprod_loc.mul₀ hkernel.tendstoLocallyUniformlyOn
      (hper₁_cont.mul hper₂_cont) hkernel_cont
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK_compact).mp hfull_loc

omit hLs in
/-- Integrating the compact-support pure-temporal convergence over the support box yields
convergence of the corresponding temporal bilinear forms. This is the dominated-convergence
step in the pure-tensor torus-to-cylinder Green comparison. -/
theorem periodizedSchwartz_mul_periodicKernel_tendsto_freeKernel_integralOn_compactDiffBox
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto
      (fun k =>
        ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
            (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
            periodicKernel ω (Lt k) (p.1 - p.2) ∂volume)
      atTop
      (nhds (∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
        (h₁ p.1 * h₂ p.2) * freeKernel ω (p.1 - p.2) ∂volume)) := by
  let K : Set (ℝ × ℝ) := Set.Icc (-T) T ×ˢ Set.Icc (-T) T
  let F : ℕ → ℝ × ℝ → ℝ := fun k p =>
    ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
      (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
      periodicKernel ω (Lt k) (p.1 - p.2)
  let F_lim : ℝ × ℝ → ℝ := fun p =>
    (h₁ p.1 * h₂ p.2) * freeKernel ω (p.1 - p.2)
  have hunif :
      TendstoUniformlyOn F F_lim atTop K := by
    simpa [F, F_lim, K] using
      periodizedSchwartz_mul_periodicKernel_tendsto_freeKernel_uniformOn_compactDiffBox
        (h₁ := h₁) (h₂ := h₂) T hT hsupp₁ hsupp₂ ω mass hmass hω Lt hLt hLt_tend
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  haveI : IsFiniteMeasure (volume.restrict K) := by
    refine ⟨?_⟩
    simpa [Measure.restrict_apply, hK_meas, K] using hK_compact.measure_lt_top (μ := volume)
  have hF_cont : ∀ k, Continuous (F k) := by
    intro k
    have hper₁ :
        Continuous (fun p : ℝ × ℝ => (@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1) :=
      ((@periodizeCLM (Lt k) (hLt k) h₁).continuous.comp continuous_fst)
    have hper₂ :
        Continuous (fun p : ℝ × ℝ => (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) :=
      ((@periodizeCLM (Lt k) (hLt k) h₂).continuous.comp continuous_snd)
    have hkernel :
        Continuous (fun p : ℝ × ℝ => periodicKernel ω (Lt k) (p.1 - p.2)) :=
      (continuous_periodicKernel ω (Lt k)).comp (continuous_fst.sub continuous_snd)
    simpa [F] using (hper₁.mul hper₂).mul hkernel
  have hF_meas :
      ∀ᶠ k in atTop, AEStronglyMeasurable (F k) (volume.restrict K) := by
    exact Eventually.of_forall fun k =>
      (hF_cont k).stronglyMeasurable.aestronglyMeasurable
  have hF_lim_cont : ContinuousOn F_lim K := by
    have hper₁_cont : ContinuousOn (fun p : ℝ × ℝ => h₁ p.1) K := by
      exact (h₁.continuous.comp continuous_fst).continuousOn
    have hper₂_cont : ContinuousOn (fun p : ℝ × ℝ => h₂ p.2) K := by
      exact (h₂.continuous.comp continuous_snd).continuousOn
    have hkernel_cont : ContinuousOn (fun p : ℝ × ℝ => freeKernel ω (p.1 - p.2)) K := by
      exact ((continuous_freeKernel ω).comp (continuous_fst.sub continuous_snd)).continuousOn
    simpa [F_lim] using (hper₁_cont.mul hper₂_cont).mul hkernel_cont
  obtain ⟨C0, hC0_image⟩ : ∃ C, ∀ y ∈ F_lim '' K, ‖y‖ ≤ C :=
    Bornology.IsBounded.exists_norm_le (hK_compact.image_of_continuousOn hF_lim_cont).isBounded
  have hC0 : ∀ p ∈ K, ‖F_lim p‖ ≤ C0 := by
    intro p hp
    exact hC0_image _ (Set.mem_image_of_mem F_lim hp)
  have h_bound :
      ∃ C, ∀ᶠ k in atTop, (∀ᵐ p ∂(volume.restrict K), ‖F k p‖ ≤ C) := by
    refine ⟨C0 + 1, ?_⟩
    have hsmall : ∀ᶠ k in atTop, ∀ p ∈ K, dist (F k p) (F_lim p) < 1 := by
      filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hunif) 1 zero_lt_one] with k hk p hp
      simpa [dist_comm] using hk p hp
    filter_upwards [hsmall] with k hk
    refine (ae_restrict_mem hK_meas).mono ?_
    intro p hp
    have hk' := hk p hp
    have hdist : ‖F k p - F_lim p‖ < 1 := by
      simpa [Real.dist_eq, Real.norm_eq_abs] using hk'
    have hC0' := hC0 p hp
    calc
      ‖F k p‖ = ‖(F k p - F_lim p) + F_lim p‖ := by
        congr 1
        ring
      _ ≤ ‖F k p - F_lim p‖ + ‖F_lim p‖ := norm_add_le _ _
      _ ≤ C0 + 1 := by
        linarith
  have h_pointwise : ∀ p ∈ K, Tendsto (fun k => F k p) atTop (nhds (F_lim p)) := by
    intro p hp
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hunif ε hε)] with k hk
    simpa [dist_comm] using hk p hp
  have h_lim : ∀ᵐ p ∂(volume.restrict K), Tendsto (fun k => F k p) atTop (nhds (F_lim p)) := by
    exact (ae_restrict_mem hK_meas).mono fun p hp => h_pointwise p hp
  have h_tend :
      Tendsto (fun k => ∫ p, F k p ∂(volume.restrict K)) atTop
        (nhds (∫ p, F_lim p ∂(volume.restrict K))) := by
    exact tendsto_integral_filter_of_norm_le_const
      (μ := volume.restrict K) hF_meas h_bound h_lim
  simpa [K, F, F_lim] using h_tend

omit hLs in
/-- The compact-support temporal convergence theorem specialized to the cylinder frequencies
`ω_n = resolventFreq Ls mass n`, written in expanded resolvent form. -/
theorem periodizedSchwartz_mul_resolventFreq_tendsto_free_uniformOn_compactDiffBox
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop) :
    TendstoUniformlyOn
      (fun k (p : ℝ × ℝ) =>
        ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
          (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
          (Real.cosh (resolventFreq Ls mass n * (Lt k / 2 - |p.1 - p.2|)) /
            (2 * resolventFreq Ls mass n * Real.sinh (resolventFreq Ls mass n * Lt k / 2))))
      (fun p =>
        (h₁ p.1 * h₂ p.2) *
          (Real.exp (-resolventFreq Ls mass n * |p.1 - p.2|) /
            (2 * resolventFreq Ls mass n)))
      atTop (Set.Icc (-T) T ×ˢ Set.Icc (-T) T) := by
  simpa [periodicKernel, freeKernel] using
    periodizedSchwartz_mul_periodicKernel_tendsto_freeKernel_uniformOn_compactDiffBox
      (h₁ := h₁) (h₂ := h₂) T hT hsupp₁ hsupp₂
      (ω := resolventFreq Ls mass n) (mass := mass) hmass
      (resolventFreq_mass_le Ls mass hmass.le n) Lt hLt hLt_tend

omit hLs in
/-- Integrating the cylinder-frequency specialization over the support box yields convergence of the
corresponding temporal bilinear forms. -/
theorem periodizedSchwartz_mul_resolventFreq_tendsto_free_integralOn_compactDiffBox
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto
      (fun k =>
        ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
            (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
            (Real.cosh (resolventFreq Ls mass n * (Lt k / 2 - |p.1 - p.2|)) /
              (2 * resolventFreq Ls mass n * Real.sinh (resolventFreq Ls mass n * Lt k / 2)))
          ∂volume)
      atTop
      (nhds (∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
        (h₁ p.1 * h₂ p.2) *
          (Real.exp (-resolventFreq Ls mass n * |p.1 - p.2|) /
            (2 * resolventFreq Ls mass n)) ∂volume)) := by
  simpa [periodicKernel, freeKernel] using
    periodizedSchwartz_mul_periodicKernel_tendsto_freeKernel_integralOn_compactDiffBox
      (h₁ := h₁) (h₂ := h₂) T hT hsupp₁ hsupp₂
      (ω := resolventFreq Ls mass n) (mass := mass) hmass
      (resolventFreq_mass_le Ls mass hmass.le n) Lt hLt hLt_tend

private theorem integral_exp_mul_cos
    (σ α a b : ℝ) (hden : σ ^ 2 + α ^ 2 ≠ 0) :
    ∫ x in a..b, Real.exp (σ * x) * Real.cos (α * x) =
      (Real.exp (σ * b) * (σ * Real.cos (α * b) + α * Real.sin (α * b)) -
        Real.exp (σ * a) * (σ * Real.cos (α * a) + α * Real.sin (α * a))) /
        (σ ^ 2 + α ^ 2) := by
  let F : ℝ → ℝ := fun x =>
    (Real.exp (σ * x) * (σ * Real.cos (α * x) + α * Real.sin (α * x))) /
      (σ ^ 2 + α ^ 2)
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (Real.exp (σ * x) * Real.cos (α * x)) x := by
    intro x hx
    have hExp : HasDerivAt (fun y : ℝ => Real.exp (σ * y)) (σ * Real.exp (σ * x)) x := by
      simpa [mul_comm] using
        (Real.hasDerivAt_exp (σ * x)).comp x ((hasDerivAt_id x).const_mul σ)
    have hCos : HasDerivAt (fun y : ℝ => σ * Real.cos (α * y))
        (σ * (-α * Real.sin (α * x))) x := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (((Real.hasDerivAt_cos (α * x)).comp x ((hasDerivAt_id x).const_mul α)).const_mul σ)
    have hSin : HasDerivAt (fun y : ℝ => α * Real.sin (α * y))
        (α * (α * Real.cos (α * x))) x := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (((Real.hasDerivAt_sin (α * x)).comp x ((hasDerivAt_id x).const_mul α)).const_mul α)
    have hTrig : HasDerivAt (fun y : ℝ => σ * Real.cos (α * y) + α * Real.sin (α * y))
        (-σ * α * Real.sin (α * x) + α ^ 2 * Real.cos (α * x)) x := by
      convert hCos.add hSin using 1
      ring
    have hMul : HasDerivAt
        (fun y : ℝ => Real.exp (σ * y) * (σ * Real.cos (α * y) + α * Real.sin (α * y)))
        (Real.exp (σ * x) * ((σ ^ 2 + α ^ 2) * Real.cos (α * x))) x := by
      convert hExp.mul hTrig using 1
      ring
    have hDiv : HasDerivAt F
        ((Real.exp (σ * x) * ((σ ^ 2 + α ^ 2) * Real.cos (α * x))) /
          (σ ^ 2 + α ^ 2)) x := by
      simpa [F] using hMul.div_const (σ ^ 2 + α ^ 2)
    convert hDiv using 1
    field_simp [hden]
  have hint : IntervalIntegrable (fun x => Real.exp (σ * x) * Real.cos (α * x)) volume a b := by
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [F]
  field_simp [hden]

private theorem integral_exp_mul_sin
    (σ α a b : ℝ) (hden : σ ^ 2 + α ^ 2 ≠ 0) :
    ∫ x in a..b, Real.exp (σ * x) * Real.sin (α * x) =
      (Real.exp (σ * b) * (σ * Real.sin (α * b) - α * Real.cos (α * b)) -
        Real.exp (σ * a) * (σ * Real.sin (α * a) - α * Real.cos (α * a))) /
        (σ ^ 2 + α ^ 2) := by
  let F : ℝ → ℝ := fun x =>
    (Real.exp (σ * x) * (σ * Real.sin (α * x) - α * Real.cos (α * x))) /
      (σ ^ 2 + α ^ 2)
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (Real.exp (σ * x) * Real.sin (α * x)) x := by
    intro x hx
    have hExp : HasDerivAt (fun y : ℝ => Real.exp (σ * y)) (σ * Real.exp (σ * x)) x := by
      simpa [mul_comm] using
        (Real.hasDerivAt_exp (σ * x)).comp x ((hasDerivAt_id x).const_mul σ)
    have hSin : HasDerivAt (fun y : ℝ => σ * Real.sin (α * y))
        (σ * (α * Real.cos (α * x))) x := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (((Real.hasDerivAt_sin (α * x)).comp x ((hasDerivAt_id x).const_mul α)).const_mul σ)
    have hCos : HasDerivAt (fun y : ℝ => α * Real.cos (α * y))
        (α * (-α * Real.sin (α * x))) x := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (((Real.hasDerivAt_cos (α * x)).comp x ((hasDerivAt_id x).const_mul α)).const_mul α)
    have hTrig : HasDerivAt (fun y : ℝ => σ * Real.sin (α * y) - α * Real.cos (α * y))
        (σ * α * Real.cos (α * x) + α ^ 2 * Real.sin (α * x)) x := by
      convert hSin.sub hCos using 1
      ring
    have hMul : HasDerivAt
        (fun y : ℝ => Real.exp (σ * y) * (σ * Real.sin (α * y) - α * Real.cos (α * y)))
        (Real.exp (σ * x) * ((σ ^ 2 + α ^ 2) * Real.sin (α * x))) x := by
      convert hExp.mul hTrig using 1
      ring
    have hDiv : HasDerivAt F
        ((Real.exp (σ * x) * ((σ ^ 2 + α ^ 2) * Real.sin (α * x))) /
          (σ ^ 2 + α ^ 2)) x := by
      simpa [F] using hMul.div_const (σ ^ 2 + α ^ 2)
    convert hDiv using 1
    field_simp [hden]
  have hint : IntervalIntegrable (fun x => Real.exp (σ * x) * Real.sin (α * x)) volume a b := by
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable a b
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp [F]
  field_simp [hden]

private theorem periodicKernel_eq_freeKernel_add_wrap
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) Lt) :
    periodicKernel ω Lt x =
      freeKernel ω x +
        (Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) /
          (2 * ω * (1 - Real.exp (-ω * Lt))) := by
  have hx_nonneg : 0 ≤ x := hx.1
  have hwrap := sub_free_eq_wrapAround ω hω x Lt hLt
  have hadd := congrArg (fun z : ℝ => z + freeKernel ω x) hwrap
  simpa [freeKernel, abs_of_nonneg hx_nonneg, add_comm, add_left_comm, add_assoc] using hadd

private theorem periodicKernel_sub_eq
    (ω Lt : ℝ) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) Lt) :
    periodicKernel ω Lt (Lt - u) = periodicKernel ω Lt u := by
  have hu_nonneg : 0 ≤ u := hu.1
  have hu_le : u ≤ Lt := hu.2
  unfold periodicKernel
  rw [abs_of_nonneg (sub_nonneg.mpr hu_le), abs_of_nonneg hu_nonneg]
  rw [show ω * (Lt / 2 - (Lt - u)) = -(ω * (Lt / 2 - u)) by ring]
  rw [Real.cosh_neg]

private theorem integral_exp_neg_mul_cos_circleFreq
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt) (k : ℕ) :
    ∫ x in (0 : ℝ)..Lt,
      Real.exp (-ω * x) * Real.cos ((2 * Real.pi * k / Lt) * x) =
      (-Real.exp (-ω * Lt) * ω + ω) /
        (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2) := by
  let α : ℝ := 2 * Real.pi * k / Lt
  have hden_pos : 0 < (-ω : ℝ) ^ 2 + α ^ 2 := by
    nlinarith [sq_pos_of_pos hω, sq_nonneg α]
  have hden : (-ω : ℝ) ^ 2 + α ^ 2 ≠ 0 := hden_pos.ne'
  have hLt_ne : Lt ≠ 0 := hLt.ne'
  have hαLt : α * Lt = k * (2 * Real.pi) := by
    dsimp [α]
    field_simp [hLt_ne]
  have hI := integral_exp_mul_cos (-ω) α 0 Lt hden
  have hsin : Real.sin (k * (2 * Real.pi)) = 0 := by
    simpa using (Real.sin_nat_mul_two_pi_sub (x := (0 : ℝ)) k)
  rw [hαLt, Real.cos_nat_mul_two_pi, hsin] at hI
  simpa [α] using hI

private theorem integral_exp_neg_mul_sin_circleFreq
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt) (k : ℕ) :
    ∫ x in (0 : ℝ)..Lt,
      Real.exp (-ω * x) * Real.sin ((2 * Real.pi * k / Lt) * x) =
      (-Real.exp (-ω * Lt) * (2 * Real.pi * k / Lt) + (2 * Real.pi * k / Lt)) /
        (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2) := by
  let α : ℝ := 2 * Real.pi * k / Lt
  have hden_pos : 0 < (-ω : ℝ) ^ 2 + α ^ 2 := by
    nlinarith [sq_pos_of_pos hω, sq_nonneg α]
  have hden : (-ω : ℝ) ^ 2 + α ^ 2 ≠ 0 := hden_pos.ne'
  have hLt_ne : Lt ≠ 0 := hLt.ne'
  have hαLt : α * Lt = k * (2 * Real.pi) := by
    dsimp [α]
    field_simp [hLt_ne]
  have hI := integral_exp_mul_sin (-ω) α 0 Lt hden
  have hsin : Real.sin (k * (2 * Real.pi)) = 0 := by
    simpa using (Real.sin_nat_mul_two_pi_sub (x := (0 : ℝ)) k)
  rw [hαLt, Real.cos_nat_mul_two_pi, hsin] at hI
  simpa [α] using hI

private theorem integral_exp_pos_mul_cos_circleFreq
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt) (k : ℕ) :
    ∫ x in (0 : ℝ)..Lt,
      Real.exp (ω * x) * Real.cos ((2 * Real.pi * k / Lt) * x) =
      (Real.exp (ω * Lt) * ω - ω) /
        (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2) := by
  let α : ℝ := 2 * Real.pi * k / Lt
  have hden_pos : 0 < (ω : ℝ) ^ 2 + α ^ 2 := by
    nlinarith [sq_pos_of_pos hω, sq_nonneg α]
  have hden : (ω : ℝ) ^ 2 + α ^ 2 ≠ 0 := hden_pos.ne'
  have hLt_ne : Lt ≠ 0 := hLt.ne'
  have hαLt : α * Lt = k * (2 * Real.pi) := by
    dsimp [α]
    field_simp [hLt_ne]
  have hI := integral_exp_mul_cos ω α 0 Lt hden
  have hsin : Real.sin (k * (2 * Real.pi)) = 0 := by
    simpa using (Real.sin_nat_mul_two_pi_sub (x := (0 : ℝ)) k)
  rw [hαLt, Real.cos_nat_mul_two_pi, hsin] at hI
  simpa [α] using hI

private theorem integral_exp_pos_mul_sin_circleFreq
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt) (k : ℕ) :
    ∫ x in (0 : ℝ)..Lt,
      Real.exp (ω * x) * Real.sin ((2 * Real.pi * k / Lt) * x) =
      (-Real.exp (ω * Lt) * (2 * Real.pi * k / Lt) + (2 * Real.pi * k / Lt)) /
        (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2) := by
  let α : ℝ := 2 * Real.pi * k / Lt
  have hden_pos : 0 < (ω : ℝ) ^ 2 + α ^ 2 := by
    nlinarith [sq_pos_of_pos hω, sq_nonneg α]
  have hden : (ω : ℝ) ^ 2 + α ^ 2 ≠ 0 := hden_pos.ne'
  have hLt_ne : Lt ≠ 0 := hLt.ne'
  have hαLt : α * Lt = k * (2 * Real.pi) := by
    dsimp [α]
    field_simp [hLt_ne]
  have hI := integral_exp_mul_sin ω α 0 Lt hden
  have hsin : Real.sin (k * (2 * Real.pi)) = 0 := by
    simpa using (Real.sin_nat_mul_two_pi_sub (x := (0 : ℝ)) k)
  rw [hαLt, Real.cos_nat_mul_two_pi, hsin] at hI
  simpa [α] using hI

private theorem integral_periodicKernel_mul_cos_circleFreq
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt) (k : ℕ) :
    ∫ x in (0 : ℝ)..Lt, periodicKernel ω Lt x * Real.cos ((2 * Real.pi * k / Lt) * x) =
      (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2)⁻¹ := by
  let a : ℝ := 2 * Real.pi * k / Lt
  let q : ℝ := Real.exp (-ω * Lt)
  let C : ℝ := 2 * ω * (1 - q)
  let D : ℝ := ω ^ 2 + a ^ 2
  have hω_ne : ω ≠ 0 := hω.ne'
  have hq_lt_one : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith
  have h1q_ne : 1 - q ≠ 0 := sub_ne_zero.mpr hq_lt_one.ne.symm
  have hC_ne : C ≠ 0 := by
    dsimp [C]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hω_ne) h1q_ne
  have hD_pos : 0 < D := by
    dsimp [D]
    nlinarith [sq_pos_of_pos hω, sq_nonneg a]
  have hD_ne : D ≠ 0 := hD_pos.ne'
  have hfree_int : IntervalIntegrable (fun x => freeKernel ω x * Real.cos (a * x)) volume 0 Lt := by
    exact ((continuous_freeKernel ω).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 Lt
  have hwrap_int : IntervalIntegrable
      (fun x =>
        ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.cos (a * x))
      volume 0 Lt := by
    have hcont :
        Continuous (fun x : ℝ =>
          ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.cos (a * x)) := by
      fun_prop
    exact hcont.intervalIntegrable 0 Lt
  have hsplit :
      ∫ x in (0 : ℝ)..Lt, periodicKernel ω Lt x * Real.cos (a * x) =
        ∫ x in (0 : ℝ)..Lt,
          (freeKernel ω x * Real.cos (a * x)) +
            (((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) *
              Real.cos (a * x)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) Lt := by
      simpa [Set.uIcc_of_le hLt.le] using hx
    have hpk := periodicKernel_eq_freeKernel_add_wrap ω Lt hω hLt hxI
    dsimp [C, q]
    rw [hpk]
    ring_nf
  have hfree :
      ∫ x in (0 : ℝ)..Lt, freeKernel ω x * Real.cos (a * x) =
        (2 * ω : ℝ)⁻¹ * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) Lt := by
      simpa [Set.uIcc_of_le hLt.le] using hx
    simp [freeKernel, abs_of_nonneg hxI.1, div_eq_mul_inv]
    ring
  have hInt1 : IntervalIntegrable
      (fun x => Real.exp (-ω * (Lt - x)) * Real.cos (a * x)) volume 0 Lt := by
    have hcont :
        Continuous (fun x : ℝ => Real.exp (-ω * (Lt - x)) * Real.cos (a * x)) := by
      fun_prop
    exact hcont.intervalIntegrable 0 Lt
  have hInt2 : IntervalIntegrable
      (fun x => Real.exp (-ω * (Lt + x)) * Real.cos (a * x)) volume 0 Lt := by
    have hcont :
        Continuous (fun x : ℝ => Real.exp (-ω * (Lt + x)) * Real.cos (a * x)) := by
      fun_prop
    exact hcont.intervalIntegrable 0 Lt
  have hA :
      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt - x)) * Real.cos (a * x) =
        q * (∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.cos (a * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [q]
    rw [show -ω * (Lt - x) = -ω * Lt + ω * x by ring, Real.exp_add]
    ring
  have hB :
      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt + x)) * Real.cos (a * x) =
        q * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [q]
    rw [show -ω * (Lt + x) = -ω * Lt + -ω * x by ring, Real.exp_add]
    ring
  have hwrap :
      ∫ x in (0 : ℝ)..Lt,
        ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.cos (a * x) =
      C⁻¹ *
        ((q * (∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.cos (a * x))) +
          q * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x))) := by
    calc
      ∫ x in (0 : ℝ)..Lt,
          ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.cos (a * x)
        = C⁻¹ * ∫ x in (0 : ℝ)..Lt,
            (Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) * Real.cos (a * x) := by
              rw [← intervalIntegral.integral_const_mul]
              apply intervalIntegral.integral_congr
              intro x hx
              field_simp [hC_ne]
      _ = C⁻¹ *
            ((∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt - x)) * Real.cos (a * x)) +
              ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt + x)) * Real.cos (a * x)) := by
              congr 1
              calc
                ∫ x in (0 : ℝ)..Lt,
                    (Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) * Real.cos (a * x)
                  = ∫ x in (0 : ℝ)..Lt,
                      Real.exp (-ω * (Lt - x)) * Real.cos (a * x) +
                        Real.exp (-ω * (Lt + x)) * Real.cos (a * x) := by
                          apply intervalIntegral.integral_congr
                          intro x hx
                          ring
                _ = ((∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt - x)) * Real.cos (a * x)) +
                      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt + x)) * Real.cos (a * x)) := by
                          rw [intervalIntegral.integral_add hInt1 hInt2]
      _ = C⁻¹ *
            ((q * (∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.cos (a * x))) +
              q * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x))) := by
              congr 1
              rw [hA, hB]
  have hnegcos :
      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x) =
        ω * (1 - q) / D := by
    calc
      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x)
        = (-Real.exp (-ω * Lt) * ω + ω) / D := by
            simpa [a, D] using integral_exp_neg_mul_cos_circleFreq ω Lt hω hLt k
      _ = ω * (1 - q) / D := by
            dsimp [q]
            ring
  have hposcos :
      ∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.cos (a * x) =
        ω * (Real.exp (ω * Lt) - 1) / D := by
    calc
      ∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.cos (a * x)
        = (Real.exp (ω * Lt) * ω - ω) / D := by
            simpa [a, D] using integral_exp_pos_mul_cos_circleFreq ω Lt hω hLt k
      _ = ω * (Real.exp (ω * Lt) - 1) / D := by ring
  calc
    ∫ x in (0 : ℝ)..Lt, periodicKernel ω Lt x * Real.cos (a * x)
      = (∫ x in (0 : ℝ)..Lt,
            (freeKernel ω x * Real.cos (a * x)) +
              (((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) *
                Real.cos (a * x))) := hsplit
    _ = ((∫ x in (0 : ℝ)..Lt, freeKernel ω x * Real.cos (a * x)) +
          ∫ x in (0 : ℝ)..Lt,
            ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.cos (a * x)) := by
            rw [intervalIntegral.integral_add hfree_int hwrap_int]
    _ = (((2 * ω : ℝ)⁻¹ * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x))) +
          ∫ x in (0 : ℝ)..Lt,
            ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.cos (a * x)) := by
            rw [hfree]
    _ = (((2 * ω : ℝ)⁻¹ * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x))) +
          C⁻¹ *
            ((q * (∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.cos (a * x))) +
              q * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.cos (a * x)))) := by
            rw [hwrap]
    _ = (((2 * ω : ℝ)⁻¹ * (ω * (1 - q) / D)) +
          C⁻¹ * ((q * (ω * (Real.exp (ω * Lt) - 1) / D)) + q * (ω * (1 - q) / D))) := by
            rw [hnegcos, hposcos]
    _ = D⁻¹ := by
          have hqexp : q * Real.exp (ω * Lt) = 1 := by
            dsimp [q]
            rw [← Real.exp_add]
            have : -ω * Lt + ω * Lt = 0 := by ring
            simp
          dsimp [C, D]
          field_simp [hω_ne, h1q_ne, hD_ne]
          nlinarith [hqexp]

private theorem integral_periodicKernel_mul_sin_circleFreq
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt) (k : ℕ) :
    ∫ x in (0 : ℝ)..Lt, periodicKernel ω Lt x * Real.sin ((2 * Real.pi * k / Lt) * x) = 0 := by
  let a : ℝ := 2 * Real.pi * k / Lt
  let q : ℝ := Real.exp (-ω * Lt)
  let C : ℝ := 2 * ω * (1 - q)
  let D : ℝ := ω ^ 2 + a ^ 2
  have hω_ne : ω ≠ 0 := hω.ne'
  have hq_lt_one : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith
  have h1q_ne : 1 - q ≠ 0 := sub_ne_zero.mpr hq_lt_one.ne.symm
  have hC_ne : C ≠ 0 := by
    dsimp [C]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hω_ne) h1q_ne
  have hD_pos : 0 < D := by
    dsimp [D]
    nlinarith [sq_pos_of_pos hω, sq_nonneg a]
  have hD_ne : D ≠ 0 := hD_pos.ne'
  have hfree_int : IntervalIntegrable (fun x => freeKernel ω x * Real.sin (a * x)) volume 0 Lt := by
    exact ((continuous_freeKernel ω).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 Lt
  have hwrap_int : IntervalIntegrable
      (fun x =>
        ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.sin (a * x))
      volume 0 Lt := by
    have hcont :
        Continuous (fun x : ℝ =>
          ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.sin (a * x)) := by
      fun_prop
    exact hcont.intervalIntegrable 0 Lt
  have hsplit :
      ∫ x in (0 : ℝ)..Lt, periodicKernel ω Lt x * Real.sin (a * x) =
        ∫ x in (0 : ℝ)..Lt,
          (freeKernel ω x * Real.sin (a * x)) +
            (((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) *
              Real.sin (a * x)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) Lt := by
      simpa [Set.uIcc_of_le hLt.le] using hx
    have hpk := periodicKernel_eq_freeKernel_add_wrap ω Lt hω hLt hxI
    dsimp [C, q]
    rw [hpk]
    ring_nf
  have hfree :
      ∫ x in (0 : ℝ)..Lt, freeKernel ω x * Real.sin (a * x) =
        (2 * ω : ℝ)⁻¹ * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) Lt := by
      simpa [Set.uIcc_of_le hLt.le] using hx
    simp [freeKernel, abs_of_nonneg hxI.1, div_eq_mul_inv]
    ring
  have hInt1 : IntervalIntegrable
      (fun x => Real.exp (-ω * (Lt - x)) * Real.sin (a * x)) volume 0 Lt := by
    have hcont :
        Continuous (fun x : ℝ => Real.exp (-ω * (Lt - x)) * Real.sin (a * x)) := by
      fun_prop
    exact hcont.intervalIntegrable 0 Lt
  have hInt2 : IntervalIntegrable
      (fun x => Real.exp (-ω * (Lt + x)) * Real.sin (a * x)) volume 0 Lt := by
    have hcont :
        Continuous (fun x : ℝ => Real.exp (-ω * (Lt + x)) * Real.sin (a * x)) := by
      fun_prop
    exact hcont.intervalIntegrable 0 Lt
  have hA :
      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt - x)) * Real.sin (a * x) =
        q * (∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.sin (a * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [q]
    rw [show -ω * (Lt - x) = -ω * Lt + ω * x by ring, Real.exp_add]
    ring
  have hB :
      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt + x)) * Real.sin (a * x) =
        q * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [q]
    rw [show -ω * (Lt + x) = -ω * Lt + -ω * x by ring, Real.exp_add]
    ring
  have hwrap :
      ∫ x in (0 : ℝ)..Lt,
        ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.sin (a * x) =
      C⁻¹ *
        ((q * (∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.sin (a * x))) +
          q * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x))) := by
    calc
      ∫ x in (0 : ℝ)..Lt,
          ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.sin (a * x)
        = C⁻¹ * ∫ x in (0 : ℝ)..Lt,
            (Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) * Real.sin (a * x) := by
              rw [← intervalIntegral.integral_const_mul]
              apply intervalIntegral.integral_congr
              intro x hx
              field_simp [hC_ne]
      _ = C⁻¹ *
            ((∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt - x)) * Real.sin (a * x)) +
              ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt + x)) * Real.sin (a * x)) := by
              congr 1
              calc
                ∫ x in (0 : ℝ)..Lt,
                    (Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) * Real.sin (a * x)
                  = ∫ x in (0 : ℝ)..Lt,
                      Real.exp (-ω * (Lt - x)) * Real.sin (a * x) +
                        Real.exp (-ω * (Lt + x)) * Real.sin (a * x) := by
                          apply intervalIntegral.integral_congr
                          intro x hx
                          ring
                _ = ((∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt - x)) * Real.sin (a * x)) +
                      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * (Lt + x)) * Real.sin (a * x)) := by
                          rw [intervalIntegral.integral_add hInt1 hInt2]
      _ = C⁻¹ *
            ((q * (∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.sin (a * x))) +
              q * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x))) := by
              rw [hA, hB]
  have hnegsin :
      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x) =
        a * (1 - q) / D := by
    calc
      ∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x)
        = (-Real.exp (-ω * Lt) * a + a) / D := by
            simpa [a, D] using integral_exp_neg_mul_sin_circleFreq ω Lt hω hLt k
      _ = a * (1 - q) / D := by
            dsimp [q]
            ring
  have hpossin :
      ∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.sin (a * x) =
        a * (1 - Real.exp (ω * Lt)) / D := by
    calc
      ∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.sin (a * x)
        = (-Real.exp (ω * Lt) * a + a) / D := by
            simpa [a, D] using integral_exp_pos_mul_sin_circleFreq ω Lt hω hLt k
      _ = a * (1 - Real.exp (ω * Lt)) / D := by ring
  calc
    ∫ x in (0 : ℝ)..Lt, periodicKernel ω Lt x * Real.sin (a * x)
      = (∫ x in (0 : ℝ)..Lt,
            (freeKernel ω x * Real.sin (a * x)) +
              (((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) *
                Real.sin (a * x))) := hsplit
    _ = ((∫ x in (0 : ℝ)..Lt, freeKernel ω x * Real.sin (a * x)) +
          ∫ x in (0 : ℝ)..Lt,
            ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.sin (a * x)) := by
            rw [intervalIntegral.integral_add hfree_int hwrap_int]
    _ = (((2 * ω : ℝ)⁻¹ * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x))) +
          ∫ x in (0 : ℝ)..Lt,
            ((Real.exp (-ω * (Lt - x)) + Real.exp (-ω * (Lt + x))) / C) * Real.sin (a * x)) := by
            rw [hfree]
    _ = (((2 * ω : ℝ)⁻¹ * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x))) +
          C⁻¹ *
            ((q * (∫ x in (0 : ℝ)..Lt, Real.exp (ω * x) * Real.sin (a * x))) +
              q * (∫ x in (0 : ℝ)..Lt, Real.exp (-ω * x) * Real.sin (a * x)))) := by
            rw [hwrap]
    _ = (((2 * ω : ℝ)⁻¹ * (a * (1 - q) / D)) +
          C⁻¹ * ((q * (a * (1 - Real.exp (ω * Lt)) / D)) + q * (a * (1 - q) / D))) := by
            rw [hnegsin, hpossin]
    _ = 0 := by
          have hqexp : q * Real.exp (ω * Lt) = 1 := by
            dsimp [q]
            rw [← Real.exp_add]
            have : -ω * Lt + ω * Lt = 0 := by ring
            simp
          have hinner : (1 - q) ^ 2 + q * (1 - Real.exp (ω * Lt) + (1 - q)) = 0 := by
            nlinarith [hqexp]
          dsimp [C, D]
          field_simp [hω_ne, h1q_ne, hD_ne]
          rw [hinner]
          ring

private theorem periodicKernel_neg
    (ω Lt u : ℝ) :
    periodicKernel ω Lt (-u) = periodicKernel ω Lt u := by
  simp [periodicKernel, abs_neg]

private theorem integral_periodicKernel_mul_cos_circleFreq_tail
    (ω Lt : ℝ) (hLt : 0 < Lt) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lt) (k : ℕ) :
    ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt u * Real.cos ((2 * Real.pi * k / Lt) * u) =
      ∫ u in t..Lt, periodicKernel ω Lt u * Real.cos ((2 * Real.pi * k / Lt) * u) := by
  let a : ℝ := 2 * Real.pi * k / Lt
  have hLt_ne : Lt ≠ 0 := hLt.ne'
  have hαLt : a * Lt = k * (2 * Real.pi) := by
    dsimp [a]
    field_simp [hLt_ne]
  calc
    ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt u * Real.cos (a * u)
      = ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt (Lt - u) * Real.cos (a * (Lt - u)) := by
          apply intervalIntegral.integral_congr
          intro u hu
          change periodicKernel ω Lt u * Real.cos (a * u) =
            periodicKernel ω Lt (Lt - u) * Real.cos (a * (Lt - u))
          have hu_mem : u ∈ Set.Icc (0 : ℝ) (Lt - t) := by
            simpa [Set.uIcc_of_le (sub_nonneg.mpr ht.2)] using hu
          have huI : u ∈ Set.Icc (0 : ℝ) Lt := by
            exact ⟨hu_mem.1, le_trans hu_mem.2 (sub_le_self Lt ht.1)⟩
          rw [← periodicKernel_sub_eq ω Lt huI]
          have harg : a * (Lt - u) = k * (2 * Real.pi) - a * u := by
            dsimp [a]
            field_simp [hLt_ne]
          rw [harg]
          rw [Real.cos_nat_mul_two_pi_sub]
    _ = ∫ u in t..Lt, periodicKernel ω Lt u * Real.cos (a * u) := by
          simpa [a, sub_eq_add_neg] using
            (intervalIntegral.integral_comp_sub_left
              (f := fun u : ℝ => periodicKernel ω Lt u * Real.cos (a * u))
              (a := (0 : ℝ)) (b := Lt - t) Lt)

private theorem integral_periodicKernel_mul_sin_circleFreq_tail
    (ω Lt : ℝ) (hLt : 0 < Lt) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lt) (k : ℕ) :
    ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt u * Real.sin ((2 * Real.pi * k / Lt) * u) =
      -∫ u in t..Lt, periodicKernel ω Lt u * Real.sin ((2 * Real.pi * k / Lt) * u) := by
  let a : ℝ := 2 * Real.pi * k / Lt
  have hLt_ne : Lt ≠ 0 := hLt.ne'
  calc
    ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt u * Real.sin (a * u)
      = ∫ u in (0 : ℝ)..Lt - t,
          -(periodicKernel ω Lt (Lt - u) * Real.sin (a * (Lt - u))) := by
            apply intervalIntegral.integral_congr
            intro u hu
            change periodicKernel ω Lt u * Real.sin (a * u) =
              -(periodicKernel ω Lt (Lt - u) * Real.sin (a * (Lt - u)))
            have hu_mem : u ∈ Set.Icc (0 : ℝ) (Lt - t) := by
              simpa [Set.uIcc_of_le (sub_nonneg.mpr ht.2)] using hu
            have huI : u ∈ Set.Icc (0 : ℝ) Lt := by
              exact ⟨hu_mem.1, le_trans hu_mem.2 (sub_le_self Lt ht.1)⟩
            rw [← periodicKernel_sub_eq ω Lt huI]
            have harg : a * (Lt - u) = k * (2 * Real.pi) - a * u := by
              dsimp [a]
              field_simp [hLt_ne]
            rw [harg]
            rw [Real.sin_nat_mul_two_pi_sub]
            ring
    _ = -∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt (Lt - u) * Real.sin (a * (Lt - u)) := by
          rw [intervalIntegral.integral_neg]
    _ = -∫ u in t..Lt, periodicKernel ω Lt u * Real.sin (a * u) := by
          congr 1
          simpa [a, sub_eq_add_neg] using
            (intervalIntegral.integral_comp_sub_left
              (f := fun u : ℝ => periodicKernel ω Lt u * Real.sin (a * u))
              (a := (0 : ℝ)) (b := Lt - t) Lt)

private theorem integral_periodicKernel_shift_mul_cos_circleFreq
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lt) (k : ℕ) :
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) * Real.cos ((2 * Real.pi * k / Lt) * s) =
      (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2)⁻¹ * Real.cos ((2 * Real.pi * k / Lt) * t) := by
  let a : ℝ := 2 * Real.pi * k / Lt
  let D : ℝ := ω ^ 2 + a ^ 2
  let kc : ℝ → ℝ := fun u => periodicKernel ω Lt u * Real.cos (a * u)
  let ks : ℝ → ℝ := fun u => periodicKernel ω Lt u * Real.sin (a * u)
  have hmain_cont :
      Continuous (fun s : ℝ => periodicKernel ω Lt (t - s) * Real.cos (a * s)) := by
    exact ((continuous_periodicKernel ω Lt).comp (continuous_const.sub continuous_id)).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hmain_int₁ :
      IntervalIntegrable (fun s : ℝ => periodicKernel ω Lt (t - s) * Real.cos (a * s))
        volume 0 t := by
    exact hmain_cont.intervalIntegrable 0 t
  have hmain_int₂ :
      IntervalIntegrable (fun s : ℝ => periodicKernel ω Lt (t - s) * Real.cos (a * s))
        volume t Lt := by
    exact hmain_cont.intervalIntegrable t Lt
  have hkc_int₁ : IntervalIntegrable kc volume 0 t := by
    exact (((continuous_periodicKernel ω Lt).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 t)
  have hkc_int₂ : IntervalIntegrable kc volume t Lt := by
    exact (((continuous_periodicKernel ω Lt).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable t Lt)
  have hks_int₁ : IntervalIntegrable ks volume 0 t := by
    exact (((continuous_periodicKernel ω Lt).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 t)
  have hks_int₂ : IntervalIntegrable ks volume t Lt := by
    exact (((continuous_periodicKernel ω Lt).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable t Lt)
  have hkc_tail : IntervalIntegrable kc volume 0 (Lt - t) := by
    exact
      ((continuous_periodicKernel ω Lt).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0
        (Lt - t)
  have hks_tail : IntervalIntegrable ks volume 0 (Lt - t) := by
    exact
      ((continuous_periodicKernel ω Lt).mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable 0
        (Lt - t)
  have hsplit :
      ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) * Real.cos (a * s) =
        (∫ s in (0 : ℝ)..t, periodicKernel ω Lt (t - s) * Real.cos (a * s)) +
          ∫ s in t..Lt, periodicKernel ω Lt (t - s) * Real.cos (a * s) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hmain_int₁ hmain_int₂]
  have hI₁ :
      ∫ s in (0 : ℝ)..t, periodicKernel ω Lt (t - s) * Real.cos (a * s) =
        Real.cos (a * t) * (∫ u in (0 : ℝ)..t, kc u) +
          Real.sin (a * t) * (∫ u in (0 : ℝ)..t, ks u) := by
    calc
      ∫ s in (0 : ℝ)..t, periodicKernel ω Lt (t - s) * Real.cos (a * s)
        = ∫ u in (0 : ℝ)..t, periodicKernel ω Lt u * Real.cos (a * (t - u)) := by
            simpa [a] using
              (intervalIntegral.integral_comp_sub_left
                (f := fun u : ℝ => periodicKernel ω Lt u * Real.cos (a * (t - u)))
                (a := (0 : ℝ)) (b := t) t)
      _ = ∫ u in (0 : ℝ)..t,
            periodicKernel ω Lt u *
              (Real.cos (a * t) * Real.cos (a * u) +
                Real.sin (a * t) * Real.sin (a * u)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            change periodicKernel ω Lt u * Real.cos (a * (t - u)) =
              periodicKernel ω Lt u *
                (Real.cos (a * t) * Real.cos (a * u) +
                  Real.sin (a * t) * Real.sin (a * u))
            have harg : a * (t - u) = a * t - a * u := by ring
            rw [harg, Real.cos_sub]
      _ = ∫ u in (0 : ℝ)..t, Real.cos (a * t) * kc u + Real.sin (a * t) * ks u := by
            apply intervalIntegral.integral_congr
            intro u hu
            simp [kc, ks]
            ring
      _ = (∫ u in (0 : ℝ)..t, Real.cos (a * t) * kc u) +
            ∫ u in (0 : ℝ)..t, Real.sin (a * t) * ks u := by
            rw [intervalIntegral.integral_add (hkc_int₁.const_mul _) (hks_int₁.const_mul _)]
      _ = Real.cos (a * t) * (∫ u in (0 : ℝ)..t, kc u) +
            Real.sin (a * t) * (∫ u in (0 : ℝ)..t, ks u) := by
            rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hI₂ :
      ∫ s in t..Lt, periodicKernel ω Lt (t - s) * Real.cos (a * s) =
        Real.cos (a * t) * (∫ u in (0 : ℝ)..Lt - t, kc u) -
          Real.sin (a * t) * (∫ u in (0 : ℝ)..Lt - t, ks u) := by
    calc
      ∫ s in t..Lt, periodicKernel ω Lt (t - s) * Real.cos (a * s)
        = ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt (-u) * Real.cos (a * (u + t)) := by
            simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              (intervalIntegral.integral_comp_sub_right
                (f := fun u : ℝ => periodicKernel ω Lt (-u) * Real.cos (a * (u + t)))
                (a := t) (b := Lt) t)
      _ = ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt u * Real.cos (a * (u + t)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            change periodicKernel ω Lt (-u) * Real.cos (a * (u + t)) =
              periodicKernel ω Lt u * Real.cos (a * (u + t))
            rw [periodicKernel_neg]
      _ = ∫ u in (0 : ℝ)..Lt - t,
            periodicKernel ω Lt u *
              (Real.cos (a * t) * Real.cos (a * u) -
                Real.sin (a * t) * Real.sin (a * u)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            change periodicKernel ω Lt u * Real.cos (a * (u + t)) =
              periodicKernel ω Lt u *
                (Real.cos (a * t) * Real.cos (a * u) -
                  Real.sin (a * t) * Real.sin (a * u))
            have harg : a * (u + t) = a * t + a * u := by ring
            rw [harg, Real.cos_add]
      _ = ∫ u in (0 : ℝ)..Lt - t, Real.cos (a * t) * kc u - Real.sin (a * t) * ks u := by
            apply intervalIntegral.integral_congr
            intro u hu
            simp [kc, ks]
            ring
      _ = (∫ u in (0 : ℝ)..Lt - t, Real.cos (a * t) * kc u) +
            ∫ u in (0 : ℝ)..Lt - t, (-Real.sin (a * t)) * ks u := by
            rw [show (fun u : ℝ => Real.cos (a * t) * kc u - Real.sin (a * t) * ks u) =
              fun u : ℝ => Real.cos (a * t) * kc u + (-Real.sin (a * t)) * ks u by
              ext u
              ring]
            have hcos_tail :
                IntervalIntegrable (fun u : ℝ => Real.cos (a * t) * kc u) volume 0 (Lt - t) :=
              hkc_tail.const_mul _
            have hsin_tail :
                IntervalIntegrable (fun u : ℝ => (-Real.sin (a * t)) * ks u) volume 0 (Lt - t) :=
              hks_tail.const_mul _
            rw [intervalIntegral.integral_add hcos_tail hsin_tail]
      _ = Real.cos (a * t) * (∫ u in (0 : ℝ)..Lt - t, kc u) -
            Real.sin (a * t) * (∫ u in (0 : ℝ)..Lt - t, ks u) := by
            rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
            ring
  have hA :
      (∫ u in (0 : ℝ)..t, kc u) + ∫ u in (0 : ℝ)..Lt - t, kc u =
        ∫ u in (0 : ℝ)..Lt, kc u := by
    have htail :
        ∫ u in (0 : ℝ)..Lt - t, kc u = ∫ u in t..Lt, kc u := by
      simpa [kc, a] using integral_periodicKernel_mul_cos_circleFreq_tail ω Lt hLt ht k
    rw [htail]
    exact intervalIntegral.integral_add_adjacent_intervals hkc_int₁ hkc_int₂
  have hB :
      (∫ u in (0 : ℝ)..t, ks u) - ∫ u in (0 : ℝ)..Lt - t, ks u =
        ∫ u in (0 : ℝ)..Lt, ks u := by
    have htail :
        ∫ u in (0 : ℝ)..Lt - t, ks u = -∫ u in t..Lt, ks u := by
      simpa [ks, a] using integral_periodicKernel_mul_sin_circleFreq_tail ω Lt hLt ht k
    calc
      (∫ u in (0 : ℝ)..t, ks u) - ∫ u in (0 : ℝ)..Lt - t, ks u
        = (∫ u in (0 : ℝ)..t, ks u) + ∫ u in t..Lt, ks u := by
            rw [htail]
            ring
      _ = ∫ u in (0 : ℝ)..Lt, ks u := by
            exact intervalIntegral.integral_add_adjacent_intervals hks_int₁ hks_int₂
  calc
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) * Real.cos (a * s)
      = (∫ s in (0 : ℝ)..t, periodicKernel ω Lt (t - s) * Real.cos (a * s)) +
          ∫ s in t..Lt, periodicKernel ω Lt (t - s) * Real.cos (a * s) := hsplit
    _ = (Real.cos (a * t) * (∫ u in (0 : ℝ)..t, kc u) +
          Real.sin (a * t) * (∫ u in (0 : ℝ)..t, ks u)) +
            (Real.cos (a * t) * (∫ u in (0 : ℝ)..Lt - t, kc u) -
              Real.sin (a * t) * (∫ u in (0 : ℝ)..Lt - t, ks u)) := by
            rw [hI₁, hI₂]
    _ = Real.cos (a * t) * (∫ u in (0 : ℝ)..Lt, kc u) +
          Real.sin (a * t) * (∫ u in (0 : ℝ)..Lt, ks u) := by
            rw [← hA, ← hB]
            ring
    _ = Real.cos (a * t) * D⁻¹ + Real.sin (a * t) * 0 := by
            rw [show (∫ u in (0 : ℝ)..Lt, kc u) = D⁻¹ by
              simpa [kc, a, D] using integral_periodicKernel_mul_cos_circleFreq ω Lt hω hLt k]
            rw [show (∫ u in (0 : ℝ)..Lt, ks u) = 0 by
              simpa [ks, a] using integral_periodicKernel_mul_sin_circleFreq ω Lt hω hLt k]
    _ = D⁻¹ * Real.cos (a * t) := by ring
    _ = (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2)⁻¹ * Real.cos ((2 * Real.pi * k / Lt) * t) := by
          simp [a, D, mul_comm]

private theorem integral_periodicKernel_shift_mul_sin_circleFreq
    (ω Lt : ℝ) (hω : 0 < ω) (hLt : 0 < Lt)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lt) (k : ℕ) :
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) * Real.sin ((2 * Real.pi * k / Lt) * s) =
      (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2)⁻¹ * Real.sin ((2 * Real.pi * k / Lt) * t) := by
  let a : ℝ := 2 * Real.pi * k / Lt
  let D : ℝ := ω ^ 2 + a ^ 2
  let kc : ℝ → ℝ := fun u => periodicKernel ω Lt u * Real.cos (a * u)
  let ks : ℝ → ℝ := fun u => periodicKernel ω Lt u * Real.sin (a * u)
  have hmain_cont :
      Continuous (fun s : ℝ => periodicKernel ω Lt (t - s) * Real.sin (a * s)) := by
    exact ((continuous_periodicKernel ω Lt).comp (continuous_const.sub continuous_id)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hmain_int₁ :
      IntervalIntegrable (fun s : ℝ => periodicKernel ω Lt (t - s) * Real.sin (a * s))
        volume 0 t := by
    exact hmain_cont.intervalIntegrable 0 t
  have hmain_int₂ :
      IntervalIntegrable (fun s : ℝ => periodicKernel ω Lt (t - s) * Real.sin (a * s))
        volume t Lt := by
    exact hmain_cont.intervalIntegrable t Lt
  have hkc_int₁ : IntervalIntegrable kc volume 0 t := by
    exact (((continuous_periodicKernel ω Lt).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 t)
  have hkc_int₂ : IntervalIntegrable kc volume t Lt := by
    exact (((continuous_periodicKernel ω Lt).mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable t Lt)
  have hks_int₁ : IntervalIntegrable ks volume 0 t := by
    exact (((continuous_periodicKernel ω Lt).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 t)
  have hks_int₂ : IntervalIntegrable ks volume t Lt := by
    exact (((continuous_periodicKernel ω Lt).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable t Lt)
  have hkc_tail : IntervalIntegrable kc volume 0 (Lt - t) := by
    exact
      ((continuous_periodicKernel ω Lt).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0
        (Lt - t)
  have hks_tail : IntervalIntegrable ks volume 0 (Lt - t) := by
    exact
      ((continuous_periodicKernel ω Lt).mul
        (Real.continuous_sin.comp (continuous_const.mul continuous_id))).intervalIntegrable 0
        (Lt - t)
  have hsplit :
      ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) * Real.sin (a * s) =
        (∫ s in (0 : ℝ)..t, periodicKernel ω Lt (t - s) * Real.sin (a * s)) +
          ∫ s in t..Lt, periodicKernel ω Lt (t - s) * Real.sin (a * s) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hmain_int₁ hmain_int₂]
  have hI₁ :
      ∫ s in (0 : ℝ)..t, periodicKernel ω Lt (t - s) * Real.sin (a * s) =
        Real.sin (a * t) * (∫ u in (0 : ℝ)..t, kc u) -
          Real.cos (a * t) * (∫ u in (0 : ℝ)..t, ks u) := by
    calc
      ∫ s in (0 : ℝ)..t, periodicKernel ω Lt (t - s) * Real.sin (a * s)
        = ∫ u in (0 : ℝ)..t, periodicKernel ω Lt u * Real.sin (a * (t - u)) := by
            simpa [a] using
              (intervalIntegral.integral_comp_sub_left
                (f := fun u : ℝ => periodicKernel ω Lt u * Real.sin (a * (t - u)))
                (a := (0 : ℝ)) (b := t) t)
      _ = ∫ u in (0 : ℝ)..t,
            periodicKernel ω Lt u *
              (Real.sin (a * t) * Real.cos (a * u) -
                Real.cos (a * t) * Real.sin (a * u)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            change periodicKernel ω Lt u * Real.sin (a * (t - u)) =
              periodicKernel ω Lt u *
                (Real.sin (a * t) * Real.cos (a * u) -
                  Real.cos (a * t) * Real.sin (a * u))
            have harg : a * (t - u) = a * t - a * u := by ring
            rw [harg, Real.sin_sub]
      _ = ∫ u in (0 : ℝ)..t, Real.sin (a * t) * kc u - Real.cos (a * t) * ks u := by
            apply intervalIntegral.integral_congr
            intro u hu
            simp [kc, ks]
            ring
      _ = (∫ u in (0 : ℝ)..t, Real.sin (a * t) * kc u) +
            ∫ u in (0 : ℝ)..t, (-Real.cos (a * t)) * ks u := by
            rw [show (fun u : ℝ => Real.sin (a * t) * kc u - Real.cos (a * t) * ks u) =
              fun u : ℝ => Real.sin (a * t) * kc u + (-Real.cos (a * t)) * ks u by
              ext u
              ring]
            have hsin_head :
                IntervalIntegrable (fun u : ℝ => Real.sin (a * t) * kc u) volume 0 t :=
              hkc_int₁.const_mul _
            have hcos_head :
                IntervalIntegrable (fun u : ℝ => (-Real.cos (a * t)) * ks u) volume 0 t :=
              hks_int₁.const_mul _
            rw [intervalIntegral.integral_add hsin_head hcos_head]
      _ = Real.sin (a * t) * (∫ u in (0 : ℝ)..t, kc u) -
            Real.cos (a * t) * (∫ u in (0 : ℝ)..t, ks u) := by
            rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
            ring
  have hI₂ :
      ∫ s in t..Lt, periodicKernel ω Lt (t - s) * Real.sin (a * s) =
        Real.sin (a * t) * (∫ u in (0 : ℝ)..Lt - t, kc u) +
          Real.cos (a * t) * (∫ u in (0 : ℝ)..Lt - t, ks u) := by
    calc
      ∫ s in t..Lt, periodicKernel ω Lt (t - s) * Real.sin (a * s)
        = ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt (-u) * Real.sin (a * (u + t)) := by
            simpa [a, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              (intervalIntegral.integral_comp_sub_right
                (f := fun u : ℝ => periodicKernel ω Lt (-u) * Real.sin (a * (u + t)))
                (a := t) (b := Lt) t)
      _ = ∫ u in (0 : ℝ)..Lt - t, periodicKernel ω Lt u * Real.sin (a * (u + t)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            change periodicKernel ω Lt (-u) * Real.sin (a * (u + t)) =
              periodicKernel ω Lt u * Real.sin (a * (u + t))
            rw [periodicKernel_neg]
      _ = ∫ u in (0 : ℝ)..Lt - t,
            periodicKernel ω Lt u *
              (Real.sin (a * t) * Real.cos (a * u) +
                Real.cos (a * t) * Real.sin (a * u)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            change periodicKernel ω Lt u * Real.sin (a * (u + t)) =
              periodicKernel ω Lt u *
                (Real.sin (a * t) * Real.cos (a * u) +
                  Real.cos (a * t) * Real.sin (a * u))
            have harg : a * (u + t) = a * t + a * u := by ring
            rw [harg, Real.sin_add]
      _ = ∫ u in (0 : ℝ)..Lt - t, Real.sin (a * t) * kc u + Real.cos (a * t) * ks u := by
            apply intervalIntegral.integral_congr
            intro u hu
            simp [kc, ks]
            ring
      _ = (∫ u in (0 : ℝ)..Lt - t, Real.sin (a * t) * kc u) +
            ∫ u in (0 : ℝ)..Lt - t, Real.cos (a * t) * ks u := by
            rw [intervalIntegral.integral_add (hkc_tail.const_mul _) (hks_tail.const_mul _)]
      _ = Real.sin (a * t) * (∫ u in (0 : ℝ)..Lt - t, kc u) +
            Real.cos (a * t) * (∫ u in (0 : ℝ)..Lt - t, ks u) := by
            rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hA :
      (∫ u in (0 : ℝ)..t, kc u) + ∫ u in (0 : ℝ)..Lt - t, kc u =
        ∫ u in (0 : ℝ)..Lt, kc u := by
    have htail :
        ∫ u in (0 : ℝ)..Lt - t, kc u = ∫ u in t..Lt, kc u := by
      simpa [kc, a] using integral_periodicKernel_mul_cos_circleFreq_tail ω Lt hLt ht k
    rw [htail]
    exact intervalIntegral.integral_add_adjacent_intervals hkc_int₁ hkc_int₂
  have hB :
      -(∫ u in (0 : ℝ)..t, ks u) + ∫ u in (0 : ℝ)..Lt - t, ks u = 0 := by
    have htail :
        ∫ u in (0 : ℝ)..Lt - t, ks u = -∫ u in t..Lt, ks u := by
      simpa [ks, a] using integral_periodicKernel_mul_sin_circleFreq_tail ω Lt hLt ht k
    calc
      -(∫ u in (0 : ℝ)..t, ks u) + ∫ u in (0 : ℝ)..Lt - t, ks u
        = -(∫ u in (0 : ℝ)..t, ks u) + -(∫ u in t..Lt, ks u) := by
            rw [htail]
      _ = -((∫ u in (0 : ℝ)..t, ks u) + ∫ u in t..Lt, ks u) := by
            ring
      _ = -(∫ u in (0 : ℝ)..Lt, ks u) := by
            rw [intervalIntegral.integral_add_adjacent_intervals hks_int₁ hks_int₂]
      _ = 0 := by
            have hks_zero : ∫ u in (0 : ℝ)..Lt, ks u = 0 := by
              simpa [ks, a] using integral_periodicKernel_mul_sin_circleFreq ω Lt hω hLt k
            rw [hks_zero]
            simp
  calc
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) * Real.sin (a * s)
      = (∫ s in (0 : ℝ)..t, periodicKernel ω Lt (t - s) * Real.sin (a * s)) +
          ∫ s in t..Lt, periodicKernel ω Lt (t - s) * Real.sin (a * s) := hsplit
    _ = (Real.sin (a * t) * (∫ u in (0 : ℝ)..t, kc u) -
          Real.cos (a * t) * (∫ u in (0 : ℝ)..t, ks u)) +
            (Real.sin (a * t) * (∫ u in (0 : ℝ)..Lt - t, kc u) +
              Real.cos (a * t) * (∫ u in (0 : ℝ)..Lt - t, ks u)) := by
            rw [hI₁, hI₂]
    _ = Real.sin (a * t) * ((∫ u in (0 : ℝ)..t, kc u) + ∫ u in (0 : ℝ)..Lt - t, kc u) +
          Real.cos (a * t) * (-(∫ u in (0 : ℝ)..t, ks u) +
            ∫ u in (0 : ℝ)..Lt - t, ks u) := by
            ring
    _ = Real.sin (a * t) * (∫ u in (0 : ℝ)..Lt, kc u) + Real.cos (a * t) * 0 := by
            rw [hA, hB]
    _ = Real.sin (a * t) * D⁻¹ + Real.cos (a * t) * 0 := by
            rw [show (∫ u in (0 : ℝ)..Lt, kc u) = D⁻¹ by
              simpa [kc, a, D] using integral_periodicKernel_mul_cos_circleFreq ω Lt hω hLt k]
    _ = D⁻¹ * Real.sin (a * t) := by ring
    _ = (ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2)⁻¹ * Real.sin ((2 * Real.pi * k / Lt) * t) := by
          simp [a, D, mul_comm]

private theorem fourierBasisFun_cos_mode
    (Lt : ℝ) [Fact (0 < Lt)] (k : ℕ) (hk : 0 < k) (t : ℝ) :
    SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k - 1) t =
      Real.sqrt (2 / Lt) * Real.cos ((2 * Real.pi * k / Lt) * t) := by
  have hLt_ne : Lt ≠ 0 := ne_of_gt (Fact.out : 0 < Lt)
  rw [show (2 * k - 1 : ℕ) = 2 * (k - 1) + 1 by omega]
  simp only [SmoothMap_Circle.fourierBasisFun,
    if_pos (show 2 * (k - 1) % 2 = 0 by omega),
    show (2 * (k - 1) / 2 + 1 : ℕ) = k by omega]
  have harg : 2 * Real.pi * (k : ℝ) * t / Lt = (2 * Real.pi * k / Lt) * t := by
    field_simp [hLt_ne]
  rw [harg]

private theorem fourierBasisFun_sin_mode
    (Lt : ℝ) [Fact (0 < Lt)] (k : ℕ) (hk : 0 < k) (t : ℝ) :
    SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k) t =
      Real.sqrt (2 / Lt) * Real.sin ((2 * Real.pi * k / Lt) * t) := by
  have hLt_ne : Lt ≠ 0 := ne_of_gt (Fact.out : 0 < Lt)
  rw [show (2 * k : ℕ) = (2 * k - 1) + 1 by omega]
  simp only [SmoothMap_Circle.fourierBasisFun,
    if_neg (show ¬ ((2 * k - 1) % 2 = 0) by omega),
    show ((2 * k - 1) / 2 + 1 : ℕ) = k by omega]
  have harg : 2 * Real.pi * (k : ℝ) * t / Lt = (2 * Real.pi * k / Lt) * t := by
    field_simp [hLt_ne]
  rw [harg]

private theorem circleEigenvalue_cos_mode
    (Lt : ℝ) [Fact (0 < Lt)] (k : ℕ) (hk : 0 < k) :
    HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (2 * k - 1) =
      (2 * Real.pi * k / Lt) ^ 2 := by
  rw [show (2 * k - 1 : ℕ) = 2 * (k - 1) + 1 by omega]
  simp only [HasLaplacianEigenvalues.eigenvalue, SmoothMap_Circle.fourierFreq]
  have hk' : (((2 * (k - 1) / 2 + 1 : ℕ) : ℝ)) = k := by
    exact_mod_cast (show (2 * (k - 1) / 2 + 1 : ℕ) = k by omega)
  rw [hk']

private theorem circleEigenvalue_sin_mode
    (Lt : ℝ) [Fact (0 < Lt)] (k : ℕ) (hk : 0 < k) :
    HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (2 * k) =
      (2 * Real.pi * k / Lt) ^ 2 := by
  rw [show (2 * k : ℕ) = (2 * k - 1) + 1 by omega]
  simp only [HasLaplacianEigenvalues.eigenvalue, SmoothMap_Circle.fourierFreq,
    show ((2 * k - 1) / 2 + 1 : ℕ) = k by omega]

private theorem integral_periodicKernel_shift_mul_fourierBasis_zero
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lt) :
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) *
        SmoothMap_Circle.fourierBasisFun (L := Lt) 0 s =
      (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) 0 + ω ^ 2)⁻¹ *
        SmoothMap_Circle.fourierBasisFun (L := Lt) 0 t := by
  have hLt : 0 < Lt := Fact.out
  have hscalar :
      ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) = (ω ^ 2)⁻¹ := by
    simpa using integral_periodicKernel_shift_mul_cos_circleFreq ω Lt hω hLt ht 0
  calc
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) *
        SmoothMap_Circle.fourierBasisFun (L := Lt) 0 s
      = ∫ s in (0 : ℝ)..Lt, (1 / Real.sqrt Lt) * periodicKernel ω Lt (t - s) := by
          apply intervalIntegral.integral_congr
          intro s hs
          simp [SmoothMap_Circle.fourierBasisFun]
          ring
    _ = (1 / Real.sqrt Lt) * ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) := by
          rw [intervalIntegral.integral_const_mul]
    _ = (1 / Real.sqrt Lt) * (ω ^ 2)⁻¹ := by rw [hscalar]
    _ = (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) 0 + ω ^ 2)⁻¹ *
          SmoothMap_Circle.fourierBasisFun (L := Lt) 0 t := by
          simp [HasLaplacianEigenvalues.eigenvalue, SmoothMap_Circle.fourierFreq,
            SmoothMap_Circle.fourierBasisFun]
          ring

private theorem integral_periodicKernel_shift_mul_fourierBasis_cos
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lt) (k : ℕ) (hk : 0 < k) :
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) *
        SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k - 1) s =
      (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (2 * k - 1) + ω ^ 2)⁻¹ *
        SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k - 1) t := by
  have hLt : 0 < Lt := Fact.out
  calc
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) *
        SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k - 1) s
      = ∫ s in (0 : ℝ)..Lt,
          Real.sqrt (2 / Lt) *
            (periodicKernel ω Lt (t - s) * Real.cos ((2 * Real.pi * k / Lt) * s)) := by
              apply intervalIntegral.integral_congr
              intro s hs
              change periodicKernel ω Lt (t - s) *
                  SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k - 1) s =
                Real.sqrt (2 / Lt) *
                  (periodicKernel ω Lt (t - s) * Real.cos ((2 * Real.pi * k / Lt) * s))
              rw [fourierBasisFun_cos_mode (Lt := Lt) k hk s]
              ring
    _ = Real.sqrt (2 / Lt) *
          ∫ s in (0 : ℝ)..Lt,
            periodicKernel ω Lt (t - s) * Real.cos ((2 * Real.pi * k / Lt) * s) := by
              rw [intervalIntegral.integral_const_mul]
    _ = Real.sqrt (2 / Lt) *
          ((ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2)⁻¹ *
            Real.cos ((2 * Real.pi * k / Lt) * t)) := by
              rw [integral_periodicKernel_shift_mul_cos_circleFreq ω Lt hω hLt ht k]
    _ = (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (2 * k - 1) + ω ^ 2)⁻¹ *
          SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k - 1) t := by
              rw [circleEigenvalue_cos_mode (Lt := Lt) k hk,
                fourierBasisFun_cos_mode (Lt := Lt) k hk t]
              ring

private theorem integral_periodicKernel_shift_mul_fourierBasis_sin
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lt) (k : ℕ) (hk : 0 < k) :
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) *
        SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k) s =
      (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (2 * k) + ω ^ 2)⁻¹ *
        SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k) t := by
  have hLt : 0 < Lt := Fact.out
  calc
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) *
        SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k) s
      = ∫ s in (0 : ℝ)..Lt,
          Real.sqrt (2 / Lt) *
            (periodicKernel ω Lt (t - s) * Real.sin ((2 * Real.pi * k / Lt) * s)) := by
              apply intervalIntegral.integral_congr
              intro s hs
              change periodicKernel ω Lt (t - s) *
                  SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k) s =
                Real.sqrt (2 / Lt) *
                  (periodicKernel ω Lt (t - s) * Real.sin ((2 * Real.pi * k / Lt) * s))
              rw [fourierBasisFun_sin_mode (Lt := Lt) k hk s]
              ring
    _ = Real.sqrt (2 / Lt) *
          ∫ s in (0 : ℝ)..Lt,
            periodicKernel ω Lt (t - s) * Real.sin ((2 * Real.pi * k / Lt) * s) := by
              rw [intervalIntegral.integral_const_mul]
    _ = Real.sqrt (2 / Lt) *
          ((ω ^ 2 + (2 * Real.pi * k / Lt) ^ 2)⁻¹ *
            Real.sin ((2 * Real.pi * k / Lt) * t)) := by
              rw [integral_periodicKernel_shift_mul_sin_circleFreq ω Lt hω hLt ht k]
    _ = (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (2 * k) + ω ^ 2)⁻¹ *
          SmoothMap_Circle.fourierBasisFun (L := Lt) (2 * k) t := by
              rw [circleEigenvalue_sin_mode (Lt := Lt) k hk,
                fourierBasisFun_sin_mode (Lt := Lt) k hk t]
              ring

private theorem integral_periodicKernel_shift_mul_fourierBasisFun
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) Lt) (n : ℕ) :
    ∫ s in (0 : ℝ)..Lt, periodicKernel ω Lt (t - s) *
        SmoothMap_Circle.fourierBasisFun (L := Lt) n s =
      (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
        SmoothMap_Circle.fourierBasisFun (L := Lt) n t := by
  cases n with
  | zero =>
      simpa using integral_periodicKernel_shift_mul_fourierBasis_zero ω Lt hω ht
  | succ m =>
      rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
      · have hm : m + 1 = 2 * (j + 1) - 1 := by
          omega
        rw [hm]
        simpa using
          integral_periodicKernel_shift_mul_fourierBasis_cos
            ω Lt hω ht (j + 1) (by omega)
      · have hm : m + 1 = 2 * (j + 1) := by
          omega
        rw [hm]
        simpa using
          integral_periodicKernel_shift_mul_fourierBasis_sin
            ω Lt hω ht (j + 1) (by omega)

private theorem smoothCircle_coeff_eq_fourierCoeffReal
    (Lt : ℝ) [Fact (0 < Lt)] (m : ℕ) (f : SmoothMap_Circle Lt ℝ) :
    DyninMityaginSpace.coeff m f = SmoothMap_Circle.fourierCoeffReal (L := Lt) m f := by
  change ((RapidDecaySeq.coeffCLM m).comp
    (SmoothMap_Circle.smoothCircleRapidDecayEquiv (L := Lt)).toContinuousLinearMap) f = _
  simp [RapidDecaySeq.coeffCLM, RapidDecaySeq.coeffLM,
    SmoothMap_Circle.smoothCircleRapidDecayEquiv,
    SmoothMap_Circle.toRapidDecayLM, SmoothMap_Circle.toRapidDecay]

private theorem integral_Icc_eq_intervalIntegral
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (_hf : IntervalIntegrable f MeasureTheory.volume a b) :
    ∫ x in Set.Icc a b, f x = ∫ x in a..b, f x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

private theorem greenFunctionBilinear_continuous_left
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E]
    [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (h : E) :
    Continuous (fun f => greenFunctionBilinear mass hmass f h) := by
  have hcdiag := greenFunctionBilinear_continuous_diag mass hmass (E := E)
  have hpol : ∀ f, greenFunctionBilinear mass hmass f h =
      (greenFunctionBilinear mass hmass (f + h) (f + h) -
        greenFunctionBilinear mass hmass f f -
        greenFunctionBilinear mass hmass h h) / 2 := by
    intro f
    have : greenFunctionBilinear mass hmass (f + h) (f + h) =
        greenFunctionBilinear mass hmass f f +
          2 * greenFunctionBilinear mass hmass f h +
          greenFunctionBilinear mass hmass h h := by
      rw [greenFunctionBilinear_add_left, greenFunctionBilinear_add_right,
        greenFunctionBilinear_add_right, greenFunctionBilinear_symm mass hmass h f]
      ring
    linarith
  exact (((hcdiag.comp (continuous_id.add continuous_const)).sub hcdiag).sub
    continuous_const).div_const 2 |>.congr (fun f => (hpol f).symm)

private noncomputable def greenCLM_left
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E]
    [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (h : E) : E →L[ℝ] ℝ :=
  ⟨{ toFun := fun f => greenFunctionBilinear mass hmass f h
     map_add' := fun f₁ f₂ => greenFunctionBilinear_add_left mass hmass f₁ f₂ h
     map_smul' := fun c f => by
      rw [greenFunctionBilinear_smul_left, RingHom.id_apply, smul_eq_mul] },
    greenFunctionBilinear_continuous_left mass hmass h⟩

@[simp] private theorem greenCLM_left_apply
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E]
    [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (h f : E) :
    greenCLM_left mass hmass h f = greenFunctionBilinear mass hmass f h := rfl

/-- Uniform bilinear version of `torusGreen_uniform_bound`.

The method-of-images estimate from gaussian-field gives a uniform diagonal bound
`G_L(embed f, embed f) ≤ C q(f)^2`. Since the embedded torus covariance is a
symmetric positive semidefinite bilinear form, Mathlib's bilinear-form
Cauchy-Schwarz upgrades this to the cross estimate
`|G_L(embed f, embed g)| ≤ C q(f) q(g)` uniformly in `Lt ≥ 1`. This is the
quantitative continuity input needed for any later density extension from the
proved compact-support finite-rank subset. -/
private theorem asymTorusGreen_uniform_product_seminorm_bound
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (C : ℝ) (_ : 0 < C) (q : Seminorm ℝ (CylinderTestFunction Ls)),
      Continuous q ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)],
        1 ≤ Lt →
        ∀ f g : CylinderTestFunction Ls,
          |asymTorusContinuumGreen Lt Ls mass hmass
              (cylinderToTorusEmbed Lt Ls f)
              (cylinderToTorusEmbed Lt Ls g)| ≤
            C * q f * q g := by
  obtain ⟨C, hC_pos, q, hq_cont, hdiag⟩ :=
    GaussianField.torusGreen_uniform_bound (Ls := Ls) mass hmass
  refine ⟨C, hC_pos, q, hq_cont, ?_⟩
  intro Lt _ hLt f g
  let B : LinearMap.BilinForm ℝ (CylinderTestFunction Ls) := by
    refine
      { toFun := ?_
        map_add' := ?_
        map_smul' := ?_ }
    · intro f'
      refine
        { toFun := ?_
          map_add' := ?_
          map_smul' := ?_ }
      · intro g'
        exact asymTorusContinuumGreen Lt Ls mass hmass
          (cylinderToTorusEmbed Lt Ls f')
          (cylinderToTorusEmbed Lt Ls g')
      · intro g₁ g₂
        simp [asymTorusContinuumGreen, greenFunctionBilinear_add_right, map_add]
      · intro c g'
        simp [asymTorusContinuumGreen, greenFunctionBilinear_smul_right, map_smul]
    · intro f₁ f₂
      ext g'
      simp [asymTorusContinuumGreen, greenFunctionBilinear_add_left, map_add]
    · intro c f'
      ext g'
      simp [asymTorusContinuumGreen, greenFunctionBilinear_smul_left, map_smul]
  have hB_nonneg : ∀ x : CylinderTestFunction Ls, 0 ≤ B x x := by
    intro x
    dsimp [B]
    simpa [asymTorusContinuumGreen] using
      greenFunctionBilinear_nonneg mass hmass (cylinderToTorusEmbed Lt Ls x)
  have hB_symm : LinearMap.IsSymm B := by
    refine ⟨?_⟩
    intro x y
    dsimp [B]
    simpa [asymTorusContinuumGreen] using
      greenFunctionBilinear_symm mass hmass
        (cylinderToTorusEmbed Lt Ls x) (cylinderToTorusEmbed Lt Ls y)
  have hsq :
      (B f g) ^ 2 ≤ (C * q f * q g) ^ 2 := by
    have hcs := LinearMap.BilinForm.apply_sq_le_of_symm (B := B) hB_nonneg hB_symm f g
    have hdiagf : B f f ≤ C * q f ^ 2 := hdiag Lt hLt f
    have hdiagg : B g g ≤ C * q g ^ 2 := hdiag Lt hLt g
    have hmul :
        (B f f) * (B g g) ≤ (C * q f ^ 2) * (C * q g ^ 2) := by
      exact mul_le_mul hdiagf hdiagg (hB_nonneg g) (by positivity)
    calc
      (B f g) ^ 2 ≤ (B f f) * (B g g) := hcs
      _ ≤ (C * q f ^ 2) * (C * q g ^ 2) := hmul
      _ = (C * q f * q g) ^ 2 := by ring
  have hrhs_nonneg : 0 ≤ C * q f * q g := by
    exact mul_nonneg (mul_nonneg (le_of_lt hC_pos) (apply_nonneg q _)) (apply_nonneg q _)
  change |B f g| ≤ C * q f * q g
  exact abs_le.2 (abs_le_of_sq_le_sq' hsq hrhs_nonneg)

private theorem periodicKernelBilinear_integrand_continuousOn
    (ω Lt : ℝ) [Fact (0 < Lt)]
    (f g : SmoothMap_Circle Lt ℝ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2))
      (Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt) := by
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt
  have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1) K := by
    exact (f.continuous.comp continuous_fst).continuousOn
  have hg : ContinuousOn (fun p : ℝ × ℝ => g p.2) K := by
    exact (g.continuous.comp continuous_snd).continuousOn
  have hk : ContinuousOn (fun p : ℝ × ℝ => periodicKernel ω Lt (p.1 - p.2)) K := by
    exact ((continuous_periodicKernel ω Lt).comp
      (continuous_fst.sub continuous_snd)).continuousOn
  simpa [K] using (hf.mul hg).mul hk

private theorem periodicKernelBilinear_integrand_integrable
    (ω Lt : ℝ) [Fact (0 < Lt)]
    (f g : SmoothMap_Circle Lt ℝ) :
    Integrable
      (fun p : ℝ × ℝ => (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2))
      (volume.restrict (Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt)) := by
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  simpa [K] using
    (periodicKernelBilinear_integrand_continuousOn ω Lt f g).integrableOn_compact hK_compact

private noncomputable def periodicKernelBilinearRightCLM
    (ω Lt : ℝ) [Fact (0 < Lt)] (f : SmoothMap_Circle Lt ℝ) :
    SmoothMap_Circle Lt ℝ →L[ℝ] ℝ := by
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt
  let lm : SmoothMap_Circle Lt ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun g =>
        ∫ p in K, (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume
      map_add' := by
        intro g₁ g₂
        have hg₁ := periodicKernelBilinear_integrand_integrable ω Lt f g₁
        have hg₂ := periodicKernelBilinear_integrand_integrable ω Lt f g₂
        have hEq :
            (fun p : ℝ × ℝ =>
              (f p.1 * (g₁ + g₂) p.2) * periodicKernel ω Lt (p.1 - p.2)) =
            fun p =>
              (f p.1 * g₁ p.2) * periodicKernel ω Lt (p.1 - p.2) +
                (f p.1 * g₂ p.2) * periodicKernel ω Lt (p.1 - p.2) := by
          ext p
          simp
          ring
        rw [hEq, MeasureTheory.integral_add hg₁ hg₂]
      map_smul' := by
        intro c g
        have hEq :
            (fun p : ℝ × ℝ =>
              (f p.1 * (c • g) p.2) * periodicKernel ω Lt (p.1 - p.2)) =
            fun p => c * ((f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2)) := by
          ext p
          simp
          ring
        rw [hEq, MeasureTheory.integral_const_mul, smul_eq_mul]
        simp }
  refine ⟨lm, ?_⟩
  change Continuous lm
  apply WithSeminorms.continuous_of_isBounded SmoothMap_Circle.smoothCircle_withSeminorms
    (norm_withSeminorms ℝ ℝ)
  intro _
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt
  let A : ℝ × ℝ → ℝ := fun p => f p.1 * periodicKernel ω Lt (p.1 - p.2)
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hA_cont : ContinuousOn A K := by
    have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1) K := by
      exact (f.continuous.comp continuous_fst).continuousOn
    have hk : ContinuousOn (fun p : ℝ × ℝ => periodicKernel ω Lt (p.1 - p.2)) K := by
      exact ((continuous_periodicKernel ω Lt).comp
        (continuous_fst.sub continuous_snd)).continuousOn
    simpa [A] using hf.mul hk
  obtain ⟨B, hB⟩ := hK_compact.exists_bound_of_continuousOn hA_cont
  have hB_nonneg : 0 ≤ B := by
    have hmem : ((0 : ℝ), (0 : ℝ)) ∈ K := by
      simp [K, le_of_lt (Fact.out : 0 < Lt)]
    exact le_trans (norm_nonneg _) (hB _ hmem)
  refine ⟨{0}, ⟨B * volume.real K, by positivity⟩, fun g => ?_⟩
  simp only [Seminorm.comp_apply, Finset.sup_singleton, NNReal.smul_def,
    Seminorm.smul_apply, NNReal.coe_mk]
  rw [coe_normSeminorm, Real.norm_eq_abs]
  calc
    |∫ p in K, (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume|
      = ‖∫ p in K, (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ (B * SmoothMap_Circle.sobolevSeminorm 0 g) * volume.real K := by
          apply norm_setIntegral_le_of_norm_le_const hK_compact.measure_lt_top
          intro p hp
          have hp₂ : p.2 ∈ Set.Icc (0 : ℝ) Lt := hp.2
          have hg_bound : ‖g p.2‖ ≤ SmoothMap_Circle.sobolevSeminorm 0 g := by
            simpa [iteratedDeriv_zero] using
              SmoothMap_Circle.norm_iteratedDeriv_le_sobolevSeminorm g 0 hp₂
          have hAp : ‖A p‖ ≤ B := hB p hp
          rw [show f p.1 * g p.2 * periodicKernel ω Lt (p.1 - p.2) = A p * g p.2 by
            dsimp [A]
            ring]
          rw [norm_mul]
          exact mul_le_mul hAp hg_bound (norm_nonneg _) hB_nonneg
    _ = (B * volume.real K) * SmoothMap_Circle.sobolevSeminorm 0 g := by
          ring

@[simp] private theorem periodicKernelBilinearRightCLM_apply
    (ω Lt : ℝ) [Fact (0 < Lt)] (f g : SmoothMap_Circle Lt ℝ) :
    periodicKernelBilinearRightCLM ω Lt f g =
      ∫ p in Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt,
        (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := rfl

private theorem periodicKernelBilinear_fourierBasis_right
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    (f : SmoothMap_Circle Lt ℝ) (n : ℕ) :
    ∫ p in Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt,
      (f p.1 * (SmoothMap_Circle.fourierBasis (L := Lt) n) p.2) *
        periodicKernel ω Lt (p.1 - p.2) ∂volume =
      (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
        SmoothMap_Circle.fourierCoeffReal (L := Lt) n f := by
  let I : Set ℝ := Set.Icc (0 : ℝ) Lt
  let K : Set (ℝ × ℝ) := I ×ˢ I
  let ψ : SmoothMap_Circle Lt ℝ := SmoothMap_Circle.fourierBasis (L := Lt) n
  let H : ℝ → ℝ := fun t => ∫ s in I, periodicKernel ω Lt (t - s) * ψ s
  let G : ℝ × ℝ → ℝ := fun p => (f p.1 * ψ p.2) * periodicKernel ω Lt (p.1 - p.2)
  have hLt : 0 < Lt := Fact.out
  have hG_int : Integrable G ((volume.restrict I).prod (volume.restrict I)) := by
    rw [Measure.prod_restrict I I]
    simpa [I, K, G] using periodicKernelBilinear_integrand_integrable ω Lt f ψ
  have hprod :
      ∫ p in K, G p ∂volume =
        ∫ t, ∫ s, G (t, s) ∂(volume.restrict I) ∂(volume.restrict I) := by
    have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume := rfl
    calc
      ∫ p in K, G p ∂volume
        = ∫ p, G p ∂((volume.restrict I).prod (volume.restrict I)) := by
            rw [Measure.prod_restrict I I]
            simp [K, hvol]
      _ = ∫ t, ∫ s, G (t, s) ∂(volume.restrict I) ∂(volume.restrict I) := by
            exact MeasureTheory.integral_prod G hG_int
  have houter :
      ∫ t, ∫ s, G (t, s) ∂(volume.restrict I) ∂(volume.restrict I) =
        ∫ t, f t * H t ∂(volume.restrict I) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    dsimp [G, H]
    rw [show
      (fun s => (f t * ψ s) * periodicKernel ω Lt (t - s)) =
        fun s => f t * (periodicKernel ω Lt (t - s) * ψ s) by
      ext s
      ring]
    rw [MeasureTheory.integral_const_mul]
  have hH :
      ∀ t ∈ I,
        H t =
          (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ * ψ t := by
    intro t ht
    dsimp [H]
    rw [integral_Icc_eq_intervalIntegral (a := 0) (b := Lt) (le_of_lt hLt)]
    · simpa [ψ, SmoothMap_Circle.fourierBasis_apply] using
        integral_periodicKernel_shift_mul_fourierBasisFun ω Lt hω ht n
    · exact (((continuous_periodicKernel ω Lt).comp
        (continuous_const.sub continuous_id)).mul ψ.continuous).intervalIntegrable _ _
  calc
    ∫ p in Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt,
        (f p.1 * (SmoothMap_Circle.fourierBasis (L := Lt) n) p.2) *
          periodicKernel ω Lt (p.1 - p.2) ∂volume
      = ∫ t, f t * H t ∂(volume.restrict I) := by
          simpa [I, K, ψ, G] using hprod.trans houter
    _ = ∫ t,
          f t *
            ((HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
              ψ t) ∂(volume.restrict I) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
            rw [hH t ht]
    _ = (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
          ∫ t, f t * ψ t ∂(volume.restrict I) := by
            rw [show
              (fun t =>
                f t *
                  ((HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
                    ψ t)) =
                fun t =>
                  (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
                    (f t * ψ t) by
              ext t
              ring]
            rw [MeasureTheory.integral_const_mul]
    _ = (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
          SmoothMap_Circle.fourierCoeffReal (L := Lt) n f := by
            simp [I, ψ, SmoothMap_Circle.fourierCoeffReal, SmoothMap_Circle.fourierBasis_apply]

private theorem greenFunctionBilinear_basis_right
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    (f : SmoothMap_Circle Lt ℝ) (n : ℕ) :
    greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω f (DyninMityaginSpace.basis n) =
      (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
        DyninMityaginSpace.coeff n f := by
  unfold greenFunctionBilinear
  rw [tsum_eq_single n]
  · have hcoeff :
        DyninMityaginSpace.coeff n (DyninMityaginSpace.basis n : SmoothMap_Circle Lt ℝ) = 1 := by
        simpa using
          DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis (E := SmoothMap_Circle Lt ℝ) n n
    change DyninMityaginSpace.coeff n f *
        DyninMityaginSpace.coeff n (DyninMityaginSpace.basis n : SmoothMap_Circle Lt ℝ) /
          (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2) =
      (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
        DyninMityaginSpace.coeff n f
    rw [hcoeff]
    ring
  · intro m hm
    have hzero :
        DyninMityaginSpace.coeff m (DyninMityaginSpace.basis n : SmoothMap_Circle Lt ℝ) = 0 := by
      simpa [hm] using
        DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis (E := SmoothMap_Circle Lt ℝ) m n
    change DyninMityaginSpace.coeff m f *
        DyninMityaginSpace.coeff m (DyninMityaginSpace.basis n : SmoothMap_Circle Lt ℝ) /
          (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) m + ω ^ 2) = 0
    rw [hzero]
    simp

private theorem greenFunctionBilinear_fourierBasis_right
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    (f : SmoothMap_Circle Lt ℝ) (n : ℕ) :
    greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω
      f (SmoothMap_Circle.fourierBasis (L := Lt) n) =
      (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) n + ω ^ 2)⁻¹ *
        SmoothMap_Circle.fourierCoeffReal (L := Lt) n f := by
  rw [← dm_basis_eq_fourierBasis (L := Lt) n]
  rw [greenFunctionBilinear_basis_right ω Lt hω f n,
    smoothCircle_coeff_eq_fourierCoeffReal (Lt := Lt) n f]

private theorem greenFunctionBilinear_fourierBasis_right_eq_periodicKernelBilinear
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    (f : SmoothMap_Circle Lt ℝ) (n : ℕ) :
    greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω
      f (SmoothMap_Circle.fourierBasis (L := Lt) n) =
    ∫ p in Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt,
      (f p.1 * (SmoothMap_Circle.fourierBasis (L := Lt) n) p.2) *
        periodicKernel ω Lt (p.1 - p.2) ∂volume := by
  rw [greenFunctionBilinear_fourierBasis_right ω Lt hω f n,
    periodicKernelBilinear_fourierBasis_right ω Lt hω f n]

private theorem greenFunctionBilinear_eq_periodicKernel_integralOn_square
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    (f g : SmoothMap_Circle Lt ℝ) :
    greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω f g =
      ∫ p in Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt,
        (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := by
  let Φ := periodicKernelBilinearRightCLM ω Lt f
  have hgreen :
      greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω f g =
        ∑' n : ℕ,
          DyninMityaginSpace.coeff n g *
            greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω
              f (DyninMityaginSpace.basis n) := by
    calc
      greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω f g
        = greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω g f := by
            rw [greenFunctionBilinear_symm]
      _ = ∑' n : ℕ,
            DyninMityaginSpace.coeff n g *
              greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω
                (DyninMityaginSpace.basis n) f := by
            exact DyninMityaginSpace.expansion (greenCLM_left ω hω f) g
      _ = ∑' n : ℕ,
            DyninMityaginSpace.coeff n g *
              greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω
                f (DyninMityaginSpace.basis n) := by
            apply tsum_congr
            intro n
            rw [greenFunctionBilinear_symm]
  have hkernel :
      ∫ p in Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt,
        (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume =
      ∑' n : ℕ, DyninMityaginSpace.coeff n g * Φ (DyninMityaginSpace.basis n) := by
    simpa [Φ] using DyninMityaginSpace.expansion Φ g
  calc
    greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω f g
      = ∑' n : ℕ,
          DyninMityaginSpace.coeff n g *
            greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω
              f (DyninMityaginSpace.basis n) := hgreen
    _ = ∑' n : ℕ, DyninMityaginSpace.coeff n g * Φ (DyninMityaginSpace.basis n) := by
          apply tsum_congr
          intro n
          rw [periodicKernelBilinearRightCLM_apply, dm_basis_eq_fourierBasis (L := Lt) n]
          exact congrArg
            (fun z =>
              DyninMityaginSpace.coeff n g * z)
            (greenFunctionBilinear_fourierBasis_right_eq_periodicKernelBilinear
              ω Lt hω f n)
    _ = ∫ p in Set.Icc (0 : ℝ) Lt ×ˢ Set.Icc (0 : ℝ) Lt,
          (f p.1 * g p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := by
          symm
          exact hkernel

private theorem periodizeCLM_eq_on_large_symmetric_halfPeriod
    {Lt : ℝ} [Fact (0 < Lt)]
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hLt_large : 2 * T < Lt) :
    ∀ t ∈ Set.Icc (-Lt / 2) (Lt / 2), (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t = h t := by
  intro t ht
  by_cases ht_nonneg : 0 ≤ t
  · have htI : t ∈ Set.Icc (0 : ℝ) (Lt / 2) := ⟨ht_nonneg, ht.2⟩
    exact periodizeCLM_eq_on_large_period
      (L := Lt) h T hT hsupp (by linarith) t htI
  · have ht_neg : t < 0 := lt_of_not_ge ht_nonneg
    have href_supp : ∀ u, T < |u| → schwartzReflection h u = 0 := by
      intro u hu
      simpa [schwartzReflection_apply, abs_neg] using hsupp (-u) (by simpa [abs_neg] using hu)
    have htI : -t ∈ Set.Icc (0 : ℝ) (Lt / 2) := by
      constructor
      · linarith
      · linarith [ht.1]
    have href :=
      periodizeCLM_eq_on_large_period
        (L := Lt) (schwartzReflection h) T hT href_supp (by linarith) (-t) htI
    have hcomm :
        (@periodizeCLM Lt ‹Fact (0 < Lt)› (schwartzReflection h)).toFun (-t) =
          (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t := by
      simpa [circleReflection] using
        congrArg (fun f : SmoothMap_Circle Lt ℝ => f (-t))
          (periodizeCLM_comp_schwartzReflection (L := Lt) h)
    calc
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t
        = (@periodizeCLM Lt ‹Fact (0 < Lt)› (schwartzReflection h)).toFun (-t) := by
            symm
            exact hcomm
      _ = (schwartzReflection h) (-t) := href
      _ = h t := by simp [schwartzReflection_apply]

private theorem periodizeCLM_eq_sub_period_on_upper_strip
    {Lt : ℝ} [Fact (0 < Lt)]
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hLt_large : 2 * T < Lt) :
    ∀ t ∈ Set.Icc (Lt / 2) Lt, (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t = h (t - Lt) := by
  intro t ht
  have hper : (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t =
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun (t - Lt) := by
    simpa [sub_eq_add_neg, add_assoc] using
      ((@periodizeCLM Lt ‹Fact (0 < Lt)› h).periodic' (t - Lt))
  have ht_sub : t - Lt ∈ Set.Icc (-Lt / 2) (Lt / 2) := by
    constructor
    · linarith [ht.1]
    · linarith [ht.2]
  calc
    (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t
      = (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun (t - Lt) := hper
    _ = h (t - Lt) :=
      periodizeCLM_eq_on_large_symmetric_halfPeriod h T hT hsupp hLt_large (t - Lt) ht_sub

private theorem periodizeCLM_eq_zero_on_middle_open_strip
    {Lt : ℝ} [Fact (0 < Lt)]
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hLt_large : 4 * T < Lt) :
    ∀ t ∈ Set.Ioo T (Lt - T), (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t = 0 := by
  intro t ht
  by_cases hhalf : t ≤ Lt / 2
  · have htI : t ∈ Set.Icc (0 : ℝ) (Lt / 2) := by
      constructor
      · linarith [hT, ht.1]
      · exact hhalf
    have hEq :
        (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t = h t :=
      periodizeCLM_eq_on_large_period
        (L := Lt) h T hT hsupp (by linarith [hLt_large]) t htI
    have ht_abs : T < |t| := by
      have ht_pos : 0 < t := by
        linarith [hT, ht.1]
      rw [abs_of_pos ht_pos]
      exact ht.1
    simpa [hEq] using hsupp t ht_abs
  · have hhalf_lt : Lt / 2 < t := lt_of_not_ge hhalf
    have htI : t ∈ Set.Icc (Lt / 2) Lt := by
      constructor
      · exact le_of_lt hhalf_lt
      · linarith [ht.2]
    have hEq :
        (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun t = h (t - Lt) :=
      periodizeCLM_eq_sub_period_on_upper_strip h T hT hsupp (by linarith [hLt_large]) t htI
    have ht_sub_neg : t - Lt < 0 := by
      linarith [ht.2]
    have ht_abs : T < |t - Lt| := by
      rw [abs_of_neg ht_sub_neg]
      linarith [ht.2]
    simpa [hEq] using hsupp (t - Lt) ht_abs

private theorem intervalIntegral_mul_periodizeCLM_eq_zero_on_middle_strip
    {Lt : ℝ} [Fact (0 < Lt)]
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hLt_large : 4 * T < Lt)
    (φ : ℝ → ℝ) :
    ∫ s in T..(Lt - T), (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun s * φ s = 0 := by
  apply intervalIntegral.integral_zero_ae
  have h_ne : ∀ᵐ s : ℝ ∂volume, s ≠ Lt - T := Measure.ae_ne volume (Lt - T)
  filter_upwards [h_ne] with s hs_ne hs_mem
  have hT_le : T ≤ Lt - T := by
    linarith [hLt_large]
  have hsIoc : s ∈ Set.Ioc T (Lt - T) := by
    simpa [Set.uIoc_of_le hT_le] using hs_mem
  have hsIoo : s ∈ Set.Ioo T (Lt - T) := ⟨hsIoc.1, lt_of_le_of_ne hsIoc.2 hs_ne⟩
  simp [periodizeCLM_eq_zero_on_middle_open_strip h T hT hsupp hLt_large s hsIoo]

private theorem periodicKernel_sub_period_eq
    (ω Lt : ℝ) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) Lt) :
    periodicKernel ω Lt (u - Lt) = periodicKernel ω Lt u := by
  rw [show u - Lt = -(Lt - u) by ring, periodicKernel_neg]
  exact periodicKernel_sub_eq ω Lt hu

private theorem periodizeCLM_intervalIntegral_eq_supportInterval_pos
    (ω Lt : ℝ) [Fact (0 < Lt)]
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hLt_large : 4 * T < Lt)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ s in (0 : ℝ)..Lt,
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun s * periodicKernel ω Lt (t - s) =
    ∫ u in (-T)..T, h u * periodicKernel ω Lt (t - u) := by
  let per : SmoothMap_Circle Lt ℝ := @periodizeCLM Lt ‹Fact (0 < Lt)› h
  let f : ℝ → ℝ := fun s => per.toFun s * periodicKernel ω Lt (t - s)
  let g : ℝ → ℝ := fun u => h u * periodicKernel ω Lt (t - u)
  have hf_cont : Continuous f := by
    dsimp [f]
    exact per.continuous.mul
      ((continuous_periodicKernel ω Lt).comp (continuous_const.sub continuous_id))
  have hg_cont : Continuous g := by
    dsimp [g]
    exact h.continuous.mul
      ((continuous_periodicKernel ω Lt).comp (continuous_const.sub continuous_id))
  have hf_int₁ : IntervalIntegrable f volume (0 : ℝ) T := hf_cont.intervalIntegrable _ _
  have hf_int₂ : IntervalIntegrable f volume T (Lt - T) := hf_cont.intervalIntegrable _ _
  have hf_int₃ : IntervalIntegrable f volume (Lt - T) Lt := hf_cont.intervalIntegrable _ _
  have hg_int₁ : IntervalIntegrable g volume (-T) 0 := hg_cont.intervalIntegrable _ _
  have hg_int₂ : IntervalIntegrable g volume (0 : ℝ) T := hg_cont.intervalIntegrable _ _
  have hsplit_left :
      (∫ s in (0 : ℝ)..(Lt - T), f s) =
        (∫ s in (0 : ℝ)..T, f s) + ∫ s in T..(Lt - T), f s := by
    exact (intervalIntegral.integral_add_adjacent_intervals hf_int₁ hf_int₂).symm
  have hsplit :
      (∫ s in (0 : ℝ)..Lt, f s) =
        (∫ s in (0 : ℝ)..(Lt - T), f s) + ∫ s in (Lt - T)..Lt, f s := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable 0 (Lt - T)) hf_int₃).symm
  have hI₁ :
      ∫ s in (0 : ℝ)..T, f s = ∫ s in (0 : ℝ)..T, g s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := by
      simpa [Set.uIcc_of_le (le_of_lt hT)] using hs
    have hsI : s ∈ Set.Icc (-T) T := by
      exact ⟨by linarith [hT, hsIcc.1], hsIcc.2⟩
    have hper :
        per.toFun s = h s :=
      periodizeCLM_eq_on_symmetric_large_period
        (L := Lt) h T hT hsupp (by linarith [hLt_large]) s hsI
    simp [f, g, hper]
  have hI_mid_zero : ∫ s in T..(Lt - T), f s = 0 := by
    simpa [f] using
      intervalIntegral_mul_periodizeCLM_eq_zero_on_middle_strip
        h T hT hsupp hLt_large (fun s => periodicKernel ω Lt (t - s))
  have hI₂ :
      ∫ s in (Lt - T)..Lt, f s = ∫ u in (-T)..0, g u := by
    calc
      ∫ s in (Lt - T)..Lt, f s = ∫ u in (-T)..0, f (u + Lt) := by
            have hshift :=
              intervalIntegral.integral_comp_add_right (f := f) (a := -T) (b := 0) Lt
            symm
            convert hshift using 1
            ring
      _ = ∫ u in (-T)..0, g u := by
            apply intervalIntegral.integral_congr
            intro u hu
            have huIcc : u ∈ Set.Icc (-T) 0 := by
              simpa [Set.uIcc_of_le (show (-T : ℝ) ≤ 0 by linarith [hT])] using hu
            have huStrip : u + Lt ∈ Set.Icc (Lt / 2) Lt := by
              constructor
              · linarith [huIcc.1, hLt_large]
              · linarith [huIcc.2]
            have hper :
                per.toFun (u + Lt) = h u := by
              simpa using
                periodizeCLM_eq_sub_period_on_upper_strip
                  h T hT hsupp (by linarith [hLt_large]) (u + Lt) huStrip
            have huKer : t - u ∈ Set.Icc (0 : ℝ) Lt := by
              constructor
              · linarith [ht.1, huIcc.2]
              · linarith [ht.2, huIcc.1, hLt_large]
            have hker :
                periodicKernel ω Lt (t - (u + Lt)) = periodicKernel ω Lt (t - u) := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                periodicKernel_sub_period_eq ω Lt huKer
            simp [f, g, hper, hker]
  calc
    ∫ s in (0 : ℝ)..Lt, (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun s *
        periodicKernel ω Lt (t - s)
      = ∫ s in (0 : ℝ)..Lt, f s := by simp [f, per]
    _ = (∫ s in (0 : ℝ)..(Lt - T), f s) + ∫ s in (Lt - T)..Lt, f s := hsplit
    _ = ((∫ s in (0 : ℝ)..T, f s) + ∫ s in T..(Lt - T), f s) + ∫ s in (Lt - T)..Lt, f s := by
          rw [hsplit_left]
    _ = (∫ s in (0 : ℝ)..T, f s) + ∫ s in (Lt - T)..Lt, f s := by
          rw [hI_mid_zero]
          ring
    _ = (∫ s in (0 : ℝ)..T, g s) + ∫ u in (-T)..0, g u := by
          rw [hI₁, hI₂]
    _ = ∫ u in (-T)..T, g u := by
          simpa [add_comm] using intervalIntegral.integral_add_adjacent_intervals hg_int₁ hg_int₂
    _ = ∫ u in (-T)..T, h u * periodicKernel ω Lt (t - u) := by
          simp [g]

private theorem periodizeCLM_intervalIntegral_eq_supportInterval_upper
    (ω Lt : ℝ) [Fact (0 < Lt)]
    (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hLt_large : 4 * T < Lt)
    {t : ℝ} (ht : t ∈ Set.Icc (-T) 0) :
    ∫ s in (0 : ℝ)..Lt,
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun s *
        periodicKernel ω Lt ((t + Lt) - s) =
    ∫ u in (-T)..T, h u * periodicKernel ω Lt (t - u) := by
  let per : SmoothMap_Circle Lt ℝ := @periodizeCLM Lt ‹Fact (0 < Lt)› h
  let f : ℝ → ℝ := fun s => per.toFun s * periodicKernel ω Lt ((t + Lt) - s)
  let g : ℝ → ℝ := fun u => h u * periodicKernel ω Lt (t - u)
  have hf_cont : Continuous f := by
    dsimp [f]
    exact per.continuous.mul ((continuous_periodicKernel ω Lt).comp
      (continuous_const.sub continuous_id))
  have hg_cont : Continuous g := by
    dsimp [g]
    exact h.continuous.mul
      ((continuous_periodicKernel ω Lt).comp (continuous_const.sub continuous_id))
  have hf_int₁ : IntervalIntegrable f volume (0 : ℝ) T := hf_cont.intervalIntegrable _ _
  have hf_int₂ : IntervalIntegrable f volume T (Lt - T) := hf_cont.intervalIntegrable _ _
  have hf_int₃ : IntervalIntegrable f volume (Lt - T) Lt := hf_cont.intervalIntegrable _ _
  have hg_int₁ : IntervalIntegrable g volume (-T) 0 := hg_cont.intervalIntegrable _ _
  have hg_int₂ : IntervalIntegrable g volume (0 : ℝ) T := hg_cont.intervalIntegrable _ _
  have hsplit_left :
      (∫ s in (0 : ℝ)..(Lt - T), f s) =
        (∫ s in (0 : ℝ)..T, f s) + ∫ s in T..(Lt - T), f s := by
    exact (intervalIntegral.integral_add_adjacent_intervals hf_int₁ hf_int₂).symm
  have hsplit :
      (∫ s in (0 : ℝ)..Lt, f s) =
        (∫ s in (0 : ℝ)..(Lt - T), f s) + ∫ s in (Lt - T)..Lt, f s := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hf_cont.intervalIntegrable 0 (Lt - T)) hf_int₃).symm
  have hI₁ :
      ∫ s in (0 : ℝ)..T, f s = ∫ s in (0 : ℝ)..T, g s := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := by
      simpa [Set.uIcc_of_le (le_of_lt hT)] using hs
    have hsI : s ∈ Set.Icc (-T) T := by
      exact ⟨by linarith [hT, hsIcc.1], hsIcc.2⟩
    have hper :
        per.toFun s = h s :=
      periodizeCLM_eq_on_symmetric_large_period
        (L := Lt) h T hT hsupp (by linarith [hLt_large]) s hsI
    have hsKer : s - t ∈ Set.Icc (0 : ℝ) Lt := by
      constructor
      · linarith [hsIcc.1, ht.2]
      · linarith [hsI.2, ht.1, hLt_large]
    have hker :
        periodicKernel ω Lt ((t + Lt) - s) = periodicKernel ω Lt (t - s) := by
      calc
        periodicKernel ω Lt ((t + Lt) - s)
          = periodicKernel ω Lt (Lt - (s - t)) := by congr 1; ring
        _ = periodicKernel ω Lt (s - t) := periodicKernel_sub_eq ω Lt hsKer
        _ = periodicKernel ω Lt (t - s) := by
              rw [show s - t = -(t - s) by ring, periodicKernel_neg]
    simp [f, g, hper, hker]
  have hI_mid_zero : ∫ s in T..(Lt - T), f s = 0 := by
    simpa [f] using
      intervalIntegral_mul_periodizeCLM_eq_zero_on_middle_strip
        h T hT hsupp hLt_large (fun s => periodicKernel ω Lt ((t + Lt) - s))
  have hI₂ :
      ∫ s in (Lt - T)..Lt, f s = ∫ u in (-T)..0, g u := by
    calc
      ∫ s in (Lt - T)..Lt, f s = ∫ u in (-T)..0, f (u + Lt) := by
            have hshift :=
              intervalIntegral.integral_comp_add_right (f := f) (a := -T) (b := 0) Lt
            symm
            convert hshift using 1
            ring
      _ = ∫ u in (-T)..0, g u := by
            apply intervalIntegral.integral_congr
            intro u hu
            have huIcc : u ∈ Set.Icc (-T) 0 := by
              simpa [Set.uIcc_of_le (show (-T : ℝ) ≤ 0 by linarith [hT])] using hu
            have huStrip : u + Lt ∈ Set.Icc (Lt / 2) Lt := by
              constructor
              · linarith [huIcc.1, hLt_large]
              · linarith [huIcc.2]
            have hper :
                per.toFun (u + Lt) = h u := by
              simpa using
                periodizeCLM_eq_sub_period_on_upper_strip
                  h T hT hsupp (by linarith [hLt_large]) (u + Lt) huStrip
            simp [f, g, hper]
  calc
    ∫ s in (0 : ℝ)..Lt,
        (@periodizeCLM Lt ‹Fact (0 < Lt)› h).toFun s *
          periodicKernel ω Lt ((t + Lt) - s)
      = ∫ s in (0 : ℝ)..Lt, f s := by simp [f, per]
    _ = (∫ s in (0 : ℝ)..(Lt - T), f s) + ∫ s in (Lt - T)..Lt, f s := hsplit
    _ = ((∫ s in (0 : ℝ)..T, f s) + ∫ s in T..(Lt - T), f s) + ∫ s in (Lt - T)..Lt, f s := by
          rw [hsplit_left]
    _ = (∫ s in (0 : ℝ)..T, f s) + ∫ s in (Lt - T)..Lt, f s := by
          rw [hI_mid_zero]
          ring
    _ = (∫ s in (0 : ℝ)..T, g s) + ∫ u in (-T)..0, g u := by
          rw [hI₁, hI₂]
    _ = ∫ u in (-T)..T, g u := by
          simpa [add_comm] using intervalIntegral.integral_add_adjacent_intervals hg_int₁ hg_int₂
    _ = ∫ u in (-T)..T, h u * periodicKernel ω Lt (t - u) := by
          simp [g]

private theorem greenFunctionBilinear_eq_periodicKernel_integralOn_compactDiffBox
    (ω Lt : ℝ) [Fact (0 < Lt)] (hω : 0 < ω)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (hLt_large : 4 * T < Lt) :
    greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h₁)
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h₂) =
    ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
      (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := by
  let per₁ : SmoothMap_Circle Lt ℝ := @periodizeCLM Lt ‹Fact (0 < Lt)› h₁
  let per₂ : SmoothMap_Circle Lt ℝ := @periodizeCLM Lt ‹Fact (0 < Lt)› h₂
  let I₀ : Set ℝ := Set.Icc (0 : ℝ) Lt
  let I : Set ℝ := Set.Icc (-T) T
  let K : Set (ℝ × ℝ) := I ×ˢ I
  let G₀ : ℝ × ℝ → ℝ := fun p =>
    (per₁ p.1 * per₂ p.2) * periodicKernel ω Lt (p.1 - p.2)
  let F : ℝ → ℝ := fun t =>
    ∫ s in (0 : ℝ)..Lt, per₂ s * periodicKernel ω Lt (t - s)
  let H : ℝ → ℝ := fun t => per₁ t * F t
  let Fbox : ℝ → ℝ := fun t =>
    ∫ s in (-T)..T, h₂ s * periodicKernel ω Lt (t - s)
  let J : ℝ → ℝ := fun t => h₁ t * Fbox t
  have hLt_pos : 0 < Lt := Fact.out
  have hG₀_int : Integrable G₀ ((volume.restrict I₀).prod (volume.restrict I₀)) := by
    rw [Measure.prod_restrict I₀ I₀]
    simpa [I₀, G₀, per₁, per₂] using
      periodicKernelBilinear_integrand_integrable ω Lt per₁ per₂
  have hprod :
      ∫ p in I₀ ×ˢ I₀, G₀ p ∂volume =
        ∫ t, ∫ s, G₀ (t, s) ∂(volume.restrict I₀) ∂(volume.restrict I₀) := by
    have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume := rfl
    calc
      ∫ p in I₀ ×ˢ I₀, G₀ p ∂volume
        = ∫ p, G₀ p ∂((volume.restrict I₀).prod (volume.restrict I₀)) := by
            rw [Measure.prod_restrict I₀ I₀]
            simp [I₀, hvol]
      _ = ∫ t, ∫ s, G₀ (t, s) ∂(volume.restrict I₀) ∂(volume.restrict I₀) := by
            exact MeasureTheory.integral_prod G₀ hG₀_int
  have hparam_cont :
      Continuous (Function.uncurry (fun t s : ℝ =>
        per₂ s * periodicKernel ω Lt (t - s))) := by
    simpa using
      ((per₂.continuous.comp continuous_snd).mul
        ((continuous_periodicKernel ω Lt).comp (continuous_fst.sub continuous_snd)))
  have hF_cont : Continuous F := by
    simpa [F] using
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := volume) (f := fun t s : ℝ => per₂ s * periodicKernel ω Lt (t - s))
        hparam_cont (0 : ℝ) Lt
  have hH_cont : Continuous H := by
    simpa [H] using per₁.continuous.mul hF_cont
  have houter_sq :
      ∫ p in I₀ ×ˢ I₀, G₀ p ∂volume = ∫ t in (0 : ℝ)..Lt, H t := by
    calc
      ∫ p in I₀ ×ˢ I₀, G₀ p ∂volume
        = ∫ t, ∫ s, G₀ (t, s) ∂(volume.restrict I₀) ∂(volume.restrict I₀) := hprod
      _ = ∫ t, H t ∂(volume.restrict I₀) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
            dsimp [H, F, G₀]
            rw [integral_Icc_eq_intervalIntegral (a := 0) (b := Lt) (le_of_lt hLt_pos)]
            · rw [show
                (fun s => (per₁ t * per₂ s) * periodicKernel ω Lt (t - s)) =
                  fun s => per₁ t * (per₂ s * periodicKernel ω Lt (t - s)) by
                ext s
                ring]
              rw [intervalIntegral.integral_const_mul]
            · simpa [mul_assoc] using
                (((per₂.continuous).mul
                  ((continuous_periodicKernel ω Lt).comp
                    (continuous_const.sub continuous_id))).intervalIntegrable
                  (μ := volume) (0 : ℝ) Lt).const_mul (per₁ t)
      _ = ∫ t in I₀, H t ∂volume := by
            simp [I₀]
      _ = ∫ t in (0 : ℝ)..Lt, H t := by
            simpa [I₀] using
              integral_Icc_eq_intervalIntegral (a := 0) (b := Lt) (le_of_lt hLt_pos)
                (hH_cont.intervalIntegrable _ _)
  have hH_int₁ : IntervalIntegrable H volume (0 : ℝ) T := hH_cont.intervalIntegrable _ _
  have hH_int₂ : IntervalIntegrable H volume T (Lt - T) := hH_cont.intervalIntegrable _ _
  have hH_int₃ : IntervalIntegrable H volume (Lt - T) Lt := hH_cont.intervalIntegrable _ _
  have hH_split_left :
      (∫ t in (0 : ℝ)..(Lt - T), H t) =
        (∫ t in (0 : ℝ)..T, H t) + ∫ t in T..(Lt - T), H t := by
    exact (intervalIntegral.integral_add_adjacent_intervals hH_int₁ hH_int₂).symm
  have hH_split :
      (∫ t in (0 : ℝ)..Lt, H t) =
        (∫ t in (0 : ℝ)..(Lt - T), H t) + ∫ t in (Lt - T)..Lt, H t := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hH_cont.intervalIntegrable 0 (Lt - T)) hH_int₃).symm
  have houter_pos :
      ∫ t in (0 : ℝ)..T, H t = ∫ t in (0 : ℝ)..T, J t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := by
      simpa [Set.uIcc_of_le (le_of_lt hT)] using ht
    have htI : t ∈ Set.Icc (-T) T := by
      exact ⟨by linarith [hT, htIcc.1], htIcc.2⟩
    have hper :
        per₁ t = h₁ t :=
      periodizeCLM_eq_on_symmetric_large_period
        (L := Lt) h₁ T hT hsupp₁ (by linarith [hLt_large]) t htI
    have hinner :
        ∫ s in (0 : ℝ)..Lt, per₂ s * periodicKernel ω Lt (t - s) =
          ∫ u in (-T)..T, h₂ u * periodicKernel ω Lt (t - u) := by
      simpa [per₂] using
        periodizeCLM_intervalIntegral_eq_supportInterval_pos
          ω Lt h₂ T hT hsupp₂ hLt_large htIcc
    dsimp [H, J, F, Fbox]
    rw [hper, hinner]
  have houter_mid_zero : ∫ t in T..(Lt - T), H t = 0 := by
    simpa [H, F, per₁] using
      intervalIntegral_mul_periodizeCLM_eq_zero_on_middle_strip
        h₁ T hT hsupp₁ hLt_large F
  have houter_upper :
      ∫ t in (Lt - T)..Lt, H t = ∫ u in (-T)..0, J u := by
    calc
      ∫ t in (Lt - T)..Lt, H t = ∫ u in (-T)..0, H (u + Lt) := by
            have hshift :=
              intervalIntegral.integral_comp_add_right (f := H) (a := -T) (b := 0) Lt
            symm
            convert hshift using 1
            ring
      _ = ∫ u in (-T)..0, J u := by
            apply intervalIntegral.integral_congr
            intro u hu
            have huIcc : u ∈ Set.Icc (-T) 0 := by
              simpa [Set.uIcc_of_le (show (-T : ℝ) ≤ 0 by linarith [hT])] using hu
            have huStrip : u + Lt ∈ Set.Icc (Lt / 2) Lt := by
              constructor
              · linarith [huIcc.1, hLt_large]
              · linarith [huIcc.2]
            have hper :
                per₁ (u + Lt) = h₁ u := by
              simpa using
                periodizeCLM_eq_sub_period_on_upper_strip
                  h₁ T hT hsupp₁ (by linarith [hLt_large]) (u + Lt) huStrip
            have hinner :
                ∫ s in (0 : ℝ)..Lt, per₂ s * periodicKernel ω Lt ((u + Lt) - s) =
                  ∫ u_1 in (-T)..T, h₂ u_1 * periodicKernel ω Lt (u - u_1) := by
              simpa [per₂] using
                periodizeCLM_intervalIntegral_eq_supportInterval_upper
                  ω Lt h₂ T hT hsupp₂ hLt_large huIcc
            dsimp [H, J, F, Fbox]
            rw [hper, hinner]
  have hbox_param_cont :
      Continuous (Function.uncurry (fun t s : ℝ =>
        h₂ s * periodicKernel ω Lt (t - s))) := by
    simpa using
      ((h₂.continuous.comp continuous_snd).mul
        ((continuous_periodicKernel ω Lt).comp (continuous_fst.sub continuous_snd)))
  have hFbox_cont : Continuous Fbox := by
    simpa [Fbox] using
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := volume) (f := fun t s : ℝ => h₂ s * periodicKernel ω Lt (t - s))
        hbox_param_cont (-T) T
  have hJ_cont : Continuous J := by
    simpa [J] using h₁.continuous.mul hFbox_cont
  have hJ_int₁ : IntervalIntegrable J volume (-T) 0 := hJ_cont.intervalIntegrable _ _
  have hJ_int₂ : IntervalIntegrable J volume (0 : ℝ) T := hJ_cont.intervalIntegrable _ _
  have hinterval :
      ∫ t in (0 : ℝ)..Lt, H t = ∫ t in (-T)..T, J t := by
    calc
      ∫ t in (0 : ℝ)..Lt, H t
        = (∫ t in (0 : ℝ)..(Lt - T), H t) + ∫ t in (Lt - T)..Lt, H t := hH_split
      _ = ((∫ t in (0 : ℝ)..T, H t) + ∫ t in T..(Lt - T), H t) +
            ∫ t in (Lt - T)..Lt, H t := by
              rw [hH_split_left]
      _ = (∫ t in (0 : ℝ)..T, H t) + ∫ t in (Lt - T)..Lt, H t := by
            rw [houter_mid_zero]
            ring
      _ = (∫ t in (0 : ℝ)..T, J t) + ∫ u in (-T)..0, J u := by
            rw [houter_pos, houter_upper]
      _ = ∫ u in (-T)..T, J u := by
            simpa [add_comm] using
              intervalIntegral.integral_add_adjacent_intervals hJ_int₁ hJ_int₂
  have hG_cont : ContinuousOn
      (fun p : ℝ × ℝ =>
        (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2)) K := by
    have hh₁ : ContinuousOn (fun p : ℝ × ℝ => h₁ p.1) K := by
      exact (h₁.continuous.comp continuous_fst).continuousOn
    have hh₂ : ContinuousOn (fun p : ℝ × ℝ => h₂ p.2) K := by
      exact (h₂.continuous.comp continuous_snd).continuousOn
    have hk : ContinuousOn (fun p : ℝ × ℝ => periodicKernel ω Lt (p.1 - p.2)) K := by
      exact ((continuous_periodicKernel ω Lt).comp (continuous_fst.sub continuous_snd)).continuousOn
    simpa using (hh₁.mul hh₂).mul hk
  have hG_int :
      Integrable
        (fun p : ℝ × ℝ =>
          (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2))
        ((volume.restrict I).prod (volume.restrict I)) := by
    have hK_compact : IsCompact K := by
      simpa [K, I] using
        (isCompact_Icc.prod isCompact_Icc : IsCompact (Set.Icc (-T) T ×ˢ Set.Icc (-T) T))
    have hG_int_on :
        IntegrableOn
          (fun p : ℝ × ℝ =>
            (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2))
          K volume :=
      hG_cont.integrableOn_compact hK_compact
    rw [IntegrableOn] at hG_int_on
    rw [Measure.prod_restrict I I]
    have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume := rfl
    simpa [K, hvol] using hG_int_on
  have hbox :
      ∫ t in (-T)..T, J t =
        ∫ p in K, (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := by
    calc
      ∫ t in (-T)..T, J t
        = ∫ t in I, J t ∂volume := by
            symm
            exact integral_Icc_eq_intervalIntegral (a := -T) (b := T) (by linarith [hT])
              (hJ_cont.intervalIntegrable _ _)
      _ = ∫ t, J t ∂(volume.restrict I) := by
            simp [I]
      _ = ∫ t, ∫ s,
            (h₁ t * h₂ s) * periodicKernel ω Lt (t - s)
              ∂(volume.restrict I) ∂(volume.restrict I) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
              dsimp [J, Fbox]
              rw [integral_Icc_eq_intervalIntegral (a := -T) (b := T) (by linarith [hT])]
              · symm
                rw [← intervalIntegral.integral_const_mul]
                apply intervalIntegral.integral_congr
                intro s hs
                ring
              · simpa [mul_assoc] using
                  (((h₂.continuous).mul
                    ((continuous_periodicKernel ω Lt).comp
                      (continuous_const.sub continuous_id))).intervalIntegrable
                    (μ := volume) (-T) T).const_mul (h₁ t)
      _ = ∫ p,
            ((fun p : ℝ × ℝ =>
              (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2)) p)
            ∂((volume.restrict I).prod (volume.restrict I)) := by
              symm
              exact MeasureTheory.integral_prod
                (fun p : ℝ × ℝ =>
                  (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2))
                hG_int
      _ = ∫ p in K, (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := by
            rw [Measure.prod_restrict I I]
            have hvol : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume := rfl
            simp [K, hvol]
  calc
    greenFunctionBilinear (E := SmoothMap_Circle Lt ℝ) ω hω per₁ per₂
      = ∫ p in I₀ ×ˢ I₀, G₀ p ∂volume := by
          simpa [I₀, G₀, per₁, per₂] using
            greenFunctionBilinear_eq_periodicKernel_integralOn_square ω Lt hω per₁ per₂
    _ = ∫ t in (0 : ℝ)..Lt, H t := houter_sq
    _ = ∫ t in (-T)..T, J t := hinterval
    _ = ∫ p in K, (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := hbox
    _ = ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := by
            simp [K, I]

private theorem periodizedSchwartz_mul_periodicKernel_integralOn_compactDiffBox_eq
    (ω Lt : ℝ) [Fact (0 < Lt)]
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (hLt_large : 4 * T < Lt) :
    ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
      (((@periodizeCLM Lt ‹Fact (0 < Lt)› h₁).toFun p.1 *
          (@periodizeCLM Lt ‹Fact (0 < Lt)› h₂).toFun p.2) *
        periodicKernel ω Lt (p.1 - p.2)) ∂volume =
    ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
      (h₁ p.1 * h₂ p.2) * periodicKernel ω Lt (p.1 - p.2) ∂volume := by
  have hK_meas :
      MeasurableSet (Set.Icc (-T) T ×ˢ Set.Icc (-T) T : Set (ℝ × ℝ)) :=
    measurableSet_Icc.prod measurableSet_Icc
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem hK_meas] with p hp
  have hper₁ :
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h₁).toFun p.1 = h₁ p.1 :=
    periodizeCLM_eq_on_symmetric_large_period
      (L := Lt) h₁ T hT hsupp₁ (by linarith [hLt_large]) p.1 hp.1
  have hper₂ :
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h₂).toFun p.2 = h₂ p.2 :=
    periodizeCLM_eq_on_symmetric_large_period
      (L := Lt) h₂ T hT hsupp₂ (by linarith [hLt_large]) p.2 hp.2
  simp [hper₁, hper₂]

private theorem freeKernel_le_of_mass_le
    (ω mass : ℝ) (hmass : 0 < mass) (hω : mass ≤ ω) (t : ℝ) :
    freeKernel ω t ≤ freeKernel mass t := by
  unfold freeKernel
  have hnum :
      Real.exp (-ω * |t|) ≤ Real.exp (-mass * |t|) := by
    apply (Real.exp_le_exp).2
    nlinarith [abs_nonneg t]
  have hinv :
      (2 * ω : ℝ)⁻¹ ≤ (2 * mass : ℝ)⁻¹ := by
    have hmass2_pos : 0 < (2 * mass : ℝ) := by positivity
    have hden_le : (2 * mass : ℝ) ≤ 2 * ω := by linarith
    simpa [one_div] using one_div_le_one_div_of_le hmass2_pos hden_le
  have hω_pos : 0 < ω := lt_of_lt_of_le hmass hω
  calc
    Real.exp (-ω * |t|) / (2 * ω)
      ≤ Real.exp (-mass * |t|) / (2 * ω) := by
          exact div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ (2 * ω : ℝ))
    _ = Real.exp (-mass * |t|) * (2 * ω : ℝ)⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ Real.exp (-mass * |t|) * (2 * mass : ℝ)⁻¹ := by
          exact mul_le_mul_of_nonneg_left hinv (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-mass * |t|) / (2 * mass) := by rw [div_eq_mul_inv]

private theorem massGapEnvelope_le_fixed_constant
    (mass : ℝ) (hmass : 0 < mass) {Lt : ℝ} (hLt : 1 ≤ Lt) :
    Real.exp (-mass * Lt / 2) / (mass * (1 - Real.exp (-mass * Lt))) ≤
      1 / (mass * (1 - Real.exp (-mass))) := by
  have hnum :
      Real.exp (-mass * Lt / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hmass_exp_lt : Real.exp (-mass) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hLt_exp_lt : Real.exp (-mass * Lt) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hden_base_pos : 0 < mass * (1 - Real.exp (-mass)) := by
    exact mul_pos hmass (sub_pos.mpr hmass_exp_lt)
  have hden_pos : 0 < mass * (1 - Real.exp (-mass * Lt)) := by
    exact mul_pos hmass (sub_pos.mpr hLt_exp_lt)
  have hLt_exp_le : Real.exp (-mass * Lt) ≤ Real.exp (-mass) := by
    apply (Real.exp_le_exp).2
    nlinarith
  have hden_le :
      mass * (1 - Real.exp (-mass)) ≤ mass * (1 - Real.exp (-mass * Lt)) := by
    apply mul_le_mul_of_nonneg_left
    · linarith
    · exact hmass.le
  calc
    Real.exp (-mass * Lt / 2) / (mass * (1 - Real.exp (-mass * Lt)))
      ≤ 1 / (mass * (1 - Real.exp (-mass * Lt))) := by
          exact div_le_div_of_nonneg_right hnum hden_pos.le
    _ ≤ 1 / (mass * (1 - Real.exp (-mass))) := by
          exact one_div_le_one_div_of_le hden_base_pos hden_le

omit hLs in
/-- A compact-box majorant for the periodized temporal integrals, uniform in the spatial mode once
`ω_a ≥ mass`. This is the quantitative input needed for Tannery on the spatial `tsum`. -/
private theorem periodizedSchwartz_mul_resolventFreq_integral_norm_le_massGapMajorant
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (mass : ℝ) (hmass : 0 < mass)
    (Lt : ℝ) [Fact (0 < Lt)]
    (hLt_large : 4 * T + 1 ≤ Lt)
    (a : ℕ) :
    |∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
        ((@periodizeCLM Lt ‹Fact (0 < Lt)› h₁).toFun p.1 *
          (@periodizeCLM Lt ‹Fact (0 < Lt)› h₂).toFun p.2) *
        periodicKernel (resolventFreq Ls mass a) Lt (p.1 - p.2) ∂volume| ≤
      ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
        |h₁ p.1 * h₂ p.2| *
          (freeKernel mass (p.1 - p.2) + 1 / (mass * (1 - Real.exp (-mass)))) ∂volume := by
  let K : Set (ℝ × ℝ) := Set.Icc (-T) T ×ˢ Set.Icc (-T) T
  let ω : ℝ := resolventFreq Ls mass a
  let F : ℝ × ℝ → ℝ := fun p =>
    ((@periodizeCLM Lt ‹Fact (0 < Lt)› h₁).toFun p.1 *
      (@periodizeCLM Lt ‹Fact (0 < Lt)› h₂).toFun p.2) *
      periodicKernel ω Lt (p.1 - p.2)
  let G : ℝ × ℝ → ℝ := fun p =>
    |h₁ p.1 * h₂ p.2| *
      (freeKernel mass (p.1 - p.2) + 1 / (mass * (1 - Real.exp (-mass))))
  have hLt_pos : 0 < Lt := Fact.out
  have hK_compact : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hK_meas : MeasurableSet K := hK_compact.isClosed.measurableSet
  have hω_ge : mass ≤ ω := resolventFreq_mass_le Ls mass hmass.le a
  have hF_cont : ContinuousOn F K := by
    have hper₁ : ContinuousOn
        (fun p : ℝ × ℝ => (@periodizeCLM Lt ‹Fact (0 < Lt)› h₁).toFun p.1) K := by
      exact ((@periodizeCLM Lt ‹Fact (0 < Lt)› h₁).continuous.comp continuous_fst).continuousOn
    have hper₂ : ContinuousOn
        (fun p : ℝ × ℝ => (@periodizeCLM Lt ‹Fact (0 < Lt)› h₂).toFun p.2) K := by
      exact ((@periodizeCLM Lt ‹Fact (0 < Lt)› h₂).continuous.comp continuous_snd).continuousOn
    have hk : ContinuousOn (fun p : ℝ × ℝ => periodicKernel ω Lt (p.1 - p.2)) K := by
      exact ((continuous_periodicKernel ω Lt).comp (continuous_fst.sub continuous_snd)).continuousOn
    simpa [F] using (hper₁.mul hper₂).mul hk
  have hG_cont : ContinuousOn G K := by
    have hh : ContinuousOn (fun p : ℝ × ℝ => |h₁ p.1 * h₂ p.2|) K := by
      exact ((h₁.continuous.comp continuous_fst).continuousOn.mul
        (h₂.continuous.comp continuous_snd).continuousOn).abs
    have hfree : ContinuousOn (fun p : ℝ × ℝ => freeKernel mass (p.1 - p.2)) K := by
      exact ((continuous_freeKernel mass).comp (continuous_fst.sub continuous_snd)).continuousOn
    have hconst : ContinuousOn
        (fun _ : ℝ × ℝ => 1 / (mass * (1 - Real.exp (-mass)))) K := by
      exact continuous_const.continuousOn
    have hk : ContinuousOn
        (fun p : ℝ × ℝ =>
          freeKernel mass (p.1 - p.2) + 1 / (mass * (1 - Real.exp (-mass)))) K := by
      exact hfree.add hconst
    simpa [G] using hh.mul hk
  have hF_int : Integrable F (volume.restrict K) := by
    simpa [K] using hF_cont.integrableOn_compact hK_compact
  have hG_int : Integrable G (volume.restrict K) := by
    simpa [K] using hG_cont.integrableOn_compact hK_compact
  have hFG_le : ∀ p ∈ K, |F p| ≤ G p := by
    rintro p hp
    rcases p with ⟨t, s⟩
    have ht_mem : t ∈ Set.Icc (-T) T := hp.1
    have hs_mem : s ∈ Set.Icc (-T) T := hp.2
    have ht_abs : |t| ≤ T := by
      simpa [Set.mem_Icc, abs_le] using ht_mem
    have hs_abs : |s| ≤ T := by
      simpa [Set.mem_Icc, abs_le] using hs_mem
    have hper₁ :
        (@periodizeCLM Lt ‹Fact (0 < Lt)› h₁).toFun t = h₁ t :=
      periodizeCLM_eq_on_symmetric_large_period
        (L := Lt) h₁ T hT hsupp₁ (by linarith [hLt_large]) t ht_mem
    have hper₂ :
        (@periodizeCLM Lt ‹Fact (0 < Lt)› h₂).toFun s = h₂ s :=
      periodizeCLM_eq_on_symmetric_large_period
        (L := Lt) h₂ T hT hsupp₂ (by linarith [hLt_large]) s hs_mem
    have hdiff_le : |t - s| ≤ 2 * T := by
      calc
        |t - s| ≤ |t| + |s| := by
            simpa using (abs_sub_le t 0 s)
        _ ≤ T + T := add_le_add ht_abs hs_abs
        _ = 2 * T := by ring
    have hdiff_lt : |t - s| < Lt / 2 := by
      have hhalf : 2 * T < Lt / 2 := by
        linarith [hLt_large]
      exact lt_of_le_of_lt hdiff_le hhalf
    have henv :
        |periodicKernel ω Lt (t - s) - freeKernel ω (t - s)| ≤
          1 / (mass * (1 - Real.exp (-mass))) := by
      refine
        (abs_sub_free_le_uniform_mass_gap ω mass hmass hω_ge
          (t - s) Lt hLt_pos hdiff_lt).trans ?_
      refine massGapEnvelope_le_fixed_constant mass hmass ?_
      linarith [hLt_large]
    have hfree :
        freeKernel ω (t - s) ≤ freeKernel mass (t - s) :=
      freeKernel_le_of_mass_le ω mass hmass hω_ge (t - s)
    have hk_abs :
        |periodicKernel ω Lt (t - s)| ≤
          freeKernel mass (t - s) + 1 / (mass * (1 - Real.exp (-mass))) := by
      have htriangle :
          |periodicKernel ω Lt (t - s)| ≤
            |periodicKernel ω Lt (t - s) - freeKernel ω (t - s)| +
              |freeKernel ω (t - s)| := by
        simpa using
          (abs_sub_le (periodicKernel ω Lt (t - s)) (freeKernel ω (t - s)) 0)
      have hfree_nonneg : 0 ≤ freeKernel ω (t - s) := by
        unfold freeKernel
        have hω_pos : 0 < ω := lt_of_lt_of_le hmass hω_ge
        positivity
      calc
        |periodicKernel ω Lt (t - s)|
          ≤ |periodicKernel ω Lt (t - s) - freeKernel ω (t - s)| +
              |freeKernel ω (t - s)| := htriangle
        _ ≤ 1 / (mass * (1 - Real.exp (-mass))) + freeKernel ω (t - s) := by
              rw [abs_of_nonneg hfree_nonneg]
              linarith
        _ ≤ 1 / (mass * (1 - Real.exp (-mass))) + freeKernel mass (t - s) := by
              linarith
        _ = freeKernel mass (t - s) + 1 / (mass * (1 - Real.exp (-mass))) := by ring
    calc
      |F (t, s)| = |h₁ t * h₂ s| * |periodicKernel ω Lt (t - s)| := by
        simp [F, hper₁, hper₂, abs_mul]
      _ ≤ |h₁ t * h₂ s| *
            (freeKernel mass (t - s) + 1 / (mass * (1 - Real.exp (-mass)))) := by
              exact mul_le_mul_of_nonneg_left hk_abs (abs_nonneg _)
      _ = G (t, s) := by
            simp [G]
  have hmono :
      ∫ p, |F p| ∂(volume.restrict K) ≤ ∫ p, G p ∂(volume.restrict K) := by
    refine integral_mono_ae hF_int.norm hG_int ?_
    filter_upwards [ae_restrict_mem hK_meas] with p hp
    exact hFG_le p hp
  calc
    |∫ p in K, F p ∂volume|
      = ‖∫ p, F p ∂(volume.restrict K)‖ := by
          simp [K, Real.norm_eq_abs]
    _ ≤ ∫ p, |F p| ∂(volume.restrict K) := by
          simpa [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm (μ := volume.restrict K) F)
    _ ≤ ∫ p, G p ∂(volume.restrict K) := hmono
    _ = ∫ p in K, G p ∂volume := by
          simp [K]
    _ = ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          |h₁ p.1 * h₂ p.2| *
            (freeKernel mass (p.1 - p.2) + 1 / (mass * (1 - Real.exp (-mass)))) ∂volume := by
          simp [K, G]

/-- Under the remaining one-dimensional temporal bridge from circle Green forms to the explicit
periodic kernel, the pure compact-support torus-to-cylinder covariance convergence follows by
Tannery's theorem over the spatial modes. This is the exact Glimm-Jaffe / Simon modewise argument,
with the unresolved content isolated to the 1D periodic Green identity. -/
private theorem asymTorusGreen_tendsto_physicalCylinderGreen_pure_of_eventually_temporalBridge
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop)
    (htemporal :
      ∀ᶠ k in atTop, ∀ a : ℕ,
        greenFunctionBilinear (E := SmoothMap_Circle (Lt k) ℝ)
          (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a)
          (@periodizeCLM (Lt k) (hLt k) h₁)
          (@periodizeCLM (Lt k) (hLt k) h₂) =
        ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
            (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
            periodicKernel (resolventFreq Ls mass a) (Lt k) (p.1 - p.2) ∂volume) :
    Tendsto
      (fun k =>
        @asymTorusContinuumGreen (Lt k) Ls (hLt k) _ mass hmass
          (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
            (NuclearTensorProduct.pure g₁ h₁))
          (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
            (NuclearTensorProduct.pure g₂ h₂)))
      atTop
      (nhds (physicalCylinderGreen_pure (Ls := Ls) mass hmass g₁ g₂ h₁ h₂)) := by
  let K : Set (ℝ × ℝ) := Set.Icc (-T) T ×ˢ Set.Icc (-T) T
  let F : ℕ → ℕ → ℝ := fun k a =>
    (DyninMityaginSpace.coeff a g₁ * DyninMityaginSpace.coeff a g₂) *
      (∫ p in K,
        ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
          (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
          periodicKernel (resolventFreq Ls mass a) (Lt k) (p.1 - p.2) ∂volume)
  let G : ℕ → ℝ := fun a =>
    (DyninMityaginSpace.coeff a g₁ * DyninMityaginSpace.coeff a g₂) *
      (∫ p in K,
        (h₁ p.1 * h₂ p.2) * freeKernel (resolventFreq Ls mass a) (p.1 - p.2) ∂volume)
  let Cmaj : ℝ :=
    ∫ p in K,
      |h₁ p.1 * h₂ p.2| *
        (freeKernel mass (p.1 - p.2) + 1 / (mass * (1 - Real.exp (-mass)))) ∂volume
  let bound : ℕ → ℝ := fun a =>
    Cmaj * |DyninMityaginSpace.coeff a g₁ * DyninMityaginSpace.coeff a g₂|
  have hCmaj_nonneg : 0 ≤ Cmaj := by
    dsimp [Cmaj]
    apply integral_nonneg
    intro p
    have hconst_nonneg : 0 ≤ 1 / (mass * (1 - Real.exp (-mass))) := by
      have hmass_exp_lt : Real.exp (-mass) < 1 := by
        rw [Real.exp_lt_one_iff]
        nlinarith
      have hden_pos : 0 < mass * (1 - Real.exp (-mass)) := by
        exact mul_pos hmass (sub_pos.mpr hmass_exp_lt)
      exact one_div_nonneg.mpr hden_pos.le
    have hfree_nonneg : 0 ≤ freeKernel mass (p.1 - p.2) := by
      unfold freeKernel
      positivity
    exact mul_nonneg (abs_nonneg _) (add_nonneg hfree_nonneg hconst_nonneg)
  have hbound_summable : Summable bound := by
    dsimp [bound]
    exact ((l2InnerProduct_summable g₁ g₂).abs.mul_left Cmaj)
  have hpointwise : ∀ a : ℕ, Tendsto (fun k => F k a) atTop (nhds (G a)) := by
    intro a
    dsimp [F, G]
    simpa [K, mul_assoc, mul_left_comm, mul_comm] using
      Filter.Tendsto.const_mul
        (DyninMityaginSpace.coeff a g₁ * DyninMityaginSpace.coeff a g₂)
        (periodizedSchwartz_mul_periodicKernel_tendsto_freeKernel_integralOn_compactDiffBox
          (h₁ := h₁) (h₂ := h₂) T hT hsupp₁ hsupp₂
          (ω := resolventFreq Ls mass a) (mass := mass) hmass
          (resolventFreq_mass_le Ls mass hmass.le a) Lt hLt hLt_tend)
  have hlarge : ∀ᶠ k in atTop, 4 * T + 1 ≤ Lt k :=
    (Filter.tendsto_atTop.mp hLt_tend) (4 * T + 1)
  have hbound_eventually : ∀ᶠ k in atTop, ∀ a : ℕ, |F k a| ≤ bound a := by
    filter_upwards [hlarge] with k hk a
    letI : Fact (0 < Lt k) := hLt k
    have htemp_bd :=
      periodizedSchwartz_mul_resolventFreq_integral_norm_le_massGapMajorant
        (Ls := Ls) (h₁ := h₁) (h₂ := h₂) T hT hsupp₁ hsupp₂ mass hmass
        (Lt := Lt k) hk a
    calc
      |F k a|
        = |DyninMityaginSpace.coeff a g₁ * DyninMityaginSpace.coeff a g₂| *
            |∫ p in K,
              ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
                (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
                periodicKernel (resolventFreq Ls mass a) (Lt k) (p.1 - p.2) ∂volume| := by
                dsimp [F]
                rw [abs_mul]
      _ ≤ |DyninMityaginSpace.coeff a g₁ * DyninMityaginSpace.coeff a g₂| * Cmaj := by
            exact mul_le_mul_of_nonneg_left htemp_bd (abs_nonneg _)
      _ = bound a := by
            simp [bound, Cmaj, mul_comm]
  have hsum_tend :
      Tendsto (fun k => ∑' a : ℕ, F k a) atTop (nhds (∑' a : ℕ, G a)) := by
    apply tendsto_tsum_of_dominated_convergence (bound := bound)
    · exact hbound_summable
    · exact hpointwise
    · exact hbound_eventually
  have htorus_eventually :
      ∀ᶠ k in atTop,
        @asymTorusContinuumGreen (Lt k) Ls (hLt k) _ mass hmass
            (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
              (NuclearTensorProduct.pure g₁ h₁))
            (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
              (NuclearTensorProduct.pure g₂ h₂)) =
          ∑' a : ℕ, F k a := by
    filter_upwards [htemporal] with k hk
    rw [asymTorusContinuumGreen_embed_pure_eq_tsum_temporalGreen
      (Ls := Ls) (Lt := Lt k) (mass := mass) (hmass := hmass)
      (g₁ := g₁) (g₂ := g₂) (h₁ := h₁) (h₂ := h₂)]
    apply tsum_congr
    intro a
    rw [hk a]
  have hmain :
      Tendsto
        (fun k =>
          @asymTorusContinuumGreen (Lt k) Ls (hLt k) _ mass hmass
            (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
              (NuclearTensorProduct.pure g₁ h₁))
            (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
              (NuclearTensorProduct.pure g₂ h₂)))
        atTop
        (nhds (∑' a : ℕ, G a)) := by
    have hsum_eventually :
        (fun k => ∑' a : ℕ, F k a) =ᶠ[atTop]
          (fun k =>
            @asymTorusContinuumGreen (Lt k) Ls (hLt k) _ mass hmass
              (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
                (NuclearTensorProduct.pure g₁ h₁))
              (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
                (NuclearTensorProduct.pure g₂ h₂))) := by
      filter_upwards [htorus_eventually] with k hk
      exact hk.symm
    exact hsum_tend.congr' hsum_eventually
  have htarget :
      physicalCylinderGreen_pure (Ls := Ls) mass hmass g₁ g₂ h₁ h₂ =
        ∑' a : ℕ, G a := by
    dsimp [G, K]
    exact physicalCylinderGreen_pure_eq_tsum_freeKernel_integralOn_compactDiffBox
      (Ls := Ls) mass hmass g₁ g₂ h₁ h₂ T hsupp₁ hsupp₂
  simpa [htarget] using hmain

/-- Compactly supported pure tensors satisfy torus-to-cylinder covariance convergence once the
temporal bridge is supplied by the compact-box periodic-kernel identity proved above. -/
private theorem asymTorusGreen_tendsto_physicalCylinderGreen_pure
    (mass : ℝ) (hmass : 0 < mass)
    (g₁ g₂ : SmoothMap_Circle Ls ℝ)
    (h₁ h₂ : SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ t, T < |t| → h₁ t = 0)
    (hsupp₂ : ∀ t, T < |t| → h₂ t = 0)
    (Lt : ℕ → ℝ) (hLt : ∀ k, Fact (0 < Lt k))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto
      (fun k =>
        @asymTorusContinuumGreen (Lt k) Ls (hLt k) _ mass hmass
          (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
            (NuclearTensorProduct.pure g₁ h₁))
          (@cylinderToTorusEmbed (Lt k) Ls (hLt k) _
            (NuclearTensorProduct.pure g₂ h₂)))
      atTop
      (nhds (physicalCylinderGreen_pure (Ls := Ls) mass hmass g₁ g₂ h₁ h₂)) := by
  have hlarge : ∀ᶠ k in atTop, 4 * T + 1 ≤ Lt k :=
    (Filter.tendsto_atTop.mp hLt_tend) (4 * T + 1)
  have htemporal :
      ∀ᶠ k in atTop, ∀ a : ℕ,
        greenFunctionBilinear (E := SmoothMap_Circle (Lt k) ℝ)
          (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a)
          (@periodizeCLM (Lt k) (hLt k) h₁)
          (@periodizeCLM (Lt k) (hLt k) h₂) =
        ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
          ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
            (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
            periodicKernel (resolventFreq Ls mass a) (Lt k) (p.1 - p.2) ∂volume := by
    filter_upwards [hlarge] with k hk a
    letI : Fact (0 < Lt k) := hLt k
    have hk' : 4 * T < Lt k := by
      linarith
    calc
      greenFunctionBilinear (E := SmoothMap_Circle (Lt k) ℝ)
          (resolventFreq Ls mass a) (resolventFreq_pos Ls mass hmass a)
          (@periodizeCLM (Lt k) (hLt k) h₁)
          (@periodizeCLM (Lt k) (hLt k) h₂)
        =
          ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
            (h₁ p.1 * h₂ p.2) *
              periodicKernel (resolventFreq Ls mass a) (Lt k) (p.1 - p.2) ∂volume := by
            exact greenFunctionBilinear_eq_periodicKernel_integralOn_compactDiffBox
              (ω := resolventFreq Ls mass a) (Lt := Lt k)
              (hω := resolventFreq_pos Ls mass hmass a)
              (h₁ := h₁) (h₂ := h₂) T hT hsupp₁ hsupp₂ hk'
      _ =
          ∫ p in Set.Icc (-T) T ×ˢ Set.Icc (-T) T,
            ((@periodizeCLM (Lt k) (hLt k) h₁).toFun p.1 *
              (@periodizeCLM (Lt k) (hLt k) h₂).toFun p.2) *
              periodicKernel (resolventFreq Ls mass a) (Lt k) (p.1 - p.2) ∂volume := by
            symm
            exact periodizedSchwartz_mul_periodicKernel_integralOn_compactDiffBox_eq
              (ω := resolventFreq Ls mass a) (Lt := Lt k)
              (h₁ := h₁) (h₂ := h₂) T hT hsupp₁ hsupp₂ hk'
  exact asymTorusGreen_tendsto_physicalCylinderGreen_pure_of_eventually_temporalBridge
    (Ls := Ls) mass hmass g₁ g₂ h₁ h₂ T hT hsupp₁ hsupp₂ Lt hLt hLt_tend htemporal

/-- Bilinearity upgrades compact-support pure convergence to finite sums of compactly supported pure
tensors, with the target given by the physically normalized pure-cylinder form termwise. This
isolates the remaining work to the genuine density/normalization extension from finite-rank compact
support to arbitrary cylinder test functions. -/
private theorem asymTorusGreen_tendsto_physicalCylinderGreen_finset_sum_of_pure
    (mass : ℝ) (hmass : 0 < mass)
    {ι₁ ι₂ : Type*}
    (s₁ : Finset ι₁) (s₂ : Finset ι₂)
    (a : ι₁ → ℝ) (b : ι₂ → ℝ)
    (g₁ : ι₁ → SmoothMap_Circle Ls ℝ)
    (h₁ : ι₁ → SchwartzMap ℝ ℝ)
    (g₂ : ι₂ → SmoothMap_Circle Ls ℝ)
    (h₂ : ι₂ → SchwartzMap ℝ ℝ)
    (T : ℝ) (hT : 0 < T)
    (hsupp₁ : ∀ i t, T < |t| → h₁ i t = 0)
    (hsupp₂ : ∀ j t, T < |t| → h₂ j t = 0)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto (fun n =>
      @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
          (∑ i ∈ s₁, a i • NuclearTensorProduct.pure (g₁ i) (h₁ i)))
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
          (∑ j ∈ s₂, b j • NuclearTensorProduct.pure (g₂ j) (h₂ j))))
      atTop
      (nhds
        (physicalCylinderGreen (Ls := Ls) mass hmass
          (∑ i ∈ s₁, a i • NuclearTensorProduct.pure (g₁ i) (h₁ i))
          (∑ j ∈ s₂, b j • NuclearTensorProduct.pure (g₂ j) (h₂ j)))) := by
  classical
  set f : CylinderTestFunction Ls :=
    ∑ i ∈ s₁, a i • NuclearTensorProduct.pure (g₁ i) (h₁ i)
  set g : CylinderTestFunction Ls :=
    ∑ j ∈ s₂, b j • NuclearTensorProduct.pure (g₂ j) (h₂ j)
  have hsum :
      Tendsto
        (fun n =>
          ∑ i ∈ s₁, ∑ j ∈ s₂,
            a i * b j *
              @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
                (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
                  (NuclearTensorProduct.pure (g₁ i) (h₁ i)))
                (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
                  (NuclearTensorProduct.pure (g₂ j) (h₂ j))))
        atTop
        (nhds
          (∑ i ∈ s₁, ∑ j ∈ s₂,
            a i * b j *
              physicalCylinderGreen_pure (Ls := Ls) mass hmass
                (g₁ i) (g₂ j) (h₁ i) (h₂ j))) := by
    apply tendsto_finset_sum
    intro i hi
    apply tendsto_finset_sum
    intro j hj
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Filter.Tendsto.const_mul (a i * b j)
        (asymTorusGreen_tendsto_physicalCylinderGreen_pure
          (Ls := Ls) mass hmass (g₁ i) (g₂ j) (h₁ i) (h₂ j) T hT
          (hsupp₁ i) (hsupp₂ j) Lt hLt hLt_tend)
  have hleft :
      (fun n =>
        @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
          (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ f)
          (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ g)) =
      (fun n =>
        ∑ i ∈ s₁, ∑ j ∈ s₂,
          a i * b j *
            @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
              (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
                (NuclearTensorProduct.pure (g₁ i) (h₁ i)))
              (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _
                (NuclearTensorProduct.pure (g₂ j) (h₂ j)))) := by
    funext n
    simpa [f, g, asymTorusContinuumGreen, mul_assoc, mul_left_comm, mul_comm] using
      (GaussianField.greenFunctionBilinear_finset_sum
        (E := AsymTorusTestFunction (Lt n) Ls) mass hmass s₁ s₂ a b
        (fun i =>
          @cylinderToTorusEmbed (Lt n) Ls (hLt n) _
            (NuclearTensorProduct.pure (g₁ i) (h₁ i)))
        (fun j =>
          @cylinderToTorusEmbed (Lt n) Ls (hLt n) _
            (NuclearTensorProduct.pure (g₂ j) (h₂ j))))
  have hright :
      physicalCylinderGreen (Ls := Ls) mass hmass f g =
        ∑ i ∈ s₁, ∑ j ∈ s₂,
          a i * b j *
            physicalCylinderGreen_pure (Ls := Ls) mass hmass
              (g₁ i) (g₂ j) (h₁ i) (h₂ j) := by
    calc
      physicalCylinderGreen (Ls := Ls) mass hmass f g =
          ∑ i ∈ s₁, ∑ j ∈ s₂,
            a i * b j *
              physicalCylinderGreen (Ls := Ls) mass hmass
                (NuclearTensorProduct.pure (g₁ i) (h₁ i))
                (NuclearTensorProduct.pure (g₂ j) (h₂ j)) := by
            simpa [f, g] using
              (physicalCylinderGreen_finset_sum (Ls := Ls) mass hmass s₁ s₂ a b
                (fun i => NuclearTensorProduct.pure (g₁ i) (h₁ i))
                (fun j => NuclearTensorProduct.pure (g₂ j) (h₂ j)))
      _ = ∑ i ∈ s₁, ∑ j ∈ s₂,
            a i * b j *
              physicalCylinderGreen_pure (Ls := Ls) mass hmass
                (g₁ i) (g₂ j) (h₁ i) (h₂ j) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [physicalCylinderGreen_apply_pure_eq]
  rw [hleft, hright]
  exact hsum

private theorem physicalCylinderGreen_symm
    (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction Ls) :
    physicalCylinderGreen (Ls := Ls) mass hmass f g =
      physicalCylinderGreen (Ls := Ls) mass hmass g f := by
  simpa [physicalCylinderGreen] using
    (cylinderGreen_symm (L := Ls) mass hmass
      (cylinderTwoPiRescale Ls f)
      (cylinderTwoPiRescale Ls g))

private theorem physicalCylinderGreen_nonneg
    (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction Ls) :
    0 ≤ physicalCylinderGreen (Ls := Ls) mass hmass f f := by
  simpa [physicalCylinderGreen] using
    (cylinderGreen_nonneg Ls mass hmass (cylinderTwoPiRescale Ls f))

private theorem physicalCylinderGreen_sub_left
    (mass : ℝ) (hmass : 0 < mass)
    (f g h : CylinderTestFunction Ls) :
    physicalCylinderGreen (Ls := Ls) mass hmass (f - g) h =
      physicalCylinderGreen (Ls := Ls) mass hmass f h -
        physicalCylinderGreen (Ls := Ls) mass hmass g h := by
  simpa [physicalCylinderGreen, sub_eq_add_neg, smul_eq_mul, map_sub, map_add, map_neg,
    map_smul, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using
    (cylinderGreen_bilinear (L := Ls) mass hmass (-1 : ℝ)
      (cylinderTwoPiRescale Ls g)
      (cylinderTwoPiRescale Ls f)
      (cylinderTwoPiRescale Ls h))

private theorem physicalCylinderGreen_sub_right
    (mass : ℝ) (hmass : 0 < mass)
    (f g h : CylinderTestFunction Ls) :
    physicalCylinderGreen (Ls := Ls) mass hmass h (f - g) =
      physicalCylinderGreen (Ls := Ls) mass hmass h f -
        physicalCylinderGreen (Ls := Ls) mass hmass h g := by
  rw [physicalCylinderGreen_symm (Ls := Ls) mass hmass h (f - g),
    physicalCylinderGreen_symm (Ls := Ls) mass hmass h f,
    physicalCylinderGreen_symm (Ls := Ls) mass hmass h g,
    physicalCylinderGreen_sub_left (Ls := Ls) mass hmass f g h]

private theorem asymTorusContinuumGreen_embed_symm
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction Ls) :
    asymTorusContinuumGreen Lt Ls mass hmass
      (cylinderToTorusEmbed Lt Ls f)
      (cylinderToTorusEmbed Lt Ls g) =
    asymTorusContinuumGreen Lt Ls mass hmass
      (cylinderToTorusEmbed Lt Ls g)
      (cylinderToTorusEmbed Lt Ls f) := by
  simpa [asymTorusContinuumGreen] using
    (greenFunctionBilinear_symm mass hmass
      (cylinderToTorusEmbed Lt Ls f)
      (cylinderToTorusEmbed Lt Ls g))

private theorem asymTorusContinuumGreen_embed_sub_left
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (f g h : CylinderTestFunction Ls) :
    asymTorusContinuumGreen Lt Ls mass hmass
      (cylinderToTorusEmbed Lt Ls (f - g))
      (cylinderToTorusEmbed Lt Ls h) =
    asymTorusContinuumGreen Lt Ls mass hmass
      (cylinderToTorusEmbed Lt Ls f)
      (cylinderToTorusEmbed Lt Ls h) -
        asymTorusContinuumGreen Lt Ls mass hmass
          (cylinderToTorusEmbed Lt Ls g)
          (cylinderToTorusEmbed Lt Ls h) := by
  simpa [asymTorusContinuumGreen, map_sub] using
    (greenFunctionBilinear_sub_left mass hmass
      (cylinderToTorusEmbed Lt Ls f)
      (cylinderToTorusEmbed Lt Ls g)
      (cylinderToTorusEmbed Lt Ls h))

private theorem asymTorusContinuumGreen_embed_sub_right
    (Lt : ℝ) [hLt : Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (f g h : CylinderTestFunction Ls) :
    asymTorusContinuumGreen Lt Ls mass hmass
      (cylinderToTorusEmbed Lt Ls h)
      (cylinderToTorusEmbed Lt Ls (f - g)) =
    asymTorusContinuumGreen Lt Ls mass hmass
      (cylinderToTorusEmbed Lt Ls h)
      (cylinderToTorusEmbed Lt Ls f) -
        asymTorusContinuumGreen Lt Ls mass hmass
          (cylinderToTorusEmbed Lt Ls h)
          (cylinderToTorusEmbed Lt Ls g) := by
  rw [asymTorusContinuumGreen_embed_symm (Ls := Ls) Lt mass hmass h (f - g),
    asymTorusContinuumGreen_embed_symm (Ls := Ls) Lt mass hmass h f,
    asymTorusContinuumGreen_embed_symm (Ls := Ls) Lt mass hmass h g,
    asymTorusContinuumGreen_embed_sub_left (Ls := Ls) Lt mass hmass f g h]
-- This finite-rank approximation proof expands several bilinear estimates and
-- needs a larger heartbeat budget than the default elaborator limit.
set_option maxHeartbeats 800000 in
/-- Extend the compact-support finite-rank convergence theorem to arbitrary cylinder test functions
by approximating both arguments in a seminorm that simultaneously controls the torus-side uniform
bound and the cylinder-side limiting bilinear form. -/
theorem asymTorusGreen_tendsto_physicalCylinderGreen
    (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction Ls)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop) :
    Tendsto (fun n =>
      @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ f)
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ g))
      atTop (nhds (physicalCylinderGreen (Ls := Ls) mass hmass f g)) := by
  obtain ⟨C, hC_pos, qt, hqt_cont, hqt_bound⟩ :=
    asymTorusGreen_uniform_product_seminorm_bound (Ls := Ls) mass hmass
  obtain ⟨qp, hqp_cont, hqp_bound⟩ :=
    physicalCylinderGreen_product_seminorm_bound (Ls := Ls) mass hmass
  set qsum : Seminorm ℝ (CylinderTestFunction Ls) := qt + qp
  have hqsum_cont : Continuous qsum := by
    dsimp [qsum]
    exact hqt_cont.add hqp_cont
  have hqt_le_qsum : ∀ u : CylinderTestFunction Ls, qt u ≤ qsum u := by
    intro u
    dsimp [qsum]
    linarith [apply_nonneg qp u]
  have hqp_le_qsum : ∀ u : CylinderTestFunction Ls, qp u ≤ qsum u := by
    intro u
    dsimp [qsum]
    linarith [apply_nonneg qt u]
  let A : ℕ → CylinderTestFunction Ls → CylinderTestFunction Ls → ℝ :=
    fun n u v =>
      @asymTorusContinuumGreen (Lt n) Ls (hLt n) _ mass hmass
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ u)
        (@cylinderToTorusEmbed (Lt n) Ls (hLt n) _ v)
  let P : CylinderTestFunction Ls → CylinderTestFunction Ls → ℝ :=
    physicalCylinderGreen (Ls := Ls) mass hmass
  rw [Metric.tendsto_nhds]
  intro ε hε
  set Qf : ℝ := qsum f
  set Qg : ℝ := qsum g
  have hQf_nonneg : 0 ≤ Qf := by
    dsimp [Qf]
    exact apply_nonneg qsum f
  have hQg_nonneg : 0 ≤ Qg := by
    dsimp [Qg]
    exact apply_nonneg qsum g
  set M : ℝ := 4 * (C + 1) * (Qf + Qg + 1)
  have hM_pos : 0 < M := by
    dsimp [M]
    nlinarith [hC_pos, hQf_nonneg, hQg_nonneg]
  set δ : ℝ := min 1 (ε / M)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (div_pos hε hM_pos)
  have hδ_le_one : δ ≤ 1 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_le_eps : δ ≤ ε / M := by
    dsimp [δ]
    exact min_le_right _ _
  obtain ⟨sf, Nf, hf_small0⟩ :=
    exists_compactSupport_basisApprox (Ls := Ls) qsum hqsum_cont f hδ_pos
  obtain ⟨sg, Ng, hg_small0⟩ :=
    exists_compactSupport_basisApprox (Ls := Ls) qsum hqsum_cont g hδ_pos
  set f₀ : CylinderTestFunction Ls := basisCutoffPartial (Ls := Ls) f sf Nf
  set g₀ : CylinderTestFunction Ls := basisCutoffPartial (Ls := Ls) g sg Ng
  have hf_small : qsum (f - f₀) < δ := by
    simpa [f₀] using hf_small0
  have hg_small : qsum (g - g₀) < δ := by
    simpa [g₀] using hg_small0
  have hf_small_sym : qsum (f₀ - f) < δ := by
    have hneg : f₀ - f = -(f - f₀) := by
      abel
    rw [hneg, map_neg_eq_map]
    exact hf_small
  have hg_small_sym : qsum (g₀ - g) < δ := by
    have hneg : g₀ - g = -(g - g₀) := by
      abel
    rw [hneg, map_neg_eq_map]
    exact hg_small
  have hqsum_f₀ : qsum f₀ ≤ Qf + δ := by
    have hdecomp : (f₀ - f) + f = f₀ := by
      abel
    calc
      qsum f₀ = qsum ((f₀ - f) + f) := by
        exact congrArg qsum hdecomp.symm
      _ ≤ qsum (f₀ - f) + qsum f := qsum.add_le' _ _
      _ ≤ δ + qsum f := by
        have hsmall : qsum (f₀ - f) ≤ δ := le_of_lt hf_small_sym
        linarith
      _ = Qf + δ := by
        simp [Qf, add_comm]
  have hqsum_g₀ : qsum g₀ ≤ Qg + δ := by
    have hdecomp : (g₀ - g) + g = g₀ := by
      abel
    calc
      qsum g₀ = qsum ((g₀ - g) + g) := by
        exact congrArg qsum hdecomp.symm
      _ ≤ qsum (g₀ - g) + qsum g := qsum.add_le' _ _
      _ ≤ δ + qsum g := by
        have hsmall : qsum (g₀ - g) ≤ δ := le_of_lt hg_small_sym
        linarith
      _ = Qg + δ := by
        simp [Qg, add_comm]
  have hqt_f₀ : qt f₀ ≤ Qf + 1 := by
    have hqt_f₀' : qt f₀ ≤ Qf + δ := le_trans (hqt_le_qsum f₀) hqsum_f₀
    nlinarith
  have hqp_f₀ : qp f₀ ≤ Qf + 1 := by
    have hqp_f₀' : qp f₀ ≤ Qf + δ := le_trans (hqp_le_qsum f₀) hqsum_f₀
    nlinarith
  set T : ℝ := 2 * (((max Nf Ng : ℕ) : ℝ) + 1)
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hsupp_f₀ :
      ∀ m t, T < |t| →
        schwartzCutoffCLM Nf (cylinderBasisTemporal m) t = 0 := by
    intro m t ht
    apply schwartzCutoffCLM_eq_zero_of_two_mul_lt_abs
    have hNf_le : (Nf : ℝ) ≤ (max Nf Ng : ℕ) := by
      exact_mod_cast Nat.le_max_left Nf Ng
    dsimp [T] at ht ⊢
    linarith
  have hsupp_g₀ :
      ∀ m t, T < |t| →
        schwartzCutoffCLM Ng (cylinderBasisTemporal m) t = 0 := by
    intro m t ht
    apply schwartzCutoffCLM_eq_zero_of_two_mul_lt_abs
    have hNg_le : (Ng : ℝ) ≤ (max Nf Ng : ℕ) := by
      exact_mod_cast Nat.le_max_right Nf Ng
    dsimp [T] at ht ⊢
    linarith
  have hmain :
      Tendsto (fun n => A n f₀ g₀) atTop (nhds (P f₀ g₀)) := by
    simpa [A, P, f₀, g₀, basisCutoffPartial] using
      (asymTorusGreen_tendsto_physicalCylinderGreen_finset_sum_of_pure
        (Ls := Ls) mass hmass
        (s₁ := sf) (s₂ := sg)
        (a := fun m => DyninMityaginSpace.coeff m f)
        (b := fun m => DyninMityaginSpace.coeff m g)
        (g₁ := fun m => cylinderBasisSpatial (Ls := Ls) m)
        (h₁ := fun m => schwartzCutoffCLM Nf (cylinderBasisTemporal m))
        (g₂ := fun m => cylinderBasisSpatial (Ls := Ls) m)
        (h₂ := fun m => schwartzCutoffCLM Ng (cylinderBasisTemporal m))
        T hT hsupp_f₀ hsupp_g₀ Lt hLt hLt_tend)
  have hLt_ge_one : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Lt n :=
    (tendsto_atTop.1 hLt_tend) 1
  have hmain_ev :
      ∀ᶠ n : ℕ in atTop, dist (A n f₀ g₀) (P f₀ g₀) < ε / 2 := by
    exact (Metric.tendsto_nhds.mp hmain) (ε / 2) (by linarith)
  filter_upwards [hLt_ge_one, hmain_ev] with n hnLt hnmain
  have hdist1 : dist (A n f g) (A n f₀ g) = |A n (f - f₀) g| := by
    rw [Real.dist_eq, ← asymTorusContinuumGreen_embed_sub_left
      (Ls := Ls) (Lt := Lt n) (hLt := hLt n) mass hmass f f₀ g]
  have hdist2 : dist (A n f₀ g) (A n f₀ g₀) = |A n f₀ (g - g₀)| := by
    rw [Real.dist_eq, ← asymTorusContinuumGreen_embed_sub_right
      (Ls := Ls) (Lt := Lt n) (hLt := hLt n) mass hmass g g₀ f₀]
  have hdist4 : dist (P f₀ g₀) (P f₀ g) = |P f₀ (g₀ - g)| := by
    rw [Real.dist_eq, ← physicalCylinderGreen_sub_right
      (Ls := Ls) mass hmass g₀ g f₀]
  have hdist5 : dist (P f₀ g) (P f g) = |P (f₀ - f) g| := by
    rw [Real.dist_eq, ← physicalCylinderGreen_sub_left
      (Ls := Ls) mass hmass f₀ f g]
  have hbound1 : dist (A n f g) (A n f₀ g) ≤ C * δ * Qg := by
    rw [hdist1]
    have hA : |A n (f - f₀) g| ≤ C * qt (f - f₀) * qt g :=
      hqt_bound (Lt n) hnLt (f - f₀) g
    have hfdiff : qt (f - f₀) ≤ δ := by
      exact le_trans (hqt_le_qsum (f - f₀)) (le_of_lt hf_small)
    have hgq : qt g ≤ Qg := by
      calc
        qt g ≤ qsum g := hqt_le_qsum g
        _ = Qg := by simp [Qg]
    have hmul₁ : C * qt (f - f₀) ≤ C * δ := by
      exact mul_le_mul_of_nonneg_left hfdiff hC_pos.le
    have hmul₂ : C * qt (f - f₀) * qt g ≤ C * δ * qt g := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hmul₁ (apply_nonneg qt g)
    have hmul₃ : C * δ * qt g ≤ C * δ * Qg := by
      have hCδ_nonneg : 0 ≤ C * δ := by positivity
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hgq hCδ_nonneg
    exact le_trans hA (le_trans hmul₂ hmul₃)
  have hbound2 : dist (A n f₀ g) (A n f₀ g₀) ≤ C * (Qf + 1) * δ := by
    rw [hdist2]
    have hA : |A n f₀ (g - g₀)| ≤ C * qt f₀ * qt (g - g₀) :=
      hqt_bound (Lt n) hnLt f₀ (g - g₀)
    have hgdiff : qt (g - g₀) ≤ δ := by
      exact le_trans (hqt_le_qsum (g - g₀)) (le_of_lt hg_small)
    have hmul₁ : C * qt f₀ * qt (g - g₀) ≤ C * qt f₀ * δ := by
      have hCqt_nonneg : 0 ≤ C * qt f₀ := by positivity
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hgdiff hCqt_nonneg
    have hmul₂ : C * qt f₀ ≤ C * (Qf + 1) := by
      exact mul_le_mul_of_nonneg_left hqt_f₀ hC_pos.le
    have hmul₃ : C * qt f₀ * δ ≤ C * (Qf + 1) * δ := by
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hmul₂ hδ_nonneg
    exact le_trans hA (le_trans hmul₁ hmul₃)
  have hbound4 : dist (P f₀ g₀) (P f₀ g) ≤ (Qf + 1) * δ := by
    rw [hdist4]
    have hA : |P f₀ (g₀ - g)| ≤ qp f₀ * qp (g₀ - g) :=
      hqp_bound f₀ (g₀ - g)
    have hgdiff : qp (g₀ - g) ≤ δ := by
      exact le_trans (hqp_le_qsum (g₀ - g)) (le_of_lt hg_small_sym)
    have hmul₁ : qp f₀ * qp (g₀ - g) ≤ qp f₀ * δ := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hgdiff (apply_nonneg qp f₀)
    have hmul₂ : qp f₀ * δ ≤ (Qf + 1) * δ := by
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hqp_f₀ hδ_nonneg
    exact le_trans hA (le_trans hmul₁ hmul₂)
  have hbound5 : dist (P f₀ g) (P f g) ≤ δ * Qg := by
    rw [hdist5]
    have hA : |P (f₀ - f) g| ≤ qp (f₀ - f) * qp g :=
      hqp_bound (f₀ - f) g
    have hfdiff : qp (f₀ - f) ≤ δ := by
      exact le_trans (hqp_le_qsum (f₀ - f)) (le_of_lt hf_small_sym)
    have hgq : qp g ≤ Qg := by
      calc
        qp g ≤ qsum g := hqp_le_qsum g
        _ = Qg := by simp [Qg]
    have hmul₁ : qp (f₀ - f) * qp g ≤ δ * qp g := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hfdiff (apply_nonneg qp g)
    have hmul₂ : δ * qp g ≤ δ * Qg := by
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hgq hδ_nonneg
    exact le_trans hA (le_trans hmul₁ hmul₂)
  let d1 : ℝ := dist (A n f g) (A n f₀ g)
  let d2 : ℝ := dist (A n f₀ g) (A n f₀ g₀)
  let d3 : ℝ := dist (A n f₀ g₀) (P f₀ g₀)
  let d4 : ℝ := dist (P f₀ g₀) (P f₀ g)
  let d5 : ℝ := dist (P f₀ g) (P f g)
  let a1 : ℝ := C * δ * Qg
  let a2 : ℝ := C * (Qf + 1) * δ
  let a4 : ℝ := (Qf + 1) * δ
  let a5 : ℝ := δ * Qg
  have hd1 : d1 ≤ a1 := by simpa [d1, a1] using hbound1
  have hd2 : d2 ≤ a2 := by simpa [d2, a2] using hbound2
  have hd4 : d4 ≤ a4 := by simpa [d4, a4] using hbound4
  have hd5 : d5 ≤ a5 := by simpa [d5, a5] using hbound5
  have htri : dist (A n f g) (P f g) ≤ d1 + d2 + d3 + d4 + d5 := by
    calc
      dist (A n f g) (P f g)
        ≤ dist (A n f g) (A n f₀ g) + dist (A n f₀ g) (P f g) := dist_triangle _ _ _
      _ ≤ dist (A n f g) (A n f₀ g) +
            (dist (A n f₀ g) (A n f₀ g₀) + dist (A n f₀ g₀) (P f g)) := by
              gcongr
              exact dist_triangle _ _ _
      _ ≤ dist (A n f g) (A n f₀ g) +
            (dist (A n f₀ g) (A n f₀ g₀) +
              (dist (A n f₀ g₀) (P f₀ g₀) + dist (P f₀ g₀) (P f g))) := by
              gcongr
              exact dist_triangle _ _ _
      _ ≤ dist (A n f g) (A n f₀ g) +
            (dist (A n f₀ g) (A n f₀ g₀) +
              (dist (A n f₀ g₀) (P f₀ g₀) +
                (dist (P f₀ g₀) (P f₀ g) + dist (P f₀ g) (P f g)))) := by
              gcongr
              exact dist_triangle _ _ _
      _ = d1 + d2 + d3 + d4 + d5 := by
              simp [d1, d2, d3, d4, d5, add_assoc]
  have hcross :
      a1 + a2 + a4 + a5 ≤ ε / 4 := by
    set B : ℝ := (C + 1) * (Qf + Qg + 1)
    have hδ_le_eps' : δ ≤ ε / (4 * (C + 1) * (Qf + Qg + 1)) := by
      simpa [M] using hδ_le_eps
    have hB_pos : 0 < B := by
      dsimp [B]
      nlinarith [hC_pos, hQf_nonneg, hQg_nonneg]
    have hδ_le_B : δ ≤ ε / (4 * B) := by
      simpa [B, mul_assoc, mul_left_comm, mul_comm] using hδ_le_eps'
    have hmul : B * δ ≤ B * (ε / (4 * B)) := by
      exact mul_le_mul_of_nonneg_left hδ_le_B hB_pos.le
    have hcancel : B * (ε / (4 * B)) = ε / 4 := by
      field_simp [hB_pos.ne']
    calc
      a1 + a2 + a4 + a5 = B * δ := by
        dsimp [a1, a2, a4, a5, B]
        ring
      _ ≤ B * (ε / (4 * B)) := hmul
      _ = ε / 4 := hcancel
  have hsum_le : d1 + d2 + d3 + d4 + d5 ≤ a1 + a2 + a4 + a5 + d3 := by
    have h12 : d1 + d2 ≤ a1 + a2 := add_le_add hd1 hd2
    have h45 : d4 + d5 ≤ a4 + a5 := add_le_add hd4 hd5
    calc
      d1 + d2 + d3 + d4 + d5 = (d1 + d2) + d3 + (d4 + d5) := by ring
      _ ≤ (a1 + a2) + d3 + (a4 + a5) := by
          gcongr
      _ = a1 + a2 + a4 + a5 + d3 := by ring
  have hbig : dist (A n f g) (P f g) ≤ a1 + a2 + a4 + a5 + d3 := by
    exact le_trans htri hsum_le
  calc
    dist (A n f g) (P f g) ≤ a1 + a2 + a4 + a5 + d3 := hbig
    _ ≤ ε / 4 + d3 := by
      nlinarith [hcross]
    _ < ε := by
      linarith

/-! ## Covariance of the IR limit

The main payoff: combining the Green's function convergence with the
weak convergence of measures to identify the covariance of the IR limit. -/

/-- **The IR limit measure has the correct physically normalized cylinder covariance.**

If the sequence of pulled-back torus measures `ν_{Lt_n}` converges
weakly to a measure ν on cylinder configurations, and each torus
measure is Gaussian with the correct torus covariance, then ν has
covariance equal to `physicalCylinderGreen`.

**Proof strategy** (characteristic function method, same as
`torusLimit_covariance_eq`):
0. `cylinderPullbackGFF_secondMoment_eq_torus`: along the approximating sequence,
   cylinder second moments equal torus second moments on `cylinderToTorusEmbed f`.
1. Each torus measure is Gaussian: `E[e^{iω(g)}] = exp(-½ ⟨Tg,Tg⟩)` with
   `T = cylinderMassOperator`, and `⟨Tg,Tg⟩ = G_{Lt}(g,g)` for `g = embed f`
   (`second_moment_eq_covariance` + covariance = `greenFunctionBilinear`).
2. The Green's function converges: `G_{Lt}(embed f, embed f) → G_phys(f,f)`
   (`asymTorusGreen_tendsto_physicalCylinderGreen`).
3. Weak convergence: `∫ cos(ω(f)) dν_{Lt} → ∫ cos(ω(f)) dν`
4. Combining: `exp(-½ ∫(ωf)² dν) = exp(-½ G_phys(f,f))`
5. By injectivity of exp: `∫ (ωf)² dν = G_phys(f,f)` -/
theorem cylinderIRLimit_covariance_eq
    (mass : ℝ) (hmass : 0 < mass)
    (ν : Measure (Configuration (CylinderTestFunction Ls)))
    [IsProbabilityMeasure ν]
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop)
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)))
    (hμ_prob : ∀ n, IsProbabilityMeasure (μ n))
    (hμ_gauss : ∀ n (g : AsymTorusTestFunction (Lt n) Ls),
      ∫ ω : Configuration (AsymTorusTestFunction (Lt n) Ls), Real.exp (ω g) ∂(μ n) =
        Real.exp ((1 / 2) * ∫ ω, (ω g) ^ 2 ∂(μ n)))
    (hμ_cov : ∀ n (g : AsymTorusTestFunction (Lt n) Ls),
      ∫ ω : Configuration (AsymTorusTestFunction (Lt n) Ls), (ω g) ^ 2 ∂(μ n) =
        asymTorusContinuumGreen (Lt n) Ls mass hmass g g)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (f : CylinderTestFunction Ls),
      Tendsto (fun n =>
        ∫ ω, Complex.exp (Complex.I * ↑(ω f))
          ∂(cylinderPullbackMeasure (Lt (φ n)) Ls
            (μ (φ n))))
        atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν)))
    (f : CylinderTestFunction Ls) :
    ∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂ν =
      physicalCylinderGreen (Ls := Ls) mass hmass f f := by
  set eval_f : Configuration (CylinderTestFunction Ls) → ℝ := fun ω => ω f
  set G : ℝ := physicalCylinderGreen (Ls := Ls) mass hmass f f
  have h_eval_meas : Measurable eval_f := configuration_eval_measurable f
  let νseq : ℕ → Measure (Configuration (CylinderTestFunction Ls)) :=
    fun n => cylinderPullbackMeasure (Lt (φ n)) Ls (μ (φ n))
  have hνseq_prob : ∀ n, IsProbabilityMeasure (νseq n) := by
    intro n
    dsimp [νseq]
    have hmeas : Measurable (cylinderPullback (Lt (φ n)) Ls) :=
      configuration_measurable_of_eval_measurable _
        (fun g => configuration_eval_measurable _)
    exact Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have hνseq_gauss : ∀ n (g : CylinderTestFunction Ls),
      ∫ ω : Configuration (CylinderTestFunction Ls), Real.exp (ω g) ∂(νseq n) =
        Real.exp ((1 / 2) * ∫ ω, (ω g) ^ 2 ∂(νseq n)) := by
    intro n g
    dsimp [νseq]
    haveI := hμ_prob (φ n)
    exact cylinderPullback_isGaussian_of_torusGaussian Ls
      (Lt := Lt (φ n)) (μ := μ (φ n)) (hμ_gauss := hμ_gauss (φ n)) g
  have hνseq_cov : ∀ n,
      ∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂(νseq n) =
        asymTorusContinuumGreen (Lt (φ n)) Ls mass hmass
          (cylinderToTorusEmbed (Lt (φ n)) Ls f)
          (cylinderToTorusEmbed (Lt (φ n)) Ls f) := by
    intro n
    dsimp [νseq]
    exact cylinderPullback_secondMoment_eq_asymTorusGreen Ls
      (Lt := Lt (φ n)) (μ := μ (φ n)) mass hmass
      (hμ_cov := hμ_cov (φ n)) f
  have h_push_gauss : ∀ n,
      (νseq n).map eval_f =
        ProbabilityTheory.gaussianReal 0
          (∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂(νseq n)).toNNReal := by
    intro n
    haveI := hνseq_prob n
    exact GaussianField.eval_map_eq_gaussianReal (μ := νseq n) (hνseq_gauss n) f
  have hG_nonneg : 0 ≤ G := by
    simpa [G] using physicalCylinderGreen_nonneg (Ls := Ls) mass hmass f
  have h_cov_tend :
      Tendsto (fun n =>
        ∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂(νseq n))
      atTop (nhds G) := by
    have hsub : Tendsto (fun n =>
        asymTorusContinuumGreen (Lt (φ n)) Ls mass hmass
          (cylinderToTorusEmbed (Lt (φ n)) Ls f)
          (cylinderToTorusEmbed (Lt (φ n)) Ls f))
        atTop (nhds G) := by
      simpa [G] using
        (asymTorusGreen_tendsto_physicalCylinderGreen
          (Ls := Ls) mass hmass f f
          (fun n => Lt (φ n)) (fun n => hLt (φ n))
          (hLt_tend.comp hφ.tendsto_atTop))
    simpa [hνseq_cov] using hsub
  have h_push_char_eq : charFun (ν.map eval_f) =
      charFun (ProbabilityTheory.gaussianReal 0 G.toNNReal) := by
    ext t
    have hcf_seq : Tendsto (fun n => charFun ((νseq n).map eval_f) t)
        atTop (nhds (charFun (ν.map eval_f) t)) := by
      have h := hconv (t • f)
      have h_eq_n : ∀ n,
          charFun ((νseq n).map eval_f) t =
            ∫ ω, Complex.exp (Complex.I * ↑(ω (t • f))) ∂(νseq n) := by
        intro n
        haveI := hνseq_prob n
        haveI : IsProbabilityMeasure ((νseq n).map eval_f) :=
          Measure.isProbabilityMeasure_map h_eval_meas.aemeasurable
        rw [charFun_apply_real, integral_map h_eval_meas.aemeasurable]
        · congr 1
          funext ω
          simp [eval_f, map_smul]
          congr 1
          ring
        · change AEStronglyMeasurable
            (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I))
            (Measure.map eval_f (νseq n))
          exact ((by fun_prop :
            Continuous fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I)).aestronglyMeasurable)
      have h_eq_lim :
          charFun (ν.map eval_f) t =
            ∫ ω, Complex.exp (Complex.I * ↑(ω (t • f))) ∂ν := by
        haveI : IsProbabilityMeasure (ν.map eval_f) :=
          Measure.isProbabilityMeasure_map h_eval_meas.aemeasurable
        rw [charFun_apply_real, integral_map h_eval_meas.aemeasurable]
        · congr 1
          funext ω
          simp [eval_f, map_smul]
          congr 1
          ring
        · change AEStronglyMeasurable
            (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I))
            (Measure.map eval_f ν)
          exact ((by fun_prop :
            Continuous fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I)).aestronglyMeasurable)
      have h' : Tendsto (fun n =>
          charFun ((νseq n).map eval_f) t)
          atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω (t • f))) ∂ν)) := by
        simpa [h_eq_n] using h
      simpa [h_eq_lim] using h'
    have hcf_target : Tendsto (fun n => charFun ((νseq n).map eval_f) t) atTop
        (nhds (charFun (ProbabilityTheory.gaussianReal 0 G.toNNReal) t)) := by
      have h_eq_n : ∀ n,
          charFun ((νseq n).map eval_f) t =
            Complex.exp (-(∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂(νseq n))
              * t ^ 2 / 2) := by
        intro n
        rw [h_push_gauss n, charFun_gaussianReal]
        congr 1
        rw [Real.coe_toNNReal _
          (integral_nonneg (fun _ : Configuration (CylinderTestFunction Ls) => sq_nonneg _))]
        push_cast
        ring
      have h_eq_lim :
          charFun (ProbabilityTheory.gaussianReal 0 G.toNNReal) t =
            Complex.exp (-G * t ^ 2 / 2) := by
        rw [charFun_gaussianReal]
        congr 1
        push_cast
        rw [Real.coe_toNNReal _ hG_nonneg]
        ring
      have h_tend_exp : Tendsto (fun n =>
          Complex.exp (-(∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂(νseq n))
            * t ^ 2 / 2)) atTop
          (nhds (Complex.exp (-G * t ^ 2 / 2))) := by
        have hcont : Continuous (fun x : ℝ => Complex.exp (-x * t ^ 2 / 2)) := by
          fun_prop
        exact hcont.continuousAt.tendsto.comp h_cov_tend
      simpa [h_eq_n, h_eq_lim] using h_tend_exp
    exact tendsto_nhds_unique hcf_seq hcf_target
  have h_push_eq : ν.map eval_f = ProbabilityTheory.gaussianReal 0 G.toNNReal :=
    Measure.ext_of_charFun h_push_char_eq
  have h_second_push : ∫ x, x ^ 2 ∂(ν.map eval_f) = G := by
    rw [h_push_eq]
    have h_mean : ∫ x, x ∂(ProbabilityTheory.gaussianReal (0 : ℝ) G.toNNReal) = 0 :=
      integral_id_gaussianReal
    have h_var := variance_of_integral_eq_zero
      (measurable_id.aemeasurable
        (μ := ProbabilityTheory.gaussianReal (0 : ℝ) G.toNNReal)) h_mean
    simp only [id] at h_var
    rw [← h_var]
    have h_var_id :
        Var[id; ProbabilityTheory.gaussianReal (0 : ℝ) G.toNNReal] = (G.toNNReal : ℝ) := by
      exact variance_fun_id_gaussianReal (μ := 0) (v := G.toNNReal)
    rw [h_var_id]
    exact Real.coe_toNNReal _ hG_nonneg
  have h_second_map :
      ∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂ν =
        ∫ x, x ^ 2 ∂(ν.map eval_f) := by
    exact (integral_map h_eval_meas.aemeasurable
      (continuous_pow 2).aestronglyMeasurable).symm
  rw [h_second_map, h_second_push]

end Pphi2

end
