/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gaussian Convolution Strict Positive Definiteness via Fourier Theory

## Overview

Proves `⟨f, G⋆f⟩ > 0` for nonzero `f ∈ L²(ℝⁿ)` by:
1. Proving `Ĝ(k) > 0` for all k (Gaussian FT is positive)
2. Axiomatizing the Fourier representation `⟨f, G⋆f⟩ = ∫ Ĝ(k) ‖f̂(k)‖² dk`
3. Deriving strict positivity from (1) + (2) + Plancherel injectivity

## References

- Folland, *Real Analysis*, §8.3; Reed-Simon I, §IX.4
-/

import Pphi2.TransferMatrix.L2Operator
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

noncomputable section

open MeasureTheory Complex FourierTransform

namespace Pphi2

variable (Ns : ℕ) [NeZero Ns]

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

The axiom states that for an L¹ kernel g whose Fourier transform
(viewed as ℂ-valued) has strictly positive real part everywhere,
the convolution quadratic form ⟨f, g⋆f⟩ is strictly positive for f ≠ 0.

This follows from the Fourier representation:
  ⟨f, g⋆f⟩ = ∫ Re(ĝ_ℂ(k)) · ‖f̂_ℂ(k)‖² dk

The proof uses: ℝ→ℂ embedding, convolution theorem on Schwartz,
Parseval identity, density of Schwartz in L², and Plancherel injectivity.
All ingredients are in Mathlib; the axiom packages the density argument. -/

/-- **Convolution PD from Fourier positivity** (Folland §8.3, Reed-Simon I §IX.4).

For `g ∈ L¹` with `Re(ĝ_ℂ(k)) > 0` for all k, and `f ∈ L²` with `f ≠ 0`:
  `⟨f, g⋆f⟩ > 0`.

**Proof**: The Fourier representation gives
`⟨f, g⋆f⟩ = ∫ Re(ĝ(k)) ‖f̂(k)‖² dk`. Since Re(ĝ) > 0 pointwise
and f ≠ 0 implies f̂ ≠ 0 a.e. (Plancherel), the integral is positive.

The Fourier representation itself follows from:
1. Embed f into L²(ℂ) via ofReal
2. Convolution theorem on Schwartz: `𝓕(g⋆s) = ĝ · ŝ`
3. Parseval: `⟨s, g⋆s⟩ = ∫ ĝ(k)|ŝ(k)|² dk`
4. Density extension: both sides continuous on L², agree on dense 𝓢

**Mathlib deps**: `fourier_mul_convolution_eq`, `integral_inner_fourier_fourier`,
`denseRange_toLpCLM`, `Lp.inner_fourier_eq`. -/
axiom inner_convCLM_pos_of_fourier_pos
    (g : SpatialField Ns → ℝ) (hg : MemLp g 1 volume)
    -- ĝ_ℂ has positive real part everywhere, where ĝ is computed on
    -- EuclideanSpace ℝ (Fin Ns) (which has the inner product structure
    -- needed for the Fourier transform)
    (hĝ_pos : ∀ w : EuclideanSpace ℝ (Fin Ns),
      0 < (𝓕 (fun (v : EuclideanSpace ℝ (Fin Ns)) =>
        (g ((WithLp.equiv 2 _) v) : ℂ)) w).re)
    (f : L2SpatialField Ns) (hf : f ≠ 0) :
    0 < @inner ℝ _ _ f (convCLM g hg f)

/-! ## Gaussian convolution is strictly PD -/

/-- **Gaussian convolution is strictly positive definite on L²(ℝⁿ, ℝ)**.

**Proof**: The transfer Gaussian `G(ψ) = exp(-½ Σᵢ ψᵢ²)` has
`G(v) = exp(-½‖v‖²)` on EuclideanSpace, so its Fourier transform
`Ĝ(k) = (2π)^{n/2} exp(-2π²‖k‖²) > 0` by `fourier_gaussian_pos`.
Apply `inner_convCLM_pos_of_fourier_pos`. -/
theorem gaussian_conv_strictlyPD :
    ∀ (f : L2SpatialField Ns), f ≠ 0 →
      0 < @inner ℝ _ _ f (convCLM (transferGaussian Ns) (transferGaussian_memLp Ns) f) := by
  intro f hf
  apply inner_convCLM_pos_of_fourier_pos Ns
      (transferGaussian Ns) (transferGaussian_memLp Ns) _ f hf
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

end Pphi2

end
