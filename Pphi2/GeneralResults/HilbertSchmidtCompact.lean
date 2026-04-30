/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hilbert-Schmidt Compactness for L² Convolution-Kernel Operators

General functional-analysis result, with no QFT content. Belongs upstream in
`SpectralThm` or Mathlib once the broader Hilbert-Schmidt API lands; co-located
in `Pphi2.GeneralResults` for now as a placeholder.

## Main result

`integral_operator_l2_kernel_compact`:

If `G` is a locally compact, second-countable, T₂ normed real vector space with
Haar measure `μ`, `K : G × G → ℝ` is a kernel with `K ∈ L²(μ ⊗ μ)`, and
`T : L²(μ) → L²(μ)` is a continuous linear map such that
  `(T f)(x) = ∫ K(x, t) · f(x − t) dμ(t)`
holds a.e. in `x`, then `T` is a compact operator.

## Proof outline

1. Pointwise Cauchy-Schwarz + Tonelli give the Hilbert-Schmidt operator-norm
   bound `‖T‖_op ≤ ‖K‖_{L²(μ⊗μ)}` for any kernel `K ∈ L²`.
2. Step kernels `Σᵢⱼ cᵢⱼ · 𝟙_{Aᵢ × Bⱼ}` (with `μ(Aᵢ), μ(Bⱼ) < ∞`) are dense in
   `L²(μ⊗μ)` (Mathlib `Lp.simpleFunc.dense_range_coe` since `μ ⊗ μ` is σ-finite).
3. For a step kernel, the integral operator has range in the finite-dimensional
   subspace `span{𝟙_{Aᵢ}}`, so it is finite-rank, hence compact.
4. Approximation in `L²(μ⊗μ)` ⟹ operator-norm approximation; limit of compacts
   in operator norm is compact (`isCompactOperator_of_tendsto`).
5. The convolution form is reduced to the standard form `∫ K(x, y) f(y) dμ(y)`
   via the Haar-measure-preserving substitution `y = x − t` (so `K_std(x, y) :=
   K_conv(x, x − y)` has the same `L²(μ⊗μ)` norm).

**Reference**: Reed-Simon I, Theorem VI.23; Simon §III.2.
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Normed.Operator.Compact

namespace Pphi2.GeneralResults

open MeasureTheory Real Filter

noncomputable section

/-- The standard-form kernel associated to a convolution-form kernel:
`Kstd x y = K x (x - y)`. -/
private def standardKernelOfConvolution {G : Type*} [Sub G] (K : G → G → ℝ) : G → G → ℝ :=
  fun x y => K x (x - y)

/-- The change of variables `(x, y) ↦ (x, x - y)` preserves `μ.prod μ`. -/
private theorem measurePreserving_standardKernelOfConvolution
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure] :
    MeasurePreserving (fun z : G × G => (z.1, z.1 - z.2)) (μ.prod μ) (μ.prod μ) := by
  let ψ : G × G → G × G := fun z => (z.1, z.2 - z.1)
  have hψ : MeasurePreserving ψ (μ.prod μ) (μ.prod μ) := by
    simpa [ψ, sub_eq_add_neg] using (measurePreserving_prod_sub (μ := μ) (ν := μ))
  have hneg : MeasurePreserving (fun z : G × G => (z.1, -z.2)) (μ.prod μ) (μ.prod μ) := by
    exact MeasurePreserving.prod (MeasurePreserving.id (μ := μ))
      (Measure.measurePreserving_neg (μ := μ))
  convert hneg.comp hψ using 1
  ext z
  · rfl
  · change z.1 - z.2 = -((z.2 - z.1))
    abel

/-- The standard-form kernel has the same `L²` membership as the convolution-form kernel. -/
private theorem standardKernelOfConvolution_memLp
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (K : G → G → ℝ)
    (hK : MemLp (Function.uncurry K) 2 (μ.prod μ)) :
    MemLp (Function.uncurry (standardKernelOfConvolution K)) 2 (μ.prod μ) := by
  change MemLp (fun z : G × G => K z.1 (z.1 - z.2)) 2 (μ.prod μ)
  simpa [Function.comp, Function.uncurry] using
    hK.comp_measurePreserving (measurePreserving_standardKernelOfConvolution (μ := μ))

/-- For fixed `x`, the substitution `y = x - t` rewrites the convolution-form integral as the
standard-form integral. -/
private theorem convolution_integral_eq_standard_integral
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (K : G → G → ℝ) (f : G → ℝ) (x : G) :
    (∫ t, K x t * f (x - t) ∂μ) = ∫ y, standardKernelOfConvolution K x y * f y ∂μ := by
  let g : G → ℝ := fun y => standardKernelOfConvolution K x y * f y
  have hmp : MeasurePreserving (fun y : G => x - y) μ μ :=
    Measure.measurePreserving_sub_left (μ := μ) x
  simpa [g, standardKernelOfConvolution, sub_sub_cancel] using
    MeasurePreserving.integral_comp hmp (measurableEmbedding_subLeft x) g

/-- The convolution-form a.e. representation of `T` rewrites to the standard form with
`standardKernelOfConvolution K`. -/
private theorem convolution_ae_eq_standard
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (K : G → G → ℝ)
    (T : (Lp ℝ 2 μ) →L[ℝ] (Lp ℝ 2 μ))
    (hT : ∀ f : Lp ℝ 2 μ,
      (T f : G → ℝ) =ᵐ[μ] fun x => ∫ t, K x t * (f : G → ℝ) (x - t) ∂μ) :
    ∀ f : Lp ℝ 2 μ,
      (T f : G → ℝ) =ᵐ[μ] fun x =>
        ∫ y, standardKernelOfConvolution K x y * (f : G → ℝ) y ∂μ := by
  intro f
  refine (hT f).trans ?_
  exact Filter.Eventually.of_forall (fun x =>
    convolution_integral_eq_standard_integral (μ := μ) K (f : G → ℝ) x)

/-- Hilbert-Schmidt compactness in standard kernel form.

Missing piece: this is where the ONB-of-the-base-space argument should live. Concretely, one needs
to construct finite-rank truncations from a Hilbert basis of `L²(μ)`, prove operator-norm
convergence using the Hilbert-Schmidt bound, and then apply
`isCompactOperator_of_tendsto`. Mathlib has the compact-operator closure theorem and abstract
Hilbert-basis API, but this file still lacks the product-space/Fubini + Parseval bridge needed to
formalize the slice coefficients `aᵢ(x) = ⟪K(x, ·), eᵢ⟫`. -/
private theorem integral_operator_l2_kernel_compact_standard
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (K : G → G → ℝ)
    (hK : MemLp (Function.uncurry K) 2 (μ.prod μ))
    (T : (Lp ℝ 2 μ) →L[ℝ] (Lp ℝ 2 μ))
    (hT : ∀ f : Lp ℝ 2 μ,
      (T f : G → ℝ) =ᵐ[μ] fun x => ∫ y, K x y * (f : G → ℝ) y ∂μ) :
    IsCompactOperator T := by
  sorry

/-- **Hilbert-Schmidt compactness theorem (convolution-kernel form).**

If `K ∈ L²(μ ⊗ μ)` is a real-valued kernel on a locally compact, second-countable,
T₂ normed space `G` with Haar measure `μ`, and `T : L²(μ) → L²(μ)` is a
continuous linear map representing the convolution-style integral operator
`(T f)(x) = ∫ K(x, t) f(x − t) dμ(t)` a.e., then `T` is compact.

This is the convolution form. The standard form `(T f)(x) = ∫ K(x, y) f(y) dμ(y)`
is recovered by the substitution `y = x − t`, which preserves the Haar product
measure.

**Reference**: Reed-Simon I, Theorem VI.23.

**Status (2026-04-29)**: stated; proof in progress. Belongs upstream in
`SpectralThm` or Mathlib once Hilbert-Schmidt API lands. -/
theorem integral_operator_l2_kernel_compact
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    {μ : Measure G} [μ.IsAddHaarMeasure]
    (K : G → G → ℝ)
    (hK : MemLp (Function.uncurry K) 2 (μ.prod μ))
    (T : (Lp ℝ 2 μ) →L[ℝ] (Lp ℝ 2 μ))
    (hT : ∀ f : Lp ℝ 2 μ,
      (T f : G → ℝ) =ᵐ[μ] fun x => ∫ t, K x t * (f : G → ℝ) (x - t) ∂μ) :
    IsCompactOperator T := by
  exact integral_operator_l2_kernel_compact_standard
    (standardKernelOfConvolution K)
    (standardKernelOfConvolution_memLp (μ := μ) K hK)
    T
    (convolution_ae_eq_standard (μ := μ) K T hT)

end

end Pphi2.GeneralResults
