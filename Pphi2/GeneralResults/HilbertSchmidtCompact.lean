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

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Normed.Operator.Compact

namespace Pphi2.GeneralResults

open MeasureTheory Real

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
  sorry

end Pphi2.GeneralResults
