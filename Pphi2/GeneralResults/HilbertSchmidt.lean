/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hilbert-Schmidt Compactness for L² Integral Operators

General functional-analysis result, with no QFT content. Belongs upstream in
`SpectralThm` or Mathlib once a full Hilbert-Schmidt theory lands.

## Main result

`integral_operator_l2_kernel_compact`:

If `G` is a locally compact, second-countable, T₂ normed real vector space with
Haar measure `μ`, `K : G × G → ℝ` is a kernel with `K ∈ L²(μ ⊗ μ)`, and
`T : L²(μ) → L²(μ)` is a continuous linear map such that
  `(T f)(x) = ∫ K(x, t) · f(x − t) dμ(t)`
holds a.e. in `x`, then `T` is a compact operator.

## Proof strategy

The proof composes:

1. **Convolution → standard form** (proved): the substitution
   `Φ : (x, y) ↦ (x, x − y)` is a measure-preserving automorphism of `μ ⊗ μ`
   on a Haar group, so the convolution-form kernel `K(x, t)` rewrites to a
   standard-form kernel `K_std(x, y) := K(x, x − y)` with the same `L²(μ⊗μ)`
   norm and the same induced operator.

2. **Hilbert-Schmidt summability** (textbook axiom `hs_basis_norm_summable`):
   for any Hilbert basis `b` of `L²(μ)`, `Σᵢ ‖T (b i)‖²_{L²(μ)} < ∞`. The textbook
   proof is one Parseval-on-the-slice step plus Tonelli.

3. **Operator-theoretic HS ⟹ compact** (textbook axiom
   `isCompactOperator_of_basis_norm_summable`): a bounded operator with
   summable squared basis norms is compact, via finite-rank truncation and the
   Bessel residual.

Both textbook axioms are well-cited (Reed-Simon I, Theorem VI.22) and each is
independently provable; they are split out here so the *composition* compiles
cleanly while the unproved analytic infrastructure remains explicit and
auditable.

## References

- Reed, M. and Simon, B., *Methods of Modern Mathematical Physics, Vol. I:
  Functional Analysis* (Academic Press, 1980), §VI.6 — Hilbert-Schmidt
  operators, Theorem VI.22.
- Simon, B., *Trace Ideals and their Applications* (AMS, 2nd ed., 2005), §III.2.
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

/-! ## Textbook axioms

Two analytic facts are taken as textbook axioms here. Each is one well-known
theorem from Reed-Simon I §VI.6, both independently provable in Mathlib once
the supporting Hilbert-Schmidt API is built. They are listed here to make the
proof of the main theorem compile cleanly while the analytic gap remains
explicitly tracked. -/

/-- **Hilbert-Schmidt summability of basis norms.**

For any standard-form integral operator `T` with kernel `K ∈ L²(μ ⊗ μ)` and any
Hilbert basis `{bᵢ}` of `L²(μ)`, the sequence `i ↦ ‖T (bᵢ)‖²` is summable.

In fact equality holds (`Σᵢ ‖T bᵢ‖² = ‖K‖²_{L²(μ⊗μ)}`); we state only the
summability since that is all the compactness argument needs.

**Reference**: Reed-Simon I (1980), Theorem VI.22.

**Proof sketch**: For each `i`, the function `T bᵢ : L²(μ)` admits the
representative `x ↦ ∫ K(x, y) · (bᵢ)(y) dμ(y) = ⟨K(x, ·), bᵢ⟩_{L²(μ)}`, where
`K(x, ·) ∈ L²(μ)` for a.e. `x` by Fubini. Parseval applied to the slice
`K(x, ·)` gives `Σᵢ |⟨K(x, ·), bᵢ⟩|² = ‖K(x, ·)‖²_{L²(μ)}`, and integrating in
`x` via Tonelli yields `Σᵢ ‖T bᵢ‖² = ∫ ‖K(x, ·)‖² dμ(x) = ‖K‖²_{L²(μ⊗μ)}`. -/
axiom hs_basis_norm_summable
    {G : Type*} [MeasurableSpace G] {μ : Measure G} [SigmaFinite μ]
    (K : G → G → ℝ)
    (_hK : MemLp (Function.uncurry K) 2 (μ.prod μ))
    (T : (Lp ℝ 2 μ) →L[ℝ] (Lp ℝ 2 μ))
    (_hT : ∀ f : Lp ℝ 2 μ,
      (T f : G → ℝ) =ᵐ[μ] fun x => ∫ y, K x y * (f : G → ℝ) y ∂μ)
    {ι : Type*} (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)) :
    Summable (fun i : ι => ‖T (b i)‖ ^ 2)

/-- **Hilbert-Schmidt criterion for compactness.**

A bounded operator `T` on a real Hilbert space is compact whenever there exists
a Hilbert basis `b` such that `Σᵢ ‖T (bᵢ)‖²` is summable.

**Reference**: Reed-Simon I (1980), Theorem VI.22(a) (Hilbert-Schmidt operators
are compact).

**Proof sketch**: Define finite-rank truncations `T_S x := Σ_{i ∈ S} ⟨bᵢ, x⟩ •
(T bᵢ)` for `S : Finset ι`. The range of `T_S` lies in the finite-dimensional
subspace `span{T bᵢ : i ∈ S}`, hence has compact closure on bounded sets, so
`T_S` is compact. The Bessel residual gives
`‖T - T_S‖²_{op} ≤ Σ_{i ∉ S} ‖T bᵢ‖²`, which tends to `0` along
`(Filter.atTop : Filter (Finset ι))` by summability. By
`isCompactOperator_of_tendsto`, `T` is compact. -/
axiom isCompactOperator_of_basis_norm_summable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {ι : Type*} (b : HilbertBasis ι ℝ H)
    (T : H →L[ℝ] H)
    (_hT_summable : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) :
    IsCompactOperator T

/-! ## Convolution-to-standard-form bridge (proved)

The substitution `(x, y) ↦ (x, x − y)` is a measure-preserving automorphism of
`μ ⊗ μ` for any Haar measure `μ`. This lets us rewrite a convolution-form
kernel `K(x, t)` as a standard-form kernel `K_std(x, y) := K(x, x − y)` without
changing the induced operator or the kernel's `L²(μ⊗μ)` norm. -/

/-- The standard-form kernel associated to a convolution-form kernel:
`Kstd x y = K x (x - y)`. -/
private def standardKernelOfConvolution {G : Type*} [Sub G]
    (K : G → G → ℝ) : G → G → ℝ :=
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

-- `L²(μ)` admits a Hilbert basis indexed by a `Set (Lp ℝ 2 μ)`. This is just
-- `_root_.exists_hilbertBasis` specialised; we inline its use below to avoid
-- universe-polymorphism juggling around an explicit existential wrapper.

/-! ## Main theorem -/

/-- **Hilbert-Schmidt compactness in standard kernel form.**

The standard-form integral operator with kernel `K ∈ L²(μ ⊗ μ)` is compact.

This composes the two textbook axioms `hs_basis_norm_summable` (kernel ⟹
summable basis norms) and `isCompactOperator_of_basis_norm_summable`
(summable basis norms ⟹ compact operator). -/
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
  obtain ⟨w, b, _⟩ := _root_.exists_hilbertBasis (𝕜 := ℝ) (E := Lp ℝ 2 μ)
  exact isCompactOperator_of_basis_norm_summable b T
    (hs_basis_norm_summable K hK T hT b)

/-- **Hilbert-Schmidt compactness theorem (convolution-kernel form).**

If `K ∈ L²(μ ⊗ μ)` is a real-valued kernel on a locally compact, second-countable,
T₂ normed space `G` with Haar measure `μ`, and `T : L²(μ) → L²(μ)` is a
continuous linear map representing the convolution-style integral operator
`(T f)(x) = ∫ K(x, t) f(x − t) dμ(t)` a.e., then `T` is compact.

The convolution form is reduced to the standard form via the Haar-invariant
substitution `(x, y) ↦ (x, x − y)`, then `integral_operator_l2_kernel_compact_standard`
finishes via the two textbook axioms above.

**Reference**: Reed-Simon I, Theorem VI.23. -/
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
