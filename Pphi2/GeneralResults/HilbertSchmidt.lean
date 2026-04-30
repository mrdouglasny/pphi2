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

/-! ### Scaffolding for the operator-theoretic Hilbert-Schmidt criterion

The textbook axiom `isCompactOperator_of_basis_norm_summable` is the
operator-theoretic step "summable squared basis norms ⟹ compact" (Reed-Simon
I, Theorem VI.22(a)). The classical proof uses finite-rank truncations and
the Bessel residual bound: the finite-rank truncation `T_S` is built from
rank-1 operators `x ↦ ⟨bᵢ, x⟩ • T(bᵢ)`, each compact (as it factors through
`ℝ`), and `‖T - T_S‖²_{op} ≤ Σ_{i ∉ S} ‖T(bᵢ)‖² → 0` along
`Filter.atTop`.

The two helpers `rank1Op_isCompactOperator` and `truncatedOp_isCompactOperator`
below discharge the "build T_S; T_S is compact" half of that proof. The
remaining op-norm-convergence half is the genuine analytic content that needs
ℓ²-Cauchy-Schwarz on `tsum`s; it is left for a future iteration and is the
**only** reason the surrounding result still appears as an `axiom`. -/

section HSCriterion

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {ι : Type*} (b : HilbertBasis ι ℝ H) (T : H →L[ℝ] H)

/-- The rank-1 operator `x ↦ ⟨bᵢ, x⟩ • T(bᵢ)`. -/
private noncomputable def rank1Op (i : ι) : H →L[ℝ] H :=
  ContinuousLinearMap.smulRight (innerSL ℝ (b i)) (T (b i))

@[simp] private theorem rank1Op_apply (i : ι) (x : H) :
    rank1Op b T i x = (inner ℝ (b i) x) • T (b i) := by
  simp [rank1Op]

/-- Each rank-1 operator factors through `ℝ` — locally compact — hence is compact. -/
private theorem rank1Op_isCompactOperator (i : ι) :
    IsCompactOperator (rank1Op b T i) := by
  -- Factor: rank1Op b T i = (smulRight 1 (T (b i))) ∘L (innerSL ℝ (b i))
  -- Source ℝ of the outer map is locally compact, so the outer map is compact;
  -- pre-composing with a CLM keeps compactness.
  have h_outer :
      IsCompactOperator
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (T (b i))) :=
    isCompactOperator_of_locallyCompactSpace_rng _
  have hcomp :
      rank1Op b T i =
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (T (b i))).comp
          (innerSL ℝ (b i)) := by
    ext x
    simp [rank1Op]
  rw [hcomp]
  exact h_outer.comp_clm _

/-- The truncated operator `T_S x := Σ_{i ∈ S} ⟨bᵢ, x⟩ • T(bᵢ)`. -/
private noncomputable def truncatedOp (S : Finset ι) : H →L[ℝ] H :=
  ∑ i ∈ S, rank1Op b T i

/-- The truncated operator is compact (finite sum of rank-1 operators). -/
private theorem truncatedOp_isCompactOperator (S : Finset ι) :
    IsCompactOperator (truncatedOp b T S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa [truncatedOp] using
      (isCompactOperator_zero (M₁ := H) (M₂ := H))
  | insert a s ha ih =>
    show IsCompactOperator (truncatedOp b T (insert a s))
    rw [truncatedOp, Finset.sum_insert ha]
    exact (rank1Op_isCompactOperator b T a).add (by simpa [truncatedOp] using ih)

variable (hT_summable : Summable (fun i : ι => ‖T (b i)‖ ^ 2))

/-- The full Hilbert-basis expansion of `T x` in rank-1 pieces. -/
private theorem hasSum_rank1Op_apply (x : H) :
    HasSum (fun i : ι => rank1Op b T i x) (T x) := by
  simpa [rank1Op_apply, HilbertBasis.repr_apply_apply] using
    (b.hasSum_repr x).mapL T

/-- The truncation residual is the `tsum` over the complement. -/
private theorem sub_truncatedOp_apply_eq_tsum (S : Finset ι) (x : H) :
    (T - truncatedOp b T S) x =
      ∑' i : {i // i ∉ S}, (inner ℝ (b i.1) x) • T (b i.1) := by
  have hsummable : Summable (fun i : ι => rank1Op b T i x) :=
    (hasSum_rank1Op_apply b T x).summable
  have hsum := hsummable.sum_add_tsum_subtype_compl S
  have htsum : ∑' i : ι, rank1Op b T i x = T x :=
    (hasSum_rank1Op_apply b T x).tsum_eq
  change T x - truncatedOp b T S x = _
  rw [sub_eq_iff_eq_add']
  rw [← htsum]
  simpa [truncatedOp, rank1Op_apply, add_comm, add_left_comm, add_assoc] using hsum.symm

/-- Pointwise Bessel-tail bound for the truncation residual. -/
private theorem norm_sub_truncatedOp_apply_le
    (hT_summable : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) (S : Finset ι) (x : H) :
    ‖(T - truncatedOp b T S) x‖ ≤
      Real.sqrt (∑' i : {i // i ∉ S}, ‖T (b i.1)‖ ^ 2) * ‖x‖ := by
  let f : {i // i ∉ S} → ℝ := fun i => ‖inner ℝ (b i.1) x‖
  let g : {i // i ∉ S} → ℝ := fun i => ‖T (b i.1)‖
  have hf_summable : Summable (fun i : {i // i ∉ S} => f i ^ 2) := by
    exact ((b.orthonormal.inner_products_summable x).subtype _)
  have hg_summable : Summable (fun i : {i // i ∉ S} => g i ^ 2) := by
    simpa [g] using Summable.subtype hT_summable {i : ι | i ∉ S}
  have hf_summable_rpow : Summable (fun i : {i // i ∉ S} => f i ^ (2 : ℝ)) := by
    simpa [Real.rpow_natCast] using hf_summable
  have hg_summable_rpow : Summable (fun i : {i // i ∉ S} => g i ^ (2 : ℝ)) := by
    simpa [Real.rpow_natCast] using hg_summable
  have hholder :=
    Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg HolderConjugate.two_two
      (fun i => norm_nonneg _)
      (fun i => norm_nonneg _)
      hf_summable_rpow
      hg_summable_rpow
  have hfg :
      ∑' i : {i // i ∉ S}, f i * g i ≤
        Real.sqrt (∑' i : {i // i ∉ S}, f i ^ 2) *
          Real.sqrt (∑' i : {i // i ∉ S}, g i ^ 2) := by
    calc
      ∑' i : {i // i ∉ S}, f i * g i
        ≤ (∑' i : {i // i ∉ S}, f i ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∑' i : {i // i ∉ S}, g i ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hholder.2
      _ = Real.sqrt (∑' i : {i // i ∉ S}, f i ^ 2) *
            Real.sqrt (∑' i : {i // i ∉ S}, g i ^ 2) := by
              simp [Real.sqrt_eq_rpow, one_div]
  have hBessel :
      ∑' i : {i // i ∉ S}, f i ^ 2 ≤ ‖x‖ ^ 2 := by
    have hsplit := (b.orthonormal.inner_products_summable x).tsum_subtype_add_tsum_subtype_compl
      {i : ι | i ∈ S}
    calc
      ∑' i : {i // i ∉ S}, f i ^ 2
        ≤ ∑' i : {i // i ∈ S}, ‖inner ℝ (b i.1) x‖ ^ 2
            + ∑' i : {i // i ∉ S}, ‖inner ℝ (b i.1) x‖ ^ 2 := by
              exact le_add_of_nonneg_left (tsum_nonneg fun i => by positivity)
      _ = ∑' i : ι, ‖inner ℝ (b i) x‖ ^ 2 := by
            simpa [f] using hsplit
      _ ≤ ‖x‖ ^ 2 := b.orthonormal.tsum_inner_products_le x
  have hsqrt :
      Real.sqrt (∑' i : {i // i ∉ S}, f i ^ 2) ≤ ‖x‖ := by
    calc
      Real.sqrt (∑' i : {i // i ∉ S}, f i ^ 2)
        ≤ Real.sqrt (‖x‖ ^ 2) := Real.sqrt_le_sqrt hBessel
      _ = ‖x‖ := by
        rw [Real.sqrt_sq_eq_abs]
        exact abs_of_nonneg (norm_nonneg _)
  have hprod_summable : Summable (fun i : {i // i ∉ S} => f i * g i) := hholder.1
  have hnorm_summable :
      Summable (fun i : {i // i ∉ S} => ‖(inner ℝ (b i.1) x) • T (b i.1)‖) := by
    simpa [f, g, norm_smul] using hprod_summable
  have hnorm :
      ‖∑' i : {i // i ∉ S}, (inner ℝ (b i.1) x) • T (b i.1)‖
        ≤ ∑' i : {i // i ∉ S}, f i * g i := by
    simpa [f, g, norm_smul] using (norm_tsum_le_tsum_norm hnorm_summable)
  calc
    ‖(T - truncatedOp b T S) x‖
      = ‖∑' i : {i // i ∉ S}, (inner ℝ (b i.1) x) • T (b i.1)‖ := by
          rw [sub_truncatedOp_apply_eq_tsum b T S x]
    _ ≤ ∑' i : {i // i ∉ S}, f i * g i := hnorm
    _ ≤ Real.sqrt (∑' i : {i // i ∉ S}, f i ^ 2) *
          Real.sqrt (∑' i : {i // i ∉ S}, g i ^ 2) := hfg
    _ ≤ Real.sqrt (∑' i : {i // i ∉ S}, ‖T (b i.1)‖ ^ 2) * ‖x‖ := by
          simpa [g, mul_comm] using
            (mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg (∑' i : {i // i ∉ S}, g i ^ 2)))

/-- Operator-norm control by the `ℓ²` tail. -/
private theorem opNorm_sub_truncatedOp_le
    (hT_summable : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) (S : Finset ι) :
    ‖T - truncatedOp b T S‖ ≤
      Real.sqrt (∑' i : {i // i ∉ S}, ‖T (b i.1)‖ ^ 2) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) ?_
  intro x
  exact norm_sub_truncatedOp_apply_le b T hT_summable S x

/-- The finite-rank truncations converge to `T` in operator norm. -/
private theorem tendsto_truncatedOp
    (hT_summable : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) :
    Filter.Tendsto (fun S : Finset ι => truncatedOp b T S) Filter.atTop (nhds T) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have htail :
      Filter.Tendsto
        (fun S : Finset ι => ∑' i : {i // i ∉ S}, ‖T (b i.1)‖ ^ 2)
        Filter.atTop (nhds 0) := by
    simpa using tendsto_tsum_compl_atTop_zero (fun i : ι => ‖T (b i)‖ ^ 2)
  have hsqrt :
      Filter.Tendsto
        (fun S : Finset ι => Real.sqrt (∑' i : {i // i ∉ S}, ‖T (b i.1)‖ ^ 2))
        Filter.atTop (nhds 0) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp htail
  refine squeeze_zero (fun S => norm_nonneg _) ?_ hsqrt
  intro S
  simpa [norm_sub_rev] using opNorm_sub_truncatedOp_le b T hT_summable S

end HSCriterion

/-- **Hilbert-Schmidt criterion for compactness.**

A bounded operator `T` on a real Hilbert space is compact whenever there exists
a Hilbert basis `b` such that `Σᵢ ‖T (bᵢ)‖²` is summable.

**Reference**: Reed-Simon I (1980), Theorem VI.22(a) (Hilbert-Schmidt operators
are compact).

**Proof sketch**: Define finite-rank truncations `T_S x := Σ_{i ∈ S} ⟨bᵢ, x⟩ •
(T bᵢ)` for `S : Finset ι` (see `truncatedOp` above). The range of `T_S` lies
in the finite-dimensional subspace `span{T bᵢ : i ∈ S}`, hence has compact
closure on bounded sets, so `T_S` is compact (proved as
`truncatedOp_isCompactOperator`). The Bessel residual gives
`‖T - T_S‖²_{op} ≤ Σ_{i ∉ S} ‖T bᵢ‖²`, which tends to `0` along
`(Filter.atTop : Filter (Finset ι))` by summability. By
`isCompactOperator_of_tendsto`, `T` is compact.

**Status**: the truncation/compactness half is proved (see `truncatedOp` and
`truncatedOp_isCompactOperator`); the operator-norm convergence half (the
Bessel residual bound combined with a tail-of-summable argument) remains as
the sole open analytic step. -/
theorem isCompactOperator_of_basis_norm_summable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {ι : Type*} (b : HilbertBasis ι ℝ H)
    (T : H →L[ℝ] H)
    (hT_summable : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) :
    IsCompactOperator T := by
  refine isCompactOperator_of_tendsto
    (F := fun S : Finset ι => truncatedOp b T S)
    (f := T)
    (tendsto_truncatedOp b T hT_summable) ?_
  filter_upwards [Filter.Eventually.of_forall (fun S : Finset ι =>
    truncatedOp_isCompactOperator b T S)] with S hS
  exact hS

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
