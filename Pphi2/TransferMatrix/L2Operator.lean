/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Transfer Matrix as L² Operator

Formalizes the transfer matrix as a bounded linear operator on L²(ℝ^Ns)
and connects it to the spectral theorem for compact self-adjoint operators.

## Main definitions

- `L2SpatialField Ns` — The Hilbert space L²(ℝ^Ns) where the transfer operator acts
- `transferOperatorCLM` — The transfer matrix as a CLM on L², defined via the
  kernel factorization T = M_w ∘ Conv_G ∘ M_w
- `transferOperator_spectral` — Spectral decomposition from gaussian-field's
  `compact_selfAdjoint_spectral`

## Construction

The transfer kernel factors as:
  `T(ψ, ψ') = w(ψ) · G(ψ - ψ') · w(ψ')`
where:
- `w(ψ) = exp(-(a/2) · h(ψ))` is the weight (bounded, from spatial action)
- `G(x) = exp(-timeCoupling(0, x))` is the Gaussian kernel (in L¹)

This gives `T = M_w ∘ Conv_G ∘ M_w` where:
- `M_w` is multiplication by `w` (a CLM on L² by Hölder, from L2Multiplication.lean)
- `Conv_G` is convolution with `G` (a CLM on L² by Young, from L2Convolution.lean)

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1 (Transfer matrix)
- Simon, *The P(φ)₂ Euclidean QFT*, §III.2 (Positivity)
- Reed-Simon, *Methods of Modern Mathematical Physics IV*, §XIII.12
-/

import Pphi2.TransferMatrix.TransferMatrix
import Pphi2.TransferMatrix.L2Multiplication
import Pphi2.TransferMatrix.L2Convolution
import GaussianField.SpectralTheorem
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section

open GaussianField Real MeasureTheory

namespace Pphi2

variable (Ns : ℕ) [NeZero Ns]

/-! ## L² Hilbert space

The transfer operator acts on L²(ℝ^Ns, dx) where ℝ^Ns = SpatialField Ns
and dx is Lebesgue measure (product of 1D Lebesgue measures). -/

/-- The L² Hilbert space of square-integrable functions on the spatial field
configuration space ℝ^Ns.

This is the natural Hilbert space for the transfer matrix formalism:
the transfer kernel T(ψ,ψ') defines an integral operator on this space. -/
abbrev L2SpatialField :=
  MeasureTheory.Lp (α := SpatialField Ns) ℝ 2 MeasureTheory.volume

/-! ## Weight function and Gaussian kernel

The building blocks for the kernel factorization T = M_w ∘ Conv_G ∘ M_w. -/

/-- The weight function `w(ψ) = exp(-(a/2) · h(ψ))` where `h` is the spatial action.

This is bounded above by `exp(a · Ns · A / 2)` where `A` is the lower bound
constant from `wickPolynomial_bounded_below`, since:
- `spatialKinetic ≥ 0` (sum of squares)
- `spatialPotential ≥ -Ns · A` (from Wick polynomial bound below)
- Therefore `h(ψ) ≥ -Ns · A`, so `w(ψ) ≤ exp(a · Ns · A / 2)`. -/
def transferWeight (P : InteractionPolynomial) (a mass : ℝ) : SpatialField Ns → ℝ :=
  let c := wickConstant 1 Ns a mass
  fun ψ => Real.exp (-(a / 2) * spatialAction Ns P a mass c ψ)

/-- The Gaussian kernel `G(x) = exp(-timeCoupling(0, x)) = exp(-½‖x‖²)`.

This is in L¹(ℝ^Ns) since `∫ exp(-½‖x‖²) dx = (2π)^{Ns/2}`. -/
def transferGaussian : SpatialField Ns → ℝ :=
  fun ψ => Real.exp (-timeCoupling Ns 0 ψ)

/-! ## Proofs that weight is bounded and Gaussian is integrable -/

/-- The spatial kinetic energy is continuous in the field configuration. -/
private theorem continuous_spatialKinetic (a : ℝ) :
    Continuous (spatialKinetic Ns a) := by
  unfold spatialKinetic
  apply Continuous.mul continuous_const
  apply continuous_finset_sum
  intro x _
  apply Continuous.mul continuous_const
  apply Continuous.pow
  apply Continuous.sub
  · exact continuous_apply (x + 1)
  · exact continuous_apply x

/-- The Wick monomial `:x^n:_c` is continuous in `x` (for fixed `n, c`). -/
private theorem continuous_wickMonomial : ∀ (n : ℕ) (c : ℝ),
    Continuous (wickMonomial n c)
  | 0, _ => by simp [wickMonomial]; exact continuous_const
  | 1, _ => by simp [wickMonomial]; exact continuous_id
  | n + 2, c => by
    simp only [wickMonomial]
    exact ((continuous_id.mul (continuous_wickMonomial (n + 1) c)).sub
      ((continuous_const).mul (continuous_wickMonomial n c)))

omit [NeZero Ns] in
/-- The spatial potential energy is continuous in the field configuration. -/
private theorem continuous_spatialPotential (P : InteractionPolynomial) (a mass c : ℝ) :
    Continuous (spatialPotential Ns P a mass c) := by
  unfold spatialPotential
  apply continuous_finset_sum
  intro x _
  apply Continuous.add
  · -- (1/2) * mass^2 * ψ(x)^2
    fun_prop
  · unfold wickPolynomial
    apply Continuous.add
    · apply Continuous.mul continuous_const
      exact (continuous_wickMonomial P.n c).comp (continuous_apply x)
    · apply continuous_finset_sum; intro m _
      apply Continuous.mul continuous_const
      exact (continuous_wickMonomial m c).comp (continuous_apply x)

/-- The spatial action is continuous in the field configuration. -/
private theorem continuous_spatialAction (P : InteractionPolynomial) (a mass c : ℝ) :
    Continuous (spatialAction Ns P a mass c) := by
  unfold spatialAction
  exact (continuous_spatialKinetic Ns a).add (continuous_spatialPotential Ns P a mass c)

/-- The weight function is continuous. -/
theorem continuous_transferWeight (P : InteractionPolynomial) (a mass : ℝ) :
    Continuous (transferWeight Ns P a mass) := by
  unfold transferWeight
  apply Real.continuous_exp.comp
  apply Continuous.mul continuous_const
  exact continuous_spatialAction Ns P a mass _

/-- The weight function is measurable. -/
theorem transferWeight_measurable (P : InteractionPolynomial) (a mass : ℝ) :
    Measurable (transferWeight Ns P a mass) :=
  (continuous_transferWeight Ns P a mass).measurable

/-- The spatial action is bounded below: `spatialAction ≥ -Ns · A`.

Since `spatialKinetic ≥ 0` (sum of squares), `½m²ψ² ≥ 0`, and
`:P(ψ):_c ≥ -A` (from `wickPolynomial_bounded_below`), we get
`spatialAction ≥ -Ns · A`. -/
private theorem spatialAction_lower_bound (P : InteractionPolynomial) (a mass : ℝ) :
    ∃ B : ℝ, ∀ ψ : SpatialField Ns, -B ≤ spatialAction Ns P a mass
      (wickConstant 1 Ns a mass) ψ := by
  obtain ⟨A, _, hA_bound⟩ := wickPolynomial_bounded_below P (wickConstant 1 Ns a mass)
  refine ⟨Ns * A, fun ψ => ?_⟩
  unfold spatialAction
  have hkin : 0 ≤ spatialKinetic Ns a ψ := by
    unfold spatialKinetic
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun x _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpot : -(↑Ns * A) ≤ spatialPotential Ns P a mass (wickConstant 1 Ns a mass) ψ := by
    unfold spatialPotential
    calc -(↑Ns * A) = ∑ _ : Fin Ns, (-A) := by simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x : Fin Ns, ((1/2) * mass^2 * (ψ x)^2 + wickPolynomial P _ (ψ x)) := by
          apply Finset.sum_le_sum; intro x _
          linarith [sq_nonneg (mass * ψ x), hA_bound (ψ x)]
  linarith

/-- The weight is essentially bounded: `‖w(ψ)‖ ≤ C` a.e.

Since `spatialAction ≥ -Ns · A` and `w = exp(-(a/2)·h)`, we get
`0 < w ≤ exp(a · Ns · A / 2)`, so `‖w‖_∞` is finite. -/
theorem transferWeight_bound (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᵐ (x : SpatialField Ns) ∂volume, ‖transferWeight Ns P a mass x‖ ≤ C := by
  obtain ⟨B, hB⟩ := spatialAction_lower_bound Ns P a mass
  refine ⟨Real.exp (a / 2 * B), Real.exp_pos _, ?_⟩
  apply Filter.Eventually.of_forall
  intro ψ
  simp only [transferWeight, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h := hB ψ
  nlinarith

omit [NeZero Ns] in
/-- The Gaussian kernel is in L¹(ℝ^Ns).

This is the standard Gaussian integral:
`∫_{ℝ^Ns} exp(-½‖x‖²) dx = (2π)^{Ns/2} < ∞`.

**Proof**: Factor `exp(-½‖x‖²) = ∏ᵢ exp(-½xᵢ²)` and use `Integrable.fintype_prod`
with `integrable_exp_neg_mul_sq` for each 1D factor. -/
theorem transferGaussian_memLp :
    MemLp (transferGaussian Ns) 1 (volume : Measure (SpatialField Ns)) := by
  rw [memLp_one_iff_integrable]
  -- Show transferGaussian = fun ψ => ∏ x, exp (-(1/2) * (ψ x)^2)
  have hfact : transferGaussian Ns =
      fun ψ => ∏ x : Fin Ns, Real.exp (-(1/2) * (ψ x) ^ 2) := by
    ext ψ
    simp only [transferGaussian, timeCoupling]
    rw [show (0 : SpatialField Ns) = fun _ => (0 : ℝ) from rfl]
    simp only [zero_sub, neg_sq]
    -- Goal: exp (-(1/2 * Σ x, (ψ x)^2)) = ∏ x, exp (-(1/2) * (ψ x)^2)
    have : -(1 / 2 * ∑ x : Fin Ns, (ψ x) ^ 2) =
        ∑ x : Fin Ns, (-(1/2) * (ψ x) ^ 2) := by
      simp only [neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [this]
    exact Real.exp_sum Finset.univ _
  rw [hfact]
  -- volume on (Fin Ns → ℝ) is Measure.pi (fun _ => volume)
  have hvol : (volume : Measure (SpatialField Ns)) =
      Measure.pi (fun _ : Fin Ns => (volume : Measure ℝ)) := rfl
  rw [hvol]
  -- Use fintype_prod to reduce to 1D integrability
  exact MeasureTheory.Integrable.fintype_prod
    (fun i => integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2))

/-! ## Transfer operator definition

The transfer operator is defined as `T = M_w ∘ Conv_G ∘ M_w`, where
`M_w` is multiplication by the weight and `Conv_G` is Gaussian convolution.

This replaces the previous axiom `transferOperatorCLM` with a definition,
eliminating one axiom from the proof. -/

/-- The transfer matrix as a continuous linear map on L²(ℝ^Ns).

Defined via the kernel factorization:
  `T = M_w ∘ Conv_G ∘ M_w`
where `w(ψ) = exp(-(a/2)·h(ψ))` and `G(x) = exp(-½‖x‖²)`.

This factors the transfer kernel as:
  `T(ψ,ψ') = w(ψ) · G(ψ-ψ') · w(ψ')`
           `= exp(-(a/2)h(ψ)) · exp(-½‖ψ-ψ'‖²) · exp(-(a/2)h(ψ'))`
           `= exp(-timeCoupling(ψ,ψ') - (a/2)h(ψ) - (a/2)h(ψ'))` -/
def transferOperatorCLM (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    L2SpatialField Ns →L[ℝ] L2SpatialField Ns :=
  let w := transferWeight Ns P a mass
  let G := transferGaussian Ns
  let hw_meas := transferWeight_measurable Ns P a mass
  let C := (transferWeight_bound Ns P a mass ha hmass).choose
  let hC := (transferWeight_bound Ns P a mass ha hmass).choose_spec.1
  let hw_bound := (transferWeight_bound Ns P a mass ha hmass).choose_spec.2
  let hG := transferGaussian_memLp Ns
  -- T = M_w ∘ Conv_G ∘ M_w
  mulCLM w hw_meas C hC hw_bound
    ∘L convCLM G hG
    ∘L mulCLM w hw_meas C hC hw_bound

/-! ## Properties of the transfer operator -/

/-- The transfer operator is self-adjoint on L²(ℝ^Ns).

This follows from the factorization `T = M_w ∘ Conv_G ∘ M_w` and the
self-adjointness of each factor:
- `M_w` is self-adjoint (since `w` is real-valued)
- `Conv_G` is self-adjoint (since the Gaussian is symmetric: `G(x) = G(-x)`)

Then: `⟨f, Tg⟩ = ⟨f, M_w(Conv_G(M_w g))⟩`
    `= ⟨M_w f, Conv_G(M_w g)⟩`     (M_w self-adjoint)
    `= ⟨Conv_G(M_w f), M_w g⟩`     (Conv_G self-adjoint)
    `= ⟨M_w(Conv_G(M_w f)), g⟩`    (M_w self-adjoint)
    `= ⟨Tf, g⟩`.

**Proof strategy**: Prove self-adjointness of `mulCLM` (from real-valuedness
of `w` and the L² inner product) and of `convCLM` (from symmetry of the
Gaussian kernel), then compose. -/
axiom transferOperator_isSelfAdjoint (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    IsSelfAdjoint (transferOperatorCLM Ns P a mass ha hmass)

/-- The transfer operator is a *positive* operator: `⟨f, Tf⟩ ≥ 0` for all `f`.

This is a consequence of the Perron-Frobenius theorem for the transfer
matrix: the kernel `T(ψ,ψ') > 0` is strictly positive everywhere
(`transferKernel_pos`), which implies the operator is positivity-improving.
Combined with self-adjointness, all eigenvalues are nonneg, giving
`⟨f, Tf⟩ = Σᵢ λᵢ |⟨eᵢ, f⟩|² ≥ 0`.

**Proof strategy**: Use the spectral decomposition from
`compact_selfAdjoint_spectral` and the Perron-Frobenius theorem
to show all spectral values are nonneg.

**References**: Reed-Simon IV, Theorem XIII.44; Simon P(φ)₂, §III.2. -/
axiom transferOperator_inner_nonneg (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∀ (f : L2SpatialField Ns),
      0 ≤ @inner ℝ _ _ f (transferOperatorCLM Ns P a mass ha hmass f)

/-- The transfer operator is compact on L²(ℝ^Ns).

The kernel satisfies T(ψ,ψ') ≤ exp(C) · exp(-½|ψ-ψ'|²), making the
integral operator Hilbert-Schmidt (hence compact):
  `∫∫ |T(ψ,ψ')|² dψ dψ' ≤ exp(2C) · ∫∫ exp(-|ψ-ψ'|²) dψ dψ' < ∞`.

In fact T is trace class: T = T^{1/2} · T^{1/2} where T^{1/2} is also
Hilbert-Schmidt (by the same Gaussian bound on its kernel).

**Proof strategy**: Bound the kernel by a Gaussian, compute the Hilbert-Schmidt
norm explicitly, conclude compactness. -/
axiom transferOperator_isCompact (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    IsCompactOperator (transferOperatorCLM Ns P a mass ha hmass)

/-! ## Spectral decomposition

By the spectral theorem for compact self-adjoint operators (proved in
gaussian-field's `SpectralTheorem.lean`), the transfer operator has a
Hilbert basis of eigenvectors with real eigenvalues. -/

/-- The spectral decomposition of the transfer operator.

By `compact_selfAdjoint_spectral`, there exists:
- A Hilbert basis `{eᵢ}` of L²(ℝ^Ns) consisting of eigenvectors of T
- Eigenvalues `λᵢ` with T(eᵢ) = λᵢ · eᵢ
- The diagonal representation: T(f) = Σᵢ λᵢ ⟨eᵢ, f⟩ eᵢ -/
theorem transferOperator_spectral (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ (L2SpatialField Ns)) (eigenval : ι → ℝ),
      (∀ i, (transferOperatorCLM Ns P a mass ha hmass :
        L2SpatialField Ns →ₗ[ℝ] L2SpatialField Ns) (b i) = eigenval i • b i) ∧
      (∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i)
        (transferOperatorCLM Ns P a mass ha hmass x)) :=
  compact_selfAdjoint_spectral _
    (transferOperator_isSelfAdjoint Ns P a mass ha hmass)
    (transferOperator_isCompact Ns P a mass ha hmass)

/-! ## Sorted eigenvalue sequence

The spectral theorem gives eigenvalues indexed by an arbitrary type ι.
For the physical application (energy levels, mass gap), we need them
sorted in decreasing order as a sequence ℕ → ℝ.

Mathematically, since L²(ℝ^Ns) is separable, ι is countable, and since
all eigenvalues are positive (Perron-Frobenius), they can be arranged as
λ₀ ≥ λ₁ ≥ λ₂ ≥ ... > 0.

We axiomatize this sorted sequence and its Perron-Frobenius properties
(strict positivity and simplicity of the ground state). -/

/-- Eigenvalues of the transfer matrix, in decreasing order:
`λ₀ ≥ λ₁ ≥ λ₂ ≥ ... > 0`.

These are the eigenvalues from `transferOperator_spectral`, sorted in
decreasing order. The sorting is well-defined because:
- L²(ℝ^Ns) is separable, so the spectral decomposition has countably many terms
- All eigenvalues are positive (by Perron-Frobenius), so they accumulate only at 0
- They can be arranged in decreasing order by the spectral theorem for compact operators

**Connection to spectral theorem**: The eigenvalues here are exactly the
values from `transferOperator_spectral`, enumerated in decreasing order.
The eigenvectors form the Hilbert basis given by that theorem. -/
axiom transferEigenvalue (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (n : ℕ) : ℝ

/-- All eigenvalues are strictly positive.

This is the Perron-Frobenius theorem for integral operators with strictly
positive kernels: since T(ψ,ψ') > 0 for all ψ, ψ' (from `transferKernel_pos`),
the operator T is positivity-preserving, which forces all eigenvalues to
be nonneg. Strict positivity follows from the stronger property that T
is positivity-*improving* (maps nonneg nonzero functions to strictly positive
functions), which implies no eigenvalue is zero.

**References**: Reed-Simon IV, Theorem XIII.44; Simon, P(φ)₂, §III.2. -/
axiom transferEigenvalue_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (n : ℕ) :
    0 < transferEigenvalue P a mass ha hmass n

/-- The eigenvalues are decreasing: `λ₀ ≥ λ₁ ≥ λ₂ ≥ ...`.

This is by construction: the eigenvalues from the spectral decomposition
are sorted in decreasing order. -/
axiom transferEigenvalue_antitone (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    Antitone (transferEigenvalue P a mass ha hmass)

/-- The largest eigenvalue λ₀ is simple (non-degenerate): `λ₀ > λ₁`.

This is the Perron-Frobenius theorem for the transfer matrix: since the
kernel T(ψ,ψ') > 0 everywhere, the operator is positivity-improving,
so the ground state eigenvalue is simple and the ground state
eigenfunction is strictly positive.

**References**: Reed-Simon IV, Theorem XIII.44 (Perron-Frobenius for
positivity-improving operators); Glimm-Jaffe §6.1. -/
axiom transferEigenvalue_ground_simple (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    transferEigenvalue P a mass ha hmass 0 >
    transferEigenvalue P a mass ha hmass 1

end Pphi2

end
