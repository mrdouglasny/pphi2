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
import Pphi2.GeneralResults.HilbertSchmidt
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

omit [NeZero Ns] in
/-- The transfer Gaussian is even: `G(-ψ) = G(ψ)`. -/
theorem transferGaussian_neg (ψ : SpatialField Ns) :
    transferGaussian Ns (-ψ) = transferGaussian Ns ψ := by
  unfold transferGaussian timeCoupling
  congr 1
  -- The quadratic form is invariant under ψ ↦ -ψ.
  simp [sq]

omit [NeZero Ns] in
/-- Symmetry of the transfer Gaussian difference kernel. -/
theorem transferGaussian_sub_comm (x y : SpatialField Ns) :
    transferGaussian Ns (x - y) = transferGaussian Ns (y - x) := by
  have hneg : x - y = -(y - x) := by
    ext i
    simp
  rw [hneg, transferGaussian_neg]

omit [NeZero Ns] in
/-- The transfer Gaussian is continuous: `exp(-½‖ψ‖²)` is smooth. -/
theorem continuous_transferGaussian :
    Continuous (transferGaussian Ns) := by
  unfold transferGaussian timeCoupling
  apply Real.continuous_exp.comp
  apply Continuous.neg
  apply Continuous.mul continuous_const
  apply continuous_finset_sum
  intro x _
  apply Continuous.pow
  apply Continuous.sub
  · exact continuous_const
  · exact continuous_apply x

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
  | 0, _ => by simpa [wickMonomial] using continuous_const
  | 1, _ => by simpa [wickMonomial] using continuous_id
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

/-- Quadratic coercive lower bound on the spatial action.

Keeping the positive mass term gives:
`spatialAction(ψ) ≥ (1/2) * mass^2 * ∑ x, ψ(x)^2 - Ns * A`.
This is the bound needed to get Gaussian decay of the transfer weight. -/
private theorem spatialAction_lower_bound_quadratic (P : InteractionPolynomial) (a mass : ℝ)
    (_ha : 0 < a) (_hmass : 0 < mass) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ ψ : SpatialField Ns,
        (1 / 2) * mass ^ 2 * (∑ x : Fin Ns, (ψ x) ^ 2) - (↑Ns * A) ≤
          spatialAction Ns P a mass (wickConstant 1 Ns a mass) ψ := by
  obtain ⟨A0, hA0_nonneg, hA0_bound⟩ :=
    wickPolynomial_bounded_below P (wickConstant 1 Ns a mass)
  refine ⟨A0, le_of_lt hA0_nonneg, fun ψ => ?_⟩
  unfold spatialAction
  have hkin : 0 ≤ spatialKinetic Ns a ψ := by
    unfold spatialKinetic
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun x _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpot : (1 / 2) * mass ^ 2 * (∑ x : Fin Ns, (ψ x) ^ 2) - (↑Ns * A0) ≤
      spatialPotential Ns P a mass (wickConstant 1 Ns a mass) ψ := by
    unfold spatialPotential
    calc
      (1 / 2) * mass ^ 2 * (∑ x : Fin Ns, (ψ x) ^ 2) - (↑Ns * A0)
          = ∑ x : Fin Ns, ((1 / 2) * mass ^ 2 * (ψ x) ^ 2 - A0) := by
              simp [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x : Fin Ns, ((1 / 2) * mass ^ 2 * (ψ x) ^ 2 +
            wickPolynomial P (wickConstant 1 Ns a mass) (ψ x)) := by
            apply Finset.sum_le_sum
            intro x _
            linarith [hA0_bound (ψ x)]
  linarith

/-- Gaussian decay upper bound for the transfer weight.

This is the key coercive estimate used in compactness heuristics:
`w(ψ) ≤ exp((a/2) * Ns * A) * exp(-(a*mass^2/4) * ∑ x, ψ(x)^2)`. -/
theorem transferWeight_gaussian_decay (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ψ : SpatialField Ns,
      transferWeight Ns P a mass ψ ≤
        Real.exp ((a / 2) * (↑Ns * A)) *
          Real.exp (-(a * mass ^ 2 / 4) * (∑ x : Fin Ns, (ψ x) ^ 2)) := by
  obtain ⟨A, hA_nonneg, hcoer⟩ := spatialAction_lower_bound_quadratic Ns P a mass ha hmass
  refine ⟨A, hA_nonneg, fun ψ => ?_⟩
  unfold transferWeight
  have hcoerψ := hcoer ψ
  have hlin :
      -(a / 2) * spatialAction Ns P a mass (wickConstant 1 Ns a mass) ψ ≤
        (a / 2) * (↑Ns * A) - (a * mass ^ 2 / 4) * (∑ x : Fin Ns, (ψ x) ^ 2) := by
    nlinarith [hcoerψ, ha, sq_nonneg mass]
  have hexp := Real.exp_le_exp.mpr hlin
  -- Split the RHS as exp(u - v) = exp(u) * exp(-v)
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, Real.exp_add, mul_comm, mul_left_comm,
    mul_assoc] using hexp

/-- The weight is essentially bounded: `‖w(ψ)‖ ≤ C` a.e.

Since `spatialAction ≥ -Ns · A` and `w = exp(-(a/2)·h)`, we get
`0 < w ≤ exp(a · Ns · A / 2)`, so `‖w‖_∞` is finite. -/
theorem transferWeight_bound (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (_hmass : 0 < mass) :
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

/-- The transfer weight is strictly positive everywhere (exponential is always positive). -/
theorem transferWeight_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ψ : SpatialField Ns) : 0 < transferWeight Ns P a mass ψ :=
  Real.exp_pos _

omit [NeZero Ns] in
/-- The Gaussian kernel is strictly positive everywhere. -/
theorem transferGaussian_pos (ψ : SpatialField Ns) :
    0 < transferGaussian Ns ψ :=
  Real.exp_pos _

/-- The Gaussian kernel is bounded by 1: `G(ψ) = exp(-½‖ψ‖²) ≤ 1`.

Since `timeCoupling Ns 0 ψ ≥ 0` (sum of squares), the exponent is `≤ 0`. -/
theorem transferGaussian_norm_le_one (ψ : SpatialField Ns) :
    ‖transferGaussian Ns ψ‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (transferGaussian_pos Ns ψ)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (timeCoupling_nonneg Ns 0 ψ))

omit [NeZero Ns] in
/-- The transfer Gaussian is in L²(ℝ^Ns).

Since G(ψ) = exp(-½‖ψ‖²), we have G² = exp(-‖ψ‖²) = ∏ᵢ exp(-ψᵢ²),
a product of 1D Gaussians, each integrable by `integrable_exp_neg_mul_sq`. -/
theorem transferGaussian_memLp_two :
    MemLp (transferGaussian Ns) 2 (volume : Measure (SpatialField Ns)) := by
  rw [memLp_two_iff_integrable_sq (transferGaussian_memLp Ns).1]
  -- G(ψ)² = ∏ᵢ exp(-(ψ i)²), a product of 1D Gaussians
  have hfact : (fun ψ : SpatialField Ns => transferGaussian Ns ψ ^ 2) =
      fun ψ => ∏ x : Fin Ns, Real.exp (-1 * (ψ x) ^ 2) := by
    ext ψ
    simp only [transferGaussian, timeCoupling]
    rw [show (0 : SpatialField Ns) = fun _ => (0 : ℝ) from rfl]
    simp only [zero_sub, neg_sq]
    rw [← Real.exp_nat_mul, ← Real.exp_sum Finset.univ]
    congr 1
    push_cast
    have : (2 : ℝ) * -(1 / 2 * ∑ x : Fin Ns, ψ x ^ 2) = -(∑ x, ψ x ^ 2) := by ring
    rw [this, ← Finset.sum_neg_distrib]
    congr 1; ext; ring
  rw [hfact, show (volume : Measure (SpatialField Ns)) =
      Measure.pi (fun _ : Fin Ns => (volume : Measure ℝ)) from rfl]
  exact MeasureTheory.Integrable.fintype_prod
    (fun _ => integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1))

/-- The transfer weight is in L²(ℝ^Ns).

From `transferWeight_gaussian_decay`, `w(ψ) ≤ C · exp(-α ∑ ψ(x)²)` where
`α = a·mass²/4 > 0`. Therefore `w(ψ)² ≤ C² · ∏ₓ exp(-2α · ψ(x)²)`, a product
of 1D Gaussians, each integrable by `integrable_exp_neg_mul_sq`. -/
theorem transferWeight_memLp_two (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    MemLp (transferWeight Ns P a mass) 2 (volume : Measure (SpatialField Ns)) := by
  rw [memLp_two_iff_integrable_sq
    (transferWeight_measurable Ns P a mass).aestronglyMeasurable]
  -- Get the Gaussian decay bound
  obtain ⟨A, hA_nonneg, hbound⟩ := transferWeight_gaussian_decay Ns P a mass ha hmass
  set K := Real.exp ((a / 2) * (↑Ns * A))
  set β := a * mass ^ 2 / 4
  have hβ : 0 < β := by positivity
  -- The dominating function: K² * ∏ exp(-2β * (ψ x)²)
  set domFn : SpatialField Ns → ℝ :=
    fun ψ => K ^ 2 * ∏ x : Fin Ns, Real.exp (-(2 * β) * (ψ x) ^ 2)
  -- Bound: w(ψ)² ≤ domFn(ψ)
  have h_sq_bound : ∀ ψ : SpatialField Ns,
      transferWeight Ns P a mass ψ ^ 2 ≤ domFn ψ := by
    intro ψ
    have hw := hbound ψ
    have hw_pos : 0 ≤ transferWeight Ns P a mass ψ := le_of_lt (transferWeight_pos Ns P a mass ψ)
    have hK_pos : 0 ≤ K := le_of_lt (Real.exp_pos _)
    have hD_pos : 0 ≤ Real.exp (-β * (∑ x : Fin Ns, (ψ x) ^ 2)) := le_of_lt (Real.exp_pos _)
    calc transferWeight Ns P a mass ψ ^ 2
        ≤ (K * Real.exp (-β * (∑ x : Fin Ns, (ψ x) ^ 2))) ^ 2 :=
          sq_le_sq' (by linarith) hw
      _ = K ^ 2 * (Real.exp (-β * (∑ x : Fin Ns, (ψ x) ^ 2))) ^ 2 := by ring
      _ = K ^ 2 * Real.exp (-(2 * β) * (∑ x : Fin Ns, (ψ x) ^ 2)) := by
          congr 1; rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ = K ^ 2 * Real.exp (∑ x : Fin Ns, (-(2 * β) * (ψ x) ^ 2)) := by
          congr 2; rw [Finset.mul_sum]
      _ = domFn ψ := by
          congr 1; rw [Real.exp_sum]
  -- The dominating function is integrable
  have h_dom : Integrable domFn volume := by
    apply Integrable.const_mul
    rw [show (volume : Measure (SpatialField Ns)) =
        Measure.pi (fun _ : Fin Ns => (volume : Measure ℝ)) from rfl]
    exact MeasureTheory.Integrable.fintype_prod
      (fun _ => integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 2 * β))
  -- Conclude by domination
  exact h_dom.mono
    ((transferWeight_measurable Ns P a mass).pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun ψ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
          Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact h_sq_bound ψ))

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
theorem transferOperator_isSelfAdjoint (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    IsSelfAdjoint (transferOperatorCLM Ns P a mass ha hmass) := by
  unfold transferOperatorCLM
  let w := transferWeight Ns P a mass
  let G := transferGaussian Ns
  let hw_meas := transferWeight_measurable Ns P a mass
  let C := (transferWeight_bound Ns P a mass ha hmass).choose
  let hC := (transferWeight_bound Ns P a mass ha hmass).choose_spec.1
  let hw_bound := (transferWeight_bound Ns P a mass ha hmass).choose_spec.2
  let hG := transferGaussian_memLp Ns
  let A : L2SpatialField Ns →L[ℝ] L2SpatialField Ns := mulCLM w hw_meas C hC hw_bound
  let B : L2SpatialField Ns →L[ℝ] L2SpatialField Ns := convCLM G hG
  have hA : IsSelfAdjoint A := mulCLM_isSelfAdjoint w hw_meas C hC hw_bound
  have hB : IsSelfAdjoint B := by
    refine convCLM_isSelfAdjoint_of_even G hG ?_
    intro x
    simpa [G] using transferGaussian_neg Ns x
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change @inner ℝ _ _ ((A.comp (B.comp A)) f) g = @inner ℝ _ _ f ((A.comp (B.comp A)) g)
  simp only [ContinuousLinearMap.comp_apply]
  have hA' : ∀ x y : L2SpatialField Ns, @inner ℝ _ _ (A x) y = @inner ℝ _ _ x (A y) := by
    intro x y
    exact hA.isSymmetric x y
  have hB' : ∀ x y : L2SpatialField Ns, @inner ℝ _ _ (B x) y = @inner ℝ _ _ x (B y) := by
    intro x y
    exact hB.isSymmetric x y
  calc
    @inner ℝ _ _ (A (B (A f))) g = @inner ℝ _ _ (B (A f)) (A g) := hA' _ _
    _ = @inner ℝ _ _ (A f) (B (A g)) := hB' _ _
    _ = @inner ℝ _ _ f (A (B (A g))) := hA' _ _

-- The axiom `integral_operator_l2_kernel_compact` (Hilbert-Schmidt compactness in
-- convolution-kernel form) has been promoted to a theorem in
-- `Pphi2.GeneralResults.HilbertSchmidtCompact`. The reference there is the
-- canonical statement; we re-export it here for compatibility with downstream
-- callers that previously imported from this module.
export Pphi2.GeneralResults (integral_operator_l2_kernel_compact)

/-- The tensor product kernel `K(x,t) = w(x) · g(t)` is in `L²(μ ⊗ μ)` when
`w ∈ L²` and `g ∈ L²`.

By Fubini: `‖K‖₂² = ∫∫ w(x)² g(t)² dx dt = ‖w‖₂² · ‖g‖₂²`.
Since `|g| ≤ 1` and `g ∈ L¹`, we have `g ∈ L²` with `‖g‖₂² ≤ ‖g‖₁`. -/
private theorem tensor_kernel_memLp
    {n : ℕ} [NeZero n]
    (w : (Fin n → ℝ) → ℝ) (hw_l2 : MemLp w 2 (volume : Measure (Fin n → ℝ)))
    (g : (Fin n → ℝ) → ℝ) (hg_l1 : MemLp g 1 (volume : Measure (Fin n → ℝ)))
    (hg_le_one : ∀ x, ‖g x‖ ≤ 1) :
    MemLp (Function.uncurry (fun x t => w x * g t))
      2 ((volume : Measure (Fin n → ℝ)).prod volume) := by
  refine ⟨?_, ?_⟩
  · -- AEStronglyMeasurable on product via pullback + multiplication
    exact (hw_l2.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst).mul
      (hg_l1.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_snd)
  · -- eLpNorm < ⊤: bound ‖w(x)g(t)‖ₑ² ≤ ‖w(x)‖ₑ² · ‖g(t)‖ₑ, then Tonelli
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    -- ∫⁻ ‖g‖ₑ < ⊤ from g ∈ L¹
    have hg_lint : ∫⁻ t, ‖g t‖ₑ ∂volume < ⊤ := by
      rw [← eLpNorm_one_eq_lintegral_enorm]; exact hg_l1.eLpNorm_lt_top
    -- ∫⁻ ‖w‖ₑ² < ⊤ from w ∈ L²
    have hw_lint : ∫⁻ x, ‖w x‖ₑ ^ (2:ℝ) ∂volume < ⊤ :=
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num) (by norm_num)
        hw_l2.eLpNorm_lt_top
    -- ‖g(t)‖ₑ ≤ 1 for all t
    have hg_enorm_le : ∀ t, ‖g t‖ₑ ≤ 1 := fun t => by
      simp only [enorm]; exact_mod_cast hg_le_one t
    calc ∫⁻ p, ‖Function.uncurry (fun x t => w x * g t) p‖ₑ ^ (2:ℝ)
            ∂(volume : Measure (Fin n → ℝ)).prod volume
        ≤ ∫⁻ p, (‖w p.1‖ₑ ^ (2:ℝ) * ‖g p.2‖ₑ)
            ∂(volume : Measure (Fin n → ℝ)).prod volume := by
          apply lintegral_mono; intro ⟨x, t⟩
          change ‖w x * g t‖ₑ ^ (2:ℝ) ≤ ‖w x‖ₑ ^ (2:ℝ) * ‖g t‖ₑ
          rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
          gcongr
          calc ‖g t‖ₑ ^ (2:ℝ) ≤ ‖g t‖ₑ ^ (1:ℝ) :=
                ENNReal.rpow_le_rpow_of_exponent_ge (hg_enorm_le t) (by norm_num : (1:ℝ) ≤ 2)
            _ = ‖g t‖ₑ := ENNReal.rpow_one _
      _ ≤ ∫⁻ x, ∫⁻ t, ‖w x‖ₑ ^ (2:ℝ) * ‖g t‖ₑ ∂volume ∂volume :=
          lintegral_prod_le _
      _ = ∫⁻ x, ‖w x‖ₑ ^ (2:ℝ) * (∫⁻ t, ‖g t‖ₑ ∂volume) ∂volume := by
          congr 1; ext x
          exact lintegral_const_mul' _ _
            (ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top)
      _ = (∫⁻ x, ‖w x‖ₑ ^ (2:ℝ) ∂volume) * (∫⁻ t, ‖g t‖ₑ ∂volume) :=
          lintegral_mul_const' _ _ (ne_of_lt hg_lint)
      _ < ⊤ := ENNReal.mul_lt_top hw_lint hg_lint

/-- The operator `M_w ∘ Conv_g` acts as a convolution integral operator with
tensor kernel `K(x,t) = w(x) · g(t)`:

  `(M_w (Conv_g f))(x) = w(x) · ∫ g(t) f(x-t) dt = ∫ w(x) · g(t) · f(x-t) dt`

Uses `mulCLM_spec` (pointwise multiplication a.e.), `convCLM_spec` (convolution
a.e.), and `integral_const_mul` (pulling w(x) into the integral). -/
private theorem mul_conv_integral_rep
    {n : ℕ} [NeZero n]
    (w : (Fin n → ℝ) → ℝ) (hw_meas : Measurable w) (C : ℝ) (hC : 0 < C)
    (hw_bound : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), ‖w x‖ ≤ C)
    (g : (Fin n → ℝ) → ℝ) (hg_l1 : MemLp g 1 (volume : Measure (Fin n → ℝ)))
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    ((mulCLM w hw_meas C hC hw_bound ∘L convCLM g hg_l1) f : (Fin n → ℝ) → ℝ)
      =ᵐ[volume] fun x =>
        ∫ t, (w x * g t) * (f : (Fin n → ℝ) → ℝ) (x - t) := by
  have h1 := mulCLM_spec w hw_meas C hC hw_bound (convCLM g hg_l1 f)
  have h2 := convCLM_spec g hg_l1 f
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [ContinuousLinearMap.comp_apply] at hx1 ⊢
  rw [hx1, hx2]
  simp only [realConv, convolution, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; ext t; ring

/-- Hilbert-Schmidt operators are compact: if `w ∈ L² ∩ L∞` and `g ∈ L¹` with
`‖g‖_∞ ≤ 1`, then `M_w ∘ Conv_g ∘ M_w` is compact on `L²`.

**Proof**: Factor as `(M_w ∘ Conv_g) ∘ M_w`. The operator `M_w ∘ Conv_g` has
convolution kernel `K(x,t) = w(x) · g(t)` with `K ∈ L²(μ ⊗ μ)` (tensor product
of L² functions), so it is Hilbert-Schmidt, hence compact by
`integral_operator_l2_kernel_compact`. The final `M_w` factor is a bounded CLM,
so the composition is compact by `IsCompactOperator.comp_clm`.

**Reference**: Reed-Simon I, Theorem VI.23. -/
theorem hilbert_schmidt_isCompact
    {n : ℕ} [NeZero n]
    (w : (Fin n → ℝ) → ℝ) (hw_meas : Measurable w) (C : ℝ) (hC : 0 < C)
    (hw_bound : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), ‖w x‖ ≤ C)
    (hw_l2 : MemLp w 2 (volume : Measure (Fin n → ℝ)))
    (g : (Fin n → ℝ) → ℝ) (hg_l1 : MemLp g 1 (volume : Measure (Fin n → ℝ)))
    (hg_le_one : ∀ x, ‖g x‖ ≤ 1) :
    IsCompactOperator (mulCLM w hw_meas C hC hw_bound
      ∘L convCLM g hg_l1
      ∘L mulCLM w hw_meas C hC hw_bound) := by
  -- Factor: M_w ∘ Conv_g ∘ M_w = (M_w ∘ Conv_g) ∘ M_w
  -- Step 1: M_w ∘ Conv_g is compact (Hilbert-Schmidt with L² kernel)
  have hMC : IsCompactOperator
      (mulCLM w hw_meas C hC hw_bound ∘L convCLM g hg_l1) :=
    integral_operator_l2_kernel_compact
      (fun x t => w x * g t)
      (tensor_kernel_memLp w hw_l2 g hg_l1 hg_le_one)
      (mulCLM w hw_meas C hC hw_bound ∘L convCLM g hg_l1)
      (fun f => mul_conv_integral_rep w hw_meas C hC hw_bound g hg_l1 f)
  -- Step 2: Compose with M_w (bounded CLM) on the right
  exact hMC.comp_clm (mulCLM w hw_meas C hC hw_bound)

/-- The transfer operator is compact on L²(ℝ^Ns).

The kernel `K(ψ,ψ') = w(ψ) G(ψ-ψ') w(ψ')` satisfies
`|K(ψ,ψ')|² ≤ w(ψ)² w(ψ')²` (since `G ≤ 1`), and `w ∈ L²`
(from Gaussian decay, `transferWeight_memLp_two`), so `K ∈ L²(ℝ^Ns × ℝ^Ns)`
and the operator is Hilbert-Schmidt, hence compact.

**Proof**: Verified hypotheses of `hilbert_schmidt_isCompact`:
- `w = transferWeight` is measurable, essentially bounded, and in L²
- `G = transferGaussian` is in L¹ and satisfies `‖G‖_∞ ≤ 1` -/
theorem transferOperator_isCompact (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    IsCompactOperator (transferOperatorCLM Ns P a mass ha hmass) := by
  unfold transferOperatorCLM
  exact hilbert_schmidt_isCompact
    (transferWeight Ns P a mass)
    (transferWeight_measurable Ns P a mass)
    (transferWeight_bound Ns P a mass ha hmass).choose
    (transferWeight_bound Ns P a mass ha hmass).choose_spec.1
    (transferWeight_bound Ns P a mass ha hmass).choose_spec.2
    (transferWeight_memLp_two Ns P a mass ha hmass)
    (transferGaussian Ns)
    (transferGaussian_memLp Ns)
    (transferGaussian_norm_le_one Ns)

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

/-! ## Perron-Frobenius facts on spectral data

The Perron-Frobenius properties (eigenvalue positivity, ground-state simplicity,
spectral gap) are derived from Jentzsch's theorem in `Jentzsch.lean`.
The names `transferOperator_eigenvalues_pos`, `transferOperator_ground_simple`,
`transferOperator_inner_nonneg`, and `transferOperator_ground_simple_spectral`
are defined there with the same signatures as the former axioms here. -/

end Pphi2

end
