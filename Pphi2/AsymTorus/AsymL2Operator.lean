/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asym cylinder transfer operator: L² infrastructure (Layer B1, Phase 1)

The cylinder transfer matrix `T = e^{-aH_{Ns}}` for the asymmetric-lattice
construction, acting per time-slice on `L²(ℝ^{Ns})`. Phase 1 of the
`asymInteracting_expMoment_volume_uniform` Layer B1 discharge:
definitions, compactness, self-adjointness.

The asym transfer operator differs from the square only in the Wick
constant used in the spatial action: `wickConstantAsym Nt Ns a mass`
(the joint 2D constant — `Nt`-dependent) instead of
`wickConstant 1 Ns a mass` (square's spatial-only). All other
infrastructure (`spatialAction`, `spatialKinetic`, `spatialPotential`,
`timeCoupling`, `transferGaussian`, `mulCLM`, `convCLM`,
`hilbert_schmidt_isCompact`) is parameterized by the Wick constant
already and is reused as-is.

## Main declarations

* `asymTransferWeight` — `w(ψ) = exp(-(a²/2) · h_asym(ψ))`.
* `asymTransferGaussian := transferGaussian Ns` (alias for clarity).
* `asymTransferWeight_measurable`, `_bound`, `_memLp_two` — the
  hypotheses needed by `mulCLM` and `hilbert_schmidt_isCompact`.
* `asymTransferOperatorCLM` — `T = M_w ∘L Conv_G ∘L M_w` on
  `L²(SpatialField Ns)`.
* `asymTransferOperator_isSelfAdjoint`, `_isCompact`.

## References

* `Pphi2/TransferMatrix/L2Operator.lean` — the square analogue. Most
  proofs here mirror it line-by-line.
* `docs/asym-l2-operator-port-scoping.md` — full scope and rationale.
-/

import Pphi2.AsymTorus.AsymLatticeMeasure
import Pphi2.TransferMatrix.L2Operator

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory Real
open scoped BigOperators

variable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]

/-- The Wick monomial `:x^n:_c` is continuous in `x`. Local helper, mirrors
the (private) one in `Pphi2/TransferMatrix/L2Operator.lean`. -/
private theorem continuous_wickMonomial_aux : ∀ (n : ℕ) (c : ℝ),
    Continuous (wickMonomial n c)
  | 0, _ => by simpa [wickMonomial] using continuous_const
  | 1, _ => by simpa [wickMonomial] using continuous_id
  | n + 2, c => by
    simp only [wickMonomial]
    exact ((continuous_id.mul (continuous_wickMonomial_aux (n + 1) c)).sub
      ((continuous_const).mul (continuous_wickMonomial_aux n c)))

/-! ## Asym transfer weight -/

/-- The asym cylinder transfer weight `w(ψ) = exp(-(a²/2) · h_asym(ψ))`,
where `h_asym = spatialAction Ns P a mass (wickConstantAsym Nt Ns a mass)`.
The only difference from the square's `transferWeight` is the Wick
constant — here we use the **joint** asym Wick constant
`wickConstantAsym Nt Ns a mass`, which is the actual GFF site variance
of the asym lattice and depends on `Nt`. -/
def asymTransferWeight (P : InteractionPolynomial) (a mass : ℝ) :
    SpatialField Ns → ℝ :=
  fun ψ => Real.exp (-(a ^ 2 / 2) *
    spatialAction Ns P a mass (wickConstantAsym Nt Ns a mass) ψ)

/-- Alias of `transferGaussian Ns` to make the asym call sites read
naturally. The Gaussian kernel does not depend on `Nt` or the Wick
constant, so this is just a renaming. -/
def asymTransferGaussian : SpatialField Ns → ℝ := transferGaussian Ns

/-- The asym transfer weight is continuous. Mirrors `continuous_transferWeight`. -/
theorem continuous_asymTransferWeight (P : InteractionPolynomial) (a mass : ℝ) :
    Continuous (asymTransferWeight Nt Ns P a mass) := by
  unfold asymTransferWeight
  apply Real.continuous_exp.comp
  apply Continuous.mul continuous_const
  -- `continuous_spatialAction` is private to `L2Operator.lean`, so re-prove inline.
  unfold spatialAction
  refine Continuous.add ?_ ?_
  · -- spatialKinetic
    unfold spatialKinetic
    apply Continuous.mul continuous_const
    apply continuous_finset_sum
    intro x _
    apply Continuous.mul continuous_const
    apply Continuous.pow
    apply Continuous.sub
    · exact continuous_apply (x + 1)
    · exact continuous_apply x
  · -- spatialPotential
    unfold spatialPotential
    apply continuous_finset_sum
    intro x _
    refine Continuous.add ?_ ?_
    · fun_prop
    · unfold wickPolynomial
      refine Continuous.add ?_ ?_
      · refine Continuous.mul continuous_const ?_
        exact (continuous_wickMonomial_aux P.n _).comp (continuous_apply x)
      · apply continuous_finset_sum
        intro m _
        refine Continuous.mul continuous_const ?_
        exact (continuous_wickMonomial_aux m _).comp (continuous_apply x)

/-- The asym transfer weight is measurable. -/
theorem asymTransferWeight_measurable (P : InteractionPolynomial) (a mass : ℝ) :
    Measurable (asymTransferWeight Nt Ns P a mass) :=
  (continuous_asymTransferWeight Nt Ns P a mass).measurable

/-! ## Spatial-action lower bounds with the asym Wick constant -/

/-- Spatial action lower bound (asym Wick constant version). Mirrors the
square's private `spatialAction_lower_bound`. -/
private theorem asymSpatialAction_lower_bound
    (P : InteractionPolynomial) (a mass : ℝ) :
    ∃ B : ℝ, ∀ ψ : SpatialField Ns,
      -B ≤ spatialAction Ns P a mass (wickConstantAsym Nt Ns a mass) ψ := by
  obtain ⟨A, _, hA_bound⟩ :=
    wickPolynomial_bounded_below P (wickConstantAsym Nt Ns a mass)
  refine ⟨Ns * A, fun ψ => ?_⟩
  unfold spatialAction
  have hkin : 0 ≤ spatialKinetic Ns a ψ := by
    unfold spatialKinetic
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun x _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpot :
      -(↑Ns * A) ≤
        spatialPotential Ns P a mass (wickConstantAsym Nt Ns a mass) ψ := by
    unfold spatialPotential
    calc -(↑Ns * A) = ∑ _ : Fin Ns, (-A) := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x : Fin Ns,
            ((1/2) * mass^2 * (ψ x)^2 +
              wickPolynomial P (wickConstantAsym Nt Ns a mass) (ψ x)) := by
            apply Finset.sum_le_sum; intro x _
            linarith [sq_nonneg (mass * ψ x), hA_bound (ψ x)]
  linarith

/-- Quadratic coercive lower bound (asym Wick constant version). Mirrors
the square's private `spatialAction_lower_bound_quadratic`. -/
private theorem asymSpatialAction_lower_bound_quadratic
    (P : InteractionPolynomial) (a mass : ℝ)
    (_ha : 0 < a) (_hmass : 0 < mass) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ ψ : SpatialField Ns,
        (1 / 2) * mass ^ 2 * (∑ x : Fin Ns, (ψ x) ^ 2) - (↑Ns * A) ≤
          spatialAction Ns P a mass (wickConstantAsym Nt Ns a mass) ψ := by
  obtain ⟨A0, hA0_pos, hA0_bound⟩ :=
    wickPolynomial_bounded_below P (wickConstantAsym Nt Ns a mass)
  refine ⟨A0, le_of_lt hA0_pos, fun ψ => ?_⟩
  unfold spatialAction
  have hkin : 0 ≤ spatialKinetic Ns a ψ := by
    unfold spatialKinetic
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun x _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpot :
      (1 / 2) * mass ^ 2 * (∑ x : Fin Ns, (ψ x) ^ 2) - (↑Ns * A0) ≤
        spatialPotential Ns P a mass (wickConstantAsym Nt Ns a mass) ψ := by
    unfold spatialPotential
    calc
      (1 / 2) * mass ^ 2 * (∑ x : Fin Ns, (ψ x) ^ 2) - (↑Ns * A0)
          = ∑ x : Fin Ns, ((1 / 2) * mass ^ 2 * (ψ x) ^ 2 - A0) := by
              simp [Finset.sum_sub_distrib, Finset.mul_sum,
                Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x : Fin Ns,
            ((1 / 2) * mass ^ 2 * (ψ x) ^ 2 +
              wickPolynomial P (wickConstantAsym Nt Ns a mass) (ψ x)) := by
              apply Finset.sum_le_sum
              intro x _
              linarith [hA0_bound (ψ x)]
  linarith

/-- Gaussian decay upper bound for the asym transfer weight. -/
theorem asymTransferWeight_gaussian_decay
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ψ : SpatialField Ns,
      asymTransferWeight Nt Ns P a mass ψ ≤
        Real.exp ((a ^ 2 / 2) * (↑Ns * A)) *
          Real.exp (-(a ^ 2 * mass ^ 2 / 4) * (∑ x : Fin Ns, (ψ x) ^ 2)) := by
  obtain ⟨A, hA_nonneg, hcoer⟩ :=
    asymSpatialAction_lower_bound_quadratic Nt Ns P a mass ha hmass
  refine ⟨A, hA_nonneg, fun ψ => ?_⟩
  unfold asymTransferWeight
  have hcoerψ := hcoer ψ
  have hlin :
      -(a ^ 2 / 2) *
          spatialAction Ns P a mass (wickConstantAsym Nt Ns a mass) ψ ≤
        (a ^ 2 / 2) * (↑Ns * A) - (a ^ 2 * mass ^ 2 / 4) * (∑ x : Fin Ns, (ψ x) ^ 2) := by
    nlinarith [hcoerψ, ha, sq_nonneg a, sq_nonneg mass]
  have hexp := Real.exp_le_exp.mpr hlin
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, Real.exp_add,
    mul_comm, mul_left_comm, mul_assoc] using hexp

/-- The asym transfer weight is strictly positive. -/
theorem asymTransferWeight_pos (P : InteractionPolynomial) (a mass : ℝ)
    (ψ : SpatialField Ns) : 0 < asymTransferWeight Nt Ns P a mass ψ :=
  Real.exp_pos _

/-- The asym transfer weight is essentially bounded. -/
theorem asymTransferWeight_bound (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (_hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᵐ (x : SpatialField Ns) ∂volume,
        ‖asymTransferWeight Nt Ns P a mass x‖ ≤ C := by
  obtain ⟨B, hB⟩ := asymSpatialAction_lower_bound Nt Ns P a mass
  refine ⟨Real.exp (a ^ 2 / 2 * B), Real.exp_pos _, ?_⟩
  apply Filter.Eventually.of_forall
  intro ψ
  simp only [asymTransferWeight, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have h := hB ψ
  nlinarith

/-- The asym transfer weight is in L². -/
theorem asymTransferWeight_memLp_two (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    MemLp (asymTransferWeight Nt Ns P a mass) 2
      (volume : Measure (SpatialField Ns)) := by
  rw [memLp_two_iff_integrable_sq
    (asymTransferWeight_measurable Nt Ns P a mass).aestronglyMeasurable]
  obtain ⟨A, hA_nonneg, hbound⟩ :=
    asymTransferWeight_gaussian_decay Nt Ns P a mass ha hmass
  set K := Real.exp ((a ^ 2 / 2) * (↑Ns * A))
  set β := a ^ 2 * mass ^ 2 / 4
  have hβ : 0 < β := by positivity
  set domFn : SpatialField Ns → ℝ :=
    fun ψ => K ^ 2 * ∏ x : Fin Ns, Real.exp (-(2 * β) * (ψ x) ^ 2)
  have h_sq_bound : ∀ ψ : SpatialField Ns,
      asymTransferWeight Nt Ns P a mass ψ ^ 2 ≤ domFn ψ := by
    intro ψ
    have hw := hbound ψ
    have hw_pos : 0 ≤ asymTransferWeight Nt Ns P a mass ψ :=
      le_of_lt (asymTransferWeight_pos Nt Ns P a mass ψ)
    have hK_pos : 0 ≤ K := le_of_lt (Real.exp_pos _)
    have hD_pos : 0 ≤ Real.exp (-β * (∑ x : Fin Ns, (ψ x) ^ 2)) :=
      le_of_lt (Real.exp_pos _)
    calc asymTransferWeight Nt Ns P a mass ψ ^ 2
        ≤ (K * Real.exp (-β * (∑ x : Fin Ns, (ψ x) ^ 2))) ^ 2 :=
          sq_le_sq' (by linarith) hw
      _ = K ^ 2 * (Real.exp (-β * (∑ x : Fin Ns, (ψ x) ^ 2))) ^ 2 := by ring
      _ = K ^ 2 * Real.exp (-(2 * β) * (∑ x : Fin Ns, (ψ x) ^ 2)) := by
          congr 1; rw [← Real.exp_nat_mul]; push_cast; ring_nf
      _ = K ^ 2 * Real.exp (∑ x : Fin Ns, (-(2 * β) * (ψ x) ^ 2)) := by
          congr 2; rw [Finset.mul_sum]
      _ = domFn ψ := by
          congr 1; rw [Real.exp_sum]
  have h_dom : Integrable domFn volume := by
    apply Integrable.const_mul
    rw [show (volume : Measure (SpatialField Ns)) =
        Measure.pi (fun _ : Fin Ns => (volume : Measure ℝ)) from rfl]
    exact MeasureTheory.Integrable.fintype_prod
      (fun _ => integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 2 * β))
  exact h_dom.mono
    ((asymTransferWeight_measurable Nt Ns P a mass).pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun ψ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
          Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact h_sq_bound ψ))

/-! ## Asym transfer operator -/

/-- The asym cylinder transfer matrix as a CLM on `L²(SpatialField Ns)`.

Same factorization shape as the square's `transferOperatorCLM`:
`T = M_w ∘L Conv_G ∘L M_w` with `w = asymTransferWeight Nt Ns P a mass`
(asym Wick constant) and `G = transferGaussian Ns`. -/
def asymTransferOperatorCLM (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    L2SpatialField Ns →L[ℝ] L2SpatialField Ns :=
  let w := asymTransferWeight Nt Ns P a mass
  let G := transferGaussian Ns
  let hw_meas := asymTransferWeight_measurable Nt Ns P a mass
  let C := (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose
  let hC := (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose_spec.1
  let hw_bound :=
    (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose_spec.2
  let hG := transferGaussian_memLp Ns
  mulCLM w hw_meas C hC hw_bound
    ∘L convCLM G hG
    ∘L mulCLM w hw_meas C hC hw_bound

/-- The asym transfer operator is self-adjoint on `L²(SpatialField Ns)`. -/
theorem asymTransferOperator_isSelfAdjoint
    (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    IsSelfAdjoint (asymTransferOperatorCLM Nt Ns P a mass ha hmass) := by
  unfold asymTransferOperatorCLM
  let w := asymTransferWeight Nt Ns P a mass
  let G := transferGaussian Ns
  let hw_meas := asymTransferWeight_measurable Nt Ns P a mass
  let C := (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose
  let hC := (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose_spec.1
  let hw_bound :=
    (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose_spec.2
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
  change @inner ℝ _ _ ((A.comp (B.comp A)) f) g =
    @inner ℝ _ _ f ((A.comp (B.comp A)) g)
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

/-- The asym transfer operator is compact on `L²(SpatialField Ns)`.

Direct application of `hilbert_schmidt_isCompact` with the asym weight
in place of the square one. The hypotheses are identical in shape
(`w ∈ L² ∩ L∞`, `G ∈ L¹` with `‖G‖_∞ ≤ 1`); only the Wick constant
inside `w` differs. -/
theorem asymTransferOperator_isCompact (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    IsCompactOperator (asymTransferOperatorCLM Nt Ns P a mass ha hmass) := by
  unfold asymTransferOperatorCLM
  exact hilbert_schmidt_isCompact
    (asymTransferWeight Nt Ns P a mass)
    (asymTransferWeight_measurable Nt Ns P a mass)
    (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose
    (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose_spec.1
    (asymTransferWeight_bound Nt Ns P a mass ha hmass).choose_spec.2
    (asymTransferWeight_memLp_two Nt Ns P a mass ha hmass)
    (transferGaussian Ns)
    (transferGaussian_memLp Ns)
    (transferGaussian_norm_le_one Ns)

end Pphi2

end
