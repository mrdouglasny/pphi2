/- 
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L² bound on the asym rough-field Wick error

This is UNIT 5 of the isotropic-rectangular Nelson port. It packages the
pointwise cross-term expansion of `asymCanonicalRoughError` and the final
uniform variance estimate.

The only remaining analytical gap is the per-cross-term L² estimate
`asymCanonicalCrossTerm_l2_sq_le`, which is the rectangular analogue of
`RoughErrorBound.canonicalCrossTerm_l2_sq_le`. The downstream finite-sum
assembly is completed here.
-/

import Pphi2.NelsonEstimate.AsymCrossTermL2Identity
import Pphi2.NelsonEstimate.WickBinomial
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open GaussianField
open MeasureTheory
open scoped BigOperators

namespace Pphi2

/-- Pointwise binomial expansion of the asym rough error. -/
lemma asymCanonicalRoughError_pointwise_decomposition
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (P : InteractionPolynomial) (η : AsymCanonicalJoint Nt Ns) :
    asymCanonicalRoughError Nt Ns a mass T P η =
      a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
        ((1 / P.n : ℝ) * ∑ k ∈ Finset.range P.n,
            (P.n.choose k : ℝ) *
              wickMonomial k (asymSmoothWickConstant Nt Ns a mass T)
                (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) *
              wickMonomial (P.n - k) (asymCanonicalRoughWickConstant Nt Ns a mass T)
                (asymCanonicalRoughFieldFunction Nt Ns a mass T η x)
        + ∑ m : Fin P.n, P.coeff m * ∑ k ∈ Finset.range (m : ℕ),
            ((m : ℕ).choose k : ℝ) *
              wickMonomial k (asymSmoothWickConstant Nt Ns a mass T)
                (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) *
              wickMonomial ((m : ℕ) - k) (asymCanonicalRoughWickConstant Nt Ns a mass T)
                (asymCanonicalRoughFieldFunction Nt Ns a mass T η x)) := by
  unfold asymCanonicalRoughError asymCanonicalFullInteractionJoint asymCanonicalSmoothInteraction
  calc
    a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
        wickPolynomial P (wickConstantAsym Nt Ns a mass)
          (asymCanonicalSumFieldFunction Nt Ns a mass T η x) -
      a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
        wickPolynomial P (asymSmoothWickConstant Nt Ns a mass T)
          (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x)
      = a ^ 2 *
          ((∑ x : AsymLatticeSites Nt Ns,
              wickPolynomial P (wickConstantAsym Nt Ns a mass)
                (asymCanonicalSumFieldFunction Nt Ns a mass T η x)) -
            ∑ x : AsymLatticeSites Nt Ns,
              wickPolynomial P (asymSmoothWickConstant Nt Ns a mass T)
                (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x)) := by
            ring
    _ = a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
          (wickPolynomial P (wickConstantAsym Nt Ns a mass)
              (asymCanonicalSumFieldFunction Nt Ns a mass T η x) -
            wickPolynomial P (asymSmoothWickConstant Nt Ns a mass T)
              (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x)) := by
            rw [Finset.sum_sub_distrib]
  refine congrArg (fun t => a ^ 2 * t) ?_
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hsplit :
      wickConstantAsym Nt Ns a mass =
        asymSmoothWickConstant Nt Ns a mass T +
          asymCanonicalRoughWickConstant Nt Ns a mass T := by
    unfold asymCanonicalRoughWickConstant
    ring
  rw [hsplit]
  change
    wickPolynomial P
        (asymSmoothWickConstant Nt Ns a mass T +
          asymCanonicalRoughWickConstant Nt Ns a mass T)
        (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x +
          asymCanonicalRoughFieldFunction Nt Ns a mass T η x) -
      wickPolynomial P (asymSmoothWickConstant Nt Ns a mass T)
        (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x) =
    _
  exact wickPolynomial_add_sub_self P
    (asymSmoothWickConstant Nt Ns a mass T)
    (asymCanonicalRoughWickConstant Nt Ns a mass T)
    (asymCanonicalSmoothFieldFunction Nt Ns a mass T η x)
    (asymCanonicalRoughFieldFunction Nt Ns a mass T η x)

/-- Reindexed cross-term expansion of the asym rough error. -/
lemma asymCanonicalRoughError_eq_sum_over_cross_terms
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (P : InteractionPolynomial) (η : AsymCanonicalJoint Nt Ns) :
    asymCanonicalRoughError Nt Ns a mass T P η =
      (1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
        (P.n.choose j : ℝ) * asymCanonicalCrossTerm Nt Ns a mass T η P.n j
      + ∑ m : Fin P.n, P.coeff m *
          ∑ j ∈ Finset.range (m : ℕ),
            ((m : ℕ).choose j : ℝ) *
              asymCanonicalCrossTerm Nt Ns a mass T η (m : ℕ) j := by
  rw [asymCanonicalRoughError_pointwise_decomposition Nt Ns a mass T P η]
  unfold asymCanonicalCrossTerm
  rw [Finset.sum_add_distrib, mul_add]
  refine congr_arg₂ (· + ·) ?_ ?_
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [mul_assoc, ← Finset.mul_sum]
    ring
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [mul_assoc, ← Finset.mul_sum]
    ring

/-- Uniform L² bound on the asym rough Wick interaction error. -/
theorem asymRoughError_variance
    (P : InteractionPolynomial)
    (mass Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) (hmass : 0 < mass) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (_ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
        ∀ (T : ℝ), 0 < T →
        ∫ η, (asymCanonicalRoughError Nt Ns a mass T P η) ^ 2
          ∂(asymCanonicalJointMeasure Nt Ns) ≤
          K * T * (1 + |Real.log T|) ^ (P.n - 1) := by
  classical
  let KLeadFun : ℕ → ℝ := fun j =>
    if hj : j ∈ Finset.range P.n then
      Classical.choose
        (asymCanonicalCrossTerm_l2_sq_le mass Lt Ls hLt hLs hmass P.n j
          (Nat.succ_le_of_lt (Nat.sub_pos_of_lt (Finset.mem_range.mp hj))))
    else 1
  let KPerFun : Fin P.n → ℕ → ℝ := fun m j =>
    if hj : j ∈ Finset.range (m : ℕ) then
      Classical.choose
        (asymCanonicalCrossTerm_l2_sq_le mass Lt Ls hLt hLs hmass (m : ℕ) j
          (Nat.succ_le_of_lt (Nat.sub_pos_of_lt (Finset.mem_range.mp hj))))
    else 1
  let LeadCoeffSq : ℝ :=
    ∑ j ∈ Finset.range P.n, (((1 / P.n : ℝ) * (P.n.choose j : ℝ)) ^ 2)
  let PerCoeffSq : Fin P.n → ℝ := fun m =>
    ∑ j ∈ Finset.range (m : ℕ), (P.coeff m * ((m : ℕ).choose j : ℝ)) ^ 2
  let KLeadSum : ℝ := LeadCoeffSq * ∑ j ∈ Finset.range P.n, KLeadFun j
  let KPerSum : ℝ := (P.n : ℝ) *
    ∑ m : Fin P.n, PerCoeffSq m * ∑ j ∈ Finset.range (m : ℕ), KPerFun m j
  let K0 : ℝ := 2 * (KLeadSum + KPerSum)
  let K : ℝ := K0 + 1
  have hKLead_pos : ∀ j (hj : j ∈ Finset.range P.n), 0 < KLeadFun j := by
    intro j hj
    dsimp [KLeadFun]
    rw [dif_pos hj]
    exact
      (Classical.choose_spec
        (asymCanonicalCrossTerm_l2_sq_le mass Lt Ls hLt hLs hmass P.n j
          (Nat.succ_le_of_lt (Nat.sub_pos_of_lt (Finset.mem_range.mp hj))))).1
  have hKLead_memLp_bound :
      ∀ j (hj : j ∈ Finset.range P.n),
        ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ), 0 < a →
          (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
          ∀ (T : ℝ), 0 < T →
          ∃ hf : MeasureTheory.MemLp
              (fun η : AsymCanonicalJoint Nt Ns =>
                asymCanonicalCrossTerm Nt Ns a mass T η P.n j)
              2
              (asymCanonicalJointMeasure Nt Ns),
            ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η P.n j) ^ 2
              ∂(asymCanonicalJointMeasure Nt Ns) ≤
              KLeadFun j * T * (1 + |Real.log T|) ^ j := by
    intro j hj Nt Ns _ _ a ha hvolt hvols T hT
    dsimp [KLeadFun]
    rw [dif_pos hj]
    exact
      (Classical.choose_spec
        (asymCanonicalCrossTerm_l2_sq_le mass Lt Ls hLt hLs hmass P.n j
          (Nat.succ_le_of_lt (Nat.sub_pos_of_lt (Finset.mem_range.mp hj))))).2
        Nt Ns a ha hvolt hvols T hT
  have hKPer_pos :
      ∀ (m : Fin P.n) (j : ℕ) (hj : j ∈ Finset.range (m : ℕ)), 0 < KPerFun m j := by
    intro m j hj
    dsimp [KPerFun]
    rw [dif_pos hj]
    exact
      (Classical.choose_spec
        (asymCanonicalCrossTerm_l2_sq_le mass Lt Ls hLt hLs hmass (m : ℕ) j
          (Nat.succ_le_of_lt (Nat.sub_pos_of_lt (Finset.mem_range.mp hj))))).1
  have hKPer_memLp_bound :
      ∀ (m : Fin P.n) (j : ℕ) (hj : j ∈ Finset.range (m : ℕ)),
        ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ), 0 < a →
          (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
          ∀ (T : ℝ), 0 < T →
          ∃ hf : MeasureTheory.MemLp
              (fun η : AsymCanonicalJoint Nt Ns =>
                asymCanonicalCrossTerm Nt Ns a mass T η (m : ℕ) j)
              2
              (asymCanonicalJointMeasure Nt Ns),
            ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η (m : ℕ) j) ^ 2
              ∂(asymCanonicalJointMeasure Nt Ns) ≤
              KPerFun m j * T * (1 + |Real.log T|) ^ j := by
    intro m j hj Nt Ns _ _ a ha hvolt hvols T hT
    dsimp [KPerFun]
    rw [dif_pos hj]
    exact
      (Classical.choose_spec
        (asymCanonicalCrossTerm_l2_sq_le mass Lt Ls hLt hLs hmass (m : ℕ) j
          (Nat.succ_le_of_lt (Nat.sub_pos_of_lt (Finset.mem_range.mp hj))))).2
        Nt Ns a ha hvolt hvols T hT
  refine ⟨K, by
    have hLeadCoeffSq_nonneg : 0 ≤ LeadCoeffSq := by
      dsimp [LeadCoeffSq]
      exact Finset.sum_nonneg fun j hj => sq_nonneg _
    have hLeadK_nonneg : 0 ≤ ∑ j ∈ Finset.range P.n, KLeadFun j := by
      exact Finset.sum_nonneg fun j hj => le_of_lt (hKLead_pos j hj)
    have hPerCoeffSq_nonneg : ∀ m : Fin P.n, 0 ≤ PerCoeffSq m := by
      intro m
      dsimp [PerCoeffSq]
      exact Finset.sum_nonneg fun j hj => sq_nonneg _
    have hPerK_nonneg : ∀ m : Fin P.n, 0 ≤ ∑ j ∈ Finset.range (m : ℕ), KPerFun m j := by
      intro m
      exact Finset.sum_nonneg fun j hj => le_of_lt (hKPer_pos m j hj)
    have hKLeadSum_nonneg : 0 ≤ KLeadSum := by
      dsimp [KLeadSum]
      exact mul_nonneg hLeadCoeffSq_nonneg hLeadK_nonneg
    have hKPerSum_nonneg : 0 ≤ KPerSum := by
      dsimp [KPerSum]
      refine mul_nonneg (by positivity) ?_
      exact Finset.sum_nonneg fun m hm =>
        mul_nonneg (hPerCoeffSq_nonneg m) (hPerK_nonneg m)
    have hK0_nonneg : 0 ≤ K0 := by
      dsimp [K0]
      positivity
    dsimp [K]
    linarith, ?_⟩
  intro Nt Ns _ _ a ha hvolt hvols T hT
  let μ := asymCanonicalJointMeasure Nt Ns
  let u : ℝ := 1 + |Real.log T|
  let Lead : AsymCanonicalJoint Nt Ns → ℝ := fun η =>
    ∑ j ∈ Finset.range P.n,
      ((1 / P.n : ℝ) * (P.n.choose j : ℝ)) *
        asymCanonicalCrossTerm Nt Ns a mass T η P.n j
  let Rm : Fin P.n → AsymCanonicalJoint Nt Ns → ℝ := fun m η =>
    ∑ j ∈ Finset.range (m : ℕ),
      (P.coeff m * ((m : ℕ).choose j : ℝ)) *
        asymCanonicalCrossTerm Nt Ns a mass T η (m : ℕ) j
  let Per : AsymCanonicalJoint Nt Ns → ℝ := fun η => ∑ m : Fin P.n, Rm m η
  have hu_one : 1 ≤ u := by
    dsimp [u]
    linarith [abs_nonneg (Real.log T)]
  have hu_nonneg : 0 ≤ u := by
    linarith
  have hT_nonneg : 0 ≤ T := le_of_lt hT
  have hcommon_nonneg : 0 ≤ T * u ^ (P.n - 1) := by
    positivity
  have hrough_eq :
      ∀ η : AsymCanonicalJoint Nt Ns,
        asymCanonicalRoughError Nt Ns a mass T P η = Lead η + Per η := by
    intro η
    calc
      asymCanonicalRoughError Nt Ns a mass T P η
        = (1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
            (P.n.choose j : ℝ) * asymCanonicalCrossTerm Nt Ns a mass T η P.n j
          + ∑ m : Fin P.n, P.coeff m *
              ∑ j ∈ Finset.range (m : ℕ),
                ((m : ℕ).choose j : ℝ) * asymCanonicalCrossTerm Nt Ns a mass T η (m : ℕ) j := by
              exact asymCanonicalRoughError_eq_sum_over_cross_terms Nt Ns a mass T P η
      _ = Lead η + Per η := by
            simp [Lead, Per, Rm, Finset.mul_sum]
            ring
  have hLead_memLp : MeasureTheory.MemLp Lead 2 μ := by
    refine memLp_finset_sum (Finset.range P.n) ?_
    intro j hj
    rcases hKLead_memLp_bound j hj Nt Ns a ha hvolt hvols T hT with ⟨hf, hbound⟩
    simpa [Lead] using hf.const_mul ((1 / P.n : ℝ) * (P.n.choose j : ℝ))
  have hRm_memLp : ∀ m : Fin P.n, MeasureTheory.MemLp (Rm m) 2 μ := by
    intro m
    refine memLp_finset_sum (Finset.range (m : ℕ)) ?_
    intro j hj
    rcases hKPer_memLp_bound m j hj Nt Ns a ha hvolt hvols T hT with ⟨hf, hbound⟩
    simpa [Rm] using hf.const_mul (P.coeff m * ((m : ℕ).choose j : ℝ))
  have hPer_memLp : MeasureTheory.MemLp Per 2 μ := by
    refine memLp_finset_sum Finset.univ ?_
    intro m hm
    simpa [Per] using hRm_memLp m
  have hTotal_memLp : MeasureTheory.MemLp (fun η => Lead η + Per η) 2 μ :=
    hLead_memLp.add hPer_memLp
  have hLead_int : Integrable (fun η => (Lead η) ^ 2) μ := hLead_memLp.integrable_sq
  have hPer_int : Integrable (fun η => (Per η) ^ 2) μ := hPer_memLp.integrable_sq
  have hTotal_int : Integrable (fun η => (Lead η + Per η) ^ 2) μ := hTotal_memLp.integrable_sq
  have hLead_point :
      ∀ η : AsymCanonicalJoint Nt Ns,
        (Lead η) ^ 2 ≤
          LeadCoeffSq *
            ∑ j ∈ Finset.range P.n,
              (asymCanonicalCrossTerm Nt Ns a mass T η P.n j) ^ 2 := by
    intro η
    dsimp [LeadCoeffSq, Lead]
    simpa [pow_two] using
      (Finset.sum_mul_sq_le_sq_mul_sq
        (R := ℝ) (Finset.range P.n)
        (fun j => (1 / P.n : ℝ) * (P.n.choose j : ℝ))
        (fun j => asymCanonicalCrossTerm Nt Ns a mass T η P.n j))
  have hRm_point :
      ∀ (m : Fin P.n) (η : AsymCanonicalJoint Nt Ns),
        (Rm m η) ^ 2 ≤
          PerCoeffSq m *
            ∑ j ∈ Finset.range (m : ℕ),
              (asymCanonicalCrossTerm Nt Ns a mass T η (m : ℕ) j) ^ 2 := by
    intro m η
    dsimp [PerCoeffSq, Rm]
    simpa [pow_two] using
      (Finset.sum_mul_sq_le_sq_mul_sq
        (R := ℝ) (Finset.range (m : ℕ))
        (fun j => P.coeff m * ((m : ℕ).choose j : ℝ))
        (fun j => asymCanonicalCrossTerm Nt Ns a mass T η (m : ℕ) j))
  have hPer_point :
      ∀ η : AsymCanonicalJoint Nt Ns,
        (Per η) ^ 2 ≤
          (P.n : ℝ) * ∑ m : Fin P.n, (Rm m η) ^ 2 := by
    intro η
    dsimp [Per]
    have h :=
      Finset.sum_mul_sq_le_sq_mul_sq
        (R := ℝ) (Finset.univ : Finset (Fin P.n))
        (fun _ : Fin P.n => (1 : ℝ))
        (fun m : Fin P.n => Rm m η)
    simpa [pow_two, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  have hLead_rhs_int :
      Integrable
        (fun η : AsymCanonicalJoint Nt Ns =>
          LeadCoeffSq *
            ∑ j ∈ Finset.range P.n,
              (asymCanonicalCrossTerm Nt Ns a mass T η P.n j) ^ 2)
        μ := by
    refine Integrable.const_mul ?_ LeadCoeffSq
    refine MeasureTheory.integrable_finset_sum (Finset.range P.n) ?_
    intro j hj
    rcases hKLead_memLp_bound j hj Nt Ns a ha hvolt hvols T hT with ⟨hf, hbound⟩
    simpa using hf.integrable_sq
  have hRm_rhs_int :
      ∀ m : Fin P.n,
        Integrable
          (fun η : AsymCanonicalJoint Nt Ns =>
            PerCoeffSq m *
              ∑ j ∈ Finset.range (m : ℕ),
                (asymCanonicalCrossTerm Nt Ns a mass T η (m : ℕ) j) ^ 2)
          μ := by
    intro m
    refine Integrable.const_mul ?_ (PerCoeffSq m)
    refine MeasureTheory.integrable_finset_sum (Finset.range (m : ℕ)) ?_
    intro j hj
    rcases hKPer_memLp_bound m j hj Nt Ns a ha hvolt hvols T hT with ⟨hf, hbound⟩
    simpa using hf.integrable_sq
  have hPer_rhs_int :
      Integrable
        (fun η : AsymCanonicalJoint Nt Ns =>
          (P.n : ℝ) * ∑ m : Fin P.n, (Rm m η) ^ 2)
        μ := by
    refine Integrable.const_mul ?_ (P.n : ℝ)
    refine MeasureTheory.integrable_finset_sum Finset.univ ?_
    intro m hm
    simpa using (hRm_memLp m).integrable_sq
  have hLead_sq_bound :
      ∫ η, (Lead η) ^ 2 ∂μ ≤
        LeadCoeffSq *
          ∑ j ∈ Finset.range P.n,
            ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η P.n j) ^ 2 ∂μ := by
    calc
      ∫ η, (Lead η) ^ 2 ∂μ
        ≤ ∫ η,
            LeadCoeffSq *
              ∑ j ∈ Finset.range P.n,
                (asymCanonicalCrossTerm Nt Ns a mass T η P.n j) ^ 2 ∂μ := by
              refine integral_mono_ae hLead_int hLead_rhs_int ?_
              exact Filter.Eventually.of_forall hLead_point
      _ = LeadCoeffSq *
            ∑ j ∈ Finset.range P.n,
              ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η P.n j) ^ 2 ∂μ := by
            rw [integral_const_mul]
            congr 1
            refine integral_finset_sum (Finset.range P.n) ?_
            intro j hj
            rcases hKLead_memLp_bound j hj Nt Ns a ha hvolt hvols T hT with ⟨hf, hbound⟩
            simpa using hf.integrable_sq
  have hRm_sq_bound :
      ∀ m : Fin P.n,
        ∫ η, (Rm m η) ^ 2 ∂μ ≤
          PerCoeffSq m *
            ∑ j ∈ Finset.range (m : ℕ),
              ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η (m : ℕ) j) ^ 2 ∂μ := by
    intro m
    calc
      ∫ η, (Rm m η) ^ 2 ∂μ
        ≤ ∫ η,
            PerCoeffSq m *
              ∑ j ∈ Finset.range (m : ℕ),
                (asymCanonicalCrossTerm Nt Ns a mass T η (m : ℕ) j) ^ 2 ∂μ := by
              refine integral_mono_ae (hRm_memLp m).integrable_sq (hRm_rhs_int m) ?_
              exact Filter.Eventually.of_forall (hRm_point m)
      _ = PerCoeffSq m *
            ∑ j ∈ Finset.range (m : ℕ),
              ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η (m : ℕ) j) ^ 2 ∂μ := by
            rw [integral_const_mul]
            congr 1
            refine integral_finset_sum (Finset.range (m : ℕ)) ?_
            intro j hj
            rcases hKPer_memLp_bound m j hj Nt Ns a ha hvolt hvols T hT with ⟨hf, hbound⟩
            simpa using hf.integrable_sq
  have hPer_sq_bound :
      ∫ η, (Per η) ^ 2 ∂μ ≤
        (P.n : ℝ) * ∑ m : Fin P.n, ∫ η, (Rm m η) ^ 2 ∂μ := by
    calc
      ∫ η, (Per η) ^ 2 ∂μ
        ≤ ∫ η, (P.n : ℝ) * ∑ m : Fin P.n, (Rm m η) ^ 2 ∂μ := by
              refine integral_mono_ae hPer_int hPer_rhs_int ?_
              exact Filter.Eventually.of_forall hPer_point
      _ = (P.n : ℝ) * ∑ m : Fin P.n, ∫ η, (Rm m η) ^ 2 ∂μ := by
            rw [integral_const_mul]
            congr 1
            refine integral_finset_sum Finset.univ ?_
            intro m hm
            simpa using (hRm_memLp m).integrable_sq
  have hLead_bound :
      ∫ η, (Lead η) ^ 2 ∂μ ≤ KLeadSum * T * u ^ (P.n - 1) := by
    have hLeadCrossBound :
        ∑ j ∈ Finset.range P.n,
          ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η P.n j) ^ 2 ∂μ
        ≤
        ∑ j ∈ Finset.range P.n,
          KLeadFun j * T * u ^ (P.n - 1) := by
      refine Finset.sum_le_sum ?_
      intro j hj
      have hj_le : j ≤ P.n - 1 := Nat.le_pred_of_lt (Finset.mem_range.mp hj)
      have hpow : u ^ j ≤ u ^ (P.n - 1) := pow_le_pow_right₀ hu_one hj_le
      rcases hKLead_memLp_bound j hj Nt Ns a ha hvolt hvols T hT with ⟨hf, hbound⟩
      calc
        ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η P.n j) ^ 2 ∂μ
          ≤ KLeadFun j * T * u ^ j := by simpa [u] using hbound
        _ ≤ KLeadFun j * T * u ^ (P.n - 1) := by
            have hKT_nonneg : 0 ≤ KLeadFun j * T :=
              mul_nonneg (le_of_lt (hKLead_pos j hj)) hT_nonneg
            exact mul_le_mul_of_nonneg_left hpow hKT_nonneg
    have hLeadCoeffSq_nonneg : 0 ≤ LeadCoeffSq := by
      dsimp [LeadCoeffSq]
      exact Finset.sum_nonneg fun j hj => sq_nonneg _
    calc
      ∫ η, (Lead η) ^ 2 ∂μ
        ≤ LeadCoeffSq *
            ∑ j ∈ Finset.range P.n,
              ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η P.n j) ^ 2 ∂μ := hLead_sq_bound
      _ ≤ LeadCoeffSq *
            ∑ j ∈ Finset.range P.n,
              KLeadFun j * T * u ^ (P.n - 1) := by
            exact mul_le_mul_of_nonneg_left hLeadCrossBound hLeadCoeffSq_nonneg
      _ = KLeadSum * T * u ^ (P.n - 1) := by
            have hsum :
                ∑ j ∈ Finset.range P.n, KLeadFun j * T * u ^ (P.n - 1) =
                  (∑ j ∈ Finset.range P.n, KLeadFun j) * (T * u ^ (P.n - 1)) := by
                calc
                  ∑ j ∈ Finset.range P.n, KLeadFun j * T * u ^ (P.n - 1)
                    = ∑ j ∈ Finset.range P.n, KLeadFun j * (T * u ^ (P.n - 1)) := by
                        refine Finset.sum_congr rfl ?_
                        intro j hj
                        ring
                  _ = (∑ j ∈ Finset.range P.n, KLeadFun j) * (T * u ^ (P.n - 1)) := by
                        exact (Finset.sum_mul
                          (s := Finset.range P.n)
                          (f := KLeadFun)
                          (a := T * u ^ (P.n - 1))).symm
            rw [hsum]
            dsimp [KLeadSum]
            ring
  have hPer_bound :
      ∫ η, (Per η) ^ 2 ∂μ ≤ KPerSum * T * u ^ (P.n - 1) := by
    have hRmBound :
        ∀ m : Fin P.n,
          ∫ η, (Rm m η) ^ 2 ∂μ ≤
            PerCoeffSq m *
              ∑ j ∈ Finset.range (m : ℕ),
                KPerFun m j * T * u ^ (P.n - 1) := by
      intro m
      calc
        ∫ η, (Rm m η) ^ 2 ∂μ
          ≤ PerCoeffSq m *
              ∑ j ∈ Finset.range (m : ℕ),
                ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η (m : ℕ) j) ^ 2 ∂μ :=
            hRm_sq_bound m
        _ ≤ PerCoeffSq m *
              ∑ j ∈ Finset.range (m : ℕ),
                KPerFun m j * T * u ^ (P.n - 1) := by
              have hsum :
                  ∑ j ∈ Finset.range (m : ℕ),
                    ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η (m : ℕ) j) ^ 2 ∂μ
                  ≤
                  ∑ j ∈ Finset.range (m : ℕ),
                    KPerFun m j * T * u ^ (P.n - 1) := by
                refine Finset.sum_le_sum ?_
                intro j hj
                have hj_le : j ≤ P.n - 1 := by
                  exact Nat.le_pred_of_lt (lt_trans (Finset.mem_range.mp hj) m.2)
                have hpow : u ^ j ≤ u ^ (P.n - 1) := pow_le_pow_right₀ hu_one hj_le
                rcases hKPer_memLp_bound m j hj Nt Ns a ha hvolt hvols T hT with ⟨hf, hbound⟩
                calc
                  ∫ η, (asymCanonicalCrossTerm Nt Ns a mass T η (m : ℕ) j) ^ 2 ∂μ
                    ≤ KPerFun m j * T * u ^ j := by simpa [u] using hbound
                  _ ≤ KPerFun m j * T * u ^ (P.n - 1) := by
                      have hKT_nonneg : 0 ≤ KPerFun m j * T :=
                        mul_nonneg (le_of_lt (hKPer_pos m j hj)) hT_nonneg
                      exact mul_le_mul_of_nonneg_left hpow hKT_nonneg
              have hcoeff_nonneg : 0 ≤ PerCoeffSq m := by
                dsimp [PerCoeffSq]
                exact Finset.sum_nonneg fun j hj => sq_nonneg _
              exact mul_le_mul_of_nonneg_left hsum hcoeff_nonneg
    calc
      ∫ η, (Per η) ^ 2 ∂μ
        ≤ (P.n : ℝ) * ∑ m : Fin P.n, ∫ η, (Rm m η) ^ 2 ∂μ := hPer_sq_bound
      _ ≤ (P.n : ℝ) * ∑ m : Fin P.n,
            PerCoeffSq m *
              ∑ j ∈ Finset.range (m : ℕ),
                KPerFun m j * T * u ^ (P.n - 1) := by
            have hsum : ∑ m : Fin P.n, ∫ η, (Rm m η) ^ 2 ∂μ ≤
                ∑ m : Fin P.n,
                  PerCoeffSq m *
                    ∑ j ∈ Finset.range (m : ℕ), KPerFun m j * T * u ^ (P.n - 1) := by
              refine Finset.sum_le_sum ?_
              intro m hm
              exact hRmBound m
            exact mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = KPerSum * T * u ^ (P.n - 1) := by
            have hsum :
                ∑ m : Fin P.n,
                  PerCoeffSq m * ∑ j ∈ Finset.range (m : ℕ), KPerFun m j * T * u ^ (P.n - 1) =
                (∑ m : Fin P.n,
                  PerCoeffSq m * ∑ j ∈ Finset.range (m : ℕ), KPerFun m j) *
                  (T * u ^ (P.n - 1)) := by
              calc
                ∑ m : Fin P.n,
                    PerCoeffSq m * ∑ j ∈ Finset.range (m : ℕ), KPerFun m j * T * u ^ (P.n - 1)
                  = ∑ m : Fin P.n,
                      (PerCoeffSq m * ∑ j ∈ Finset.range (m : ℕ), KPerFun m j) *
                        (T * u ^ (P.n - 1)) := by
                          refine Finset.sum_congr rfl ?_
                          intro m hm
                          have hinner :
                              ∑ j ∈ Finset.range (m : ℕ), KPerFun m j * T * u ^ (P.n - 1) =
                                (∑ j ∈ Finset.range (m : ℕ), KPerFun m j) *
                                  (T * u ^ (P.n - 1)) := by
                                  calc
                                    ∑ j ∈ Finset.range (m : ℕ), KPerFun m j * T * u ^ (P.n - 1)
                                      = ∑ j ∈ Finset.range (m : ℕ),
                                          KPerFun m j * (T * u ^ (P.n - 1)) := by
                                            refine Finset.sum_congr rfl ?_
                                            intro j hj
                                            ring
                                    _ =
                                        (∑ j ∈ Finset.range (m : ℕ), KPerFun m j) *
                                          (T * u ^ (P.n - 1)) := by
                                            exact (Finset.sum_mul
                                              (s := Finset.range (m : ℕ))
                                              (f := KPerFun m)
                                              (a := T * u ^ (P.n - 1))).symm
                          rw [hinner]
                          ring
                _ =
                    (∑ m : Fin P.n,
                      PerCoeffSq m * ∑ j ∈ Finset.range (m : ℕ), KPerFun m j) *
                      (T * u ^ (P.n - 1)) := by
                        exact (Finset.sum_mul
                          (s := Finset.univ)
                          (f := fun m : Fin P.n =>
                            PerCoeffSq m * ∑ j ∈ Finset.range (m : ℕ), KPerFun m j)
                          (a := T * u ^ (P.n - 1))).symm
            rw [hsum]
            dsimp [KPerSum]
            ring
  have hRough_sq_bound :
      ∫ η, (Lead η + Per η) ^ 2 ∂μ ≤
        2 * (∫ η, (Lead η) ^ 2 ∂μ + ∫ η, (Per η) ^ 2 ∂μ) := by
    have h_rhs_int : Integrable
        (fun η : AsymCanonicalJoint Nt Ns => 2 * ((Lead η) ^ 2 + (Per η) ^ 2)) μ := by
      exact (hLead_int.add hPer_int).const_mul 2
    have h_point :
        ∀ η : AsymCanonicalJoint Nt Ns,
          (Lead η + Per η) ^ 2 ≤ 2 * ((Lead η) ^ 2 + (Per η) ^ 2) := by
      intro η
      nlinarith [sq_nonneg (Lead η - Per η)]
    calc
      ∫ η, (Lead η + Per η) ^ 2 ∂μ
        ≤ ∫ η, 2 * ((Lead η) ^ 2 + (Per η) ^ 2) ∂μ := by
              refine integral_mono_ae hTotal_int h_rhs_int ?_
              exact Filter.Eventually.of_forall h_point
      _ = 2 * (∫ η, (Lead η) ^ 2 ∂μ + ∫ η, (Per η) ^ 2 ∂μ) := by
            rw [integral_const_mul, integral_add hLead_int hPer_int]
  calc
    ∫ η, (asymCanonicalRoughError Nt Ns a mass T P η) ^ 2 ∂μ
      = ∫ η, (Lead η + Per η) ^ 2 ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun η => by
            change (asymCanonicalRoughError Nt Ns a mass T P η) ^ 2 =
              (Lead η + Per η) ^ 2
            rw [hrough_eq η]
    _ ≤ 2 * (∫ η, (Lead η) ^ 2 ∂μ + ∫ η, (Per η) ^ 2 ∂μ) := hRough_sq_bound
    _ ≤ 2 * (KLeadSum * T * u ^ (P.n - 1) + KPerSum * T * u ^ (P.n - 1)) := by
          gcongr
    _ = K0 * T * u ^ (P.n - 1) := by
          dsimp [K0]
          ring
    _ ≤ K * T * u ^ (P.n - 1) := by
          have hK0_le_K : K0 ≤ K := by
            dsimp [K, K0]
            linarith
          simpa [mul_assoc] using
            (mul_le_mul_of_nonneg_right hK0_le_K hcommon_nonneg)
    _ = K * T * (1 + |Real.log T|) ^ (P.n - 1) := by
          rfl

end Pphi2
