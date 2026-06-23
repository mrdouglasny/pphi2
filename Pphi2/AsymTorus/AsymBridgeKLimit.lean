/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymBridgeInstance
import Pphi2.AsymTorus.AsymVarianceBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Layer-B2 Route A, Piece 3: removing the slice truncation

This file is the dominated-convergence bridge from the bounded slice observable
`A_{g,K}` to the unbounded linear slice observable `A_g`.

The final theorem is intentionally stated with the finite-`K` estimate as a
hypothesis: Piece 2 currently exposes the connected two-point/susceptibility
bound, while downstream assembly may package the corresponding finite-`K`
time-sum estimate in more than one equivalent form.  This file proves the
K-limit step once such a K-uniform bound is supplied.
-/

open MeasureTheory GaussianField ReflectionPositivity Filter
open scoped BigOperators Topology

namespace Pphi2

variable {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]

local notation "ν" => (volume : Measure (SpatialField Ns))

/-! ## Time-family observables -/

/-- The untruncated linear time-family observable
`ψ ↦ Σ_t ⟨g_t, ψ_t⟩` on the periodic path space. -/
noncomputable def asymSliceFamilyLinear
    (g : ZMod Nt → SpatialField Ns) (ψ : ZMod Nt → SpatialField Ns) : ℝ :=
  ∑ t : ZMod Nt, asymSliceObsLinear (g t) (ψ t)

/-- The truncated time-family observable with a common cutoff `K` on all slices. -/
noncomputable def asymSliceFamilyTrunc
    (g : ZMod Nt → SpatialField Ns) (K : ℝ) (ψ : ZMod Nt → SpatialField Ns) : ℝ :=
  ∑ t : ZMod Nt, asymSliceObsTrunc (g t) K (ψ t)

/-- The absolute-value dominator used for dominated convergence. -/
noncomputable def asymSliceFamilyAbsLinear
    (g : ZMod Nt → SpatialField Ns) (ψ : ZMod Nt → SpatialField Ns) : ℝ :=
  ∑ t : ZMod Nt, |asymSliceObsLinear (g t) (ψ t)|

theorem asymSliceFamilyLinear_eq_slicePairing
    (g : ZMod Nt → SpatialField Ns) (ψ : ZMod Nt → SpatialField Ns) :
    asymSliceFamilyLinear g ψ =
      slicePairing Nt Ns ((asymSliceEquiv Nt Ns).symm g) ψ := by
  unfold asymSliceFamilyLinear slicePairing asymSliceObsLinear
  refine Finset.sum_congr rfl (fun t _ => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h := congrFun (congrFun ((asymSliceEquiv Nt Ns).apply_symm_apply g) t) i
  rw [h]

theorem asymSliceFamilyLinear_measurable (g : ZMod Nt → SpatialField Ns) :
    Measurable (asymSliceFamilyLinear (Nt := Nt) (Ns := Ns) g) := by
  rw [show asymSliceFamilyLinear g =
      slicePairing Nt Ns ((asymSliceEquiv Nt Ns).symm g) by
        funext ψ; exact asymSliceFamilyLinear_eq_slicePairing g ψ]
  exact slicePairing_measurable Nt Ns ((asymSliceEquiv Nt Ns).symm g)

omit [NeZero Ns] in
theorem asymSliceFamilyTrunc_measurable (g : ZMod Nt → SpatialField Ns) (K : ℝ) :
    Measurable (asymSliceFamilyTrunc (Nt := Nt) (Ns := Ns) g K) := by
  unfold asymSliceFamilyTrunc
  refine Finset.measurable_sum _ (fun t _ => ?_)
  exact (asymSliceObsTrunc_measurable (g t) K).comp (measurable_pi_apply t)

/-! ## Pointwise truncation limit -/

omit [NeZero Nt] [NeZero Ns] in
/-- Pointwise convergence of the scalar truncated slice observable as `K → ∞`. -/
theorem asymSliceObsTrunc_tendsto_linear (g : SpatialField Ns) (ψ : SpatialField Ns) :
    Tendsto (fun K : ℝ => asymSliceObsTrunc g K ψ) atTop
      (𝓝 (asymSliceObsLinear g ψ)) := by
  set x := asymSliceObsLinear g ψ
  have hev : (fun K : ℝ => asymSliceObsTrunc g K ψ) =ᶠ[atTop] fun _ => x := by
    filter_upwards [eventually_ge_atTop |x|] with K hK
    have hx_hi : x ≤ K := (le_abs_self x).trans hK
    have hx_lo : -K ≤ x := by linarith [neg_abs_le x]
    simp [asymSliceObsTrunc, x, min_eq_right hx_hi, max_eq_right hx_lo]
  exact tendsto_const_nhds.congr' hev.symm

omit [NeZero Ns] in
theorem asymSliceFamilyTrunc_tendsto_linear
    (g : ZMod Nt → SpatialField Ns) (ψ : ZMod Nt → SpatialField Ns) :
    Tendsto (fun K : ℝ => asymSliceFamilyTrunc g K ψ) atTop
      (𝓝 (asymSliceFamilyLinear g ψ)) := by
  unfold asymSliceFamilyTrunc asymSliceFamilyLinear
  apply tendsto_finsetSum
  intro t _
  exact asymSliceObsTrunc_tendsto_linear (g t) (ψ t)

/-! ## Integrability of the DCT dominator -/

/-- Squared lattice pairings are integrable under the interacting asym lattice measure. -/
theorem asymInteractingLattice_pairing_sq_integrable
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : AsymLatticeField Nt Ns) :
    Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) => (ω g) ^ 2)
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) := by
  set μG := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  set bw := boltzmannWeightAsym Nt Ns P a mass
  obtain ⟨B, hB⟩ := interactionFunctionalAsym_bounded_below Nt Ns P a mass ha hmass
  have hZ := partitionFunctionAsym_pos Nt Ns P a mass ha hmass
  suffices h :
      Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) => (ω g) ^ 2)
        (μG.withDensity (fun ω => ENNReal.ofReal (bw ω))) by
    unfold interactingLatticeMeasureAsym
    exact h.smul_measure (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ).ne'))
  have hdens_meas : Measurable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      ENNReal.ofReal (bw ω)) :=
    ENNReal.measurable_ofReal.comp
      ((interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp)
  apply (integrable_withDensity_iff hdens_meas
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  have hbw_toReal : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      (ENNReal.ofReal (bw ω)).toReal = bw ω :=
    fun ω => ENNReal.toReal_ofReal (le_of_lt (boltzmannWeightAsym_pos Nt Ns P a mass ω))
  simp_rw [hbw_toReal]
  have h_sq_G : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) => (ω g) ^ 2) μG :=
    (pairing_memLp (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) g 2).integrable_sq
  apply (h_sq_G.mul_const (Real.exp B)).mono
  · exact ((configuration_eval_measurable g).pow_const 2).aestronglyMeasurable.mul
      ((interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp.aestronglyMeasurable)
  · refine Filter.Eventually.of_forall fun ω => ?_
    simp only [Real.norm_eq_abs]
    have hsq : 0 ≤ (ω g) ^ 2 := sq_nonneg _
    have hbw_pos : 0 < bw ω := boltzmannWeightAsym_pos Nt Ns P a mass ω
    have hbw_le : bw ω ≤ Real.exp B := by
      change Real.exp (-(interactionFunctionalAsym Nt Ns P a mass ω)) ≤ Real.exp B
      exact Real.exp_le_exp_of_le (by linarith [hB ω])
    rw [abs_of_nonneg (mul_nonneg hsq hbw_pos.le),
      abs_of_nonneg (mul_nonneg hsq (Real.exp_pos B).le)]
    exact mul_le_mul_of_nonneg_left hbw_le hsq

/-- Path-measure square integrability of a linear time-family observable. -/
theorem asymSliceFamilyLinear_sq_integrable_pathMeasure
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : ZMod Nt → SpatialField Ns) :
    Integrable (fun ψ : ZMod Nt → SpatialField Ns => (asymSliceFamilyLinear g ψ) ^ 2)
      ((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) := by
  set μI := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  set hmap := asymSliceEquiv Nt Ns ∘ evalMapAsym Nt Ns
  have hmeas : AEMeasurable hmap μI :=
    ((measurePreserving_asymSliceEquiv Nt Ns).measurable.comp
      (measurable_evalMapAsym Nt Ns)).aemeasurable
  have hpush :
      μI.map hmap =
        (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt := by
    dsimp [hmap, μI]
    rw [← Measure.map_map (measurePreserving_asymSliceEquiv Nt Ns).measurable
      (measurable_evalMapAsym Nt Ns)]
    exact interactingLatticeMeasureAsym_slice_pushforward_eq_pathMeasure
      (Nt := Nt) (Ns := Ns) P a mass ha hmass
  rw [← hpush, integrable_map_measure
    (((asymSliceFamilyLinear_measurable g).pow_const 2).aestronglyMeasurable) hmeas]
  refine (asymInteractingLattice_pairing_sq_integrable
    (Nt := Nt) (Ns := Ns) P a mass ha hmass ((asymSliceEquiv Nt Ns).symm g)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
  change (ω ((asymSliceEquiv Nt Ns).symm g)) ^ 2 =
    (asymSliceFamilyLinear g (hmap ω)) ^ 2
  have hpair :
      asymSliceFamilyLinear g (hmap ω) = ω ((asymSliceEquiv Nt Ns).symm g) := by
    rw [asymSliceFamilyLinear_eq_slicePairing]
    dsimp [hmap]
    change slicePairing Nt Ns ((asymSliceEquiv Nt Ns).symm g)
        ((asymSliceEquiv Nt Ns) (evalMapAsym Nt Ns ω)) =
      ω ((asymSliceEquiv Nt Ns).symm g)
    exact (config_pairing_eq_slice Nt Ns ω ((asymSliceEquiv Nt Ns).symm g)).symm
  rw [hpair]

/-- The DCT dominator `(Σ_t |⟨g_t, ψ_t⟩|)^2` is integrable under the path measure. -/
theorem asymSliceObsLinear_sq_integrable_pathMeasure
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : ZMod Nt → SpatialField Ns) :
    Integrable (fun ψ : ZMod Nt → SpatialField Ns =>
        (asymSliceFamilyAbsLinear g ψ) ^ 2)
      ((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) := by
  set μ := (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt
  have hterm : ∀ t : ZMod Nt,
      Integrable (fun ψ : ZMod Nt → SpatialField Ns =>
        (asymSliceObsLinear (g t) (ψ t)) ^ 2) μ := by
    intro t
    let gt : ZMod Nt → SpatialField Ns := fun s => if s = t then g t else 0
    have hlin := asymSliceFamilyLinear_sq_integrable_pathMeasure
      (Nt := Nt) (Ns := Ns) P a mass ha hmass gt
    refine hlin.congr (Filter.Eventually.of_forall fun ψ => ?_)
    have hsum :
        asymSliceFamilyLinear gt ψ = asymSliceObsLinear (g t) (ψ t) := by
      unfold asymSliceFamilyLinear gt
      rw [Finset.sum_eq_single t]
      · simp
      · intro b _ hb
        simp [hb, asymSliceObsLinear]
      · intro ht
        exact absurd (Finset.mem_univ t) ht
    simp [hsum]
  have hsum_sq : Integrable (fun ψ : ZMod Nt → SpatialField Ns =>
      ∑ t : ZMod Nt, (asymSliceObsLinear (g t) (ψ t)) ^ 2) μ :=
    integrable_finsetSum _ (fun t _ => hterm t)
  have hsum_sq_scaled : Integrable (fun ψ : ZMod Nt → SpatialField Ns =>
      (Fintype.card (ZMod Nt) : ℝ) *
        ∑ t : ZMod Nt, (asymSliceObsLinear (g t) (ψ t)) ^ 2) μ :=
    hsum_sq.const_mul (Fintype.card (ZMod Nt) : ℝ)
  have hmeas : AEStronglyMeasurable (fun ψ : ZMod Nt → SpatialField Ns =>
      (asymSliceFamilyAbsLinear g ψ) ^ 2) μ :=
    ((Finset.measurable_sum _ (fun t _ =>
      ((asymSliceObsLinear_measurable (g t)).comp (measurable_pi_apply t)).abs)).pow_const 2
        |>.aestronglyMeasurable)
  refine hsum_sq_scaled.mono' hmeas ?_
  refine Filter.Eventually.of_forall fun ψ => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (s := (Finset.univ : Finset (ZMod Nt)))
    (f := fun _ : ZMod Nt => (1 : ℝ))
    (g := fun t : ZMod Nt => |asymSliceObsLinear (g t) (ψ t)|)
  have hcard : (∑ _t : ZMod Nt, (1 : ℝ) ^ 2) = (Fintype.card (ZMod Nt) : ℝ) := by
    simp
  have hsum_abs_sq :
      (∑ t : ZMod Nt, |asymSliceObsLinear (g t) (ψ t)|) ^ 2
        ≤ (Fintype.card (ZMod Nt) : ℝ) *
          ∑ t : ZMod Nt, |asymSliceObsLinear (g t) (ψ t)| ^ 2 := by
    simpa [hcard, mul_comm, mul_left_comm, mul_assoc] using hcs
  calc
    (asymSliceFamilyAbsLinear g ψ) ^ 2
        ≤ (Fintype.card (ZMod Nt) : ℝ) *
            ∑ t : ZMod Nt, |asymSliceObsLinear (g t) (ψ t)| ^ 2 := by
          simpa [asymSliceFamilyAbsLinear] using hsum_abs_sq
    _ = (Fintype.card (ZMod Nt) : ℝ) *
            ∑ t : ZMod Nt, (asymSliceObsLinear (g t) (ψ t)) ^ 2 := by
          simp

/-- B1, restated on the path-measure side for a linear time-family observable. -/
theorem asymSliceFamilyLinear_pathMeasure_second_moment_le_B1
    (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (a : ℝ) (ha : 0 < a)
    (hvolt : (Nt : ℝ) * a = Lt) (hvols : (Ns : ℝ) * a = Ls)
    (g : ZMod Nt → SpatialField Ns) :
    ∃ C : ℝ, 0 < C ∧
      ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt)
        ≤
      C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω ((asymSliceEquiv Nt Ns).symm g)) ^ 2
            ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    asymInteractingVariance_le_freeVariance_lattice (Lt := Lt) (Ls := Ls) P mass hmass
  refine ⟨C, hC_pos, ?_⟩
  set G : AsymLatticeField Nt Ns := (asymSliceEquiv Nt Ns).symm g
  have hpath :
      ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt)
        =
      ∫ ψ : ZMod Nt → SpatialField Ns, (slicePairing Nt Ns G ψ) ^ 2
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ψ => ?_)
    simp [G, asymSliceFamilyLinear_eq_slicePairing]
  rw [hpath]
  rw [← asym_interacting_second_moment_eq_pathMeasure_slicePairing
    (Nt := Nt) (Ns := Ns) P a mass ha hmass G]
  simpa [G] using hC_bound Nt Ns a ha hvolt hvols G

/-! ## Dominated convergence and the K-uniform bound transfer -/

omit [NeZero Ns] in
private theorem asymSliceFamilyTrunc_sq_dominated
    (g : ZMod Nt → SpatialField Ns) :
    ∀ᶠ K : ℝ in atTop, ∀ ψ : ZMod Nt → SpatialField Ns,
      ‖(asymSliceFamilyTrunc g K ψ) ^ 2‖ ≤
        (asymSliceFamilyAbsLinear g ψ) ^ 2 := by
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with K hK ψ
  have habs :
      |asymSliceFamilyTrunc g K ψ| ≤ asymSliceFamilyAbsLinear g ψ := by
    calc
      |asymSliceFamilyTrunc g K ψ|
          ≤ ∑ t : ZMod Nt, |asymSliceObsTrunc (g t) K (ψ t)| := by
            unfold asymSliceFamilyTrunc
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ t : ZMod Nt, |asymSliceObsLinear (g t) (ψ t)| := by
            exact Finset.sum_le_sum fun t _ =>
              asymSliceObsTrunc_abs_le_linear (g t) hK (ψ t)
      _ = asymSliceFamilyAbsLinear g ψ := rfl
  have hdom_nonneg : 0 ≤ asymSliceFamilyAbsLinear g ψ :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  rw [Real.norm_eq_abs, abs_sq]
  rwa [sq_le_sq, abs_of_nonneg hdom_nonneg]

/-- Dominated convergence removes the common truncation from the squared time-sum observable. -/
theorem asymSliceFamilyTrunc_sq_integral_tendsto_linear
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : ZMod Nt → SpatialField Ns) :
    Tendsto
      (fun K : ℝ =>
        ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyTrunc g K ψ) ^ 2
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt))
      atTop
      (𝓝 (∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
          ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt))) := by
  set μ := (asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt
  refine tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (fun ψ => (asymSliceFamilyAbsLinear g ψ) ^ 2) ?_ ?_
    (asymSliceObsLinear_sq_integrable_pathMeasure
      (Nt := Nt) (Ns := Ns) P a mass ha hmass g) ?_
  · filter_upwards with K
    exact ((asymSliceFamilyTrunc_measurable g K).pow_const 2).aestronglyMeasurable
  · filter_upwards [asymSliceFamilyTrunc_sq_dominated (Nt := Nt) (Ns := Ns) g] with K hK
    exact Filter.Eventually.of_forall (hK)
  · refine Filter.Eventually.of_forall fun ψ => ?_
    exact (asymSliceFamilyTrunc_tendsto_linear g ψ).pow 2

/-- If a finite-`K` path-measure square bound is uniform in `K`, then the same bound holds
for the untruncated linear time-family observable. -/
theorem asymSliceObsLinear_pathMeasure_two_point_bound
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (g : ZMod Nt → SpatialField Ns) (B : ℝ)
    (hK_bound : ∀ K : ℝ, 0 < K →
      ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyTrunc g K ψ) ^ 2
        ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) ≤ B) :
    ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
        ∂((asymTransferSystem (Nt := Nt) (Ns := Ns) P a mass ha hmass).pathMeasure Nt) ≤ B := by
  have htend := asymSliceFamilyTrunc_sq_integral_tendsto_linear
    (Nt := Nt) (Ns := Ns) P a mass ha hmass g
  refine le_of_tendsto htend ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with K hK
  exact hK_bound K hK

end Pphi2
