/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Standard-Gaussian chaos membership for the asym rough error

This is the `Z_Nt × Z_Ns` analogue of the square chaos-membership stack in
`RoughErrorBound.lean`. The port is dimension-symmetric: the only structural
divergences are the hard-coded two-dimensional lattice volume factor `a ^ 2`
and the rectangular mode/site indices `Fin Nt × Fin Ns`.
-/

import Pphi2.NelsonEstimate.AsymRoughErrorVariance
import Pphi2.NelsonEstimate.RoughErrorBound

noncomputable section

open GaussianField MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Pphi2

private abbrev asymCanonicalStdIndex (Nt Ns : ℕ) :=
  Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns))

/-- Fin-indexed standard-Gaussian coordinates for the asym canonical joint space. -/
noncomputable def asymCanonicalJointStdGaussianMeasurableEquiv
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    AsymCanonicalJoint Nt Ns ≃ᵐ
      (Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) → ℝ) :=
  ((MeasurableEquiv.sumPiEquivProdPi
      (fun _ : AsymCanonicalJointSumIndex Nt Ns => ℝ)).symm).trans
    (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) => ℝ)
      (Fintype.equivFin (AsymCanonicalJointSumIndex Nt Ns)))

/-- The asym canonical joint measure becomes the product standard Gaussian after sum encoding. -/
theorem asymCanonicalJointMeasure_map_sum_pi_gaussian
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    (asymCanonicalJointMeasure Nt Ns).map
        ((MeasurableEquiv.sumPiEquivProdPi
          (fun _ : AsymCanonicalJointSumIndex Nt Ns => ℝ)).symm) =
      Measure.pi
        (fun _ : AsymCanonicalJointSumIndex Nt Ns =>
          gaussianReal 0 1) := by
  simpa [asymCanonicalJointMeasure, AsymCanonicalJointSumIndex]
    using
      (measurePreserving_sumPiEquivProdPi_symm
        (fun _ : AsymCanonicalJointSumIndex Nt Ns =>
          (gaussianReal 0 1 : Measure ℝ))).map_eq

/-- The asym canonical joint measure becomes `stdGaussianFin` under the Fin-indexed equivalence. -/
theorem asymCanonicalJointMeasure_map_stdGaussian
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    (asymCanonicalJointMeasure Nt Ns).map
        (asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns) =
      GaussianHilbert.stdGaussianFin
        (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) := by
  unfold asymCanonicalJointStdGaussianMeasurableEquiv
  simp only [MeasurableEquiv.coe_trans]
  have h_map_map :
      Measure.map
          (⇑(MeasurableEquiv.piCongrLeft
            (fun _ : Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) => ℝ)
            (Fintype.equivFin (AsymCanonicalJointSumIndex Nt Ns))) ∘
            ⇑(MeasurableEquiv.sumPiEquivProdPi
              (fun _ : AsymCanonicalJointSumIndex Nt Ns => ℝ)).symm)
          (asymCanonicalJointMeasure Nt Ns) =
        Measure.map
          (MeasurableEquiv.piCongrLeft
            (fun _ : Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) => ℝ)
            (Fintype.equivFin (AsymCanonicalJointSumIndex Nt Ns)))
          ((asymCanonicalJointMeasure Nt Ns).map
            ((MeasurableEquiv.sumPiEquivProdPi
              (fun _ : AsymCanonicalJointSumIndex Nt Ns => ℝ)).symm)) := by
    simpa using
      (Measure.map_map
        (g := MeasurableEquiv.piCongrLeft
          (fun _ : Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) => ℝ)
          (Fintype.equivFin (AsymCanonicalJointSumIndex Nt Ns)))
        (f := (MeasurableEquiv.sumPiEquivProdPi
          (fun _ : AsymCanonicalJointSumIndex Nt Ns => ℝ)).symm)
        (μ := asymCanonicalJointMeasure Nt Ns)
        (MeasurableEquiv.piCongrLeft
          (fun _ : Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) => ℝ)
          (Fintype.equivFin (AsymCanonicalJointSumIndex Nt Ns))).measurable
        ((MeasurableEquiv.sumPiEquivProdPi
          (fun _ : AsymCanonicalJointSumIndex Nt Ns => ℝ)).symm.measurable)).symm
  rw [h_map_map, asymCanonicalJointMeasure_map_sum_pi_gaussian]
  simpa [GaussianHilbert.stdGaussianFin, AsymCanonicalJointSumIndex]
    using
      (measurePreserving_piCongrLeft
        (μ := fun _ : Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) =>
          (gaussianReal 0 1 : Measure ℝ))
        (α := fun _ : Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) => ℝ)
        (f := Fintype.equivFin (AsymCanonicalJointSumIndex Nt Ns))).map_eq

private def asymCanonicalStdInlIndex (Nt Ns : ℕ)
    (m : AsymCanonicalMode Nt Ns) : asymCanonicalStdIndex Nt Ns :=
  Fintype.equivFin (AsymCanonicalJointSumIndex Nt Ns) (Sum.inl m)

private def asymCanonicalStdInrIndex (Nt Ns : ℕ)
    (m : AsymCanonicalMode Nt Ns) : asymCanonicalStdIndex Nt Ns :=
  Fintype.equivFin (AsymCanonicalJointSumIndex Nt Ns) (Sum.inr m)

private def asymCanonicalJointMultiIndexOfPair (Nt Ns : ℕ)
    (αS αR : AsymCanonicalMode Nt Ns → ℕ) :
    asymCanonicalStdIndex Nt Ns → ℕ :=
  fun i => Sum.elim αS αR ((Fintype.equivFin (AsymCanonicalJointSumIndex Nt Ns)).symm i)

@[simp] private lemma asymCanonicalJointMultiIndexOfPair_inl
    (Nt Ns : ℕ) (αS αR : AsymCanonicalMode Nt Ns → ℕ)
    (m : AsymCanonicalMode Nt Ns) :
    asymCanonicalJointMultiIndexOfPair Nt Ns αS αR
        (asymCanonicalStdInlIndex Nt Ns m) = αS m := by
  unfold asymCanonicalJointMultiIndexOfPair asymCanonicalStdInlIndex
  simp

@[simp] private lemma asymCanonicalJointMultiIndexOfPair_inr
    (Nt Ns : ℕ) (αS αR : AsymCanonicalMode Nt Ns → ℕ)
    (m : AsymCanonicalMode Nt Ns) :
    asymCanonicalJointMultiIndexOfPair Nt Ns αS αR
        (asymCanonicalStdInrIndex Nt Ns m) = αR m := by
  unfold asymCanonicalJointMultiIndexOfPair asymCanonicalStdInrIndex
  simp

private lemma asymCanonicalJointMultiIndexOfPair_totalDegree
    (Nt Ns : ℕ) (αS αR : AsymCanonicalMode Nt Ns → ℕ) :
    GaussianHilbert.MultiIndex.totalDegree
        (asymCanonicalJointMultiIndexOfPair Nt Ns αS αR) =
      (∑ m : AsymCanonicalMode Nt Ns, αS m) +
        ∑ m : AsymCanonicalMode Nt Ns, αR m := by
  unfold GaussianHilbert.MultiIndex.totalDegree asymCanonicalJointMultiIndexOfPair
  simpa [Fintype.sum_sum_type] using
    (Equiv.sum_comp
      (Fintype.equivFin (AsymCanonicalJointSumIndex Nt Ns)).symm
      (fun s : AsymCanonicalJointSumIndex Nt Ns => Sum.elim αS αR s))

private lemma asymCanonicalJointMultiIndexOfPair_wick_prod
    (Nt Ns : ℕ) (αS αR : AsymCanonicalMode Nt Ns → ℕ)
    (ξ : asymCanonicalStdIndex Nt Ns → ℝ) :
    (∏ i : asymCanonicalStdIndex Nt Ns,
        wickMonomial
          (Sum.elim αS αR
            ((Fintype.equivFin (AsymCanonicalJointSumIndex Nt Ns)).symm i))
          1 (ξ i)) =
      (∏ m : AsymCanonicalMode Nt Ns,
        wickMonomial (αS m) 1
          (ξ (asymCanonicalStdInlIndex Nt Ns m))) *
      ∏ m : AsymCanonicalMode Nt Ns,
        wickMonomial (αR m) 1
          (ξ (asymCanonicalStdInrIndex Nt Ns m)) := by
  let f : AsymCanonicalJointSumIndex Nt Ns → ℝ :=
    fun s =>
      wickMonomial (Sum.elim αS αR s) 1
        (ξ (Fintype.equivFin (AsymCanonicalJointSumIndex Nt Ns) s))
  calc
    ∏ i : Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)),
        wickMonomial
          (Sum.elim αS αR
            ((Fintype.equivFin (AsymCanonicalJointSumIndex Nt Ns)).symm i))
          1 (ξ i)
      = ∏ s : AsymCanonicalJointSumIndex Nt Ns, f s := by
          simpa [f] using
            (Equiv.prod_comp
              (Fintype.equivFin (AsymCanonicalJointSumIndex Nt Ns)).symm
              (fun s : AsymCanonicalJointSumIndex Nt Ns =>
                wickMonomial (Sum.elim αS αR s) 1
                  (ξ (Fintype.equivFin (AsymCanonicalJointSumIndex Nt Ns) s))))
    _ = (∏ m : AsymCanonicalMode Nt Ns, f (Sum.inl m)) *
          ∏ m : AsymCanonicalMode Nt Ns, f (Sum.inr m) := by
            rw [show (∏ s : AsymCanonicalJointSumIndex Nt Ns,
                wickMonomial (Sum.elim αS αR s) 1
                  (ξ (Fintype.equivFin (AsymCanonicalJointSumIndex Nt Ns) s))) =
                  ∏ s : AsymCanonicalJointSumIndex Nt Ns, f s by
                  simp [f]]
            exact Fintype.prod_sum_type f
    _ = (∏ m : AsymCanonicalMode Nt Ns,
          wickMonomial (αS m) 1
            (ξ (asymCanonicalStdInlIndex Nt Ns m))) *
        ∏ m : AsymCanonicalMode Nt Ns,
          wickMonomial (αR m) 1
            (ξ (asymCanonicalStdInrIndex Nt Ns m)) := by
              simp [f, asymCanonicalStdInlIndex, asymCanonicalStdInrIndex]

@[simp] private lemma asymCanonicalJointStdGaussianMeasurableEquiv_symm_fst
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (ξ : asymCanonicalStdIndex Nt Ns → ℝ) (m : AsymCanonicalMode Nt Ns) :
    ((asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns).symm ξ).1 m =
      ξ (asymCanonicalStdInlIndex Nt Ns m) := by
  rfl

@[simp] private lemma asymCanonicalJointStdGaussianMeasurableEquiv_symm_snd
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (ξ : asymCanonicalStdIndex Nt Ns → ℝ) (m : AsymCanonicalMode Nt Ns) :
    ((asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns).symm ξ).2 m =
      ξ (asymCanonicalStdInrIndex Nt Ns m) := by
  rfl

private def asymCanonicalSiteCrossStd
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (x : AsymLatticeSites Nt Ns) (k j : ℕ)
    (ξ : asymCanonicalStdIndex Nt Ns → ℝ) : ℝ :=
  wickMonomial j (asymSmoothWickConstant Nt Ns a mass T)
      (asymCanonicalSmoothFieldFunction Nt Ns a mass T
        ((asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns).symm ξ) x) *
    wickMonomial (k - j) (asymCanonicalRoughWickConstant Nt Ns a mass T)
      (asymCanonicalRoughFieldFunction Nt Ns a mass T
        ((asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns).symm ξ) x)

private lemma asymCanonicalSmoothFieldFunction_std_eq_sum_gamma
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (x : AsymLatticeSites Nt Ns)
    (ξ : asymCanonicalStdIndex Nt Ns → ℝ) :
    asymCanonicalSmoothFieldFunction Nt Ns a mass T
        ((asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns).symm ξ) x =
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalSmoothGamma Nt Ns a mass T x m *
          ξ (asymCanonicalStdInlIndex Nt Ns m) := by
  simpa using
    (asymCanonicalSmoothFieldFunctionOfFst_eq_sum_gamma
      Nt Ns a mass T
      (((asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns).symm ξ).1) x)

private lemma asymCanonicalRoughFieldFunction_std_eq_sum_gamma
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (x : AsymLatticeSites Nt Ns)
    (ξ : asymCanonicalStdIndex Nt Ns → ℝ) :
    asymCanonicalRoughFieldFunction Nt Ns a mass T
        ((asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns).symm ξ) x =
      ∑ m : AsymCanonicalMode Nt Ns,
        asymCanonicalRoughGamma Nt Ns a mass T x m *
          ξ (asymCanonicalStdInrIndex Nt Ns m) := by
  simpa using
    (asymCanonicalRoughFieldFunctionOfSnd_eq_sum_gamma
      Nt Ns a mass T
      (((asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns).symm ξ).2) x)

private theorem asymCanonicalSiteCrossStd_mem_wienerChaosLE
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T)
    (x : AsymLatticeSites Nt Ns) (k j : ℕ) (hjk : j ≤ k) :
    ∃ hf : MeasureTheory.MemLp
        (asymCanonicalSiteCrossStd Nt Ns a mass T x k j) 2
        (GaussianHilbert.stdGaussianFin
          (Fintype.card (AsymCanonicalJointSumIndex Nt Ns))),
      (hf.toLp (asymCanonicalSiteCrossStd Nt Ns a mass T x k j)) ∈
        GaussianHilbert.wienerChaosLE
          (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) k := by
  classical
  let γS : AsymCanonicalMode Nt Ns → ℝ := asymCanonicalSmoothGamma Nt Ns a mass T x
  let γR : AsymCanonicalMode Nt Ns → ℝ := asymCanonicalRoughGamma Nt Ns a mass T x
  let sS := multiIndicesOfTotalDegree (AsymCanonicalMode Nt Ns) j
  let sR := multiIndicesOfTotalDegree (AsymCanonicalMode Nt Ns) (k - j)
  let β : (AsymCanonicalMode Nt Ns → ℕ) × (AsymCanonicalMode Nt Ns → ℕ) →
      asymCanonicalStdIndex Nt Ns → ℕ :=
    fun p => asymCanonicalJointMultiIndexOfPair Nt Ns p.1 p.2
  let c : (AsymCanonicalMode Nt Ns → ℕ) × (AsymCanonicalMode Nt Ns → ℕ) → ℝ :=
    fun p =>
      wickExpansionCoeff j γS p.1 *
        wickExpansionCoeff (k - j) γR p.2
  let f : (asymCanonicalStdIndex Nt Ns → ℝ) → ℝ :=
    asymCanonicalSiteCrossStd Nt Ns a mass T x k j
  let g : (asymCanonicalStdIndex Nt Ns → ℝ) → ℝ :=
    fun ξ => ∑ p ∈ sS.product sR, c p * ∏ i, wickMonomial (β p i) 1 (ξ i)
  have hf_def : f = g := by
    funext ξ
    unfold f g asymCanonicalSiteCrossStd c β wickExpansionCoeff
    rw [show asymSmoothWickConstant Nt Ns a mass T =
        ∑ m : AsymCanonicalMode Nt Ns, (γS m) ^ 2 from by
      simpa [γS] using
        (asymCanonicalSmoothGamma_sq_sum_eq_asymSmoothWickConstant
          Nt Ns a mass ha hmass T x).symm]
    rw [show asymCanonicalRoughWickConstant Nt Ns a mass T =
        ∑ m : AsymCanonicalMode Nt Ns, (γR m) ^ 2 from by
      simpa [γR] using
        (asymCanonicalRoughGamma_sq_sum_eq_asymCanonicalRoughWickConstant
          Nt Ns a mass ha hmass T hT x).symm]
    rw [asymCanonicalSmoothFieldFunction_std_eq_sum_gamma
      Nt Ns a mass T x ξ]
    rw [asymCanonicalRoughFieldFunction_std_eq_sum_gamma
      Nt Ns a mass T x ξ]
    rw [show
      wickMonomial j (∑ m : AsymCanonicalMode Nt Ns, (γS m) ^ 2)
          (∑ m : AsymCanonicalMode Nt Ns, asymCanonicalSmoothGamma Nt Ns a mass T x m *
            ξ (asymCanonicalStdInlIndex Nt Ns m)) =
        ∑ α ∈ sS,
          wickExpansionCoeff j γS α *
            ∏ m : AsymCanonicalMode Nt Ns,
              wickMonomial (α m) 1 (ξ (asymCanonicalStdInlIndex Nt Ns m)) from by
              simpa [γS, wickMonomial_eq_root_local] using
                (wickMonomial_pow_sum_expansion_of_totalDegree
                  (γ := γS)
                  (ξ := fun m => ξ (asymCanonicalStdInlIndex Nt Ns m)) (k := j))]
    rw [show
      wickMonomial (k - j) (∑ m : AsymCanonicalMode Nt Ns, (γR m) ^ 2)
          (∑ m : AsymCanonicalMode Nt Ns, asymCanonicalRoughGamma Nt Ns a mass T x m *
            ξ (asymCanonicalStdInrIndex Nt Ns m)) =
        ∑ α ∈ sR,
          wickExpansionCoeff (k - j) γR α *
            ∏ m : AsymCanonicalMode Nt Ns,
              wickMonomial (α m) 1 (ξ (asymCanonicalStdInrIndex Nt Ns m)) from by
              simpa [γR, wickMonomial_eq_root_local] using
                (wickMonomial_pow_sum_expansion_of_totalDegree
                  (γ := γR)
                  (ξ := fun m => ξ (asymCanonicalStdInrIndex Nt Ns m)) (k := k - j))]
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr rfl ?_
    intro p hp
    rcases p with ⟨αS, αR⟩
    calc
      (wickExpansionCoeff j γS αS *
          ∏ m, wickMonomial (αS m) 1 (ξ (asymCanonicalStdInlIndex Nt Ns m))) *
          (wickExpansionCoeff (k - j) γR αR *
            ∏ m, wickMonomial (αR m) 1 (ξ (asymCanonicalStdInrIndex Nt Ns m)))
        =
          (wickExpansionCoeff j γS αS * wickExpansionCoeff (k - j) γR αR) *
            ((∏ m, wickMonomial (αS m) 1 (ξ (asymCanonicalStdInlIndex Nt Ns m))) *
              ∏ m, wickMonomial (αR m) 1 (ξ (asymCanonicalStdInrIndex Nt Ns m))) := by
                ring
      _ =
          (wickExpansionCoeff j γS αS * wickExpansionCoeff (k - j) γR αR) *
            ∏ i, wickMonomial (asymCanonicalJointMultiIndexOfPair Nt Ns αS αR i)
              1 (ξ i) := by
              simpa [asymCanonicalJointMultiIndexOfPair] using
                (congrArg
                  (fun z =>
                    (wickExpansionCoeff j γS αS * wickExpansionCoeff (k - j) γR αR) * z)
                  (asymCanonicalJointMultiIndexOfPair_wick_prod
                    Nt Ns αS αR ξ).symm)
      _ = ((↑j.factorial / ∏ j, ↑(αS j).factorial) * ∏ j, γS j ^ αS j) *
            ((↑(k - j).factorial / ∏ j, ↑(αR j).factorial) * ∏ j, γR j ^ αR j) *
              ∏ i, wickMonomial (asymCanonicalJointMultiIndexOfPair Nt Ns αS αR i)
                1 (ξ i) := by
                unfold wickExpansionCoeff
                ring
  have hg_memLp : MeasureTheory.MemLp g 2
      (GaussianHilbert.stdGaussianFin
        (Fintype.card (AsymCanonicalJointSumIndex Nt Ns))) := by
    refine memLp_finset_sum (sS.product sR) ?_
    intro p hp
    have h_term :
        MeasureTheory.MemLp
          (fun ξ : asymCanonicalStdIndex Nt Ns → ℝ =>
            c p * ∏ i, wickMonomial (β p i) 1 (ξ i))
          2
          (GaussianHilbert.stdGaussianFin
            (Fintype.card (AsymCanonicalJointSumIndex Nt Ns))) := by
      have h_eq :
          (fun ξ : asymCanonicalStdIndex Nt Ns → ℝ =>
            c p * ∏ i, wickMonomial (β p i) 1 (ξ i)) =
          fun ξ => c p * GaussianHilbert.hermiteMultiEval (β p) ξ := by
        funext ξ
        rw [multiWickMonomial_eq_hermiteMultiEval (β p) ξ]
      rw [h_eq]
      exact (GaussianHilbert.hermiteMultiEval_memLp (β p)).const_mul (c p)
    exact h_term
  let hf : MeasureTheory.MemLp
      (asymCanonicalSiteCrossStd Nt Ns a mass T x k j) 2
      (GaussianHilbert.stdGaussianFin
        (Fintype.card (AsymCanonicalJointSumIndex Nt Ns))) := by
          simpa [f, g, hf_def] using hg_memLp
  refine ⟨hf, ?_⟩
  refine finite_indexed_wick_sum_mem_wienerChaosLE
    (s := sS.product sR) β c ?_
    (asymCanonicalSiteCrossStd Nt Ns a mass T x k j)
    (by simpa [f, g] using hf_def)
    hf
  intro p hp
  rcases Finset.mem_product.mp hp with ⟨hpS, hpR⟩
  have hpSdeg : ∑ m : AsymCanonicalMode Nt Ns, p.1 m = j := by
    have hpS' :
        (∀ a : AsymCanonicalMode Nt Ns, p.1 a ≤ j) ∧
          ∑ a : AsymCanonicalMode Nt Ns, p.1 a = j := by
      simpa [sS, multiIndicesOfTotalDegree] using hpS
    exact hpS'.2
  have hpRdeg : ∑ m : AsymCanonicalMode Nt Ns, p.2 m = k - j := by
    have hpR' :
        (∀ a : AsymCanonicalMode Nt Ns, p.2 a ≤ k - j) ∧
          ∑ a : AsymCanonicalMode Nt Ns, p.2 a = k - j := by
      simpa [sR, multiIndicesOfTotalDegree] using hpR
    exact hpR'.2
  calc
    GaussianHilbert.MultiIndex.totalDegree (β p)
        = (∑ m : AsymCanonicalMode Nt Ns, p.1 m) +
            ∑ m : AsymCanonicalMode Nt Ns, p.2 m := by
              simpa [GaussianHilbert.MultiIndex.totalDegree] using
                asymCanonicalJointMultiIndexOfPair_totalDegree Nt Ns p.1 p.2
    _ = j + (k - j) := by rw [hpSdeg, hpRdeg]
    _ ≤ k := by
          exact le_of_eq (Nat.add_sub_of_le hjk)

/-- Standard-Gaussian representative of a single asym rough cross-term. -/
def asymCanonicalCrossTermStd
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (k j : ℕ)
    (ξ : Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) → ℝ) : ℝ :=
  a ^ 2 * ∑ x : AsymLatticeSites Nt Ns,
    asymCanonicalSiteCrossStd Nt Ns a mass T x k j ξ

@[simp] theorem asymCanonicalCrossTermStd_eq
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (η : AsymCanonicalJoint Nt Ns) (k j : ℕ) :
    asymCanonicalCrossTermStd Nt Ns a mass T k j
        (asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns η) =
      asymCanonicalCrossTerm Nt Ns a mass T η k j := by
  unfold asymCanonicalCrossTermStd asymCanonicalCrossTerm asymCanonicalSiteCrossStd
  simp

/-- A standard-coordinate asym cross-term lies in chaos degree at most `k`. -/
theorem asymCanonicalCrossTermStd_mem_wienerChaosLE
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T)
    (k j : ℕ) (hjk : j ≤ k) :
    ∃ hf : MeasureTheory.MemLp
        (asymCanonicalCrossTermStd Nt Ns a mass T k j) 2
        (GaussianHilbert.stdGaussianFin
          (Fintype.card (AsymCanonicalJointSumIndex Nt Ns))),
      (hf.toLp (asymCanonicalCrossTermStd Nt Ns a mass T k j)) ∈
        GaussianHilbert.wienerChaosLE
          (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) k := by
  classical
  let μ := GaussianHilbert.stdGaussianFin
    (Fintype.card (AsymCanonicalJointSumIndex Nt Ns))
  let hfSite :
      ∀ x : AsymLatticeSites Nt Ns,
        MeasureTheory.MemLp
          (fun ξ : asymCanonicalStdIndex Nt Ns → ℝ =>
            asymCanonicalSiteCrossStd Nt Ns a mass T x k j ξ) 2 μ :=
    fun x =>
      Classical.choose <|
        asymCanonicalSiteCrossStd_mem_wienerChaosLE
          Nt Ns a mass ha hmass T hT x k j hjk
  have hfSite_spec :
      ∀ x : AsymLatticeSites Nt Ns,
        ((hfSite x).toLp
          (fun ξ : asymCanonicalStdIndex Nt Ns → ℝ =>
            asymCanonicalSiteCrossStd Nt Ns a mass T x k j ξ)) ∈
          GaussianHilbert.wienerChaosLE
            (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) k := by
    intro x
    exact
      Classical.choose_spec <|
        asymCanonicalSiteCrossStd_mem_wienerChaosLE
          Nt Ns a mass ha hmass T hT x k j hjk
  have hsum_memLp :
      MeasureTheory.MemLp
        (fun ξ : asymCanonicalStdIndex Nt Ns → ℝ =>
          ∑ x : AsymLatticeSites Nt Ns, asymCanonicalSiteCrossStd Nt Ns a mass T x k j ξ)
        2 μ := by
    refine memLp_finset_sum Finset.univ ?_
    intro x hx
    simpa using hfSite x
  let hf : MeasureTheory.MemLp
      (asymCanonicalCrossTermStd Nt Ns a mass T k j) 2 μ := by
        simpa [asymCanonicalCrossTermStd] using hsum_memLp.const_mul (a ^ 2)
  refine ⟨hf, ?_⟩
  have h_toLp :
      hf.toLp (asymCanonicalCrossTermStd Nt Ns a mass T k j) =
        (a ^ 2) • ∑ x : AsymLatticeSites Nt Ns,
          (hfSite x).toLp
            (fun ξ : asymCanonicalStdIndex Nt Ns → ℝ =>
              asymCanonicalSiteCrossStd Nt Ns a mass T x k j ξ) := by
    apply MeasureTheory.Lp.ext
    refine (MemLp.coeFn_toLp hf).trans ?_
    symm
    refine (MeasureTheory.Lp.coeFn_smul (a ^ 2)
      (∑ x : AsymLatticeSites Nt Ns,
        (hfSite x).toLp
          (fun ξ : asymCanonicalStdIndex Nt Ns → ℝ =>
            asymCanonicalSiteCrossStd Nt Ns a mass T x k j ξ))).trans ?_
    have hsum_coe :
        (((∑ x : AsymLatticeSites Nt Ns,
            (hfSite x).toLp
              (fun ξ : asymCanonicalStdIndex Nt Ns → ℝ =>
                asymCanonicalSiteCrossStd Nt Ns a mass T x k j ξ) :
              MeasureTheory.Lp ℝ 2 μ) :
          (asymCanonicalStdIndex Nt Ns → ℝ) → ℝ)) =ᵐ[μ]
            ∑ x : AsymLatticeSites Nt Ns,
              (((hfSite x).toLp
                (fun ξ : asymCanonicalStdIndex Nt Ns → ℝ =>
                  asymCanonicalSiteCrossStd Nt Ns a mass T x k j ξ) :
                  MeasureTheory.Lp ℝ 2 μ) :
                (asymCanonicalStdIndex Nt Ns → ℝ) → ℝ) :=
      MeasureTheory.Lp.coeFn_finset_sum Finset.univ
        (fun x =>
          (hfSite x).toLp
            (fun ξ : asymCanonicalStdIndex Nt Ns → ℝ =>
              asymCanonicalSiteCrossStd Nt Ns a mass T x k j ξ))
    have h_each :
        ∀ x ∈ ((Finset.univ : Finset (AsymLatticeSites Nt Ns)) : Set (AsymLatticeSites Nt Ns)),
          ∀ᵐ ξ ∂μ,
            (((hfSite x).toLp
              (fun ξ : asymCanonicalStdIndex Nt Ns → ℝ =>
                asymCanonicalSiteCrossStd Nt Ns a mass T x k j ξ) :
                MeasureTheory.Lp ℝ 2 μ) :
              (asymCanonicalStdIndex Nt Ns → ℝ) → ℝ) ξ =
              asymCanonicalSiteCrossStd Nt Ns a mass T x k j ξ := by
      intro x _
      exact MemLp.coeFn_toLp (hfSite x)
    have h_ae_all :
        ∀ᵐ ξ ∂μ,
          ∀ x ∈ ((Finset.univ : Finset (AsymLatticeSites Nt Ns)) :
              Set (AsymLatticeSites Nt Ns)),
            (((hfSite x).toLp
              (fun ξ : asymCanonicalStdIndex Nt Ns → ℝ =>
                asymCanonicalSiteCrossStd Nt Ns a mass T x k j ξ) :
                MeasureTheory.Lp ℝ 2 μ) :
              (asymCanonicalStdIndex Nt Ns → ℝ) → ℝ) ξ =
              asymCanonicalSiteCrossStd Nt Ns a mass T x k j ξ :=
      (ae_ball_iff (Finset.univ : Finset (AsymLatticeSites Nt Ns)).countable_toSet).mpr
        h_each
    filter_upwards [hsum_coe, h_ae_all] with ξ hsumξ hξ
    rw [Pi.smul_apply, hsumξ, Finset.sum_apply, asymCanonicalCrossTermStd]
    congr 1
    exact Finset.sum_congr rfl fun x hx =>
      hξ x (Finset.mem_coe.mpr hx)
  rw [h_toLp]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro x hx
  exact hfSite_spec x

/-- Finite linear combinations of fixed-degree asym cross-terms stay in a higher chaos cutoff. -/
theorem asymCanonicalCrossTermLinearCombo_mem_wienerChaosLE
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T)
    (k l : ℕ) (hkl : k ≤ l) (c : ℕ → ℝ) :
    ∃ hf : MeasureTheory.MemLp
        (fun ξ : asymCanonicalStdIndex Nt Ns → ℝ =>
          ∑ j ∈ Finset.range k, c j * asymCanonicalCrossTermStd Nt Ns a mass T k j ξ)
        2
        (GaussianHilbert.stdGaussianFin
          (Fintype.card (AsymCanonicalJointSumIndex Nt Ns))),
      (hf.toLp
        (fun ξ : asymCanonicalStdIndex Nt Ns → ℝ =>
          ∑ j ∈ Finset.range k, c j * asymCanonicalCrossTermStd Nt Ns a mass T k j ξ)) ∈
        GaussianHilbert.wienerChaosLE
          (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) l := by
  classical
  let μ := GaussianHilbert.stdGaussianFin
    (Fintype.card (AsymCanonicalJointSumIndex Nt Ns))
  let F : ℕ → MeasureTheory.Lp ℝ 2 μ := fun j =>
    if hj : j ∈ Finset.range k then
      let hfj :=
        Classical.choose <|
          asymCanonicalCrossTermStd_mem_wienerChaosLE
            Nt Ns a mass ha hmass T hT k j (Nat.le_of_lt (Finset.mem_range.mp hj))
      hfj.toLp (asymCanonicalCrossTermStd Nt Ns a mass T k j)
    else 0
  have hmemLp :
      MeasureTheory.MemLp
        (fun ξ : asymCanonicalStdIndex Nt Ns → ℝ =>
          ∑ j ∈ Finset.range k, c j * asymCanonicalCrossTermStd Nt Ns a mass T k j ξ)
        2 μ := by
    refine memLp_finset_sum (Finset.range k) ?_
    intro j hj
    let hfj :=
      Classical.choose <|
        asymCanonicalCrossTermStd_mem_wienerChaosLE
          Nt Ns a mass ha hmass T hT k j (Nat.le_of_lt (Finset.mem_range.mp hj))
    simpa using (hfj.const_mul (c j))
  refine ⟨hmemLp, ?_⟩
  have h_toLp :
      hmemLp.toLp
        (fun ξ : asymCanonicalStdIndex Nt Ns → ℝ =>
          ∑ j ∈ Finset.range k, c j * asymCanonicalCrossTermStd Nt Ns a mass T k j ξ) =
        ∑ j ∈ Finset.range k, c j • F j := by
    apply MeasureTheory.Lp.ext
    refine (MemLp.coeFn_toLp hmemLp).trans ?_
    symm
    have hsum_coe :
        (((∑ j ∈ Finset.range k, c j • F j : MeasureTheory.Lp ℝ 2 μ) :
          (asymCanonicalStdIndex Nt Ns → ℝ) → ℝ)) =ᵐ[μ]
            ∑ j ∈ Finset.range k,
              (((c j • F j : MeasureTheory.Lp ℝ 2 μ) :
                (asymCanonicalStdIndex Nt Ns → ℝ) → ℝ)) :=
      MeasureTheory.Lp.coeFn_finset_sum (Finset.range k) (fun j => c j • F j)
    have h_each :
        ∀ j ∈ ((Finset.range k : Finset ℕ) : Set ℕ),
          ∀ᵐ ξ ∂μ,
            (((c j • F j : MeasureTheory.Lp ℝ 2 μ) :
              (asymCanonicalStdIndex Nt Ns → ℝ) → ℝ) ξ) =
              c j * asymCanonicalCrossTermStd Nt Ns a mass T k j ξ := by
      intro j hjset
      have hj : j ∈ Finset.range k := Finset.mem_coe.mp hjset
      dsimp [F]
      simp only [hj, ↓reduceDIte]
      let hfj :=
        Classical.choose <|
          asymCanonicalCrossTermStd_mem_wienerChaosLE
            Nt Ns a mass ha hmass T hT k j (Nat.le_of_lt (Finset.mem_range.mp hj))
      refine (MeasureTheory.Lp.coeFn_smul (c j)
        (hfj.toLp (asymCanonicalCrossTermStd Nt Ns a mass T k j))).trans ?_
      filter_upwards [MemLp.coeFn_toLp hfj] with ξ hξ
      simp [hξ, smul_eq_mul]
    have h_ae_all :
        ∀ᵐ ξ ∂μ,
          ∀ j ∈ ((Finset.range k : Finset ℕ) : Set ℕ),
            (((c j • F j : MeasureTheory.Lp ℝ 2 μ) :
              (asymCanonicalStdIndex Nt Ns → ℝ) → ℝ) ξ) =
              c j * asymCanonicalCrossTermStd Nt Ns a mass T k j ξ :=
      (ae_ball_iff (Finset.range k).countable_toSet).mpr h_each
    refine hsum_coe.trans ?_
    filter_upwards [h_ae_all] with ξ hξ
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun j hj =>
      hξ j (Finset.mem_coe.mpr hj)
  rw [h_toLp]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  have hmemk :
      F j ∈ GaussianHilbert.wienerChaosLE
        (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) k := by
    dsimp [F]
    simp only [hj, ↓reduceDIte]
    exact Classical.choose_spec <|
      asymCanonicalCrossTermStd_mem_wienerChaosLE
        Nt Ns a mass ha hmass T hT k j (Nat.le_of_lt (Finset.mem_range.mp hj))
  exact wienerChaosLE_mono (n := Fintype.card (AsymCanonicalJointSumIndex Nt Ns))
    hkl hmemk

/-- Standard-Gaussian representative of the full asym canonical rough error. -/
def asymCanonicalRoughErrorStd
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (P : InteractionPolynomial)
    (ξ : Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) → ℝ) : ℝ :=
  (1 / P.n : ℝ) * ∑ j ∈ Finset.range P.n,
      (P.n.choose j : ℝ) * asymCanonicalCrossTermStd Nt Ns a mass T P.n j ξ
  + ∑ m : Fin P.n, P.coeff m *
      ∑ j ∈ Finset.range (m : ℕ),
        ((m : ℕ).choose j : ℝ) *
          asymCanonicalCrossTermStd Nt Ns a mass T (m : ℕ) j ξ

@[simp] theorem asymCanonicalRoughErrorStd_eq
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass T : ℝ) (P : InteractionPolynomial) (η : AsymCanonicalJoint Nt Ns) :
    asymCanonicalRoughErrorStd Nt Ns a mass T P
        (asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns η) =
      asymCanonicalRoughError Nt Ns a mass T P η := by
  rw [asymCanonicalRoughError_eq_sum_over_cross_terms Nt Ns a mass T P η]
  unfold asymCanonicalRoughErrorStd
  refine congr_arg₂ (· + ·) ?_ ?_
  · simp only [asymCanonicalCrossTermStd_eq]
  · refine Finset.sum_congr rfl ?_
    intro m hm
    simp only [asymCanonicalCrossTermStd_eq]

/-- The standard-coordinate asym rough error lies in chaos degree at most `P.n`. -/
theorem asymCanonicalRoughErrorStd_mem_wienerChaosLE
    (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (T : ℝ) (hT : 0 < T)
    (P : InteractionPolynomial) :
    ∃ hf : MeasureTheory.MemLp
        (asymCanonicalRoughErrorStd Nt Ns a mass T P) 2
        (GaussianHilbert.stdGaussianFin
          (Fintype.card (AsymCanonicalJointSumIndex Nt Ns))),
      (hf.toLp (asymCanonicalRoughErrorStd Nt Ns a mass T P)) ∈
        GaussianHilbert.wienerChaosLE
          (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) P.n := by
  classical
  let μ := GaussianHilbert.stdGaussianFin
    (Fintype.card (AsymCanonicalJointSumIndex Nt Ns))
  let leadSum : (Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) → ℝ) → ℝ := fun ξ =>
    ∑ j ∈ Finset.range P.n,
      (P.n.choose j : ℝ) * asymCanonicalCrossTermStd Nt Ns a mass T P.n j ξ
  let lead : (Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) → ℝ) → ℝ := fun ξ =>
    (1 / P.n : ℝ) • leadSum ξ
  obtain ⟨hfLeadSum, hLeadSumChaos⟩ :=
    asymCanonicalCrossTermLinearCombo_mem_wienerChaosLE
      Nt Ns a mass ha hmass T hT P.n P.n le_rfl (fun j => (P.n.choose j : ℝ))
  let hfLead : MeasureTheory.MemLp lead 2 μ := hfLeadSum.const_smul (1 / P.n : ℝ)
  have hLeadChaos :
      (hfLead.toLp lead) ∈
        GaussianHilbert.wienerChaosLE
          (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) P.n := by
    have hLead_toLp :
        hfLead.toLp lead =
          (1 / P.n : ℝ) • hfLeadSum.toLp leadSum := by
      simpa [lead, leadSum] using
        (MeasureTheory.MemLp.toLp_const_smul (1 / P.n : ℝ) hfLeadSum)
    rw [hLead_toLp]
    exact Submodule.smul_mem _ _ hLeadSumChaos
  let perInner : Fin P.n →
      ((Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) → ℝ) → ℝ) := fun m ξ =>
    ∑ j ∈ Finset.range (m : ℕ),
      ((m : ℕ).choose j : ℝ) *
        asymCanonicalCrossTermStd Nt Ns a mass T (m : ℕ) j ξ
  let per : (Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) → ℝ) → ℝ := fun ξ =>
    ∑ m : Fin P.n, P.coeff m * perInner m ξ
  have hPerInner :
      ∀ m : Fin P.n,
        ∃ hf : MeasureTheory.MemLp (perInner m) 2 μ,
          (hf.toLp (perInner m)) ∈
            GaussianHilbert.wienerChaosLE
              (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) P.n := by
    intro m
    exact asymCanonicalCrossTermLinearCombo_mem_wienerChaosLE
      Nt Ns a mass ha hmass T hT (m : ℕ) P.n (Nat.le_of_lt m.2)
      (fun j => ((m : ℕ).choose j : ℝ))
  let hfPerInner : ∀ m : Fin P.n, MeasureTheory.MemLp (perInner m) 2 μ :=
    fun m => (hPerInner m).choose
  have hPerInnerChaos :
      ∀ m : Fin P.n,
        ((hfPerInner m).toLp (perInner m)) ∈
          GaussianHilbert.wienerChaosLE
            (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) P.n := by
    intro m
    exact (hPerInner m).choose_spec
  have hfPer : MeasureTheory.MemLp per 2 μ := by
    refine memLp_finset_sum Finset.univ ?_
    intro m hm
    simpa [perInner] using (hfPerInner m).const_mul (P.coeff m)
  have hPerChaos :
      (hfPer.toLp per) ∈
        GaussianHilbert.wienerChaosLE
          (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) P.n := by
    have hPer_toLp :
        hfPer.toLp per =
          ∑ m : Fin P.n, P.coeff m • (hfPerInner m).toLp (perInner m) := by
      apply MeasureTheory.Lp.ext
      refine (MemLp.coeFn_toLp hfPer).trans ?_
      symm
      have hsum_coe :
          (((∑ m : Fin P.n, P.coeff m • (hfPerInner m).toLp (perInner m) :
              MeasureTheory.Lp ℝ 2 μ) :
            (asymCanonicalStdIndex Nt Ns → ℝ) → ℝ)) =ᵐ[μ]
              ∑ m : Fin P.n,
                (((P.coeff m • (hfPerInner m).toLp (perInner m) :
                    MeasureTheory.Lp ℝ 2 μ) :
                  (asymCanonicalStdIndex Nt Ns → ℝ) → ℝ)) :=
        MeasureTheory.Lp.coeFn_finset_sum Finset.univ
          (fun m => P.coeff m • (hfPerInner m).toLp (perInner m))
      have h_each :
          ∀ m ∈ ((Finset.univ : Finset (Fin P.n)) : Set (Fin P.n)),
            ∀ᵐ ξ ∂μ,
              (((P.coeff m • (hfPerInner m).toLp (perInner m) :
                  MeasureTheory.Lp ℝ 2 μ) :
                (asymCanonicalStdIndex Nt Ns → ℝ) → ℝ) ξ) =
                P.coeff m * perInner m ξ := by
        intro m hm
        refine (MeasureTheory.Lp.coeFn_smul (P.coeff m)
          ((hfPerInner m).toLp (perInner m))).trans ?_
        filter_upwards [MemLp.coeFn_toLp (hfPerInner m)] with ξ hξ
        simp [hξ, smul_eq_mul]
      have h_ae_all :
          ∀ᵐ ξ ∂μ,
            ∀ m ∈ ((Finset.univ : Finset (Fin P.n)) : Set (Fin P.n)),
              (((P.coeff m • (hfPerInner m).toLp (perInner m) :
                  MeasureTheory.Lp ℝ 2 μ) :
                (asymCanonicalStdIndex Nt Ns → ℝ) → ℝ) ξ) =
                P.coeff m * perInner m ξ :=
        (ae_ball_iff (Finset.univ : Finset (Fin P.n)).countable_toSet).mpr h_each
      refine hsum_coe.trans ?_
      filter_upwards [h_ae_all] with ξ hξ
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun m hm =>
        hξ m (Finset.mem_coe.mpr hm)
    rw [hPer_toLp]
    apply Submodule.sum_mem
    intro m hm
    exact Submodule.smul_mem _ _ (hPerInnerChaos m)
  have hf : MeasureTheory.MemLp (asymCanonicalRoughErrorStd Nt Ns a mass T P) 2 μ := by
    change MeasureTheory.MemLp (fun ξ => lead ξ + per ξ) 2 μ
    simpa using hfLead.add hfPer
  refine ⟨hf, ?_⟩
  have h_toLp :
      hf.toLp (asymCanonicalRoughErrorStd Nt Ns a mass T P) =
        hfLead.toLp lead + hfPer.toLp per := by
    calc
      hf.toLp (asymCanonicalRoughErrorStd Nt Ns a mass T P)
          = MeasureTheory.MemLp.toLp (fun ξ => lead ξ + per ξ) (hfLead.add hfPer) := by
              apply MeasureTheory.MemLp.toLp_congr hf (hfLead.add hfPer)
              filter_upwards with ξ
              simp [asymCanonicalRoughErrorStd, lead, leadSum, per, perInner, smul_eq_mul]
      _ = hfLead.toLp lead + hfPer.toLp per := by
            simpa using (MeasureTheory.MemLp.toLp_add hfLead hfPer)
  rw [h_toLp]
  exact Submodule.add_mem _ hLeadChaos hPerChaos

/-- Asym analogue of `canonicalRoughError_neg_tail_of_stdGaussian_explicit_ae`:
given a standard-Gaussian `L²` representative `F` of the asym rough error
(only ae-equal to it under the joint↔std pushforward), with `‖F‖ ≤ K` and
`F ∈ wienerChaosLE _ m`, the polynomial-chaos concentration bound transfers
back to the joint measure. -/
theorem asymCanonicalRoughError_neg_tail_of_stdGaussian_explicit_ae
    {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns] (a mass T : ℝ) (P : InteractionPolynomial)
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ (F : MeasureTheory.Lp ℝ 2
        (GaussianHilbert.stdGaussianFin
          (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)))),
      F ∈ GaussianHilbert.wienerChaosLE
            (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) m →
      ∀ (K : ℝ), 0 < K → ‖F‖ ≤ K →
      (∀ᵐ η ∂(asymCanonicalJointMeasure Nt Ns),
        (F : (Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) → ℝ) → ℝ)
          (asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns η) =
            asymCanonicalRoughError Nt Ns a mass T P η) →
      ∀ (t : ℝ), 0 < t →
        (asymCanonicalJointMeasure Nt Ns)
          {η | asymCanonicalRoughError Nt Ns a mass T P η ≤ -t} ≤
            2 * ENNReal.ofReal
              (Real.exp
                (-(Pphi2.ChaosTailBridge.chaosTailConstant m) *
                  (t / (2 * K)) ^ ((2 : ℝ) / m))) := by
  intro F hF_chaos K hK_pos hF_norm hrepr t ht
  have hset_ae :
      {η | asymCanonicalRoughError Nt Ns a mass T P η ≤ -t}
        =ᵐ[asymCanonicalJointMeasure Nt Ns]
        (asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns) ⁻¹'
          {ω |
            (F : (Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) → ℝ) → ℝ) ω ≤ -t} := by
    filter_upwards [hrepr] with η hη
    change
      (asymCanonicalRoughError Nt Ns a mass T P η ≤ -t) =
        (((F : (Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) → ℝ) → ℝ)
          (asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns η)) ≤ -t)
    rw [← hη]
  have hset_meas :
      MeasurableSet
        {ω |
          (F : (Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) → ℝ) → ℝ) ω ≤ -t} := by
    simpa [Set.preimage, Set.setOf_mem_eq] using
      (MeasureTheory.Lp.stronglyMeasurable F).measurable
        (isClosed_Iic.measurableSet : MeasurableSet (Set.Iic (-t)))
  calc
    (asymCanonicalJointMeasure Nt Ns)
          {η | asymCanonicalRoughError Nt Ns a mass T P η ≤ -t}
        =
      (asymCanonicalJointMeasure Nt Ns)
        ((asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns) ⁻¹'
          {ω |
            (F : (Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) → ℝ) → ℝ) ω ≤ -t}) := by
          exact measure_congr hset_ae
    _ =
      (Measure.map
        (asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns)
        (asymCanonicalJointMeasure Nt Ns))
        {ω |
          (F : (Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) → ℝ) → ℝ) ω ≤ -t} := by
            symm
            rw [Measure.map_apply
              (asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns).measurable]
            exact hset_meas
    _ =
      (GaussianHilbert.stdGaussianFin
        (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)))
        {ω |
          (F : (Fin (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) → ℝ) → ℝ) ω ≤ -t} := by
            rw [asymCanonicalJointMeasure_map_stdGaussian Nt Ns]
    _ ≤
      2 * ENNReal.ofReal
        (Real.exp
          (-(Pphi2.ChaosTailBridge.chaosTailConstant m) *
            (t / (2 * K)) ^ ((2 : ℝ) / m))) :=
      Pphi2.ChaosTailBridge.chaos_neg_tail_bound_explicit
        (Fintype.card (AsymCanonicalJointSumIndex Nt Ns)) m hm
        F hF_chaos K hK_pos hF_norm t ht

/-- UNIT 6b — uniform asym joint rough negative tail from `asymRoughError_variance`.

Packages the asym standard-Gaussian representative, its `wienerChaosLE`
membership (UNIT 6a), and the L² variance estimate (UNIT 5) into the
dimension-independent polynomial-chaos concentration bound. The constant
`K` depends only on `(P, mass, Lt, Ls)` (not on `Nt`, `Ns`, or `a`). -/
theorem asymCanonicalRoughError_neg_tail_uniform
    (P : InteractionPolynomial)
    (mass Lt Ls : ℝ) (hLt : 0 < Lt) (hLs : 0 < Ls) (hmass : 0 < mass) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (_ha : 0 < a)
        (_hvolt : (Nt : ℝ) * a = Lt) (_hvols : (Ns : ℝ) * a = Ls)
        (T : ℝ) (_hT : 0 < T)
        (t : ℝ) (_ht : 0 < t),
        (asymCanonicalJointMeasure Nt Ns)
          {η | asymCanonicalRoughError Nt Ns a mass T P η ≤ -t} ≤
            2 * ENNReal.ofReal
              (Real.exp
                (-(Pphi2.ChaosTailBridge.chaosTailConstant P.n) *
                  (t /
                    (2 * Real.sqrt
                      (K * T * (1 + |Real.log T|) ^ (P.n - 1)))) ^
                    ((2 : ℝ) / P.n))) := by
  obtain ⟨K, hK_pos, hvar⟩ :=
    asymRoughError_variance P mass Lt Ls hLt hLs hmass
  refine ⟨K, hK_pos, ?_⟩
  intro Nt Ns _ _ a ha hvolt hvols T hT t ht
  let nStd : ℕ := Fintype.card (AsymCanonicalJointSumIndex Nt Ns)
  obtain ⟨hf, hF_chaos⟩ :=
    asymCanonicalRoughErrorStd_mem_wienerChaosLE
      Nt Ns a mass ha hmass T hT P
  let F : MeasureTheory.Lp ℝ 2 (GaussianHilbert.stdGaussianFin nStd) :=
    hf.toLp (asymCanonicalRoughErrorStd Nt Ns a mass T P)
  have hrepr_joint :
      ∀ᵐ η ∂(asymCanonicalJointMeasure Nt Ns),
        (F : (Fin nStd → ℝ) → ℝ)
          (asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns η) =
            asymCanonicalRoughError Nt Ns a mass T P η := by
    have hrepr_std :
        ∀ᵐ ξ ∂(GaussianHilbert.stdGaussianFin nStd),
          (F : (Fin nStd → ℝ) → ℝ) ξ =
            asymCanonicalRoughErrorStd Nt Ns a mass T P ξ := by
      simpa [F] using
        (MemLp.coeFn_toLp hf :
          (hf.toLp (asymCanonicalRoughErrorStd Nt Ns a mass T P) :
              (Fin nStd → ℝ) → ℝ)
            =ᵐ[GaussianHilbert.stdGaussianFin nStd]
              asymCanonicalRoughErrorStd Nt Ns a mass T P)
    have hrepr_map :
        ∀ᵐ η ∂(asymCanonicalJointMeasure Nt Ns),
          (F : (Fin nStd → ℝ) → ℝ)
            (asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns η) =
              asymCanonicalRoughErrorStd Nt Ns a mass T P
                (asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns η) := by
      have hrepr_std' :
          ∀ᵐ ξ ∂((asymCanonicalJointMeasure Nt Ns).map
            (asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns)),
            (F : (Fin nStd → ℝ) → ℝ) ξ =
              asymCanonicalRoughErrorStd Nt Ns a mass T P ξ := by
        simpa [nStd, asymCanonicalJointMeasure_map_stdGaussian Nt Ns] using hrepr_std
      exact MeasureTheory.ae_of_ae_map
        (asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns).measurable.aemeasurable
        hrepr_std'
    filter_upwards [hrepr_map] with η hη
    simpa using hη.trans
      (asymCanonicalRoughErrorStd_eq Nt Ns a mass T P η)
  have hF_norm_sq :
      ‖F‖ ^ 2 =
        ∫ ξ, (asymCanonicalRoughErrorStd Nt Ns a mass T P ξ) ^ 2
          ∂(GaussianHilbert.stdGaussianFin nStd) := by
    change
      ‖hf.toLp (asymCanonicalRoughErrorStd Nt Ns a mass T P)‖ ^ 2 =
        ∫ ξ, (asymCanonicalRoughErrorStd Nt Ns a mass T P ξ) ^ 2
          ∂(GaussianHilbert.stdGaussianFin nStd)
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hf] with ξ hξ
    simp [hξ, sq]
  have hsq_integrable :
      Integrable (fun ξ => (asymCanonicalRoughErrorStd Nt Ns a mass T P ξ) ^ 2)
        (GaussianHilbert.stdGaussianFin nStd) := hf.integrable_sq
  have hsq_integrable_map :
      Integrable (fun ξ => (asymCanonicalRoughErrorStd Nt Ns a mass T P ξ) ^ 2)
        ((asymCanonicalJointMeasure Nt Ns).map
          (asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns)) := by
      simpa [nStd, asymCanonicalJointMeasure_map_stdGaussian Nt Ns] using hsq_integrable
  have hstd_eq_joint :
      ∫ ξ, (asymCanonicalRoughErrorStd Nt Ns a mass T P ξ) ^ 2
          ∂(GaussianHilbert.stdGaussianFin nStd) =
        ∫ η, (asymCanonicalRoughError Nt Ns a mass T P η) ^ 2
          ∂(asymCanonicalJointMeasure Nt Ns) := by
    rw [← asymCanonicalJointMeasure_map_stdGaussian Nt Ns]
    rw [integral_map
      (asymCanonicalJointStdGaussianMeasurableEquiv Nt Ns).measurable.aemeasurable
      hsq_integrable_map.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [Filter.Eventually.of_forall
      (fun η : AsymCanonicalJoint Nt Ns =>
        asymCanonicalRoughErrorStd_eq Nt Ns a mass T P η)] with η hη
    simp [hη]
  have hvar_bound :
      ‖F‖ ^ 2 ≤ K * T * (1 + |Real.log T|) ^ (P.n - 1) := by
    rw [hF_norm_sq, hstd_eq_joint]
    exact hvar Nt Ns a ha hvolt hvols T hT
  have hscale_pos :
      0 <
        Real.sqrt (K * T * (1 + |Real.log T|) ^ (P.n - 1)) := by
    apply Real.sqrt_pos.2
    positivity
  have hscale_norm :
      ‖F‖ ≤ Real.sqrt (K * T * (1 + |Real.log T|) ^ (P.n - 1)) := by
    have hnonneg :
        0 ≤ K * T * (1 + |Real.log T|) ^ (P.n - 1) := by positivity
    have hsq :
        ‖F‖ ^ 2 ≤
          (Real.sqrt (K * T * (1 + |Real.log T|) ^ (P.n - 1))) ^ 2 := by
      simpa [Real.sq_sqrt hnonneg] using hvar_bound
    nlinarith [hsq, norm_nonneg F, Real.sqrt_nonneg (K * T * (1 + |Real.log T|) ^ (P.n - 1))]
  exact
    asymCanonicalRoughError_neg_tail_of_stdGaussian_explicit_ae
      a mass T P P.n
      (le_trans (by norm_num) P.hn_ge)
      F hF_chaos
      (Real.sqrt (K * T * (1 + |Real.log T|) ^ (P.n - 1)))
      hscale_pos hscale_norm hrepr_joint t ht

end Pphi2
