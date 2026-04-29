/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Continuum Characteristic-Functional Support

Generic continuum-limit support results for characteristic functionals on the
distinguished `P(phi)_2` plane background.

This file contains:
- complex analyticity of the finite-source generating functional,
- extension of real Euclidean invariance to complex sources,
- Z2/reality support lemmas,
- continuity and norm bounds for the generating functional,
- the standard clustering-to-ergodicity passage.
-/

import Pphi2.ContinuumLimit.Convergence
import Pphi2.EuclideanComplex
import Pphi2.GeneralResults.FunctionalAnalysis
import Pphi2.OSforGFF.TimeTranslation
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

private lemma generatingFunctionalC_integrand_sum_eq {n : ℕ}
    (ω : FieldConfig2) (z : Fin n → ℂ) (J : Fin n → TestFunction2ℂ) :
    Complex.exp
        (Complex.I * ((ω (EuclideanOS.schwartzRe (∑ i, z i • J i)) : ℂ) +
          Complex.I * (ω (EuclideanOS.schwartzIm (∑ i, z i • J i)) : ℂ))) =
      Complex.exp
        (Complex.I * ∑ i : Fin n,
          z i * ((ω (EuclideanOS.schwartzRe (J i)) : ℂ) +
            Complex.I * (ω (EuclideanOS.schwartzIm (J i)) : ℂ))) := by
  congr 1
  rw [pairing_sum_complex_smul]

private lemma generatingFunctionalC_compact_dom
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_moments : ∀ (f : TestFunction2) (c : ℝ), 0 < c →
      Integrable (fun ω : FieldConfig2 => Real.exp (c * |ω f|)) μ)
    (n : ℕ) (J : Fin n → TestFunction2ℂ) :
    ∀ K : Set (Fin n → ℂ), IsCompact K →
      ∃ bound : FieldConfig2 → ℝ, Integrable bound μ ∧
        ∀ z ∈ K, ∀ᵐ ω : FieldConfig2 ∂μ,
          ‖Complex.exp
              (Complex.I * ((ω (EuclideanOS.schwartzRe (∑ i, z i • J i)) : ℂ) +
                Complex.I * (ω (EuclideanOS.schwartzIm (∑ i, z i • J i)) : ℂ)))‖ ≤
            bound ω := by
  intro K hK
  obtain ⟨C_K, hC_K_nn, hC_K⟩ := compact_re_im_bound hK
  by_cases hn : n = 0
  · subst hn
    exact ⟨fun _ => 1, integrable_const 1, fun z _ => ae_of_all μ fun ω => by
      have h0 :
          ‖Complex.exp
              (Complex.I * ((ω (EuclideanOS.schwartzRe (0 : TestFunction2ℂ)) : ℂ) +
                Complex.I * (ω (EuclideanOS.schwartzIm (0 : TestFunction2ℂ)) : ℂ)))‖ = 1 := by
        rw [show EuclideanOS.schwartzRe (0 : TestFunction2ℂ) = 0 by
              ext x; rfl]
        rw [show EuclideanOS.schwartzIm (0 : TestFunction2ℂ) = 0 by
              ext x; rfl]
        simp
      simpa only [Finset.univ_eq_empty, Finset.sum_empty] using h0.le⟩
  · set cK : ℝ := 1 + 2 * ↑n * C_K
    have hcK_pos : 0 < cK := by
      dsimp [cK]
      nlinarith [hC_K_nn]
    set bound := fun ω : FieldConfig2 =>
      ∑ i : Fin n,
        (Real.exp (cK * |ω (EuclideanOS.schwartzRe (J i))|) +
          Real.exp (cK * |ω (EuclideanOS.schwartzIm (J i))|)) with hbound_def
    refine ⟨bound, ?_, fun z hz => ae_of_all μ fun ω => ?_⟩
    · apply integrable_finset_sum
      intro i _
      exact (h_moments (EuclideanOS.schwartzRe (J i)) cK hcK_pos).add
        (h_moments (EuclideanOS.schwartzIm (J i)) cK hcK_pos)
    · rw [Complex.norm_exp]
      have h_re :
          (Complex.I * ((ω (EuclideanOS.schwartzRe (∑ i, z i • J i)) : ℂ) +
            Complex.I * (ω (EuclideanOS.schwartzIm (∑ i, z i • J i)) : ℂ))).re =
            -(ω (EuclideanOS.schwartzIm (∑ i, z i • J i))) := by
        have :
            Complex.I * ((ω (EuclideanOS.schwartzRe (∑ i, z i • J i)) : ℂ) +
              Complex.I * (ω (EuclideanOS.schwartzIm (∑ i, z i • J i)) : ℂ)) =
              -(ω (EuclideanOS.schwartzIm (∑ i, z i • J i)) : ℂ) +
                (ω (EuclideanOS.schwartzRe (∑ i, z i • J i)) : ℂ) * Complex.I := by
          rw [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul]
          ring
        rw [this, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      rw [h_re]
      calc
        Real.exp (-(ω (EuclideanOS.schwartzIm (∑ i, z i • J i))))
            ≤ Real.exp (|ω (EuclideanOS.schwartzIm (∑ i, z i • J i))|) :=
          Real.exp_le_exp_of_le (neg_le_abs _)
        _ ≤ Real.exp
            (C_K * ∑ i : Fin n,
              (|ω (EuclideanOS.schwartzRe (J i))| +
                |ω (EuclideanOS.schwartzIm (J i))|)) := by
            apply Real.exp_le_exp_of_le
            rw [schwartzIm_sum_complex_smul, map_sum]
            calc
              |∑ i : Fin n,
                  ω ((z i).re • EuclideanOS.schwartzIm (J i) +
                    (z i).im • EuclideanOS.schwartzRe (J i))|
                  ≤ ∑ i : Fin n,
                      |ω ((z i).re • EuclideanOS.schwartzIm (J i) +
                        (z i).im • EuclideanOS.schwartzRe (J i))| :=
                Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ i : Fin n,
                    (|(z i).re| * |ω (EuclideanOS.schwartzIm (J i))| +
                      |(z i).im| * |ω (EuclideanOS.schwartzRe (J i))|) := by
                apply Finset.sum_le_sum
                intro i _
                simpa [Real.norm_eq_abs, map_add, map_smul, smul_eq_mul, abs_mul] using
                  (norm_add_le
                    (ω ((z i).re • EuclideanOS.schwartzIm (J i)))
                    (ω ((z i).im • EuclideanOS.schwartzRe (J i))))
              _ ≤ ∑ i : Fin n,
                    (C_K * |ω (EuclideanOS.schwartzIm (J i))| +
                      C_K * |ω (EuclideanOS.schwartzRe (J i))|) := by
                apply Finset.sum_le_sum
                intro i _
                obtain ⟨h_re_i, h_im_i⟩ := hC_K z hz i
                apply add_le_add
                · exact mul_le_mul_of_nonneg_right h_re_i (abs_nonneg _)
                · exact mul_le_mul_of_nonneg_right h_im_i (abs_nonneg _)
              _ = C_K * ∑ i : Fin n,
                    (|ω (EuclideanOS.schwartzRe (J i))| +
                      |ω (EuclideanOS.schwartzIm (J i))|) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ ≤ ∑ i : Fin n,
              Real.exp
                (↑n * C_K *
                  (|ω (EuclideanOS.schwartzRe (J i))| +
                    |ω (EuclideanOS.schwartzIm (J i))|)) :=
          exp_mul_sum_le (Nat.pos_of_ne_zero hn) C_K hC_K_nn _
        _ ≤ ∑ i : Fin n,
              (Real.exp (2 * ↑n * C_K * |ω (EuclideanOS.schwartzRe (J i))|) +
                Real.exp (2 * ↑n * C_K * |ω (EuclideanOS.schwartzIm (J i))|)) := by
          apply Finset.sum_le_sum
          intro i _
          simpa [mul_assoc] using
            exp_mul_add_le (↑n * C_K) |ω (EuclideanOS.schwartzRe (J i))|
              |ω (EuclideanOS.schwartzIm (J i))|
              (mul_nonneg (Nat.cast_nonneg' n) hC_K_nn)
        _ ≤ bound ω := by
          rw [hbound_def]
          apply Finset.sum_le_sum
          intro i _
          apply add_le_add
          · apply Real.exp_le_exp_of_le
            have hcoef : 2 * ↑n * C_K ≤ cK := by
              dsimp [cK]
              nlinarith [hC_K_nn]
            exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
          · apply Real.exp_le_exp_of_le
            have hcoef : 2 * ↑n * C_K ≤ cK := by
              dsimp [cK]
              nlinarith [hC_K_nn]
            exact mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)

/-- **Analyticity of the complex generating functional from exponential moments.**

If the measure μ has all exponential moments, then the complex generating
functional `z ↦ Z_ℂ[Σ zᵢ Jᵢ]` is jointly analytic in `z ∈ ℂⁿ` for any finite
family of complex test functions. The proof is by `analyticOnNhd_integral`
using the complex-linearity rewrite for the pairing and compact-set domination
by one-source exponential moments. -/
theorem analyticOn_generatingFunctionalC
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_moments : ∀ (f : TestFunction2) (c : ℝ), 0 < c →
        Integrable (fun ω : FieldConfig2 => Real.exp (c * |ω f|)) μ)
    (n : ℕ) (J : Fin n → TestFunction2ℂ) :
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ (∑ i, z i • J i)) Set.univ := by
  let F : (Fin n → ℂ) → FieldConfig2 → ℂ := fun z ω =>
    Complex.exp
      (Complex.I * ((ω (EuclideanOS.schwartzRe (∑ i, z i • J i)) : ℂ) +
        Complex.I * (ω (EuclideanOS.schwartzIm (∑ i, z i • J i)) : ℂ)))
  rw [analyticOn_univ]
  apply analyticOnNhd_integral
  · intro ω z _
    have hfun :
        (fun w : Fin n → ℂ => F w ω) =
          fun w : Fin n → ℂ =>
            Complex.exp
              (Complex.I * ∑ i : Fin n,
                w i * ((ω (EuclideanOS.schwartzRe (J i)) : ℂ) +
                  Complex.I * (ω (EuclideanOS.schwartzIm (J i)) : ℂ))) := by
      funext w
      dsimp [F]
      exact generatingFunctionalC_integrand_sum_eq ω w J
    rw [hfun]
    apply AnalyticAt.cexp'
    exact analyticAt_const.mul (Finset.univ.analyticAt_fun_sum (fun i _ =>
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt z).mul
        analyticAt_const))
  · intro z
    dsimp [F]
    apply (Complex.measurable_exp.comp _).aestronglyMeasurable
    exact (measurable_const.mul ((Complex.measurable_ofReal.comp
      (configuration_eval_measurable _)).add (measurable_const.mul
      (Complex.measurable_ofReal.comp (configuration_eval_measurable _)))))
  · exact generatingFunctionalC_compact_dom μ h_moments n J

/-- **Complex generating functional invariance from real invariance.**

If the real generating functional is `g`-invariant for all real test functions,
then the complex generating functional is also `g`-invariant.

**Proof**: Define analytic families `F(z) = Z_ℂ[Re(J) + z·Im(J)]` and
`G(z) = Z_ℂ[g·Re(J) + z·g·Im(J)]`. Both are entire (from
`analyticOn_generatingFunctionalC`). They agree on `ℝ` by the real invariance
hypothesis, hence agree on all of `ℂ` by the identity theorem. Evaluating at
`z = i` gives `Z_ℂ[J] = Z_ℂ[g·J]`. -/
theorem complex_gf_invariant_of_real_gf_invariant
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_moments : ∀ (f : TestFunction2) (c : ℝ), 0 < c →
      Integrable (fun ω : FieldConfig2 => Real.exp (c * |ω f|)) μ)
    (g : E2)
    (h_real : ∀ f : TestFunction2,
      EuclideanOS.generatingFunctional (B := plane2Background) μ f =
        EuclideanOS.generatingFunctional (B := plane2Background) μ (euclideanAction2 g f))
    (J : TestFunction2ℂ) :
    EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ J =
      EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ (euclideanAction2ℂ g J) := by
  let JF : Fin 2 → TestFunction2ℂ :=
    ![schwartzOfReal (EuclideanOS.schwartzRe (B := plane2Background) J),
      schwartzOfReal (EuclideanOS.schwartzIm (B := plane2Background) J)]
  let JG : Fin 2 → TestFunction2ℂ :=
    ![schwartzOfReal (euclideanAction2 g (EuclideanOS.schwartzRe (B := plane2Background) J)),
      schwartzOfReal (euclideanAction2 g (EuclideanOS.schwartzIm (B := plane2Background) J))]
  let ψ : ℂ → Fin 2 → ℂ := fun z => ![(1 : ℂ), z]
  let F : ℂ → ℂ := fun z =>
    EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ (∑ i : Fin 2, (ψ z i) • JF i)
  let G : ℂ → ℂ := fun z =>
    EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ (∑ i : Fin 2, (ψ z i) • JG i)
  have hψ_analytic : AnalyticOn ℂ ψ Set.univ := by
    refine AnalyticOn.pi (fun i => ?_)
    fin_cases i
    · simpa using (analyticOn_const : AnalyticOn ℂ (fun _ : ℂ => (1 : ℂ)) Set.univ)
    · simpa using (analyticOn_id : AnalyticOn ℂ (fun z : ℂ => z) Set.univ)
  have hF_analytic : AnalyticOn ℂ F Set.univ := by
    have hbase : AnalyticOn ℂ (fun w : Fin 2 → ℂ =>
        EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ (∑ i : Fin 2, w i • JF i))
        Set.univ :=
      analyticOn_generatingFunctionalC μ h_moments 2 JF
    exact hbase.comp hψ_analytic (by intro z hz; simp [Set.mem_univ])
  have hG_analytic : AnalyticOn ℂ G Set.univ := by
    have hbase : AnalyticOn ℂ (fun w : Fin 2 → ℂ =>
        EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ (∑ i : Fin 2, w i • JG i))
        Set.univ :=
      analyticOn_generatingFunctionalC μ h_moments 2 JG
    exact hbase.comp hψ_analytic (by intro z hz; simp [Set.mem_univ])
  have h_real_axis : ∀ r : ℝ, F r = G r := by
    intro r
    have hF_r : F r =
        EuclideanOS.generatingFunctional (B := plane2Background) μ
          (EuclideanOS.schwartzRe (B := plane2Background) J +
            r • EuclideanOS.schwartzIm (B := plane2Background) J) := by
      simpa [F, ψ, JF, Fin.sum_univ_two] using
        (generatingFunctionalℂ_ofReal_add_real_smul μ
          (EuclideanOS.schwartzRe (B := plane2Background) J)
          (EuclideanOS.schwartzIm (B := plane2Background) J) r)
    have hG_r : G r =
        EuclideanOS.generatingFunctional (B := plane2Background) μ
          (euclideanAction2 g (EuclideanOS.schwartzRe (B := plane2Background) J) +
            r • euclideanAction2 g (EuclideanOS.schwartzIm (B := plane2Background) J)) := by
      simpa [G, ψ, JG, Fin.sum_univ_two] using
        (generatingFunctionalℂ_ofReal_add_real_smul μ
          (euclideanAction2 g (EuclideanOS.schwartzRe (B := plane2Background) J))
          (euclideanAction2 g (EuclideanOS.schwartzIm (B := plane2Background) J)) r)
    rw [hF_r, hG_r]
    simpa [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul] using
      h_real
        (EuclideanOS.schwartzRe (B := plane2Background) J +
          r • EuclideanOS.schwartzIm (B := plane2Background) J)
  have hF_nhd : AnalyticOnNhd ℂ F Set.univ := analyticOn_univ.mp hF_analytic
  have hG_nhd : AnalyticOnNhd ℂ G Set.univ := analyticOn_univ.mp hG_analytic
  have hfreq : ∃ᶠ z : ℂ in nhdsWithin (0 : ℂ) ({0}ᶜ), F z = G z := by
    rw [Filter.frequently_iff]
    intro U hU
    rcases Metric.mem_nhdsWithin_iff.mp hU with ⟨ε, hε, hUball⟩
    have hball : (ε / 2 : ℂ) ∈ Metric.ball (0 : ℂ) ε := by
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero]
      have hnorm : ‖(ε / 2 : ℂ)‖ = |ε| / 2 := by simp
      rw [hnorm]
      have hεabs : |ε| = ε := abs_of_pos hε
      rw [hεabs]
      linarith
    have hne : (ε / 2 : ℂ) ≠ 0 := by
      exact_mod_cast (show (ε / 2 : ℝ) ≠ 0 by linarith)
    refine ⟨(ε / 2 : ℂ), ?_, ?_⟩
    · exact hUball ⟨hball, hne⟩
    · simpa using h_real_axis (ε / 2)
  have h_eq : Set.EqOn F G Set.univ := by
    simpa using
      hF_nhd.eqOn_of_preconnected_of_frequently_eq hG_nhd
        isPreconnected_univ (by simp : (0 : ℂ) ∈ Set.univ) hfreq
  have hJ_decomp :
      J = schwartzOfReal (EuclideanOS.schwartzRe (B := plane2Background) J) +
        (Complex.I : ℂ) • schwartzOfReal (EuclideanOS.schwartzIm (B := plane2Background) J) :=
    schwartz_decompose J
  have hJg_decomp : euclideanAction2ℂ g J =
      schwartzOfReal (euclideanAction2 g (EuclideanOS.schwartzRe (B := plane2Background) J)) +
      (Complex.I : ℂ) •
        schwartzOfReal (euclideanAction2 g (EuclideanOS.schwartzIm (B := plane2Background) J)) :=
    schwartz_decompose_continuumEuclideanActionComplex g J
  have hF_I : F Complex.I =
      EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ
        (schwartzOfReal (EuclideanOS.schwartzRe (B := plane2Background) J) +
          (Complex.I : ℂ) • schwartzOfReal (EuclideanOS.schwartzIm (B := plane2Background) J)) := by
    simp [F, ψ, JF, Fin.sum_univ_two]
  have hG_I : G Complex.I =
      EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ
        (schwartzOfReal
            (euclideanAction2 g (EuclideanOS.schwartzRe (B := plane2Background) J)) +
          (Complex.I : ℂ) •
            schwartzOfReal
              (euclideanAction2 g (EuclideanOS.schwartzIm (B := plane2Background) J))) := by
    simp [G, ψ, JG, Fin.sum_univ_two]
  have hGF_J :
      EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ J =
        EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ
          (schwartzOfReal (EuclideanOS.schwartzRe (B := plane2Background) J) +
            (Complex.I : ℂ) •
              schwartzOfReal (EuclideanOS.schwartzIm (B := plane2Background) J)) :=
    congrArg (EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ) hJ_decomp
  have hGF_gJ :
      EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ (euclideanAction2ℂ g J) =
        EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ
          (schwartzOfReal
              (euclideanAction2 g (EuclideanOS.schwartzRe (B := plane2Background) J)) +
            (Complex.I : ℂ) •
              schwartzOfReal
                (euclideanAction2 g (EuclideanOS.schwartzIm (B := plane2Background) J))) :=
    congrArg (EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ) hJg_decomp
  have hFG_I : F Complex.I = G Complex.I := h_eq (by simp)
  calc
    EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ J
        = F Complex.I := hGF_J.trans hF_I.symm
    _ = G Complex.I := hFG_I
    _ = EuclideanOS.generatingFunctionalℂ (B := plane2Background) μ (euclideanAction2ℂ g J) :=
      hG_I.trans hGF_gJ.symm

/-- **Textbook axiom: Z₂ symmetry of the P(Φ)₂ measure.**

The continuum limit measure is invariant under field negation `φ ↦ -φ`, as
recorded directly in `IsPphi2Limit`. -/
theorem pphi2_measure_neg_invariant (P : InteractionPolynomial)
    (mass : ℝ) (_hmass : 0 < mass)
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_limit : IsPphi2Limit μ P mass) :
    Measure.map (Neg.neg : FieldConfig2 → FieldConfig2) μ = μ := by
  rcases h_limit with ⟨_a, _ν, _hprob, _ha_tend, _ha_pos, _hmom, hneg, _hcf, _hlat,
    _hweakconv, _happrox_os3⟩
  exact hneg

/-- Negation on Configuration is measurable w.r.t. the cylindrical σ-algebra. -/
theorem configuration_neg_measurable :
    @Measurable FieldConfig2 FieldConfig2
      instMeasurableSpaceConfiguration instMeasurableSpaceConfiguration
      (Neg.neg : FieldConfig2 → FieldConfig2) :=
  configuration_measurable_of_eval_measurable _ fun f =>
    (configuration_eval_measurable f).neg

/-- The generating functional of a Z₂-symmetric measure is real-valued. -/
theorem pphi2_generating_functional_real (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_limit : IsPphi2Limit μ P mass)
    (f : TestFunction2) :
    (EuclideanOS.generatingFunctional (B := plane2Background) μ f).im = 0 := by
  have h_sym := pphi2_measure_neg_invariant P mass hmass μ h_limit
  simp only [EuclideanOS.generatingFunctional]
  set g := fun ω : FieldConfig2 => Complex.exp (Complex.I * ↑(ω f))
  have hconj : starRingEnd ℂ (∫ ω, g ω ∂μ) = ∫ ω, starRingEnd ℂ (g ω) ∂μ :=
    (integral_conj (f := g)).symm
  have hconj_exp : ∀ ω : FieldConfig2,
      starRingEnd ℂ (g ω) = Complex.exp (Complex.I * ↑((-ω) f)) := by
    intro ω
    simp only [g]
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    simp only [show (-ω) f = -(ω f) from rfl, Complex.ofReal_neg]
    ring
  have hcov : ∫ ω, Complex.exp (Complex.I * ↑((-ω) f)) ∂μ = ∫ ω, g ω ∂μ := by
    have heq : (fun ω : FieldConfig2 => Complex.exp (Complex.I * ↑((-ω) f))) =
        g ∘ Neg.neg := by
      ext ω; simp only [g, Function.comp]
    rw [heq]
    have hasm : AEStronglyMeasurable g (Measure.map Neg.neg μ) := by
      rw [h_sym]
      exact ((Complex.measurable_ofReal.comp (configuration_eval_measurable f)).const_mul
        Complex.I |>.cexp).aestronglyMeasurable
    have := MeasureTheory.integral_map configuration_neg_measurable.aemeasurable hasm
    rw [h_sym] at this
    exact this.symm
  have hself_conj : starRingEnd ℂ (∫ ω, g ω ∂μ) = ∫ ω, g ω ∂μ := by
    rw [hconj]
    simp_rw [hconj_exp]
    exact hcov
  exact Complex.conj_eq_iff_im.mp hself_conj

/-- **Continuity of the generating functional under translations.** -/
theorem generatingFunctional_translate_continuous
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (f g : TestFunction2) :
    Continuous (fun t : ℝ =>
      EuclideanOS.generatingFunctional (B := plane2Background) μ
        (f + SchwartzMap.translate (timeTranslationVector2 t) g)) := by
  set h : ℝ → TestFunction2 := fun t =>
    f + SchwartzMap.translate (timeTranslationVector2 t) g with hh_def
  change Continuous (fun t => ∫ ω : FieldConfig2, Complex.exp (Complex.I * ↑(ω (h t))) ∂μ)
  apply MeasureTheory.continuous_of_dominated
  · intro t
    exact ((Complex.measurable_ofReal.comp (configuration_eval_measurable (h t))).const_mul
      Complex.I |>.cexp).aestronglyMeasurable
  · intro t
    exact ae_of_all μ fun ω => by
      rw [show Complex.I * ↑(ω (h t)) = ↑(ω (h t)) * Complex.I from mul_comm _ _]
      exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  · exact integrable_const 1
  · exact ae_of_all μ fun ω => by
      apply Complex.continuous_exp.comp
      apply Continuous.mul continuous_const
      apply Complex.continuous_ofReal.comp
      show Continuous (fun t => ω (h t))
      simp only [hh_def, map_add]
      apply Continuous.add continuous_const
      apply ω.continuous.comp
      haveI : Fact (0 < 2) := ⟨by norm_num⟩
      have h_eq : (fun t => SchwartzMap.translate (timeTranslationVector2 t) g) =
          (fun t => TimeTranslation.timeTranslationSchwartz (-t) g) := by
        funext t
        simpa using (translate_timeTranslationVector2_eq_timeTranslationSchwartz_neg t g)
      rw [h_eq]
      exact (TimeTranslation.continuous_timeTranslationSchwartz g).comp (continuous_neg)

/-- **Norm bound on the generating functional.** -/
theorem norm_generatingFunctional_le_one
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (f : TestFunction2) :
    ‖EuclideanOS.generatingFunctional (B := plane2Background) μ f‖ ≤ 1 := by
  simp only [EuclideanOS.generatingFunctional]
  calc ‖∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂μ‖
      ≤ ∫ ω, ‖Complex.exp (Complex.I * ↑(ω f))‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ = ∫ _ : FieldConfig2, (1 : ℝ) ∂μ := by
        congr 1; ext ω; exact Complex.norm_exp_I_mul_ofReal (ω f)
    _ = 1 := by
        rw [integral_const, probReal_univ, smul_eq_mul, mul_one]

/-- **Clustering implies ergodicity for P(Φ)₂ measures.** -/
theorem os4_clustering_implies_ergodicity (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure FieldConfig2) [IsProbabilityMeasure μ]
    (h_limit : IsPphi2Limit μ P mass)
    (h_cluster : EuclideanOS.OS4_Clustering (B := plane2Background) μ) :
    EuclideanOS.OS4_Ergodicity plane2TimeStructure μ := by
  intro f g
  set L := (EuclideanOS.generatingFunctional (B := plane2Background) μ f).re *
    (EuclideanOS.generatingFunctional (B := plane2Background) μ g).re
  have hf_real := pphi2_generating_functional_real P mass hmass μ h_limit f
  have hg_real := pphi2_generating_functional_real P mass hmass μ h_limit g
  have h_re_product :
      (EuclideanOS.generatingFunctional (B := plane2Background) μ f *
        EuclideanOS.generatingFunctional (B := plane2Background) μ g).re = L := by
    simp only [Complex.mul_re, L]
    rw [hf_real, hg_real]
    ring
  set h_fun : ℝ → ℝ := fun t =>
    (EuclideanOS.generatingFunctional (B := plane2Background) μ
      (f + SchwartzMap.translate (timeTranslationVector2 t) g)).re
  have h_Z_tend : Filter.Tendsto
      (fun t : ℝ => EuclideanOS.generatingFunctional (B := plane2Background) μ
        (f + SchwartzMap.translate (timeTranslationVector2 t) g))
      Filter.atTop
      (nhds
        (EuclideanOS.generatingFunctional (B := plane2Background) μ f *
          EuclideanOS.generatingFunctional (B := plane2Background) μ g)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨R, hR, h_bound⟩ := h_cluster f g ε hε
    use R + 1
    intro t ht
    have h_norm_ge : ‖timeTranslationVector2 t‖ > R := by
      have h1 := PiLp.norm_apply_le (timeTranslationVector2 t) (0 : Fin 2)
      have h2 : (timeTranslationVector2 t).ofLp (0 : Fin 2) = t := by simp
      rw [h2, Real.norm_eq_abs] at h1
      linarith [le_abs_self t]
    rw [Complex.dist_eq]
    exact h_bound _ h_norm_ge
  have h_ptwise : Filter.Tendsto h_fun Filter.atTop (nhds L) := by
    rw [show L =
      (EuclideanOS.generatingFunctional (B := plane2Background) μ f *
        EuclideanOS.generatingFunctional (B := plane2Background) μ g).re from
      h_re_product.symm]
    have h_re_cont : Filter.Tendsto Complex.re
        (nhds
          (EuclideanOS.generatingFunctional (B := plane2Background) μ f *
            EuclideanOS.generatingFunctional (B := plane2Background) μ g))
        (nhds
          (EuclideanOS.generatingFunctional (B := plane2Background) μ f *
            EuclideanOS.generatingFunctional (B := plane2Background) μ g).re) :=
      Complex.continuous_re.continuousAt
    exact h_re_cont.comp h_Z_tend
  have h_bounded : ∃ M : ℝ, ∀ t, |h_fun t| ≤ M := by
    use 1
    intro t
    exact (Complex.abs_re_le_norm _).trans (norm_generatingFunctional_le_one μ _)
  have h_meas : Measurable h_fun :=
    (Complex.continuous_re.comp (generatingFunctional_translate_continuous μ f g)).measurable
  exact cesaro_set_integral_tendsto h_fun L h_meas h_bounded h_ptwise

end Pphi2

end
