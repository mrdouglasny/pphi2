/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michael R. Douglas
-/
import Pphi2.WickOrdering.WickPolynomial
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Wick monomials have mean zero under centered Gaussians

For `σ² > 0`, `wickMonomial n σ²` is a scaled Hermite polynomial. We first
extract the standard-normal Hermite mean-zero identity from the public theorem
`hermiteFunction_orthonormal`, then transport it to arbitrary variance via the
scaling formula for `gaussianReal`.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Section I.3
- `GaussianField/SchwartzNuclear/HermiteFunctions.lean`
-/
noncomputable section

open scoped Topology ProbabilityTheory NNReal
open MeasureTheory ProbabilityTheory

namespace Pphi2

private abbrev hermiteEval (n : ℕ) : ℝ → ℝ :=
  fun x => ((Polynomial.hermite n).map (Int.castRingHom ℝ)).eval x

private abbrev halfVariance : ℝ≥0 := 1 / 2

private noncomputable def halfGaussianDensity (x : ℝ) : ℝ≥0 :=
  ⟨ProbabilityTheory.gaussianPDFReal (0 : ℝ) halfVariance x,
    ProbabilityTheory.gaussianPDFReal_nonneg _ _ x⟩

private lemma hermiteFunctionNormConst_pos (n : ℕ) : 0 < hermiteFunctionNormConst n := by
  unfold hermiteFunctionNormConst
  have hfact : 0 < (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos n
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  positivity

private lemma hermiteFunction_mul_zero (n : ℕ) :
    (fun x : ℝ => hermiteFunction n x * hermiteFunction 0 x) =
      fun x => (hermiteFunctionNormConst n * hermiteFunctionNormConst 0) *
        (hermiteEval n (Real.sqrt 2 * x) * Real.exp (-(x ^ 2))) := by
  funext x
  unfold hermiteFunction hermiteEval
  have hG : Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2) = Real.exp (-(x ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [Polynomial.hermite_zero, eq_intCast, Int.cast_one, Polynomial.map_one,
    Polynomial.eval_one, mul_one]
  calc
    hermiteFunctionNormConst n *
          Polynomial.eval (x * √2) (Polynomial.map (Int.castRingHom ℝ) (Polynomial.hermite n)) *
          Real.exp (-(x ^ 2) / 2) * (hermiteFunctionNormConst 0 * Real.exp (-(x ^ 2) / 2))
        =
      hermiteFunctionNormConst n * hermiteFunctionNormConst 0 *
          (Polynomial.eval (x * √2) (Polynomial.map (Int.castRingHom ℝ) (Polynomial.hermite n)) *
            (Real.exp (-(x ^ 2) / 2) * Real.exp (-(x ^ 2) / 2))) := by ring
    _ =
      hermiteFunctionNormConst n * hermiteFunctionNormConst 0 *
          (Polynomial.eval (x * √2) (Polynomial.map (Int.castRingHom ℝ) (Polynomial.hermite n)) *
            Real.exp (-(x ^ 2))) := by rw [hG]
    _ = (hermiteFunctionNormConst n * hermiteFunctionNormConst 0) *
          (hermiteEval n (Real.sqrt 2 * x) * Real.exp (-(x ^ 2))) := by
            simp [hermiteEval, mul_comm, mul_assoc]

private lemma gaussianPDFReal_zero_half (x : ℝ) :
    ProbabilityTheory.gaussianPDFReal 0 halfVariance x =
      (Real.sqrt Real.pi)⁻¹ * Real.exp (-(x ^ 2)) := by
  rw [ProbabilityTheory.gaussianPDFReal_def]
  norm_num [halfVariance, show (((1 / 2 : ℝ≥0) : ℝ)) = (1 / 2 : ℝ) by rfl]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  calc
    √2 * ((√Real.pi)⁻¹ * (√2)⁻¹) = (√2 * (√2)⁻¹) * (√Real.pi)⁻¹ := by ring
    _ = (√Real.pi)⁻¹ := by rw [mul_inv_cancel₀ hs, one_mul]


private lemma integrable_hermiteEval_sqrt_two_mul_exp (n : ℕ) :
    Integrable (fun x : ℝ => hermiteEval n (Real.sqrt 2 * x) * Real.exp (-(x ^ 2))) volume := by
  let K : ℝ := hermiteFunctionNormConst n * hermiteFunctionNormConst 0
  have hK_ne : K ≠ 0 := by
    dsimp [K]
    exact mul_ne_zero
      (ne_of_gt (hermiteFunctionNormConst_pos n))
      (ne_of_gt (hermiteFunctionNormConst_pos 0))
  have hprod : Integrable (fun x : ℝ => hermiteFunction n x * hermiteFunction 0 x) volume := by
    exact (hermiteFunction_memLp n).integrable_mul (hermiteFunction_memLp 0)
  rw [hermiteFunction_mul_zero n] at hprod
  exact (MeasureTheory.integrable_const_mul_iff (IsUnit.mk0 K hK_ne) _).1 hprod

private lemma integral_hermiteEval_sqrt_two_mul_exp_eq_zero (n : ℕ) (hn : 1 ≤ n) :
    ∫ x : ℝ, hermiteEval n (Real.sqrt 2 * x) * Real.exp (-(x ^ 2)) = 0 := by
  let K : ℝ := hermiteFunctionNormConst n * hermiteFunctionNormConst 0
  have hK_ne : K ≠ 0 := by
    dsimp [K]
    exact mul_ne_zero
      (ne_of_gt (hermiteFunctionNormConst_pos n))
      (ne_of_gt (hermiteFunctionNormConst_pos 0))
  have horth : ∫ x : ℝ, hermiteFunction n x * hermiteFunction 0 x = 0 := by
    have := hermiteFunction_orthonormal n 0
    simpa [Nat.ne_of_gt hn] using this
  rw [hermiteFunction_mul_zero n, MeasureTheory.integral_const_mul] at horth
  exact (mul_eq_zero.mp horth).resolve_left hK_ne

private lemma integrable_hermiteEval_sqrt_two_half (n : ℕ) :
    Integrable (fun x : ℝ => hermiteEval n (Real.sqrt 2 * x))
      (gaussianReal (0 : ℝ) halfVariance) := by
  have hbase :
      Integrable (fun x : ℝ => hermiteEval n (Real.sqrt 2 * x) * Real.exp (-(x ^ 2))) volume :=
    integrable_hermiteEval_sqrt_two_mul_exp n
  have hweighted :
      Integrable
        (fun x : ℝ => (halfGaussianDensity x : ℝ) * hermiteEval n (Real.sqrt 2 * x))
        volume := by
    have hconst :
        Integrable
          (fun x : ℝ =>
            (Real.sqrt Real.pi)⁻¹ *
              (hermiteEval n (Real.sqrt 2 * x) * Real.exp (-(x ^ 2))))
          volume := hbase.const_mul ((Real.sqrt Real.pi)⁻¹)
    refine hconst.congr ?_
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    change
      (Real.sqrt Real.pi)⁻¹ * (hermiteEval n (Real.sqrt 2 * x) * Real.exp (-(x ^ 2))) =
        (halfGaussianDensity x : ℝ) * hermiteEval n (Real.sqrt 2 * x)
    have hpdf :
        (halfGaussianDensity x : ℝ) =
          ProbabilityTheory.gaussianPDFReal (0 : ℝ) halfVariance x := by
      simp [halfGaussianDensity]
    rw [hpdf, gaussianPDFReal_zero_half]
    ring
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero
    (μ := (0 : ℝ)) (v := halfVariance) (by norm_num)]
  rw [ProbabilityTheory.gaussianPDF_def]
  have hmeas_half : Measurable halfGaussianDensity := by
    have hdef :
        halfGaussianDensity =
          fun x : ℝ =>
            Real.toNNReal (ProbabilityTheory.gaussianPDFReal (0 : ℝ) halfVariance x) := by
      funext x
      simp [halfGaussianDensity, Real.toNNReal_of_nonneg, ProbabilityTheory.gaussianPDFReal_nonneg]
    rw [hdef]
    exact (ProbabilityTheory.measurable_gaussianPDFReal _ _).real_toNNReal
  have hdens :
      (fun x : ℝ => (halfGaussianDensity x : ENNReal)) =
        fun x : ℝ =>
          ENNReal.ofReal (ProbabilityTheory.gaussianPDFReal (0 : ℝ) halfVariance x) := by
    funext x
    rw [halfGaussianDensity]
    symm
    exact ENNReal.ofReal_eq_coe_nnreal (ProbabilityTheory.gaussianPDFReal_nonneg _ _ x)
  rw [← hdens]
  exact
    (MeasureTheory.integrable_withDensity_iff_integrable_coe_smul
      (μ := volume) (f := halfGaussianDensity)
      (g := fun x : ℝ => hermiteEval n (Real.sqrt 2 * x))
      (hf := hmeas_half)).2 <| by
        simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hweighted

private lemma integral_hermiteEval_sqrt_two_half_eq_zero (n : ℕ) (hn : 1 ≤ n) :
    ∫ x : ℝ, hermiteEval n (Real.sqrt 2 * x) ∂gaussianReal (0 : ℝ) halfVariance = 0 := by
  have hbase : ∫ x : ℝ, hermiteEval n (Real.sqrt 2 * x) * Real.exp (-(x ^ 2)) = 0 :=
    integral_hermiteEval_sqrt_two_mul_exp_eq_zero n hn
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul (μ := (0 : ℝ)) (v := halfVariance)
    (by norm_num)]
  have hcongr :
      ∫ x : ℝ,
          ProbabilityTheory.gaussianPDFReal (0 : ℝ) halfVariance x •
            hermiteEval n (Real.sqrt 2 * x) =
        ∫ x : ℝ,
          (Real.sqrt Real.pi)⁻¹ * (hermiteEval n (Real.sqrt 2 * x) * Real.exp (-(x ^ 2))) := by
    refine MeasureTheory.integral_congr_ae ?_
    exact MeasureTheory.ae_of_all _ (fun x => by
      change
        ProbabilityTheory.gaussianPDFReal (0 : ℝ) halfVariance x *
            hermiteEval n (Real.sqrt 2 * x) =
          (Real.sqrt Real.pi)⁻¹ * (hermiteEval n (Real.sqrt 2 * x) * Real.exp (-(x ^ 2)))
      have hpdfhalf :
          ProbabilityTheory.gaussianPDFReal (0 : ℝ) halfVariance x =
            (Real.sqrt Real.pi)⁻¹ * Real.exp (-(x ^ 2)) := gaussianPDFReal_zero_half x
      rw [hpdfhalf]
      ring)
  calc
    ∫ x : ℝ,
        ProbabilityTheory.gaussianPDFReal (0 : ℝ) halfVariance x •
          hermiteEval n (Real.sqrt 2 * x)
          = ∫ x : ℝ,
              (Real.sqrt Real.pi)⁻¹ *
                (hermiteEval n (Real.sqrt 2 * x) * Real.exp (-(x ^ 2))) :=
            hcongr
    _ = (Real.sqrt Real.pi)⁻¹ *
          ∫ x : ℝ, hermiteEval n (Real.sqrt 2 * x) * Real.exp (-(x ^ 2)) := by
          rw [MeasureTheory.integral_const_mul]
    _ = 0 := by simp [hbase]

private lemma half_gaussian_map_sqrt_two :
    MeasureTheory.Measure.map (fun x : ℝ => Real.sqrt 2 * x)
      (gaussianReal (0 : ℝ) halfVariance) =
      gaussianReal (0 : ℝ) (1 : ℝ≥0) := by
  calc
    MeasureTheory.Measure.map (fun x : ℝ => Real.sqrt 2 * x) (gaussianReal (0 : ℝ) halfVariance) =
        gaussianReal (Real.sqrt 2 * (0 : ℝ)) (⟨Real.sqrt 2 ^ 2, sq_nonneg _⟩ * halfVariance) := by
          simpa using
            (gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := halfVariance) (c := Real.sqrt 2))
    _ = gaussianReal (0 : ℝ) (1 : ℝ≥0) := by
      congr 1
      · ring
      · apply NNReal.coe_injective
        norm_num [Real.sq_sqrt two_pos.le]

private lemma continuous_hermiteEval (n : ℕ) : Continuous (hermiteEval n) := by
  simpa [hermiteEval] using (((Polynomial.hermite n).map (Int.castRingHom ℝ)).continuous)

private lemma integrable_hermiteEval_standard (n : ℕ) :
    Integrable (hermiteEval n) (gaussianReal (0 : ℝ) (1 : ℝ≥0)) := by
  have hmap := half_gaussian_map_sqrt_two
  rw [← hmap]
  refine (MeasureTheory.integrable_map_measure
    (g := hermiteEval n)
    ((continuous_hermiteEval n).measurable.aestronglyMeasurable)
    ((measurable_const.mul measurable_id).aemeasurable)).2 ?_
  simpa [Function.comp, mul_comm] using integrable_hermiteEval_sqrt_two_half n

private lemma integral_hermiteEval_standard_eq_zero (n : ℕ) (hn : 1 ≤ n) :
    ∫ x : ℝ, hermiteEval n x ∂gaussianReal (0 : ℝ) (1 : ℝ≥0) = 0 := by
  have hmap := half_gaussian_map_sqrt_two
  rw [← hmap]
  have htransport := MeasureTheory.integral_map
    ((measurable_const.mul measurable_id).aemeasurable)
    ((continuous_hermiteEval n).measurable.aestronglyMeasurable)
    (μ := gaussianReal (0 : ℝ) halfVariance) (φ := fun x : ℝ => Real.sqrt 2 * x)
    (f := hermiteEval n)
  rw [htransport]
  simpa [Function.comp, mul_comm] using integral_hermiteEval_sqrt_two_half_eq_zero n hn

private theorem continuous_wickMonomial (n : ℕ) (c : ℝ) :
    Continuous (fun x : ℝ => wickMonomial n c x) := by
  match n with
  | 0 => simpa [wickMonomial] using continuous_const
  | 1 => simpa [wickMonomial] using continuous_id
  | n + 2 =>
      simpa [wickMonomial_succ_succ] using
        (continuous_id.mul (continuous_wickMonomial (n + 1) c)).sub
          (continuous_const.mul (continuous_wickMonomial n c))

private lemma gaussianReal_map_sqrt_variance (σ_sq : ℝ) (hσ : 0 < σ_sq) :
    MeasureTheory.Measure.map (fun x : ℝ => Real.sqrt σ_sq * x)
      (gaussianReal (0 : ℝ) (1 : ℝ≥0)) =
      gaussianReal (0 : ℝ) σ_sq.toNNReal := by
  calc
    MeasureTheory.Measure.map (fun x : ℝ => Real.sqrt σ_sq * x)
        (gaussianReal (0 : ℝ) (1 : ℝ≥0)) =
        gaussianReal (Real.sqrt σ_sq * (0 : ℝ))
          (⟨Real.sqrt σ_sq ^ 2, sq_nonneg _⟩ * (1 : ℝ≥0)) := by
          simpa using
            (gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (c := Real.sqrt σ_sq))
    _ = gaussianReal (0 : ℝ) σ_sq.toNNReal := by
      congr 1
      · ring
      · apply NNReal.coe_injective
        simp [Real.sq_sqrt hσ.le, Real.coe_toNNReal σ_sq hσ.le]

private lemma wickMonomial_sqrt_mul_eq (n : ℕ) (σ_sq : ℝ) (hσ : 0 < σ_sq) (x : ℝ) :
    wickMonomial n σ_sq (Real.sqrt σ_sq * x) =
      σ_sq ^ ((n : ℝ) / 2) * hermiteEval n x := by
  rw [wickMonomial_eq_hermite n σ_sq hσ (Real.sqrt σ_sq * x)]
  congr 1
  rw [mul_comm, mul_div_assoc, div_self (by exact ne_of_gt (Real.sqrt_pos.mpr hσ)), mul_one]

theorem gaussian_hermite_zero_mean (σ_sq : ℝ) (hσ : 0 < σ_sq) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun t => wickMonomial n σ_sq t) (gaussianReal (0 : ℝ) σ_sq.toNNReal) ∧
      ∫ t, wickMonomial n σ_sq t ∂gaussianReal (0 : ℝ) σ_sq.toNNReal = 0 := by
  have hmap := gaussianReal_map_sqrt_variance σ_sq hσ
  have hstd_int : Integrable (hermiteEval n) (gaussianReal (0 : ℝ) (1 : ℝ≥0)) :=
    integrable_hermiteEval_standard n
  have hstd_zero : ∫ x : ℝ, hermiteEval n x ∂gaussianReal (0 : ℝ) (1 : ℝ≥0) = 0 :=
    integral_hermiteEval_standard_eq_zero n hn
  have hint_comp :
      Integrable
        (fun x : ℝ => wickMonomial n σ_sq (Real.sqrt σ_sq * x))
        (gaussianReal (0 : ℝ) (1 : ℝ≥0)) := by
    have hscaled_int :
        Integrable
          (fun x : ℝ => σ_sq ^ ((n : ℝ) / 2) * hermiteEval n x)
          (gaussianReal (0 : ℝ) (1 : ℝ≥0)) := hstd_int.const_mul (σ_sq ^ ((n : ℝ) / 2))
    refine hscaled_int.congr ?_
    refine MeasureTheory.ae_of_all _ (fun x => ?_)
    symm
    exact wickMonomial_sqrt_mul_eq n σ_sq hσ x
  have hzero_comp :
      ∫ x : ℝ, wickMonomial n σ_sq (Real.sqrt σ_sq * x) ∂gaussianReal (0 : ℝ) (1 : ℝ≥0) = 0 := by
    calc
      ∫ x : ℝ, wickMonomial n σ_sq (Real.sqrt σ_sq * x) ∂gaussianReal (0 : ℝ) (1 : ℝ≥0)
          = ∫ x : ℝ, σ_sq ^ ((n : ℝ) / 2) * hermiteEval n x ∂gaussianReal (0 : ℝ) (1 : ℝ≥0) := by
              refine MeasureTheory.integral_congr_ae ?_
              exact MeasureTheory.ae_of_all _ (fun x => wickMonomial_sqrt_mul_eq n σ_sq hσ x)
      _ = σ_sq ^ ((n : ℝ) / 2) * ∫ x : ℝ, hermiteEval n x ∂gaussianReal (0 : ℝ) (1 : ℝ≥0) := by
            rw [MeasureTheory.integral_const_mul]
      _ = 0 := by simp [hstd_zero]
  constructor
  · rw [← hmap]
    refine (MeasureTheory.integrable_map_measure
      (g := fun t : ℝ => wickMonomial n σ_sq t)
      ((continuous_wickMonomial n σ_sq).measurable.aestronglyMeasurable)
      ((measurable_const.mul measurable_id).aemeasurable)).2 ?_
    simpa [Function.comp, mul_comm] using hint_comp
  · rw [← hmap]
    have htransport := MeasureTheory.integral_map
      ((measurable_const.mul measurable_id).aemeasurable)
      ((continuous_wickMonomial n σ_sq).measurable.aestronglyMeasurable)
      (μ := gaussianReal (0 : ℝ) (1 : ℝ≥0)) (φ := fun x : ℝ => Real.sqrt σ_sq * x)
      (f := fun t : ℝ => wickMonomial n σ_sq t)
    rw [htransport]
    simpa [Function.comp, mul_comm] using hzero_comp

end Pphi2