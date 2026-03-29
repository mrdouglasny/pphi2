/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# IR Tightness: Prokhorov Extraction for Lt → ∞

Proves tightness of the cylinder pullback measures as Lt → ∞ and
extracts a convergent subsequence via Prokhorov's theorem.

The structure follows `AsymTorusInteractingLimit.lean` exactly:
uniform second moments → Mitoma-Chebyshev → tightness → Prokhorov.

## Main results

- `cylinderIR_tight` — the family of pulled-back measures is tight
- `cylinderIRLimit_exists` — existence of the IR limit measure

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII
- Glimm-Jaffe, *Quantum Physics*, §19
-/

import Pphi2.IRLimit.GreenFunctionComparison
import Pphi2.IRLimit.UniformExponentialMoment
import Pphi2.AsymTorus.AsymTorusOS
import GaussianField.Tightness
import GaussianField.ConfigurationEmbedding

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory Filter

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]

private lemma cylinderExpEval_integrable
    (μ : Measure (Configuration (CylinderTestFunction Ls)))
    [IsProbabilityMeasure μ] (g : CylinderTestFunction Ls) :
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      Complex.exp (Complex.I * ↑(ω g))) μ := by
  apply (integrable_const (1 : ℂ)).mono
  · exact (Complex.continuous_exp.measurable.comp
      (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
        (configuration_eval_measurable g)))).aestronglyMeasurable
  · apply ae_of_all
    intro ω
    simp only [norm_one]
    rw [show Complex.I * ↑(ω g) = ↑(ω g) * Complex.I from mul_comm _ _]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I (ω g))

private lemma cylinderExpIntegral_re_eq_integral_cos
    (μ : Measure (Configuration (CylinderTestFunction Ls)))
    [IsProbabilityMeasure μ] (g : CylinderTestFunction Ls) :
    (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).re =
    ∫ ω : Configuration (CylinderTestFunction Ls), Real.cos (ω g) ∂μ := by
  rw [show (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).re =
    Complex.reCLM (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ) from rfl]
  rw [← ContinuousLinearMap.integral_comp_comm Complex.reCLM
    (cylinderExpEval_integrable Ls μ g)]
  congr 1 with ω
  simp only [Complex.reCLM_apply, mul_comm Complex.I, Complex.exp_mul_I,
    Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.sin_ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  exact Complex.cos_ofReal_re (ω g)

private lemma cylinderExpIntegral_im_eq_integral_sin
    (μ : Measure (Configuration (CylinderTestFunction Ls)))
    [IsProbabilityMeasure μ] (g : CylinderTestFunction Ls) :
    (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).im =
    ∫ ω : Configuration (CylinderTestFunction Ls), Real.sin (ω g) ∂μ := by
  rw [show (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).im =
    Complex.imCLM (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ) from rfl]
  rw [← ContinuousLinearMap.integral_comp_comm Complex.imCLM
    (cylinderExpEval_integrable Ls μ g)]
  congr 1 with ω
  simp only [Complex.imCLM_apply, mul_comm Complex.I, Complex.exp_mul_I,
    Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
  ring

/-! ## IR Limit Existence

Given a sequence of time periods `Lt_n → ∞` and for each one an interacting
measure `μ_n` on `AsymTorusTestFunction Lt_n Ls` satisfying OS0–OS2 (from
the UV limit), the pulled-back cylinder measures are tight and have a
convergent subsequence. -/

/-- The IR limit measure on the cylinder S¹_{Ls} × ℝ exists.

Given a sequence of time periods `Lt : ℕ → ℝ` with `Lt n → ∞` and
interacting measures `μ_n` on the corresponding asymmetric tori, the
pulled-back cylinder measures `cylinderPullbackMeasure (Lt n) Ls (μ n)`
have a weakly convergent subsequence.

**Proof sketch**:
1. Uniform second moment bound (from `cylinderIR_uniform_second_moment`)
2. Mitoma-Chebyshev tightness criterion (from gaussian-field)
3. Prokhorov's theorem (Polish space + tight → subsequential limit)

The limit is a probability measure on `Configuration (CylinderTestFunction Ls)`.

Convergence is stated for the **characteristic functional** (not just
first moments), since this is what's needed for OS axiom transfer. By
the Lévy continuity theorem on nuclear spaces, characteristic functional
convergence is equivalent to weak convergence. -/
theorem cylinderIRLimit_exists
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop)
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)))
    (hμ_prob : ∀ n, IsProbabilityMeasure (μ n))
    (hμ_os : ∀ n, @AsymSatisfiesTorusOS (Lt n) Ls _ _ (μ n) (hμ_prob n)) :
    ∃ (φ : ℕ → ℕ) (ν : Measure (Configuration (CylinderTestFunction Ls))),
    StrictMono φ ∧ IsProbabilityMeasure ν ∧
    -- Characteristic functional convergence
    (∀ (f : CylinderTestFunction Ls),
    Tendsto (fun n =>
      ∫ ω, Complex.exp (Complex.I * ↑(ω f))
        ∂(cylinderPullbackMeasure (Lt (φ n)) Ls (μ (φ n))))
      atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν))) := by
  -- Step 1: Uniform second moment bound from cylinderIR_uniform_second_moment
  obtain ⟨C, q, hC, hq_cont, h_moment⟩ :=
    cylinderIR_uniform_second_moment Ls P mass hmass
  obtain ⟨K, Cexp, qexp, hK_pos, hCexp_pos, hqexp_cont, h_exp⟩ :=
    cylinderIR_uniform_exponential_moment Ls P mass hmass
  have hLt_ge_one : ∀ᶠ n in atTop, 1 ≤ Lt n := tendsto_atTop.1 hLt_tend 1
  rcases (eventually_atTop.1 hLt_ge_one) with ⟨N0, hN0⟩
  let νseq : ℕ → Measure (Configuration (CylinderTestFunction Ls)) := fun n =>
    cylinderPullbackMeasure (Lt (n + N0)) Ls (μ (n + N0))
  have hν_prob : ∀ n, IsProbabilityMeasure (νseq n) := by
    intro n
    dsimp [νseq]
    haveI : Fact (0 < Lt (n + N0)) := hLt (n + N0)
    haveI : IsProbabilityMeasure (μ (n + N0)) := hμ_prob (n + N0)
    have hmeas : Measurable (cylinderPullback (Lt (n + N0)) Ls) :=
      configuration_measurable_of_eval_measurable _
        (fun φ => configuration_eval_measurable _)
    exact Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have hν_int :
      ∀ (f : CylinderTestFunction Ls) (n : ℕ),
        Integrable (fun ω : Configuration (CylinderTestFunction Ls) => (ω f) ^ 2) (νseq n) := by
    intro f n
    haveI : Fact (0 < Lt (n + N0)) := hLt (n + N0)
    haveI : IsProbabilityMeasure (μ (n + N0)) := hμ_prob (n + N0)
    have h_exp_int :
        Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
          Real.exp (|ω ((2 : ℝ) • f)|)) (νseq n) :=
      (h_exp (Lt (n + N0)) (hN0 (n + N0) (Nat.le_add_left _ _))
        (μ (n + N0)) (hμ_os (n + N0)) ((2 : ℝ) • f)).1
    refine h_exp_int.mono'
      (((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable)
      (ae_of_all _ fun ω => ?_)
    have h_abs_le : |ω f| ≤ Real.exp |ω f| := by
      calc
        |ω f| ≤ 1 + |ω f| := by linarith
        _ ≤ Real.exp |ω f| := by simpa [add_comm] using Real.add_one_le_exp (|ω f|)
    calc
      ‖(ω f) ^ 2‖ = (ω f) ^ 2 := by rw [Real.norm_of_nonneg (sq_nonneg _)]
      _ = |ω f| ^ 2 := by rw [sq_abs]
      _ ≤ (Real.exp |ω f|) ^ 2 := by
        exact pow_le_pow_left₀ (abs_nonneg _) h_abs_le 2
      _ = Real.exp (2 * |ω f|) := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring_nf
      _ = Real.exp (|ω ((2 : ℝ) • f)|) := by
        rw [map_smul, smul_eq_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hν_moments :
      ∀ f : CylinderTestFunction Ls, ∃ C' : ℝ, ∀ n,
        ∫ ω : Configuration (CylinderTestFunction Ls), (ω f) ^ 2 ∂(νseq n) ≤ C' := by
    intro f
    refine ⟨C * q f ^ 2, fun n => ?_⟩
    haveI : Fact (0 < Lt (n + N0)) := hLt (n + N0)
    haveI : IsProbabilityMeasure (μ (n + N0)) := hμ_prob (n + N0)
    simpa [νseq] using
      h_moment (Lt (n + N0)) (hN0 (n + N0) (Nat.le_add_left _ _))
        (μ (n + N0)) (hμ_os (n + N0)) f
  have hν_tight : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set (Configuration (CylinderTestFunction Ls)), IsCompact K ∧
        ∀ n, 1 - ε ≤ ((νseq n) K).toReal := by
    intro ε hε
    exact configuration_tight_of_uniform_second_moments
      νseq hν_prob hν_int hν_moments ε hε
  obtain ⟨φtail, ν, hφtail, hν_lim_prob, hconv⟩ :=
    prokhorov_configuration νseq hν_prob hν_tight
  have hcf_tail : ∀ (f : CylinderTestFunction Ls),
      Tendsto (fun n =>
        ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂(νseq (φtail n)))
      atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν)) := by
    intro f
    have hcos : Tendsto
        (fun n => ∫ ω, Real.cos (ω f) ∂(νseq (φtail n)))
        atTop (nhds (∫ ω, Real.cos (ω f) ∂ν)) :=
      hconv (fun ω => Real.cos (ω f))
        (Real.continuous_cos.comp (WeakDual.eval_continuous f))
        ⟨1, fun ω => Real.abs_cos_le_one (ω f)⟩
    have hsin : Tendsto
        (fun n => ∫ ω, Real.sin (ω f) ∂(νseq (φtail n)))
        atTop (nhds (∫ ω, Real.sin (ω f) ∂ν)) :=
      hconv (fun ω => Real.sin (ω f))
        (Real.continuous_sin.comp (WeakDual.eval_continuous f))
        ⟨1, fun ω => Real.abs_sin_le_one (ω f)⟩
    have h_re : Tendsto
        (fun n => (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂(νseq (φtail n))).re)
        atTop (nhds ((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).re)) := by
      have h_re_eq :
          (fun n => (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂(νseq (φtail n))).re) =
          fun n => ∫ ω, Real.cos (ω f) ∂(νseq (φtail n)) := by
        funext n
        haveI : IsProbabilityMeasure (νseq (φtail n)) := hν_prob (φtail n)
        exact cylinderExpIntegral_re_eq_integral_cos Ls (νseq (φtail n)) f
      have h_re_lim :
          (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).re =
          ∫ ω, Real.cos (ω f) ∂ν := by
        haveI : IsProbabilityMeasure ν := hν_lim_prob
        exact cylinderExpIntegral_re_eq_integral_cos Ls ν f
      rw [h_re_eq, h_re_lim]
      exact hcos
    have h_im : Tendsto
        (fun n => (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂(νseq (φtail n))).im)
        atTop (nhds ((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).im)) := by
      have h_im_eq :
          (fun n => (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂(νseq (φtail n))).im) =
          fun n => ∫ ω, Real.sin (ω f) ∂(νseq (φtail n)) := by
        funext n
        haveI : IsProbabilityMeasure (νseq (φtail n)) := hν_prob (φtail n)
        exact cylinderExpIntegral_im_eq_integral_sin Ls (νseq (φtail n)) f
      have h_im_lim :
          (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).im =
          ∫ ω, Real.sin (ω f) ∂ν := by
        haveI : IsProbabilityMeasure ν := hν_lim_prob
        exact cylinderExpIntegral_im_eq_integral_sin Ls ν f
      rw [h_im_eq, h_im_lim]
      exact hsin
    have h_pair : Tendsto
        (fun n =>
          ((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂(νseq (φtail n))).re,
           (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂(νseq (φtail n))).im))
        atTop
        (nhds
          (((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).re),
           ((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).im))) :=
      h_re.prodMk_nhds h_im
    have h_complex : Tendsto
        (fun n =>
          Complex.equivRealProdCLM.symm
            ((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂(νseq (φtail n))).re,
             (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂(νseq (φtail n))).im))
        atTop
        (nhds
          (Complex.equivRealProdCLM.symm
            (((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).re),
             ((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).im)))) :=
      (Complex.equivRealProdCLM.symm.continuous.tendsto
        (((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).re),
         ((∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν).im))).comp h_pair
    simpa [Complex.equivRealProdCLM_symm_apply, Complex.re_add_im] using h_complex
  let φ : ℕ → ℕ := fun n => φtail n + N0
  have hφ : StrictMono φ := by
    intro a b hab
    exact Nat.add_lt_add_right (hφtail hab) N0
  refine ⟨φ, ν, hφ, hν_lim_prob, ?_⟩
  intro f
  simpa [φ, νseq] using hcf_tail f
  -- The proof chains through proved gaussian-field infrastructure:
  -- Step 1: cylinderIR_uniform_second_moment → ∀ f, ∃ C(f), ∀ n, ∫ (ω f)² ≤ C(f)
  -- Step 2: configuration_tight_of_uniform_second_moments → tightness
  -- Step 3: prokhorov_configuration → (φ, ν) with weak convergence
  -- Step 4: weak convergence → CF convergence (cos/sin are bounded continuous)
  --
  -- The plumbing involves: defining the pulled-back measure sequence,
  -- showing probability measure + integrability + moment bounds, then
  -- chaining the three gaussian-field theorems.

end Pphi2
