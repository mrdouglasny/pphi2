/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# IR Tightness: Prokhorov Extraction for Lt → ∞

Proves tightness of the cylinder pullback measures as Lt → ∞ and
extracts a convergent subsequence via Prokhorov's theorem.

The structure follows `AsymTorusInteractingLimit.lean` exactly:
uniform second moments → Mitoma-Chebyshev → tightness → Prokhorov.

## Main result

- `cylinderIRLimit_exists` — existence of an IR-limit subsequence, conditional
  on the explicit eventual Green-controlled moment input
  `AsymTorusSequenceHasUniformGreenMomentBound`.

## References

- Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII
- Glimm-Jaffe, *Quantum Physics*, §19
-/

import Pphi2.IRLimit.GreenFunctionComparison
import Pphi2.IRLimit.UniformExponentialMoment
import GaussianField.Tightness
import GaussianField.ConfigurationEmbedding

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory Filter

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]

/-! ## Uniform Green-moment input for the IR family -/

/-- The remaining volume-uniform analytic input for Route B′.

Eventually, every asymmetric-torus measure in the family has the
Green-controlled exponential moment bound with the same constants `KG, CG`.
This is the precise tail hypothesis needed for cylinder tightness and OS0; the
finite initial segment is irrelevant to the IR limit and is therefore not
included in the predicate. The separate assumption `Lt → ∞` supplies `Lt ≥ 1`
on a tail when consumers need the method-of-images bound. -/
def AsymTorusSequenceHasUniformGreenMomentBound
    (mass : ℝ) (hmass : 0 < mass) (KG CG : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls))) : Prop :=
  ∀ᶠ n in atTop,
    @MeasureHasGreenMomentBound Ls _ (Lt n) (hLt n) mass hmass KG CG (μ n)

/-- A pointwise Green-moment bound is, in particular, the eventual sequence
input used by the IR-limit tightness theorem. -/
theorem AsymTorusSequenceHasUniformGreenMomentBound.of_forall
    (mass : ℝ) (hmass : 0 < mass) (KG CG : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)))
    (h : ∀ n,
      @MeasureHasGreenMomentBound Ls _ (Lt n) (hLt n) mass hmass KG CG (μ n)) :
    AsymTorusSequenceHasUniformGreenMomentBound Ls mass hmass KG CG Lt hLt μ :=
  Filter.Eventually.of_forall h

/-- The previous stronger `Lt ≥ 1`-indexed shape implies the honest eventual
Green-moment input once the periods tend to infinity. -/
theorem AsymTorusSequenceHasUniformGreenMomentBound.of_forall_ge_one
    (mass : ℝ) (hmass : 0 < mass) (KG CG : ℝ)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop)
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)))
    (h : ∀ n, 1 ≤ Lt n →
      @MeasureHasGreenMomentBound Ls _ (Lt n) (hLt n) mass hmass KG CG (μ n)) :
    AsymTorusSequenceHasUniformGreenMomentBound Ls mass hmass KG CG Lt hLt μ :=
  (tendsto_atTop.1 hLt_tend 1).mono h

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
  simpa using configuration_expIntegral_re_eq_integral_cos μ g

private lemma cylinderExpIntegral_im_eq_integral_sin
    (μ : Measure (Configuration (CylinderTestFunction Ls)))
    [IsProbabilityMeasure μ] (g : CylinderTestFunction Ls) :
    (∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ).im =
    ∫ ω : Configuration (CylinderTestFunction Ls), Real.sin (ω g) ∂μ := by
  simpa using configuration_expIntegral_im_eq_integral_sin μ g

/-! ## IR Limit Existence

Given a sequence of time periods `Lt_n → ∞` and measures `μ_n` on
`AsymTorusTestFunction Lt_n Ls` satisfying the explicit eventual Green-moment
input, the pulled-back cylinder measures are tight and have a convergent
subsequence. -/

/-- The IR limit measure on the cylinder S¹_{Ls} × ℝ exists.

Given a sequence of time periods `Lt : ℕ → ℝ` with `Lt n → ∞`, measures `μ_n`
on the corresponding asymmetric tori, and an eventual Green-controlled
exponential moment bound, the pulled-back cylinder measures
`cylinderPullbackMeasure (Lt n) Ls (μ n)` have a weakly convergent subsequence.

**Proof sketch**:
1. Uniform second moment bound (from `cylinderIR_uniform_second_moment`)
2. Mitoma-Chebyshev tightness criterion (from gaussian-field)
3. `prokhorov_configuration` (tightness → subsequential bounded-continuous
   convergence on configuration space)

The limit is a probability measure on `Configuration (CylinderTestFunction Ls)`.

Convergence is stated both as bounded-continuous convergence and as
characteristic-functional convergence, since the latter is what the OS axiom
transfer consumes. The characteristic-functional convergence is derived from
bounded-continuous convergence by the proved cos/sin decomposition below, not
by invoking an unformalized Lévy-continuity theorem. -/
theorem cylinderIRLimit_exists
    (mass : ℝ) (hmass : 0 < mass)
    (KG CG : ℝ) (hKG_pos : 0 < KG) (hCG_pos : 0 < CG)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop)
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)))
    (hμ_prob : ∀ n, IsProbabilityMeasure (μ n))
    (hμ_green : AsymTorusSequenceHasUniformGreenMomentBound Ls mass hmass KG CG Lt hLt μ) :
    ∃ (φ : ℕ → ℕ) (ν : Measure (Configuration (CylinderTestFunction Ls))),
    StrictMono φ ∧ IsProbabilityMeasure ν ∧
    -- Bounded-continuous convergence (full weak convergence)
    (∀ (g : Configuration (CylinderTestFunction Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n =>
        ∫ ω, g ω ∂(cylinderPullbackMeasure (Lt (φ n)) Ls (μ (φ n))))
        atTop (nhds (∫ ω, g ω ∂ν))) ∧
    -- Characteristic functional convergence
    (∀ (f : CylinderTestFunction Ls),
    Tendsto (fun n =>
      ∫ ω, Complex.exp (Complex.I * ↑(ω f))
        ∂(cylinderPullbackMeasure (Lt (φ n)) Ls (μ (φ n))))
      atTop (nhds (∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν))) := by
  -- Step 1: Uniform second moment bound from cylinderIR_uniform_second_moment
  -- (additive form `C₁ q(f)² + C₂`, derived from the Green-moment input)
  obtain ⟨C₁, C₂, q, hC₁, hC₂, hq_cont, h_moment⟩ :=
    cylinderIR_uniform_second_moment Ls mass hmass KG CG hKG_pos hCG_pos
  obtain ⟨K, Cexp, qexp, hK_pos, hCexp_pos, hqexp_cont, h_exp⟩ :=
    cylinderIR_uniform_exponential_moment Ls mass hmass KG CG hKG_pos hCG_pos
  have hLt_ge_one : ∀ᶠ n in atTop, 1 ≤ Lt n := tendsto_atTop.1 hLt_tend 1
  have h_green_tail : ∀ᶠ n in atTop,
      @MeasureHasGreenMomentBound Ls _ (Lt n) (hLt n) mass hmass KG CG (μ n) := by
    simpa [AsymTorusSequenceHasUniformGreenMomentBound] using hμ_green
  have h_tail : ∀ᶠ n in atTop,
      1 ≤ Lt n ∧
        @MeasureHasGreenMomentBound Ls _ (Lt n) (hLt n) mass hmass KG CG (μ n) :=
    hLt_ge_one.and h_green_tail
  rcases (eventually_atTop.1 h_tail) with ⟨N0, hN0⟩
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
    have htail_n := hN0 (n + N0) (Nat.le_add_left _ _)
    haveI : Fact (0 < Lt (n + N0)) := hLt (n + N0)
    haveI : IsProbabilityMeasure (μ (n + N0)) := hμ_prob (n + N0)
    have h_exp_int :
        Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
          Real.exp (|ω ((2 : ℝ) • f)|)) (νseq n) :=
      (h_exp (Lt (n + N0)) htail_n.1
        (μ (n + N0)) htail_n.2 ((2 : ℝ) • f)).1
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
    refine ⟨C₁ * q f ^ 2 + C₂, fun n => ?_⟩
    have htail_n := hN0 (n + N0) (Nat.le_add_left _ _)
    haveI : Fact (0 < Lt (n + N0)) := hLt (n + N0)
    haveI : IsProbabilityMeasure (μ (n + N0)) := hμ_prob (n + N0)
    simpa [νseq] using
      (h_moment (Lt (n + N0)) htail_n.1
        (μ (n + N0)) htail_n.2 f).2
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
  refine ⟨φ, ν, hφ, hν_lim_prob, ?_, ?_⟩
  · -- BC convergence: from prokhorov_configuration BC convergence, reindexed
    intro g hg_cont hg_bdd
    have := hconv g hg_cont hg_bdd
    simpa [φ, νseq] using this
  · -- CF convergence: from BC convergence via cos/sin
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
