/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniform Exponential Moment Bound for Cylinder Pullback

Provides the uniform-in-Lt exponential moment bound
`E_{ν_Lt}[exp(|ω(f)|)] ≤ K · exp(C · q(f)²)` needed for OS0 analyticity.

This is pulled through from the AsymTorus Nelson/Fröhlich bound via
the cylinder-to-torus embedding.

## Mathematical background

The torus interacting measure satisfies (from `asymTorusInteracting_exponentialMomentBound`):
  `E_{μ_Lt}[exp(|ω(g)|)] ≤ K · exp(σ²_Lt(g))`

For `g = embed(f)` where `f` is a cylinder test function:
  `σ²_Lt(embed f) ≤ C · q(f)²`  (from the method of images bound)

Combined: `E_{ν_Lt}[exp(|ω(f)|)] ≤ K · exp(C · q(f)²)` uniformly in Lt.

Together with bounded-continuous convergence of the extracted limit, this is
sufficient for the dominated integral proof of OS0 analyticity.
-/

import Pphi2.AsymTorus.MomentBoundOS1

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory Filter

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]

/-- Uniform exponential moment bound for the cylinder pullback measures.

For any cylinder test function `f`, the exponential moment under the
pulled-back torus interacting measure is bounded uniformly in Lt:

  `∫ exp(|ω(f)|) dν_Lt ≤ K · exp(C · q(f)²)`

where `q` is a continuous seminorm on `CylinderTestFunction Ls` and
`K, C > 0` are constants independent of `f` and `Lt`.

This theorem deliberately keeps the needed analytic input explicit. The
abstract `AsymSatisfiesTorusOS.os1` clause has a bound by an unspecified
continuous seminorm, which is too weak to imply uniformity as `Lt → ∞`.
Assuming instead the Green-controlled bound `MeasureHasGreenMomentBound` with
constants uniform in `Lt`, `cylinderPullback_expMoment_uniform_bound` composes
that input with the method-of-images estimate. -/
theorem cylinderIR_uniform_exponential_moment
    (mass : ℝ) (hmass : 0 < mass)
    (KG CG : ℝ) (hKG_pos : 0 < KG) (hCG_pos : 0 < CG) :
    ∃ (K C : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls)),
    0 < K ∧ 0 < C ∧ Continuous q ∧
    ∀ (Lt : ℝ) [Fact (0 < Lt)] (_ : 1 ≤ Lt)
      (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
      [IsProbabilityMeasure μ]
      (_ : MeasureHasGreenMomentBound Ls mass hmass KG CG μ)
      (f : CylinderTestFunction Ls),
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      Real.exp (|ω f|)) (cylinderPullbackMeasure Lt Ls μ) ∧
    ∫ ω : Configuration (CylinderTestFunction Ls),
      Real.exp (|ω f|) ∂(cylinderPullbackMeasure Lt Ls μ) ≤
    K * Real.exp (C * q f ^ 2) := by
  obtain ⟨K, C, q, hK, hC, hq_cont, hbound⟩ :=
    cylinderPullback_expMoment_uniform_bound Ls mass hmass KG CG hKG_pos hCG_pos
  refine ⟨K, C, q, hK, hC, hq_cont, ?_⟩
  intro Lt _ hLt μ _ hμ_green f
  exact hbound Lt hLt μ hμ_green f

/-- Elementary inequality `x² ≤ 2 e^|x|`, used to extract a polynomial
    moment from the exponential moment. -/
private lemma sq_le_two_mul_exp_abs (x : ℝ) : x ^ 2 ≤ 2 * Real.exp |x| := by
  have h := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
  have hx_nn : 0 ≤ |x| := abs_nonneg x
  have h_sq : |x| ^ 2 ≤ 2 * Real.exp |x| := by linarith [h, hx_nn]
  rwa [sq_abs] at h_sq

/-- **Uniform second moment bound** for cylinder pullback measures.

For each fixed cylinder test function `f`, the second moment under the
pulled-back torus interacting measure is finite, and is bounded
**uniformly in `Lt ≥ 1`** by the additive expression
  `∫ (ω f)² dν_{Lt} ≤ C₁ · q(f)² + C₂`,
where `C₁, C₂ > 0` and the seminorm `q` are independent of `Lt` and `f`.

The bound is **per-f** (not a uniform Hilbertian-seminorm bound in the
Mitoma sense) and the additive `C₂` is **essential** to the scaling
argument used here — the strict multiplicative form `C · q(f)²` would
require a separate a.s.-vanishing argument for the `q(f) = 0` corner.
The IR-tightness consumer (`IRTightness.lean`) only needs an
`f`-dependent bound uniform in `Lt`, so this additive form suffices.

The conclusion bundles `Integrable (fun ω => (ω f)²) ν` so the consumer
gets integrability without a separate derivation; both come from the
same exp-moment input (`cylinderIR_uniform_exponential_moment`) without
circularity (integrability uses `Real.exp |ω f|` as dominator;
the bound uses the rescaled `Real.exp |ω(λ•f)|`).

**Proof of the bound.** Apply `cylinderIR_uniform_exponential_moment` to
the scaled test function `λ • f` (any `λ > 0`):
  `∫ exp(|ω(λf)|) dν ≤ K · exp(C λ² q(f)²)`.
The pointwise inequality `(λx)² ≤ 2 exp(λ|x|)` (from
`Real.quadratic_le_exp_of_nonneg`) gives
  `λ² ∫ (ω f)² dν ≤ 2K · exp(C λ² q(f)²)`.
Choose `λ² = 1 / (C (q(f)² + 1))`, so `Cλ²q(f)² ≤ 1`:
  `∫ (ω f)² dν ≤ 2K · C · (q(f)² + 1) · e = (2KCe) q(f)² + (2KCe)`.

Hence `C₁ = C₂ = 2KCe`.

**Proof of integrability.** Apply the exp-moment at `λ = 1` (i.e. the
test function `f` itself) to get `Integrable (Real.exp ∘ |· f|) ν`. By
the pointwise bound `(ω f)² ≤ 2 · Real.exp |ω f|` (the `λ = 1` case of
the same helper) and `Integrable.mono'` against the AE-strong
measurability of `(· f) ^ 2` (composition of `configuration_eval_measurable`
with `pow_const 2`), `(ω f)²` is integrable. -/
theorem cylinderIR_uniform_second_moment
    (mass : ℝ) (hmass : 0 < mass)
    (KG CG : ℝ) (hKG_pos : 0 < KG) (hCG_pos : 0 < CG) :
    ∃ (C₁ C₂ : ℝ) (q : Seminorm ℝ (CylinderTestFunction Ls)),
    0 < C₁ ∧ 0 < C₂ ∧ Continuous q ∧
    ∀ (Lt : ℝ) [Fact (0 < Lt)] (_ : 1 ≤ Lt)
      (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
      [IsProbabilityMeasure μ]
      (_ : MeasureHasGreenMomentBound Ls mass hmass KG CG μ)
      (f : CylinderTestFunction Ls),
    Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      (ω f) ^ 2) (cylinderPullbackMeasure Lt Ls μ) ∧
    ∫ ω : Configuration (CylinderTestFunction Ls),
      (ω f) ^ 2 ∂(cylinderPullbackMeasure Lt Ls μ) ≤
    C₁ * q f ^ 2 + C₂ := by
  obtain ⟨K, C, q, hK, hC, hq_cont, hbound⟩ :=
    cylinderIR_uniform_exponential_moment Ls mass hmass KG CG hKG_pos hCG_pos
  refine ⟨2 * K * C * Real.exp 1, 2 * K * C * Real.exp 1, q,
    by positivity, by positivity, hq_cont, ?_⟩
  intro Lt _ hLt μ _ hμ_green f
  set ν := cylinderPullbackMeasure Lt Ls μ with hν_def
  set s : ℝ := q f with hs_def
  have hs_nn : 0 ≤ s := apply_nonneg q f
  -- Choose scaling: λ² = 1 / (C (s² + 1))
  set α : ℝ := C * (s ^ 2 + 1) with hα_def
  have hα_pos : 0 < α := by rw [hα_def]; positivity
  set lam : ℝ := Real.sqrt (1 / α) with hlam_def
  have hlam_pos : 0 < lam :=
    Real.sqrt_pos.mpr (one_div_pos.mpr hα_pos)
  have hlam_sq : lam ^ 2 = 1 / α :=
    Real.sq_sqrt (one_div_pos.mpr hα_pos).le
  have hlam2_pos : (0:ℝ) < lam ^ 2 := by positivity
  -- Apply exp moment at λ = 1 (for integrability of (ωf)²)
  obtain ⟨h_int_one, _⟩ := hbound Lt hLt μ hμ_green f
  -- Apply exp moment to (lam • f) (for the moment bound)
  obtain ⟨h_int_lam, h_bd_lam⟩ := hbound Lt hLt μ hμ_green (lam • f)
  -- AE-strong measurability of (ω f)² via configuration_eval_measurable
  have h_meas_sq : AEStronglyMeasurable
      (fun ω : Configuration (CylinderTestFunction Ls) => (ω f) ^ 2) ν :=
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
  -- Integrability of (ω f)² via domination by 2 * Real.exp |ω f|
  have h_int_sq : Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
      (ω f) ^ 2) ν := by
    refine (h_int_one.const_mul 2).mono' h_meas_sq (ae_of_all _ fun ω => ?_)
    have h := sq_le_two_mul_exp_abs (ω f)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact h
  refine ⟨h_int_sq, ?_⟩
  -- Linearity of ω: ω(λ•f) = λ * ω f
  have h_eval : ∀ ω : Configuration (CylinderTestFunction Ls),
      ω (lam • f) = lam * ω f := by
    intro ω; simp [map_smul]
  -- Seminorm scaling: q(λ•f)² = λ² * s²
  have h_q : q (lam • f) ^ 2 = lam ^ 2 * s ^ 2 := by
    rw [map_smul_eq_mul q lam f, mul_pow, Real.norm_eq_abs, sq_abs, hs_def]
  -- Pointwise: λ² (ω f)² ≤ 2 * exp(|ω(λ•f)|)
  have h_pt : ∀ ω : Configuration (CylinderTestFunction Ls),
      lam ^ 2 * (ω f) ^ 2 ≤ 2 * Real.exp |ω (lam • f)| := by
    intro ω
    have h := sq_le_two_mul_exp_abs (lam * ω f)
    have h_pow : (lam * ω f) ^ 2 = lam ^ 2 * (ω f) ^ 2 := by ring
    have h_abs : |lam * ω f| = |ω (lam • f)| := by rw [h_eval ω]
    rw [h_pow, h_abs] at h
    exact h
  -- Integrate the pointwise inequality
  have h_2exp_int :
      Integrable (fun ω => 2 * Real.exp |ω (lam • f)|) ν := h_int_lam.const_mul 2
  have h_lhs_nn :
      0 ≤ᵐ[ν] fun ω : Configuration (CylinderTestFunction Ls) =>
        lam ^ 2 * (ω f) ^ 2 :=
    Filter.Eventually.of_forall fun ω => by positivity
  have h_pt_ae :
      (fun ω : Configuration (CylinderTestFunction Ls) =>
        lam ^ 2 * (ω f) ^ 2) ≤ᵐ[ν]
      (fun ω => 2 * Real.exp |ω (lam • f)|) :=
    Filter.Eventually.of_forall h_pt
  have h_int_le :
      ∫ ω, lam ^ 2 * (ω f) ^ 2 ∂ν ≤
      ∫ ω, 2 * Real.exp |ω (lam • f)| ∂ν :=
    integral_mono_of_nonneg h_lhs_nn h_2exp_int h_pt_ae
  rw [integral_const_mul, integral_const_mul] at h_int_le
  -- Combine with exponential moment bound
  have h_chain :
      lam ^ 2 * ∫ ω, (ω f) ^ 2 ∂ν ≤
      2 * (K * Real.exp (C * q (lam • f) ^ 2)) :=
    h_int_le.trans (by gcongr)
  rw [h_q] at h_chain
  -- Now: lam² * A ≤ 2K * exp(C * lam² * s²) where A = ∫(ωf)²
  -- Bound exp(C lam² s²) ≤ exp(1) since C lam² s² ≤ 1
  have hCls_le_1 : C * lam ^ 2 * s ^ 2 ≤ 1 := by
    rw [hlam_sq]
    have hs2_le : C * s ^ 2 ≤ α := by
      change C * s ^ 2 ≤ C * (s ^ 2 + 1)
      have : s ^ 2 ≤ s ^ 2 + 1 := by linarith
      exact mul_le_mul_of_nonneg_left this hC.le
    rw [show C * (1 / α) * s ^ 2 = C * s ^ 2 / α by ring,
        div_le_one hα_pos]
    exact hs2_le
  have h_exp_le : Real.exp (C * lam ^ 2 * s ^ 2) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr hCls_le_1
  -- A ≤ (2K/lam²) exp(C lam² s²) ≤ (2K/lam²) e = 2K * α * e = 2KC(s²+1) e
  --   = 2KCe s² + 2KCe = C₁ s² + C₂
  have h_A_le_div :
      ∫ ω, (ω f) ^ 2 ∂ν ≤
      (2 * K / lam ^ 2) * Real.exp (C * lam ^ 2 * s ^ 2) := by
    have h_arg_eq : C * (lam ^ 2 * s ^ 2) = C * lam ^ 2 * s ^ 2 := by ring
    have h_chain' : lam ^ 2 * ∫ ω, (ω f) ^ 2 ∂ν ≤
        2 * K * Real.exp (C * lam ^ 2 * s ^ 2) := by
      calc lam ^ 2 * ∫ ω, (ω f) ^ 2 ∂ν
          ≤ 2 * (K * Real.exp (C * (lam ^ 2 * s ^ 2))) := h_chain
        _ = 2 * K * Real.exp (C * lam ^ 2 * s ^ 2) := by rw [h_arg_eq]; ring
    rw [div_mul_eq_mul_div, le_div_iff₀ hlam2_pos, mul_comm _ (lam ^ 2)]
    exact h_chain'
  calc ∫ ω, (ω f) ^ 2 ∂ν
      ≤ (2 * K / lam ^ 2) * Real.exp (C * lam ^ 2 * s ^ 2) := h_A_le_div
    _ ≤ (2 * K / lam ^ 2) * Real.exp 1 := by
        have : 0 ≤ 2 * K / lam ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left h_exp_le this
    _ = 2 * K * α * Real.exp 1 := by
        rw [hlam_sq]
        field_simp
    _ = 2 * K * C * (s ^ 2 + 1) * Real.exp 1 := by
        rw [hα_def]; ring
    _ = 2 * K * C * Real.exp 1 * s ^ 2 + 2 * K * C * Real.exp 1 := by ring

end Pphi2
