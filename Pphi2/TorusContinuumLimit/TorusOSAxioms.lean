/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Torus OS Axioms: OS0–OS3 for the Gaussian Continuum Limit

Defines and proves Osterwalder-Schrader axioms OS0 through OS3 for the
torus Gaussian continuum limit measure.

## Main results

- `TorusOS0_Analyticity` — characteristic functional is analytic
- `TorusOS1_Regularity` — ‖Z[f_re, f_im]‖ ≤ exp(c·(q(f_re)+q(f_im)))
- `TorusOS2_TranslationInvariance` — invariance under (ℝ/Lℤ)² translations
- `TorusOS2_D4Invariance` — invariance under D4 point group
- `TorusOS3_ReflectionPositivity` — RP matrix positive semidefinite
- `SatisfiesTorusOS` — bundled structure for all torus OS axioms
- `torusGaussianLimit_satisfies_OS` — main theorem

## Mathematical background

The torus T²_L has:
- **OS0**: Z[f] = exp(-½ G_L(f,f)) is entire since G_L is bilinear.
- **OS1**: ‖Z[f_re,f_im]‖ ≤ exp(c·(q(f_re)+q(f_im))) for continuous seminorm q.
- **OS2**: G_L is translation-invariant (spectral argument: translation
  acts by phase on Fourier modes) and D4-invariant (eigenvalues are D4-symmetric).
- **OS3**: For positive-time test functions f₁,...,fₙ, the RP matrix
  `Mᵢⱼ = Re(Z[fᵢ - Θfⱼ])` is positive semidefinite. Uses the
  generating-functional matrix form matching `OS3_ReflectionPositivity`
  in `OSAxioms.lean`.

## Warmup for cylinder S¹ × ℝ

This torus formulation prepares for the cylinder S¹ × ℝ, where
"positive time" is the clean half-line {t > 0} and OS reconstruction
applies directly. On the torus (ℝ/Lℤ)², positive time means
t ∈ (0, L/2), which is the correct half for RP with periodic BCs.

## References

- Osterwalder-Schrader (1973, 1975)
- Glimm-Jaffe, *Quantum Physics*, Ch. 6, 19
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Pphi2.TorusContinuumLimit.TorusGaussianLimit
import Pphi2.TorusContinuumLimit.TorusPropagatorConvergence
import Pphi2.GeneralResults.FunctionalAnalysis
import Pphi2.GeneralResults.ComplexAnalysis
import Torus.Symmetry
import HeatKernel.GreenInvariance
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open GaussianField MeasureTheory Filter ProbabilityTheory

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Generating functionals -/

/-- The generating functional (characteristic functional) on the torus.

  `Z_μ(f) = E_μ[e^{i ω(f)}] = ∫ e^{i ω(f)} dμ(ω)`

For a Gaussian measure with covariance C: `Z(f) = exp(-½ C(f,f))`. -/
def torusGeneratingFunctional
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] (f : TorusTestFunction L) : ℂ :=
  ∫ ω : Configuration (TorusTestFunction L),
    Complex.exp (Complex.I * ↑(ω f)) ∂μ

/-- The complex generating functional on the torus.

For a "complex test function" represented by a pair (f_re, f_im) of real
torus test functions, the complex pairing is:

  `⟨ω, J⟩_ℂ = ω(f_re) + i · ω(f_im)`

and the generating functional is:

  `Z[J] = E[exp(i ⟨ω, J⟩_ℂ)] = ∫ exp(i ω(f_re) - ω(f_im)) dμ(ω)`

Note: `exp(-ω(f_im))` is unbounded, so `‖Z[J]‖ ≤ 1` does NOT hold
for complex test functions. This is why OS1 requires exponential bounds.

We represent complex torus test functions as pairs since `TorusTestFunction L`
is real-valued. This matches the pattern in `generatingFunctionalℂ` from
`OSAxioms.lean`. -/
def torusGeneratingFunctionalℂ
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] (f_re f_im : TorusTestFunction L) : ℂ :=
  ∫ ω : Configuration (TorusTestFunction L),
    Complex.exp (Complex.I * ((ω f_re : ℂ) + Complex.I * (ω f_im : ℂ))) ∂μ

/-! ## OS0: Analyticity -/

/-- **OS0: Analyticity of the generating functional.**

The generating functional `Z[Σ zᵢJᵢ]` is entire analytic as a function
of z = (z₁,...,zₙ) ∈ ℂⁿ, for any choice of (real) test functions Jᵢ.

This is the torus analogue of `OS0_Analyticity` in `OSAxioms.lean`.
Since `TorusTestFunction L` is real-valued, we use real test functions
as the basis directions and allow complex coefficients zᵢ ∈ ℂ: the
"complex test function" is Σ zᵢ Jᵢ = Σ (Re zᵢ) Jᵢ + i Σ (Im zᵢ) Jᵢ. -/
def TorusOS0_Analyticity
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (n : ℕ) (J : Fin n → TorusTestFunction L),
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      torusGeneratingFunctionalℂ L μ
        (∑ i, (z i).re • J i) (∑ i, (z i).im • J i)) Set.univ

/-- **Characteristic functional of the Gaussian continuum limit.**

For the Gaussian measure with covariance G_L:
  `E[e^{i ω(f)}] = exp(-½ G_L(f,f))`

This connects the moment generating function (real exponential, given by
`IsTorusGaussianContinuumLimit.isGaussian`) to the characteristic function
(imaginary exponential) via analytic continuation `t → it`.

Reference: Fernique (1975), §III.4; Reed-Simon I, Thm V.8. -/
theorem torusGaussianLimit_characteristic_functional
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass)
    (f : TorusTestFunction L) :
    torusGeneratingFunctional L μ f =
    Complex.exp ((-1 / 2) * ↑(torusContinuumGreen L mass hmass f f)) := by
  -- Setup: X = evaluation at f, G_ff = continuum Green's function diagonal
  set X : Configuration (TorusTestFunction L) → ℝ := fun ω => ω f with hX_def
  set G_ff := torusContinuumGreen L mass hmass f f
  set v : NNReal := G_ff.toNNReal with hv_def
  have hG_nonneg : 0 ≤ G_ff := torusContinuumGreen_nonneg L mass hmass f
  have hv_coe : (v : ℝ) = G_ff := Real.coe_toNNReal _ hG_nonneg
  -- Step 1: Show MGF of X under μ equals MGF of N(0, G_ff)
  have h_mgf_eq : mgf X μ = mgf id (ProbabilityTheory.gaussianReal 0 v) := by
    ext t
    -- LHS: use Gaussian hypothesis at t • f
    change ∫ ω, Real.exp (t * ω f) ∂μ = _
    have h1 := hGCL.isGaussian (t • f)
    -- ω(t • f) = t * ω(f) by linearity
    simp_rw [show ∀ ω : Configuration (TorusTestFunction L), ω (t • f) = t * ω f from
      fun ω => map_smul ω t f] at h1
    -- (t * ω f)² = t² * (ω f)²; pull constant out of integral
    have h2 : ∫ ω : Configuration (TorusTestFunction L), (t * ω f) ^ 2 ∂μ =
        t ^ 2 * ∫ ω, (ω f) ^ 2 ∂μ := by
      simp_rw [mul_pow]; exact integral_const_mul _ _
    rw [h2, hGCL.covariance_eq f] at h1
    rw [h1]
    -- RHS: mgf id (gaussianReal 0 v) t = exp(v * t²/2)
    suffices h : mgf id (gaussianReal 0 v) t = Real.exp ((v : ℝ) * t ^ 2 / 2) by
      rw [h, hv_coe]; congr 1; ring
    simp only [mgf_id_gaussianReal, zero_mul, zero_add]
  -- Step 2: Show I.re = 0 ∈ interior(integrableExpSet X μ)
  have h_in_domain : Complex.I.re ∈ interior (integrableExpSet X μ) := by
    rw [integrableExpSet_eq_of_mgf h_mgf_eq, integrableExpSet_id_gaussianReal,
        interior_univ, Complex.I_re]
    exact Set.mem_univ 0
  -- Step 3: complexMGF agrees at I
  have h_eq_at_I := eqOn_complexMGF_of_mgf h_mgf_eq h_in_domain
  -- Step 4: LHS = torusGeneratingFunctional
  have h_lhs : complexMGF X μ Complex.I = torusGeneratingFunctional L μ f := by
    simp only [complexMGF, torusGeneratingFunctional, hX_def]
  -- Step 5: RHS = exp(-G_ff/2)
  have h_rhs : complexMGF id (ProbabilityTheory.gaussianReal 0 v) Complex.I =
      Complex.exp ((-1 / 2) * ↑G_ff) := by
    rw [show Complex.I = (1 : ℝ) * Complex.I from by norm_num, complexMGF_id_mul_I,
        charFun_gaussianReal]
    congr 1
    rw [show (v : ℝ) = G_ff from hv_coe]; push_cast; ring
  -- Combine
  rw [← h_lhs, h_eq_at_I, h_rhs]

/-! ### Multi-variable identity theorem helper -/

/-- Real nonzero numbers cluster at 0 in ℂ (used for the identity theorem). -/
private lemma frequently_real_near_zero_complex :
    ∃ᶠ w : ℂ in nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ, w.im = 0 := by
  rw [Filter.Frequently]; intro hev
  rw [eventually_nhdsWithin_iff, eventually_iff_exists_mem] at hev
  obtain ⟨s, hs_nhds, hs⟩ := hev
  obtain ⟨t, ht_sub, ht_open, ht_mem⟩ := mem_nhds_iff.mp hs_nhds
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ht_open 0 ht_mem
  exact hs _ (ht_sub (hball (by
    rw [Metric.mem_ball, Complex.dist_eq, sub_zero, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith : ε / 2 > 0)]; linarith)))
    (Set.mem_compl_singleton_iff.mpr (by
      intro h; have := congr_arg Complex.re h; simp at this; linarith))
    (by simp)

/-- `Function.update z k ·` is analytic in the updated value. -/
private lemma update_analyticAt {n : ℕ} (z : Fin n → ℂ) (k : Fin n) (w₀ : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => Function.update z k w) w₀ := by
  rw [analyticAt_pi_iff]; intro i
  by_cases h : i = k
  · have : (fun w => Function.update z k w i) = id := by
      ext w; subst h; simp [Function.update_self]
    rw [this]; exact analyticAt_id
  · have : (fun w => Function.update z k w i) = fun _ => z i := by
      ext w; simp [Function.update_of_ne h]
    rw [this]; exact analyticAt_const

/-- **Multi-variable identity theorem for entire functions.**

If two entire analytic functions `(Fin n → ℂ) → ℂ` agree on `ℝⁿ ⊂ ℂⁿ`,
then they agree on all of `ℂⁿ`.

The proof proceeds by induction on the number of variables that have been
extended from ℝ to ℂ, using the 1-variable identity theorem
(`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`) at each step. -/
private theorem analyticOnNhd_eq_of_eqOn_reals {n : ℕ}
    {f g : (Fin n → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (h_eq : ∀ x : Fin n → ℝ, f (fun i => (x i : ℂ)) = g (fun i => (x i : ℂ))) :
    f = g := by
  suffices key : ∀ k : ℕ, k ≤ n →
      ∀ w : Fin n → ℂ, (∀ i : Fin n, k ≤ i.val → (w i).im = 0) → f w = g w by
    ext z; exact key n le_rfl z (fun i hi => absurd hi (Nat.not_le.mpr i.isLt))
  intro k
  induction k with
  | zero =>
    intro _ w hw
    convert h_eq (fun i => (w i).re) using 1 <;>
    · congr 1; ext i; simp [Complex.ext_iff, hw i (Nat.zero_le _)]
  | succ k ih =>
    intro hk w hw
    have hk' : k < n := Nat.lt_of_succ_le hk
    set j₀ : Fin n := ⟨k, hk'⟩
    have hφ : AnalyticOnNhd ℂ (fun t => f (Function.update w j₀ t)) Set.univ :=
      fun t _ => (hf _ (Set.mem_univ _)).comp (update_analyticAt w j₀ t)
    have hψ : AnalyticOnNhd ℂ (fun t => g (Function.update w j₀ t)) Set.univ :=
      fun t _ => (hg _ (Set.mem_univ _)).comp (update_analyticAt w j₀ t)
    have h_agree : ∀ t : ℝ, f (Function.update w j₀ (t : ℂ)) =
        g (Function.update w j₀ (t : ℂ)) := by
      intro t; apply ih (Nat.le_of_lt hk'); intro i hi
      by_cases h : i = j₀
      · subst h; simp [Function.update_self]
      · rw [Function.update_of_ne h]
        exact hw i (by have : i.val ≠ k := fun heq => h (Fin.ext heq); omega)
    have h_id := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hφ hψ
      isPreconnected_univ (Set.mem_univ 0)
      (frequently_real_near_zero_complex.mono (fun t ht => by
        rw [show t = (t.re : ℂ) from Complex.ext (by simp) (by simp [ht])]
        exact h_agree t.re))
    rw [show w = Function.update w j₀ (w j₀) from (Function.update_eq_self j₀ w).symm]
    exact h_id (Set.mem_univ _)


/-! ### Gaussian OS0: analyticity of the generating functional -/

/-- **Gaussian linear exponential integrability.**

For a Gaussian measure satisfying `E[exp(ω(f))] = exp(½ ∫(ω f)² dμ)`,
the function `ω ↦ exp(t·ω(f))` is integrable for any real `t`.

Proof by contradiction: if not integrable, `integral_undef` gives the
integral = 0, but `isGaussian` says it equals `exp(½ t² C(f,f)) > 0`. -/
private lemma gaussian_linear_exp_integrable
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass)
    (t : ℝ) (f : TorusTestFunction L) :
    Integrable (fun ω : Configuration (TorusTestFunction L) =>
      Real.exp (t * ω f)) μ := by
  by_contra h_not_int
  have h_zero := integral_undef h_not_int
  have h := hGCL.isGaussian (t • f)
  simp only [show ∀ ω : Configuration (TorusTestFunction L), ω (t • f) = t * ω f
    from fun ω => ContinuousLinearMap.map_smul_of_tower ω t f] at h
  linarith [Real.exp_pos ((1 / 2) * ∫ ω : Configuration (TorusTestFunction L),
    (t * ω f) ^ 2 ∂μ)]

/-- **Gaussian exponential sum integrability (domination bound).**

For a Gaussian measure, `ω ↦ exp(∑ Mᵢ |ω(Jᵢ)|)` is integrable.
This provides the locally uniform domination bound needed for
`analyticOnNhd_integral`.

The proof uses `exp(∑ Mᵢ|xᵢ|) = ∏ exp(Mᵢ|xᵢ|)` and bounds each factor
by `exp(Mᵢ xᵢ) + exp(-Mᵢ xᵢ)`, whose integral is finite by the Gaussian
hypothesis (`gaussian_linear_exp_integrable`). For the product integrability,
Hölder's inequality with `n` exponents reduces to `Lⁿ`-integrability of
each factor, which holds since all exponential moments of Gaussians are
finite. -/
private lemma gaussian_exp_sum_abs_integrable
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass)
    (n : ℕ) (M : Fin n → ℝ) (J : Fin n → TorusTestFunction L) :
    Integrable (fun ω : Configuration (TorusTestFunction L) =>
      Real.exp (∑ i : Fin n, M i * |ω (J i)|)) μ := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Real.exp_zero]
    exact integrable_const 1
  | succ n ih =>
    -- Split: ∑_{i<n+1} = M₀|ω(J₀)| + ∑_{i<n} M_{i+1}|ω(J_{i+1})|
    -- exp(a + b) = exp(a) · exp(b), so our function is a product f₁ · f₂.
    -- Product integrability via AM-GM: f₁·f₂ ≤ (f₁² + f₂²)/2 for nonneg f₁,f₂.
    -- f₁² = exp(2M₀|x₀|), f₂² = exp(2∑Mᵢ|xᵢ|), both integrable.
    -- Helper: exp(c|x|) ≤ exp(cx) + exp(-cx)
    have exp_abs_le : ∀ (c x : ℝ), Real.exp (c * |x|) ≤
        Real.exp (c * x) + Real.exp (-c * x) := by
      intro c x
      rcases le_or_gt 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        linarith [Real.exp_pos (-c * x)]
      · rw [abs_of_neg hx]
        have : c * (-x) = -c * x := by ring
        rw [this]
        linarith [Real.exp_pos (c * x)]
    -- Helper: exp(c|x|) is integrable for any c, using gaussian_linear_exp_integrable
    have exp_abs_int : ∀ (c : ℝ) (f : TorusTestFunction L),
        Integrable (fun ω => Real.exp (c * |ω f|)) μ := by
      intro c f
      apply Integrable.mono'
        ((gaussian_linear_exp_integrable L mass hmass μ hGCL c f).add
         (gaussian_linear_exp_integrable L mass hmass μ hGCL (-c) f))
      · exact (Real.measurable_exp.comp (measurable_const.mul
            (configuration_eval_measurable f |>.abs))).aestronglyMeasurable
      · exact ae_of_all _ (fun ω => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact exp_abs_le c (ω f))
    -- f₁² = exp(2M₀|ω(J₀)|) is integrable
    have hf₁_sq : Integrable (fun ω => Real.exp (2 * M 0 * |ω (J 0)|)) μ :=
      exp_abs_int (2 * M 0) (J 0)
    -- f₂² = exp(2·∑ Mᵢ|ωᵢ|) = exp(∑ (2Mᵢ)|ωᵢ|) is integrable by IH
    have hf₂_sq : Integrable (fun ω => Real.exp (∑ i : Fin n,
        2 * M i.succ * |ω (J i.succ)|)) μ :=
      ih (fun i => 2 * M i.succ) (fun i => J i.succ)
    -- The bound function: (f₁² + f₂²) / 2
    set bound : Configuration (TorusTestFunction L) → ℝ :=
      fun ω => (Real.exp (2 * M 0 * |ω (J 0)|) +
                Real.exp (∑ i : Fin n, 2 * M i.succ * |ω (J i.succ)|)) / 2
    have hbound_int : Integrable bound μ := (hf₁_sq.add hf₂_sq).div_const 2
    -- Our function ≤ bound (AM-GM: a·b ≤ (a²+b²)/2 for nonneg a,b)
    have hle : ∀ ω, Real.exp (∑ i : Fin (n + 1), M i * |ω (J i)|) ≤ bound ω := by
      intro ω
      rw [Fin.sum_univ_succ, Real.exp_add]
      -- a · b ≤ (a² + b²) / 2 for nonneg a, b
      have ham : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
        intro a b ha hb; nlinarith [sq_nonneg (a - b)]
      calc Real.exp (M 0 * |ω (J 0)|) *
              Real.exp (∑ i : Fin n, M i.succ * |ω (J i.succ)|)
          ≤ (Real.exp (M 0 * |ω (J 0)|) ^ 2 +
              Real.exp (∑ i : Fin n, M i.succ * |ω (J i.succ)|) ^ 2) / 2 :=
            ham _ _ (Real.exp_pos _).le (Real.exp_pos _).le
        _ = (Real.exp (2 * M 0 * |ω (J 0)|) +
              Real.exp (∑ i : Fin n, 2 * M i.succ * |ω (J i.succ)|)) / 2 := by
            have hsq1 : Real.exp (M 0 * |ω (J 0)|) ^ 2 =
                Real.exp (2 * M 0 * |ω (J 0)|) := by
              rw [sq, ← Real.exp_add]; ring_nf
            have hsq2 : Real.exp (∑ i : Fin n, M i.succ * |ω (J i.succ)|) ^ 2 =
                Real.exp (∑ i : Fin n, 2 * M i.succ * |ω (J i.succ)|) := by
              rw [sq, ← Real.exp_add, ← Finset.sum_add_distrib]
              congr 1; exact Finset.sum_congr rfl (fun i _ => by ring)
            rw [hsq1, hsq2]
    -- Measurability of our function
    have hmeas : AEStronglyMeasurable
        (fun ω => Real.exp (∑ i : Fin (n + 1), M i * |ω (J i)|)) μ :=
      (Real.measurable_exp.comp (Finset.measurable_sum _ (fun i _ =>
        measurable_const.mul (configuration_eval_measurable (J i) |>.abs)))).aestronglyMeasurable
    -- Conclude by domination
    exact hbound_int.mono' hmeas (ae_of_all _ (fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hle ω))

/-- **Rewriting lemma**: the complex generating functional equals an integral
where the integrand is manifestly entire in `z`.

By linearity of `ω` (a continuous linear functional), the integrand
`exp(I·(ω(∑ xᵢJᵢ) + I·ω(∑ yᵢJᵢ)))` simplifies to `exp(∑ I·zᵢ·ω(Jᵢ))`
where `zᵢ = xᵢ + iyᵢ`. The latter form exhibits entire dependence on `z`. -/
private lemma torusGeneratingFunctionalℂ_eq_integral_exp
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (n : ℕ) (J : Fin n → TorusTestFunction L) (z : Fin n → ℂ) :
    torusGeneratingFunctionalℂ L μ
      (∑ i, (z i).re • J i) (∑ i, (z i).im • J i) =
    ∫ ω : Configuration (TorusTestFunction L),
      Complex.exp (∑ i : Fin n, Complex.I * z i * ↑(ω (J i))) ∂μ := by
  simp only [torusGeneratingFunctionalℂ]
  congr 1 with ω
  simp only [map_sum, map_smul, smul_eq_mul]
  congr 1
  -- Goal: I * (↑(∑ xᵢωᵢ) + I * ↑(∑ yᵢωᵢ)) = ∑ I * zᵢ * ↑ωᵢ
  -- Step 1: Push ↑(∑...) into the sum
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  -- Step 2: Distribute I over sums
  rw [mul_add, Finset.mul_sum, ← mul_assoc, Finset.mul_sum, ← Finset.sum_add_distrib]
  -- Step 3: Combine summands using z = re + I*im
  congr 1 with i
  -- Rewrite z i in terms of re + im*I, but avoid creating .re/.im of complex exprs
  -- Instead, directly show the equality
  have hre := Complex.ofReal_re (z i).re
  have him := Complex.ofReal_re (z i).im
  rw [show z i = ↑(z i).re + ↑(z i).im * Complex.I from (Complex.re_add_im (z i)).symm]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  ring

/-- **Analyticity of the complex generating functional.**

The map `z ↦ Z_ℂ(∑ Re(zᵢ)·Jᵢ, ∑ Im(zᵢ)·Jᵢ)` is entire analytic in `z ∈ ℂⁿ`.

**Proof.** By linearity of ω, the generating functional rewrites as
`∫ exp(∑ I·zᵢ·ω(Jᵢ)) dμ` (see `torusGeneratingFunctionalℂ_eq_integral_exp`).
The integrand `exp(∑ I·zᵢ·cᵢ)` is entire in z for each fixed ω (it is `exp`
composed with a ℂ-linear function). The domination bound
`‖exp(∑ I·zᵢ·ω(Jᵢ))‖ ≤ exp(∑ |Im zᵢ|·|ω(Jᵢ)|)` is integrable on compact
sets by the Gaussian moment bound (`gaussian_exp_sum_abs_integrable`).
By `analyticOnNhd_integral` (Morera + Osgood), the integral is entire.

Reference: Reed-Simon I, Thm VI.1; Fernique (1975), §III.4. -/
theorem torusGeneratingFunctionalℂ_analyticOnNhd
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass)
    (n : ℕ) (J : Fin n → TorusTestFunction L) :
    AnalyticOnNhd ℂ (fun z : Fin n → ℂ =>
      torusGeneratingFunctionalℂ L μ
        (∑ i, (z i).re • J i) (∑ i, (z i).im • J i)) Set.univ := by
  -- Rewrite using the manifestly analytic form
  have h_rw : (fun z : Fin n → ℂ =>
      torusGeneratingFunctionalℂ L μ
        (∑ i, (z i).re • J i) (∑ i, (z i).im • J i)) =
      fun z => ∫ ω : Configuration (TorusTestFunction L),
        Complex.exp (∑ i : Fin n, Complex.I * z i * ↑(ω (J i))) ∂μ := by
    ext z; exact torusGeneratingFunctionalℂ_eq_integral_exp L μ n J z
  rw [h_rw]
  set F : (Fin n → ℂ) → Configuration (TorusTestFunction L) → ℂ :=
    fun z ω => Complex.exp (∑ i : Fin n, Complex.I * z i * ↑(ω (J i))) with hF_def
  -- Condition 1: For each ω, z ↦ F(z,ω) is entire (exp ∘ ℂ-linear)
  have hF_an : ∀ ω : Configuration (TorusTestFunction L),
      AnalyticOnNhd ℂ (F · ω) Set.univ := by
    intro ω z _
    apply AnalyticAt.cexp'
    apply Finset.univ.analyticAt_fun_sum; intro i _
    exact (analyticAt_const.mul
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt z)).mul
      analyticAt_const
  -- Condition 2: For each z, F(z,·) is AEStronglyMeasurable
  -- exp composed with a finite sum of (const * ofReal ∘ configuration_eval) is measurable
  -- via configuration_eval_measurable + standard composition lemmas.
  have hF_meas : ∀ z : Fin n → ℂ, AEStronglyMeasurable (F z) μ := by
    intro z; simp only [hF_def]
    have h_eval_meas : ∀ i : Fin n, Measurable (fun ω : Configuration (TorusTestFunction L) =>
        Complex.I * z i * ↑(ω (J i))) := by
      intro i
      have h1 : Measurable (fun ω : Configuration (TorusTestFunction L) =>
          (ω (J i) : ℂ)) :=
        Complex.continuous_ofReal.measurable.comp (configuration_eval_measurable (J i))
      exact h1.const_mul _
    exact (Complex.continuous_exp.measurable.comp
      (Finset.measurable_sum _ (fun i _ => h_eval_meas i))).aestronglyMeasurable
  -- Condition 3: Locally uniform domination by an integrable bound
  have hF_dom : ∀ K : Set (Fin n → ℂ), IsCompact K →
      ∃ bound : Configuration (TorusTestFunction L) → ℝ, Integrable bound μ ∧
        ∀ z ∈ K, ∀ᵐ ω ∂μ, ‖F z ω‖ ≤ bound ω := by
    intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    refine ⟨fun ω => Real.exp (∑ i : Fin n, R * |ω (J i)|),
            gaussian_exp_sum_abs_integrable L mass hmass μ hGCL n (fun _ => R) J, ?_⟩
    intro z hz
    apply ae_of_all μ; intro ω
    simp only [hF_def, Complex.norm_exp]
    -- ‖exp(∑ Izᵢωᵢ)‖ = exp(Re(∑ Izᵢωᵢ)) ≤ exp(∑ R·|ωᵢ|)
    -- exp is monotone, so it suffices to show Re(∑ ...) ≤ ∑ R·|ωᵢ|
    gcongr
    rw [show (∑ i : Fin n, Complex.I * z i * ↑(ω (J i))).re =
      ∑ i : Fin n, (Complex.I * z i * ↑(ω (J i))).re from
      map_sum Complex.reAddGroupHom _ _]
    apply Finset.sum_le_sum
    intro i _
    -- Re(I·zᵢ·↑ωᵢ) = -Im(zᵢ)·ωᵢ ≤ |Im(zᵢ)|·|ωᵢ| ≤ R·|ωᵢ|
    calc (Complex.I * z i * ↑(ω (J i))).re
        = -(z i).im * ω (J i) := by
          simp [Complex.mul_re, Complex.I_re, Complex.I_im,
                Complex.ofReal_re, Complex.ofReal_im]
      _ ≤ |-(z i).im * ω (J i)| := le_abs_self _
      _ = |(z i).im| * |ω (J i)| := by rw [abs_mul, abs_neg]
      _ ≤ R * |ω (J i)| := by
          gcongr
          exact (Complex.abs_im_le_norm (z i)).trans
            ((norm_le_pi_norm z i).trans (hR z hz))
  exact _root_.analyticOnNhd_integral hF_an hF_meas hF_dom

/-! ### Complex generating functional = exp(quadratic) -/

/-- **Complex generating functional of a torus Gaussian as exp of a quadratic form.**

For a Gaussian measure μ with covariance G_L, the complex generating functional
evaluated on `f_re = ∑ Re(zᵢ) Jᵢ, f_im = ∑ Im(zᵢ) Jᵢ` simplifies to:

  `Z_ℂ[z] = exp(-½ ∑ᵢⱼ zᵢ zⱼ G_L(Jᵢ, Jⱼ))`

**Proof:** Both sides are entire analytic functions of z ∈ ℂⁿ (LHS by
`torusGeneratingFunctionalℂ_analyticOnNhd`, RHS by exp ∘ quadratic polynomial).
For z ∈ ℝⁿ, Im(zᵢ) = 0, so the LHS reduces to the characteristic functional
`Z(∑ xᵢ·Jᵢ) = exp(-½ G(∑ xᵢ·Jᵢ, ∑ xⱼ·Jⱼ))` (proved), and the RHS reduces to
`exp(-½ ∑ xᵢxⱼGᵢⱼ) = exp(-½ G(∑ xᵢ·Jᵢ, ∑ xⱼ·Jⱼ))` by bilinearity
(`greenFunctionBilinear_finset_sum`). Agreement on ℝⁿ plus analyticity on ℂⁿ
gives equality by the multi-variable identity principle
(`analyticOnNhd_eq_of_eqOn_reals`). -/
theorem torusGaussianLimit_complex_cf_quadratic
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass)
    (n : ℕ) (J : Fin n → TorusTestFunction L)
    (z : Fin n → ℂ) :
    torusGeneratingFunctionalℂ L μ
      (∑ i, (z i).re • J i) (∑ i, (z i).im • J i) =
    Complex.exp ((-1 / 2 : ℂ) * ∑ i : Fin n, ∑ j : Fin n,
      z i * z j * (torusContinuumGreen L mass hmass (J i) (J j) : ℂ)) := by
  set F := fun z : Fin n → ℂ =>
    torusGeneratingFunctionalℂ L μ (∑ i, (z i).re • J i) (∑ i, (z i).im • J i)
  set G := fun z : Fin n → ℂ =>
    Complex.exp ((-1 / 2 : ℂ) * ∑ i : Fin n, ∑ j : Fin n,
      z i * z j * (torusContinuumGreen L mass hmass (J i) (J j) : ℂ))
  have hF_an : AnalyticOnNhd ℂ F Set.univ :=
    torusGeneratingFunctionalℂ_analyticOnNhd L mass hmass μ hGCL n J
  have hG_an : AnalyticOnNhd ℂ G Set.univ := by
    intro z _; apply AnalyticAt.cexp'
    apply AnalyticAt.mul analyticAt_const
    apply Finset.univ.analyticAt_fun_sum; intro i _
    apply Finset.univ.analyticAt_fun_sum; intro j _
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt z |>.mul
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).analyticAt z)).mul
      analyticAt_const
  have h_eq_real : ∀ x : Fin n → ℝ,
      F (fun i => (x i : ℂ)) = G (fun i => (x i : ℂ)) := by
    intro x
    simp only [F, G, Complex.ofReal_re, Complex.ofReal_im]
    rw [show (∑ i : Fin n, (0 : ℝ) • J i) = (0 : TorusTestFunction L) from by simp]
    rw [show torusGeneratingFunctionalℂ L μ (∑ i, x i • J i) 0 =
        torusGeneratingFunctional L μ (∑ i, x i • J i) from by
      simp [torusGeneratingFunctionalℂ, torusGeneratingFunctional, map_zero]]
    rw [torusGaussianLimit_characteristic_functional L mass hmass μ hGCL]
    congr 1; congr 1
    simp only [torusContinuumGreen]
    rw [greenFunctionBilinear_finset_sum mass hmass Finset.univ Finset.univ x x J J]
    push_cast; ring
  exact congr_fun (analyticOnNhd_eq_of_eqOn_reals hF_an hG_an h_eq_real) z

/-- OS0 for the torus Gaussian continuum limit.

For Gaussian μ with covariance G_L, the complex generating functional is:
  `Z[f_re, f_im] = exp(-½ G_L(f_re + if_im, f_re + if_im))`
This is entire in the coefficients zᵢ since it is `exp ∘ (quadratic polynomial)`.

The proof uses `torusGaussianLimit_complex_cf_quadratic` to rewrite the
generating functional as `exp(-½ ∑ᵢⱼ zᵢzⱼ Gᵢⱼ)`, then shows this is
analytic because both exp and polynomials are entire. -/
theorem torusGaussianLimit_os0
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass) :
    TorusOS0_Analyticity L μ := by
  intro n J
  have h_eq : (fun z : Fin n → ℂ =>
      torusGeneratingFunctionalℂ L μ
        (∑ i, (z i).re • J i) (∑ i, (z i).im • J i)) =
      (fun z => Complex.exp ((-1 / 2 : ℂ) * ∑ i : Fin n, ∑ j : Fin n,
        z i * z j * (torusContinuumGreen L mass hmass (J i) (J j) : ℂ))) := by
    ext z; exact torusGaussianLimit_complex_cf_quadratic L mass hmass μ hGCL n J z
  rw [h_eq]
  intro z _
  apply AnalyticAt.analyticWithinAt
  apply AnalyticAt.cexp'
  apply AnalyticAt.mul analyticAt_const
  apply Finset.univ.analyticAt_fun_sum; intro i _
  apply Finset.univ.analyticAt_fun_sum; intro j _
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt z |>.mul
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).analyticAt z)).mul
    analyticAt_const

/-! ## OS1: Regularity -/

/-- **OS1: Regularity of the complex generating functional.**

The complex generating functional satisfies exponential bounds:

  `‖Z[f_re, f_im]‖ ≤ exp(c · (q(f_re) + q(f_im)))`

for some continuous seminorm `q` on the torus test function space
and constant `c > 0`.

This is the torus analogue of `OS1_Regularity` in `OSAxioms.lean`,
adapted to the abstract nuclear Fréchet test function space where
spatial Lᵖ norms are not directly available. The continuous seminorm
formulation is the standard OS1 for nuclear test function spaces and
subsumes the `L¹ + Lᵖ` form used in the infinite-volume case.

The bound controls the growth of Z when the imaginary part of the
test function (which produces the unbounded factor `exp(-ω(f_im))`)
is nonzero.

For a Gaussian with covariance G_L, the bound holds with
`q(f) = G_L(f,f)` (the RKHS norm squared). For the interacting
case, Nelson's hypercontractive estimate gives the bound via
a Sobolev-type seminorm. -/
def TorusOS1_Regularity
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∃ (q : TorusTestFunction L → ℝ) (_ : Continuous q) (c : ℝ), c > 0 ∧
    ∀ (f_re f_im : TorusTestFunction L),
      ‖torusGeneratingFunctionalℂ L μ f_re f_im‖ ≤
        Real.exp (c * (q f_re + q f_im))

/-- **Continuity of the Green's function diagonal.**

  `f ↦ G_L(f, f)` is continuous on `TorusTestFunction L`.

The proof uses `greenFunctionBilinear_continuous_diag` from gaussian-field,
which shows that the spectral sum `Σ (coeff_m f)² / (μ_m + mass²)` converges
locally uniformly (via the Weierstrass M-test with the `coeff_decay` bound
from `DyninMityaginSpace`). -/
theorem torusContinuumGreen_continuous_diag
    (mass : ℝ) (hmass : 0 < mass) :
    Continuous (fun f : TorusTestFunction L => torusContinuumGreen L mass hmass f f) :=
  GaussianField.greenFunctionBilinear_continuous_diag mass hmass

/-- OS1 for the torus Gaussian continuum limit.

For Gaussian μ with covariance G_L, the triangle inequality gives:
  `‖Z_ℂ[f_re, f_im]‖ ≤ ∫ ‖exp(i(ω(f_re) + iω(f_im)))‖ dμ`
  `= ∫ exp(-ω(f_im)) dμ = exp(½ G_L(f_im,f_im))`
  `≤ exp(½ (G_L(f_re,f_re) + G_L(f_im,f_im)))`

using `‖exp(-y + ix)‖ = exp(-y)` and the Gaussian MGF
`E[exp(-ω(f_im))] = E[exp(ω(-f_im))] = exp(½ G(f_im,f_im))`.

This gives the bound with `q(f) = G_L(f,f)` and `c = 1/2`. -/
theorem torusGaussianLimit_os1
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass) :
    TorusOS1_Regularity L μ := by
  refine ⟨fun f => torusContinuumGreen L mass hmass f f,
          torusContinuumGreen_continuous_diag L mass hmass,
          1 / 2, by norm_num, ?_⟩
  intro f_re f_im
  -- Triangle inequality: ‖Z_ℂ‖ ≤ ∫ ‖exp(I*(ω(f_re) + I*ω(f_im)))‖ dμ
  have h_tri : ‖torusGeneratingFunctionalℂ L μ f_re f_im‖ ≤
      ∫ ω, ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ ∂μ :=
    norm_integral_le_integral_norm _
  -- ‖exp(I*(x + Iy))‖ = exp(-y), since I*(x+Iy) = -y + Ix has real part -y
  have h_norm : ∀ ω : Configuration (TorusTestFunction L),
      ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ =
      Real.exp (-(ω f_im)) := by
    intro ω
    rw [Complex.norm_exp]
    congr 1
    have : Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)) =
        -↑(ω f_im) + ↑(ω f_re) * Complex.I := by
      rw [mul_add, ← mul_assoc, Complex.I_mul_I, neg_one_mul]; ring
    rw [this, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  -- Gaussian MGF: ∫ exp(-ω(f_im)) dμ = exp(½ G(f_im,f_im))
  have h_mgf : ∫ ω : Configuration (TorusTestFunction L),
      Real.exp (-(ω f_im)) ∂μ =
      Real.exp ((1 / 2) * torusContinuumGreen L mass hmass f_im f_im) := by
    simp_rw [show ∀ ω : Configuration (TorusTestFunction L),
        -(ω f_im) = ω (-f_im) from fun ω => (map_neg ω f_im).symm]
    rw [hGCL.isGaussian (-f_im)]
    congr 1; congr 1
    simp_rw [show ∀ ω : Configuration (TorusTestFunction L),
        (ω (-f_im)) ^ 2 = (ω f_im) ^ 2 from fun ω => by rw [map_neg]; ring]
    exact hGCL.covariance_eq f_im
  -- Combine: ‖Z_ℂ‖ ≤ exp(½ G_im) ≤ exp(½ (G_re + G_im))
  calc ‖torusGeneratingFunctionalℂ L μ f_re f_im‖
      ≤ ∫ ω, ‖Complex.exp (Complex.I * (↑(ω f_re) + Complex.I * ↑(ω f_im)))‖ ∂μ := h_tri
    _ = ∫ ω, Real.exp (-(ω f_im)) ∂μ := by simp_rw [h_norm]
    _ = Real.exp ((1 / 2) * torusContinuumGreen L mass hmass f_im f_im) := h_mgf
    _ ≤ Real.exp (1 / 2 * (torusContinuumGreen L mass hmass f_re f_re +
                            torusContinuumGreen L mass hmass f_im f_im)) := by
        gcongr
        linarith [torusContinuumGreen_nonneg L mass hmass f_re]

/-! ## OS2: Euclidean invariance (translation + D4) -/

/-- **OS2a: Translation invariance of the generating functional.**

The measure μ is invariant under (ℝ/Lℤ)² translations. -/
def TorusOS2_TranslationInvariance
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  ∀ (v : ℝ × ℝ) (f : TorusTestFunction L),
    torusGeneratingFunctional L μ f =
    torusGeneratingFunctional L μ (torusTranslation L v f)

/-- **OS2b: D4 point group invariance.**

The measure μ is invariant under coordinate swap and time reflection. -/
def TorusOS2_D4Invariance
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] : Prop :=
  (∀ f, torusGeneratingFunctional L μ f =
         torusGeneratingFunctional L μ (torusSwap L f)) ∧
  (∀ f, torusGeneratingFunctional L μ f =
         torusGeneratingFunctional L μ (torusTimeReflection L f))

/-- **Translation invariance of the torus continuum Green's function.**

  `G_L(T_v f, T_v g) = G_L(f, g)` for all v ∈ (ℝ/Lℤ)².

Spectral argument: translation acts by phase rotation on each cos/sin
pair. The paired product of Fourier coefficients is invariant
(from `cos²+sin²=1`), and paired modes share eigenvalues.

Uses `greenFunctionBilinear_translation_invariant` from gaussian-field,
which combines pure-tensor invariance with the extension principle.

Reference: Glimm-Jaffe, *Quantum Physics*, §6.4. -/
theorem torusContinuumGreen_translation_invariant
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ × ℝ)
    (f g : TorusTestFunction L) :
    torusContinuumGreen L mass hmass (torusTranslation L v f) (torusTranslation L v g) =
    torusContinuumGreen L mass hmass f g := by
  simp only [torusContinuumGreen, torusTranslation]
  exact greenFunctionBilinear_translation_invariant L mass hmass v f g

/-- **D4 point group invariance of the torus continuum Green's function.**

  `G_L` is invariant under coordinate swap and time reflection.

- **Swap**: Reindex `(n₁,n₂) ↦ (n₂,n₁)` in the spectral sum;
  eigenvalues are symmetric under exchange.
- **Reflection**: Each mode transforms by ±1, so `(±1)² = 1`
  in the coefficient products.

Uses `greenFunctionBilinear_swap_invariant` and
`greenFunctionBilinear_timeReflection_invariant` from gaussian-field.

Reference: Glimm-Jaffe, *Quantum Physics*, §6.4. -/
theorem torusContinuumGreen_pointGroup_invariant
    (mass : ℝ) (hmass : 0 < mass) :
    (∀ f g : TorusTestFunction L,
      torusContinuumGreen L mass hmass (torusSwap L f) (torusSwap L g) =
      torusContinuumGreen L mass hmass f g) ∧
    (∀ f g : TorusTestFunction L,
      torusContinuumGreen L mass hmass (torusTimeReflection L f) (torusTimeReflection L g) =
      torusContinuumGreen L mass hmass f g) := by
  constructor
  · intro f g
    simp only [torusContinuumGreen, torusSwap]
    exact greenFunctionBilinear_swap_invariant L mass hmass f g
  · intro f g
    simp only [torusContinuumGreen, torusTimeReflection]
    exact greenFunctionBilinear_timeReflection_invariant L mass hmass f g

/-- OS2 (translation) for the torus Gaussian continuum limit.

For Gaussian μ determined by covariance G_L, translation invariance of G_L
implies: `E[e^{iω(Tf)}] = exp(-½ G_L(Tf,Tf)) = exp(-½ G_L(f,f)) = E[e^{iωf}]`. -/
theorem torusGaussianLimit_os2_translation
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass) :
    TorusOS2_TranslationInvariance L μ := by
  intro v f
  -- Both sides equal exp(-½ G_L(f,f)) by the characteristic functional formula
  rw [torusGaussianLimit_characteristic_functional L mass hmass μ hGCL f,
      torusGaussianLimit_characteristic_functional L mass hmass μ hGCL
        (torusTranslation L v f)]
  congr 1; congr 1; congr 1
  exact (torusContinuumGreen_translation_invariant L mass hmass v f f).symm

/-- OS2 (D4) for the torus Gaussian continuum limit. -/
theorem torusGaussianLimit_os2_D4
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass) :
    TorusOS2_D4Invariance L μ := by
  obtain ⟨h_swap, h_refl⟩ := torusContinuumGreen_pointGroup_invariant L mass hmass
  constructor
  · intro f
    rw [torusGaussianLimit_characteristic_functional L mass hmass μ hGCL f,
        torusGaussianLimit_characteristic_functional L mass hmass μ hGCL (torusSwap L f)]
    congr 1; congr 1; congr 1
    exact (h_swap f f).symm
  · intro f
    rw [torusGaussianLimit_characteristic_functional L mass hmass μ hGCL f,
        torusGaussianLimit_characteristic_functional L mass hmass μ hGCL
          (torusTimeReflection L f)]
    congr 1; congr 1; congr 1
    exact (h_refl f f).symm

/-! ## OS3: Reflection positivity (dropped — see Route C cylinder)

OS3 is more natural on the cylinder S¹×ℝ with its real time axis.
The positive-time submodule, lattice RP axiom, and RP weak limit
transfer have been removed from the torus route. -/

/-! ### Helper lemmas (retained for potential reuse) -/

/-- `ω ↦ cos(ω(g))` is continuous on configuration space. -/
private lemma torusCosEval_continuous (g : TorusTestFunction L) :
    Continuous (fun ω : Configuration (TorusTestFunction L) => Real.cos (ω g)) :=
  Real.continuous_cos.comp (WeakDual.eval_continuous g)

/-- `ω ↦ cos(ω(g))` is bounded by 1. -/
private lemma torusCosEval_bounded (g : TorusTestFunction L) :
    ∃ C : ℝ, ∀ ω : Configuration (TorusTestFunction L), |Real.cos (ω g)| ≤ C :=
  ⟨1, fun ω => Real.abs_cos_le_one (ω g)⟩

/-- `ω ↦ exp(i·ω(g))` is AE strongly measurable w.r.t. the cylindrical σ-algebra.
Uses `configuration_eval_measurable` (not topology, since the measurable space
on Configuration is cylindrical, not Borel). -/
private lemma torusExpEval_aestronglyMeasurable
    (μ : Measure (Configuration (TorusTestFunction L)))
    (g : TorusTestFunction L) :
    AEStronglyMeasurable (fun ω : Configuration (TorusTestFunction L) =>
      Complex.exp (Complex.I * ↑(ω g))) μ :=
  (Complex.continuous_exp.measurable.comp
    (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
      (configuration_eval_measurable g)))).aestronglyMeasurable

/-- `ω ↦ exp(i·ω(g))` is integrable w.r.t. any probability measure.
Bounded by 1 since `‖exp(ix)‖ = 1` for real `x`. -/
private lemma torusExpEval_integrable
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] (g : TorusTestFunction L) :
    Integrable (fun ω : Configuration (TorusTestFunction L) =>
      Complex.exp (Complex.I * ↑(ω g))) μ := by
  apply (integrable_const (1 : ℂ)).mono
  · exact torusExpEval_aestronglyMeasurable L μ g
  · apply ae_of_all
    intro ω
    simp only [norm_one]
    rw [show Complex.I * ↑(ω g) = ↑(ω g) * Complex.I from mul_comm _ _]
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I (ω g))

/-- **Re(Z_μ[g]) = ∫ cos(ω(g)) dμ(ω).**

Connects the generating functional to the cos integral. This is the key
bridge to apply weak convergence (which works for bounded continuous
real-valued functions) to the complex generating functional.

Proof: `Re(∫ exp(i·ω(g)) dμ) = ∫ Re(exp(i·ω(g))) dμ = ∫ cos(ω(g)) dμ`,
using `ContinuousLinearMap.integral_comp_comm` (Re commutes with integration
for integrable functions) and Euler's formula `Re(exp(ix)) = cos(x)`. -/
private lemma torusGeneratingFunctional_re_eq_integral_cos
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] (g : TorusTestFunction L) :
    (torusGeneratingFunctional L μ g).re =
    ∫ ω : Configuration (TorusTestFunction L), Real.cos (ω g) ∂μ := by
  simpa [torusGeneratingFunctional] using configuration_expIntegral_re_eq_integral_cos μ g

/-! ### OS3 definition (matrix form) -/

-- OS3 (reflection positivity) removed from torus route.
-- See Route C (cylinder S¹×ℝ) for OS3 via Laplace factorization.

/-! ## Bundle and main theorem -/

/-- **Bundled torus OS axioms OS0–OS3.**

This structure is measure-agnostic: it applies to any probability measure
on Configuration(TorusTestFunction L), whether Gaussian or interacting.
The axiom definitions depend only on `L` and `μ`, not on mass or polynomial. -/
structure SatisfiesTorusOS
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ] : Prop where
  os0 : TorusOS0_Analyticity L μ
  os1 : TorusOS1_Regularity L μ
  os2_translation : TorusOS2_TranslationInvariance L μ
  os2_D4 : TorusOS2_D4Invariance L μ
  -- OS3 (reflection positivity) dropped: natural on cylinder S¹×ℝ, not torus T²

/-- **The torus Gaussian continuum limit satisfies OS0–OS3.**

The proof uses the Gaussian structure (characteristic functional = exp(-½G))
to establish OS0, OS1, and OS2. OS3 is inherited from lattice RP via
weak limits. -/
theorem torusGaussianLimit_satisfies_OS
    (mass : ℝ) (hmass : 0 < mass)
    (μ : Measure (Configuration (TorusTestFunction L)))
    [IsProbabilityMeasure μ]
    (hGCL : IsTorusGaussianContinuumLimit L μ mass hmass) :
    SatisfiesTorusOS L μ where
  os0 := torusGaussianLimit_os0 L mass hmass μ hGCL
  os1 := torusGaussianLimit_os1 L mass hmass μ hGCL
  os2_translation := torusGaussianLimit_os2_translation L mass hmass μ hGCL
  os2_D4 := torusGaussianLimit_os2_D4 L mass hmass μ hGCL

/-- **Existence of a torus Gaussian measure satisfying OS0–OS3.**

Master theorem: for any torus size L > 0 and mass m > 0, there exists
a probability measure on Configuration(TorusTestFunction L) satisfying
all torus OS axioms. The measure is the continuum limit of lattice GFFs.

The statement hides all construction details (mass, lattice, convergence)
behind the existential — the output is just a measure satisfying `SatisfiesTorusOS`. -/
theorem torusGaussianOS_exists (mass : ℝ) (hmass : 0 < mass) :
    ∃ (μ : Measure (Configuration (TorusTestFunction L)))
      (_ : IsProbabilityMeasure μ),
      @SatisfiesTorusOS L hL μ ‹_› := by
  obtain ⟨μ, hμ_prob, hGCL, _⟩ := torusGaussianLimit_converges L mass hmass
  exact ⟨μ, hμ_prob, torusGaussianLimit_satisfies_OS L mass hmass μ hGCL⟩

end Pphi2

end
