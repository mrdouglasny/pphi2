/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder OS Axioms via Route B' IR Limit

States OS0–OS3 for the P(φ)₂ cylinder measure obtained as the IR limit
(Lt → ∞) of asymmetric torus measures from Route B'.

OS2 (invariance) is EXACT at every finite Lt — proved, not axiomatized.
OS0 (analyticity) and OS3 (reflection positivity) remain axiomatized
with documented proof routes.

## References

- Osterwalder-Schrader (1973, 1975)
- Glimm-Jaffe, *Quantum Physics*, Ch. 6, 19
-/

import Pphi2.IRLimit.IRTightness
import Pphi2.IRLimit.UniformExponentialMoment
import Pphi2.GeneralResults.ComplexAnalysis
import Cylinder.Symmetry
import Cylinder.PositiveTime
import Cylinder.ReflectionPositivity

noncomputable section

namespace Pphi2

open GaussianField MeasureTheory Filter

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]

/-! ## OS2: Translation and Reflection Invariance (EXACT)

Periodization perfectly intertwines continuous shifts:
  `periodize(shift_τ f)(t) = Σ_k f(t - τ + kLt) = shift_τ(periodize f)(t)`

So the cylinder pullback measure is EXACTLY translation-invariant and
time-reflection-invariant at every finite Lt. These are algebraic
identities, not limiting statements. -/

/-- **OS2 time translation**: The pulled-back cylinder measure is exactly
time-translation invariant at every finite Lt.

Proof: `Z_Lt(shift_τ f) = Z_Lt(f)` because periodization commutes with
time shifts. The torus measure is translation-invariant (proved in
AsymTorusOS), and `embed(shift_τ f) = shift_τ(embed f)` (periodization
intertwines shifts). -/
theorem cylinderPullback_timeTranslation_invariant
    (Lt : ℝ) [Fact (0 < Lt)]
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (hμ_os2 : ∀ v f, ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂μ =
      ∫ ω, Complex.exp (Complex.I * ↑(ω (asymTorusTranslation Lt Ls v f))) ∂μ)
    (τ : ℝ) (f : CylinderTestFunction Ls) :
    ∫ ω, Complex.exp (Complex.I * ↑(ω f))
      ∂(cylinderPullbackMeasure Lt Ls μ) =
    ∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderTranslation Ls 0 τ f)))
      ∂(cylinderPullbackMeasure Lt Ls μ) := by
  -- Both sides are ∫ exp(i·ω_torus(embed ?)) dμ via the pullback
  -- LHS: ∫ exp(i·ω_torus(embed f)) dμ
  -- RHS: ∫ exp(i·ω_torus(embed(T_{0,τ} f))) dμ
  --     = ∫ exp(i·ω_torus(T_{τ,0}(embed f))) dμ  (intertwining)
  --     = ∫ exp(i·ω_torus(embed f)) dμ  (torus translation invariance)
  -- So LHS = RHS.
  unfold cylinderPullbackMeasure
  have hmeas : Measurable (cylinderPullback Lt Ls) :=
    configuration_measurable_of_eval_measurable _
      (fun φ => configuration_eval_measurable _)
  have hasm : ∀ g : CylinderTestFunction Ls,
      AEStronglyMeasurable (fun ω => Complex.exp (Complex.I * ↑(ω g)))
        (Measure.map (cylinderPullback Lt Ls) μ) :=
    fun g => (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp
        (configuration_eval_measurable g)))).aestronglyMeasurable
  rw [integral_map hmeas.aemeasurable (hasm _),
      integral_map hmeas.aemeasurable (hasm _)]
  simp only [cylinderPullback_eval]
  simp_rw [cylinderToTorusEmbed_comp_timeTranslation]
  exact hμ_os2 (τ, 0) (cylinderToTorusEmbed Lt Ls f)

-- NOTE: This is "axiom" only because formalizing "periodization intertwines
-- shifts" requires periodizeCLM_comp_schwartzTranslation in gaussian-field.
-- The mathematical content is trivial: reindexing a sum over ℤ.

/-- **OS2 time reflection**: The pulled-back cylinder measure is exactly
time-reflection invariant at every finite Lt, provided the torus measure
is time-reflection invariant.

**Proof chain**:
1. `∫ exp(iωf) dν_Lt = ∫ exp(iω(embed f)) dμ` (pullback)
2. `= ∫ exp(iω(Θ_torus(embed f))) dμ` (torus reflection invariance)
3. `= ∫ exp(iω(embed(Θ f))) dμ` (intertwining: `embed ∘ Θ = Θ_torus ∘ embed`)
4. `= ∫ exp(iω(Θf)) dν_Lt` (pullback) -/
theorem cylinderPullback_timeReflection_invariant
    (Lt : ℝ) [Fact (0 < Lt)]
    (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
    [IsProbabilityMeasure μ]
    (hμ_refl : ∀ g : AsymTorusTestFunction Lt Ls,
      ∫ ω, Complex.exp (Complex.I * ↑(ω g)) ∂μ =
      ∫ ω, Complex.exp (Complex.I * ↑(ω (asymTorusTimeReflection Lt Ls g))) ∂μ)
    (f : CylinderTestFunction Ls) :
    ∫ ω, Complex.exp (Complex.I * ↑(ω f))
      ∂(cylinderPullbackMeasure Lt Ls μ) =
    ∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderTimeReflection Ls f)))
      ∂(cylinderPullbackMeasure Lt Ls μ) := by
  unfold cylinderPullbackMeasure
  have hmeas : Measurable (cylinderPullback Lt Ls) :=
    configuration_measurable_of_eval_measurable _
      (fun φ => configuration_eval_measurable _)
  have hasm : ∀ g : CylinderTestFunction Ls,
      AEStronglyMeasurable (fun ω => Complex.exp (Complex.I * ↑(ω g)))
        (Measure.map (cylinderPullback Lt Ls) μ) :=
    fun g => (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp
        (configuration_eval_measurable g)))).aestronglyMeasurable
  rw [integral_map hmeas.aemeasurable (hasm _),
      integral_map hmeas.aemeasurable (hasm _)]
  simp only [cylinderPullback_eval]
  simp_rw [cylinderToTorusEmbed_comp_timeReflection]
  exact hμ_refl (cylinderToTorusEmbed Lt Ls f)

/-! ## OS0: Analyticity (PROVED)

Uniform exponential moment bounds pass to the limit measure via truncation +
monotone convergence (BC weak convergence gives convergence for bounded
continuous truncations min(exp(|ωf|), M), then M → ∞). The limit measure
therefore has finite exponential moments, and `analyticOnNhd_integral`
gives analyticity of the generating functional. -/

/-- Exponential moments of the limit measure from uniform bounds + BC convergence.

If `∫ exp(|ω f|) dν_n ≤ B` for all n and ν_n → ν in the BC sense,
then `∫ exp(|ω f|) dν ≤ B`. Proof: min(exp(|·|), M) is bounded continuous,
so ∫ min(exp(|ωf|), M) dν = lim ∫ min(exp(|ωf|), M) dν_n ≤ B. Send M → ∞. -/
private theorem limit_exponential_moment
    (νseq : ℕ → Measure (Configuration (CylinderTestFunction Ls)))
    (hνseq_prob : ∀ n, IsProbabilityMeasure (νseq n))
    (ν : Measure (Configuration (CylinderTestFunction Ls)))
    [IsProbabilityMeasure ν]
    (hbc : ∀ (g : Configuration (CylinderTestFunction Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n => ∫ ω, g ω ∂(νseq n)) atTop (nhds (∫ ω, g ω ∂ν)))
    (f : CylinderTestFunction Ls) (B : ℝ)
    (h_unif : ∀ n, Integrable (fun ω => Real.exp (|ω f|)) (νseq n) ∧
      ∫ ω, Real.exp (|ω f|) ∂(νseq n) ≤ B) :
    Integrable (fun ω => Real.exp (|ω f|)) ν ∧
    ∫ ω, Real.exp (|ω f|) ∂ν ≤ B := by
  -- The key function: ω ↦ exp(|ω f|) ≥ 0
  have hexp_nn : ∀ ω : Configuration (CylinderTestFunction Ls), 0 ≤ Real.exp (|ω f|) :=
    fun ω => (Real.exp_pos _).le
  -- ω ↦ ω f is AEStronglyMeasurable (from Measurable, not Continuous.aestronglyMeasurable
  -- which would need OpensMeasurableSpace on the domain)
  have heval_ae : AEStronglyMeasurable
      (fun ω : Configuration (CylinderTestFunction Ls) => ω f) ν :=
    (configuration_eval_measurable f).aestronglyMeasurable
  -- ω ↦ ω f is continuous (evaluation in WeakDual), for continuity arguments
  have heval_cont : Continuous (fun ω : Configuration (CylinderTestFunction Ls) => ω f) :=
    WeakDual.eval_continuous f
  -- ω ↦ exp(|ω f|) is AEStronglyMeasurable (via comp_aestronglyMeasurable)
  have hexp_meas : AEStronglyMeasurable
      (fun ω : Configuration (CylinderTestFunction Ls) => Real.exp (|ω f|)) ν :=
    (Real.continuous_exp.comp continuous_abs).comp_aestronglyMeasurable heval_ae
  -- Nonnegativity of truncation
  have hgM_nn : ∀ (M : ℕ) (ω : Configuration (CylinderTestFunction Ls)),
      0 ≤ min (Real.exp (|ω f|)) (↑(M + 1) : ℝ) :=
    fun M ω => le_min (Real.exp_pos _).le (by positivity)
  -- Step 1-4: For each M, ∫ min(exp(|ω f|), M+1) dν ≤ B
  -- by using hbc (bounded-continuous convergence) + monotone comparison.
  have hgM_int_le : ∀ M : ℕ, ∫ ω, min (Real.exp (|ω f|)) (↑(M + 1) : ℝ) ∂ν ≤ B := by
    intro M
    -- min(exp(|·|), M+1) is continuous
    have hgM_cont : Continuous (fun ω : Configuration (CylinderTestFunction Ls) =>
        min (Real.exp (|ω f|)) (↑(M + 1) : ℝ)) :=
      (Real.continuous_exp.comp (continuous_abs.comp heval_cont)).min continuous_const
    -- min(exp(|·|), M+1) is bounded: absolute value ≤ ↑(M+1)
    have hgM_bound : ∃ C : ℝ, ∀ ω : Configuration (CylinderTestFunction Ls),
        |min (Real.exp (|ω f|)) (↑(M + 1) : ℝ)| ≤ C :=
      ⟨↑(M + 1), fun ω => by
        rw [abs_of_nonneg (hgM_nn M ω)]
        exact min_le_right _ _⟩
    -- By hbc: ∫ min(...) dν = lim_n ∫ min(...) dν_n
    have hbc_gM := hbc _ hgM_cont hgM_bound
    -- Each ∫ min(...) dν_n ≤ B (compare with exp bound, then use h_unif)
    have hgM_le_B : ∀ n, ∫ ω, min (Real.exp (|ω f|)) (↑(M + 1) : ℝ) ∂(νseq n) ≤ B :=
      fun n => (integral_mono_of_nonneg (ae_of_all _ (hgM_nn M)) (h_unif n).1
        (ae_of_all _ fun ω => min_le_left _ _)).trans (h_unif n).2
    -- Limit ≤ B (le_of_tendsto)
    exact le_of_tendsto hbc_gM (Eventually.of_forall hgM_le_B)
  -- Step 5: MCT via lintegral_iSup.
  -- The ENNReal truncations are measurable and monotone.
  have hgMenr_meas : ∀ M : ℕ, Measurable (fun ω : Configuration (CylinderTestFunction Ls) =>
      ENNReal.ofReal (min (Real.exp (|ω f|)) (↑(M + 1) : ℝ))) :=
    fun M => ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp
        (measurable_abs.comp (configuration_eval_measurable f))).min measurable_const)
  have hgMenr_mono : Monotone (fun (M : ℕ) (ω : Configuration (CylinderTestFunction Ls)) =>
      ENNReal.ofReal (min (Real.exp (|ω f|)) (↑(M + 1) : ℝ))) :=
    fun m n hmn ω => ENNReal.ofReal_le_ofReal
      (min_le_min_left _ (by exact_mod_cast Nat.add_le_add_right hmn 1))
  -- Pointwise iSup of truncations equals ENNReal.ofReal (exp(|ω f|))
  have hgMenr_iSup : ∀ ω : Configuration (CylinderTestFunction Ls),
      ⨆ M : ℕ, ENNReal.ofReal (min (Real.exp (|ω f|)) (↑(M + 1) : ℝ)) =
      ENNReal.ofReal (Real.exp (|ω f|)) := by
    intro ω
    apply le_antisymm
    · exact iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · apply le_iSup_of_le (Nat.ceil (Real.exp (|ω f|)))
      apply ENNReal.ofReal_le_ofReal
      apply le_min le_rfl
      have h1 : Real.exp (|ω f|) ≤ ↑⌈Real.exp (|ω f|)⌉₊ := Nat.le_ceil _
      have h2 : (⌈Real.exp (|ω f|)⌉₊ : ℝ) ≤ ↑(⌈Real.exp (|ω f|)⌉₊ + 1) := by
        push_cast; linarith
      linarith
  -- MCT: ∫⁻ exp(|·|) dν = sup_M ∫⁻ min(..., M+1) dν
  -- (using lintegral_iSup via the pointwise iSup identity)
  have hlint_iSup : ∫⁻ ω, ENNReal.ofReal (Real.exp (|ω f|)) ∂ν =
      ⨆ (M : ℕ), ∫⁻ ω, ENNReal.ofReal (min (Real.exp (|ω f|)) (↑(M + 1) : ℝ)) ∂ν := by
    have : (fun ω : Configuration (CylinderTestFunction Ls) =>
          ENNReal.ofReal (Real.exp (|ω f|))) =
        fun ω => ⨆ (M : ℕ), ENNReal.ofReal (min (Real.exp (|ω f|)) (↑(M + 1) : ℝ)) :=
      funext fun ω => (hgMenr_iSup ω).symm
    rw [this, lintegral_iSup hgMenr_meas hgMenr_mono]
  -- Each ∫⁻ min(..., M+1) dν ≤ ENNReal.ofReal B (via Bochner integral bound)
  have hlint_gM_le : ∀ (M : ℕ),
      ∫⁻ ω, ENNReal.ofReal (min (Real.exp (|ω f|)) (↑(M + 1) : ℝ)) ∂ν ≤
      ENNReal.ofReal B := by
    intro M
    have hgM_ae : AEStronglyMeasurable
        (fun ω : Configuration (CylinderTestFunction Ls) =>
          min (Real.exp (|ω f|)) (↑(M + 1) : ℝ)) ν :=
      ((Real.continuous_exp.comp continuous_abs).min continuous_const)
        |>.comp_aestronglyMeasurable heval_ae
    have hgM_integrable : Integrable
        (fun ω => min (Real.exp (|ω f|)) (↑(M + 1) : ℝ)) ν :=
      Integrable.of_bound hgM_ae (↑(M + 1) : ℝ) (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (hgM_nn M ω)]
        exact min_le_right _ _)
    rw [← ofReal_integral_eq_lintegral_ofReal hgM_integrable (ae_of_all _ (hgM_nn M))]
    exact ENNReal.ofReal_le_ofReal (hgM_int_le M)
  -- Supremum ≤ ENNReal.ofReal B
  have hlint_le : ∫⁻ ω, ENNReal.ofReal (Real.exp (|ω f|)) ∂ν ≤ ENNReal.ofReal B :=
    hlint_iSup ▸ iSup_le (fun (M : ℕ) => hlint_gM_le M)
  -- Step 6a: Integrability from finite lintegral
  have hint : Integrable (fun ω => Real.exp (|ω f|)) ν := by
    rw [← lintegral_ofReal_ne_top_iff_integrable hexp_meas (ae_of_all _ hexp_nn)]
    exact (hlint_le.trans_lt ENNReal.ofReal_lt_top).ne
  -- B is nonneg (since B ≥ ∫ exp|ωf| dν_0 ≥ 0)
  have hB_nn : 0 ≤ B :=
    le_trans (integral_nonneg (fun ω => hexp_nn ω)) (h_unif 0).2
  -- Step 6b: Integral ≤ B
  have hint_le : ∫ ω, Real.exp (|ω f|) ∂ν ≤ B := by
    have heq := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hexp_nn)
    rw [← heq] at hlint_le
    exact (ENNReal.ofReal_le_ofReal_iff hB_nn).mp hlint_le
  exact ⟨hint, hint_le⟩

/-- On a compact set K ⊆ (Fin n → ℂ), imaginary parts are uniformly bounded. -/
private lemma cylinderCompact_im_bound {n : ℕ} {K : Set (Fin n → ℂ)} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ i : Fin n, |Complex.im (z i)| ≤ C := by
  by_cases hKe : K.Nonempty
  · obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
    exact ⟨M, le_trans (norm_nonneg _) (hM _ hKe.some_mem), fun z hz i =>
      (Complex.abs_im_le_norm (z i)).trans ((norm_le_pi_norm z i).trans (hM z hz))⟩
  · exact ⟨0, le_refl _, fun z hz => absurd ⟨z, hz⟩ hKe⟩

/-- For aᵢ ≥ 0: exp(c · Σ aᵢ) ≤ Σ exp(n·c·aᵢ). -/
private lemma cylinderExp_mul_sum_le {n : ℕ} (hn : 0 < n) (c : ℝ) (hc : 0 ≤ c)
    (a : Fin n → ℝ) :
    Real.exp (c * ∑ i : Fin n, a i) ≤
    ∑ i : Fin n, Real.exp (↑n * c * a i) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set M := Finset.univ.sup' hne a
  have hM : ∀ i, a i ≤ M := fun i => Finset.le_sup' a (Finset.mem_univ i)
  have h_sum_le : ∑ i : Fin n, a i ≤ ↑n * M :=
    (Finset.sum_le_sum (fun i _ => hM i)).trans
      (by simp [Finset.sum_const, nsmul_eq_mul])
  have h1 : Real.exp (c * ∑ i, a i) ≤ Real.exp (↑n * c * M) :=
    Real.exp_le_exp_of_le (by nlinarith)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' hne a
  exact h1.trans ((congr_arg Real.exp (by rw [← hj])).le.trans
    (Finset.single_le_sum (f := fun i => Real.exp (↑n * c * a i))
      (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ j)))

/-! ## OS3: Reflection Positivity (axiomatized)

Via compact support density: for `f ∈ C_c^∞((0,R) × S¹)` and `Lt > 2R`,
`embed f` has no wrap-around, so torus RP applies. Pass through IR limit.
Extend by density of `C_c^∞` in the positive Schwartz space. -/

axiom cylinderIR_os3
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (ν : Measure (Configuration (CylinderTestFunction Ls)))
    [IsProbabilityMeasure ν]
    (n : ℕ) (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls)) (c : Fin n → ℂ) :
    0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
      ∫ ω, Complex.exp (Complex.I *
        ↑(ω ((f i : CylinderTestFunction Ls) -
          cylinderTimeReflection Ls (f j : CylinderTestFunction Ls)))) ∂ν).re

/-! ## Main theorem -/

/-- **Route B' main theorem**: the IR limit satisfies OS0+OS2+OS3. -/
theorem routeBPrime_cylinder_OS
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Lt : ℕ → ℝ) (hLt : ∀ n, Fact (0 < Lt n))
    (hLt_tend : Tendsto Lt atTop atTop)
    (μ : ∀ n, Measure (Configuration (AsymTorusTestFunction (Lt n) Ls)))
    (hμ_prob : ∀ n, IsProbabilityMeasure (μ n))
    (hμ_os : ∀ n, @AsymSatisfiesTorusOS (Lt n) Ls _ _ (μ n) (hμ_prob n)) :
    ∃ (ν : Measure (Configuration (CylinderTestFunction Ls))),
    IsProbabilityMeasure ν ∧
    -- OS0
    (∀ (n : ℕ) (J : Fin n → CylinderTestFunction Ls),
      AnalyticOnNhd ℂ (fun z : Fin n → ℂ =>
        ∫ ω, Complex.exp (∑ i, Complex.I * z i * ↑(ω (J i))) ∂ν) Set.univ) ∧
    -- OS2 time reflection
    (∀ (f : CylinderTestFunction Ls),
      ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν =
      ∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderTimeReflection Ls f))) ∂ν) ∧
    -- OS2 time translation
    (∀ (τ : ℝ) (f : CylinderTestFunction Ls),
      ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν =
      ∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderTranslation Ls 0 τ f))) ∂ν) ∧
    -- OS2 spatial translation
    (∀ (v : ℝ) (f : CylinderTestFunction Ls),
      ∫ ω, Complex.exp (Complex.I * ↑(ω f)) ∂ν =
      ∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderSpatialTranslation Ls v f))) ∂ν) ∧
    -- OS3
    (∀ (n : ℕ) (f : Fin n → ↥(cylinderPositiveTimeSubmodule Ls)) (c : Fin n → ℂ),
      0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
        ∫ ω, Complex.exp (Complex.I *
          ↑(ω ((f i : CylinderTestFunction Ls) -
            cylinderTimeReflection Ls (f j : CylinderTestFunction Ls)))) ∂ν).re) := by
  have ⟨φ, ν, hφ, rest⟩ :=
    cylinderIRLimit_exists Ls P mass hmass Lt hLt hLt_tend μ hμ_prob hμ_os
  haveI : IsProbabilityMeasure ν := rest.1
  have hν_bc_and_cf := rest.2
  have hν_bc := hν_bc_and_cf.1
  have hν_conv := hν_bc_and_cf.2
  -- Exponential moments of the limit measure: from uniform exp moment bound
  -- on the pullback measures + BC weak convergence + truncation/MCT.
  have h_exp_limit : ∀ f : CylinderTestFunction Ls,
      Integrable (fun ω : Configuration (CylinderTestFunction Ls) =>
        Real.exp (|ω f|)) ν := by
    intro f
    -- Step 1: Get uniform exp moment constants K, C, q from the axiom.
    obtain ⟨K, C, q, hK, hC, hq_cont, h_exp⟩ :=
      cylinderIR_uniform_exponential_moment Ls P mass hmass
    -- Step 2: Get N0 such that ∀ n ≥ N0, 1 ≤ Lt n (from hLt_tend).
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 (tendsto_atTop.1 hLt_tend 1)
    -- Step 3: Use shifted sequence n ↦ φ (n + N0) so Lt (φ (n + N0)) ≥ 1 for all n.
    -- φ strictly mono implies φ m ≥ m for all m, so φ (n + N0) ≥ n + N0 ≥ N0.
    have hLt_shift : ∀ n, 1 ≤ Lt (φ (n + N0)) :=
      fun n => hN0 (φ (n + N0)) ((Nat.le_add_left N0 n).trans (hφ.id_le (n + N0)))
    -- Step 4: Define the shifted measure sequence.
    let νseq' : ℕ → Measure (Configuration (CylinderTestFunction Ls)) :=
      fun n => cylinderPullbackMeasure (Lt (φ (n + N0))) Ls (μ (φ (n + N0)))
    -- Step 5: νseq' n is a probability measure for all n.
    have hνseq'_prob : ∀ n, IsProbabilityMeasure (νseq' n) := by
      intro n
      simp only [νseq', cylinderPullbackMeasure]
      haveI : Fact (0 < Lt (φ (n + N0))) := hLt (φ (n + N0))
      haveI : IsProbabilityMeasure (μ (φ (n + N0))) := hμ_prob (φ (n + N0))
      have hmeas : Measurable (cylinderPullback (Lt (φ (n + N0))) Ls) :=
        configuration_measurable_of_eval_measurable _
          (fun g => configuration_eval_measurable _)
      exact Measure.isProbabilityMeasure_map hmeas.aemeasurable
    -- Step 6: νseq' → ν in BC sense (from hν_bc via shift by N0).
    have hbc' : ∀ (g : Configuration (CylinderTestFunction Ls) → ℝ),
        Continuous g → (∃ C', ∀ x, |g x| ≤ C') →
        Tendsto (fun n => ∫ ω, g ω ∂(νseq' n)) atTop (nhds (∫ ω, g ω ∂ν)) := by
      intro g hg_cont hg_bdd
      exact (tendsto_add_atTop_iff_nat N0).mpr (hν_bc g hg_cont hg_bdd)
    -- Step 7: Apply the uniform exp moment bound for all n in νseq' (since Lt ≥ 1).
    have h_unif : ∀ n,
        Integrable (fun ω => Real.exp (|ω f|)) (νseq' n) ∧
        ∫ ω : Configuration (CylinderTestFunction Ls),
          Real.exp (|ω f|) ∂(νseq' n) ≤ K * Real.exp (C * q f ^ 2) := by
      intro n
      simp only [νseq']
      haveI : Fact (0 < Lt (φ (n + N0))) := hLt (φ (n + N0))
      haveI : IsProbabilityMeasure (μ (φ (n + N0))) := hμ_prob (φ (n + N0))
      exact h_exp (Lt (φ (n + N0))) (hLt_shift n) (μ (φ (n + N0)))
        (hμ_os (φ (n + N0))) f
    -- Step 8: Apply limit_exponential_moment and extract integrability.
    exact (limit_exponential_moment Ls νseq' hνseq'_prob ν hbc' f
      (K * Real.exp (C * q f ^ 2)) h_unif).1
  refine ⟨ν, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · -- OS0: Analyticity via analyticOnNhd_integral
    -- The limit measure has exponential moments (from uniform bounds + BC convergence),
    -- so the integrand is dominated on compact sets. Same proof pattern as torus OS0.
    intro n J
    apply analyticOnNhd_integral
    · -- Pointwise analyticity: z ↦ exp(Σ i·zⱼ·ω(Jⱼ)) is entire for each ω
      -- Same argument as asymTorusInteracting_os0: exp of analytic sum
      intro ω z _
      apply AnalyticAt.cexp'
      apply Finset.analyticAt_fun_sum
      intro i _
      exact (analyticAt_const.mul
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i).analyticAt z)).mul
        analyticAt_const
    · -- Measurability: F(z, ·) is ae strongly measurable for each z
      -- exp ∘ (measurable sum of measurable terms)
      intro z
      apply (Complex.measurable_exp.comp _).aestronglyMeasurable
      exact Finset.measurable_sum Finset.univ (fun i _ =>
        measurable_const.mul
          (Complex.measurable_ofReal.comp (configuration_eval_measurable (J i))))
    · -- Domination: on compact K, ‖F(z, ω)‖ ≤ bound(ω), bound integrable
      intro K hK
      obtain ⟨C_K, hC_K_nn, hC_K⟩ := cylinderCompact_im_bound hK
      by_cases hn : n = 0
      · -- n = 0: integrand is exp(0) = 1, bounded by 1
        subst hn
        exact ⟨fun _ => 1, integrable_const 1, fun z _ => ae_of_all ν fun ω => by
          simp only [Finset.univ_eq_empty, Finset.sum_empty, Complex.exp_zero, norm_one]; rfl⟩
      · -- n > 0: bound by Σᵢ exp(n · C_K · |ω(Jᵢ)|)
        set bound := fun ω : Configuration (CylinderTestFunction Ls) =>
          ∑ i : Fin n, Real.exp (↑n * C_K * |ω (J i)|) with hbound_def
        refine ⟨bound, ?_, fun z hz => ae_of_all ν fun ω => ?_⟩
        · -- Integrability of bound: each term exp(n·C_K·|ω(Jᵢ)|) is integrable
          apply integrable_finset_sum; intro i _
          have hscale : ∀ ω : Configuration (CylinderTestFunction Ls),
              Real.exp (↑n * C_K * |ω (J i)|) =
              Real.exp (|ω ((↑n * C_K) • J i)|) := by
            intro ω
            rw [map_smul, smul_eq_mul, abs_mul,
                abs_of_nonneg (mul_nonneg (Nat.cast_nonneg' n) hC_K_nn)]
          simp_rw [hscale]
          exact h_exp_limit ((↑n * C_K) • J i)
        · -- Pointwise bound: ‖F(z, ω)‖ ≤ bound(ω) for z ∈ K
          rw [Complex.norm_exp]
          have h_re : (∑ i : Fin n, Complex.I * z i * ↑(ω (J i))).re =
              -(∑ i : Fin n, (z i).im * ω (J i)) := by
            simp only [Complex.re_sum, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul,
              zero_sub, neg_mul, sub_zero, Finset.sum_neg_distrib]
          rw [h_re]
          calc Real.exp (-(∑ i : Fin n, (z i).im * ω (J i)))
              ≤ Real.exp (|∑ i : Fin n, (z i).im * ω (J i)|) :=
                Real.exp_le_exp_of_le (neg_le_abs _)
            _ ≤ Real.exp (C_K * ∑ i : Fin n, |ω (J i)|) := by
                apply Real.exp_le_exp_of_le
                calc |∑ i, (z i).im * ω (J i)|
                    ≤ ∑ i, |(z i).im * ω (J i)| := Finset.abs_sum_le_sum_abs _ _
                  _ = ∑ i, |(z i).im| * |ω (J i)| := by
                      congr 1; ext i; rw [abs_mul]
                  _ ≤ ∑ i, C_K * |ω (J i)| :=
                      Finset.sum_le_sum (fun i _ =>
                        mul_le_mul_of_nonneg_right (hC_K z hz i) (abs_nonneg _))
                  _ = C_K * ∑ i, |ω (J i)| := (Finset.mul_sum _ _ _).symm
            _ ≤ bound ω := cylinderExp_mul_sum_le (Nat.pos_of_ne_zero hn) C_K hC_K_nn _
  · -- OS2: time reflection passes through the weak limit
    -- At each finite Lt, reflection is exact (cylinderPullback_timeReflection_invariant)
    -- Taking the limit, both sides converge to the same value.
    intro f
    -- Z_{Lt_n}(f) → Z(f) by characteristic functional convergence
    have hL := hν_conv f
    -- Z_{Lt_n}(Θf) → Z(Θf) by convergence applied to Θf
    have hR := hν_conv (cylinderTimeReflection Ls f)
    -- But Z_{Lt_n}(f) = Z_{Lt_n}(Θf) at each finite Lt_n (exact reflection invariance)
    have h_eq : ∀ n,
        (∫ ω, Complex.exp (Complex.I * ↑(ω f))
          ∂(cylinderPullbackMeasure (Lt (φ n)) Ls (μ (φ n)))) =
        (∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderTimeReflection Ls f)))
          ∂(cylinderPullbackMeasure (Lt (φ n)) Ls (μ (φ n)))) := by
      intro n
      exact @cylinderPullback_timeReflection_invariant Ls _ (Lt (φ n)) (hLt (φ n))
        (μ (φ n)) (hμ_prob (φ n))
        (fun g => (hμ_os (φ n)).os2_timeReflection g)
        f
    -- Since Z_{Lt_n}(f) = Z_{Lt_n}(Θf) and both converge, their limits agree
    exact tendsto_nhds_unique hL (hR.congr (fun n => (h_eq n).symm))
  · -- OS2: time translation passes through (exact at finite Lt)
    intro τ f
    have hL := hν_conv f
    have hR := hν_conv (cylinderTranslation Ls 0 τ f)
    have h_eq : ∀ n,
        (∫ ω, Complex.exp (Complex.I * ↑(ω f))
          ∂(cylinderPullbackMeasure (Lt (φ n)) Ls (μ (φ n)))) =
        (∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderTranslation Ls 0 τ f)))
          ∂(cylinderPullbackMeasure (Lt (φ n)) Ls (μ (φ n)))) := by
      intro n
      exact @cylinderPullback_timeTranslation_invariant Ls _ (Lt (φ n)) (hLt (φ n))
        (μ (φ n)) (hμ_prob (φ n))
        (fun v g => (hμ_os (φ n)).os2_translation v g)
        τ f
    exact tendsto_nhds_unique hL (hR.congr (fun n => (h_eq n).symm))
  · -- OS2: spatial translation (exact at finite Lt via torus spatial invariance)
    intro v f
    have hL := hν_conv f
    have hR := hν_conv (cylinderSpatialTranslation Ls v f)
    have h_eq : ∀ n,
        (∫ ω, Complex.exp (Complex.I * ↑(ω f))
          ∂(cylinderPullbackMeasure (Lt (φ n)) Ls (μ (φ n)))) =
        (∫ ω, Complex.exp (Complex.I * ↑(ω (cylinderSpatialTranslation Ls v f)))
          ∂(cylinderPullbackMeasure (Lt (φ n)) Ls (μ (φ n)))) := by
      intro n
      unfold cylinderPullbackMeasure
      have hmeas : Measurable (cylinderPullback (Lt (φ n)) Ls) :=
        configuration_measurable_of_eval_measurable _
          (fun g => configuration_eval_measurable _)
      have hasm : ∀ g : CylinderTestFunction Ls,
          AEStronglyMeasurable (fun ω => Complex.exp (Complex.I * ↑(ω g)))
            (Measure.map (cylinderPullback (Lt (φ n)) Ls) (μ (φ n))) :=
        fun g => (Complex.measurable_exp.comp (measurable_const.mul
          (Complex.measurable_ofReal.comp
            (configuration_eval_measurable g)))).aestronglyMeasurable
      rw [integral_map hmeas.aemeasurable (hasm _),
          integral_map hmeas.aemeasurable (hasm _)]
      simp only [cylinderPullback_eval]
      simp_rw [cylinderToTorusEmbed_comp_spatialTranslation]
      exact (hμ_os (φ n)).os2_translation (0, v) (cylinderToTorusEmbed (Lt (φ n)) Ls f)
    exact tendsto_nhds_unique hL (hR.congr (fun n => (h_eq n).symm))
  · -- OS3: reflection positivity
    intro n f c; exact cylinderIR_os3 Ls P mass hmass ν n f c

end Pphi2
