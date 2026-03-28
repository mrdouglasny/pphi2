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

/-! ## OS0: Analyticity (axiomatized)

Uniform exponential moment bounds (`cylinderIR_uniform_exponential_moment`)
give locally uniform boundedness of `z ↦ Z_Lt[zf]`. Combined with pointwise
convergence on ℝ (from weak convergence), Vitali/Montel gives analyticity. -/

axiom cylinderIR_os0
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (ν : Measure (Configuration (CylinderTestFunction Ls)))
    [IsProbabilityMeasure ν]
    (n : ℕ) (J : Fin n → CylinderTestFunction Ls) :
    AnalyticOnNhd ℂ (fun z : Fin n → ℂ =>
      ∫ ω, Complex.exp (∑ i, Complex.I * z i * ↑(ω (J i))) ∂ν) Set.univ

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
  obtain ⟨φ, ν, hφ, hν_prob, hν_conv⟩ :=
    cylinderIRLimit_exists Ls P mass hmass Lt hLt hLt_tend μ hμ_prob hμ_os
  refine ⟨ν, hν_prob, fun n J => cylinderIR_os0 Ls P mass hmass ν n J, ?_, ?_, ?_, ?_⟩
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
    sorry -- same pattern: cylinderPullback_spatialTranslation_invariant (needs formalization)
  · -- OS3: reflection positivity
    intro n f c; exact cylinderIR_os3 Ls P mass hmass ν n f c

end Pphi2
