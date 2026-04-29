/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tightness of the Continuum-Embedded Measures

Shows that the family of continuum-embedded interacting measures
`{ν_a}_{a ∈ (0,1]}` is tight in S'(ℝ^d). This is the key technical step
enabling extraction of a convergent subsequence via Prokhorov's theorem.

## Main results

- `continuum_second_moment_uniform` — uniform bound on `∫ (ω f)² dν_a`
- `continuumMeasures_tight` — tightness of `{ν_a}` in S'(ℝ^d)

## Strategy

Port of the torus tightness pipeline
(`torus_second_moment_uniform` → `torusContinuumMeasures_tight`) to ℝ^d:

1. Uniform second moments transfer from the Gaussian free field case
   (`gaussian_second_moment_uniform`) via the interacting-to-Gaussian
   Cauchy-Schwarz bound (`interacting_moment_bound` at `n = 1, p = 2`):
     `∫ |ωf|² dν_a ≤ C·(2p-1)^{pn/2}·(∫|ωf|² dν_{GFF,a})^{p/2}
                   = 3C·(∫|ωf|² dν_{GFF,a})`.
2. Tightness follows from the Mitoma-Chebyshev criterion on a nuclear
   dual: `configuration_tight_of_uniform_second_moments`.

## References

- Mitoma (1983), "Tightness of probabilities on C([0,1]; S') and D([0,1]; S')"
- Simon, *The P(φ)₂ Euclidean QFT*, §V.1
- Glimm-Jaffe, *Quantum Physics*, §19.4
-/

import Pphi2.ContinuumLimit.Hypercontractivity
import Pphi2.GaussianContinuumLimit.GaussianTightness

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (d N : ℕ) [NeZero N] [Fact (0 < d)]

/-! ## Uniform second moment bound for the interacting continuum measure -/

/-- **Uniform bound on interacting continuum second moments.**

`∫ (ω f)² dν_a ≤ C(f, m, P)` uniformly in `a ∈ (0, 1]`.

Derived from `interacting_moment_bound` at `n = 1, p = 2, m = 1` + the
uniform Gaussian bound `gaussian_second_moment_uniform`:
  `∫ |ωf|² dν_a ≤ K · 3 · ∫ |ωf|² dν_{GFF,a} ≤ 3·K·C_G`. -/
theorem continuum_second_moment_uniform (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) (f : ContinuumTestFunction d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∫ ω : Configuration (ContinuumTestFunction d),
      (ω f) ^ 2 ∂(continuumMeasure d N P a mass ha hmass) ≤ C := by
  obtain ⟨C_gauss, hCG_pos, hCG⟩ := gaussian_second_moment_uniform d N mass hmass f
  obtain ⟨K, hK_pos, hK⟩ := interacting_moment_bound d N P mass hmass
  refine ⟨3 * K * C_gauss, by positivity, fun a ha ha_le => ?_⟩
  -- Apply the interacting moment bound at n = 1, p = 2, m = 1
  have hp_eq : (2 : ℝ) = 2 * ((1 : ℕ) : ℝ) := by norm_num
  have hK_inst := hK 1 2 1 le_rfl hp_eq f a ha ha_le
  -- Normalise all ℝ-arithmetic on RHS (↑1 = 1, 2·1 = 2, 2·2-1 = 3, 2/2 = 1, _^(1:ℝ) = _)
  simp only [Nat.cast_one, mul_one,
             show ((2 : ℝ) * 2 - 1) = 3 from by norm_num,
             show ((2 : ℝ) / 2) = 1 from by norm_num,
             Real.rpow_one] at hK_inst
  -- Convert `|ω f|^(2:ℝ)` (rpow) to `(ω f)^2` (npow) in both integrals
  have h_int_eq : ∀ (ν : Measure (Configuration (ContinuumTestFunction d))),
      ∫ ω, |ω f| ^ (2 : ℝ) ∂ν = ∫ ω, (ω f) ^ 2 ∂ν := fun ν => by
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    calc |ω f| ^ (2 : ℝ) = |ω f| ^ ((2 : ℕ) : ℝ) := by norm_num
      _ = |ω f| ^ (2 : ℕ) := Real.rpow_natCast _ 2
      _ = (ω f) ^ 2 := sq_abs _
  simp_rw [h_int_eq] at hK_inst
  -- `Measure.map (latticeEmbedLift ...) (latticeGaussianMeasure ...)` = `gaussianContinuumMeasure`
  have h_gauss_eq : Measure.map (latticeEmbedLift d N a ha)
      (latticeGaussianMeasure d N a mass ha hmass) =
      gaussianContinuumMeasure d N a mass ha hmass := rfl
  rw [h_gauss_eq] at hK_inst
  -- Chain: ∫(ωf)² d(continuum) ≤ K · 3 · (∫ |ωf|²/² d(gaussian)) ≤ K · 3 · C_gauss
  have h_gauss_bound := hCG a ha ha_le
  calc ∫ ω, (ω f) ^ 2 ∂(continuumMeasure d N P a mass ha hmass)
      ≤ K * 3 * (∫ ω, |ω f| ^ 2
          ∂(gaussianContinuumMeasure d N a mass ha hmass)) := hK_inst
    _ = K * 3 * (∫ ω, (ω f) ^ 2
          ∂(gaussianContinuumMeasure d N a mass ha hmass)) := by
        congr 1
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        exact sq_abs _
    _ ≤ K * 3 * C_gauss := by
        apply mul_le_mul_of_nonneg_left h_gauss_bound
        positivity
    _ = 3 * K * C_gauss := by ring

/-! ## Integrability of `(ω f)²` under the interacting continuum measure -/

/-- Integrability of the squared evaluation functional under the interacting
continuum measure.

Mirrors `gaussianContinuumMeasure_sq_integrable`: push through
`integrable_map_measure`, rewrite `(ι ω) f = ω g_f` where
`g_f = latticeTestField`, and reduce to lattice integrability. The
interacting case dominates `bw ω ≤ exp(B)` to transfer from the Gaussian
L²-integrability (`pairing_product_integrable`). -/
private theorem continuumMeasure_sq_integrable
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : ContinuumTestFunction d) :
    Integrable (fun ω : Configuration (ContinuumTestFunction d) =>
      (ω f) ^ 2) (continuumMeasure d N P a mass ha hmass) := by
  -- Push through Measure.map to reduce to lattice integrability.
  unfold continuumMeasure
  apply (integrable_map_measure
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
    (latticeEmbedLift_measurable d N a ha).aemeasurable).mpr
  -- Rewrite using `latticeEmbedLift_eval_eq`: `(ι ω) f = ω g_f`
  set g_f := latticeTestField d N a f
  have h_eval : ∀ ω : Configuration (FinLatticeField d N),
      (latticeEmbedLift d N a ha ω) f = ω g_f :=
    fun ω => latticeEmbedLift_eval_eq d N a ha f ω
  have h_congr :
      ((fun ω : Configuration (ContinuumTestFunction d) => (ω f) ^ 2) ∘
        latticeEmbedLift d N a ha) =
      fun ω : Configuration (FinLatticeField d N) => (ω g_f) * (ω g_f) := by
    ext ω
    simp only [Function.comp, h_eval, sq]
  rw [h_congr]
  -- Goal: Integrable (fun ω => (ω g_f) * (ω g_f)) (interactingLatticeMeasure ...)
  -- Now follow the `field_second_moment_finite` pattern for general g_f.
  obtain ⟨B, hB⟩ := interactionFunctional_bounded_below d N P a mass ha hmass
  have hZ := partitionFunction_pos d N P a mass ha hmass
  set μ_GFF := latticeGaussianMeasure d N a mass ha hmass
  set bw := boltzmannWeight d N P a mass
  -- Step 1: reduce via `interactingLatticeMeasure` definition
  suffices h : Integrable (fun ω : Configuration (FinLatticeField d N) =>
      (ω g_f) * (ω g_f))
      (μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) by
    unfold interactingLatticeMeasure
    exact h.smul_measure (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ).ne'))
  -- Step 2: withDensity → multiplicative weight under μ_GFF
  have hf_meas : Measurable (fun ω : Configuration (FinLatticeField d N) =>
      ENNReal.ofReal (bw ω)) :=
    ENNReal.measurable_ofReal.comp
      ((interactionFunctional_measurable d N P a mass).neg.exp)
  apply (integrable_withDensity_iff hf_meas
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  have hbw_simp : ∀ ω : Configuration (FinLatticeField d N),
      (ENNReal.ofReal (bw ω)).toReal = bw ω :=
    fun ω => ENNReal.toReal_ofReal (le_of_lt (boltzmannWeight_pos d N P a mass ω))
  simp_rw [hbw_simp]
  -- Goal: Integrable (fun ω => (ω g_f)*(ω g_f) * bw ω) μ_GFF
  -- Step 3: L² integrability of (ω g_f)*(ω g_f) under μ_GFF via pairing_product_integrable
  have h_sq_int : Integrable (fun ω : Configuration (FinLatticeField d N) =>
      (ω g_f) * (ω g_f)) μ_GFF := by
    have : μ_GFF = GaussianField.measure (latticeCovariance d N a mass ha hmass) := rfl
    rw [this]
    exact pairing_product_integrable
      (latticeCovariance d N a mass ha hmass) g_f g_f
  -- Step 4: dominate (ω g_f)*(ω g_f) * bw ω by (ω g_f)*(ω g_f) * exp(B)
  apply (h_sq_int.mul_const (Real.exp B)).mono
  · exact
      (((configuration_eval_measurable g_f).mul
        (configuration_eval_measurable g_f)).aestronglyMeasurable).mul
        ((interactionFunctional_measurable d N P a mass).neg.exp.aestronglyMeasurable)
  · exact Filter.Eventually.of_forall fun ω => by
      simp only [Real.norm_eq_abs]
      have h1 : 0 ≤ (ω g_f) * (ω g_f) := mul_self_nonneg _
      have h2 : 0 < bw ω := boltzmannWeight_pos d N P a mass ω
      have h3 : bw ω ≤ Real.exp B := by
        change Real.exp (-interactionFunctional d N P a mass ω) ≤ Real.exp B
        exact Real.exp_le_exp_of_le (by linarith [hB ω])
      rw [abs_of_nonneg (mul_nonneg h1 (le_of_lt h2)),
          abs_of_nonneg (mul_nonneg h1 (le_of_lt (Real.exp_pos B)))]
      exact mul_le_mul_of_nonneg_left h3 h1

/-! ## Tightness -/

/-- **Tightness of the continuum-embedded interacting measures.**

The family `{ν_a = (ι_a)_* μ_a}_{a ∈ (0, 1]}` is tight on
`Configuration (ContinuumTestFunction d) = S'(ℝ^d)`.

**Proof**: apply `configuration_tight_of_uniform_second_moments` with
`ι = { a : ℝ // 0 < a ∧ a ≤ 1 }`, the probability structure from
`continuumMeasure_isProbability`, the integrability from
`continuumMeasure_sq_integrable`, and the uniform second moment bound
from `continuum_second_moment_uniform`. The nuclearity hypothesis is
provided by `schwartz_dyninMityaginSpace` (requires `0 < d`). -/
theorem continuumMeasures_tight (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) :
    ∀ ε : ℝ, 0 < ε →
    ∃ (K : Set (Configuration (ContinuumTestFunction d))),
      IsCompact K ∧
      ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
      1 - ε ≤ (continuumMeasure d N P a mass ha hmass K).toReal := by
  intro ε hε
  have hd : 0 < d := Fact.out
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) := inferInstance
  haveI : DyninMityaginSpace (ContinuumTestFunction d) := schwartz_dyninMityaginSpace
  set ι := { a : ℝ // 0 < a ∧ a ≤ 1 }
  set μ : ι → Measure (Configuration (ContinuumTestFunction d)) :=
    fun i => continuumMeasure d N P i.val mass i.prop.1 hmass
  have hprob : ∀ i : ι, IsProbabilityMeasure (μ i) :=
    fun i => continuumMeasure_isProbability d N P i.val mass i.prop.1 hmass
  have h_int :
      ∀ (f : ContinuumTestFunction d) (i : ι),
      Integrable (fun ω : Configuration (ContinuumTestFunction d) =>
        (ω f) ^ 2) (μ i) :=
    fun f i =>
      continuumMeasure_sq_integrable d N P i.val mass i.prop.1 hmass f
  have h_moments :
      ∀ f : ContinuumTestFunction d, ∃ C : ℝ, ∀ i : ι,
      ∫ ω : Configuration (ContinuumTestFunction d),
        (ω f) ^ 2 ∂(μ i) ≤ C := by
    intro f
    obtain ⟨C, _, hC⟩ := continuum_second_moment_uniform d N P mass hmass f
    exact ⟨C, fun i => hC i.val i.prop.1 i.prop.2⟩
  obtain ⟨K, hK_compact, hK_mass⟩ :=
    configuration_tight_of_uniform_second_moments
      μ hprob h_int h_moments ε hε
  exact ⟨K, hK_compact, fun a ha ha_le => hK_mass ⟨a, ha, ha_le⟩⟩

end Pphi2

end
