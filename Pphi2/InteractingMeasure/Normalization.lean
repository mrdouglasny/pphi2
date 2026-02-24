/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Normalization and Well-Definedness

Further properties of the interacting lattice measure: integrability of
observables, moment bounds, and connection to FKG.

## Main results

- `observable_integrable` — bounded continuous observables are integrable
- `fkg_interacting` — FKG inequality for the interacting measure
- `interacting_moment_bound` — moment bounds for field evaluations

## Mathematical background

The interacting measure `dμ_a = (1/Z) exp(-V_a) dμ_{GFF}` inherits good
properties from both the Gaussian measure and the interaction:

1. The Gaussian measure provides Fernique-type moment bounds.
2. The interaction `V_a` is bounded below, so `exp(-V_a)` is bounded above.
3. The interaction is convex (for convex P), enabling FKG from gaussian-field.

## References

- Glimm-Jaffe, *Quantum Physics*, §19.2
- Simon, *The P(φ)₂ Euclidean QFT*, §II.2
-/

import Pphi2.InteractingMeasure.LatticeMeasure
import Lattice.FKG

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (d N : ℕ) [NeZero N]

/-! ## Integrability of observables -/

/-- Bounded measurable functions are integrable under the interacting measure.

Since μ_a is a probability measure (or at least finite), any bounded
measurable function is integrable. -/
theorem bounded_integrable_interacting (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (F : Configuration (FinLatticeField d N) → ℝ)
    (hF_bound : ∃ C, ∀ ω, |F ω| ≤ C)
    (hF_meas : @Measurable _ _ instMeasurableSpaceConfiguration
      (borel ℝ) F) :
    Integrable F (interactingLatticeMeasure d N P a mass ha hmass) := by
  obtain ⟨C, hC⟩ := hF_bound
  haveI := interactingLatticeMeasure_isProbability d N P a mass ha hmass
  exact Integrable.of_bound hF_meas.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs]; exact hC ω))

/-! ## Moment bounds

Field evaluations ω(δ_x) have finite moments of all orders under the
interacting measure. This follows from the Gaussian moments (Fernique)
combined with the fact that exp(-V) is bounded above. -/

/-- Field evaluations have finite second moments under the interacting measure.

  `∫ |ω(δ_x)|² dμ_a(ω) < ∞`

Proof: `|ω(δ_x)|² exp(-V) ≤ |ω(δ_x)|² exp(B)`, and the Gaussian integral
of `|ω(δ_x)|²` is finite (= G_a(x,x) = c_a) by `pairing_memLp`. -/
theorem field_second_moment_finite (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (x : FinLatticeSites d N) :
    Integrable (fun ω : Configuration (FinLatticeField d N) =>
      (ω (finLatticeDelta d N x)) ^ 2)
      (interactingLatticeMeasure d N P a mass ha hmass) := by
  -- Setup
  obtain ⟨B, hB⟩ := interactionFunctional_bounded_below d N P a mass ha hmass
  have hZ := partitionFunction_pos d N P a mass ha hmass
  set μ_GFF := latticeGaussianMeasure d N a mass ha hmass with hμ_def
  set δx := finLatticeDelta d N x
  set bw := boltzmannWeight d N P a mass
  -- The interacting measure = (1/Z) • μ_GFF.withDensity(bw)
  -- Strategy: reduce to integrability under Gaussian via measure decomposition
  -- Step 1: Suffices to show integrability under μ_GFF.withDensity
  suffices h : Integrable (fun ω : Configuration (FinLatticeField d N) =>
      (ω δx) ^ 2)
      (μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) by
    unfold interactingLatticeMeasure
    exact h.smul_measure (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ).ne'))
  -- Step 2: Reduce withDensity to multiplicative weight under Gaussian
  -- Using integrable_withDensity_iff (f := density, g := our function)
  have hf_meas : Measurable (fun ω : Configuration (FinLatticeField d N) =>
      ENNReal.ofReal (bw ω)) :=
    ENNReal.measurable_ofReal.comp ((interactionFunctional_measurable d N P a mass).neg.exp)
  apply (integrable_withDensity_iff hf_meas
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  -- Goal: Integrable (fun ω => (ω δx)^2 * (ENNReal.ofReal (bw ω)).toReal) μ_GFF
  -- Simplify toReal ∘ ofReal = id (since bw > 0)
  have hbw_simp : ∀ ω : Configuration (FinLatticeField d N),
      (ENNReal.ofReal (bw ω)).toReal = bw ω :=
    fun ω => ENNReal.toReal_ofReal (le_of_lt (boltzmannWeight_pos d N P a mass ω))
  simp_rw [hbw_simp]
  -- Goal: Integrable (fun ω => (ω δx)^2 * bw ω) μ_GFF
  -- Step 3: Get Gaussian integrability of (ω δx)²
  have h_sq_int : Integrable (fun ω : Configuration (FinLatticeField d N) =>
      (ω δx) ^ 2) μ_GFF := by
    have := pairing_product_integrable (latticeCovariance d N a mass ha hmass) δx δx
    simp only [sq]
    exact this
  -- Step 4: Dominate (ω δx)² * bw ω by (ω δx)² * exp(B)
  apply (h_sq_int.mul_const (Real.exp B)).mono
  · -- AEStronglyMeasurable
    exact ((configuration_eval_measurable δx).pow_const 2).aestronglyMeasurable.mul
      ((interactionFunctional_measurable d N P a mass).neg.exp.aestronglyMeasurable)
  · -- Pointwise norm bound
    exact Filter.Eventually.of_forall fun ω => by
      simp only [Real.norm_eq_abs]
      have h1 : 0 ≤ (ω δx) ^ 2 := sq_nonneg _
      have h2 : 0 < bw ω := boltzmannWeight_pos d N P a mass ω
      have h3 : bw ω ≤ Real.exp B := by
        show Real.exp _ ≤ Real.exp B
        exact Real.exp_le_exp_of_le (by linarith [hB ω])
      rw [abs_of_nonneg (mul_nonneg h1 (le_of_lt h2)),
          abs_of_nonneg (mul_nonneg h1 (le_of_lt (Real.exp_pos B)))]
      exact mul_le_mul_of_nonneg_left h3 h1

/-- All moments of field evaluations are finite under the interacting measure.

  `∫ |ω(δ_x)|^p dμ_a(ω) < ∞`  for all p ∈ ℕ

This is stronger than just p=2 and follows from the same argument:
the Gaussian has all moments finite (`pairing_memLp T f p` for all p),
and the interaction weight is bounded above. -/
axiom field_all_moments_finite (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (x : FinLatticeSites d N) (p : ℕ) :
    Integrable (fun ω : Configuration (FinLatticeField d N) =>
      (ω (finLatticeDelta d N x)) ^ p)
      (interactingLatticeMeasure d N P a mass ha hmass)

/-! ## FKG inequality

The interacting measure satisfies the FKG inequality for monotone observables.
This follows from `fkg_perturbed` in gaussian-field, since the interaction
V_a is a sum of single-site functions (each :P(φ(x)): depends only on φ(x)). -/

/-- **FKG inequality for the interacting lattice measure.**

For monotone (increasing) functions F, G on field configurations:
  `E_{μ_a}[F · G] ≥ E_{μ_a}[F] · E_{μ_a}[G]`

That is, increasing functions are positively correlated under the
interacting measure, just as under the Gaussian.

This follows from `fkg_perturbed` (gaussian-field/Lattice/FKG.lean)
applied to our interaction V_a, which is a sum of single-site functions. -/
theorem fkg_interacting (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (F G : Configuration (FinLatticeField d N) → ℝ)
    (hF : IsFieldMonotone d N F) (hG : IsFieldMonotone d N G)
    (hFi : Integrable F (interactingLatticeMeasure d N P a mass ha hmass))
    (hGi : Integrable G (interactingLatticeMeasure d N P a mass ha hmass))
    (hFGi : Integrable (F * G) (interactingLatticeMeasure d N P a mass ha hmass)) :
    let μ := interactingLatticeMeasure d N P a mass ha hmass
    (∫ ω, F ω * G ω ∂μ) ≥ (∫ ω, F ω ∂μ) * (∫ ω, G ω ∂μ) := by
  -- The proof should connect to fkg_perturbed from gaussian-field.
  -- The interacting measure is (1/Z) exp(-V) dμ_{GFF}, and V is a sum of
  -- single-site functions (latticeInteraction_single_site), so fkg_perturbed applies.
  sorry

/-! ## Exponential integrability

The generating functional `Z_a[J] = ∫ exp(i⟨ω,J⟩) dμ_a` is well-defined
and bounded. -/

/-- The generating functional of the interacting measure is bounded by 1.

  `|Z_a[f]| = |∫ exp(i·ω(f)) dμ_a(ω)| ≤ 1`

This follows trivially from `|exp(i·t)| = 1` and μ_a being a probability measure. -/
theorem generating_functional_bounded (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) :
    |∫ ω : Configuration (FinLatticeField d N),
      Real.cos (ω f) ∂(interactingLatticeMeasure d N P a mass ha hmass)| ≤ 1 := by
  haveI := interactingLatticeMeasure_isProbability d N P a mass ha hmass
  set μ := interactingLatticeMeasure d N P a mass ha hmass
  -- |∫ cos dμ| ≤ ∫ |cos| dμ ≤ ∫ 1 dμ = 1
  calc |∫ ω, Real.cos (ω f) ∂μ|
      = ‖∫ ω, Real.cos (ω f) ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ ω, ‖Real.cos (ω f)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _ω, (1 : ℝ) ∂μ := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
        · exact integrable_const 1
        · exact Filter.Eventually.of_forall (fun ω => by
            show ‖Real.cos (ω f)‖ ≤ 1
            rw [Real.norm_eq_abs]
            exact abs_le.mpr ⟨by linarith [Real.neg_one_le_cos (ω f)], Real.cos_le_one _⟩)
    _ = 1 := by rw [integral_const, smul_eq_mul, mul_one, probReal_univ]

end Pphi2

end
