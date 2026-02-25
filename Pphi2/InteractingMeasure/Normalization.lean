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
the Gaussian has all moments finite (from `pairing_is_gaussian` +
`integrable_pow_of_mem_interior_integrableExpSet`),
and the interaction weight is bounded above. -/
theorem field_all_moments_finite (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (x : FinLatticeSites d N) (p : ℕ) :
    Integrable (fun ω : Configuration (FinLatticeField d N) =>
      (ω (finLatticeDelta d N x)) ^ p)
      (interactingLatticeMeasure d N P a mass ha hmass) := by
  -- Setup
  obtain ⟨B, hB⟩ := interactionFunctional_bounded_below d N P a mass ha hmass
  have hZ := partitionFunction_pos d N P a mass ha hmass
  set μ_GFF := latticeGaussianMeasure d N a mass ha hmass with hμ_def
  set δx := finLatticeDelta d N x
  set bw := boltzmannWeight d N P a mass
  -- Step 1: Reduce to withDensity measure (remove Z⁻¹ scaling)
  suffices h : Integrable (fun ω : Configuration (FinLatticeField d N) =>
      (ω δx) ^ p)
      (μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) by
    unfold interactingLatticeMeasure
    exact h.smul_measure (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ).ne'))
  -- Step 2: Reduce withDensity to multiplicative weight under Gaussian
  have hf_meas : Measurable (fun ω : Configuration (FinLatticeField d N) =>
      ENNReal.ofReal (bw ω)) :=
    ENNReal.measurable_ofReal.comp ((interactionFunctional_measurable d N P a mass).neg.exp)
  apply (integrable_withDensity_iff hf_meas
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  have hbw_simp : ∀ ω : Configuration (FinLatticeField d N),
      (ENNReal.ofReal (bw ω)).toReal = bw ω :=
    fun ω => ENNReal.toReal_ofReal (le_of_lt (boltzmannWeight_pos d N P a mass ω))
  simp_rw [hbw_simp]
  -- Goal: Integrable (fun ω => (ω δx)^p * bw ω) μ_GFF
  -- Step 3: Get Gaussian integrability of (ω δx)^p
  -- Pushforward by ω ↦ ω δx is a Gaussian; all moments of Gaussians are finite
  have h_pow_int : Integrable (fun ω : Configuration (FinLatticeField d N) =>
      (ω δx) ^ p) μ_GFF := by
    set T := latticeCovariance d N a mass ha hmass
    -- x^p is integrable under gaussianReal (Gaussian has all polynomial moments)
    have h_gauss := pairing_is_gaussian T δx
    have h_int_gauss : Integrable (fun x : ℝ => x ^ p)
        (ProbabilityTheory.gaussianReal 0 (@inner ℝ _ _ (T δx) (T δx) : ℝ).toNNReal) :=
      ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet (by simp) p
    -- Pull back via the pushforward identity
    rw [← h_gauss] at h_int_gauss
    rwa [integrable_map_measure h_int_gauss.aestronglyMeasurable
      (configuration_eval_measurable δx).aemeasurable] at h_int_gauss
  -- Step 4: Dominate (ω δx)^p * bw ω by |(ω δx)^p| * exp(B)
  apply (h_pow_int.mul_const (Real.exp B)).mono
  · -- AEStronglyMeasurable
    exact ((configuration_eval_measurable δx).pow_const p).aestronglyMeasurable.mul
      ((interactionFunctional_measurable d N P a mass).neg.exp.aestronglyMeasurable)
  · -- Pointwise norm bound
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
      apply mul_le_mul_of_nonneg_left
      · rw [abs_of_pos (boltzmannWeight_pos d N P a mass ω),
            abs_of_pos (Real.exp_pos B)]
        exact Real.exp_le_exp_of_le (by linarith [hB ω])
      · exact abs_nonneg _

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
    (hFm : Measurable F) (hGm : Measurable G)
    (hFi : Integrable F (interactingLatticeMeasure d N P a mass ha hmass))
    (hGi : Integrable G (interactingLatticeMeasure d N P a mass ha hmass))
    (hFGi : Integrable (F * G) (interactingLatticeMeasure d N P a mass ha hmass)) :
    let μ := interactingLatticeMeasure d N P a mass ha hmass
    (∫ ω, F ω * G ω ∂μ) ≥ (∫ ω, F ω ∂μ) * (∫ ω, G ω ∂μ) := by
  -- Reduce let binding to explicit measure
  show (∫ ω, F ω * G ω ∂interactingLatticeMeasure d N P a mass ha hmass) ≥
    (∫ ω, F ω ∂interactingLatticeMeasure d N P a mass ha hmass) *
    (∫ ω, G ω ∂interactingLatticeMeasure d N P a mass ha hmass)
  -- Setup
  set μ_GFF := latticeGaussianMeasure d N a mass ha hmass
  set V := interactionFunctional d N P a mass
  set bw := boltzmannWeight d N P a mass
  set Z := partitionFunction d N P a mass ha hmass
  have hZ_pos : (0 : ℝ) < Z := partitionFunction_pos d N P a mass ha hmass
  -- ENNReal facts about Z
  have hZ_ennreal_ne_zero : ENNReal.ofReal Z ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hZ_pos).ne'
  have hZ_ennreal_ne_top : ENNReal.ofReal Z ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc_ne_zero : (ENNReal.ofReal Z)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr hZ_ennreal_ne_top
  have hc_ne_top : (ENNReal.ofReal Z)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr hZ_ennreal_ne_zero
  -- Measurability of the density
  have hbw_meas_ennreal : Measurable (fun ω : Configuration (FinLatticeField d N) =>
      ENNReal.ofReal (bw ω)) :=
    ENNReal.measurable_ofReal.comp
      ((interactionFunctional_measurable d N P a mass).neg.exp)
  have hbw_lt_top : ∀ ω : Configuration (FinLatticeField d N),
      ENNReal.ofReal (bw ω) < ⊤ := fun _ => ENNReal.ofReal_lt_top
  -- Step 1: V is single-site (absorb a^d into per-site functions)
  have hV_ss : ∃ v : FinLatticeSites d N → (ℝ → ℝ),
      ∀ ω : Configuration (FinLatticeField d N),
        V ω = ∑ x, v x (ω (finLatticeDelta d N x)) := by
    obtain ⟨v, hv⟩ := interactionFunctional_single_site d N P a mass
    exact ⟨fun x t => a ^ (d : ℕ) * v x t, fun ω => by
      simp only [V, hv ω]; rw [Finset.mul_sum]⟩
  -- Step 2: Convert integrability from interacting measure to Gaussian + weight
  -- μ_a = (ENNReal.ofReal Z)⁻¹ • μ_GFF.withDensity(ENNReal.ofReal ∘ bw)
  have int_conv : ∀ (f : Configuration (FinLatticeField d N) → ℝ),
      Integrable f (interactingLatticeMeasure d N P a mass ha hmass) →
      Integrable (fun ω => f ω * bw ω) μ_GFF := by
    intro f hf
    -- Remove Z⁻¹ scaling
    unfold interactingLatticeMeasure at hf
    rw [integrable_smul_measure hc_ne_zero hc_ne_top] at hf
    -- Remove withDensity
    rw [integrable_withDensity_iff hbw_meas_ennreal
      (Filter.Eventually.of_forall hbw_lt_top)] at hf
    have hbw_simp : ∀ ω : Configuration (FinLatticeField d N),
        (ENNReal.ofReal (bw ω)).toReal = bw ω :=
      fun ω => ENNReal.toReal_ofReal (le_of_lt (boltzmannWeight_pos d N P a mass ω))
    simp_rw [hbw_simp] at hf
    exact hf
  -- Convert each integrability hypothesis
  have hFi' : Integrable (fun ω => F ω * Real.exp (-V ω)) μ_GFF := int_conv F hFi
  have hGi' : Integrable (fun ω => G ω * Real.exp (-V ω)) μ_GFF := int_conv G hGi
  have hFGi' : Integrable (fun ω => F ω * G ω * Real.exp (-V ω)) μ_GFF :=
    int_conv (F * G) hFGi
  -- Step 3: Apply fkg_perturbed (un-normalized FKG inequality)
  have hfkg := fkg_perturbed d N a mass ha hmass V hV_ss
    (boltzmannWeight_integrable d N P a mass ha hmass)
    F G hF hG hFm hGm hFi' hGi' hFGi'
  -- hfkg: (∫ FG*exp(-V) dμ_GFF) * (∫ exp(-V) dμ_GFF) ≥
  --        (∫ F*exp(-V) dμ_GFF) * (∫ G*exp(-V) dμ_GFF)
  -- Step 4: Convert back to interacting measure integrals
  -- ∫ f dμ_a = Z⁻¹ * ∫ (f · bw) dμ_GFF, so ∫ (f · bw) dμ_GFF = Z * ∫ f dμ_a
  -- The un-normalized inequality implies the normalized one by dividing by Z²
  -- Use integral_smul_measure: ∫ f d(c • μ) = c.toReal • ∫ f dμ
  unfold interactingLatticeMeasure
  simp_rw [integral_smul_measure]
  -- Goal now involves c.toReal • ∫ ... d(μ_GFF.withDensity ...)
  -- where c = (ENNReal.ofReal Z)⁻¹
  set c := (ENNReal.ofReal Z)⁻¹
  -- c.toReal = Z⁻¹
  have hc_real : c.toReal = Z⁻¹ := by
    simp [c, ENNReal.toReal_inv, ENNReal.toReal_ofReal (le_of_lt hZ_pos)]
  rw [hc_real]
  -- Now use withDensity integral identity
  -- ∫ f d(μ_GFF.withDensity(bw̃)) = ∫ (f * bw) dμ_GFF
  -- via integral_withDensity_eq_integral_smul with NNReal density
  set bw_nn := fun ω : Configuration (FinLatticeField d N) => Real.toNNReal (bw ω)
  -- The withDensity measure with ENNReal.ofReal ∘ bw = withDensity with ↑bw_nn
  -- (since ENNReal.ofReal = ↑ ∘ Real.toNNReal by definition)
  have hbw_nn_meas : Measurable bw_nn := by
    exact Measurable.real_toNNReal
      ((interactionFunctional_measurable d N P a mass).neg.exp)
  -- Rewrite the integrals using withDensity identity
  have wd_eq : ∀ (f : Configuration (FinLatticeField d N) → ℝ),
      ∫ ω, f ω ∂(μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) =
      ∫ ω, bw ω * f ω ∂μ_GFF := by
    intro f
    -- ENNReal.ofReal = ↑ ∘ Real.toNNReal (definitional)
    change ∫ ω, f ω ∂(μ_GFF.withDensity (fun ω => ↑(bw_nn ω))) =
      ∫ ω, bw ω * f ω ∂μ_GFF
    rw [integral_withDensity_eq_integral_smul hbw_nn_meas]
    congr 1; ext ω
    simp only [bw_nn, NNReal.smul_def, smul_eq_mul]
    rw [Real.coe_toNNReal _ (le_of_lt (boltzmannWeight_pos d N P a mass ω))]
  -- Rewrite integrals using wd_eq: ∫ f dν = ∫ bw * f dμ_GFF
  rw [wd_eq (fun ω => F ω * G ω), wd_eq F, wd_eq G]
  -- Rewrite hfkg integrands to match goal form
  -- hfkg has: ∫ F*G*exp(-V), ∫ F*exp(-V), ∫ G*exp(-V), ∫ exp(-V)
  -- Goal has:  ∫ bw*(F*G),    ∫ bw*F,      ∫ bw*G
  -- These match since bw = exp(-V) and up to commuting multiplication
  have hA : ∫ ω, F ω * G ω * Real.exp (-V ω) ∂μ_GFF =
      ∫ ω, bw ω * (F ω * G ω) ∂μ_GFF :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only [bw, boltzmannWeight]; ring)
  have hB : ∫ ω, F ω * Real.exp (-V ω) ∂μ_GFF =
      ∫ ω, bw ω * F ω ∂μ_GFF :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only [bw, boltzmannWeight]; ring)
  have hC : ∫ ω, G ω * Real.exp (-V ω) ∂μ_GFF =
      ∫ ω, bw ω * G ω ∂μ_GFF :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only [bw, boltzmannWeight]; ring)
  -- Goal has • (smul); for ℝ this is definitionally *
  show Z⁻¹ * (∫ ω, bw ω * (F ω * G ω) ∂μ_GFF) ≥
    (Z⁻¹ * (∫ ω, bw ω * F ω ∂μ_GFF)) *
    (Z⁻¹ * (∫ ω, bw ω * G ω ∂μ_GFF))
  -- Suffices to show the un-normalized FKG inequality
  suffices h_unnorm : (∫ ω, bw ω * (F ω * G ω) ∂μ_GFF) * Z ≥
      (∫ ω, bw ω * F ω ∂μ_GFF) * (∫ ω, bw ω * G ω ∂μ_GFF) by
    -- Derive normalized from un-normalized by dividing by Z²
    have hZinv_pos : 0 < Z⁻¹ := inv_pos.mpr hZ_pos
    have hZZ : Z⁻¹ * Z = 1 := inv_mul_cancel₀ (ne_of_gt hZ_pos)
    set A := ∫ ω, bw ω * (F ω * G ω) ∂μ_GFF
    set B := ∫ ω, bw ω * F ω ∂μ_GFF
    set C := ∫ ω, bw ω * G ω ∂μ_GFF
    -- h_unnorm: A * Z ≥ B * C; Goal: Z⁻¹ * A ≥ (Z⁻¹ * B) * (Z⁻¹ * C)
    have step1 := mul_le_mul_of_nonneg_left (GE.ge.le h_unnorm)
      (mul_nonneg (le_of_lt hZinv_pos) (le_of_lt hZinv_pos))
    have lhs_simp : Z⁻¹ * Z⁻¹ * (A * Z) = Z⁻¹ * A := by
      have : Z⁻¹ * Z⁻¹ * (A * Z) = Z⁻¹ * A * (Z⁻¹ * Z) := by ring
      rw [this, hZZ, mul_one]
    have rhs_simp : Z⁻¹ * Z⁻¹ * (B * C) = (Z⁻¹ * B) * (Z⁻¹ * C) := by ring
    linarith
  -- Prove the un-normalized FKG from hfkg by matching integrands
  -- hfkg: (∫ FG*exp(-V)) * (∫ exp(-V)) ≥ (∫ F*exp(-V)) * (∫ G*exp(-V))
  -- Convert: bw*f = f*exp(-V) (since bw = exp(-V)), Z = ∫ exp(-V) = ∫ bw
  have eq1 : (∫ ω, bw ω * (F ω * G ω) ∂μ_GFF) =
      (∫ ω, F ω * G ω * Real.exp (-V ω) ∂μ_GFF) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only [bw, boltzmannWeight]; ring)
  have eq2 : Z = ∫ ω, Real.exp (-V ω) ∂μ_GFF := rfl
  have eq3 : (∫ ω, bw ω * F ω ∂μ_GFF) =
      (∫ ω, F ω * Real.exp (-V ω) ∂μ_GFF) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only [bw, boltzmannWeight]; ring)
  have eq4 : (∫ ω, bw ω * G ω ∂μ_GFF) =
      (∫ ω, G ω * Real.exp (-V ω) ∂μ_GFF) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only [bw, boltzmannWeight]; ring)
  rw [eq1, eq2, eq3, eq4]
  exact hfkg

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
