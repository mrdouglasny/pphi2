/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.U4AffineBound

/-!
# Coupling-`g` interacting lattice measure (Route A foundation)

The weak-coupling family `μ_g ∝ e^{−g·V} μ_GFF` at the lattice level, and the bridge
`connectedFourPoint μ_g f = u4(…,g)`. For `g = 1` this is `interactingLatticeMeasure`; the point of
the family is *small* `g`, where `lattice_u4_neg_uniform` gives `u₄(μ_g) ≤ −c < 0`. This is the
foundation of Route A (discharge φ⁴₂ non-Gaussianity at weak coupling) — see
`planning/route-A-weak-coupling-plan.md`.

## Main results
* `interactingLatticeMeasureCoupling` — `μ_g = Z(g)⁻¹ · (e^{−g·V} · μ_GFF)`.
* `interactingLatticeMeasureCoupling_isProbability` — `μ_g` is a probability measure (`g ≥ 0`).
* `integral_pow_interactingLatticeMeasureCoupling` — `∫ (ωf)ⁿ dμ_g = normalizedMoment(…,n,g)`.
* `connectedFourPoint_interactingLatticeMeasureCoupling_eq_u4` — `connectedFourPoint μ_g f = u4(g)`.
-/

namespace Pphi2

open MeasureTheory GaussianField

variable (d N : ℕ) [NeZero N]

/-- The coupling-`g` interacting lattice measure `μ_g = Z(g)⁻¹ · (e^{−g·V} · μ_GFF)`, with
`Z(g) = partitionFn(g) = ∫ e^{−g·V}`. For `g = 1` it agrees with `interactingLatticeMeasure`. -/
noncomputable def interactingLatticeMeasureCoupling (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (g : ℝ) :
    @Measure (Configuration (FinLatticeField d N)) instMeasurableSpaceConfiguration :=
  (ENNReal.ofReal (partitionFn d N a mass ha hmass P g))⁻¹ •
    (latticeGaussianMeasure d N a mass ha hmass).withDensity
      (fun ω => ENNReal.ofReal (Real.exp (-(g * interactionFunctional d N P a mass ω))))

/-- The coupling weight `e^{−g·V}` is integrable against the lattice GFF (for `g ≥ 0`):
`V ≥ -B` gives `e^{−g·V} ≤ e^{g·B}`. -/
theorem expNegCoupling_integrable (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) {g : ℝ} (hg : 0 ≤ g) :
    Integrable (fun ω => Real.exp (-(g * interactionFunctional d N P a mass ω)))
      (latticeGaussianMeasure d N a mass ha hmass) := by
  obtain ⟨B, hB_bound⟩ := interactionFunctional_bounded_below d N P a mass ha hmass
  haveI := latticeGaussianMeasure_isProbability d N a mass ha hmass
  apply Integrable.of_bound (C := Real.exp (g * B))
  · exact ((interactionFunctional_measurable d N P a mass).const_mul g).neg.exp.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp_of_le (by nlinarith [hB_bound ω, hg])

/-- `partitionFn(g) > 0` for `g ≥ 0` (it is `≥ 1` by `partitionFn_ge_one`). -/
theorem partitionFn_pos_of_nonneg (P : InteractionPolynomial) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) {g : ℝ} (hg : 0 ≤ g) :
    0 < partitionFn d N a mass ha hmass P g :=
  lt_of_lt_of_le one_pos (partitionFn_ge_one d N P a mass ha hmass hg)

/-- The coupling-`g` interacting lattice measure is a probability measure (`g ≥ 0`). -/
theorem interactingLatticeMeasureCoupling_isProbability (P : InteractionPolynomial)
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) {g : ℝ} (hg : 0 ≤ g) :
    IsProbabilityMeasure (interactingLatticeMeasureCoupling d N P a mass ha hmass g) := by
  constructor
  have hZ := partitionFn_pos_of_nonneg d N P a mass ha hmass hg
  have hZ_ne : ENNReal.ofReal (partitionFn d N a mass ha hmass P g) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hZ).ne'
  have hZ_ne_top : ENNReal.ofReal (partitionFn d N a mass ha hmass P g) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  unfold interactingLatticeMeasureCoupling
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (expNegCoupling_integrable d N P a mass ha hmass hg)
      (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le))]
  simp only [smul_eq_mul]
  exact ENNReal.inv_mul_cancel hZ_ne hZ_ne_top

/-- `∫ (ωf)ⁿ dμ_g = normalizedMoment(…,n,g) = M_n(g)/Z(g)` (`g ≥ 0`). -/
theorem integral_pow_interactingLatticeMeasureCoupling (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField d N) (n : ℕ) {g : ℝ} (hg : 0 ≤ g) :
    (∫ ω, (ω f) ^ n ∂(interactingLatticeMeasureCoupling d N P a mass ha hmass g))
      = normalizedMoment d N a mass ha hmass P f n g := by
  have hZ := partitionFn_pos_of_nonneg d N P a mass ha hmass hg
  have hw_meas : Measurable (fun ω =>
      Real.toNNReal (Real.exp (-(g * interactionFunctional d N P a mass ω)))) :=
    ((interactionFunctional_measurable d N P a mass).const_mul g).neg.exp.real_toNNReal
  have wd : ∫ ω, (ω f) ^ n ∂((latticeGaussianMeasure d N a mass ha hmass).withDensity
        (fun ω => ENNReal.ofReal (Real.exp (-(g * interactionFunctional d N P a mass ω)))))
      = ∫ ω, Real.exp (-(g * interactionFunctional d N P a mass ω)) * (ω f) ^ n
        ∂(latticeGaussianMeasure d N a mass ha hmass) := by
    change ∫ ω, (ω f) ^ n ∂((latticeGaussianMeasure d N a mass ha hmass).withDensity
      (fun ω => ↑(Real.toNNReal (Real.exp (-(g * interactionFunctional d N P a mass ω)))))) = _
    rw [integral_withDensity_eq_integral_smul hw_meas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [NNReal.smul_def, smul_eq_mul]
    rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
  unfold interactingLatticeMeasureCoupling normalizedMoment gibbsMoment
  rw [integral_smul_measure, wd,
    show ((ENNReal.ofReal (partitionFn d N a mass ha hmass P g))⁻¹).toReal
        = (partitionFn d N a mass ha hmass P g)⁻¹ from by
      rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le], smul_eq_mul, div_eq_inv_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  ring

/-! ### A3 — `g`-family analytic inputs (Nelson + density transfer), reusing the general lemmas -/

/-- **`g`-family Nelson bound (`0 ≤ g ≤ 1`).** From `∫ (e^{−V})² ≤ K` one gets `∫ (e^{−gV})² ≤ K`
for `g ∈ [0,1]`: `(e^{−gV})² = e^{−(2g)V}`, then `expMoment_le_rpow` gives
`∫ e^{−(2g)V} ≤ (∫ e^{−2V})^{g} ≤ ∫ e^{−2V} ≤ K` (base `≥ 1` by `partitionFn_ge_one`, exponent
`≤ 1`). So the proven `g=1` uniform Nelson bound transfers to the whole weak-coupling family. -/
theorem expMoment_two_coupling_le (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) {g K : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hK : ∫ ω, (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
            ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K) :
    ∫ ω, (Real.exp (-(g * interactionFunctional d N P a mass ω))) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K := by
  have h1 : ∀ ω, (Real.exp (-(g * interactionFunctional d N P a mass ω))) ^ 2
      = Real.exp (-(2 * g * interactionFunctional d N P a mass ω)) := by
    intro ω; rw [sq, ← Real.exp_add]; congr 1; ring
  have h2 : ∀ ω, (Real.exp (-interactionFunctional d N P a mass ω)) ^ 2
      = Real.exp (-(2 * interactionFunctional d N P a mass ω)) := by
    intro ω; rw [sq, ← Real.exp_add]; congr 1; ring
  simp_rw [h1]
  have hrpow := expMoment_le_rpow d N P a mass ha hmass (s := 2 * g) (by linarith) (by linarith)
  have hbase_ge : (1 : ℝ) ≤ ∫ ω, Real.exp (-(2 * interactionFunctional d N P a mass ω))
      ∂(latticeGaussianMeasure d N a mass ha hmass) :=
    partitionFn_ge_one d N P a mass ha hmass (by norm_num : (0 : ℝ) ≤ 2)
  have hbase_pow : (∫ ω, Real.exp (-(2 * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass)) ^ (2 * g / 2)
      ≤ ∫ ω, Real.exp (-(2 * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass) := by
    calc (∫ ω, Real.exp (-(2 * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass)) ^ (2 * g / 2)
        ≤ (∫ ω, Real.exp (-(2 * interactionFunctional d N P a mass ω))
            ∂(latticeGaussianMeasure d N a mass ha hmass)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase_ge (by linarith)
      _ = _ := Real.rpow_one _
  have hK' : ∫ ω, Real.exp (-(2 * interactionFunctional d N P a mass ω))
      ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K := by simp_rw [← h2]; exact hK
  calc ∫ ω, Real.exp (-(2 * g * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass)
      ≤ _ := hrpow
    _ ≤ _ := hbase_pow
    _ ≤ K := hK'

/-- **`g`-family density-transfer bound (Cauchy–Schwarz, `0 ≤ g`).** For `F ≥ 0` with `F² ∈ L¹(μ_GFF)`,
`∫ F dμ_g ≤ K^{1/2}·(∫ F² dμ_GFF)^{1/2}` whenever `∫ (e^{−gV})² ≤ K`. Generalizes `density_transfer_bound`
(`g=1`) to the coupling family. -/
theorem density_transfer_bound_coupling (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) {g : ℝ} (hg : 0 ≤ g) (K : ℝ)
    (hK : ∫ ω, (Real.exp (-(g * interactionFunctional d N P a mass ω))) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K)
    (F : Configuration (FinLatticeField d N) → ℝ) (hF_nn : ∀ ω, 0 ≤ F ω)
    (hF_meas : AEStronglyMeasurable F (latticeGaussianMeasure d N a mass ha hmass))
    (hF_sq_int : Integrable (fun ω => F ω ^ 2) (latticeGaussianMeasure d N a mass ha hmass)) :
    ∫ ω, F ω ∂(interactingLatticeMeasureCoupling d N P a mass ha hmass g) ≤
    K ^ (1 / 2 : ℝ) *
    (∫ ω, F ω ^ (2 : ℝ) ∂(latticeGaussianMeasure d N a mass ha hmass)) ^ (1 / 2 : ℝ) := by
  set μ_GFF := latticeGaussianMeasure d N a mass ha hmass with hμ
  set V := interactionFunctional d N P a mass with hVdef
  set Z := partitionFn d N a mass ha hmass P g with hZdef
  have hZ_pos : 0 < Z := partitionFn_pos_of_nonneg d N P a mass ha hmass hg
  have hZ_ge : (1 : ℝ) ≤ Z := partitionFn_ge_one d N P a mass ha hmass hg
  have hbw_meas : Measurable (fun ω => Real.exp (-(g * V ω))) :=
    ((interactionFunctional_measurable d N P a mass).const_mul g).neg.exp
  have hbw_nn_meas : Measurable (fun ω => Real.toNNReal (Real.exp (-(g * V ω)))) :=
    Measurable.real_toNNReal hbw_meas
  unfold interactingLatticeMeasureCoupling
  rw [integral_smul_measure]
  have wd_eq : ∫ ω, F ω ∂(μ_GFF.withDensity (fun ω => ENNReal.ofReal (Real.exp (-(g * V ω)))))
      = ∫ ω, Real.exp (-(g * V ω)) * F ω ∂μ_GFF := by
    change ∫ ω, F ω ∂(μ_GFF.withDensity
      (fun ω => ↑(Real.toNNReal (Real.exp (-(g * V ω)))))) = _
    rw [integral_withDensity_eq_integral_smul hbw_nn_meas]
    congr 1; ext ω
    simp only [NNReal.smul_def, smul_eq_mul]
    rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
  rw [wd_eq]
  have hc_real : ((ENNReal.ofReal Z)⁻¹).toReal = Z⁻¹ := by
    simp [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ_pos.le]
  rw [hc_real]
  obtain ⟨B, hB⟩ := interactionFunctional_bounded_below d N P a mass ha hmass
  have hbw_bound : ∀ ω, Real.exp (-(g * V ω)) ≤ Real.exp (g * B) := fun ω =>
    Real.exp_le_exp_of_le (by nlinarith [hB ω, hg])
  haveI : IsProbabilityMeasure μ_GFF := latticeGaussianMeasure_isProbability d N a mass ha hmass
  have hbw_sq_int : Integrable (fun ω => Real.exp (-(g * V ω)) ^ 2) μ_GFF :=
    Integrable.of_bound (hbw_meas.pow_const 2).aestronglyMeasurable (Real.exp (g * B) ^ 2)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact sq_le_sq' (by linarith [Real.exp_pos (-(g * V ω)), Real.exp_pos (g * B)])
          (hbw_bound ω))
  have hbw_memLp : MemLp (fun ω => Real.exp (-(g * V ω))) 2 μ_GFF :=
    (memLp_two_iff_integrable_sq hbw_meas.aestronglyMeasurable).mpr hbw_sq_int
  have hF_memLp : MemLp F 2 μ_GFF := (memLp_two_iff_integrable_sq hF_meas).mpr hF_sq_int
  have h_cs : ∫ ω, Real.exp (-(g * V ω)) * F ω ∂μ_GFF ≤
      (∫ ω, Real.exp (-(g * V ω)) ^ (2:ℝ) ∂μ_GFF) ^ (1/2 : ℝ) *
        (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2 : ℝ) := by
    have h_ofReal : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_num
    have hbw' : MemLp (fun ω => Real.exp (-(g * V ω))) (ENNReal.ofReal 2) μ_GFF :=
      h_ofReal ▸ hbw_memLp
    have hF' : MemLp F (ENNReal.ofReal 2) μ_GFF := h_ofReal ▸ hF_memLp
    exact integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ (fun ω => (Real.exp_pos _).le)) (ae_of_all _ hF_nn) hbw' hF'
  have hZinv_le : Z⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hZ_ge
  have hbw_sq_le : (∫ ω, Real.exp (-(g * V ω)) ^ (2:ℝ) ∂μ_GFF) ^ (1/2 : ℝ) ≤ K ^ (1/2 : ℝ) := by
    apply Real.rpow_le_rpow (integral_nonneg (fun ω => Real.rpow_nonneg (Real.exp_pos _).le _))
    · have hconv : ∫ ω, Real.exp (-(g * V ω)) ^ (2:ℝ) ∂μ_GFF
          = ∫ ω, Real.exp (-(g * V ω)) ^ 2 ∂μ_GFF := by
        congr 1; ext ω; exact Real.rpow_natCast _ 2
      rw [hconv]; exact hK
    · linarith
  have hF_int_nn : 0 ≤ (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) :=
    Real.rpow_nonneg (integral_nonneg (fun ω => Real.rpow_nonneg (hF_nn ω) _)) _
  have hbw_int_nn : 0 ≤ (∫ ω, Real.exp (-(g * V ω)) ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) :=
    Real.rpow_nonneg (integral_nonneg (fun ω => Real.rpow_nonneg (Real.exp_pos _).le _)) _
  calc Z⁻¹ * ∫ ω, Real.exp (-(g * V ω)) * F ω ∂μ_GFF
      ≤ Z⁻¹ * ((∫ ω, Real.exp (-(g * V ω)) ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) *
          (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ)) :=
        mul_le_mul_of_nonneg_left h_cs (inv_pos.mpr hZ_pos).le
    _ ≤ 1 * (K ^ (1/2:ℝ) * (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ)) := by
        apply mul_le_mul hZinv_le _ (mul_nonneg hbw_int_nn hF_int_nn) (by linarith)
        exact mul_le_mul_of_nonneg_right hbw_sq_le hF_int_nn
    _ = K ^ (1/2:ℝ) * (∫ ω, F ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) := one_mul _

/-- **Route-A bridge.** The connected four-point of the coupling-`g` interacting lattice measure is
`u₄` at coupling `g`: `connectedFourPoint μ_g f = u4(…,g)` (`g ≥ 0`). Generalizes
`connectedFourPoint_interactingLatticeMeasure_eq_u4_one` from `g = 1` to arbitrary `g ≥ 0`, so that
`lattice_u4_neg_uniform` (`u₄(g₀) ≤ −c` for small `g₀`) becomes a strict-negativity statement about
an actual measure. -/
theorem connectedFourPoint_interactingLatticeMeasureCoupling_eq_u4 (a mass : ℝ) (ha : 0 < a)
    (hmass : 0 < mass) (P : InteractionPolynomial) (f : FinLatticeField d N) {g : ℝ} (hg : 0 ≤ g) :
    connectedFourPoint (interactingLatticeMeasureCoupling d N P a mass ha hmass g) f
      = u4 d N a mass ha hmass P f g := by
  unfold connectedFourPoint u4
  rw [integral_pow_interactingLatticeMeasureCoupling d N a mass ha hmass P f 4 hg,
    integral_pow_interactingLatticeMeasureCoupling d N a mass ha hmass P f 2 hg]

end Pphi2
