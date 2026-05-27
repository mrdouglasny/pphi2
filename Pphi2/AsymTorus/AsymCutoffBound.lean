/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cutoff-level exponential moment bound (heterogeneous isotropic lattice)

The lattice-level exponential moment bound for the isotropic-lattice interacting measure: for each
torus test function `f` and lattice `(Nt, Ns, a)` at fixed volume `Lt·Ls`,

  `∫ exp(|ω f|) dμ̃_int ≤ K · exp(σ²)`,

where `K` is the *uniform* Nelson constant (`asymNelson_exponential_estimate_iso`) and `σ²` is the
heterogeneous lattice second moment `∫ (ω g)² dμ_{GFF,asym}` with `g = asymLatticeTestFnIso f`.
The bound is assembled from the Cauchy–Schwarz density transfer (`density_transfer_bound_iso`), the
generic Gaussian exp-modulus moment (`GaussianField.gaussian_exp_abs_moment`), and `Z_a ≥ 1`
(`partitionFunctionAsym_ge_one`), pushed through the embedding `asymTorusEmbedLiftIso`.

Heterogeneous analogue of `asymTorusInteractingMeasure_exponentialMomentBound_cutoff`
(`AsymTorus/AsymTorusOS.lean`). Pieces 1+2 (`second_moment_asym_tendsto`) send `σ²` to the
continuum Green function, giving the `N`-independent bound downstream.

## Reference

Glimm–Jaffe, *Quantum Physics*, §V/§19; Simon, *P(φ)₂* (1974), §V.
-/

import Pphi2.AsymTorus.AsymTorusEmbeddingIso
import Pphi2.AsymTorus.AsymNelson
import Pphi2.AsymTorus.AsymWickMean
import Pphi2.GeneralResults.GaussianExpMoment

noncomputable section

open MeasureTheory GaussianField

namespace Pphi2

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-- **Cutoff-level exponential moment bound for the isotropic interacting measure.**

For each torus test function `f` and lattice `(Nt, Ns, a)` with `Nt·a = Lt`, `Ns·a = Ls`,

  `∫ exp(|ω f|) dμ̃_{int} ≤ K · exp(σ²)`,

with `K` the universal Nelson constant and `σ² = ∫ (ω g)² dμ_{GFF,asym}` the heterogeneous lattice
second moment of `g = asymLatticeTestFnIso f`. Heterogeneous analogue of
`asymTorusInteractingMeasure_exponentialMomentBound_cutoff`. -/
theorem asymTorusInteractingMeasureIso_exponentialMomentBound_cutoff_of_nelson
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (K : ℝ) (hK_pos : 0 < K)
    (hK_bound : ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
      (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
      ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (Real.exp (-interactionFunctionalAsym Nt Ns P a mass ω)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) ≤ K)
    (f : AsymTorusTestFunction Lt Ls) (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (ha : 0 < a) (hvolt : (Nt : ℝ) * a = Lt) (hvols : (Ns : ℝ) * a = Ls) :
    Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Real.exp (|ω f|)) (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ∧
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      Real.exp (|ω f|) ∂(asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ≤
    Real.sqrt (2 * K) * Real.exp (∫ ω : Configuration (AsymLatticeField Nt Ns),
      (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ 2
      ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) := by
  -- Setup
  set μ_int := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  set μ_GFF := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  set ι := asymTorusEmbedLiftIso Lt Ls Nt Ns a
  set g := asymLatticeTestFnIso Lt Ls Nt Ns a f
  set T := latticeCovarianceAsymGJ Nt Ns a mass ha hmass
  have hμ_eq : μ_GFF = GaussianField.measure T := rfl
  have hι_meas : AEMeasurable ι μ_int :=
    (asymTorusEmbedLiftIso_measurable Lt Ls Nt Ns a).aemeasurable
  have h_eval : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      (ι ω) f = ω g := fun ω => asymTorusEmbedLiftIso_eval_eq Lt Ls Nt Ns a f ω
  -- Step 1: Push through the torus embedding
  have hmeas_lhs : AEStronglyMeasurable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Real.exp (|ω f|)) (Measure.map ι μ_int) :=
    (Real.measurable_exp.comp (configuration_eval_measurable f).abs).aestronglyMeasurable
  set σ2 := ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω g) ^ 2 ∂μ_GFF
  change Integrable (fun ω => Real.exp (|ω f|)) (Measure.map ι μ_int) ∧
    ∫ ω, Real.exp (|ω f|) ∂(Measure.map ι μ_int) ≤ Real.sqrt (2 * K) * Real.exp σ2
  rw [integrable_map_measure hmeas_lhs hι_meas, integral_map hι_meas hmeas_lhs]
  simp_rw [Function.comp_def, h_eval]
  -- Step 2: Integrability of exp(|ω g|) under μ_int
  obtain ⟨B, hB⟩ := interactionFunctionalAsym_bounded_below Nt Ns P a mass ha hmass
  set bw := boltzmannWeightAsym Nt Ns P a mass
  have hbw_bound : ∀ ω, bw ω ≤ Real.exp B := fun ω =>
    Real.exp_le_exp_of_le (by linarith [hB ω])
  have hbw_pos : ∀ ω, 0 < bw ω := boltzmannWeightAsym_pos Nt Ns P a mass
  have hF_meas_raw : Measurable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      Real.exp (|ω g|)) := Real.measurable_exp.comp (configuration_eval_measurable g).abs
  -- exp(|ω g|) integrable under μ_GFF (generic MGF at t = 1)
  have hF_int_GFF : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      Real.exp (|ω g|)) μ_GFF := by
    rw [hμ_eq]
    have h := (gaussian_exp_abs_moment T g 1).1
    exact h.congr (ae_of_all _ fun ω => by ring_nf)
  have hZ_pos : 0 < partitionFunctionAsym Nt Ns P a mass ha hmass :=
    partitionFunctionAsym_pos Nt Ns P a mass ha hmass
  have hf_dens_meas : Measurable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      ENNReal.ofReal (bw ω)) :=
    ENNReal.measurable_ofReal.comp
      ((interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp)
  have hbw_simp : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      (ENNReal.ofReal (bw ω)).toReal = bw ω :=
    fun ω => ENNReal.toReal_ofReal (le_of_lt (hbw_pos ω))
  have hF_int_wd : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      Real.exp (|ω g|)) (μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) := by
    apply (integrable_withDensity_iff hf_dens_meas
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
    simp_rw [hbw_simp]
    apply (hF_int_GFF.mul_const (Real.exp B)).mono
    · exact hF_meas_raw.aestronglyMeasurable.mul
        (interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hbw_pos ω).le),
            abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos B).le)]
        exact mul_le_mul_of_nonneg_left (hbw_bound ω) (Real.exp_pos _).le
  have hF_int_int : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      Real.exp (|ω g|)) μ_int := by
    change Integrable _ (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)
    unfold interactingLatticeMeasureAsym
    exact hF_int_wd.smul_measure
      (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ_pos).ne'))
  -- Step 3: density transfer
  have hZ_ge_one := partitionFunctionAsym_ge_one Nt Ns P a mass ha hmass
  have hF_nn : ∀ ω : Configuration (AsymLatticeField Nt Ns), 0 ≤ Real.exp (|ω g|) :=
    fun ω => (Real.exp_pos _).le
  have hF_meas : AEStronglyMeasurable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      Real.exp (|ω g|)) μ_GFF := hF_meas_raw.aestronglyMeasurable
  have hF_sq_int : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      Real.exp (|ω g|) ^ 2) μ_GFF := by
    have h_eq : ∀ ω : Configuration (AsymLatticeField Nt Ns),
        Real.exp (|ω g|) ^ 2 = Real.exp (2 * |ω g|) := fun ω => by
      rw [sq, ← Real.exp_add]; ring_nf
    simp_rw [h_eq]
    rw [hμ_eq]
    exact (gaussian_exp_abs_moment T g 2).1
  have h_dt := density_transfer_bound_iso Nt Ns P a mass ha hmass K hK_pos
    (hK_bound Nt Ns a ha hvolt hvols) hZ_ge_one
    (fun ω => Real.exp (|ω g|)) hF_nn hF_meas hF_sq_int
  -- Step 4: bound the Gaussian factor via the MGF at t = 2
  have h_rpow_eq : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      Real.exp (|ω g|) ^ (2:ℝ) = Real.exp (2 * |ω g|) := fun ω => by
    rw [show (2:ℝ) = ↑(2:ℕ) from by norm_num, Real.rpow_natCast, sq, ← Real.exp_add]; ring_nf
  have h_int_rpow_eq : ∫ ω, (fun ω => Real.exp (|ω g|)) ω ^ (2:ℝ) ∂μ_GFF =
      ∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF := by
    congr 1; ext ω; exact h_rpow_eq ω
  have h_gauss : ∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF ≤
      2 * Real.exp ((2:ℝ) ^ 2 / 2 * ∫ ω, (ω g) ^ 2 ∂μ_GFF) := by
    rw [hμ_eq]
    exact (gaussian_exp_abs_moment T g 2).2
  have h_exp_simp : (2:ℝ) ^ 2 / 2 * ∫ ω, (ω g) ^ 2 ∂μ_GFF = 2 * σ2 := by
    have h22 : (2:ℝ) ^ 2 / 2 = 2 := by norm_num
    rw [h22]
  have h_gauss' : ∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF ≤ 2 * Real.exp (2 * σ2) := by
    rw [← h_exp_simp]; exact h_gauss
  -- Step 5: (∫ exp(2|ωg|))^{1/2} ≤ √2 · exp(σ2)
  have h_gauss_nn : (0:ℝ) ≤ ∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF :=
    integral_nonneg fun ω => (Real.exp_pos _).le
  have h_rpow_bound : (∫ ω, (fun ω => Real.exp (|ω g|)) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) ≤
      Real.sqrt 2 * Real.exp σ2 := by
    rw [h_int_rpow_eq]
    calc (∫ ω, Real.exp (2 * |ω g|) ∂μ_GFF) ^ (1/2:ℝ)
        ≤ (2 * Real.exp (2 * σ2)) ^ (1/2:ℝ) :=
          Real.rpow_le_rpow h_gauss_nn h_gauss' (by norm_num : (0:ℝ) ≤ 1/2)
      _ = Real.sqrt (2 * Real.exp (2 * σ2)) := by rw [Real.sqrt_eq_rpow]
      _ = Real.sqrt 2 * Real.sqrt (Real.exp (2 * σ2)) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      _ = Real.sqrt 2 * Real.exp σ2 := by
          congr 1
          rw [show (2 : ℝ) * σ2 = σ2 + σ2 from by ring,
              Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  -- Step 6: combine
  have h_integral_bound : ∫ ω, Real.exp (|ω g|) ∂μ_int ≤
      Real.sqrt (2 * K) * Real.exp σ2 := by
    calc ∫ ω, Real.exp (|ω g|) ∂μ_int
        ≤ K ^ (1/2:ℝ) *
          (∫ ω, (fun ω => Real.exp (|ω g|)) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) := h_dt
      _ ≤ K ^ (1/2:ℝ) * (Real.sqrt 2 * Real.exp σ2) :=
          mul_le_mul_of_nonneg_left h_rpow_bound (Real.rpow_nonneg hK_pos.le _)
      _ = Real.sqrt K * (Real.sqrt 2 * Real.exp σ2) := by rw [← Real.sqrt_eq_rpow]
      _ = (Real.sqrt K * Real.sqrt 2) * Real.exp σ2 := by ring
      _ = Real.sqrt (2 * K) * Real.exp σ2 := by
          congr 1
          rw [mul_comm (Real.sqrt K) (Real.sqrt 2),
              ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact ⟨hF_int_int, h_integral_bound⟩

/-- **Cutoff-level exponential moment bound for the isotropic interacting measure** (with the
volume-uniform Nelson constant supplied by `asymNelson_exponential_estimate_iso`). Thin wrapper
over `…_cutoff_of_nelson`. -/
theorem asymTorusInteractingMeasureIso_exponentialMomentBound_cutoff
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : AsymTorusTestFunction Lt Ls) (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
      (a : ℝ) (ha : 0 < a), (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
    Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
      Real.exp (|ω f|)) (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ∧
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      Real.exp (|ω f|) ∂(asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ≤
    K * Real.exp (∫ ω : Configuration (AsymLatticeField Nt Ns),
      (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ 2
      ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) := by
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    asymNelson_exponential_estimate_iso P mass hmass Lt Ls hLt.out hLs.out
  exact ⟨Real.sqrt (2 * K), Real.sqrt_pos_of_pos (by linarith),
    fun f Nt Ns _ _ a ha hvolt hvols =>
      asymTorusInteractingMeasureIso_exponentialMomentBound_cutoff_of_nelson
        Lt Ls P mass hmass K hK_pos hK_bound f Nt Ns a ha hvolt hvols⟩

end Pphi2

end
