/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.TorusContinuumLimit.TorusInteractingLimit

/-!
# Uniform higher moments of the torus interacting measures (Layer-IV foundation)

Step IV of the `TorusIsInteracting` proof plan (`planning/torus-interacting-proof-plan.md`) needs
4th-moment **convergence** `⟨(ωf)⁴⟩_{μ_N} → ⟨(ωf)⁴⟩_μ` along the Prokhorov subsequence. The
`torusInteractingLimit_exists` limit only supplies weak (bounded-continuous) convergence, so the gap
is closed by **uniform integrability**, which needs a cutoff-uniform bound on a moment strictly above
4. This file proves the uniform **4th** moment (and the route generalizes to any even power); the
uniform 6th/8th moment for the Vitali step is the same proof with a larger hypercontractive exponent.

`torus_interacting_fourth_moment_uniform` mirrors the proved
`torus_interacting_second_moment_uniform` (`TorusInteractingLimit.lean`): Cauchy–Schwarz density
transfer `∫F dμ_int ≤ √K·(∫F² dμ_GFF)^{1/2}` with `F=(ωg)⁴`, Nelson's exponential estimate for `K`,
and Gaussian hypercontractivity `∫(ωg)⁸ dμ_GFF ≤ 7⁴·(∫(ωg)²)⁴` for the free 8th moment.
-/

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-- **Uniform fourth moment bound** for the torus interacting measures. For each test function `f`,
`∫ (ωf)⁴ dμ_{P,N} ≤ C` uniformly in the lattice size `N`. Same template as the second-moment bound:
density transfer (Cauchy–Schwarz) + Nelson's exponential estimate + Gaussian hypercontractivity (the
free 8th moment `∫(ωg)⁸ ≤ 7⁴(∫(ωg)²)⁴`). -/
theorem torus_interacting_fourth_moment_uniform
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (TorusTestFunction L),
      (ω f) ^ 4 ∂(torusInteractingMeasure L N P mass hmass) ≤ C := by
  obtain ⟨K, hK_pos, hK_bound⟩ := nelson_exponential_estimate L P mass hmass
  obtain ⟨Cg, hCg_pos, hCg_bound⟩ := torusEmbeddedTwoPoint_uniform_bound L mass hmass f
  -- C = 49 · √K · Cg² works: (∫(ωg)⁸)^{1/2} ≤ (7⁴ Cg⁴)^{1/2} = 49 Cg².
  refine ⟨49 * Real.sqrt K * Cg ^ 2,
    mul_pos (mul_pos (by norm_num : (0:ℝ) < 49) (Real.sqrt_pos_of_pos hK_pos))
      (pow_pos hCg_pos 2), fun N _ => ?_⟩
  set μ_int := interactingLatticeMeasure 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass
  set μ_GFF := latticeGaussianMeasure 2 N (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass
  set ι := torusEmbedLift L N
  set g := latticeTestFn L N f
  have hι_meas : AEMeasurable ι μ_int :=
    (torusEmbedLift_measurable L N).aemeasurable
  change ∫ ω, (ω f) ^ 4 ∂(Measure.map ι μ_int) ≤ 49 * Real.sqrt K * Cg ^ 2
  rw [integral_map hι_meas
    ((configuration_eval_measurable f).pow_const 4).aestronglyMeasurable]
  have h_eval : ∀ ω : Configuration (FinLatticeField 2 N),
      (ι ω) f = ω g := fun ω => torusEmbedLift_eval_eq L N f ω
  simp_rw [h_eval]
  -- Goal: ∫ (ω g)⁴ dμ_int ≤ 49 * √K * Cg²
  have hZ_ge_one := partitionFunction_ge_one 2 N P mass hmass
    (circleSpacing L N) (circleSpacing_pos L N)
  -- F = (ω g)⁴ : nonneg, measurable, with F² = (ω g)⁸ integrable under μ_GFF.
  have hF_nn : ∀ ω : Configuration (FinLatticeField 2 N), 0 ≤ (ω g) ^ 4 :=
    fun ω => by positivity
  have hF_meas : AEStronglyMeasurable (fun ω : Configuration (FinLatticeField 2 N) =>
      (ω g) ^ 4) μ_GFF :=
    ((configuration_eval_measurable g).pow_const 4).aestronglyMeasurable
  have hF_sq_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      ((ω g) ^ 4) ^ 2) μ_GFF := by
    have h8 : MemLp (fun ω : Configuration (FinLatticeField 2 N) => ω g) 8 μ_GFF := by
      exact_mod_cast pairing_memLp (latticeCovarianceGJ 2 N (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass) g 8
    have hmem := h8.norm_rpow (p := (8 : ENNReal))
      (by norm_num : (8 : ENNReal) ≠ 0) (by norm_num : (8 : ENNReal) ≠ ⊤)
    rw [memLp_one_iff_integrable] at hmem
    have h_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
        ‖ω g‖ ^ (8 : ℕ)) μ_GFF := by
      refine hmem.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp [ENNReal.toReal_ofNat]
    exact h_int.congr (Filter.Eventually.of_forall fun ω => by
      dsimp only
      rw [Real.norm_eq_abs]
      conv_rhs => rw [show ((ω g) ^ 4) ^ 2 = ((ω g) ^ 2) ^ 4 from by ring,
        show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]
      ring)
  have h_dt := density_transfer_bound 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass K hK_pos (hK_bound N)
    hZ_ge_one (fun ω => (ω g) ^ 4) hF_nn hF_meas hF_sq_int
  -- h_dt : ∫ (ω g)⁴ dμ_int ≤ √K · (∫ ((ω g)⁴)^(2:ℝ) dμ_GFF)^{1/2}
  have h_rpow_to_npow : ∫ ω, (fun ω => (ω g) ^ 4) ω ^ (2:ℝ) ∂μ_GFF =
      ∫ ω, ((ω g) ^ 4) ^ 2 ∂μ_GFF := by
    congr 1; ext ω; exact Real.rpow_natCast ((ω g) ^ 4) 2
  -- Free 8th moment via hypercontractivity: ∫ (ω g)⁸ ≤ 7⁴ · (∫ (ω g)²)⁴ ≤ 7⁴ · Cg⁴.
  set T := latticeCovarianceGJ 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass
  have hμ_eq : μ_GFF = GaussianField.measure T := rfl
  have h_second_moment_eq : ∫ ω, (ω g) ^ 2 ∂μ_GFF =
      torusEmbeddedTwoPoint L N mass hmass f f :=
    (torusEmbeddedTwoPoint_eq_lattice_second_moment L N mass hmass f).symm
  have h_second_le : ∫ ω, (ω g) ^ 2 ∂μ_GFF ≤ Cg := by
    rw [h_second_moment_eq]; exact hCg_bound N
  have h_second_nn : 0 ≤ ∫ ω, (ω g) ^ 2 ∂μ_GFF :=
    integral_nonneg fun ω => sq_nonneg _
  have h_eighth_le : ∫ ω, ((ω g) ^ 4) ^ 2 ∂μ_GFF ≤ 7 ^ 4 * Cg ^ 4 := by
    have h_eq8 : ∀ ω : Configuration (FinLatticeField 2 N),
        ((ω g) ^ 4) ^ 2 = |ω g| ^ 8 := by
      intro ω
      rw [show ((ω g) ^ 4) ^ 2 = ((ω g) ^ 2) ^ 4 from by ring,
        show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]
      ring
    simp_rw [h_eq8]
    have h_hyper := gaussian_hypercontractive T g 1 8
      (by norm_num : (2:ℝ) ≤ 8) 4 (by norm_num : 1 ≤ 4)
      (by norm_num : (8:ℝ) = 2 * ↑4)
    have h_lhs_eq : ∫ ω, |ω g| ^ 8 ∂μ_GFF =
        ∫ ω, |ω g| ^ ((8:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T) := by
      rw [hμ_eq]; congr 1; ext ω
      simp only [Nat.cast_one, mul_one]; exact (Real.rpow_natCast _ 8).symm
    rw [h_lhs_eq]
    have h_int_2_eq : ∫ ω, |ω g| ^ (2 * 1) ∂(GaussianField.measure T) =
        ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
      rw [hμ_eq]; congr 1; ext ω; simp [sq_abs]
    have h_hyper' : ∫ ω, |ω g| ^ ((8:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T) ≤
        ((8:ℝ) - 1) ^ ((8:ℝ) * ↑(1:ℕ) / 2) *
        (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((8:ℝ) / 2) := by
      have := h_hyper; rwa [h_int_2_eq] at this
    have h_coeff : ((8:ℝ) - 1) ^ ((8:ℝ) * ↑(1:ℕ) / 2) = 7 ^ 4 := by
      simp only [Nat.cast_one, mul_one]
      rw [show (8:ℝ) / 2 = ↑(4:ℕ) from by norm_num, Real.rpow_natCast]; norm_num
    have h_exp_eq' : (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((8:ℝ) / 2) =
        (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 4 := by
      rw [show (8:ℝ) / 2 = ↑(4:ℕ) from by norm_num, Real.rpow_natCast]
    calc ∫ ω, |ω g| ^ ((8:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T)
        ≤ ((8:ℝ) - 1) ^ ((8:ℝ) * ↑(1:ℕ) / 2) *
          (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((8:ℝ) / 2) := h_hyper'
      _ = 7 ^ 4 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 4 := by rw [h_coeff, h_exp_eq']
      _ ≤ 7 ^ 4 * Cg ^ 4 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ h_second_nn h_second_le 4
  -- Combine: ∫ (ω g)⁴ dμ_int ≤ √K · (∫ (ω g)⁸)^{1/2} ≤ √K · (7⁴ Cg⁴)^{1/2} = √K · 49 Cg².
  have h_eighth_nn : (0:ℝ) ≤ ∫ ω, ((ω g) ^ 4) ^ 2 ∂μ_GFF :=
    integral_nonneg fun ω => by positivity
  have h_8th_bound : (∫ ω, (fun ω => (ω g) ^ 4) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) ≤ 7 ^ 2 * Cg ^ 2 := by
    rw [h_rpow_to_npow]
    calc (∫ ω, ((ω g) ^ 4) ^ 2 ∂μ_GFF) ^ (1/2:ℝ)
        ≤ (7 ^ 4 * Cg ^ 4) ^ (1/2:ℝ) :=
          Real.rpow_le_rpow h_eighth_nn h_eighth_le (by norm_num : (0:ℝ) ≤ 1/2)
      _ = 7 ^ 2 * Cg ^ 2 := by
          rw [show (7:ℝ) ^ 4 * Cg ^ 4 = (7 ^ 2 * Cg ^ 2) ^ 2 from by ring, ← Real.sqrt_eq_rpow,
            Real.sqrt_sq (by positivity)]
  have hK_sqrt : K ^ (1/2:ℝ) = Real.sqrt K := (Real.sqrt_eq_rpow K).symm
  calc ∫ ω, (ω g) ^ 4 ∂μ_int
      ≤ K ^ (1/2:ℝ) * (∫ ω, (fun ω => (ω g) ^ 4) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) := h_dt
    _ ≤ K ^ (1/2:ℝ) * (7 ^ 2 * Cg ^ 2) :=
        mul_le_mul_of_nonneg_left h_8th_bound (Real.rpow_nonneg hK_pos.le _)
    _ = Real.sqrt K * (49 * Cg ^ 2) := by rw [hK_sqrt]; norm_num
    _ = 49 * Real.sqrt K * Cg ^ 2 := by ring

/-- **Uniform eighth moment bound** for the torus interacting measures: `∫ (ωf)⁸ dμ_{P,N} ≤ C`
uniformly in `N`. Same template as the fourth-moment bound (`p = 16` hypercontractive exponent,
`∫(ωg)¹⁶ ≤ 15⁸(∫(ωg)²)⁸`). Since `8 > 4`, this gives **uniform integrability of `(ωf)⁴`** across the
family `{μ_{P,N}}` (Vitali), the input the moment-convergence step (IV.b) needs to pass `⟨(ωf)⁴⟩`
through the weak (bounded-continuous) limit. -/
theorem torus_interacting_eighth_moment_uniform
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (TorusTestFunction L),
      (ω f) ^ 8 ∂(torusInteractingMeasure L N P mass hmass) ≤ C := by
  obtain ⟨K, hK_pos, hK_bound⟩ := nelson_exponential_estimate L P mass hmass
  obtain ⟨Cg, hCg_pos, hCg_bound⟩ := torusEmbeddedTwoPoint_uniform_bound L mass hmass f
  refine ⟨15 ^ 4 * Real.sqrt K * Cg ^ 4,
    mul_pos (mul_pos (by norm_num : (0:ℝ) < 15 ^ 4) (Real.sqrt_pos_of_pos hK_pos))
      (pow_pos hCg_pos 4), fun N _ => ?_⟩
  set μ_int := interactingLatticeMeasure 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass
  set μ_GFF := latticeGaussianMeasure 2 N (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass
  set ι := torusEmbedLift L N
  set g := latticeTestFn L N f
  have hι_meas : AEMeasurable ι μ_int :=
    (torusEmbedLift_measurable L N).aemeasurable
  change ∫ ω, (ω f) ^ 8 ∂(Measure.map ι μ_int) ≤ 15 ^ 4 * Real.sqrt K * Cg ^ 4
  rw [integral_map hι_meas
    ((configuration_eval_measurable f).pow_const 8).aestronglyMeasurable]
  have h_eval : ∀ ω : Configuration (FinLatticeField 2 N),
      (ι ω) f = ω g := fun ω => torusEmbedLift_eval_eq L N f ω
  simp_rw [h_eval]
  have hZ_ge_one := partitionFunction_ge_one 2 N P mass hmass
    (circleSpacing L N) (circleSpacing_pos L N)
  have hF_nn : ∀ ω : Configuration (FinLatticeField 2 N), 0 ≤ (ω g) ^ 8 :=
    fun ω => by positivity
  have hF_meas : AEStronglyMeasurable (fun ω : Configuration (FinLatticeField 2 N) =>
      (ω g) ^ 8) μ_GFF :=
    ((configuration_eval_measurable g).pow_const 8).aestronglyMeasurable
  have hF_sq_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      ((ω g) ^ 8) ^ 2) μ_GFF := by
    have h16 : MemLp (fun ω : Configuration (FinLatticeField 2 N) => ω g) 16 μ_GFF := by
      exact_mod_cast pairing_memLp (latticeCovarianceGJ 2 N (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass) g 16
    have hmem := h16.norm_rpow (p := (16 : ENNReal))
      (by norm_num : (16 : ENNReal) ≠ 0) (by norm_num : (16 : ENNReal) ≠ ⊤)
    rw [memLp_one_iff_integrable] at hmem
    have h_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
        ‖ω g‖ ^ (16 : ℕ)) μ_GFF := by
      refine hmem.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp [ENNReal.toReal_ofNat]
    exact h_int.congr (Filter.Eventually.of_forall fun ω => by
      dsimp only
      rw [Real.norm_eq_abs]
      conv_rhs => rw [show ((ω g) ^ 8) ^ 2 = ((ω g) ^ 2) ^ 8 from by ring,
        show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]
      ring)
  have h_dt := density_transfer_bound 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass K hK_pos (hK_bound N)
    hZ_ge_one (fun ω => (ω g) ^ 8) hF_nn hF_meas hF_sq_int
  have h_rpow_to_npow : ∫ ω, (fun ω => (ω g) ^ 8) ω ^ (2:ℝ) ∂μ_GFF =
      ∫ ω, ((ω g) ^ 8) ^ 2 ∂μ_GFF := by
    congr 1; ext ω; exact Real.rpow_natCast ((ω g) ^ 8) 2
  set T := latticeCovarianceGJ 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass
  have hμ_eq : μ_GFF = GaussianField.measure T := rfl
  have h_second_moment_eq : ∫ ω, (ω g) ^ 2 ∂μ_GFF =
      torusEmbeddedTwoPoint L N mass hmass f f :=
    (torusEmbeddedTwoPoint_eq_lattice_second_moment L N mass hmass f).symm
  have h_second_le : ∫ ω, (ω g) ^ 2 ∂μ_GFF ≤ Cg := by
    rw [h_second_moment_eq]; exact hCg_bound N
  have h_second_nn : 0 ≤ ∫ ω, (ω g) ^ 2 ∂μ_GFF :=
    integral_nonneg fun ω => sq_nonneg _
  have h_sixteenth_le : ∫ ω, ((ω g) ^ 8) ^ 2 ∂μ_GFF ≤ 15 ^ 8 * Cg ^ 8 := by
    have h_eq16 : ∀ ω : Configuration (FinLatticeField 2 N),
        ((ω g) ^ 8) ^ 2 = |ω g| ^ 16 := by
      intro ω
      rw [show ((ω g) ^ 8) ^ 2 = ((ω g) ^ 2) ^ 8 from by ring,
        show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]
      ring
    simp_rw [h_eq16]
    have h_hyper := gaussian_hypercontractive T g 1 16
      (by norm_num : (2:ℝ) ≤ 16) 8 (by norm_num : 1 ≤ 8)
      (by norm_num : (16:ℝ) = 2 * ↑8)
    have h_lhs_eq : ∫ ω, |ω g| ^ 16 ∂μ_GFF =
        ∫ ω, |ω g| ^ ((16:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T) := by
      rw [hμ_eq]; congr 1; ext ω
      simp only [Nat.cast_one, mul_one]; exact (Real.rpow_natCast _ 16).symm
    rw [h_lhs_eq]
    have h_coeff : ((16:ℝ) - 1) ^ ((16:ℝ) * ↑(1:ℕ) / 2) = 15 ^ 8 := by
      simp only [Nat.cast_one, mul_one]
      rw [show (16:ℝ) / 2 = ↑(8:ℕ) from by norm_num, Real.rpow_natCast]; norm_num
    have h_int_2_eq : ∫ ω, |ω g| ^ (2 * 1) ∂(GaussianField.measure T) =
        ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
      rw [hμ_eq]; congr 1; ext ω; simp [sq_abs]
    have h_hyper' : ∫ ω, |ω g| ^ ((16:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T) ≤
        ((16:ℝ) - 1) ^ ((16:ℝ) * ↑(1:ℕ) / 2) *
        (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((16:ℝ) / 2) := by
      have := h_hyper; rwa [h_int_2_eq] at this
    have h_exp_eq' : (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((16:ℝ) / 2) =
        (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 8 := by
      rw [show (16:ℝ) / 2 = ↑(8:ℕ) from by norm_num, Real.rpow_natCast]
    calc ∫ ω, |ω g| ^ ((16:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T)
        ≤ ((16:ℝ) - 1) ^ ((16:ℝ) * ↑(1:ℕ) / 2) *
          (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((16:ℝ) / 2) := h_hyper'
      _ = 15 ^ 8 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 8 := by rw [h_coeff, h_exp_eq']
      _ ≤ 15 ^ 8 * Cg ^ 8 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ h_second_nn h_second_le 8
  have h_16th_bound : (∫ ω, (fun ω => (ω g) ^ 8) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) ≤
      15 ^ 4 * Cg ^ 4 := by
    rw [h_rpow_to_npow]
    have h_nn : (0:ℝ) ≤ ∫ ω, ((ω g) ^ 8) ^ 2 ∂μ_GFF := integral_nonneg fun ω => by positivity
    calc (∫ ω, ((ω g) ^ 8) ^ 2 ∂μ_GFF) ^ (1/2:ℝ)
        ≤ (15 ^ 8 * Cg ^ 8) ^ (1/2:ℝ) :=
          Real.rpow_le_rpow h_nn h_sixteenth_le (by norm_num : (0:ℝ) ≤ 1/2)
      _ = 15 ^ 4 * Cg ^ 4 := by
          rw [show (15:ℝ) ^ 8 * Cg ^ 8 = (15 ^ 4 * Cg ^ 4) ^ 2 from by ring, ← Real.sqrt_eq_rpow,
            Real.sqrt_sq (by positivity)]
  have hK_sqrt : K ^ (1/2:ℝ) = Real.sqrt K := (Real.sqrt_eq_rpow K).symm
  calc ∫ ω, (ω g) ^ 8 ∂μ_int
      ≤ K ^ (1/2:ℝ) * (∫ ω, (fun ω => (ω g) ^ 8) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) := h_dt
    _ ≤ K ^ (1/2:ℝ) * (15 ^ 4 * Cg ^ 4) :=
        mul_le_mul_of_nonneg_left h_16th_bound (Real.rpow_nonneg hK_pos.le _)
    _ = 15 ^ 4 * Real.sqrt K * Cg ^ 4 := by rw [hK_sqrt]; ring

/-- **Power-integrability under the torus interacting measure.** `|ω f|^k` is integrable w.r.t.
`torusInteractingMeasure` for every `k ≥ 1`. Mirrors the proved 2nd-moment integrability: push
through the embedding, decompose `μ_int = Z⁻¹·μ_GFF.withDensity(bw)`, dominate `|ωg|^k·bw` by
`|ωg|^k·e^B` (Boltzmann weight bounded), and use Gaussian `Lᵏ` integrability of the pairing. -/
theorem torus_interacting_abs_pow_integrable (P : InteractionPolynomial) (mass : ℝ)
    (hmass : 0 < mass) (f : TorusTestFunction L) (k : ℕ) (hk : 1 ≤ k) (N : ℕ) [NeZero N] :
    Integrable (fun ω => |ω f| ^ k) (torusInteractingMeasure L N P mass hmass) := by
  unfold torusInteractingMeasure
  rw [integrable_map_measure
    (((configuration_eval_measurable f).abs).pow_const k).aestronglyMeasurable
    (torusEmbedLift_measurable L N).aemeasurable]
  have h_eq : (fun ω => |ω f| ^ k) ∘ (torusEmbedLift L N) =
      fun ω => |ω (latticeTestFn L N f)| ^ k := by
    ext ω; simp [Function.comp, torusEmbedLift_eval_eq L N f ω]
  rw [h_eq]
  set g := latticeTestFn L N f
  set μ_GFF := latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass
  set bw := boltzmannWeight 2 N P (circleSpacing L N) mass
  obtain ⟨B, hB⟩ := interactionFunctional_bounded_below 2 N P
    (circleSpacing L N) mass (circleSpacing_pos L N) hmass
  have hZ := partitionFunction_pos 2 N P (circleSpacing L N) mass (circleSpacing_pos L N) hmass
  suffices h : Integrable (fun ω : Configuration (FinLatticeField 2 N) => |ω g| ^ k)
      (μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) by
    unfold interactingLatticeMeasure
    exact h.smul_measure (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ).ne'))
  have hf_meas : Measurable (fun ω : Configuration (FinLatticeField 2 N) =>
      ENNReal.ofReal (bw ω)) :=
    ENNReal.measurable_ofReal.comp
      ((interactionFunctional_measurable 2 N P (circleSpacing L N) mass).neg.exp)
  apply (integrable_withDensity_iff hf_meas
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  have hbw_simp : ∀ ω : Configuration (FinLatticeField 2 N),
      (ENNReal.ofReal (bw ω)).toReal = bw ω :=
    fun ω => ENNReal.toReal_ofReal (le_of_lt (boltzmannWeight_pos 2 N P (circleSpacing L N) mass ω))
  simp_rw [hbw_simp]
  -- Gaussian integrability of |ω g|^k
  have h_gauss : Integrable (fun ω : Configuration (FinLatticeField 2 N) => |ω g| ^ k) μ_GFF := by
    have hmem : MemLp (fun ω : Configuration (FinLatticeField 2 N) => ω g) (k : ENNReal) μ_GFF := by
      exact_mod_cast pairing_memLp (latticeCovarianceGJ 2 N (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass) g k
    have h := hmem.norm_rpow (p := (k : ENNReal))
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hk) (by simp)
    rw [memLp_one_iff_integrable] at h
    refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs]
  apply (h_gauss.mul_const (Real.exp B)).mono
  · exact (((configuration_eval_measurable g).abs).pow_const k).aestronglyMeasurable.mul
      (Measurable.aestronglyMeasurable
        (interactionFunctional_measurable 2 N P (circleSpacing L N) mass).neg.exp)
  · refine Filter.Eventually.of_forall fun ω => ?_
    simp only [Real.norm_eq_abs]
    have h1 : 0 ≤ |ω g| ^ k := by positivity
    have h2 : 0 < bw ω := boltzmannWeight_pos 2 N P (circleSpacing L N) mass ω
    have h3 : bw ω ≤ Real.exp B := Real.exp_le_exp_of_le (by linarith [hB ω])
    rw [abs_of_nonneg (mul_nonneg h1 h2.le),
        abs_of_nonneg (mul_nonneg h1 (Real.exp_pos B).le)]
    exact mul_le_mul_of_nonneg_left h3 h1

/-- **Limit moment bound + integrability from a uniform bound** (the "bound side"). For `F ≥ 0`
continuous + measurable, integrable under each `ν n` with `∫F ∂(ν n) ≤ C`, and weak (bounded-cont)
convergence `ν n ⇀ μ`, the limit satisfies `Integrable F μ` and `∫F ∂μ ≤ C`. Truncation + weak
convergence (`∫min(F,M)∂μ ≤ C`) + monotone convergence. Mirrors
`torusInteracting_exponentialMomentBound` with a constant bound. -/
theorem limit_le_of_uniform_bound
    {ν : ℕ → Measure (Configuration (TorusTestFunction L))}
    {μ : Measure (Configuration (TorusTestFunction L))} [IsProbabilityMeasure μ]
    {F : Configuration (TorusTestFunction L) → ℝ} {C : ℝ}
    (hF_cont : Continuous F) (hF_meas : Measurable F) (hF_nn : ∀ ω, 0 ≤ F ω)
    (hF_int_ν : ∀ n, Integrable F (ν n)) (hbound : ∀ n, ∫ ω, F ω ∂(ν n) ≤ C)
    (hconv : ∀ (g : Configuration (TorusTestFunction L) → ℝ),
      Continuous g → (∃ B, ∀ x, |g x| ≤ B) →
      Tendsto (fun n => ∫ ω, g ω ∂(ν n)) atTop (nhds (∫ ω, g ω ∂μ))) :
    Integrable F μ ∧ ∫ ω, F ω ∂μ ≤ C := by
  have h_trunc : ∀ M : ℝ, 0 < M → ∫ ω, min (F ω) M ∂μ ≤ C := by
    intro M hM
    have h_cont : Continuous (fun ω => min (F ω) M) := hF_cont.min continuous_const
    have h_bdd : ∃ B, ∀ ω, |min (F ω) M| ≤ B :=
      ⟨M, fun ω => by rw [abs_of_nonneg (le_min (hF_nn ω) hM.le)]; exact min_le_right _ _⟩
    have h_lim := hconv _ h_cont h_bdd
    refine le_of_tendsto' h_lim (fun n => ?_)
    calc ∫ ω, min (F ω) M ∂(ν n) ≤ ∫ ω, F ω ∂(ν n) :=
          integral_mono_of_nonneg (ae_of_all _ fun ω => le_min (hF_nn ω) hM.le) (hF_int_ν n)
            (ae_of_all _ fun ω => min_le_left _ _)
      _ ≤ C := hbound n
  have h_trunc_int : ∀ n : ℕ, Integrable (fun ω => min (F ω) (↑n : ℝ)) μ := fun n =>
    Integrable.of_bound (hF_meas.min measurable_const).aestronglyMeasurable n
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hF_nn ω) (Nat.cast_nonneg n))]
        exact min_le_right _ _)
  have hC_nn : 0 ≤ C := le_trans (integral_nonneg fun ω => hF_nn ω) (hbound 0)
  have h_trunc_nat : ∀ n : ℕ, ∫ ω, min (F ω) (↑n : ℝ) ∂μ ≤ C := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : ∫ ω, min (F ω) ((0 : ℕ) : ℝ) ∂μ = 0 := by
        simp only [Nat.cast_zero]
        rw [show (fun ω => min (F ω) (0 : ℝ)) = (fun _ => (0 : ℝ)) from
          funext fun ω => min_eq_right (hF_nn ω)]
        simp
      rw [h0]; exact hC_nn
    · exact h_trunc n (by exact_mod_cast hn)
  have h_int : Integrable F μ := by
    refine ⟨hF_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hF_nn)]
    have h_lint_mono : ∀ᵐ ω ∂μ, Monotone
        (fun n : ℕ => ENNReal.ofReal (min (F ω) (↑n : ℝ))) :=
      ae_of_all _ fun ω n m hnm =>
        ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hnm))
    have h_lint_pw : ∀ᵐ ω ∂μ, Tendsto
        (fun n : ℕ => ENNReal.ofReal (min (F ω) (↑n : ℝ))) atTop (nhds (ENNReal.ofReal (F ω))) :=
      ae_of_all _ fun ω => (ENNReal.continuous_ofReal.tendsto _).comp
        (tendsto_atTop_of_eventually_const (i₀ := ⌈F ω⌉₊) fun n hn => by
          rw [min_eq_left]; exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn))
    have h_lint_meas : ∀ n : ℕ, AEMeasurable
        (fun ω => ENNReal.ofReal (min (F ω) (↑n : ℝ))) μ :=
      fun n => (hF_meas.min measurable_const).ennreal_ofReal.aemeasurable
    have h_lint_conv := lintegral_tendsto_of_tendsto_of_monotone h_lint_meas h_lint_mono h_lint_pw
    have h_lint_bound : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (min (F ω) (↑n : ℝ)) ∂μ ≤
        ENNReal.ofReal C := by
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal (h_trunc_int n)
        (ae_of_all _ fun ω => le_min (hF_nn ω) (Nat.cast_nonneg n))]
      exact ENNReal.ofReal_le_ofReal (h_trunc_nat n)
    exact lt_of_le_of_lt (le_of_tendsto' h_lint_conv h_lint_bound) ENNReal.ofReal_lt_top
  refine ⟨h_int, ?_⟩
  have h_mono : ∀ᵐ ω ∂μ, Monotone (fun n : ℕ => min (F ω) (↑n : ℝ)) :=
    ae_of_all _ fun ω n m hnm => min_le_min_left _ (Nat.cast_le.mpr hnm)
  have h_pw : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => min (F ω) (↑n : ℝ)) atTop (nhds (F ω)) :=
    ae_of_all _ fun ω => tendsto_atTop_of_eventually_const (i₀ := ⌈F ω⌉₊) fun n hn => by
      rw [min_eq_left]; exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
  have h_mct : Tendsto (fun n : ℕ => ∫ ω, min (F ω) (↑n : ℝ) ∂μ) atTop (nhds (∫ ω, F ω ∂μ)) :=
    integral_tendsto_of_tendsto_of_monotone h_trunc_int h_int h_mono h_pw
  exact le_of_tendsto' h_mct h_trunc_nat

/-- The uniform-integrability domination: `y − min(y, M) ≤ y²/M` for `y ≥ 0`, `M > 0`. With
`y = (ωf)^{2k}` (so `y² = (ωf)^{4k}`) this is the `F − min(F,M) ≤ G/M` hypothesis of
`moment_tendsto_of_uniform`. (Holds for all `y ≥ 0`: trivially when `y ≤ M`; when `y ≥ M`,
`y − M ≤ y²/M ⇔ 0 ≤ y² − My + M²`, always true.) -/
theorem sub_min_le_sq_div {y M : ℝ} (hy : 0 ≤ y) (hM : 0 < M) :
    y - min y M ≤ y ^ 2 / M := by
  rcases le_total y M with h | h
  · rw [min_eq_left h, sub_self]; positivity
  · rw [min_eq_right h, le_div_iff₀ hM]
    nlinarith [sq_nonneg (y - M), mul_nonneg hy hM.le]

/-- **Moment-convergence core (IV.b).** If `F ≥ 0` is continuous with the uniform-integrability
domination `F − min(F,M) ≤ G/M` by a higher moment `G`, with `F, G` integrable under each `ν n` and
under `μ`, cutoff-uniform `∫G ∂(ν n) ≤ C` and `∫G ∂μ ≤ C`, and weak convergence
`∫min(F,M) ∂(ν n) → ∫min(F,M) ∂μ` on bounded-continuous truncations, then `∫F ∂(ν n) → ∫F ∂μ`.

This is the ε/3 truncation argument: the two tails are `≤ C/M` (uniformly), the middle (a bounded
continuous truncation) converges by weak convergence. Applied with `(F,G) = ((ωf)², (ωf)⁴)` and
`((ωf)⁴, (ωf)⁸)` it gives convergence of the 2nd and 4th moments of the interacting limit. -/
private lemma moment_tendsto_of_uniform
    {ν : ℕ → Measure (Configuration (TorusTestFunction L))}
    {μ : Measure (Configuration (TorusTestFunction L))}
    {F G : Configuration (TorusTestFunction L) → ℝ} {C : ℝ}
    (hF_cont : Continuous F) (hF_meas : Measurable F) (hF_nn : ∀ ω, 0 ≤ F ω)
    (hFG : ∀ ω, ∀ M : ℝ, 0 < M → F ω - min (F ω) M ≤ G ω / M)
    (hF_int_ν : ∀ n, Integrable F (ν n)) (hF_int_μ : Integrable F μ)
    (hG_int_ν : ∀ n, Integrable G (ν n)) (hG_int_μ : Integrable G μ)
    (hG_ν : ∀ n, ∫ ω, G ω ∂(ν n) ≤ C) (hG_μ : ∫ ω, G ω ∂μ ≤ C)
    (hconv : ∀ (g : Configuration (TorusTestFunction L) → ℝ),
      Continuous g → (∃ B, ∀ x, |g x| ≤ B) →
      Tendsto (fun n => ∫ ω, g ω ∂(ν n)) atTop (nhds (∫ ω, g ω ∂μ))) :
    Tendsto (fun n => ∫ ω, F ω ∂(ν n)) atTop (nhds (∫ ω, F ω ∂μ)) := by
  have hG_nn : ∀ ω, 0 ≤ G ω := fun ω => by
    have h := hFG ω 1 one_pos
    rw [div_one] at h
    exact le_trans (sub_nonneg.mpr (min_le_left _ _)) h
  have hC_nn : 0 ≤ C := le_trans (integral_nonneg (fun ω => hG_nn ω)) hG_μ
  -- the truncated, bounded-continuous test function and its key properties
  have key : ∀ M : ℝ, 0 < M → (∀ n, |∫ ω, F ω ∂(ν n) - ∫ ω, min (F ω) M ∂(ν n)| ≤ C / M) ∧
      |∫ ω, F ω ∂μ - ∫ ω, min (F ω) M ∂μ| ≤ C / M ∧
      Tendsto (fun n => ∫ ω, min (F ω) M ∂(ν n)) atTop (nhds (∫ ω, min (F ω) M ∂μ)) := by
    intro M hM
    have hmin_cont : Continuous (fun ω => min (F ω) M) := hF_cont.min continuous_const
    have hmin_bdd : ∃ B, ∀ ω, |min (F ω) M| ≤ B :=
      ⟨M, fun ω => by rw [abs_of_nonneg (le_min (hF_nn ω) hM.le)]; exact min_le_right _ _⟩
    -- tail bound for an arbitrary measure ρ with F,G integrable, ∫G ≤ C
    have tail : ∀ (ρ : Measure (Configuration (TorusTestFunction L)))
        (_ : Integrable F ρ) (_ : Integrable G ρ) (_ : ∫ ω, G ω ∂ρ ≤ C),
        |∫ ω, F ω ∂ρ - ∫ ω, min (F ω) M ∂ρ| ≤ C / M := by
      intro ρ hFρ hGρ hGρC
      have hdiff_nn : ∀ ω, 0 ≤ F ω - min (F ω) M := fun ω => sub_nonneg.mpr (min_le_left _ _)
      have hmin_int : Integrable (fun ω => min (F ω) M) ρ :=
        hFρ.mono' (hF_meas.min measurable_const).aestronglyMeasurable
          (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hF_nn ω) hM.le)]; exact min_le_left _ _)
      rw [← integral_sub hFρ hmin_int, abs_of_nonneg (integral_nonneg hdiff_nn)]
      calc ∫ ω, (F ω - min (F ω) M) ∂ρ
          ≤ ∫ ω, G ω / M ∂ρ :=
            integral_mono_of_nonneg (ae_of_all _ hdiff_nn) (hGρ.div_const M)
              (ae_of_all _ fun ω => hFG ω M hM)
        _ = (∫ ω, G ω ∂ρ) / M := by rw [integral_div]
        _ ≤ C / M := by gcongr
    exact ⟨fun n => tail (ν n) (hF_int_ν n) (hG_int_ν n) (hG_ν n),
      tail μ hF_int_μ hG_int_μ hG_μ, hconv _ hmin_cont hmin_bdd⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  set M := 4 * (C + 1) / ε with hM_def
  have hM_pos : 0 < M := by positivity
  obtain ⟨htail_ν, htail_μ, hmid⟩ := key M hM_pos
  have hCM : C / M ≤ ε / 4 := by
    rw [div_le_iff₀ hM_pos, hM_def,
      show ε / 4 * (4 * (C + 1) / ε) = C + 1 from by field_simp]
    linarith
  rw [Metric.tendsto_atTop] at hmid
  obtain ⟨N₀, hN₀⟩ := hmid (ε / 2) (by positivity)
  refine ⟨N₀, fun n hn => ?_⟩
  have hmid_n := hN₀ n hn
  rw [Real.dist_eq] at hmid_n ⊢
  set a := ∫ ω, F ω ∂(ν n)
  set b := ∫ ω, min (F ω) M ∂(ν n)
  set c := ∫ ω, min (F ω) M ∂μ
  set d := ∫ ω, F ω ∂μ
  have h1 : |a - b| ≤ ε / 4 := le_trans (htail_ν n) hCM
  have h3 : |c - d| ≤ ε / 4 := by rw [abs_sub_comm]; exact le_trans htail_μ hCM
  calc |a - d| ≤ |a - b| + |b - d| := abs_sub_le a b d
    _ ≤ |a - b| + (|b - c| + |c - d|) := by gcongr; exact abs_sub_le b c d
    _ < ε / 4 + (ε / 2 + ε / 4) :=
        add_lt_add_of_le_of_lt h1 (add_lt_add_of_lt_of_le hmid_n h3)
    _ = ε := by ring

/-- **Step IV.b — 4th-moment convergence.** Along the Prokhorov subsequence, the interacting
4th moment converges to that of the limit: `⟨(ωf)⁴⟩_{μ_N} → ⟨(ωf)⁴⟩_μ`. Assembles
`moment_tendsto_of_uniform` with `F=(ωf)⁴`, `G=(ωf)⁸`: ν-integrability from
`torus_interacting_abs_pow_integrable`, the uniform `∫(ωf)⁸ ≤ C` from IV.a, the limit
integrability+bound from `limit_le_of_uniform_bound`, and the UI domination from `sub_min_le_sq_div`. -/
theorem torus_interacting_fourth_moment_tendsto (P : InteractionPolynomial) (mass : ℝ)
    (hmass : 0 < mass) (f : TorusTestFunction L)
    (μ : Measure (Configuration (TorusTestFunction L))) [IsProbabilityMeasure μ]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ (g : Configuration (TorusTestFunction L) → ℝ),
      Continuous g → (∃ B, ∀ x, |g x| ≤ B) →
      Tendsto (fun n => ∫ ω, g ω ∂(torusInteractingMeasure L (φ n + 1) P mass hmass)) atTop
        (nhds (∫ ω, g ω ∂μ))) :
    Tendsto (fun n => ∫ ω, (ω f) ^ 4 ∂(torusInteractingMeasure L (φ n + 1) P mass hmass)) atTop
      (nhds (∫ ω, (ω f) ^ 4 ∂μ)) := by
  obtain ⟨C4, _, hC4⟩ := torus_interacting_fourth_moment_uniform L P mass hmass f
  obtain ⟨C8, _, hC8⟩ := torus_interacting_eighth_moment_uniform L P mass hmass f
  have hF_cont : Continuous (fun ω : Configuration (TorusTestFunction L) => (ω f) ^ 4) :=
    (WeakDual.eval_continuous f).pow 4
  have hF_meas : Measurable (fun ω : Configuration (TorusTestFunction L) => (ω f) ^ 4) :=
    (configuration_eval_measurable f).pow_const 4
  have hG_cont : Continuous (fun ω : Configuration (TorusTestFunction L) => (ω f) ^ 8) :=
    (WeakDual.eval_continuous f).pow 8
  have hG_meas : Measurable (fun ω : Configuration (TorusTestFunction L) => (ω f) ^ 8) :=
    (configuration_eval_measurable f).pow_const 8
  have hF_nn : ∀ ω : Configuration (TorusTestFunction L), 0 ≤ (ω f) ^ 4 := fun ω => by positivity
  have hG_nn : ∀ ω : Configuration (TorusTestFunction L), 0 ≤ (ω f) ^ 8 := fun ω => by positivity
  -- even-power |·| = (·) conversions for ν-side integrability
  have hF_eq : (fun ω : Configuration (TorusTestFunction L) => (ω f) ^ 4) =
      (fun ω => |ω f| ^ 4) := by
    funext ω; rw [show |ω f| ^ 4 = (|ω f| ^ 2) ^ 2 from by ring, sq_abs]; ring
  have hG_eq : (fun ω : Configuration (TorusTestFunction L) => (ω f) ^ 8) =
      (fun ω => |ω f| ^ 8) := by
    funext ω; rw [show |ω f| ^ 8 = (|ω f| ^ 2) ^ 4 from by ring, sq_abs]; ring
  have hF_int_ν : ∀ n, Integrable (fun ω => (ω f) ^ 4)
      (torusInteractingMeasure L (φ n + 1) P mass hmass) := fun n => by
    rw [hF_eq]; exact torus_interacting_abs_pow_integrable L P mass hmass f 4 (by norm_num) (φ n + 1)
  have hG_int_ν : ∀ n, Integrable (fun ω => (ω f) ^ 8)
      (torusInteractingMeasure L (φ n + 1) P mass hmass) := fun n => by
    rw [hG_eq]; exact torus_interacting_abs_pow_integrable L P mass hmass f 8 (by norm_num) (φ n + 1)
  obtain ⟨hF_int_μ, -⟩ :=
    limit_le_of_uniform_bound L hF_cont hF_meas hF_nn hF_int_ν (fun n => hC4 (φ n + 1)) hconv
  obtain ⟨hG_int_μ, hG_μ⟩ :=
    limit_le_of_uniform_bound L hG_cont hG_meas hG_nn hG_int_ν (fun n => hC8 (φ n + 1)) hconv
  exact moment_tendsto_of_uniform (L := L) (G := fun ω => (ω f) ^ 8) (C := C8) hF_cont hF_meas hF_nn
    (fun ω M hM => by
      have h := sub_min_le_sq_div (show (0:ℝ) ≤ (ω f) ^ 4 from by positivity) hM
      rwa [show ((ω f) ^ 4) ^ 2 = (ω f) ^ 8 from by ring] at h)
    hF_int_ν hF_int_μ hG_int_ν hG_int_μ (fun n => hC8 (φ n + 1)) hG_μ hconv

end Pphi2
