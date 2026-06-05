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

end Pphi2
