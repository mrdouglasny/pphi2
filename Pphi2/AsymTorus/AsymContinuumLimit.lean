/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# UV continuum limit of the isotropic interacting measure (heterogeneous lattice)

The continuum (`a → 0`) limit of the isotropic-lattice interacting measures, pushed to the
asymmetric torus, at fixed `(Lt, Ls)`. This is the heterogeneous analogue of the square-via-
geometric-mean construction in `AsymTorus/AsymTorusInteractingLimit.lean`, now metric-correct.

## Main results (this file, in progress)

- `asymTorusIso_interacting_second_moment_density_transfer` — interacting `2`nd moment bounded
  by the free Gaussian `2`nd moment (Cauchy–Schwarz density transfer + Gaussian `4`th moment).

## Reference

Simon, *The P(φ)₂ Euclidean QFT*, Ch. VIII; Glimm–Jaffe, *Quantum Physics*, §19.
-/

import Pphi2.AsymTorus.AsymCutoffBound
import GaussianField.HypercontractiveNat

noncomputable section

open MeasureTheory GaussianField

namespace Pphi2

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-- **Interacting second moment ≤ free Gaussian second moment** (heterogeneous lattice).

For each torus test function `f` and lattice `(Nt, Ns, a)` with `Nt·a = Lt`, `Ns·a = Ls`,

  `∫ (ω f)² dμ̃_int ≤ C · ∫ (ω g)² dμ_{GFF,asym}`,    `g = asymLatticeTestFnIso f`,

with `C = 3√K` (`K` the uniform Nelson constant). Cauchy–Schwarz density transfer
(`density_transfer_bound_iso`) plus the Gaussian `4`th-moment bound `∫(ωg)⁴ ≤ 9(∫(ωg)²)²`
(`gaussian_hypercontractive`). Heterogeneous analogue of
`asymTorus_interacting_second_moment_density_transfer`. -/
theorem asymTorusIso_interacting_second_moment_density_transfer
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : AsymTorusTestFunction Lt Ls) (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
      (a : ℝ) (ha : 0 < a), (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls →
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      (ω f) ^ 2 ∂(asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ≤
    C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
      (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ 2
        ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    asymNelson_exponential_estimate_iso P mass hmass Lt Ls hLt.out hLs.out
  refine ⟨3 * Real.sqrt K, mul_pos (by norm_num : (0 : ℝ) < 3)
    (Real.sqrt_pos_of_pos hK_pos), ?_⟩
  intro f Nt Ns _ _ a ha hvolt hvols
  set μ_int := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  set μ_GFF := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  set ι := asymTorusEmbedLiftIso Lt Ls Nt Ns a
  set g := asymLatticeTestFnIso Lt Ls Nt Ns a f
  set T := latticeCovarianceAsymGJ Nt Ns a mass ha hmass
  have hμ_eq : μ_GFF = GaussianField.measure T := rfl
  have hι_meas : AEMeasurable ι μ_int :=
    (asymTorusEmbedLiftIso_measurable Lt Ls Nt Ns a).aemeasurable
  change ∫ ω, (ω f) ^ 2 ∂(Measure.map ι μ_int) ≤
    3 * Real.sqrt K * ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω g) ^ 2 ∂μ_GFF
  rw [integral_map hι_meas
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable]
  have h_eval : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      (ι ω) f = ω g := fun ω => asymTorusEmbedLiftIso_eval_eq Lt Ls Nt Ns a f ω
  simp_rw [h_eval]
  have hZ_ge_one := partitionFunctionAsym_ge_one Nt Ns P a mass ha hmass
  have hF_nn : ∀ ω : Configuration (AsymLatticeField Nt Ns), 0 ≤ (ω g) ^ 2 :=
    fun ω => sq_nonneg _
  have hF_meas : AEStronglyMeasurable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      (ω g) ^ 2) μ_GFF :=
    ((configuration_eval_measurable g).pow_const 2).aestronglyMeasurable
  have hF_sq_int : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      ((ω g) ^ 2) ^ 2) μ_GFF := by
    have h4 : MemLp (fun ω : Configuration (AsymLatticeField Nt Ns) => ω g) 4 μ_GFF := by
      exact_mod_cast pairing_memLp T g 4
    have hmem := h4.norm_rpow (p := (4 : ENNReal))
      (by norm_num : (4 : ENNReal) ≠ 0) (by norm_num : (4 : ENNReal) ≠ ⊤)
    rw [memLp_one_iff_integrable] at hmem
    have h_int : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
        ‖ω g‖ ^ (4 : ℕ)) μ_GFF := by
      refine hmem.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp [ENNReal.toReal_ofNat]
    exact h_int.congr (Filter.Eventually.of_forall fun ω => by
      dsimp only
      rw [Real.norm_eq_abs]
      conv_rhs => rw [show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]
      ring)
  have h_dt := density_transfer_bound_iso Nt Ns P a mass ha hmass K hK_pos
    (hK_bound Nt Ns a ha hvolt hvols)
    hZ_ge_one (fun ω => (ω g) ^ 2) hF_nn hF_meas hF_sq_int
  have h_int_rpow_eq : ∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2 : ℝ) ∂μ_GFF =
      ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF := by
    congr 1; ext ω; exact Real.rpow_natCast ((ω g) ^ 2) 2
  have h_second_nn : 0 ≤ ∫ ω, (ω g) ^ 2 ∂μ_GFF :=
    integral_nonneg fun ω => sq_nonneg _
  have h_fourth_le : ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF ≤
      9 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by
    have h_eq4 : ∀ ω : Configuration (AsymLatticeField Nt Ns),
        ((ω g) ^ 2) ^ 2 = |ω g| ^ 4 := by
      intro ω; rw [show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]; ring
    simp_rw [h_eq4]
    have h_hyper := gaussian_hypercontractive T g 1 4
      (by norm_num : (2 : ℝ) ≤ 4) 2 (by norm_num : 1 ≤ 2)
      (by norm_num : (4 : ℝ) = 2 * ↑2)
    have h_lhs_eq : ∫ ω, |ω g| ^ 4 ∂μ_GFF =
        ∫ ω, |ω g| ^ ((4 : ℝ) * ↑(1 : ℕ)) ∂(GaussianField.measure T) := by
      rw [hμ_eq]; congr 1; ext ω
      simp only [Nat.cast_one, mul_one]; exact (Real.rpow_natCast _ 4).symm
    rw [h_lhs_eq]
    have h_coeff : ((4 : ℝ) - 1) ^ ((4 : ℝ) * ↑(1 : ℕ) / 2) = 9 := by
      simp only [Nat.cast_one, mul_one]
      rw [show (4 : ℝ) / 2 = ↑(2 : ℕ) from by norm_num, Real.rpow_natCast]; norm_num
    have h_exp_eq' : (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4 : ℝ) / 2) =
        (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by
      rw [show (4 : ℝ) / 2 = ↑(2 : ℕ) from by norm_num, Real.rpow_natCast]
    have h_int_2_eq : ∫ ω, |ω g| ^ (2 * 1) ∂(GaussianField.measure T) =
        ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
      rw [hμ_eq]; congr 1; ext ω; simp [sq_abs]
    have h_hyper' : ∫ ω, |ω g| ^ ((4 : ℝ) * ↑(1 : ℕ)) ∂(GaussianField.measure T) ≤
        ((4 : ℝ) - 1) ^ ((4 : ℝ) * ↑(1 : ℕ) / 2) *
        (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4 : ℝ) / 2) := by
      have := h_hyper; rwa [h_int_2_eq] at this
    calc ∫ ω, |ω g| ^ ((4 : ℝ) * ↑(1 : ℕ)) ∂(GaussianField.measure T)
        ≤ ((4 : ℝ) - 1) ^ ((4 : ℝ) * ↑(1 : ℕ) / 2) *
          (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4 : ℝ) / 2) := h_hyper'
      _ = 9 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by rw [h_coeff, h_exp_eq']
  have h_fourth_nn : (0 : ℝ) ≤ ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF :=
    integral_nonneg fun ω => by positivity
  have h_4th_bound : (∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2 : ℝ) ∂μ_GFF) ^ (1 / 2 : ℝ) ≤
      3 * ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
    rw [h_int_rpow_eq]
    calc (∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF) ^ (1 / 2 : ℝ)
        ≤ (9 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow h_fourth_nn h_fourth_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
      _ = 3 * ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
          rw [show 9 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 =
            (3 * ∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 from by ring]
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) h_second_nn)]
  have hK_sqrt : K ^ (1 / 2 : ℝ) = Real.sqrt K := (Real.sqrt_eq_rpow K).symm
  calc ∫ ω, (ω g) ^ 2 ∂μ_int
      ≤ K ^ (1 / 2 : ℝ) * (∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2 : ℝ) ∂μ_GFF) ^ (1 / 2 : ℝ) := h_dt
    _ ≤ K ^ (1 / 2 : ℝ) * (3 * ∫ ω, (ω g) ^ 2 ∂μ_GFF) :=
        mul_le_mul_of_nonneg_left h_4th_bound (Real.rpow_nonneg hK_pos.le _)
    _ = Real.sqrt K * (3 * ∫ ω, (ω g) ^ 2 ∂μ_GFF) := by rw [hK_sqrt]
    _ = 3 * Real.sqrt K * ∫ ω, (ω g) ^ 2 ∂μ_GFF := by ring

/-- **Uniform second moment along an isotropic sequence.** For any test function `f` and any
isotropic lattice sequence `(Nt k, Ns k, a k)` with `Nt k·a k = Lt`, `Ns k·a k = Ls`, `a k → 0`,
the interacting second moment `∫ (ω f)² dμ̃_int,k` is bounded uniformly in `k`.

The free Gaussian second moment `∫ (ω g_k)² dμ_{GFF,k} = ⟪T_k g_k, T_k g_k⟫` *converges* (to
`asymTorusContinuumGreen f f`, by `second_moment_asym_tendsto`) hence is bounded; the density
transfer then bounds the interacting moment by `3√K` times it. -/
theorem asymTorusIso_interacting_second_moment_uniform
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k)) (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, (Nt k : ℝ) * a k = Lt) (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0))
    (f : AsymTorusTestFunction Lt Ls) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ,
      ∫ ω, (ω f) ^ 2 ∂(haveI := hNt k; haveI := hNs k
        asymTorusInteractingMeasureIso Lt Ls (Nt k) (Ns k) (a k) P mass (ha k) hmass) ≤ C := by
  obtain ⟨Cdt, hCdt_pos, hCdt⟩ :=
    asymTorusIso_interacting_second_moment_density_transfer Lt Ls P mass hmass
  -- The free Gaussian second moment along the sequence
  set σ2 : ℕ → ℝ := fun k => haveI := hNt k; haveI := hNs k
    ∫ ω : Configuration (AsymLatticeField (Nt k) (Ns k)),
      (ω (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) f)) ^ 2
      ∂(latticeGaussianMeasureAsym (Nt k) (Ns k) (a k) mass (ha k) hmass) with hσ2_def
  -- σ2 k = covariance(T_k) g_k g_k → converges, hence bounded
  have hσ2_eq : σ2 = fun k => haveI := hNt k; haveI := hNs k
      covariance (latticeCovarianceAsymGJ (Nt k) (Ns k) (a k) mass (ha k) hmass)
        (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) f)
        (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) f) := by
    funext k; haveI := hNt k; haveI := hNs k
    rw [hσ2_def]
    exact second_moment_eq_covariance _ _
  have hσ2_tendsto : Filter.Tendsto σ2 Filter.atTop
      (nhds (asymTorusContinuumGreen Lt Ls mass hmass f f)) := by
    rw [hσ2_eq]
    exact second_moment_asym_tendsto Lt Ls mass hmass Nt Ns a hNt hNs ha hvolt hvols ha0 f f
  obtain ⟨Cg, hCg⟩ := hσ2_tendsto.bddAbove_range
  have hσ2_le : ∀ k, σ2 k ≤ Cg := fun k => hCg (Set.mem_range_self k)
  have hσ2_nn : ∀ k, 0 ≤ σ2 k := by
    intro k; rw [hσ2_def]; exact integral_nonneg fun ω => sq_nonneg _
  have hCg_nn : 0 ≤ Cg := le_trans (hσ2_nn 0) (hσ2_le 0)
  refine ⟨Cdt * Cg + 1, by positivity, fun k => ?_⟩
  haveI := hNt k; haveI := hNs k
  calc ∫ ω, (ω f) ^ 2
        ∂(asymTorusInteractingMeasureIso Lt Ls (Nt k) (Ns k) (a k) P mass (ha k) hmass)
      ≤ Cdt * σ2 k := hCdt f (Nt k) (Ns k) (a k) (ha k) (hvolt k) (hvols k)
    _ ≤ Cdt * Cg := mul_le_mul_of_nonneg_left (hσ2_le k) hCdt_pos.le
    _ ≤ Cdt * Cg + 1 := by linarith

end Pphi2

end
