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
import Pphi2.AsymTorus.MomentBoundOS1
import Pphi2.GeneralResults.WeakLimitMoment
import GaussianField.HypercontractiveNat
import GaussianField.Tightness
import GaussianField.ConfigurationEmbedding

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

/-- The isotropic-lattice interacting measure pushed to the torus is a probability measure. -/
theorem asymTorusInteractingMeasureIso_isProbability (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (P : InteractionPolynomial) (mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    IsProbabilityMeasure (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) := by
  haveI := interactingLatticeMeasureAsym_isProbability Nt Ns P a mass ha hmass
  exact Measure.isProbabilityMeasure_map
    (asymTorusEmbedLiftIso_measurable Lt Ls Nt Ns a).aemeasurable

/-- The squared evaluation `(ω f)²` is integrable under the isotropic interacting torus measure.
Pushes through the embedding to `(ω g)²` under `interactingLatticeMeasureAsym`, then bounds the
Boltzmann-weighted Gaussian integral via `pairing_memLp` + bounded-below interaction. -/
theorem asymTorusInteractingMeasureIso_sq_integrable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (P : InteractionPolynomial) (mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymTorusTestFunction Lt Ls) :
    Integrable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => (ω f) ^ 2)
      (asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) := by
  unfold asymTorusInteractingMeasureIso
  rw [integrable_map_measure
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
    (asymTorusEmbedLiftIso_measurable Lt Ls Nt Ns a).aemeasurable]
  have h_eq : (fun ω : Configuration (AsymTorusTestFunction Lt Ls) => (ω f) ^ 2) ∘
      (asymTorusEmbedLiftIso Lt Ls Nt Ns a) =
      fun ω : Configuration (AsymLatticeField Nt Ns) =>
        (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ 2 := by
    ext ω; simp [Function.comp, asymTorusEmbedLiftIso_eval_eq Lt Ls Nt Ns a f ω]
  rw [h_eq]
  set g := asymLatticeTestFnIso Lt Ls Nt Ns a f
  set μ_GFF := latticeGaussianMeasureAsym Nt Ns a mass ha hmass
  set bw := boltzmannWeightAsym Nt Ns P a mass
  obtain ⟨B, hB⟩ := interactionFunctionalAsym_bounded_below Nt Ns P a mass ha hmass
  have hZ := partitionFunctionAsym_pos Nt Ns P a mass ha hmass
  suffices h : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) => (ω g) ^ 2)
      (μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) by
    unfold interactingLatticeMeasureAsym
    exact h.smul_measure (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ).ne'))
  have hf_meas : Measurable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
      ENNReal.ofReal (bw ω)) :=
    ENNReal.measurable_ofReal.comp
      ((interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp)
  apply (integrable_withDensity_iff hf_meas
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  have hbw_simp : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      (ENNReal.ofReal (bw ω)).toReal = bw ω :=
    fun ω => ENNReal.toReal_ofReal (le_of_lt (boltzmannWeightAsym_pos Nt Ns P a mass ω))
  simp_rw [hbw_simp]
  have h_sq_int : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) => (ω g) ^ 2) μ_GFF :=
    (pairing_memLp (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) g 2).integrable_sq
  apply (h_sq_int.mul_const (Real.exp B)).mono
  · exact ((configuration_eval_measurable g).pow_const 2).aestronglyMeasurable.mul
      (Measurable.aestronglyMeasurable
        (interactionFunctionalAsym_measurable Nt Ns P a mass).neg.exp)
  · exact Filter.Eventually.of_forall fun ω => by
      simp only [Real.norm_eq_abs]
      have h1 : 0 ≤ (ω g) ^ 2 := sq_nonneg _
      have h2 : 0 < bw ω := boltzmannWeightAsym_pos Nt Ns P a mass ω
      have h3 : bw ω ≤ Real.exp B := by
        change Real.exp (-interactionFunctionalAsym Nt Ns P a mass ω) ≤ Real.exp B
        exact Real.exp_le_exp_of_le (by linarith [hB ω])
      rw [abs_of_nonneg (mul_nonneg h1 (le_of_lt h2)),
          abs_of_nonneg (mul_nonneg h1 (le_of_lt (Real.exp_pos B)))]
      exact mul_le_mul_of_nonneg_left h3 h1

/-- **Existence of the isotropic UV continuum limit.** Along any isotropic lattice sequence
`(Nt k, Ns k, a k)` with `Nt k·a k = Lt`, `Ns k·a k = Ls`, `a k → 0`, a subsequence of the
interacting torus measures converges weakly to a probability measure `μ` on
`Configuration (AsymTorusTestFunction Lt Ls)`.

Tightness from the uniform second moment (`asymTorusIso_interacting_second_moment_uniform`) via
Mitoma–Chebyshev (`configuration_tight_of_uniform_second_moments`), then Prokhorov extraction.
Heterogeneous analogue of `asymTorusInteractingLimit_exists`. -/
theorem asymTorusIso_interacting_limit_exists
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k)) (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, (Nt k : ℝ) * a k = Lt) (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) :
    ∃ (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
      (_ : IsProbabilityMeasure μ) (φ : ℕ → ℕ) (_ : StrictMono φ),
    ∀ (F : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous F → (∃ C, ∀ x, |F x| ≤ C) →
        Filter.Tendsto (fun n => ∫ ω, F ω ∂(haveI := hNt (φ n); haveI := hNs (φ n)
            asymTorusInteractingMeasureIso Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n)) P mass
              (ha (φ n)) hmass))
          Filter.atTop (nhds (∫ ω, F ω ∂μ)) := by
  set ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)) := fun k =>
    haveI := hNt k; haveI := hNs k
    asymTorusInteractingMeasureIso Lt Ls (Nt k) (Ns k) (a k) P mass (ha k) hmass with hν_def
  have hν_prob : ∀ k, IsProbabilityMeasure (ν k) := fun k => by
    haveI := hNt k; haveI := hNs k
    exact asymTorusInteractingMeasureIso_isProbability Lt Ls (Nt k) (Ns k) (a k) P mass (ha k) hmass
  obtain ⟨φ, μ, hφ_mono, hμ_prob, hconv⟩ := prokhorov_configuration ν hν_prob
    (fun ε hε => by
      refine configuration_tight_of_uniform_second_moments ν hν_prob
        (fun f k => by
          haveI := hNt k; haveI := hNs k
          exact asymTorusInteractingMeasureIso_sq_integrable Lt Ls (Nt k) (Ns k) (a k)
            P mass (ha k) hmass f)
        (fun f => by
          obtain ⟨C, _, hC⟩ := asymTorusIso_interacting_second_moment_uniform Lt Ls P mass hmass
            Nt Ns a hNt hNs ha hvolt hvols ha0 f
          exact ⟨C, fun k => hC k⟩)
        ε hε)
  exact ⟨μ, hμ_prob, φ, hφ_mono, hconv⟩

/-- **The isotropic UV continuum limit has the Green-controlled exponential moment bound.**

Along any isotropic lattice sequence `(Nt k, Ns k, a k)` (volume `Lt`, `Ls`; `a k → 0`), the UV
continuum-limit torus measure `μ` satisfies `MeasureHasGreenMomentBound` with `C = 1` and the
*uniform* Nelson constant `K`:

  `∫ exp(|ω f|) dμ ≤ K · exp(asymTorusContinuumGreen f f)`.

This is the Phase-3 endpoint: the cutoff bound `∫ exp|ωf| dμ̃_k ≤ K·exp(σ²_k)` (`K` uniform) plus
`σ²_k → asymTorusContinuumGreen f f` (`second_moment_asym_tendsto`) pass to the weak limit by
`weakLimit_exponential_moment` (truncation + MCT). `MeasureHasGreenMomentBound`, never produced for
the metric-mismatched square construction, is here a **theorem** (modulo the two analytic
axioms). -/
theorem asymTorusIso_measureHasGreenMomentBound
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k)) (ha : ∀ k, 0 < a k)
    (hvolt : ∀ k, (Nt k : ℝ) * a k = Lt) (hvols : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Filter.Tendsto a Filter.atTop (nhds 0)) :
    ∃ (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls))) (K : ℝ),
      IsProbabilityMeasure μ ∧ 0 < K ∧ MeasureHasGreenMomentBound Ls mass hmass K 1 μ := by
  obtain ⟨μ, hμ_prob, φ, hφ_mono, hconv⟩ :=
    asymTorusIso_interacting_limit_exists Lt Ls P mass hmass Nt Ns a hNt hNs ha hvolt hvols ha0
  obtain ⟨K, hK_pos, hcutoff⟩ :=
    asymTorusInteractingMeasureIso_exponentialMomentBound_cutoff Lt Ls P mass hmass
  haveI := hμ_prob
  refine ⟨μ, K, hμ_prob, hK_pos, fun f => ?_⟩
  -- Subsequence measures and their uniform probability instances
  set ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)) := fun n =>
    haveI := hNt (φ n); haveI := hNs (φ n)
    asymTorusInteractingMeasureIso Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n)) P mass (ha (φ n)) hmass
    with hν_def
  have hν_prob : ∀ n, IsProbabilityMeasure (ν n) := fun n => by
    haveI := hNt (φ n); haveI := hNs (φ n)
    exact asymTorusInteractingMeasureIso_isProbability Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n))
      P mass (ha (φ n)) hmass
  -- The lattice second moment along the subsequence
  set B : ℕ → ℝ := fun n => K * Real.exp (haveI := hNt (φ n); haveI := hNs (φ n)
    ∫ ω : Configuration (AsymLatticeField (Nt (φ n)) (Ns (φ n))),
      (ω (asymLatticeTestFnIso Lt Ls (Nt (φ n)) (Ns (φ n)) (a (φ n)) f)) ^ 2
      ∂(latticeGaussianMeasureAsym (Nt (φ n)) (Ns (φ n)) (a (φ n)) mass (ha (φ n)) hmass))
    with hB_def
  -- B n → K · exp(asymTorusContinuumGreen f f): the σ² converge to the Green's function
  have hφ_atTop : Filter.Tendsto φ Filter.atTop Filter.atTop := hφ_mono.tendsto_atTop
  have hσ2_full : Filter.Tendsto (fun k => haveI := hNt k; haveI := hNs k
      ∫ ω : Configuration (AsymLatticeField (Nt k) (Ns k)),
        (ω (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) f)) ^ 2
        ∂(latticeGaussianMeasureAsym (Nt k) (Ns k) (a k) mass (ha k) hmass))
      Filter.atTop (nhds (asymTorusContinuumGreen Lt Ls mass hmass f f)) := by
    have heq : (fun k => haveI := hNt k; haveI := hNs k
        ∫ ω : Configuration (AsymLatticeField (Nt k) (Ns k)),
          (ω (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) f)) ^ 2
          ∂(latticeGaussianMeasureAsym (Nt k) (Ns k) (a k) mass (ha k) hmass)) =
        fun k => haveI := hNt k; haveI := hNs k
          covariance (latticeCovarianceAsymGJ (Nt k) (Ns k) (a k) mass (ha k) hmass)
            (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) f)
            (asymLatticeTestFnIso Lt Ls (Nt k) (Ns k) (a k) f) := by
      funext k; haveI := hNt k; haveI := hNs k
      exact second_moment_eq_covariance _ _
    rw [heq]
    exact second_moment_asym_tendsto Lt Ls mass hmass Nt Ns a hNt hNs ha hvolt hvols ha0 f f
  have hB_tendsto : Filter.Tendsto B Filter.atTop
      (nhds (K * Real.exp (asymTorusContinuumGreen Lt Ls mass hmass f f))) := by
    rw [hB_def]
    exact ((Real.continuous_exp.tendsto _).comp (hσ2_full.comp hφ_atTop)).const_mul K
  -- Uniform per-n exponential moment bound from the cutoff bound
  have h_unif : ∀ n, Integrable (fun ω => Real.exp (|ω f|)) (ν n) ∧
      ∫ ω, Real.exp (|ω f|) ∂(ν n) ≤ B n := fun n => by
    haveI := hNt (φ n); haveI := hNs (φ n)
    exact hcutoff f (Nt (φ n)) (Ns (φ n)) (a (φ n)) (ha (φ n)) (hvolt (φ n)) (hvols (φ n))
  -- Bounded-continuous weak convergence along the subsequence
  have hbc : ∀ (g : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous g → (∃ C, ∀ x, |g x| ≤ C) →
      Filter.Tendsto (fun n => ∫ ω, g ω ∂(ν n)) Filter.atTop (nhds (∫ ω, g ω ∂μ)) :=
    fun g hg_cont hg_bdd => hconv g hg_cont hg_bdd
  -- Pass to the weak limit (truncation + MCT)
  obtain ⟨hint, hle⟩ := weakLimit_exponential_moment ν hν_prob μ hbc f B
    (K * Real.exp (asymTorusContinuumGreen Lt Ls mass hmass f f)) hB_tendsto h_unif
  refine ⟨hint, ?_⟩
  rw [one_mul]
  exact hle

end Pphi2

end
