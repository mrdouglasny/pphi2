/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.TorusContinuumLimit.TorusInteractingLimit
import Pphi2.InteractingMeasure.CouplingMeasure

/-!
# Continuum limit of the coupling-`g` interacting torus measure (Route A, bricks A4)

The torus pushforward `μ_{g,N}^{torus}` of `interactingLatticeMeasureCoupling`, its uniform second
moment (hence tightness), and the existence of the `N → ∞` subsequential continuum limit — the
weak-coupling analogs of `torusInteractingMeasure`, `torus_interacting_second_moment_uniform`,
`torus_interacting_tightness`, `torusInteractingLimit_exists`. The only `g`-dependent inputs are the
`…_coupling` Nelson/density bricks (`CouplingMeasure.lean`); the free fourth-moment bound is
`g`-independent and is factored out as `latticeFourthMoment_sqrt_le`. See
`planning/route-A-weak-coupling-plan.md`.
-/

namespace Pphi2

open MeasureTheory GaussianField Filter Topology

variable (L : ℝ) [hL : Fact (0 < L)]

/-- **Free fourth-moment bound (`g`-independent).** `(∫ ((ωg)²)² dμ_GFF)^{1/2} ≤ 3·Cg` whenever
`∫ (ωg)² dμ_GFF ≤ Cg` — by 1D Gaussian hypercontractivity `∫(ωg)⁴ ≤ 9(∫(ωg)²)²`. Used by both the
`g=1` and coupling second-moment bounds. -/
lemma latticeFourthMoment_sqrt_le (N : ℕ) [NeZero N] (mass : ℝ) (hmass : 0 < mass)
    (g : FinLatticeField 2 N) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (h_second_le : ∫ ω, (ω g) ^ 2 ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass) ≤ Cg) :
    (∫ ω, ((ω g) ^ 2) ^ (2 : ℝ) ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass)) ^ (1 / 2 : ℝ) ≤ 3 * Cg := by
  set μ_GFF := latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass
    with hμ
  set T := latticeCovarianceGJ 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass with hT
  have hμ_eq : μ_GFF = GaussianField.measure T := rfl
  have h_second_nn : 0 ≤ ∫ ω, (ω g) ^ 2 ∂μ_GFF := integral_nonneg fun ω => sq_nonneg _
  have h_fourth_le : ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF ≤ 9 * Cg ^ 2 := by
    have h_eq4 : ∀ ω : Configuration (FinLatticeField 2 N), ((ω g) ^ 2) ^ 2 = |ω g| ^ 4 := by
      intro ω; rw [show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]; ring
    simp_rw [h_eq4]
    have h_hyper := gaussian_hypercontractive T g 1 4
      (by norm_num : (2:ℝ) ≤ 4) 2 (by norm_num : 1 ≤ 2) (by norm_num : (4:ℝ) = 2 * ↑2)
    have h_lhs_eq : ∫ ω, |ω g| ^ 4 ∂μ_GFF =
        ∫ ω, |ω g| ^ ((4:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T) := by
      rw [hμ_eq]; congr 1; ext ω
      simp only [Nat.cast_one, mul_one]
      exact (Real.rpow_natCast _ 4).symm
    rw [h_lhs_eq]
    have h_int_2_eq : ∫ ω, |ω g| ^ (2 * 1) ∂(GaussianField.measure T) =
        ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
      rw [hμ_eq]; congr 1; ext ω; simp [sq_abs]
    have h_hyper' : ∫ ω, |ω g| ^ ((4:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T) ≤
        ((4:ℝ) - 1) ^ ((4:ℝ) * ↑(1:ℕ) / 2) * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4:ℝ) / 2) := by
      have := h_hyper; rwa [h_int_2_eq] at this
    have h_coeff : ((4:ℝ) - 1) ^ ((4:ℝ) * ↑(1:ℕ) / 2) = 9 := by
      simp only [Nat.cast_one, mul_one]
      rw [show (4:ℝ) / 2 = ↑(2:ℕ) from by norm_num, Real.rpow_natCast]; norm_num
    have h_exp_eq' : (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4:ℝ) / 2) = (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by
      rw [show (4:ℝ) / 2 = ↑(2:ℕ) from by norm_num, Real.rpow_natCast]
    calc ∫ ω, |ω g| ^ ((4:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T)
        ≤ ((4:ℝ) - 1) ^ ((4:ℝ) * ↑(1:ℕ) / 2) * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4:ℝ) / 2) := h_hyper'
      _ = 9 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by rw [h_coeff, h_exp_eq']
      _ ≤ 9 * Cg ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact pow_le_pow_left₀ h_second_nn h_second_le 2
  have h_int_rpow_eq : ∫ ω, ((ω g) ^ 2) ^ (2:ℝ) ∂μ_GFF = ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF := by
    congr 1; ext ω; exact Real.rpow_natCast ((ω g) ^ 2) 2
  have h_fourth_nn : (0:ℝ) ≤ ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF := integral_nonneg fun ω => by positivity
  rw [h_int_rpow_eq]
  calc (∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF) ^ (1/2:ℝ)
      ≤ (9 * Cg ^ 2) ^ (1/2:ℝ) := Real.rpow_le_rpow h_fourth_nn h_fourth_le (by norm_num)
    _ = 3 * Cg := by
        rw [show (9:ℝ) = 3 ^ 2 from by norm_num, ← mul_pow, ← Real.sqrt_eq_rpow,
          Real.sqrt_sq (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hCg)]

/-- The coupling-`g` interacting torus measure `μ_{g,N}^{torus} = (torusEmbedLift)_* μ_{g,N}`. -/
noncomputable def torusInteractingMeasureCoupling (N : ℕ) [NeZero N] (P : InteractionPolynomial)
    (mass : ℝ) (hmass : 0 < mass) (g : ℝ) : Measure (Configuration (TorusTestFunction L)) :=
  Measure.map (torusEmbedLift L N)
    (interactingLatticeMeasureCoupling 2 N P (circleSpacing L N) mass (circleSpacing_pos L N) hmass g)

/-- The coupling-`g` interacting torus measure is a probability measure (`g ≥ 0`). -/
instance torusInteractingMeasureCoupling_isProbability (N : ℕ) [NeZero N]
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) {g : ℝ} (hg : 0 ≤ g) :
    IsProbabilityMeasure (torusInteractingMeasureCoupling L N P mass hmass g) := by
  unfold torusInteractingMeasureCoupling
  haveI := interactingLatticeMeasureCoupling_isProbability 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass hg
  exact Measure.isProbabilityMeasure_map (torusEmbedLift_measurable L N).aemeasurable

/-- **`g`-family Nelson estimate (uniform in `N`).** `∫ (e^{−gV})² ≤ K` for `g ∈ [0,1]`, with `K`
from the `g=1` `nelson_exponential_estimate` (Jensen transfer, `expMoment_two_coupling_le`). -/
theorem nelson_exponential_estimate_coupling (P : InteractionPolynomial) (mass : ℝ)
    (hmass : 0 < mass) {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) [NeZero N],
      ∫ ω, (Real.exp (-(g * interactionFunctional 2 N P (circleSpacing L N) mass ω))) ^ 2
        ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass) ≤ K := by
  obtain ⟨K, hKpos, hKbound⟩ := nelson_exponential_estimate L P mass hmass
  exact ⟨K, hKpos, fun N _ => expMoment_two_coupling_le 2 N (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass P hg0 hg1 (hKbound N)⟩

/-- **Uniform second moment for the coupling-`g` torus measures** (`0 ≤ g ≤ 1`). Density transfer
(`density_transfer_bound_coupling`) + the `g`-Nelson bound + the free fourth-moment bound. -/
theorem torus_interacting_second_moment_uniform_coupling
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) (f : TorusTestFunction L)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (TorusTestFunction L),
      (ω f) ^ 2 ∂(torusInteractingMeasureCoupling L N P mass hmass g) ≤ C := by
  obtain ⟨K, hK_pos, hK_bound⟩ := nelson_exponential_estimate_coupling L P mass hmass hg0 hg1
  obtain ⟨Cg, hCg_pos, hCg_bound⟩ := torusEmbeddedTwoPoint_uniform_bound L mass hmass f
  refine ⟨3 * Real.sqrt K * Cg,
    mul_pos (mul_pos (by norm_num : (0:ℝ) < 3) (Real.sqrt_pos_of_pos hK_pos)) hCg_pos,
    fun N _ => ?_⟩
  set μ_g := interactingLatticeMeasureCoupling 2 N P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass g with hμg
  set μ_GFF := latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass
  set ι := torusEmbedLift L N
  set gf := latticeTestFn L N f with hgf
  have hι_meas : AEMeasurable ι μ_g := (torusEmbedLift_measurable L N).aemeasurable
  change ∫ ω, (ω f) ^ 2 ∂(Measure.map ι μ_g) ≤ 3 * Real.sqrt K * Cg
  rw [integral_map hι_meas
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable]
  have h_eval : ∀ ω : Configuration (FinLatticeField 2 N), (ι ω) f = ω gf :=
    fun ω => torusEmbedLift_eval_eq L N f ω
  simp_rw [h_eval]
  -- ∫ (ω gf)² dμ_g ≤ √K · 3Cg via density transfer + free fourth moment
  have hF_nn : ∀ ω : Configuration (FinLatticeField 2 N), 0 ≤ (ω gf) ^ 2 := fun ω => sq_nonneg _
  have hF_meas : AEStronglyMeasurable (fun ω : Configuration (FinLatticeField 2 N) => (ω gf) ^ 2)
      μ_GFF := ((configuration_eval_measurable gf).pow_const 2).aestronglyMeasurable
  have hF_sq_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) => ((ω gf) ^ 2) ^ 2)
      μ_GFF := by
    have h4 : MemLp (fun ω : Configuration (FinLatticeField 2 N) => ω gf) 4 μ_GFF := by
      exact_mod_cast pairing_memLp (latticeCovarianceGJ 2 N (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass) gf 4
    have hmem := h4.norm_rpow (p := (4 : ENNReal)) (by norm_num) (by norm_num)
    rw [memLp_one_iff_integrable] at hmem
    have h_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) => ‖ω gf‖ ^ (4 : ℕ))
        μ_GFF := hmem.congr (Filter.Eventually.of_forall fun ω => by simp [ENNReal.toReal_ofNat])
    refine h_int.congr (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [Real.norm_eq_abs]
    conv_rhs => rw [show ω gf ^ 2 = |ω gf| ^ 2 from (sq_abs _).symm]
    ring
  have h_dt := density_transfer_bound_coupling 2 N (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass P hg0 K (hK_bound N) (fun ω => (ω gf) ^ 2) hF_nn hF_meas hF_sq_int
  have h_second_le : ∫ ω, (ω gf) ^ 2 ∂μ_GFF ≤ Cg := by
    rw [(torusEmbeddedTwoPoint_eq_lattice_second_moment L N mass hmass f).symm]; exact hCg_bound N
  have hfree := latticeFourthMoment_sqrt_le L N mass hmass gf hCg_pos.le h_second_le
  have hK_sqrt : K ^ (1/2:ℝ) = Real.sqrt K := (Real.sqrt_eq_rpow K).symm
  calc ∫ ω, (ω gf) ^ 2 ∂μ_g
      ≤ K ^ (1/2:ℝ) * (∫ ω, ((ω gf) ^ 2) ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) := h_dt
    _ ≤ K ^ (1/2:ℝ) * (3 * Cg) :=
        mul_le_mul_of_nonneg_left hfree (Real.rpow_nonneg hK_pos.le _)
    _ = Real.sqrt K * (3 * Cg) := by rw [hK_sqrt]
    _ = 3 * Real.sqrt K * Cg := by ring

/-- **Tightness of the coupling-`g` torus interacting measures** (`0 ≤ g ≤ 1`). -/
theorem torus_interacting_tightness_coupling
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    ∀ ε : ℝ, 0 < ε →
    ∃ (K : Set (Configuration (TorusTestFunction L))), IsCompact K ∧
      ∀ (N : ℕ) [NeZero N], 1 - ε ≤ (torusInteractingMeasureCoupling L N P mass hmass g K).toReal := by
  intro ε hε
  obtain ⟨K, hK_compact, hK_bound⟩ := configuration_tight_of_uniform_second_moments
    (ι := {N : ℕ // 0 < N})
    (fun ⟨N, hN⟩ => haveI : NeZero N := ⟨by omega⟩;
      torusInteractingMeasureCoupling L N P mass hmass g)
    (fun ⟨N, hN⟩ => by
      haveI : NeZero N := ⟨by omega⟩
      exact torusInteractingMeasureCoupling_isProbability L N P mass hmass hg0)
    (fun f ⟨N, hN⟩ => by
      haveI : NeZero N := ⟨by omega⟩
      change Integrable (fun ω => (ω f) ^ 2) (torusInteractingMeasureCoupling L N P mass hmass g)
      unfold torusInteractingMeasureCoupling
      rw [integrable_map_measure
        ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
        (torusEmbedLift_measurable L N).aemeasurable]
      have h_eq : (fun ω => (ω f) ^ 2) ∘ (torusEmbedLift L N) =
          fun ω => (ω (latticeTestFn L N f)) ^ 2 := by
        ext ω; simp [Function.comp, torusEmbedLift_eval_eq L N f ω]
      rw [h_eq]
      set gf := latticeTestFn L N f
      set μ_GFF := latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass
      have hZ := partitionFn_pos_of_nonneg 2 N P (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass hg0
      suffices h : Integrable (fun ω : Configuration (FinLatticeField 2 N) => (ω gf) ^ 2)
          (μ_GFF.withDensity (fun ω =>
            ENNReal.ofReal (Real.exp (-(g * interactionFunctional 2 N P (circleSpacing L N) mass ω))))) by
        unfold interactingLatticeMeasureCoupling
        exact h.smul_measure (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ).ne'))
      have hf_meas : Measurable (fun ω : Configuration (FinLatticeField 2 N) =>
          ENNReal.ofReal (Real.exp (-(g * interactionFunctional 2 N P (circleSpacing L N) mass ω)))) :=
        ENNReal.measurable_ofReal.comp
          (((interactionFunctional_measurable 2 N P (circleSpacing L N) mass).const_mul g).neg.exp)
      apply (integrable_withDensity_iff hf_meas
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
      have hbw_simp : ∀ ω : Configuration (FinLatticeField 2 N),
          (ENNReal.ofReal (Real.exp (-(g * interactionFunctional 2 N P (circleSpacing L N) mass ω)))).toReal
            = Real.exp (-(g * interactionFunctional 2 N P (circleSpacing L N) mass ω)) :=
        fun ω => ENNReal.toReal_ofReal (Real.exp_pos _).le
      simp_rw [hbw_simp]
      obtain ⟨B, hB⟩ := interactionFunctional_bounded_below 2 N P (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass
      have h_sq_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) => (ω gf) ^ 2) μ_GFF :=
        (pairing_memLp (latticeCovarianceGJ 2 N (circleSpacing L N) mass
          (circleSpacing_pos L N) hmass) gf 2).integrable_sq
      apply (h_sq_int.mul_const (Real.exp (g * B))).mono
      · exact ((configuration_eval_measurable gf).pow_const 2).aestronglyMeasurable.mul
          (Measurable.aestronglyMeasurable
            (((interactionFunctional_measurable 2 N P (circleSpacing L N) mass).const_mul g).neg.exp))
      · refine Filter.Eventually.of_forall fun ω => ?_
        simp only [Real.norm_eq_abs]
        have h1 : 0 ≤ (ω gf) ^ 2 := sq_nonneg _
        have h2 : 0 < Real.exp (-(g * interactionFunctional 2 N P (circleSpacing L N) mass ω)) :=
          Real.exp_pos _
        have h3 : Real.exp (-(g * interactionFunctional 2 N P (circleSpacing L N) mass ω))
            ≤ Real.exp (g * B) := Real.exp_le_exp_of_le (by nlinarith [hB ω, hg0])
        rw [abs_of_nonneg (mul_nonneg h1 h2.le), abs_of_nonneg (mul_nonneg h1 (Real.exp_pos _).le)]
        exact mul_le_mul_of_nonneg_left h3 h1)
    (fun f => by
      obtain ⟨C, _, hC_bound⟩ := torus_interacting_second_moment_uniform_coupling L P mass hmass f hg0 hg1
      exact ⟨C, fun ⟨N, hN⟩ => by haveI : NeZero N := ⟨by omega⟩; exact hC_bound N⟩)
    ε hε
  exact ⟨K, hK_compact, fun N inst => hK_bound ⟨N, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩

/-- **Existence of the coupling-`g` torus continuum limit** (`0 ≤ g ≤ 1`). Subsequential weak limit
via Prokhorov + tightness — the weak-coupling analog of `torusInteractingLimit_exists`. -/
theorem torusInteractingLimitCoupling_exists
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1) :
    ∃ (φ : ℕ → ℕ) (μ : Measure (Configuration (TorusTestFunction L))),
      StrictMono φ ∧ IsProbabilityMeasure μ ∧
      ∀ (f : Configuration (TorusTestFunction L) → ℝ),
        Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(torusInteractingMeasureCoupling L (φ n + 1) P mass hmass g))
          atTop (nhds (∫ ω, f ω ∂μ)) := by
  exact prokhorov_configuration
    (fun n => torusInteractingMeasureCoupling L (n + 1) P mass hmass g)
    (fun n => torusInteractingMeasureCoupling_isProbability L (n + 1) P mass hmass hg0)
    (fun ε hε => by
      obtain ⟨K, hK_compact, hK_bound⟩ :=
        torus_interacting_tightness_coupling L P mass hmass hg0 hg1 ε hε
      exact ⟨K, hK_compact, fun n => hK_bound (n + 1)⟩)

end Pphi2
