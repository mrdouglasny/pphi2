/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.AsymTorus.AsymSliceFamilySusceptibility
import Pphi2.AsymTorus.AsymBandFreeComparison
import Pphi2.AsymTorus.AsymLowModeBand
import Pphi2.AsymTorus.AsymInfraredBound
import Pphi2.AsymTorus.AsymVarianceDischarge
import Pphi2.AsymTorus.AsymGroundIntegrability

/-!
# Layer-B2 Stage C: master assembly (thresholded interacting ≤ free variance bound)

The Stage-C master theorem
`asymInteractingVariance_le_freeVariance_lattice_thresholded`, restricted to
quartic `P` through its FSS high branch: at fixed spatial
circumference `Ls`, there are `C, L₀, a₀ > 0` such that for every asymmetric torus lattice
with `Ns·a = Ls`, `a ≤ a₀` and `Nt·a ≥ L₀`, and every lattice test vector `G`,

  `∫ (ω G)² dμ_int ≤ C · ∫ (ω G)² dμ_free`.

This is the B2 bound in the thresholded (eventual) form pinned in
`planning/b2-stageB-holes-spec.md` §"C4 design": the constant is uniform over the whole
`(Nt, Ns, a)` family above the thresholds, which is all any downstream consumer
(`Lt → ∞` IR limit, `a → 0` UV limit) uses.

## Assembly

Fix `τ := 1` and `κ := min mass (4/Ls)`, so `κ² ≤ 16/Ls² ≤ spatialGap Ns a` (Stage A A6;
`Ns ≥ 2` is forced by `a₀ ≤ Ls/2`).  Split `G` by the spectral projections onto
`S_low = {k : λ_k < mass² + κ²}` and its complement (S4), and use `(x+y)² ≤ 2x² + 2y²`
under the interacting integral:

* **high branch** — the FSS infrared consumer `asymHighModes_variance_le_freeVariance`
  gives `Var_int(P_high G) ≤ (1 + mass²/κ²)·Var_free(P_high G)`;
* **low branch** — `P_low G` is slice-constant (Stage A A5) and temporally band-limited
  (C1); chain B3 (`interacting_second_moment_eq_pathMeasure`) → B-I in the sharp uniform
  τ-form (`asymSliceFamily_pathMeasure_second_moment_le_fixedLs_sharp_uniform`, `hInt`
  discharged by C2) → B5b (`groundVariance_sum_le_freeCovariance_sum`) → B-II per-instance
  (`freeSingleSliceCovarianceSum_le_freeVariance_of_band_sharp`).

The a-ledger of the low branch (the Stage-C crux): with `γ = e^{-m₀a}` and `m₀a ≤ 1`,
`1 - γ ≥ m₀a/2` (elementary convexity bound `e^{-x} ≤ 1 - x/2` on `[0,1]`), so
`(2/(1-γ))·(2a/m)` loses its `1/a` against the spare `a` of B-II and
`(2/(1-γ))·4/(Nt·m²) ≤ 16/(m₀m²·Lt)` is controlled by the threshold `Lt ≥ L₀`; the
remainder `C_rem·Nt·γ^(Nt-⌈τ/a⌉)` is damped by `Lt·e^{-m₀(Lt-τ-1/m₀)} ≤ 2/m₀` for
`Lt ≥ L₀ := 2(τ + 1/m₀)` (crude `y ≤ e^y`).  All resulting constants depend only on
`(P, mass, Ls)`.

Free-side reassembly is exact (S4 additivity `asymFreeVariance_proj_add`), and
`C := 2·max(C_high, C_low)`.
-/

noncomputable section

open MeasureTheory GaussianField
open scoped BigOperators

namespace Pphi2

/-! ## Elementary exponential bounds for the a-ledger -/

/-- Convexity-type bound `e^{-x} ≤ 1 - x/2` on `[0, 1]`, via `1 + x ≤ e^x`. -/
theorem exp_neg_le_one_sub_half {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-x) ≤ 1 - x / 2 := by
  have h1x : (0 : ℝ) < 1 + x := by linarith
  have hle : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hinv : Real.exp (-x) ≤ (1 + x)⁻¹ := by
    rw [Real.exp_neg, inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le h1x hle
  have h2 : (1 + x)⁻¹ ≤ 1 - x / 2 := by
    rw [inv_eq_one_div, div_le_iff₀ h1x]
    nlinarith
  linarith

/-- The uniform-damping bound `Lt · e^{-m₀(Lt - c)} ≤ 2/m₀` for `Lt ≥ 2c`, via the
crude estimate `y ≤ e^y`. -/
theorem mul_exp_neg_mul_sub_le {m₀ c Lt : ℝ} (hm₀ : 0 < m₀) (hc : 0 < c)
    (hLt : 2 * c ≤ Lt) :
    Lt * Real.exp (-(m₀ * (Lt - c))) ≤ 2 / m₀ := by
  have hLc : 0 < Lt - c := by linarith
  have hy : 0 < m₀ * (Lt - c) := mul_pos hm₀ hLc
  have hyexp : m₀ * (Lt - c) ≤ Real.exp (m₀ * (Lt - c)) := by
    linarith [Real.add_one_le_exp (m₀ * (Lt - c))]
  have hexp : Real.exp (-(m₀ * (Lt - c))) ≤ (m₀ * (Lt - c))⁻¹ := by
    rw [Real.exp_neg, inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hy hyexp
  have hLt0 : 0 ≤ Lt := by linarith
  calc Lt * Real.exp (-(m₀ * (Lt - c))) ≤ Lt * (m₀ * (Lt - c))⁻¹ :=
        mul_le_mul_of_nonneg_left hexp hLt0
    _ ≤ 2 / m₀ := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ hy hm₀]
        nlinarith [mul_nonneg hm₀.le (by linarith : (0 : ℝ) ≤ Lt - 2 * c)]

/-! ## The Stage-C master theorem -/

set_option maxHeartbeats 1600000 in
/-- **B2, thresholded form (Stage C master assembly).** Restricted to
`P.n = 4` because the high branch consumes `fss_infrared_quadratic`. At fixed spatial circumference
`Ls = Ns·a`, there are constants `C, L₀, a₀ > 0` — depending only on `(P, mass, Ls)` —
such that for every asymmetric torus lattice with `Ns·a = Ls`, spacing `a ≤ a₀` and
temporal extent `Nt·a ≥ L₀`, the second moment of every lattice pairing under the
interacting measure is bounded by `C` times its Gaussian (free) second moment. -/
theorem asymInteractingVariance_le_freeVariance_lattice_thresholded
    (P : InteractionPolynomial) (hP : P.n = 4) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) (hLs : 0 < Ls) :
    ∃ C L₀ a₀ : ℝ, 0 < C ∧ 0 < L₀ ∧ 0 < a₀ ∧
      ∀ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Ns : ℝ) * a = Ls → a ≤ a₀ → L₀ ≤ (Nt : ℝ) * a →
        ∀ (G : AsymLatticeField Nt Ns),
          ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω G) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
          C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω G) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  classical
  -- The band threshold κ: κ² ≤ 16/Ls² keeps the low modes below the spatial gap.
  set κ : ℝ := min mass (4 / Ls) with hκ_def
  have hκ : 0 < κ := lt_min hmass (by positivity)
  -- Hole B-I, sharp uniform τ-form at τ := 1 (through S2 and the τ-form bridge axioms).
  obtain ⟨m₀, hm₀, a₁, ha₁, C_rem, hCrem, hSharp⟩ :=
    asymSliceFamily_pathMeasure_second_moment_le_fixedLs_sharp_uniform
      P mass hmass Ls hLs 1 one_pos
  -- The B5b constant.
  set C_B5b : ℝ := groundVarianceFreeCovarianceConstant P mass hmass Ls hLs with hB5b_def
  have hC_B5b : 0 < C_B5b := groundVarianceFreeCovarianceConstant_pos P mass hmass Ls hLs
  -- Thresholds and headline constants.
  set L₀ : ℝ := 2 + 2 / m₀ with hL₀_def
  have hL₀ : 0 < L₀ := by positivity
  set a₀ : ℝ := min a₁ (min (Ls / 2) (1 / m₀)) with ha₀_def
  have ha₀ : 0 < a₀ := lt_min ha₁ (lt_min (by positivity) (by positivity))
  set C_high : ℝ := 1 + mass ^ 2 / κ ^ 2 with hCh_def
  have hC_high : 0 < C_high := by positivity
  set C_low : ℝ := C_B5b * ((κ ^ 2 + mass ^ 2) *
    (16 / (m₀ * mass ^ 2 * L₀) + 8 / (m₀ * mass) +
      4 * C_rem / mass ^ 2 + 4 * C_rem / (m₀ * mass))) with hCl_def
  have hC_low : 0 ≤ C_low := by
    have h1 : (0 : ℝ) ≤ 16 / (m₀ * mass ^ 2 * L₀) := by positivity
    have h2 : (0 : ℝ) ≤ 8 / (m₀ * mass) := by positivity
    have h3 : (0 : ℝ) ≤ 4 * C_rem / mass ^ 2 := div_nonneg (by linarith) (by positivity)
    have h4 : (0 : ℝ) ≤ 4 * C_rem / (m₀ * mass) := div_nonneg (by linarith) (by positivity)
    have hκm : (0 : ℝ) ≤ κ ^ 2 + mass ^ 2 := by positivity
    exact mul_nonneg hC_B5b.le (mul_nonneg hκm (by linarith))
  refine ⟨2 * max C_high C_low, L₀, a₀, ?_, hL₀, ha₀, ?_⟩
  · have := lt_of_lt_of_le hC_high (le_max_left C_high C_low)
    linarith
  intro Nt Ns _ _ a ha hLsa haa hLta G
  -- Unpack the spacing threshold.
  have haa₁ : a ≤ a₁ := haa.trans (min_le_left _ _)
  have haLs2 : a ≤ Ls / 2 := haa.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ham₀ : a ≤ 1 / m₀ := haa.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hNtR : (0 : ℝ) < (Nt : ℝ) := Nat.cast_pos.mpr (NeZero.pos Nt)
  -- Ns ≥ 2 (so the spatial-gap lower bound applies).
  have hNs2 : 2 ≤ Ns := by
    have h2a : 2 * a ≤ Ls := by linarith
    have hcast : (2 : ℝ) ≤ (Ns : ℝ) := by nlinarith [hLsa]
    exact_mod_cast hcast
  -- κ² sits below the spatial gap.
  have hκgap : κ ^ 2 ≤ spatialGap Ns a := by
    have hκ4 : κ ≤ 4 / Ls := min_le_right _ _
    have hκsq : κ ^ 2 ≤ 16 / Ls ^ 2 := by
      calc κ ^ 2 ≤ (4 / Ls) ^ 2 := pow_le_pow_left₀ hκ.le hκ4 2
        _ = 16 / Ls ^ 2 := by rw [div_pow]; norm_num
    exact hκsq.trans (spatialGap_ge_sixteen_of_fixed_Ls Ns a Ls ha hLsa hNs2)
  -- The τ-window fits: 2τ = 2 ≤ L₀ ≤ Lt.
  have h2τ : 2 * 1 ≤ (Nt : ℝ) * a := by
    have h2L : (2 : ℝ) ≤ L₀ := by
      rw [hL₀_def]
      have : (0 : ℝ) < 2 / m₀ := by positivity
      linarith
    linarith
  -- The mode split at mass² + κ².
  set Slow : Finset (AsymLatticeSites Nt Ns) :=
    Finset.univ.filter
      (fun k => massEigenvaluesAsym Nt Ns a mass k < mass ^ 2 + κ ^ 2) with hSlow_def
  have hSlow : ∀ k ∈ Slow, massEigenvaluesAsym Nt Ns a mass k < mass ^ 2 + κ ^ 2 := by
    intro k hk
    rw [hSlow_def, Finset.mem_filter] at hk
    exact hk.2
  have hShigh : ∀ k ∈ Slowᶜ, mass ^ 2 + κ ^ 2 ≤ massEigenvaluesAsym Nt Ns a mass k := by
    intro k hk
    have hnot := Finset.mem_compl.mp hk
    rw [hSlow_def, Finset.mem_filter] at hnot
    exact le_of_not_gt fun hlt => hnot ⟨Finset.mem_univ k, hlt⟩
  set Gl : AsymLatticeField Nt Ns := asymModeProj Nt Ns a mass Slow G with hGl_def
  set Gh : AsymLatticeField Nt Ns := asymModeProj Nt Ns a mass Slowᶜ G with hGh_def
  have hsplit : Gl + Gh = G := asymModeProj_add_compl Nt Ns a mass Slow G
  -- Interacting-side integrability of the pieces.
  have hIl : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) => (ω Gl) ^ 2)
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) :=
    asymInteractingLattice_pairing_sq_integrable (Nt := Nt) (Ns := Ns) P a mass ha hmass Gl
  have hIh : Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) => (ω Gh) ^ 2)
      (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) :=
    asymInteractingLattice_pairing_sq_integrable (Nt := Nt) (Ns := Ns) P a mass ha hmass Gh
  -- The (x+y)² ≤ 2x² + 2y² split under the interacting integral.
  have hVarSplit : ∫ ω : Configuration (AsymLatticeField Nt Ns),
      (ω G) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
      2 * ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω Gl) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) +
      2 * ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω Gh) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) := by
    have hsq : ∀ ω : Configuration (AsymLatticeField Nt Ns),
        (ω G) ^ 2 ≤ 2 * (ω Gl) ^ 2 + 2 * (ω Gh) ^ 2 := by
      intro ω
      have h : ω G = ω Gl + ω Gh := by rw [← hsplit, map_add]
      rw [h]
      nlinarith [sq_nonneg (ω Gl - ω Gh)]
    have hle := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun ω : Configuration (AsymLatticeField Nt Ns) =>
        sq_nonneg (ω G))
      (show Integrable (fun ω : Configuration (AsymLatticeField Nt Ns) =>
          2 * (ω Gl) ^ 2 + 2 * (ω Gh) ^ 2)
          (interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) from
        (hIl.const_mul 2).add (hIh.const_mul 2))
      (Filter.Eventually.of_forall hsq)
    rwa [integral_add (hIl.const_mul 2) (hIh.const_mul 2),
      integral_const_mul, integral_const_mul] at hle
  -- HIGH branch: the FSS infrared consumer.
  have hHighChain : ∫ ω : Configuration (AsymLatticeField Nt Ns),
      (ω Gh) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
      C_high * ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω Gh) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) :=
    asymHighModes_variance_le_freeVariance Nt Ns P hP a mass ha hmass κ hκ Slowᶜ hShigh G
  -- LOW branch, step 1: slice-constancy and band-limitedness of the low projection.
  have hsc : sliceConstant Nt Ns Gl := by
    intro t s s'
    exact asymModeProj_sliceConstant Nt Ns a mass ha hmass Slow
      (fun k hk => lt_of_lt_of_le (hSlow k hk) (by linarith)) G t s s'
  have hband : temporalBandLimited Nt Ns a κ Gl :=
    asymModeProj_temporalBandLimited Nt Ns a mass κ ha hmass hκgap Slow hSlow G
  -- LOW branch, step 2: B3 rewrites the interacting second moment over the path measure,
  -- in the slice-family coordinates g := asymSliceEquiv Gl.
  set g : ZMod Nt → SpatialField Ns := asymSliceEquiv Nt Ns Gl with hg_def
  have hgsymm : (asymSliceEquiv Nt Ns).symm g = Gl := by
    rw [hg_def]
    exact (asymSliceEquiv Nt Ns).symm_apply_apply Gl
  have hpair : ∀ ψ : ZMod Nt → SpatialField Ns,
      slicePairing Nt Ns Gl ψ = asymSliceFamilyLinear g ψ := by
    intro ψ
    rw [asymSliceFamilyLinear_eq_slicePairing, hgsymm]
  have hB3' : ∫ ω : Configuration (AsymLatticeField Nt Ns),
      (ω Gl) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) =
      ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
        ∂((asymTransferSystem Nt Ns P a mass ha hmass).pathMeasure Nt) := by
    rw [interacting_second_moment_eq_pathMeasure Nt Ns P a mass ha hmass Gl]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ψ => by
      show slicePairing Nt Ns Gl ψ ^ 2 = asymSliceFamilyLinear g ψ ^ 2
      rw [hpair ψ])
  -- LOW branch, step 3: B-I sharp uniform (hInt discharged by C2).
  have hInt := asymGroundVector_sliceObs_sq_integrable_family Nt Ns P a mass ha hmass g
  have hLow1 := hSharp Nt Ns a ha hLsa haa₁ h2τ g hInt
  -- LOW branch, step 4: B5b and B-II.
  have hB5b : groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g ≤
      C_B5b * freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass g :=
    groundVariance_sum_le_freeCovariance_sum (Nt := Nt) (Ns := Ns)
      P mass hmass Ls hLs a ha hLsa g
  have hBII : freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass g ≤
      ((κ ^ 2 + mass ^ 2) * (4 / ((Nt : ℝ) * mass ^ 2) + 2 * a / mass)) *
        ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω Gl) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
    have h := freeSingleSliceCovarianceSum_le_freeVariance_of_band_sharp
      Nt Ns a mass ha hmass κ Gl hsc hband
    rwa [← hg_def] at h
  -- The a-ledger: bound the composed low-branch coefficient uniformly.
  have hx : 0 < m₀ * a := mul_pos hm₀ ha
  have hx1 : m₀ * a ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left ham₀ hm₀.le
    rwa [mul_one_div, div_self hm₀.ne'] at h
  have hγlt1 : Real.exp (-(m₀ * a)) < 1 := by
    have h1 : Real.exp (-(m₀ * a)) < Real.exp 0 := Real.exp_lt_exp.mpr (by nlinarith)
    simpa using h1
  have h1γ : (m₀ * a) / 2 ≤ 1 - Real.exp (-(m₀ * a)) := by
    linarith [exp_neg_le_one_sub_half hx.le hx1]
  have h1γpos : 0 < 1 - Real.exp (-(m₀ * a)) := by linarith
  have h2γ : 2 / (1 - Real.exp (-(m₀ * a))) ≤ 4 / (m₀ * a) := by
    rw [div_le_div_iff₀ h1γpos hx]
    linarith
  -- Damping of the remainder exponent: Lt·γ^(Nt-⌈1/a⌉) ≤ 2/m₀.
  have hcpos : (0 : ℝ) < 1 + 1 / m₀ := by positivity
  have hceil : (Nat.ceil (1 / a) : ℝ) * a ≤ 1 + 1 / m₀ := by
    have h := (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 1 / a)).le
    have h2 : (Nat.ceil (1 / a) : ℝ) * a ≤ (1 / a + 1) * a :=
      mul_le_mul_of_nonneg_right h ha.le
    have h3 : (1 / a + 1) * a = 1 + a := by field_simp
    linarith
  have hL2c : L₀ = 2 * (1 + 1 / m₀) := by rw [hL₀_def]; ring
  have hceil_lt : Nat.ceil (1 / a) < Nt := by
    have h1 : (Nat.ceil (1 / a) : ℝ) * a < (Nt : ℝ) * a := by
      calc (Nat.ceil (1 / a) : ℝ) * a ≤ 1 + 1 / m₀ := hceil
        _ < 2 * (1 + 1 / m₀) := by linarith
        _ = L₀ := hL2c.symm
        _ ≤ (Nt : ℝ) * a := hLta
    have h2 : (Nat.ceil (1 / a) : ℝ) < (Nt : ℝ) := lt_of_mul_lt_mul_right h1 ha.le
    exact_mod_cast h2
  have hexpcast : ((Nt - Nat.ceil (1 / a) : ℕ) : ℝ) =
      (Nt : ℝ) - (Nat.ceil (1 / a) : ℝ) := by
    exact_mod_cast Nat.cast_sub hceil_lt.le
  have hEbound : Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a)) ≤
      Real.exp (-(m₀ * ((Nt : ℝ) * a - (1 + 1 / m₀)))) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [hexpcast]
    nlinarith [mul_le_mul_of_nonneg_left hceil hm₀.le]
  have hE1 : Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a)) ≤ 1 :=
    pow_le_one₀ (Real.exp_pos _).le hγlt1.le
  have hE0 : (0 : ℝ) ≤ Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a)) :=
    pow_nonneg (Real.exp_pos _).le _
  have hLtE : (Nt : ℝ) * a * Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a)) ≤ 2 / m₀ := by
    have h1 : (Nt : ℝ) * a * Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a)) ≤
        (Nt : ℝ) * a * Real.exp (-(m₀ * ((Nt : ℝ) * a - (1 + 1 / m₀)))) :=
      mul_le_mul_of_nonneg_left hEbound (by positivity)
    refine h1.trans (mul_exp_neg_mul_sub_le hm₀ hcpos ?_)
    rw [← hL2c]
    exact hLta
  -- The composed low-branch coefficient.
  set F₁ : ℝ := 2 / (1 - Real.exp (-(m₀ * a))) +
    C_rem * Nt * Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a)) with hF₁_def
  have hF₁ : 0 ≤ F₁ := by
    have h2 : 0 ≤ 2 / (1 - Real.exp (-(m₀ * a))) := div_nonneg (by norm_num) h1γpos.le
    have h3 : 0 ≤ C_rem * Nt * Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a)) :=
      mul_nonneg (mul_nonneg hCrem hNtR.le) hE0
    rw [hF₁_def]
    linarith
  have hcoeff : F₁ * ((κ ^ 2 + mass ^ 2) * (4 / ((Nt : ℝ) * mass ^ 2) + 2 * a / mass)) ≤
      (κ ^ 2 + mass ^ 2) *
        (16 / (m₀ * mass ^ 2 * L₀) + 8 / (m₀ * mass) +
          4 * C_rem / mass ^ 2 + 4 * C_rem / (m₀ * mass)) := by
    have hκm : (0 : ℝ) ≤ κ ^ 2 + mass ^ 2 := by positivity
    have hmain : F₁ * (4 / ((Nt : ℝ) * mass ^ 2) + 2 * a / mass) ≤
        16 / (m₀ * mass ^ 2 * L₀) + 8 / (m₀ * mass) +
          4 * C_rem / mass ^ 2 + 4 * C_rem / (m₀ * mass) := by
      -- piece A: the zero-mode term against the temporal threshold
      have hA : 2 / (1 - Real.exp (-(m₀ * a))) * (4 / ((Nt : ℝ) * mass ^ 2)) ≤
          16 / (m₀ * mass ^ 2 * L₀) := by
        have h1 : 2 / (1 - Real.exp (-(m₀ * a))) * (4 / ((Nt : ℝ) * mass ^ 2)) ≤
            4 / (m₀ * a) * (4 / ((Nt : ℝ) * mass ^ 2)) :=
          mul_le_mul_of_nonneg_right h2γ (by positivity)
        have h2 : 4 / (m₀ * a) * (4 / ((Nt : ℝ) * mass ^ 2)) =
            16 / (m₀ * mass ^ 2 * ((Nt : ℝ) * a)) := by
          field_simp
          ring
        have h3 : 16 / (m₀ * mass ^ 2 * ((Nt : ℝ) * a)) ≤ 16 / (m₀ * mass ^ 2 * L₀) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hLta
            (by positivity : (0 : ℝ) ≤ 16 * (m₀ * mass ^ 2))]
        calc 2 / (1 - Real.exp (-(m₀ * a))) * (4 / ((Nt : ℝ) * mass ^ 2))
            ≤ 4 / (m₀ * a) * (4 / ((Nt : ℝ) * mass ^ 2)) := h1
          _ = 16 / (m₀ * mass ^ 2 * ((Nt : ℝ) * a)) := h2
          _ ≤ 16 / (m₀ * mass ^ 2 * L₀) := h3
      -- piece B: the spare a of B-II cancels the 1/a of the susceptibility prefactor
      have hB : 2 / (1 - Real.exp (-(m₀ * a))) * (2 * a / mass) ≤ 8 / (m₀ * mass) := by
        have h1 : 2 / (1 - Real.exp (-(m₀ * a))) * (2 * a / mass) ≤
            4 / (m₀ * a) * (2 * a / mass) :=
          mul_le_mul_of_nonneg_right h2γ (by positivity)
        have h2 : 4 / (m₀ * a) * (2 * a / mass) = 8 / (m₀ * mass) := by
          field_simp
          ring
        linarith
      -- piece C: the remainder against the zero-mode term (Nt cancels)
      have hC' : C_rem * Nt * Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a)) *
          (4 / ((Nt : ℝ) * mass ^ 2)) ≤ 4 * C_rem / mass ^ 2 := by
        have heq : C_rem * Nt * Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a)) *
            (4 / ((Nt : ℝ) * mass ^ 2)) =
            (4 * C_rem / mass ^ 2) *
              Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a)) := by
          field_simp
        rw [heq]
        have hnn : (0 : ℝ) ≤ 4 * C_rem / mass ^ 2 :=
          div_nonneg (by linarith) (by positivity)
        calc (4 * C_rem / mass ^ 2) * Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a))
            ≤ (4 * C_rem / mass ^ 2) * 1 := mul_le_mul_of_nonneg_left hE1 hnn
          _ = 4 * C_rem / mass ^ 2 := mul_one _
      -- piece D: the remainder against the spare a (Lt·γ^† damping)
      have hD : C_rem * Nt * Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a)) *
          (2 * a / mass) ≤ 4 * C_rem / (m₀ * mass) := by
        have heq : C_rem * Nt * Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a)) *
            (2 * a / mass) =
            (C_rem * (2 / mass)) *
              ((Nt : ℝ) * a * Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a))) := by
          ring
        rw [heq]
        have hnn : (0 : ℝ) ≤ C_rem * (2 / mass) := mul_nonneg hCrem (by positivity)
        calc (C_rem * (2 / mass)) *
              ((Nt : ℝ) * a * Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a)))
            ≤ (C_rem * (2 / mass)) * (2 / m₀) := mul_le_mul_of_nonneg_left hLtE hnn
          _ = 4 * C_rem / (m₀ * mass) := by
              field_simp
              ring
      calc F₁ * (4 / ((Nt : ℝ) * mass ^ 2) + 2 * a / mass)
          = 2 / (1 - Real.exp (-(m₀ * a))) * (4 / ((Nt : ℝ) * mass ^ 2)) +
            2 / (1 - Real.exp (-(m₀ * a))) * (2 * a / mass) +
            C_rem * Nt * Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a)) *
              (4 / ((Nt : ℝ) * mass ^ 2)) +
            C_rem * Nt * Real.exp (-(m₀ * a)) ^ (Nt - Nat.ceil (1 / a)) *
              (2 * a / mass) := by
            rw [hF₁_def]
            ring
        _ ≤ 16 / (m₀ * mass ^ 2 * L₀) + 8 / (m₀ * mass) +
            4 * C_rem / mass ^ 2 + 4 * C_rem / (m₀ * mass) := by linarith
    calc F₁ * ((κ ^ 2 + mass ^ 2) * (4 / ((Nt : ℝ) * mass ^ 2) + 2 * a / mass))
        = (κ ^ 2 + mass ^ 2) * (F₁ * (4 / ((Nt : ℝ) * mass ^ 2) + 2 * a / mass)) := by
          ring
      _ ≤ (κ ^ 2 + mass ^ 2) *
            (16 / (m₀ * mass ^ 2 * L₀) + 8 / (m₀ * mass) +
              4 * C_rem / mass ^ 2 + 4 * C_rem / (m₀ * mass)) :=
          mul_le_mul_of_nonneg_left hmain hκm
  -- LOW branch chain: interacting ≤ C_low · free for the low projection.
  have hVfl : (0 : ℝ) ≤ ∫ ω : Configuration (AsymLatticeField Nt Ns),
      (ω Gl) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) :=
    integral_nonneg fun ω => sq_nonneg _
  have hLowChain : ∫ ω : Configuration (AsymLatticeField Nt Ns),
      (ω Gl) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) ≤
      C_low * ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω Gl) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
    rw [hB3']
    calc ∫ ψ : ZMod Nt → SpatialField Ns, (asymSliceFamilyLinear g ψ) ^ 2
          ∂((asymTransferSystem Nt Ns P a mass ha hmass).pathMeasure Nt)
        ≤ F₁ * groundSliceVarianceSum (Nt := Nt) (Ns := Ns) P a mass ha hmass g := hLow1
      _ ≤ F₁ * (C_B5b *
            freeSingleSliceCovarianceSum (Nt := Nt) (Ns := Ns) a mass ha hmass g) :=
          mul_le_mul_of_nonneg_left hB5b hF₁
      _ ≤ F₁ * (C_B5b *
            (((κ ^ 2 + mass ^ 2) * (4 / ((Nt : ℝ) * mass ^ 2) + 2 * a / mass)) *
              ∫ ω : Configuration (AsymLatticeField Nt Ns),
                (ω Gl) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBII hC_B5b.le) hF₁
      _ = C_B5b *
            (F₁ * ((κ ^ 2 + mass ^ 2) * (4 / ((Nt : ℝ) * mass ^ 2) + 2 * a / mass))) *
            ∫ ω : Configuration (AsymLatticeField Nt Ns),
              (ω Gl) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
          ring
      _ ≤ C_B5b * ((κ ^ 2 + mass ^ 2) *
            (16 / (m₀ * mass ^ 2 * L₀) + 8 / (m₀ * mass) +
              4 * C_rem / mass ^ 2 + 4 * C_rem / (m₀ * mass))) *
            ∫ ω : Configuration (AsymLatticeField Nt Ns),
              (ω Gl) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcoeff hC_B5b.le) hVfl
      _ = C_low * ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω Gl) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
          rw [hCl_def]
  -- Final reassembly: exact free-side additivity across the mode split.
  have hVfh : (0 : ℝ) ≤ ∫ ω : Configuration (AsymLatticeField Nt Ns),
      (ω Gh) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) :=
    integral_nonneg fun ω => sq_nonneg _
  have hVadd : (∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω Gl) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) +
      (∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω Gh) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) =
      ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω G) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) :=
    asymFreeVariance_proj_add Nt Ns a mass ha hmass Slow G
  have hmaxl : C_low ≤ max C_high C_low := le_max_right _ _
  have hmaxh : C_high ≤ max C_high C_low := le_max_left _ _
  calc ∫ ω : Configuration (AsymLatticeField Nt Ns),
        (ω G) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass)
      ≤ 2 * ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω Gl) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) +
        2 * ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω Gh) ^ 2 ∂(interactingLatticeMeasureAsym Nt Ns P a mass ha hmass) :=
        hVarSplit
    _ ≤ 2 * (C_low * ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω Gl) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) +
        2 * (C_high * ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω Gh) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) := by
        linarith
    _ ≤ 2 * (max C_high C_low * ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω Gl) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) +
        2 * (max C_high C_low * ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω Gh) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) := by
        have h1 := mul_le_mul_of_nonneg_right hmaxl hVfl
        have h2 := mul_le_mul_of_nonneg_right hmaxh hVfh
        linarith
    _ = 2 * max C_high C_low *
          ((∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω Gl) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass)) +
          (∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω Gh) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass))) := by
        ring
    _ = 2 * max C_high C_low * ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (ω G) ^ 2 ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
        rw [hVadd]

/-! ## Torus-level thresholded assembly (Piece-5 migration) -/

/-- **B2 torus assembly, thresholded form.** This inherits `P.n = 4` from
the lattice master theorem. The torus variance bound in the thresholded
(eventual) quantifier structure: there are `C, L₀, a₀ > 0` — depending only on
`(P, mass, Ls)` — such that for every asymmetric torus with `Nt·a = Lt ≥ L₀`, `Ns·a = Ls`,
`a ≤ a₀`, and every torus test function `f`, the interacting second moment of the torus
pairing is bounded by `C` times the free lattice second moment of the pulled-back pairing.

Proved from the Stage-C lattice master theorem
`asymInteractingVariance_le_freeVariance_lattice_thresholded` by the same Piece-5
pushforward + pairing argument as `asymInteractingVariance_le_freeVariance_Lt_uniform`
(push the torus interacting measure back along `asymTorusEmbedLiftIso` and rewrite the
torus pairing as the lattice pairing against `asymLatticeTestFnIso`), but consuming the
proved lattice **theorem** instead of the legacy all-`(Lt, a)` axiom
`asymInteractingVariance_le_freeVariance_lattice_Lt_uniform`. Downstream consumers should
migrate to this form (planning/b2-stageB-holes-spec.md §C4 design). -/
theorem asymInteractingVariance_le_freeVariance_torus_thresholded
    (P : InteractionPolynomial) (hP : P.n = 4) (mass : ℝ) (hmass : 0 < mass)
    (Ls : ℝ) [Fact (0 < Ls)] :
    ∃ C L₀ a₀ : ℝ, 0 < C ∧ 0 < L₀ ∧ 0 < a₀ ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)]
        (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) (ha : 0 < a),
        (Nt : ℝ) * a = Lt → (Ns : ℝ) * a = Ls → a ≤ a₀ → L₀ ≤ Lt →
        ∀ (f : AsymTorusTestFunction Lt Ls),
          ∫ ω : Configuration (AsymTorusTestFunction Lt Ls), (ω f) ^ 2
            ∂(asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass) ≤
          C * ∫ ω : Configuration (AsymLatticeField Nt Ns),
            (ω (asymLatticeTestFnIso Lt Ls Nt Ns a f)) ^ 2
              ∂(latticeGaussianMeasureAsym Nt Ns a mass ha hmass) := by
  obtain ⟨C, L₀, a₀, hC_pos, hL₀, ha₀, hC_bound⟩ :=
    asymInteractingVariance_le_freeVariance_lattice_thresholded P hP mass hmass Ls Fact.out
  refine ⟨C, L₀, a₀, hC_pos, hL₀, ha₀, ?_⟩
  intro Lt _hLt Nt Ns _ _ a ha hvolt hvols haa hLta f
  have hLta' : L₀ ≤ (Nt : ℝ) * a := by rw [hvolt]; exact hLta
  set g := asymLatticeTestFnIso Lt Ls Nt Ns a f
  set μ_int_T := asymTorusInteractingMeasureIso Lt Ls Nt Ns a P mass ha hmass
  set μ_int_L := interactingLatticeMeasureAsym Nt Ns P a mass ha hmass
  have hι_meas : Measurable (asymTorusEmbedLiftIso Lt Ls Nt Ns a) :=
    asymTorusEmbedLiftIso_measurable Lt Ls Nt Ns a
  have h_eval : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      (asymTorusEmbedLiftIso Lt Ls Nt Ns a ω) f = ω g :=
    asymTorusEmbedLiftIso_eval_eq Lt Ls Nt Ns a f
  have h_pushforward : μ_int_T =
      Measure.map (asymTorusEmbedLiftIso Lt Ls Nt Ns a) μ_int_L := rfl
  have h_F_sq_meas :
      AEStronglyMeasurable (fun ω : Configuration (AsymTorusTestFunction Lt Ls) =>
        (ω f) ^ 2) μ_int_T :=
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
  rw [h_pushforward]
  rw [integral_map hι_meas.aemeasurable h_F_sq_meas]
  have h_integrand :
      ∫ ω : Configuration (AsymLatticeField Nt Ns),
          (asymTorusEmbedLiftIso Lt Ls Nt Ns a ω f) ^ 2 ∂μ_int_L =
        ∫ ω : Configuration (AsymLatticeField Nt Ns), (ω g) ^ 2 ∂μ_int_L := by
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun ω => ?_
    simpa using congrArg (fun x : ℝ => x ^ 2) (h_eval ω)
  rw [h_integrand]
  exact hC_bound Nt Ns a ha hvols haa hLta' g

end Pphi2

end
