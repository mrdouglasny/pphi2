/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.U4Derivative
import Pphi2.TorusContinuumLimit.TorusInteractingLimit
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Integral

/-!
# Uniform-in-N building blocks for the weak-coupling discharge

Foundational facts for the `N`-uniform remainder bound that closes
`torus_weakCoupling_lattice_connectedFourPoint_strictNeg` (see
`planning/uniform-remainder-roadmap.md`). This file starts with the **fixed-volume identity**: on the
torus the lattice spacing `a = L/N`, so the lattice "volume" `a^d · #sites = (a·N)^d` is `L^d`,
**independent of `N`**. This is the structural reason the fixed torus is uniformly controllable where
infinite volume is not.
-/

namespace Pphi2

open MeasureTheory GaussianField

/-- The number of lattice sites is `N^d`. -/
@[simp] lemma latticeSites_card (d N : ℕ) [NeZero N] :
    Fintype.card (FinLatticeSites d N) = N ^ d := by
  simp [FinLatticeSites, Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- **Fixed-volume identity.** `a^d · #sites = (a·N)^d`. With the torus spacing `a = L/N` this is
`L^d`, uniform in `N`. -/
lemma lattice_volume_eq (d N : ℕ) [NeZero N] (a : ℝ) :
    a ^ d * (Fintype.card (FinLatticeSites d N) : ℝ) = (a * N) ^ d := by
  rw [latticeSites_card]; push_cast; rw [mul_pow]

/-- **Torus volume is `L^d`, uniform in `N`.** The lattice volume `(circleSpacing L N)^d · #sites`
equals `L^d` for every `N`. -/
lemma torus_volume_eq (L : ℝ) [Fact (0 < L)] (d N : ℕ) [NeZero N] :
    (circleSpacing L N) ^ d * (Fintype.card (FinLatticeSites d N) : ℝ) = L ^ d := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [lattice_volume_eq, circleSpacing_eq]
  field_simp

/-! ## Partition-function lower bound `Z_t ≥ 1` (corrected L4 foundation) -/

/-- **`⟨V⟩₀ ≤ 0`.** The free-field mean of the interaction is nonpositive: each site contributes the
constant Wick coefficient `P.coeff₀ ≤ 0` (`coeff_zero_nonpos`), so
`∫ V dμ_GFF = a^d·#sites·P.coeff₀ ≤ 0`. -/
lemma interactionFunctional_integral_nonpos (d N : ℕ) [NeZero N]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    ∫ ω, interactionFunctional d N P a mass ω
      ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ 0 := by
  have key : ∫ ω, interactionFunctional d N P a mass ω
        ∂(latticeGaussianMeasure d N a mass ha hmass)
      = a ^ d * ((Fintype.card (FinLatticeSites d N) : ℝ) *
          P.coeff ⟨0, by have := P.hn_ge; omega⟩) := by
    simp only [interactionFunctional]
    rw [integral_const_mul, integral_finset_sum _
      (fun z _ => (wickPolynomial_integral_eq_coeff_zero d N P a mass ha hmass z).1)]
    rw [show (∑ z : FinLatticeSites d N, ∫ ω, wickPolynomial P (wickConstant d N a mass)
          (ω (finLatticeDelta d N z)) ∂(latticeGaussianMeasure d N a mass ha hmass))
        = ∑ _z : FinLatticeSites d N, P.coeff ⟨0, by have := P.hn_ge; omega⟩ from
      Finset.sum_congr rfl fun z _ =>
        (wickPolynomial_integral_eq_coeff_zero d N P a mass ha hmass z).2,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [key]
  exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ha.le d)
    (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) P.coeff_zero_nonpos)

/-- **Partition-function lower bound, uniform `c = 1`.** For every coupling `t ≥ 0`,
`Z_t = ∫ e^{-t V} dμ_GFF ≥ 1`. Proof: `e^{-tV} ≥ 1 - tV` (convexity) and `∫(1 - tV) = 1 - t⟨V⟩₀ ≥ 1`
since `⟨V⟩₀ ≤ 0`. (No Wick-constant divergence — this is the `Z_t ≥ 1` brick the corrected L4 uses in
place of the false pointwise `V ≥ -B`.) -/
lemma partitionFn_ge_one (d N : ℕ) [NeZero N]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    {t : ℝ} (ht : 0 ≤ t) :
    (1 : ℝ) ≤ ∫ ω, Real.exp (-(t * interactionFunctional d N P a mass ω))
      ∂(latticeGaussianMeasure d N a mass ha hmass) := by
  set μ := latticeGaussianMeasure d N a mass ha hmass with hμ
  set V := interactionFunctional d N P a mass with hV
  haveI : IsProbabilityMeasure μ := latticeGaussianMeasure_isProbability d N a mass ha hmass
  have hVmeas : Measurable V := interactionFunctional_measurable d N P a mass
  have hVint : Integrable V μ := by
    rw [hV]; unfold interactionFunctional
    exact (integrable_finset_sum _ (fun z _ =>
      (wickPolynomial_integral_eq_coeff_zero d N P a mass ha hmass z).1)).const_mul _
  have hVnonpos : ∫ ω, V ω ∂μ ≤ 0 := interactionFunctional_integral_nonpos d N P a mass ha hmass
  obtain ⟨B, hB⟩ := interactionFunctional_bounded_below d N P a mass ha hmass
  have hexp_int : Integrable (fun ω => Real.exp (-(t * V ω))) μ := by
    apply Integrable.of_bound (C := Real.exp (t * B))
    · exact ((hVmeas.const_mul t).neg.exp).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp_of_le (by nlinarith [hB ω, ht])
  have hpt : ∀ ω, 1 - t * V ω ≤ Real.exp (-(t * V ω)) := fun ω => by
    have := Real.add_one_le_exp (-(t * V ω)); linarith
  have hmono : ∫ ω, (1 - t * V ω) ∂μ ≤ ∫ ω, Real.exp (-(t * V ω)) ∂μ :=
    integral_mono ((integrable_const 1).sub (hVint.const_mul t)) hexp_int hpt
  have hlhs : ∫ ω, (1 - t * V ω) ∂μ = 1 - t * ∫ ω, V ω ∂μ := by
    rw [integral_sub (integrable_const 1) (hVint.const_mul t), integral_const_mul]
    simp
  rw [hlhs] at hmono
  have htV : t * ∫ ω, V ω ∂μ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht hVnonpos
  linarith [hmono, htV]

/-- **Exp-moment interpolation.** For `0 ≤ s ≤ 2`, `∫ e^{-s V} ≤ (∫ e^{-2 V})^{s/2}` (Jensen for the
concave `x ↦ x^{s/2}` on `[0,∞)`). Combined with the Nelson estimate `∫ e^{-2V} ≤ K` (uniform in N)
and `∫ e^{-2V} ≥ 1` (`partitionFn_ge_one`), this gives `∫ e^{-sV} ≤ K` uniformly — the exp-moment
control the corrected L4 pull-back needs (since `V` is not uniformly bounded below). -/
lemma expMoment_le_rpow (d N : ℕ) [NeZero N]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    {s : ℝ} (hs0 : 0 ≤ s) (hs2 : s ≤ 2) :
    ∫ ω, Real.exp (-(s * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass)
      ≤ (∫ ω, Real.exp (-(2 * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass)) ^ (s / 2) := by
  set μ := latticeGaussianMeasure d N a mass ha hmass with hμ
  set V := interactionFunctional d N P a mass with hV
  haveI : IsProbabilityMeasure μ := latticeGaussianMeasure_isProbability d N a mass ha hmass
  have hVmeas : Measurable V := interactionFunctional_measurable d N P a mass
  obtain ⟨B, hB⟩ := interactionFunctional_bounded_below d N P a mass ha hmass
  have ht0 : (0 : ℝ) ≤ s / 2 := by linarith
  have ht1 : s / 2 ≤ 1 := by linarith
  set f : Configuration (FinLatticeField d N) → ℝ := fun ω => Real.exp (-(2 * V ω)) with hf
  have hf_int : Integrable f μ := by
    apply Integrable.of_bound (C := Real.exp (2 * B))
    · exact ((hVmeas.const_mul 2).neg.exp).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by
        rw [hf, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp_of_le (by nlinarith [hB ω])
  have hsV_eq : (fun ω => f ω ^ (s / 2)) = fun ω => Real.exp (-(s * V ω)) := by
    funext ω; rw [hf, ← Real.exp_mul]; congr 1; ring
  have hgf_int : Integrable (fun ω => f ω ^ (s / 2)) μ := by
    rw [hsV_eq]
    apply Integrable.of_bound (C := Real.exp (s * B))
    · exact ((hVmeas.const_mul s).neg.exp).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp_of_le (by nlinarith [hB ω, hs0])
  have hconc : ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ (s / 2)) := Real.concaveOn_rpow ht0 ht1
  have hcont : ContinuousOn (fun x : ℝ => x ^ (s / 2)) (Set.Ici 0) :=
    continuousOn_id.rpow_const (fun x _ => Or.inr ht0)
  have hmem : ∀ᵐ ω ∂μ, f ω ∈ Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall fun ω => Set.mem_Ici.mpr (by rw [hf]; exact (Real.exp_pos _).le)
  have hjensen := hconc.le_map_integral hcont isClosed_Ici hmem hf_int hgf_int
  rwa [hsV_eq] at hjensen

/-- **L4 pull-back (Cauchy–Schwarz).** For `X ∈ L²(μ_GFF)` and `t ≥ 0`,
`∫ |X|·e^{-tV} ≤ (∫ X²)^{1/2}·(∫ e^{-2tV})^{1/2}`. Dividing by `Z_t ≥ 1` and using
`∫ e^{-2tV} ≤ (∫ e^{-2V})^t ≤ K` (Nelson, uniform), this bounds the interacting moment
`⟨|X|⟩_t = ∫|X|e^{-tV}/Z_t` by `‖X‖_{L²}·√K` — uniform in `N`, the corrected L4 mechanism. -/
lemma boltzmann_cauchySchwarz (d N : ℕ) [NeZero N]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (X : Configuration (FinLatticeField d N) → ℝ)
    (hX : MemLp X 2 (latticeGaussianMeasure d N a mass ha hmass))
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, |X ω| * Real.exp (-(t * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass)
      ≤ (∫ ω, (X ω) ^ 2 ∂(latticeGaussianMeasure d N a mass ha hmass)) ^ (1 / 2 : ℝ) *
        (∫ ω, Real.exp (-(2 * t * interactionFunctional d N P a mass ω))
          ∂(latticeGaussianMeasure d N a mass ha hmass)) ^ (1 / 2 : ℝ) := by
  set μ := latticeGaussianMeasure d N a mass ha hmass with hμ
  set V := interactionFunctional d N P a mass with hV
  haveI : IsProbabilityMeasure μ := latticeGaussianMeasure_isProbability d N a mass ha hmass
  have hVmeas : Measurable V := interactionFunctional_measurable d N P a mass
  obtain ⟨B, hB⟩ := interactionFunctional_bounded_below d N P a mass ha hmass
  have hg_memLp : MemLp (fun ω => Real.exp (-(t * V ω))) 2 μ := by
    apply MemLp.of_bound ((hVmeas.const_mul t).neg.exp).aestronglyMeasurable (Real.exp (t * B))
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp_of_le (by nlinarith [hB ω, ht])
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (f := fun ω => |X ω|) (g := fun ω => Real.exp (-(t * V ω)))
    (Filter.Eventually.of_forall fun ω => abs_nonneg (X ω))
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
    (by rw [ENNReal.ofReal_ofNat]; exact hX.abs)
    (by rw [ENNReal.ofReal_ofNat]; exact hg_memLp)
  refine le_trans key (le_of_eq ?_)
  congr 1
  · congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only; rw [Real.rpow_two, sq_abs]
  · congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only; rw [Real.rpow_two, pow_two, ← Real.exp_add]; congr 1; ring

end Pphi2
