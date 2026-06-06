/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.U4Derivative
import Pphi2.TorusContinuumLimit.TorusInteractingLimit

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

end Pphi2
