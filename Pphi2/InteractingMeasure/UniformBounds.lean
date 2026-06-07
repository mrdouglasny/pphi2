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

/-- **L4 pull-back, assembled.** For `X ∈ L²(μ_GFF)`, `t ∈ [0,1]`, and a uniform Nelson
exp-bound `∫ e^{-2V} ≤ K` (with `K ≥ 1`), the interacting moment is `L²`-controlled:
`⟨|X|⟩_t = (∫|X|e^{-tV})/Z_t ≤ ‖X‖_{L²}·√K`. Composition of `boltzmann_cauchySchwarz`
(Cauchy–Schwarz), `expMoment_le_rpow` (`∫e^{-2tV} ≤ (∫e^{-2V})^t ≤ K`), and `partitionFn_ge_one`
(`Z_t ≥ 1`, so dividing only decreases). Uniform in `N` once `K` is (Nelson). This is the corrected
L4 mechanism — `V` is not *uniformly-in-N* bounded below (the 2D Wick constant log-diverges), so the
control is via the exp-moment, not a pointwise bound. -/
lemma interacting_moment_le_L2_of_expBound (d N : ℕ) [NeZero N]
    (P : InteractionPolynomial) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (X : Configuration (FinLatticeField d N) → ℝ)
    (hX : MemLp X 2 (latticeGaussianMeasure d N a mass ha hmass))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {K : ℝ} (hK1 : 1 ≤ K)
    (hKbound : ∫ ω, Real.exp (-(2 * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass) ≤ K) :
    (∫ ω, |X ω| * Real.exp (-(t * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass)) /
      (∫ ω, Real.exp (-(t * interactionFunctional d N P a mass ω))
        ∂(latticeGaussianMeasure d N a mass ha hmass))
      ≤ (∫ ω, (X ω) ^ 2 ∂(latticeGaussianMeasure d N a mass ha hmass)) ^ (1 / 2 : ℝ) *
        K ^ (1 / 2 : ℝ) := by
  set μ := latticeGaussianMeasure d N a mass ha hmass with hμ
  set V := interactionFunctional d N P a mass with hV
  have hnum_nonneg : 0 ≤ ∫ ω, |X ω| * Real.exp (-(t * V ω)) ∂μ :=
    integral_nonneg fun ω => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hZ : (1 : ℝ) ≤ ∫ ω, Real.exp (-(t * V ω)) ∂μ :=
    partitionFn_ge_one d N P a mass ha hmass ht0
  have hdiv : (∫ ω, |X ω| * Real.exp (-(t * V ω)) ∂μ) /
      (∫ ω, Real.exp (-(t * V ω)) ∂μ) ≤ ∫ ω, |X ω| * Real.exp (-(t * V ω)) ∂μ :=
    div_le_self hnum_nonneg hZ
  have hCS := boltzmann_cauchySchwarz d N P a mass ha hmass X hX ht0
  have hexp : (∫ ω, Real.exp (-(2 * t * V ω)) ∂μ) ^ (1 / 2 : ℝ) ≤ K ^ (1 / 2 : ℝ) := by
    refine Real.rpow_le_rpow (integral_nonneg fun ω => (Real.exp_pos _).le) ?_ (by norm_num)
    calc ∫ ω, Real.exp (-(2 * t * V ω)) ∂μ
        ≤ (∫ ω, Real.exp (-(2 * V ω)) ∂μ) ^ (2 * t / 2) :=
          expMoment_le_rpow d N P a mass ha hmass (by linarith) (by linarith)
      _ = (∫ ω, Real.exp (-(2 * V ω)) ∂μ) ^ t := by rw [show 2 * t / 2 = t by ring]
      _ ≤ K ^ t := Real.rpow_le_rpow (integral_nonneg fun ω => (Real.exp_pos _).le) hKbound ht0
      _ ≤ K := by
          calc K ^ t ≤ K ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK1 ht1
            _ = K := Real.rpow_one K
  calc (∫ ω, |X ω| * Real.exp (-(t * V ω)) ∂μ) / (∫ ω, Real.exp (-(t * V ω)) ∂μ)
      ≤ ∫ ω, |X ω| * Real.exp (-(t * V ω)) ∂μ := hdiv
    _ ≤ (∫ ω, (X ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
          (∫ ω, Real.exp (-(2 * t * V ω)) ∂μ) ^ (1 / 2 : ℝ) := hCS
    _ ≤ (∫ ω, (X ω) ^ 2 ∂μ) ^ (1 / 2 : ℝ) * K ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hexp
          (Real.rpow_nonneg (integral_nonneg fun ω => sq_nonneg _) _)

/-! ## Uniform assembly (the connective tissue: leaves ⟹ uniform negativity) -/

/-- **Uniform-in-N negativity from a uniform affine derivative bound.** If a family `(φ_i)` (think
`φ_N = u₄` of the Gibbs family at lattice size `N`) all vanish at `0`, are differentiable on
`[0,g₀]`, and satisfy the **uniform** affine bound `φ_i'(t) ≤ -s + K·t` with `s,K,g₀` independent of
`i`, then a **single** `g>0, c>0` works for ALL `i`: `φ_i g ≤ -c`. The `i`-uniform upgrade of
`deriv_affine_bound_neg`; the connective lemma turning the leaf estimates (uniform leading slope
`s`, uniform second-order constant `K`) into the uniform strict bound the headline axiom needs. -/
lemma exists_uniform_neg_of_uniform_affine_bound {ι : Type*} {φ φ' : ι → ℝ → ℝ} {s K g₀ : ℝ}
    (hs : 0 < s) (hK : 0 < K) (hg₀ : 0 < g₀)
    (h0 : ∀ i, φ i 0 = 0)
    (hderiv : ∀ i, ∀ t ∈ Set.Icc 0 g₀, HasDerivAt (φ i) (φ' i t) t)
    (hbound : ∀ i, ∀ t ∈ Set.Icc 0 g₀, φ' i t ≤ -s + K * t) :
    ∃ g c : ℝ, 0 < g ∧ 0 < c ∧ ∀ i, φ i g ≤ -c := by
  have hKne : K ≠ 0 := hK.ne'
  have hg_pos : 0 < min g₀ (s / (2 * K)) := lt_min hg₀ (by positivity)
  have hgg₀ : min g₀ (s / (2 * K)) ≤ g₀ := min_le_left _ _
  have hKg : K * min g₀ (s / (2 * K)) ≤ s / 2 := by
    have hle := mul_le_mul_of_nonneg_left (min_le_right g₀ (s / (2 * K))) hK.le
    have heq : K * (s / (2 * K)) = s / 2 := by field_simp
    rwa [heq] at hle
  refine ⟨min g₀ (s / (2 * K)), (s / 2) * min g₀ (s / (2 * K)), hg_pos, by positivity, fun i => ?_⟩
  have := deriv_affine_bound_neg (h0 i) (hderiv i) (hbound i) hK.le hg_pos hgg₀ hKg
  linarith [this]

/-- **MVT bound with the correct one-sided-at-`0` interface.** Same conclusion as
`deriv_affine_bound_neg`, but only requires **continuity on `[0,g₀]`** and `HasDerivAt` on the
**open** `(0,g₀)` — the right hypotheses for the Gibbs-family `u₄`, which has no two-sided
derivative at `g=0` (`∫e^{-gV}` diverges for `g<0`). -/
lemma deriv_affine_bound_neg_of_continuousOn {φ φ' : ℝ → ℝ} {s K g₀ : ℝ}
    (h0 : φ 0 = 0) (hcont : ContinuousOn φ (Set.Icc 0 g₀))
    (hderiv : ∀ t ∈ Set.Ioo 0 g₀, HasDerivAt φ (φ' t) t)
    (hbound : ∀ t ∈ Set.Ioo 0 g₀, φ' t ≤ -s + K * t) (hK : 0 ≤ K)
    {g : ℝ} (hg : 0 < g) (hgg₀ : g ≤ g₀) (hKg : K * g ≤ s / 2) :
    φ g ≤ -(s / 2) * g := by
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope φ φ' hg
    (hcont.mono (Set.Icc_subset_Icc le_rfl hgg₀))
    (fun x hx => hderiv x ⟨hx.1, hx.2.trans_le hgg₀⟩)
  rw [h0, sub_zero, sub_zero] at hξeq
  have hφg : φ g = φ' ξ * g := by rw [hξeq, div_mul_cancel₀ _ (ne_of_gt hg)]
  have hξle : φ' ξ ≤ -s + K * ξ := hbound ξ ⟨hξ.1, hξ.2.trans_le hgg₀⟩
  have hKξ : K * ξ ≤ K * g := mul_le_mul_of_nonneg_left (le_of_lt hξ.2) hK
  have : φ' ξ ≤ -(s / 2) := by linarith [hξle, hKξ, hKg]
  rw [hφg]; exact mul_le_mul_of_nonneg_right this (le_of_lt hg)

/-- **Uniform negativity, correct interface.** The `i`-uniform assembly using continuity on `[0,g₀]`
and interior differentiability — the version actually usable for `φ_N = u₄` of the Gibbs family. -/
lemma exists_uniform_neg_of_uniform_affine_bound' {ι : Type*} {φ φ' : ι → ℝ → ℝ} {s K g₀ : ℝ}
    (hs : 0 < s) (hK : 0 < K) (hg₀ : 0 < g₀)
    (h0 : ∀ i, φ i 0 = 0)
    (hcont : ∀ i, ContinuousOn (φ i) (Set.Icc 0 g₀))
    (hderiv : ∀ i, ∀ t ∈ Set.Ioo 0 g₀, HasDerivAt (φ i) (φ' i t) t)
    (hbound : ∀ i, ∀ t ∈ Set.Ioo 0 g₀, φ' i t ≤ -s + K * t) :
    ∃ g c : ℝ, 0 < g ∧ 0 < c ∧ ∀ i, φ i g ≤ -c := by
  have hKne : K ≠ 0 := hK.ne'
  have hg_pos : 0 < min g₀ (s / (2 * K)) := lt_min hg₀ (by positivity)
  have hgg₀ : min g₀ (s / (2 * K)) ≤ g₀ := min_le_left _ _
  have hKg : K * min g₀ (s / (2 * K)) ≤ s / 2 := by
    have hle := mul_le_mul_of_nonneg_left (min_le_right g₀ (s / (2 * K))) hK.le
    have heq : K * (s / (2 * K)) = s / 2 := by field_simp
    rwa [heq] at hle
  refine ⟨min g₀ (s / (2 * K)), (s / 2) * min g₀ (s / (2 * K)), hg_pos, by positivity, fun i => ?_⟩
  have := deriv_affine_bound_neg_of_continuousOn (h0 i) (hcont i) (hderiv i) (hbound i) hK.le
    hg_pos hgg₀ hKg
  linarith [this]

end Pphi2
