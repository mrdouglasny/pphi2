/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Pphi2.InteractingMeasure.InteractionVariance
import Pphi2.InteractingMeasure.U4Derivative
import Pphi2.InteractingMeasure.LeadingTerm

/-!
# Uniform free product moment `⟨φ(f)^{2n} V^{2k}⟩₀ ≤ K₀` (uniform-discharge brick L3)

The final L3 deliverable for the uniform-discharge roadmap: for the normalised-constant test
function `f = (#sites)⁻¹·1` and the torus lattice GFF, the free product moment
`∫ (ωf)^{2n}·V^{2k} dμ_GFF` is bounded **uniformly in `N`**. This is what `L4`
(`interacting_moment_le_L2_of_expBound`) consumes to control the interacting moments
`⟨(ωf)^a V^b⟩_t` appearing in the `u₄''` expansion (`L5(ii)`).

Assembly of the three L3 bricks:
* `normConst_second_moment` — the field variance closed form `∫(ωf)² = (a^d·#sites·m²)⁻¹`,
  manifestly `= (L^d m²)⁻¹` on the torus (`torus_volume_eq`), uniform in `N`.
* `field_pow_le_second_pow` — Gaussian hypercontractivity `∫(ωf)^{2m} ≤ (2m-1)^m·(∫(ωf)²)^m`.
* `free_product_moment_cauchy_schwarz` — Hölder split + `interaction_moment_le` (uniform `V`).
-/

namespace Pphi2

open MeasureTheory GaussianField

variable {d N : ℕ}

/-- **L3 field variance closed form.** For the normalised-constant test function
`f = (#sites)⁻¹·1`, the free field variance is `∫(ωf)² dμ_GFF = (a^d·#sites·m²)⁻¹`. Via the variance
bridge `∫(ωf)² = gffSmearedCovariance f f`, the position-space expansion, and the covariance row-sum
`∑_x C(x,z) = (a^d m²)⁻¹` (the zero mode). On the torus `a^d·#sites = L^d`, so this is `(L^d m²)⁻¹`,
manifestly independent of `N`. -/
lemma normConst_second_moment [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    ∫ ω, (ω (fun _ : FinLatticeSites d N => (Fintype.card (FinLatticeSites d N) : ℝ)⁻¹)) ^ 2
        ∂(latticeGaussianMeasure d N a mass ha hmass)
      = (a ^ d * (Fintype.card (FinLatticeSites d N) : ℝ) * mass ^ 2)⁻¹ := by
  have hcard : (Fintype.card (FinLatticeSites d N) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_pos.ne'
  have had : (a ^ d : ℝ) ≠ 0 := (pow_pos ha d).ne'
  have hmsq : (mass ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hmass.ne'
  rw [latticeSecondMoment_eq_smearedCovariance d N a mass ha hmass,
    gffSmearedCovariance_eq_sum_position, Finset.sum_comm]
  have hval : ∀ y : FinLatticeSites d N,
      (∑ x, (Fintype.card (FinLatticeSites d N) : ℝ)⁻¹
          * (Fintype.card (FinLatticeSites d N) : ℝ)⁻¹ * gffPositionCovariance d N a mass x y)
      = (Fintype.card (FinLatticeSites d N) : ℝ)⁻¹ * (Fintype.card (FinLatticeSites d N) : ℝ)⁻¹
          * ((a ^ d : ℝ)⁻¹ * (mass ^ 2)⁻¹) := by
    intro y
    rw [← Finset.mul_sum, gffPositionCovariance_row_sum d N a mass ha hmass y]
  rw [Finset.sum_congr rfl (fun y _ => hval y), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **L3 field variance on the torus.** Specialising `normConst_second_moment` to `a = circleSpacing`
and `d = 2`, the torus volume identity `a²·#sites = L²` (`torus_volume_eq`) makes the free field
variance `∫(ωf)² dμ_GFF = (L²·m²)⁻¹` — exactly independent of `N`. -/
lemma torus_normConst_second_moment (L mass : ℝ) [Fact (0 < L)] (hmass : 0 < mass)
    (N : ℕ) [NeZero N] :
    ∫ ω, (ω (fun _ : FinLatticeSites 2 N => (Fintype.card (FinLatticeSites 2 N) : ℝ)⁻¹)) ^ 2
        ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass)
      = (L ^ 2 * mass ^ 2)⁻¹ := by
  rw [normConst_second_moment (circleSpacing L N) mass (circleSpacing_pos L N) hmass]
  congr 1
  rw [torus_volume_eq L 2 N]

/-- **L3 — uniform field moment.** For the normalised-constant test function on the torus, the free
even moment `∫(ωf)^{2m} dμ_GFF` is bounded uniformly in `N` by `(2m-1)^m·(L²m²)^{-m} + 1`. Combines
`field_pow_le_second_pow` (Gaussian hypercontractivity) with the uniform variance
`torus_normConst_second_moment`. -/
theorem torus_normConst_field_moment_uniform (L mass : ℝ) [Fact (0 < L)] (hmass : 0 < mass)
    (m : ℕ) :
    ∃ Cf : ℝ, 0 < Cf ∧ ∀ (N : ℕ) [NeZero N],
      ∫ ω, (ω (fun _ : FinLatticeSites 2 N => (Fintype.card (FinLatticeSites 2 N) : ℝ)⁻¹)) ^ (2 * m)
          ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass)
        ≤ Cf := by
  have hL : (0 : ℝ) < L := Fact.out
  have hbase : (0 : ℝ) ≤ ((2 * (m : ℝ) - 1)) ^ m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · refine pow_nonneg ?_ m
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
  have hprod : (0 : ℝ) ≤ ((2 * (m : ℝ) - 1)) ^ m * ((L ^ 2 * mass ^ 2)⁻¹) ^ m :=
    mul_nonneg hbase (by positivity)
  refine ⟨((2 * (m : ℝ) - 1)) ^ m * ((L ^ 2 * mass ^ 2)⁻¹) ^ m + 1, by linarith, fun N _ => ?_⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    haveI := latticeGaussianMeasure_isProbability 2 N (circleSpacing L N) mass
      (circleSpacing_pos L N) hmass
    simp only [mul_zero, pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
    linarith
  · have hfield := field_pow_le_second_pow (d := 2) (N := N) (circleSpacing L N) mass
      (circleSpacing_pos L N) hmass (fun _ => (Fintype.card (FinLatticeSites 2 N) : ℝ)⁻¹) m hm
    rw [torus_normConst_second_moment L mass hmass N] at hfield
    linarith

/-- **L3 — uniform free product moment.** For the normalised-constant test function and `k ≥ 1`, the
free product moment `∫(ωf)^{2n}·V^{2k} dμ_GFF` is bounded uniformly in `N`. Assembles the
Cauchy–Schwarz split (`free_product_moment_cauchy_schwarz`) with the uniform field moment
(`torus_normConst_field_moment_uniform`) and the uniform interaction moment
(`interaction_moment_le`). This is the free `L²`-norm input that `L4`
(`interacting_moment_le_L2_of_expBound`) consumes for the interacting moments in `u₄''`. -/
theorem torus_free_product_moment_uniform (L mass : ℝ) [Fact (0 < L)] (hmass : 0 < mass)
    (P : InteractionPolynomial) (n k : ℕ) (hk : 1 ≤ k) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ (N : ℕ) [NeZero N],
      ∫ ω, (ω (fun _ : FinLatticeSites 2 N => (Fintype.card (FinLatticeSites 2 N) : ℝ)⁻¹)) ^ (2 * n)
            * (interactionFunctional 2 N P (circleSpacing L N) mass ω) ^ (2 * k)
          ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass)
        ≤ K₀ := by
  obtain ⟨Cf, hCf, hCfb⟩ := torus_normConst_field_moment_uniform L mass hmass (2 * n)
  obtain ⟨KV, hKV, hKVb⟩ := interaction_moment_le L mass hmass P (2 * k) (by omega)
  refine ⟨Cf ^ (1 / 2 : ℝ) * KV ^ (1 / 2 : ℝ), by positivity, fun N _ => ?_⟩
  have hf := hCfb N
  rw [show 2 * (2 * n) = 4 * n from by ring] at hf
  have hV := hKVb N
  rw [show 2 * (2 * k) = 4 * k from by ring] at hV
  refine le_trans (free_product_moment_cauchy_schwarz P (circleSpacing L N) mass
    (circleSpacing_pos L N) hmass _ n k hk) ?_
  have hfn : (0 : ℝ) ≤ ∫ ω, (ω (fun _ : FinLatticeSites 2 N
      => (Fintype.card (FinLatticeSites 2 N) : ℝ)⁻¹)) ^ (4 * n)
      ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass) :=
    integral_nonneg fun ω => (show Even (4 * n) from ⟨2 * n, by ring⟩).pow_nonneg _
  have hVn : (0 : ℝ) ≤ ∫ ω, (interactionFunctional 2 N P (circleSpacing L N) mass ω) ^ (4 * k)
      ∂(latticeGaussianMeasure 2 N (circleSpacing L N) mass (circleSpacing_pos L N) hmass) :=
    integral_nonneg fun ω => (show Even (4 * k) from ⟨2 * k, by ring⟩).pow_nonneg _
  apply mul_le_mul
  · exact Real.rpow_le_rpow hfn hf (by norm_num)
  · exact Real.rpow_le_rpow hVn hV (by norm_num)
  · exact Real.rpow_nonneg hVn _
  · exact Real.rpow_nonneg hCf.le _

/-- **`(ωf)ⁿ·Vᵇ ∈ L²(μ_GFF)`** (`b ≥ 1`). The building-block observable of the `u₄''` interacting
moments lies in `L²`: `‖(ωf)ⁿVᵇ‖²_{L²} = ∫(ωf)^{2n}V^{2b}`, integrable as a product of the `L²`
functions `(ωf)^{2n}` (`pairing_memLp`) and `V^{2b}` (`interaction_memLp`) via Hölder `(2,2,1)`.
Provides the `MemLp` hypothesis of `abs_interacting_moment_le` for each `u₄''` moment. -/
theorem memLp_pairing_pow_mul_interaction_pow [NeZero N] (a mass : ℝ) (ha : 0 < a)
    (hmass : 0 < mass)
    (P : InteractionPolynomial) (f : FinLatticeField 2 N) (n b : ℕ) (hb : 1 ≤ b) :
    MemLp (fun ω => (ω f) ^ n * (interactionFunctional 2 N P a mass ω) ^ b) 2
      (latticeGaussianMeasure 2 N a mass ha hmass) := by
  set μ := latticeGaussianMeasure 2 N a mass ha hmass with hμ
  rw [memLp_two_iff_integrable_sq (((configuration_eval_measurable f).pow_const n).mul
    ((interactionFunctional_measurable 2 N P a mass).pow_const b)).aestronglyMeasurable]
  have h1 : MemLp (fun ω => (ω f) ^ (2 * n)) 2 μ := by
    rw [memLp_two_iff_integrable_sq
      ((configuration_eval_measurable f).pow_const (2 * n)).aestronglyMeasurable]
    refine (integrable_pow_pairing 2 N a mass ha hmass f (4 * n)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    show (ω f) ^ (4 * n) = ((ω f) ^ (2 * n)) ^ 2
    rw [← pow_mul]; congr 1; ring
  have h2 : MemLp (fun ω => (interactionFunctional 2 N P a mass ω) ^ (2 * b)) 2 μ := by
    rw [memLp_two_iff_integrable_sq
      ((interactionFunctional_measurable 2 N P a mass).pow_const (2 * b)).aestronglyMeasurable]
    refine (interactionFunctional_pow_integrable N a mass ha hmass P (4 * b) (by omega)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    show (interactionFunctional 2 N P a mass ω) ^ (4 * b)
      = ((interactionFunctional 2 N P a mass ω) ^ (2 * b)) ^ 2
    rw [← pow_mul]; congr 1; ring
  refine (h1.integrable_mul h2).congr (Filter.Eventually.of_forall fun ω => ?_)
  show (ω f) ^ (2 * n) * (interactionFunctional 2 N P a mass ω) ^ (2 * b)
    = ((ω f) ^ n * (interactionFunctional 2 N P a mass ω) ^ b) ^ 2
  rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf

end Pphi2
