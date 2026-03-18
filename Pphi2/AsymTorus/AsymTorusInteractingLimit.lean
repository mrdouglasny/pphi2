/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asymmetric Torus Interacting Limit: Route B'

Proves existence of the interacting P(φ)₂ continuum limit on the
asymmetric torus T_{Lt,Ls}, following the same structure as
`TorusInteractingLimit.lean` for the symmetric torus.

## Main results

- `asymNelson_exponential_estimate` — Nelson bound uniform in N
- `asymTorus_interacting_second_moment_uniform` — uniform second moments
- `asymTorus_interacting_tightness` — tightness via Mitoma-Chebyshev
- `asymTorusInteractingLimit_exists` — subsequential weak limit exists

## Key identity

Nelson's estimate uses: `a_geom² · N² = Lt · Ls` (physical volume constant).
This is the asymmetric analog of `a² · N² = L²` for the symmetric torus.
-/

import Pphi2.AsymTorus.AsymTorusEmbedding
import Pphi2.NelsonEstimate.NelsonEstimate
import Pphi2.ContinuumLimit.Hypercontractivity
import Pphi2.TorusContinuumLimit.TorusPropagatorConvergence
import GaussianField.Tightness
import GaussianField.ConfigurationEmbedding
import GaussianField.Properties
import GaussianField.HypercontractiveNat

noncomputable section

open GaussianField MeasureTheory Filter

namespace Pphi2

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-! ## Nelson's exponential estimate (asymmetric) -/

/-- Physical volume identity: a_geom² · N² = Lt · Ls.

This is the key identity for Nelson's estimate: the physical volume
is independent of the lattice size N. -/
theorem asymGeomSpacing_sq_mul_sq (N : ℕ) [NeZero N] :
    asymGeomSpacing Lt Ls N ^ 2 * (N : ℝ) ^ 2 = Lt * Ls := by
  unfold asymGeomSpacing asymTimeSpacing asymSpaceSpacing
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have h_nn : 0 ≤ Lt / ↑N * (Ls / ↑N) :=
    mul_nonneg (div_nonneg hLt.out.le hN_pos.le) (div_nonneg hLs.out.le hN_pos.le)
  rw [Real.sq_sqrt h_nn]
  field_simp

/-- **Nelson's exponential estimate** (asymmetric torus, uniform in N).

The L² norm of the Boltzmann weight is bounded by a constant K that
depends on P, mass, Lt, Ls but NOT on N:

  `∫ exp(-2V) dμ_GFF ≤ K`   for all N ≥ 1

Proof: identical to the symmetric case. The interaction
`V = a_geom² Σ_x :P(φ(x)):_c` satisfies `V ≥ -a_geom² N² A = -Lt·Ls·A`
where A is the uniform lower bound on Wick polynomials.
Hence `exp(-2V) ≤ exp(2·Lt·Ls·A)` uniformly in N. -/
theorem asymNelson_exponential_estimate
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (K : ℝ), 0 < K ∧
    ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (FinLatticeField 2 N),
        (Real.exp (-interactionFunctional 2 N P (asymGeomSpacing Lt Ls N) mass ω)) ^ 2
        ∂(latticeGaussianMeasure 2 N (asymGeomSpacing Lt Ls N) mass
          (asymGeomSpacing_pos Lt Ls N) hmass) ≤ K := by
  -- Same proof as nelson_exponential_estimate_lattice but with a_geom²N² = Lt·Ls
  -- instead of a²N² = L². K = exp(2 · Lt · Ls · A).
  -- Step 1: Get uniform lower bound on wickPolynomial for c ∈ [0, mass⁻²]
  obtain ⟨A, hA_pos, hA_bound⟩ :=
    Pphi2.wickPolynomial_uniform_bounded_below P (mass⁻¹ ^ 2) (by positivity)
  -- Step 2: K = exp(2 · Lt · Ls · A) works uniformly in N
  refine ⟨Real.exp (2 * (Lt * Ls) * A), Real.exp_pos _, fun N _ => ?_⟩
  set a := asymGeomSpacing Lt Ls N
  set ha := asymGeomSpacing_pos Lt Ls N
  set μ := latticeGaussianMeasure 2 N a mass ha hmass
  haveI : IsProbabilityMeasure μ := latticeGaussianMeasure_isProbability 2 N a mass ha hmass
  -- Step 3: V(ω) ≥ -(a² · |Λ| · A) = -(Lt·Ls · A) for all ω
  have hc_nn : 0 ≤ wickConstant 2 N a mass :=
    le_of_lt (wickConstant_pos 2 N a mass ha hmass)
  have hc_le : wickConstant 2 N a mass ≤ mass⁻¹ ^ 2 :=
    wickConstant_le_inv_mass_sq 2 N a mass ha hmass
  set Λ := Fintype.card (FinLatticeSites 2 N)
  -- Key identity: a² · Λ = Lt · Ls (since a = √(Lt·Ls)/N and Λ = N²)
  have hΛ_eq : (Λ : ℝ) = (N : ℝ) ^ 2 := by
    change (Fintype.card (Fin 2 → ZMod N) : ℝ) = (N : ℝ) ^ 2
    simp [ZMod.card]
  have ha_sq_Λ : a ^ 2 * (Λ : ℝ) = Lt * Ls := by
    rw [hΛ_eq]
    exact asymGeomSpacing_sq_mul_sq Lt Ls N
  have h_wp_bound : ∀ (ω : Configuration (FinLatticeField 2 N)),
      interactionFunctional 2 N P a mass ω ≥ -(Lt * Ls * A) := by
    intro ω
    unfold interactionFunctional
    have ha_pow : (0 : ℝ) ≤ a ^ 2 := sq_nonneg a
    calc a ^ 2 * ∑ x : FinLatticeSites 2 N,
          wickPolynomial P (wickConstant 2 N a mass) (ω (finLatticeDelta 2 N x))
        ≥ a ^ 2 * ∑ _x : FinLatticeSites 2 N, (-A) := by
          apply mul_le_mul_of_nonneg_left _ ha_pow
          exact Finset.sum_le_sum fun x _ => hA_bound _ hc_nn hc_le _
      _ = a ^ 2 * (-(↑Λ * A)) := by
          congr 1; rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      _ = -(a ^ 2 * ↑Λ * A) := by ring
      _ = -(Lt * Ls * A) := by rw [ha_sq_Λ]
  -- Step 4: exp(-2V) ≤ exp(2 · Lt · Ls · A) pointwise
  have h_exp_bound : ∀ ω, (Real.exp (-interactionFunctional 2 N P a mass ω)) ^ 2 ≤
      Real.exp (2 * (Lt * Ls) * A) := by
    intro ω
    rw [sq, ← Real.exp_add, show -interactionFunctional 2 N P a mass ω +
        (-interactionFunctional 2 N P a mass ω) =
        -2 * interactionFunctional 2 N P a mass ω from by ring]
    exact Real.exp_le_exp_of_le (by linarith [h_wp_bound ω])
  -- Step 5: Integrate the pointwise bound over the probability measure
  calc ∫ ω, (Real.exp (-interactionFunctional 2 N P a mass ω)) ^ 2 ∂μ
      ≤ ∫ _ω, Real.exp (2 * (Lt * Ls) * A) ∂μ := by
        apply integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _)
          (integrable_const _) (ae_of_all _ h_exp_bound)
    _ = Real.exp (2 * (Lt * Ls) * A) := by
        simp [integral_const]

/-- The asymmetric torus interacting measure is a probability measure. -/
instance asymTorusInteractingMeasure_isProbability (N : ℕ) [NeZero N]
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    IsProbabilityMeasure (asymTorusInteractingMeasure Lt Ls N P mass hmass) := by
  unfold asymTorusInteractingMeasure
  haveI := interactingLatticeMeasure_isProbability 2 N P
    (asymGeomSpacing Lt Ls N) mass (asymGeomSpacing_pos Lt Ls N) hmass
  exact Measure.isProbabilityMeasure_map
    (asymTorusEmbedLift_measurable Lt Ls N).aemeasurable

/-! ## Gaussian second moment bounds -/

/-- The Gaussian second moment `∫ (ω g)² dμ_GFF` on the lattice with geometric
mean spacing is bounded uniformly in N.

This is the asymmetric analog of `torusEmbeddedTwoPoint_uniform_bound`.
The proof follows the same structure: `∫ (ω g)² = ⟨Tg, Tg⟩ ≤ m⁻² Σ_x g(x)²`,
and the Riemann sum `Σ_x (evalAsymAtFinSite x f)²` is bounded uniformly
because each factor uses `circleRestriction` with `√(L_i/N)` normalization,
giving `Σ_x ≤ Lt·Ls·C₀⁴·p₀f² + 1`.

Template: `torusEmbeddedTwoPoint_uniform_bound` in TorusPropagatorConvergence.lean:531-555.
Key change: `L²` → `Lt·Ls` in the Riemann sum bound (different circle periods per direction). -/
-- Helper: pure basis element equals basisVec (asymmetric version).
private theorem asym_pure_basis_eq_basisVec_pair (i j : ℕ) :
    (NuclearTensorProduct.pure
      (DyninMityaginSpace.basis i : SmoothMap_Circle Lt ℝ)
      (DyninMityaginSpace.basis j : SmoothMap_Circle Ls ℝ) :
      AsymTorusTestFunction Lt Ls) =
    RapidDecaySeq.basisVec (Nat.pair i j) := by
  ext m
  simp only [NuclearTensorProduct.pure_val, RapidDecaySeq.basisVec]
  rw [smoothCircle_coeff_basis Lt (Nat.unpair m).1 i,
      smoothCircle_coeff_basis Ls (Nat.unpair m).2 j]
  by_cases h1 : (Nat.unpair m).1 = i <;> by_cases h2 : (Nat.unpair m).2 = j <;>
    simp only [h1, h2, ↓reduceIte, mul_one, mul_zero,
      left_eq_ite_iff, right_eq_ite_iff, one_ne_zero,
      zero_ne_one, imp_false, Decidable.not_not]
  · conv_lhs => rw [← Nat.pair_unpair m]; rw [h1, h2]
  · intro h; exact h2 (by have := congr_arg (fun p => (Nat.unpair p).2) h
                          simpa only [Nat.unpair_pair] using this)
  · intro h; exact h1 (by have := congr_arg (fun p => (Nat.unpair p).1) h
                          simpa only [Nat.unpair_pair] using this)
  · intro h; exact h1 (by have := congr_arg (fun p => (Nat.unpair p).1) h
                          simpa only [Nat.unpair_pair] using this)

-- Parameterized Riemann sum bound: given Sobolev constants C₀t, C₀s,
-- the squared sum Σ_x (asymLatticeTestFn f x)² ≤ Lt*Ls*C₀t²*C₀s²*(p₀f)² + 1.
theorem asymLatticeTestFn_norm_sq_le
    (C₀t : ℝ) (hC₀t_pos : 0 < C₀t)
    (hC₀t : ∀ n, SmoothMap_Circle.sobolevSeminorm (L := Lt) 0
      (SmoothMap_Circle.fourierBasis n) ≤ C₀t)
    (C₀s : ℝ) (hC₀s_pos : 0 < C₀s)
    (hC₀s : ∀ n, SmoothMap_Circle.sobolevSeminorm (L := Ls) 0
      (SmoothMap_Circle.fourierBasis n) ≤ C₀s)
    (f : AsymTorusTestFunction Lt Ls) (N : ℕ) [NeZero N] :
    ∑ x : FinLatticeSites 2 N, (asymLatticeTestFn Lt Ls N f x) ^ 2 ≤
    Lt * Ls * C₀t ^ 2 * C₀s ^ 2 * (RapidDecaySeq.rapidDecaySeminorm 0 f) ^ 2 + 1 := by
  set p₀f := RapidDecaySeq.rapidDecaySeminorm 0 f
  -- Summability of |f.val m|.
  have hf_sum : Summable (fun m => |f.val m|) :=
    (f.rapid_decay 0).congr (fun m => by simp [pow_zero])
  -- Step 4: Bound |circleRestriction L_i N (basis n) k| ≤ √(L_i/N) * C₀i.
  have h_cr_t : ∀ n (k : ZMod N),
      |circleRestriction Lt N (DyninMityaginSpace.basis n :
        SmoothMap_Circle Lt ℝ) k| ≤ Real.sqrt (Lt / ↑N) * C₀t := by
    intro n k
    rw [dm_basis_eq_fourierBasis (L := Lt), circleRestriction_apply,
      circleSpacing_eq, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    calc |(SmoothMap_Circle.fourierBasis (L := Lt) n : ℝ → ℝ) (circlePoint Lt N k)|
        = ‖iteratedDeriv 0 ((SmoothMap_Circle.fourierBasis (L := Lt) n : ℝ → ℝ))
            (circlePoint Lt N k)‖ := by rw [iteratedDeriv_zero, Real.norm_eq_abs]
      _ ≤ SmoothMap_Circle.sobolevSeminorm 0 (SmoothMap_Circle.fourierBasis n) :=
          SmoothMap_Circle.norm_iteratedDeriv_le_sobolevSeminorm' _ 0 _
      _ ≤ C₀t := hC₀t n
  have h_cr_s : ∀ n (k : ZMod N),
      |circleRestriction Ls N (DyninMityaginSpace.basis n :
        SmoothMap_Circle Ls ℝ) k| ≤ Real.sqrt (Ls / ↑N) * C₀s := by
    intro n k
    rw [dm_basis_eq_fourierBasis (L := Ls), circleRestriction_apply,
      circleSpacing_eq, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    calc |(SmoothMap_Circle.fourierBasis (L := Ls) n : ℝ → ℝ) (circlePoint Ls N k)|
        = ‖iteratedDeriv 0 ((SmoothMap_Circle.fourierBasis (L := Ls) n : ℝ → ℝ))
            (circlePoint Ls N k)‖ := by rw [iteratedDeriv_zero, Real.norm_eq_abs]
      _ ≤ SmoothMap_Circle.sobolevSeminorm 0 (SmoothMap_Circle.fourierBasis n) :=
          SmoothMap_Circle.norm_iteratedDeriv_le_sobolevSeminorm' _ 0 _
      _ ≤ C₀s := hC₀s n
  -- Step 5: Bound |eval_x(basisVec m)| ≤ √(Lt/N)·C₀t · √(Ls/N)·C₀s
  have hLtN : (0 : ℝ) ≤ Lt / ↑N :=
    (div_pos hLt.out (Nat.cast_pos.mpr (NeZero.pos N))).le
  have hLsN : (0 : ℝ) ≤ Ls / ↑N :=
    (div_pos hLs.out (Nat.cast_pos.mpr (NeZero.pos N))).le
  have h_basis : ∀ (x : FinLatticeSites 2 N) (m : ℕ),
      |evalAsymAtFinSite Lt Ls N x (RapidDecaySeq.basisVec m)| ≤
      Real.sqrt (Lt / ↑N) * C₀t * (Real.sqrt (Ls / ↑N) * C₀s) := by
    intro x m
    -- evalAsymAtFinSite = evalAsymTorusAtSite = evalCLM (proj ∘ circleRestriction) (...)
    -- For basisVec, pure tensor decomposition applies
    unfold evalAsymAtFinSite evalAsymTorusAtSite
    rw [show RapidDecaySeq.basisVec m = NuclearTensorProduct.pure
        (DyninMityaginSpace.basis (Nat.unpair m).1 : SmoothMap_Circle Lt ℝ)
        (DyninMityaginSpace.basis (Nat.unpair m).2 : SmoothMap_Circle Ls ℝ) from by
      rw [asym_pure_basis_eq_basisVec_pair, Nat.pair_unpair]]
    rw [NuclearTensorProduct.evalCLM_pure]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    rw [abs_mul]
    exact mul_le_mul (h_cr_t _ _) (h_cr_s _ _) (abs_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) hC₀t_pos.le)
  -- Step 6: Bound |eval_x f| ≤ √(Lt/N)·C₀t · √(Ls/N)·C₀s · p₀f via DM expansion.
  set B := Real.sqrt (Lt / ↑N) * C₀t * (Real.sqrt (Ls / ↑N) * C₀s)
  have hB_nn : 0 ≤ B :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC₀t_pos.le)
      (mul_nonneg (Real.sqrt_nonneg _) hC₀s_pos.le)
  have h_pw : ∀ x : FinLatticeSites 2 N,
      |asymLatticeTestFn Lt Ls N f x| ≤ B * p₀f := by
    intro x
    unfold asymLatticeTestFn
    rw [DyninMityaginSpace.expansion (evalAsymAtFinSite Lt Ls N x) f]
    have hsf : Summable (fun m => f.val m *
        evalAsymAtFinSite Lt Ls N x (RapidDecaySeq.basisVec m)) :=
      (hf_sum.mul_right B).of_norm_bounded
        (fun m => by rw [Real.norm_eq_abs, abs_mul]
                     exact mul_le_mul_of_nonneg_left (h_basis x m) (abs_nonneg _))
    calc |∑' m, f.val m * evalAsymAtFinSite Lt Ls N x (RapidDecaySeq.basisVec m)|
        = ‖∑' m, f.val m * evalAsymAtFinSite Lt Ls N x (RapidDecaySeq.basisVec m)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∑' m, ‖f.val m * evalAsymAtFinSite Lt Ls N x (RapidDecaySeq.basisVec m)‖ :=
          norm_tsum_le_tsum_norm hsf.norm
      _ ≤ ∑' m, |f.val m| * B := by
          apply Summable.tsum_le_tsum _ hsf.norm (hf_sum.mul_right _)
          intro m
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_left (h_basis x m) (abs_nonneg _)
      _ = B * ∑' m, |f.val m| := by rw [tsum_mul_right]; ring
      _ = B * p₀f := by
          congr 1
          change ∑' m, |f.val m| = ∑' m, |f.val m| * (1 + (m : ℝ)) ^ 0
          simp
  -- Step 7: Sum of squares over lattice sites.
  -- N² · B² · p₀f² where B = √(Lt/N)·C₀t · √(Ls/N)·C₀s
  -- B² = (Lt/N)·C₀t² · (Ls/N)·C₀s² so N²·B² = Lt·Ls·C₀t²·C₀s²
  calc ∑ x : FinLatticeSites 2 N, (asymLatticeTestFn Lt Ls N f x) ^ 2
      ≤ ∑ _x : FinLatticeSites 2 N, (B * p₀f) ^ 2 := by
        apply Finset.sum_le_sum; intro x _
        exact sq_le_sq' (by linarith [h_pw x, neg_abs_le (asymLatticeTestFn Lt Ls N f x)])
          (le_of_abs_le (h_pw x))
    _ = ↑(Fintype.card (FinLatticeSites 2 N)) * (B * p₀f) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = ↑N ^ 2 * (B * p₀f) ^ 2 := by
        congr 1; simp [FinLatticeSites, ZMod.card, Fintype.card_fin]
    _ = Lt * Ls * C₀t ^ 2 * C₀s ^ 2 * p₀f ^ 2 := by
        have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
        -- B = √(Lt/N) * C₀t * (√(Ls/N) * C₀s)
        -- B² = (Lt/N) * C₀t² * (Ls/N) * C₀s²
        -- N² * B² = Lt * Ls * C₀t² * C₀s²
        change ↑N ^ 2 * (B * p₀f) ^ 2 = Lt * Ls * C₀t ^ 2 * C₀s ^ 2 * p₀f ^ 2
        have hB_sq : B ^ 2 = (Lt / ↑N) * C₀t ^ 2 * ((Ls / ↑N) * C₀s ^ 2) := by
          change (Real.sqrt (Lt / ↑N) * C₀t * (Real.sqrt (Ls / ↑N) * C₀s)) ^ 2 = _
          rw [show (Real.sqrt (Lt / ↑N) * C₀t * (Real.sqrt (Ls / ↑N) * C₀s)) ^ 2 =
              (Real.sqrt (Lt / ↑N)) ^ 2 * C₀t ^ 2 *
              ((Real.sqrt (Ls / ↑N)) ^ 2 * C₀s ^ 2) from by ring]
          rw [Real.sq_sqrt hLtN, Real.sq_sqrt hLsN]
        rw [show (B * p₀f) ^ 2 = B ^ 2 * p₀f ^ 2 from by ring, hB_sq]
        field_simp
    _ ≤ Lt * Ls * C₀t ^ 2 * C₀s ^ 2 * p₀f ^ 2 + 1 :=
        le_add_of_nonneg_right (by positivity)

-- Existential wrapper for `asymLatticeTestFn_norm_sq_le`.
theorem asymLatticeTestFn_norm_sq_bounded
    (f : AsymTorusTestFunction Lt Ls) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N],
    ∑ x : FinLatticeSites 2 N, (asymLatticeTestFn Lt Ls N f x) ^ 2 ≤ C := by
  obtain ⟨C₀t, hC₀t_pos, hC₀t_bound⟩ :=
    SmoothMap_Circle.sobolevSeminorm_fourierBasis_le (L := Lt) 0
  have hC₀t : ∀ n, SmoothMap_Circle.sobolevSeminorm (L := Lt) 0
      (SmoothMap_Circle.fourierBasis n) ≤ C₀t := fun n => by
    specialize hC₀t_bound n; simp only [pow_zero, mul_one] at hC₀t_bound; exact hC₀t_bound
  obtain ⟨C₀s, hC₀s_pos, hC₀s_bound⟩ :=
    SmoothMap_Circle.sobolevSeminorm_fourierBasis_le (L := Ls) 0
  have hC₀s : ∀ n, SmoothMap_Circle.sobolevSeminorm (L := Ls) 0
      (SmoothMap_Circle.fourierBasis n) ≤ C₀s := fun n => by
    specialize hC₀s_bound n; simp only [pow_zero, mul_one] at hC₀s_bound; exact hC₀s_bound
  set p₀f := RapidDecaySeq.rapidDecaySeminorm 0 f
  have hC_pos : 0 < Lt * Ls * C₀t ^ 2 * C₀s ^ 2 * p₀f ^ 2 + 1 := by
    have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hLt.out.le hLs.out.le)
      (sq_nonneg C₀t)) (sq_nonneg C₀s)) (sq_nonneg p₀f)
    linarith
  exact ⟨_, hC_pos, fun N _ =>
    asymLatticeTestFn_norm_sq_le Lt Ls C₀t hC₀t_pos hC₀t C₀s hC₀s_pos hC₀s f N⟩

theorem asymGaussian_second_moment_uniform_bound
    (mass : ℝ) (hmass : 0 < mass)
    (f : AsymTorusTestFunction Lt Ls) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (FinLatticeField 2 N),
      (ω (asymLatticeTestFn Lt Ls N f)) ^ 2
      ∂(latticeGaussianMeasure 2 N (asymGeomSpacing Lt Ls N) mass
        (asymGeomSpacing_pos Lt Ls N) hmass) ≤ Cg := by
  obtain ⟨C_f, hC_f_pos, hC_f_bound⟩ := asymLatticeTestFn_norm_sq_bounded Lt Ls f
  refine ⟨mass⁻¹ ^ 2 * C_f, mul_pos (pow_pos (inv_pos.mpr hmass) 2) hC_f_pos, fun N _ => ?_⟩
  set g := asymLatticeTestFn Lt Ls N f
  set a := asymGeomSpacing Lt Ls N
  set ha := asymGeomSpacing_pos Lt Ls N
  set T := latticeCovariance 2 N a mass ha hmass
  change ∫ ω, (ω g) ^ 2 ∂(GaussianField.measure T) ≤ mass⁻¹ ^ 2 * C_f
  rw [second_moment_eq_covariance T g]
  -- Step 3: Apply covariance bound
  calc @inner ℝ ell2' _
        (T g) (T g)
      ≤ mass⁻¹ ^ 2 *
          ∑ x : FinLatticeSites 2 N, g x ^ 2 :=
        covariance_inner_le_mass_inv_sq_norm_sq N a mass ha hmass g
    _ ≤ mass⁻¹ ^ 2 * C_f :=
        mul_le_mul_of_nonneg_left (hC_f_bound N) (le_of_lt (pow_pos (inv_pos.mpr hmass) 2))

/-! ## Tightness and limit existence -/

/-- Uniform second moment bound for the asymmetric torus interacting measures.

For each test function f, `∫ (ω f)² dμ_{P,N}` is bounded uniformly in N. -/
theorem asymTorus_interacting_second_moment_uniform
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (f : AsymTorusTestFunction Lt Ls) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      (ω f) ^ 2 ∂(asymTorusInteractingMeasure Lt Ls N P mass hmass) ≤ C := by
  -- Step 1: Get K from Nelson's exponential estimate (uniform in N)
  obtain ⟨K, hK_pos, hK_bound⟩ := asymNelson_exponential_estimate Lt Ls P mass hmass
  -- Step 2: Get Cg from uniform Gaussian second moment bound
  obtain ⟨Cg, hCg_pos, hCg_bound⟩ := asymGaussian_second_moment_uniform_bound Lt Ls mass hmass f
  -- C = 3 · √K · Cg works, from density transfer + hypercontractivity
  refine ⟨3 * Real.sqrt K * Cg,
    mul_pos (mul_pos (by norm_num : (0:ℝ) < 3) (Real.sqrt_pos_of_pos hK_pos)) hCg_pos,
    fun N _ => ?_⟩
  -- Step 1: Push integral through torus embedding
  set μ_int := interactingLatticeMeasure 2 N P (asymGeomSpacing Lt Ls N) mass
    (asymGeomSpacing_pos Lt Ls N) hmass
  set μ_GFF := latticeGaussianMeasure 2 N (asymGeomSpacing Lt Ls N) mass
    (asymGeomSpacing_pos Lt Ls N) hmass
  set ι := asymTorusEmbedLift Lt Ls N
  set g := asymLatticeTestFn Lt Ls N f
  have hι_meas : AEMeasurable ι μ_int :=
    (asymTorusEmbedLift_measurable Lt Ls N).aemeasurable
  -- ∫ (ω f)² d(map ι μ_int) = ∫ ((ι ω) f)² dμ_int = ∫ (ω g)² dμ_int
  change ∫ ω, (ω f) ^ 2 ∂(Measure.map ι μ_int) ≤ 3 * Real.sqrt K * Cg
  rw [integral_map hι_meas
    ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable]
  -- Rewrite (ι ω) f = ω g using asymTorusEmbedLift_eval_eq
  have h_eval : ∀ ω : Configuration (FinLatticeField 2 N),
      (ι ω) f = ω g := fun ω => asymTorusEmbedLift_eval_eq Lt Ls N f ω
  simp_rw [h_eval]
  -- Now goal: ∫ (ω g)² dμ_int ≤ 3 * √K * Cg
  -- Step 2: Apply density_transfer_bound with F(ω) = (ω g)²
  have hZ_ge_one := partitionFunction_ge_one 2 N P mass hmass
    (asymGeomSpacing Lt Ls N) (asymGeomSpacing_pos Lt Ls N)
  have hF_nn : ∀ ω : Configuration (FinLatticeField 2 N), 0 ≤ (ω g) ^ 2 :=
    fun ω => sq_nonneg _
  have hF_meas : AEStronglyMeasurable (fun ω : Configuration (FinLatticeField 2 N) =>
      (ω g) ^ 2) μ_GFF :=
    ((configuration_eval_measurable g).pow_const 2).aestronglyMeasurable
  have hF_sq_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
      ((ω g) ^ 2) ^ 2) μ_GFF := by
    have h4 : MemLp (fun ω : Configuration (FinLatticeField 2 N) => ω g)
        4 μ_GFF := by
      exact_mod_cast pairing_memLp (latticeCovariance 2 N (asymGeomSpacing Lt Ls N) mass
        (asymGeomSpacing_pos Lt Ls N) hmass) g 4
    have hmem := h4.norm_rpow (p := (4 : ENNReal))
      (by norm_num : (4 : ENNReal) ≠ 0) (by norm_num : (4 : ENNReal) ≠ ⊤)
    rw [memLp_one_iff_integrable] at hmem
    have h_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
        ‖ω g‖ ^ (4 : ℕ)) μ_GFF := by
      refine hmem.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp [ENNReal.toReal_ofNat]
    exact h_int.congr (Filter.Eventually.of_forall fun ω => by
      dsimp only
      rw [Real.norm_eq_abs]
      conv_rhs => rw [show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]
      ring)
  -- Apply density_transfer_bound
  have h_dt := density_transfer_bound 2 N P (asymGeomSpacing Lt Ls N) mass
    (asymGeomSpacing_pos Lt Ls N) hmass K hK_pos (hK_bound N)
    hZ_ge_one (fun ω => (ω g) ^ 2) hF_nn hF_meas hF_sq_int
  -- Step 3: Convert rpow to nat pow in h_dt and bound
  have h_rpow_to_npow : ∀ ω : Configuration (FinLatticeField 2 N),
      (fun ω => (ω g) ^ 2) ω ^ (2:ℝ) = ((ω g) ^ 2) ^ 2 := by
    intro ω
    exact Real.rpow_natCast ((ω g) ^ 2) 2
  have h_int_rpow_eq : ∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2:ℝ) ∂μ_GFF =
      ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF := by
    congr 1; ext ω; exact h_rpow_to_npow ω
  -- Step 4: Bound ∫ ((ω g)²)² dμ_GFF using hypercontractivity
  have h_second_le : ∫ ω, (ω g) ^ 2 ∂μ_GFF ≤ Cg := hCg_bound N
  have h_second_nn : 0 ≤ ∫ ω, (ω g) ^ 2 ∂μ_GFF :=
    integral_nonneg fun ω => sq_nonneg _
  set T := latticeCovariance 2 N (asymGeomSpacing Lt Ls N) mass
    (asymGeomSpacing_pos Lt Ls N) hmass
  have hμ_eq : μ_GFF = GaussianField.measure T := rfl
  have h_fourth_le : ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF ≤ 9 * Cg ^ 2 := by
    have h_eq4 : ∀ ω : Configuration (FinLatticeField 2 N),
        ((ω g) ^ 2) ^ 2 = |ω g| ^ 4 := by
      intro ω; rw [show ω g ^ 2 = |ω g| ^ 2 from (sq_abs _).symm]; ring
    simp_rw [h_eq4]
    have h_hyper := gaussian_hypercontractive T g 1 4
      (by norm_num : (2:ℝ) ≤ 4) 2 (by norm_num : 1 ≤ 2)
      (by norm_num : (4:ℝ) = 2 * ↑2)
    have h_lhs_eq : ∫ ω, |ω g| ^ 4 ∂μ_GFF =
        ∫ ω, |ω g| ^ ((4:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T) := by
      rw [hμ_eq]
      congr 1; ext ω
      simp only [Nat.cast_one, mul_one]
      exact (Real.rpow_natCast _ 4).symm
    rw [h_lhs_eq]
    have h_coeff : ((4:ℝ) - 1) ^ ((4:ℝ) * ↑(1:ℕ) / 2) = 9 := by
      simp only [Nat.cast_one, mul_one]
      rw [show (4:ℝ) / 2 = ↑(2:ℕ) from by norm_num, Real.rpow_natCast]
      norm_num
    have h_exp_eq' : (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4:ℝ) / 2) =
        (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by
      rw [show (4:ℝ) / 2 = ↑(2:ℕ) from by norm_num, Real.rpow_natCast]
    have h_int_2_eq : ∫ ω, |ω g| ^ (2 * 1) ∂(GaussianField.measure T) =
        ∫ ω, (ω g) ^ 2 ∂μ_GFF := by
      rw [hμ_eq]; congr 1; ext ω; simp [sq_abs]
    have h_hyper' : ∫ ω, |ω g| ^ ((4:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T) ≤
        ((4:ℝ) - 1) ^ ((4:ℝ) * ↑(1:ℕ) / 2) *
        (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4:ℝ) / 2) := by
      have := h_hyper
      rwa [h_int_2_eq] at this
    calc ∫ ω, |ω g| ^ ((4:ℝ) * ↑(1:ℕ)) ∂(GaussianField.measure T)
        ≤ ((4:ℝ) - 1) ^ ((4:ℝ) * ↑(1:ℕ) / 2) *
          (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ ((4:ℝ) / 2) := h_hyper'
      _ = 9 * (∫ ω, (ω g) ^ 2 ∂μ_GFF) ^ 2 := by
          rw [h_coeff, h_exp_eq']
      _ ≤ 9 * Cg ^ 2 := by
          apply mul_le_mul_of_nonneg_left
          · exact pow_le_pow_left₀ h_second_nn h_second_le 2
          · norm_num
  -- Step 5: Combine
  have h_fourth_nn : (0:ℝ) ≤ ∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF :=
    integral_nonneg fun ω => by positivity
  have h_4th_bound : (∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) ≤
      3 * Cg := by
    rw [h_int_rpow_eq]
    calc (∫ ω, ((ω g) ^ 2) ^ 2 ∂μ_GFF) ^ (1/2:ℝ)
        ≤ (9 * Cg ^ 2) ^ (1/2:ℝ) :=
          Real.rpow_le_rpow h_fourth_nn h_fourth_le (by norm_num : (0:ℝ) ≤ 1/2)
      _ = 3 * Cg := by
          rw [show (9:ℝ) = 3 ^ 2 from by norm_num, ← mul_pow]
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq
            (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hCg_pos.le)]
  have hK_sqrt : K ^ (1/2:ℝ) = Real.sqrt K :=
    (Real.sqrt_eq_rpow K).symm
  calc ∫ ω, (ω g) ^ 2 ∂μ_int
      ≤ K ^ (1/2:ℝ) * (∫ ω, (fun ω => (ω g) ^ 2) ω ^ (2:ℝ) ∂μ_GFF) ^ (1/2:ℝ) := h_dt
    _ ≤ K ^ (1/2:ℝ) * (3 * Cg) :=
        mul_le_mul_of_nonneg_left h_4th_bound (Real.rpow_nonneg hK_pos.le _)
    _ = Real.sqrt K * (3 * Cg) := by rw [hK_sqrt]
    _ = 3 * Real.sqrt K * Cg := by ring

/-- Tightness of the asymmetric torus interacting measures.

The family `{μ_{P,N} : N ≥ 1}` is tight on `Configuration(AsymTorusTestFunction Lt Ls)`.
Follows from the uniform second moment bound via Mitoma-Chebyshev. -/
theorem asymTorus_interacting_tightness
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∀ (ε : ℝ), 0 < ε → ∃ (K : Set (Configuration (AsymTorusTestFunction Lt Ls))),
    IsCompact K ∧ ∀ (N : ℕ) [NeZero N],
    ENNReal.ofReal (1 - ε) ≤
      (asymTorusInteractingMeasure Lt Ls N P mass hmass) K := by
  intro ε hε
  -- Apply Mitoma-Chebyshev with ι = {N : ℕ // 0 < N}
  obtain ⟨K, hK_compact, hK_bound⟩ := configuration_tight_of_uniform_second_moments
    (ι := {N : ℕ // 0 < N})
    (fun ⟨N, hN⟩ => haveI : NeZero N := ⟨by omega⟩;
      asymTorusInteractingMeasure Lt Ls N P mass hmass)
    (fun ⟨N, hN⟩ => by haveI : NeZero N := ⟨by omega⟩; infer_instance)
    (fun f ⟨N, hN⟩ => by
      haveI : NeZero N := ⟨by omega⟩
      -- Push through Measure.map to reduce to lattice integrability
      change Integrable (fun ω => (ω f) ^ 2) (asymTorusInteractingMeasure Lt Ls N P mass hmass)
      unfold asymTorusInteractingMeasure
      rw [integrable_map_measure
        ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
        (asymTorusEmbedLift_measurable Lt Ls N).aemeasurable]
      -- Rewrite composition using asymTorusEmbedLift_eval_eq
      have h_eq : (fun ω => (ω f) ^ 2) ∘ (asymTorusEmbedLift Lt Ls N) =
          fun ω => (ω (asymLatticeTestFn Lt Ls N f)) ^ 2 := by
        ext ω; simp [Function.comp, asymTorusEmbedLift_eval_eq Lt Ls N f ω]
      rw [h_eq]
      -- Now show: Integrable (fun ω => (ω g)²) (interactingLatticeMeasure ...)
      set g := asymLatticeTestFn Lt Ls N f
      set μ_GFF := latticeGaussianMeasure 2 N (asymGeomSpacing Lt Ls N) mass
        (asymGeomSpacing_pos Lt Ls N) hmass
      set bw := boltzmannWeight 2 N P (asymGeomSpacing Lt Ls N) mass
      obtain ⟨B, hB⟩ := interactionFunctional_bounded_below 2 N P
        (asymGeomSpacing Lt Ls N) mass (asymGeomSpacing_pos Lt Ls N) hmass
      have hZ := partitionFunction_pos 2 N P (asymGeomSpacing Lt Ls N) mass
        (asymGeomSpacing_pos Lt Ls N) hmass
      -- Step 1: Reduce to withDensity measure
      suffices h : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
          (ω g) ^ 2)
          (μ_GFF.withDensity (fun ω => ENNReal.ofReal (bw ω))) by
        unfold interactingLatticeMeasure
        exact h.smul_measure (ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr hZ).ne'))
      -- Step 2: Use integrable_withDensity_iff
      have hf_meas : Measurable (fun ω : Configuration (FinLatticeField 2 N) =>
          ENNReal.ofReal (bw ω)) :=
        ENNReal.measurable_ofReal.comp
          ((interactionFunctional_measurable 2 N P (asymGeomSpacing Lt Ls N) mass).neg.exp)
      apply (integrable_withDensity_iff hf_meas
        (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
      -- Simplify toReal ∘ ofReal
      have hbw_simp : ∀ ω : Configuration (FinLatticeField 2 N),
          (ENNReal.ofReal (bw ω)).toReal = bw ω :=
        fun ω => ENNReal.toReal_ofReal
          (le_of_lt (boltzmannWeight_pos 2 N P (asymGeomSpacing Lt Ls N) mass ω))
      simp_rw [hbw_simp]
      -- Goal: Integrable (fun ω => (ω g)^2 * bw ω) μ_GFF
      have h_sq_int : Integrable (fun ω : Configuration (FinLatticeField 2 N) =>
          (ω g) ^ 2) μ_GFF :=
        (pairing_memLp (latticeCovariance 2 N (asymGeomSpacing Lt Ls N) mass
          (asymGeomSpacing_pos Lt Ls N) hmass) g 2).integrable_sq
      apply (h_sq_int.mul_const (Real.exp B)).mono
      · exact ((configuration_eval_measurable g).pow_const 2).aestronglyMeasurable.mul
          (Measurable.aestronglyMeasurable
            (interactionFunctional_measurable 2 N P (asymGeomSpacing Lt Ls N) mass).neg.exp)
      · exact Filter.Eventually.of_forall fun ω => by
          simp only [Real.norm_eq_abs]
          have h1 : 0 ≤ (ω g) ^ 2 := sq_nonneg _
          have h2 : 0 < bw ω :=
            boltzmannWeight_pos 2 N P (asymGeomSpacing Lt Ls N) mass ω
          have h3 : bw ω ≤ Real.exp B := by
            change Real.exp (-interactionFunctional 2 N P (asymGeomSpacing Lt Ls N) mass ω)
              ≤ Real.exp B
            exact Real.exp_le_exp_of_le (by linarith [hB ω])
          rw [abs_of_nonneg (mul_nonneg h1 (le_of_lt h2)),
              abs_of_nonneg (mul_nonneg h1 (le_of_lt (Real.exp_pos B)))]
          exact mul_le_mul_of_nonneg_left h3 h1)
    (fun f => by
      obtain ⟨C, _, hC_bound⟩ := asymTorus_interacting_second_moment_uniform Lt Ls P mass hmass f
      exact ⟨C, fun ⟨N, hN⟩ => by haveI : NeZero N := ⟨by omega⟩; exact hC_bound N⟩)
    ε hε
  refine ⟨K, hK_compact, fun N inst => ?_⟩
  -- Convert from .toReal to ENNReal.ofReal form
  have h_toReal := hK_bound ⟨N, Nat.pos_of_ne_zero (NeZero.ne N)⟩
  haveI : IsProbabilityMeasure (asymTorusInteractingMeasure Lt Ls N P mass hmass) :=
    asymTorusInteractingMeasure_isProbability Lt Ls N P mass hmass
  have h_lt_top : (asymTorusInteractingMeasure Lt Ls N P mass hmass) K < ⊤ :=
    measure_lt_top _ _
  calc ENNReal.ofReal (1 - ε)
      ≤ ENNReal.ofReal ((asymTorusInteractingMeasure Lt Ls N P mass hmass) K).toReal :=
        ENNReal.ofReal_le_ofReal h_toReal
    _ = (asymTorusInteractingMeasure Lt Ls N P mass hmass) K :=
        ENNReal.ofReal_toReal h_lt_top.ne

/-- **Existence of the asymmetric torus interacting continuum limit.**

There exists a subsequence along which the interacting measures converge
weakly to a probability measure on `Configuration(AsymTorusTestFunction Lt Ls)`.

This is the UV limit of Route B' (N → ∞ with Lt, Ls fixed). -/
theorem asymTorusInteractingLimit_exists
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∃ (μ : Measure (Configuration (AsymTorusTestFunction Lt Ls)))
      (_ : IsProbabilityMeasure μ)
      (φ : ℕ → ℕ) (_ : StrictMono φ),
    ∀ (f : Configuration (AsymTorusTestFunction Lt Ls) → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ ω, f ω ∂(asymTorusInteractingMeasure Lt Ls (φ n + 1) P mass hmass))
          atTop (nhds (∫ ω, f ω ∂μ)) := by
  let ν : ℕ → Measure (Configuration (AsymTorusTestFunction Lt Ls)) :=
    fun n => asymTorusInteractingMeasure Lt Ls (n + 1) P mass hmass
  -- Apply Prokhorov's theorem
  obtain ⟨φ, μ, hφ_mono, hμ_prob, hconv⟩ := prokhorov_configuration ν
    (fun n => asymTorusInteractingMeasure_isProbability Lt Ls (n + 1) P mass hmass)
    (fun ε hε => by
      obtain ⟨K, hK_compact, hK_bound⟩ :=
        asymTorus_interacting_tightness Lt Ls P mass hmass ε hε
      -- Convert ENNReal bound to toReal bound
      refine ⟨K, hK_compact, fun n => ?_⟩
      haveI : IsProbabilityMeasure (ν n) :=
        asymTorusInteractingMeasure_isProbability Lt Ls (n + 1) P mass hmass
      have h_lt_top : ν n K < ⊤ := measure_lt_top _ _
      have h_ennreal := hK_bound (n + 1)
      -- ENNReal.ofReal (1-ε) ≤ ν n K, need 1-ε ≤ (ν n K).toReal
      by_cases h1ε : 1 - ε ≤ 0
      · exact le_trans h1ε (ENNReal.toReal_nonneg)
      · push_neg at h1ε
        rwa [← ENNReal.ofReal_toReal h_lt_top.ne,
             ENNReal.ofReal_le_ofReal_iff (ENNReal.toReal_nonneg)] at h_ennreal)
  exact ⟨μ, hμ_prob, φ, hφ_mono, hconv⟩

end Pphi2

end
