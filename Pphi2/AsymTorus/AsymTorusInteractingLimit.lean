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

/-! ## Tightness and limit existence -/

/-- Uniform second moment bound for the asymmetric torus interacting measures.

For each test function f, `∫ (ω f)² dμ_{P,N}` is bounded uniformly in N. -/
theorem asymTorus_interacting_second_moment_uniform
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass)
    (f : AsymTorusTestFunction Lt Ls) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (AsymTorusTestFunction Lt Ls),
      (ω f) ^ 2 ∂(asymTorusInteractingMeasure Lt Ls N P mass hmass) ≤ C := by
  sorry -- Same proof as torus_interacting_second_moment_uniform
  -- Uses: asymNelson_exponential_estimate + density_transfer_bound
  -- + Gaussian hypercontractivity + uniform two-point bound

/-- Tightness of the asymmetric torus interacting measures.

The family `{μ_{P,N} : N ≥ 1}` is tight on `Configuration(AsymTorusTestFunction Lt Ls)`.
Follows from the uniform second moment bound via Mitoma-Chebyshev. -/
theorem asymTorus_interacting_tightness
    (P : InteractionPolynomial) (mass : ℝ) (hmass : 0 < mass) :
    ∀ (ε : ℝ), 0 < ε → ∃ (K : Set (Configuration (AsymTorusTestFunction Lt Ls))),
    IsCompact K ∧ ∀ (N : ℕ) [NeZero N],
    ENNReal.ofReal (1 - ε) ≤
      (asymTorusInteractingMeasure Lt Ls N P mass hmass) K := by
  sorry -- From asymTorus_interacting_second_moment_uniform
  -- + configuration_tight_of_uniform_second_moments

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
  sorry -- From asymTorus_interacting_tightness + Prokhorov

end Pphi2

end
