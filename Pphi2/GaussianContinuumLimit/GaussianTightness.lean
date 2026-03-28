/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tightness of Embedded Gaussian Measures

Shows that the family of continuum-embedded Gaussian measures
`{ν_{GFF,a}}_{a ∈ (0,1]}` is tight in S'(ℝ^d).

## Main results

- `gaussian_second_moment_uniform` — `∫ (ω f)² dν_{GFF,a} ≤ C` uniformly
- `gaussianContinuumMeasures_tight` — tightness via uniform second moments

## Mathematical background

### Uniform moment bounds

The embedded two-point function satisfies `E[Φ_a(f)²] ≤ C(f,m)` uniformly
in a (from `embeddedTwoPoint_uniform_bound`). This is the Gaussian core
that the interacting case builds on via Cauchy-Schwarz density transfer.

### Mitoma criterion for tightness on S'

Mitoma's theorem (1983) reduces tightness of measures on S'(ℝ^d) to
tightness of the 1D projections: a family {ν_α} on S' is tight iff
for each f ∈ S, the pushforward measures {(ev_f)_* ν_α} are tight on ℝ.

For the Gaussian measures, the 1D marginals are N(0, σ²_α) with
σ²_α = E[Φ_α(f)²] ≤ C uniformly. A Gaussian N(0, σ²) with σ² ≤ C
satisfies P(|X| > R) ≤ 2e^{-R²/2C}, so tightness on ℝ is immediate.

Equicontinuity in f follows from the Schwartz seminorm bound on the
discretized L² norm.

## References

- Mitoma (1983), "Tightness of probabilities on C([0,1]; S') and D([0,1]; S')"
- Simon, *The P(φ)₂ Euclidean QFT*, §V.1
-/

import Pphi2.GaussianContinuumLimit.PropagatorConvergence
import GaussianField.Tightness
import SchwartzNuclear.HermiteNuclear

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (d N : ℕ) [NeZero N] [Fact (0 < d)]

/-! ## Uniform second moment bounds -/

/-- **Uniform bound on Gaussian second moments.**

  `∫ (ω f)² dν_{GFF,a} ≤ C(f, m)` uniformly in a ∈ (0, 1] and N

This is a direct consequence of `embeddedTwoPoint_uniform_bound`:
the embedded two-point function `E[Φ_a(f)²]` is uniformly bounded.

This provides the Gaussian core for the interacting tightness:
the Cauchy-Schwarz density transfer in `Hypercontractivity.lean`
reduces the interacting second moment to this Gaussian bound. -/
theorem gaussian_second_moment_uniform (mass : ℝ) (hmass : 0 < mass)
    (f : ContinuumTestFunction d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∫ ω : Configuration (ContinuumTestFunction d),
      (ω f) ^ 2 ∂(gaussianContinuumMeasure d N a mass ha hmass) ≤ C := by
  -- Rewrite the integral as embeddedTwoPoint d N a mass ha hmass f f,
  -- then apply the uniform bound.
  obtain ⟨C, hC_pos, hC_bound⟩ := embeddedTwoPoint_uniform_bound d N mass hmass f
  refine ⟨C, hC_pos, fun a ha ha_le => ?_⟩
  -- ∫ (ω f)² = ∫ ω(f) * ω(f) = embeddedTwoPoint ... f f
  have : ∫ ω : Configuration (ContinuumTestFunction d),
      (ω f) ^ 2 ∂(gaussianContinuumMeasure d N a mass ha hmass) =
    embeddedTwoPoint d N a mass ha hmass f f := by
    congr 1; ext ω; ring
  rw [this]
  exact hC_bound a ha ha_le

/-! ## Tightness of Gaussian continuum measures -/

/-- Integrability of evaluation-squared through the lattice embedding.

The key fact: `(latticeEmbedLift ω) f = ω(g_f)` where
`g_f = a^d • Σ_x evalAtSite(f, x) • e_x` is a lattice test function,
so `((latticeEmbedLift ω) f)² = ω(g_f)²`, which is integrable by
`pairing_product_integrable` for the Gaussian measure. -/
private theorem gaussianContinuumMeasure_sq_integrable
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : ContinuumTestFunction d) :
    Integrable (fun ω : Configuration (ContinuumTestFunction d) =>
      (ω f) ^ 2) (gaussianContinuumMeasure d N a mass ha hmass) := by
  unfold gaussianContinuumMeasure
  apply (integrable_map_measure
    ((configuration_eval_measurable f).aestronglyMeasurable.pow 2)
    (latticeEmbedLift_measurable d N a ha).aemeasurable).mpr
  set T := latticeCovariance d N a mass ha hmass
  set g_f : FinLatticeField d N :=
    a ^ d • ∑ x : FinLatticeSites d N,
      evalAtSite d N a f x • Pi.single x (1 : ℝ)
  -- The goal has Pi-level power: ((fun ω => ω f) ^ 2) ∘ lift
  -- Show this equals fun ω => (ω g_f) * (ω g_f)
  show Integrable
    (((fun ω : Configuration (ContinuumTestFunction d) =>
        ω f) ^ 2) ∘ latticeEmbedLift d N a ha)
    (latticeGaussianMeasure d N a mass ha hmass)
  have h_congr :
      (((fun ω : Configuration (ContinuumTestFunction d) =>
          ω f) ^ 2) ∘ latticeEmbedLift d N a ha) =
      fun ω => (ω g_f) * (ω g_f) := by
    ext ω; simp only [Function.comp, Pi.pow_apply]
    have : (latticeEmbedLift d N a ha ω) f = ω g_f := by
      simp only [latticeEmbedLift, latticeEmbed_eval, latticeEmbedEval,
        g_f, map_smul, map_sum, smul_eq_mul]
      congr 1; apply Finset.sum_congr rfl; intro x _; ring
    rw [this, sq]
  rw [h_congr]
  exact pairing_product_integrable T g_f g_f

theorem gaussianContinuumMeasures_tight
    (mass : ℝ) (hmass : 0 < mass) :
    ∀ ε : ℝ, 0 < ε →
    ∃ (K : Set (Configuration (ContinuumTestFunction d))),
      IsCompact K ∧
      ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 →
      1 - ε ≤ (gaussianContinuumMeasure d N a mass ha hmass K).toReal := by
  intro ε hε
  -- Provide DyninMityaginSpace instance for the Schwartz test function space.
  -- For d ≥ 1, this is the Hermite-function basis instance.
  -- For d = 0, the space S(ℝ⁰) ≅ ℝ is trivially a DM space but the
  -- formalized instance requires Nontrivial, which fails for Fin 0.
  have hd : 0 < d := Fact.out
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  haveI : Nontrivial (EuclideanSpace ℝ (Fin d)) := inferInstance
  haveI : DyninMityaginSpace (ContinuumTestFunction d) :=
    schwartz_dyninMityaginSpace
  set ι := { a : ℝ // 0 < a ∧ a ≤ 1 }
  set μ : ι → Measure (Configuration (ContinuumTestFunction d)) :=
    fun i => gaussianContinuumMeasure d N i.val mass i.prop.1 hmass
  have hprob : ∀ i : ι, IsProbabilityMeasure (μ i) :=
    fun i => gaussianContinuumMeasure_isProbability d N
      i.val mass i.prop.1 hmass
  have h_int :
      ∀ (f : ContinuumTestFunction d) (i : ι),
      Integrable (fun ω : Configuration (ContinuumTestFunction d) =>
        (ω f) ^ 2) (μ i) :=
    fun f i => gaussianContinuumMeasure_sq_integrable d N
      i.val mass i.prop.1 hmass f
  have h_moments :
      ∀ f : ContinuumTestFunction d, ∃ C : ℝ, ∀ i : ι,
      ∫ ω : Configuration (ContinuumTestFunction d),
        (ω f) ^ 2 ∂(μ i) ≤ C := by
    intro f
    obtain ⟨C, _, hC⟩ :=
      gaussian_second_moment_uniform d N mass hmass f
    exact ⟨C, fun i => hC i.val i.prop.1 i.prop.2⟩
  obtain ⟨K, hK_compact, hK_mass⟩ :=
    configuration_tight_of_uniform_second_moments
      μ hprob h_int h_moments ε hε
  exact ⟨K, hK_compact,
    fun a ha ha_le => hK_mass ⟨a, ha, ha_le⟩⟩

end Pphi2

end
