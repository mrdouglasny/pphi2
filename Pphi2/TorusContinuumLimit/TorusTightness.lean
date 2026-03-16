/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tightness of Torus Gaussian Measures

Shows that the family of continuum-embedded Gaussian measures
`{ν_{GFF,N}}_{N ≥ 1}` is tight on Configuration(TorusTestFunction L).

## Main results

- `torus_second_moment_uniform` — `∫ (ω f)² dν_{GFF,N} ≤ C` uniformly in N
- `configuration_tight_of_uniform_second_moments` — (axiom) Mitoma-Chebyshev criterion
- `torusContinuumMeasures_tight` — (proved) tightness from uniform second moments

## Mathematical background

### Tightness on the torus vs S'(ℝ^d)

The torus approach makes tightness significantly easier than on S'(ℝ^d):
- **Finite volume**: The torus T²_L is compact, so there is no IR contribution
  to the Riemann sum bounds.
- **Mitoma criterion on compact spaces**: For measures on the dual of a nuclear
  Fréchet space over a compact base, tightness of 1D marginals suffices.
- **1D marginals are Gaussian**: Each `(ev_f)_* ν_{GFF,N}` is N(0, σ²_N) with
  σ²_N ≤ C uniformly (from `torusEmbeddedTwoPoint_uniform_bound`).

## References

- Mitoma (1983), "Tightness of probabilities on C([0,1]; S') and D([0,1]; S')"
- Simon, *The P(φ)₂ Euclidean QFT*, §V.1
-/

import Pphi2.TorusContinuumLimit.TorusPropagatorConvergence
import GaussianField.Tightness

noncomputable section

open GaussianField MeasureTheory

namespace Pphi2

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Uniform second moment bounds -/

/-- **Uniform bound on torus Gaussian second moments.**

  `∫ (ω f)² dν_{GFF,N} ≤ C(f, L, m)` uniformly in N ≥ 1

This is a direct consequence of `torusEmbeddedTwoPoint_uniform_bound`. -/
theorem torus_second_moment_uniform (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N],
    ∫ ω : Configuration (TorusTestFunction L),
      (ω f) ^ 2 ∂(torusContinuumMeasure L N mass hmass) ≤ C := by
  obtain ⟨C, hC_pos, hC_bound⟩ := torusEmbeddedTwoPoint_uniform_bound L mass hmass f
  refine ⟨C, hC_pos, fun N _ => ?_⟩
  have : ∫ ω : Configuration (TorusTestFunction L),
      (ω f) ^ 2 ∂(torusContinuumMeasure L N mass hmass) =
    torusEmbeddedTwoPoint L N mass hmass f f := by
    congr 1; ext ω; ring
  rw [this]
  exact hC_bound N

/-! ## Mitoma-Chebyshev tightness criterion

Imported from `GaussianField.Tightness` (gaussian-field repo).
The theorem `configuration_tight_of_uniform_second_moments` is now proved
(modulo 2 sorry's: BaireSpace instance + lower semicontinuity via Fatou). -/

/-! ## Tightness of torus Gaussian measures -/

/-- **Tightness of the torus-embedded Gaussian measures.**

The family `{ν_{GFF,N}}_{N ≥ 1}` is tight on Configuration(TorusTestFunction L).

**Proof**: Apply `configuration_tight_of_uniform_second_moments` with
`ι = {N : ℕ // 0 < N}` and the uniform second moment bounds from
`torus_second_moment_uniform`. The nuclearity hypothesis is satisfied by
`DyninMityaginSpace (TorusTestFunction L)` (from `NuclearTensorProduct`),
and the Polish/Borel instances by `configuration_torus_polish`/`borelSpace`.

Reference: Mitoma (1983), Simon §V.1. -/
theorem torusContinuumMeasures_tight
    (mass : ℝ) (hmass : 0 < mass) :
    ∀ ε : ℝ, 0 < ε →
    ∃ (K : Set (Configuration (TorusTestFunction L))),
      IsCompact K ∧
      ∀ (N : ℕ) [NeZero N],
      1 - ε ≤ (torusContinuumMeasure L N mass hmass K).toReal := by
  intro ε hε
  -- Apply Mitoma-Chebyshev with ι = {N : ℕ // 0 < N}
  obtain ⟨K, hK_compact, hK_bound⟩ := configuration_tight_of_uniform_second_moments
    (ι := {N : ℕ // 0 < N})
    (fun ⟨N, hN⟩ => haveI : NeZero N := ⟨by omega⟩;
      torusContinuumMeasure L N mass hmass)
    (fun ⟨N, hN⟩ => by haveI : NeZero N := ⟨by omega⟩; exact inferInstance)
    (fun f ⟨N, hN⟩ => by  -- integrability of (ω f)² w.r.t. torus Gaussian
      haveI : NeZero N := ⟨by omega⟩
      -- torusContinuumMeasure = map torusEmbedLift (latticeGaussianMeasure ...)
      -- Push through Measure.map to reduce to lattice integrability
      change Integrable (fun ω => (ω f) ^ 2) (torusContinuumMeasure L N mass hmass)
      unfold torusContinuumMeasure
      rw [integrable_map_measure
        ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
        (torusEmbedLift_measurable L N).aemeasurable]
      -- Goal: Integrable ((fun ω => (ω f) ^ 2) ∘ torusEmbedLift L N) (latticeGaussianMeasure ...)
      -- Rewrite using torusEmbedLift_eval_eq: (torusEmbedLift L N ω) f = ω (latticeTestFn L N f)
      have h_eq : (fun ω => (ω f) ^ 2) ∘ (torusEmbedLift L N) =
          fun ω => (ω (latticeTestFn L N f)) ^ 2 := by
        ext ω; simp [Function.comp, torusEmbedLift_eval_eq L N f ω]
      rw [h_eq]
      -- (ω g)² is integrable under the lattice Gaussian = GaussianField.measure T
      exact (pairing_memLp (latticeCovariance 2 N (circleSpacing L N) mass
        (circleSpacing_pos L N) hmass) (latticeTestFn L N f) 2).integrable_sq)
    (fun f => by
      obtain ⟨C, _, hC_bound⟩ := torus_second_moment_uniform L mass hmass f
      exact ⟨C, fun ⟨N, hN⟩ => by haveI : NeZero N := ⟨by omega⟩; exact hC_bound N⟩)
    ε hε
  exact ⟨K, hK_compact, fun N inst => hK_bound ⟨N, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩

end Pphi2

end
