/-!
# Sobolev Prokhorov Replacement Plan

This file records the implementation plan for replacing
`prokhorov_configuration_sequential` with a proof pipeline through a Polish
weighted Sobolev space.

Current status:
- `continuumLimit` uses `prokhorov_configuration_sequential` (axiom).
- We keep that axiom for now so the main development can continue.
- The items below define the intended theorem-level API for later work.

## Strategy

1. Build a weighted negative Sobolev Hilbert space `Hws` and a measurable/continuous
   map from configuration space into `Hws`.
2. Prove free Gaussian weighted Sobolev moments.
3. Transfer moments to interacting measures via Holder/Cauchy-Schwarz + exponential
   moment control + partition-function lower bound.
4. Convert uniform moment bounds into tightness on `Hws` using Markov/Chebyshev.
5. Use compact embedding from a stronger weighted Sobolev space into a weaker one
   to get compact sets for Prokhorov.
6. Apply the already-proved `prokhorov_sequential` on the Polish target space.
7. Pull back/push forward convergence to obtain the desired configuration-space
   subsequential weak limit theorem.

## Scope Notes

- On `R^2`, unweighted negative Sobolev balls are not compact enough for tightness
  (mass can drift to spatial infinity). Weighted spaces are the intended fix.
- The most expensive prerequisites are functional-analytic infrastructure:
  weighted Sobolev definitions, compact embeddings, and compatibility with the
  project's `Configuration` model.
- This file intentionally contains no declarations yet (no new axioms/sorries).

## Proposed Theorem Signatures (for future implementation)

The signatures below are intentionally comments to preserve the current axiom
count while giving a concrete implementation target.

```lean
-- 1. Space/model setup
theorem configuration_to_weightedSobolev_continuous
    (d : Nat) :
    Continuous (configurationToWeightedSobolev (d := d))

theorem configuration_to_weightedSobolev_measurable
    (d : Nat) :
    Measurable (configurationToWeightedSobolev (d := d))

-- 2. Free Gaussian moment bounds
theorem freeGaussian_weightedSobolev_moment
    (d : Nat) (p : Nat) :
    Integrable (fun ω =>
      ‖configurationToWeightedSobolev (d := d) ω‖ ^ (2 * p))
      (freeGaussianMeasure d)

-- 3. Interaction controls
theorem partitionFunction_lower_bound
    (d N : Nat) (P : InteractionPolynomial) (mass : Real)
    (hmass : 0 < mass) :
    ∃ c : Real, 0 < c ∧
      ∀ a : Real, 0 < a → c ≤ partitionFunction d N P a mass

theorem interacting_weightedSobolev_moment_uniform
    (d N : Nat) (P : InteractionPolynomial) (mass : Real)
    (hmass : 0 < mass) (p : Nat) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ a : Real, 0 < a → a ≤ 1 →
        ∫ ω, ‖configurationToWeightedSobolev (d := d) ω‖ ^ p
          ∂(continuumMeasure d N P a mass ‹0 < a› hmass) ≤ C

-- 4. Tightness in a Polish weighted Sobolev space
theorem continuumMeasures_tight_weightedSobolev
    (d N : Nat) (P : InteractionPolynomial) (mass : Real)
    (hmass : 0 < mass) :
    ∀ ε : Real, 0 < ε →
      ∃ K : Set (WeightedNegativeSobolev d),
        IsCompact K ∧
        ∀ a : Real, 0 < a → a ≤ 1 →
          1 - ε ≤
            ((Measure.map (configurationToWeightedSobolev (d := d))
                (continuumMeasure d N P a mass ‹0 < a› hmass)) K).toReal

-- 5. Sequential extraction in weighted Sobolev target
theorem continuum_subseq_limit_weightedSobolev
    (d N : Nat) (P : InteractionPolynomial) (mass : Real)
    (hmass : 0 < mass)
    (a : Nat → Real) (ha_pos : ∀ n, 0 < a n) (ha_le : ∀ n, a n ≤ 1)
    (ha_lim : Tendsto a atTop (nhds 0)) :
    ∃ (φ : Nat → Nat) (νH : Measure (WeightedNegativeSobolev d)),
      StrictMono φ ∧ IsProbabilityMeasure νH ∧
      (∀ f : WeightedNegativeSobolev d → Real, Continuous f →
        (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n =>
          ∫ x, f x ∂(Measure.map (configurationToWeightedSobolev (d := d))
            (continuumMeasure d N P (a (φ n)) mass (ha_pos (φ n)) hmass)))
          atTop (nhds (∫ x, f x ∂νH)))

-- 6. Lift back to configuration-space convergence
theorem prokhorov_configuration_sequential_from_weightedSobolev
    (d N : Nat) :
    prokhorov_configuration_sequential (d := d)
```

-/

namespace Pphi2.ContinuumLimit

end Pphi2.ContinuumLimit
