# Discharge plan — 18. weak-coupling uniqueness (the coherence keystone)

**New target** identified by [`coherence-analysis.md`]. Not one of the original 17 axioms, but the
ingredient that makes their discharge *compose* into the headline "an **interacting** φ⁴₂ theory
satisfying OS exists." It simultaneously fixes coherence gaps A (interacting∧OS for one μ), B
(regime propagation), and C (subsequence → genuine limit).

## The statement

In the weak-coupling regime, the φ⁴₂ continuum/infinite-volume limit measure is **unique** —
independent of the lattice-spacing subsequence and the boundary conditions:

```
theorem pphi2_limit_unique (P : InteractionPolynomial) (mass coupling : ℝ) (hmass : 0 < mass)
    (hP : isPhi4 P coupling) (h_weak : IsWeakCoupling P mass coupling) :
    ∃! μ : Measure (Configuration (ContinuumTestFunction 2)),
      IsProbabilityMeasure μ ∧ IsPphi2Limit μ P mass
```

(`IsWeakCoupling` already exists in `Bridge.lean:178`.) Equivalently: any two Prokhorov limit
points of `(ν_{a_n})` coincide.

## Why it is the keystone

- **Gap A** (interacting ∧ OS): `pphi2_exists` gives `μ₁ ⊨ SatisfiesFullOS`; `pphi2_nontriviality`
  gives `μ₂` with `S₂>0`; `pphi2_nonGaussianity` gives `μ₃` with `u₄≠0`. All three are
  `IsPphi2Limit`-measures, so by uniqueness `μ₁ = μ₂ = μ₃ =: μ`, and the conjoined headline follows.
- **Gap B** (regime): uniqueness *holds precisely* at weak coupling — so threading `h_weak` is not
  an artificial restriction, it is the natural hypothesis the whole construction lives under.
- **Gap C** (subsequence → limit): `∃!` upgrades the Prokhorov *subsequence* extraction to genuine
  convergence of the full net.

## Discharge route

Standard constructive QFT, weak coupling:
1. **Cluster (polymer/Mayer) expansion** — Glimm–Jaffe Ch. 18; Glimm–Jaffe–Spencer (1974). At small
   `λ` the Schwinger functions are given by an absolutely convergent expansion, hence unique +
   analytic in `λ`. This is the canonical route and also yields the mass gap (axiom 17) and
   exponential clustering as by-products — **so 17 + 14/15 + 18 share the cluster-expansion engine.**
2. **Dobrushin / Dobrushin–Shlosman uniqueness** — a high-temperature (≈ weak-coupling, large mass)
   uniqueness criterion for the Gibbs specification; lighter than a full cluster expansion if only
   uniqueness (not analyticity) is needed.
3. **Correlation-inequality squeeze** — monotone (in volume) convergence via GKS/FKG forces all
   limit points to agree, without a full expansion. Most tractable if the FKG infrastructure
   (`Lattice/FKG.lean`) extends to the needed monotonicity. **Try this first** — it reuses existing
   pieces and may give uniqueness of the *continuum* limit at fixed volume cheaply.

Difficulty ★★★ (the cluster expansion is a major standalone project). Route 3 may give a partial,
cheaper uniqueness sufficient to close Gap A. Vet the route with a literature/Gemini pass first.

## Accompanying code refactor (do WITH the discharge, not before)

These edits are **gated on this keystone** and on the regime decision; doing them on the current
green build (before the keystone is provable) would only propagate hypotheses with no proof gain.
When discharging:
1. **Thread the regime.** Add `(hP : isPhi4 P coupling) (h_weak : IsWeakCoupling P mass coupling)`
   to axioms `spectral_gap_uniform` (17), `spectral_gap_lower_bound` (16), `continuumLimit_nonGaussian`
   (9), and propagate through `os4_clustering`/`os4_ergodicity` into `pphi2_exists`. (This changes
   signatures and cascades — do it as one PR.)
2. **State the conjoined headline** (the genuine result), e.g. in a new `Pphi2/InteractingQFT.lean`:
   ```
   theorem pphi2_interacting_qft_exists (P …) (hP : isPhi4 P coupling)
       (h_weak : IsWeakCoupling P mass coupling) :
       ∃ μ (hμ : IsProbabilityMeasure μ),
         SatisfiesFullOS μ ∧ (∀ f ≠ 0, 0 < S₂ μ f) ∧ (∃ f, u₄ μ f ≠ 0)
   ```
   proof: extract `μ` from `pphi2_exists`; obtain `S₂>0` / `u₄≠0` measures from 11 / 9; collapse to
   the same `μ` via `pphi2_limit_unique`; bundle. This is the statement that actually means
   "interacting φ⁴₂ QFT exists" — make it the headline, with the old `pphi2_existence` /
   `pphi2_nontriviality` / `pphi2_nonGaussianity` as corollaries.

## Status
- [ ] **18. `pphi2_limit_unique`** — ★★★; route 3 (correlation-inequality squeeze) first, cluster
  expansion if needed. Deps: the regime (16/17). Unblocks the conjoined headline + Gaps A/B/C.

References: Glimm–Jaffe Ch. 18; Glimm–Jaffe–Spencer (1974); Simon *P(φ)₂* §III; Dobrushin (1968).
