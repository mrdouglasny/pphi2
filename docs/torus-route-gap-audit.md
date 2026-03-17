# Torus Route Gap Audit

Date: 2026-03-17

This note records the current state of the torus continuum-limit route after
reading the repo sources, not just the README prose.

## Short answer

The torus route is buildable, but it is not completely finished in the sense
claimed by the README.

- `torusInteractingLimit_exists` is not fully closed.
- Torus interacting `OS0`-`OS2` are not fully axiom-free.
- The README currently overstates completion.

## Documentation mismatch

The README contradicts itself.

- It claims Route B has `0 axioms, 0 sorry` and that all torus `OS0`-`OS2`
  are fully proved.
- Later it says Route B still has `1 axiom, 1 sorry`.

Relevant lines:

- `README.md:67-73`
- `README.md:175-188`

`status.md` is closer to the source state and still lists active torus axioms:

- `status.md:65-69`

## What is actually finished

These torus files build:

- `Pphi2.TorusContinuumLimit.TorusInteractingLimit`
- `Pphi2.TorusContinuumLimit.TorusOSAxioms`
- `Pphi2.TorusContinuumLimit.TorusInteractingOS`

But the successful build still reports transitive `sorry` usage in upstream
dependencies, so "builds" does not mean "fully closed".

## Gaps

### 1. Interacting limit existence still depends on a non-closed tightness input

`torusInteractingLimit_exists` is proved in
`Pphi2/TorusContinuumLimit/TorusInteractingLimit.lean`, but its tightness step
uses `configuration_tight_of_uniform_second_moments`.

Relevant lines:

- `Pphi2/TorusContinuumLimit/TorusInteractingLimit.lean:344-457`
- `Pphi2/TorusContinuumLimit/TorusTightness.lean:13`
- `Pphi2/TorusContinuumLimit/TorusTightness.lean:69-70`

So the interacting limit is only as closed as that Mitoma-Chebyshev criterion.

### 2. Interacting OS0 still depends on a local complex-analysis axiom

`torusInteracting_os0` uses `analyticOnNhd_integral`:

- `Pphi2/TorusContinuumLimit/TorusInteractingOS.lean:2618-2634`

That theorem depends on the local axiom `osgood_separately_analytic`:

- `Pphi2/GeneralResults/ComplexAnalysis.lean:71-76`

So interacting OS0 is not fully formalized end-to-end.

### 3. Interacting OS2 depends on two upstream `sorry`s in torus evaluation

The torus interacting translation proof uses:

- `Pphi2/TorusContinuumLimit/TorusInteractingOS.lean:352-365`

The time-reflection proof uses:

- `Pphi2/TorusContinuumLimit/TorusInteractingOS.lean:2070-2081`

Those depend directly on upstream theorems that still contain `sorry`:

- `.lake/packages/GaussianField/Torus/Evaluation.lean:123-135`
- `.lake/packages/GaussianField/Torus/Evaluation.lean:149-161`

These are:

- `evalTorusAtSite_timeReflection`
- `evalTorusAtSite_latticeTranslation`

So the torus interacting symmetry proofs are not fully closed.

### 4. Gaussian torus OS is also not axiom-free

The Gaussian torus OS file still contains:

- `Pphi2/TorusContinuumLimit/TorusOSAxioms.lean:268-276`

This is the axiom:

- `torusGeneratingFunctionalℂ_analyticOnNhd`

That axiom is used in the Gaussian OS0 proof chain:

- `Pphi2/TorusContinuumLimit/TorusOSAxioms.lean:287-319`

So even the Gaussian torus OS route is not fully finished.

### 5. Gaussian uniqueness still inherits an upstream `sorry`

The torus Gaussian limit uses `gaussian_measure_unique_of_covariance`, which
ultimately relies on upstream `pushforward_eq_of_eval_eq`.

Relevant lines:

- `Pphi2/TorusContinuumLimit/TorusGaussianLimit.lean:768-783`
- `.lake/packages/GaussianField/GaussianField/MeasureUniqueness.lean:205-215`

`pushforward_eq_of_eval_eq` is still `sorry`, so this uniqueness step is not
fully closed either.

### 6. Route B OS2 is weaker than the project-wide OS2 on `R^2`

On the torus, "OS2" is split into translation invariance plus `D4` point-group
invariance, not full Euclidean invariance on `R^2`.

Definitions:

- `Pphi2/TorusContinuumLimit/TorusOSAxioms.lean:505-510`
- `Pphi2/TorusContinuumLimit/TorusOSAxioms.lean:515-520`

So the README wording can easily be read too strongly if it is compared with the
main `OSAxioms.lean` notion of Euclidean invariance.

### 7. The interacting torus OS file is not imported by the umbrella module

`Pphi2.lean` imports:

- `TorusEmbedding`
- `TorusPropagatorConvergence`
- `TorusTightness`
- `TorusConvergence`
- `TorusGaussianLimit`
- `TorusInteractingLimit`
- `TorusOSAxioms`

but not:

- `TorusInteractingOS`

Relevant lines:

- `Pphi2.lean:37-44`

So the interacting torus OS results are not wired into the main umbrella import.

## Bottom line

The current torus-route status is:

- Interacting limit existence: partially closed, but still depends on a
  non-closed tightness criterion.
- Interacting OS0: not fully closed.
- Interacting OS1: locally much stronger, but still sits on the incomplete
  existence/tightness stack.
- Interacting OS2: not fully closed because of upstream torus-evaluation
  `sorry`s.
- Gaussian torus OS0: not fully closed because of the analytic-functional axiom.
- Gaussian uniqueness: not fully closed because of upstream measure-uniqueness
  `sorry`.

So the torus route is best described as advanced and buildable, but not
completely finished.
