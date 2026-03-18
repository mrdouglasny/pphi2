# Torus Route Gap Audit

Date: 2026-03-17

This note records the current state of the torus continuum-limit route after
reading the repo sources, not just the README or `status.md` prose.

## Short answer

The torus route is buildable, and the active Route B path currently appears
closed with respect to explicit axioms and `sorry`s in the imported torus
files.

- `torusInteractingLimit_exists` is backed by a proved tightness theorem.
- `TorusInteractingOS.lean` is locally closed.
- `TorusOSAxioms.lean` now has a theorem `torusGeneratingFunctionalℂ_analyticOnNhd`,
  not an axiom.
- The remaining problems are primarily documentation drift, plus some inactive
  torus-side files that still contain `sorry`.

## Documentation mismatch

After merging the latest `origin/main`, the source state improved in two real
ways:

- the torus-evaluation `sorry`s in gaussian-field are gone
- `Pphi2.lean` now imports `TorusInteractingOS`

The top-level prose is now stale in the opposite direction: the source has
moved ahead of the docs.

- The README is correct that `TorusInteractingOS.lean` has `0 local axioms,
  0 sorry`, but its bullet list of remaining upstream gaps is now stale.
- `status.md` also has a stale Route B gap summary.

Relevant lines:

- `README.md:67-73`
- `status.md:14-21`
- `status.md:69-78`

In particular, the docs still mention:

- `evalTorusAtSite_timeReflection` / `evalTorusAtSite_latticeTranslation`
  as `sorry`s, but those are now proved
- `torusGeneratingFunctionalℂ_analyticOnNhd` as an axiom, but it is now a theorem

## What is actually finished

These torus files build:

- `Pphi2.TorusContinuumLimit.TorusInteractingLimit`
- `Pphi2.TorusContinuumLimit.TorusOSAxioms`
- `Pphi2.TorusContinuumLimit.TorusInteractingOS`

The targeted Route B build now succeeds without `sorry` warnings in
`ComplexAnalysis.lean`, `TorusOSAxioms.lean`, or `TorusInteractingOS.lean`.

## Resolved since the previous audit

Earlier blockers that are now resolved:

- `.lake/packages/GaussianField/Torus/Evaluation.lean` no longer has the
  `evalTorusAtSite_timeReflection` / `evalTorusAtSite_latticeTranslation`
  `sorry`s.
- `Pphi2.lean` now imports `Pphi2.TorusContinuumLimit.TorusInteractingOS`.
- `ComplexAnalysis.lean` now imports `OsgoodN` and `osgood_separately_analytic`
  is a theorem.
- `TorusOSAxioms.lean` now proves `torusGeneratingFunctionalℂ_analyticOnNhd`.

## Gaps

### 1. Tightness is not a blocker

`torusInteractingLimit_exists` is proved in
`Pphi2/TorusContinuumLimit/TorusInteractingLimit.lean`, but its tightness step
uses `configuration_tight_of_uniform_second_moments`.

Relevant lines:

- `Pphi2/TorusContinuumLimit/TorusInteractingLimit.lean:344-457`
- `Pphi2/TorusContinuumLimit/TorusTightness.lean:69-70`
- `.lake/packages/GaussianField/GaussianField/Tightness.lean:744`

`configuration_tight_of_uniform_second_moments` is a theorem in gaussian-field,
not an axiom. The only remaining issue here is documentation drift in
`TorusTightness.lean`, whose header/comments are stale.

### 2. Osgood is no longer a blocker

`torusInteracting_os0` uses `analyticOnNhd_integral`:

- `Pphi2/TorusContinuumLimit/TorusInteractingOS.lean:2618-2634`

`ComplexAnalysis.lean` now imports `OsgoodN` and its
`osgood_separately_analytic` is a theorem, not an axiom:

- `Pphi2/GeneralResults/ComplexAnalysis.lean:43`
- `Pphi2/GeneralResults/ComplexAnalysis.lean:69-75`
- `Pphi2/GeneralResults/Osgood/OsgoodN.lean:1057`

`block_osgood_series` in `OsgoodN.lean` is also now a theorem, not an axiom.
So the Osgood part of the analyticity chain is no longer a blocker.

### 3. Gaussian torus OS0 no longer has the old analyticity axiom

`torusGeneratingFunctionalℂ_analyticOnNhd` is now a theorem in
`TorusOSAxioms.lean`:

- `Pphi2/TorusContinuumLimit/TorusOSAxioms.lean:427`

This was previously one of the main blockers. It is now resolved.

### 4. Gaussian uniqueness is no longer a blocker in the torus route

There is a local, sorry-free proof in:

- `Pphi2/TorusContinuumLimit/MeasureUniqueness.lean:204`
- `Pphi2/TorusContinuumLimit/MeasureUniqueness.lean:337`

`Pphi2/TorusContinuumLimit/MeasureUniqueness.lean` defines the theorem in the
`GaussianField` namespace, so the call site in `TorusGaussianLimit.lean`
resolves to this local replacement:

- `Pphi2/TorusContinuumLimit/TorusGaussianLimit.lean:768-783`

The upstream gaussian-field file still has a `sorry`, but the torus route does
not depend on that upstream version anymore.

### 5. Remaining torus-side `sorry`s are outside the active Route B path

`rg` still finds `sorry` in:

- `Pphi2/TorusContinuumLimit/TorusNuclearBridge.lean`

But `TorusNuclearBridge.lean` is not imported by `Pphi2.lean`, so these do not
currently block the active torus Route B development path.

### 6. Route B OS2 is weaker than the project-wide OS2 on `R^2`

On the torus, "OS2" is split into translation invariance plus `D4` point-group
invariance, not full Euclidean invariance on `R^2`.

Definitions:

- `Pphi2/TorusContinuumLimit/TorusOSAxioms.lean:505-510`
- `Pphi2/TorusContinuumLimit/TorusOSAxioms.lean:515-520`

So the README wording can easily be read too strongly if it is compared with the
main `OSAxioms.lean` notion of Euclidean invariance.

## Bottom line (updated 2026-03-17)

The active torus Route B path is **essentially complete**:

- Interacting limit existence: **closed.**
- Interacting OS0: **closed.** Osgood proved (1965 lines), Gaussian integrability proved (AM-GM).
- Interacting OS1: **closed.**
- Interacting OS2: **closed** (torus symmetries; `evalTorusAtSite` sorrys resolved in gaussian-field).
- Gaussian torus OS0: **closed.** `torusGeneratingFunctionalℂ_analyticOnNhd` is a theorem.
- Gaussian uniqueness: **closed** (local replacement in `MeasureUniqueness.lean`).

The only remaining transitive dependency is `configuration_tight_of_uniform_second_moments`
(a theorem in gaussian-field, not an axiom). All sorrys and axioms in the active
torus path (`ComplexAnalysis.lean`, `TorusOSAxioms.lean`, `TorusInteractingOS.lean`)
are resolved.
