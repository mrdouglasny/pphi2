# Migration Plan: `configuration_polishSpace` / `configuration_borelSpace`

This note gives concrete file skeletons and dependency edits to move the continuum-configuration topology facts from `pphi2` to `gaussian-field`.

## Goal

Move these declarations out of:
- `Pphi2/ContinuumLimit/Convergence.lean`

into `gaussian-field`, so pphi2 imports them as upstream infrastructure.

## 1. New upstream module (gaussian-field)

Create:
- `GaussianField/ConfigurationTopology.lean`

Suggested skeleton:

```lean
import GaussianField.Construction
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Metrizable.Basic

noncomputable section

open MeasureTheory

namespace GaussianField

/-- Continuum test-function space S(R^d). -/
abbrev ContinuumTestFunction (d : ℕ) :=
  SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ

/-- S'(R^d) = `Configuration (ContinuumTestFunction d)` is Polish. -/
axiom configuration_polishSpace (d : ℕ) :
  PolishSpace (Configuration (ContinuumTestFunction d))

/-- Borel structure on S'(R^d), compatible with the weak-* cylindrical structure. -/
axiom configuration_borelSpace (d : ℕ) :
  BorelSpace (Configuration (ContinuumTestFunction d))

end GaussianField
```

Then export it from:
- `GaussianField.lean`

by adding:

```lean
import GaussianField.ConfigurationTopology
```

near other `GaussianField.*` imports.

## 2. pphi2 dependency edits

In `Pphi2/ContinuumLimit/Convergence.lean`:

1. Delete local declarations:

```lean
axiom configuration_polishSpace ...
axiom configuration_borelSpace ...
```

2. Keep using the same names via `open GaussianField` (already present), or qualify explicitly:

```lean
haveI : PolishSpace (Configuration (ContinuumTestFunction d)) :=
  GaussianField.configuration_polishSpace d
haveI : BorelSpace (Configuration (ContinuumTestFunction d)) :=
  GaussianField.configuration_borelSpace d
```

No other logic changes are needed in `continuumLimit`.

## 3. Optional compatibility bridge during migration

If needed for incremental rollout, add temporary abbrev/theorem aliases in pphi2:

```lean
abbrev configuration_polishSpace := GaussianField.configuration_polishSpace
abbrev configuration_borelSpace := GaussianField.configuration_borelSpace
```

and remove them after downstream files are updated.

## 4. Longer-term proof plan in gaussian-field

Target theorem package for replacing the axioms:

1. Show `ContinuumTestFunction d = SchwartzMap (R^d) R` is nuclear Fréchet (already broadly in project scope).
2. Construct a countable family of seminorm controls yielding metrizability of the weak-* dual.
3. Prove completeness + separability of the weak-* dual model.
4. Instantiate `PolishSpace` for `Configuration (ContinuumTestFunction d)`.
5. Prove Borel/cylindrical sigma-algebra compatibility and instantiate `BorelSpace`.

This keeps topology/measure structure as reusable upstream infrastructure for all downstream QFT projects.
