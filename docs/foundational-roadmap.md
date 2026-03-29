# Foundations Roadmap

This note records how to turn the existing `P(Φ)₂` formalization into a more
foundational library without overclaiming what has been formalized.

The current project already proves a serious theorem: a constructive bosonic
scalar Euclidean field theory in the Glimm-Jaffe/Nelson framework, realized as
a positive probability measure on `S'(ℝ²)` satisfying OS0-OS4. That theorem
should be preserved and clarified, not downgraded.

What the recent discussions make clear is different:

- A positive-measure Euclidean model is not the same thing as a general QFT.
- The original Osterwalder-Schrader axioms are stated for Schwinger functions,
  not directly for probability measures.
- The Euclidean-to-Minkowski passage is not automatic from bare Schwinger data:
  the original OS reconstruction needs extra growth hypotheses such as the 1975
  linear-growth conditions `E0'` / `E0''`.
- Gauge, topological, finite-density, and fermionic settings may fail to admit a
  positive-measure formulation even when they still have meaningful Euclidean or
  Minkowski correlation data.

The right response is therefore not to abandon formalization, but to formalize
the distinctions themselves.

## Formulation layers

The repository should separate four layers of Euclidean QFT data.

1. `MeasureModel`
   A concrete positive probability measure on a configuration space, with
   generating functionals obtained by integration. This is the natural layer for
   Glimm-Jaffe/Nelson `P(Φ)₂`.

2. `TensorSchwingerModel`
   Moments or Schwinger functions on simple tensors `f₁ ⊗ ... ⊗ fₙ`, encoded as
   tuples of one-point test functions. This is weaker than a full OS Schwinger
   theory and should not be silently identified with it.

3. `DistributionalSchwingerModel`
   Genuine `n`-point Schwinger functions on an `n`-point test-function space.
   This is the level closest to the original OS axioms. Unlike the measure and
   simple-tensor layers, this requires explicit linear/topological test-function
   structure; the shared library should therefore use a stronger
   `SchwingerFormulation` interface here rather than overloading the bare
   one-point `Formulation`.

4. `ReconstructionInput`
   Extra hypotheses needed to run reconstruction, such as linear-growth
   conditions. This layer is where the hard Euclidean-to-Minkowski subtlety
   lives and should remain explicit. The hypothesis should appear as a named
   predicate on the Schwinger package, not as an anonymous bare `Prop`.

These layers are now scaffolded in
`Common/QFT/Euclidean/Formulations.lean`, with the backend-independent
linear-growth / reconstruction-rule surfaces factored separately into
`Common/QFT/Euclidean/ReconstructionInterfaces.lean`.

## Immediate refactor program

1. Extract shared formulation interfaces from `Phi4/OSAxioms.lean` into
   `Common/QFT`.
   `Phi4` already contains a more abstract Schwinger/OS interface than `Pphi2`.
   That abstraction should become shared infrastructure instead of staying
   project-local.
   Current state: `Phi4/FormulationAdapter.lean` now exposes the tensor-Schwinger
   layer using only the infinite-volume infrastructure that already builds in
   this repo. The stronger distributional-Schwinger / reconstruction adapter is
   kept in-tree but outside the active `Phi4.lean` umbrella until an external
   `OSReconstruction` backend is intentionally wired in and version-aligned.

2. Recast `Pphi2/OSAxioms.lean` as a measure-level adapter.
   `Pphi2` should remain the canonical example of a strong positive-measure
   construction, but it should export its results into the shared Schwinger /
   reconstruction interfaces instead of defining "the" OS framework by itself.
   In particular, do not add a generic `PairingMeasureModel -> TensorSchwinger`
   constructor without explicit measurability / moment-integrability input:
   that bridge is mathematically nontrivial even in scalar theories.

3. Compare theories at the Schwinger level first, not the measure level first.
   Literal equality of probability measures is a very strong notion of
   equivalence specialized to scalar positive-measure theories. The primary
   comparison object should be Schwinger data, with measure equality as a
   downstream corollary under determinacy hypotheses.

4. Formalize the reconstruction hypotheses explicitly.
   A gold-standard library should not state "OS implies Wightman" without also
   recording which extra hypothesis is actually being used in a given theorem:
   original OS 1975 growth input, a later equivalent condition, or a stronger
   project-specific replacement.

5. Keep positivity notions separate.
   Probability-measure positivity, reflection positivity, and Hilbert-space
   positivity after reconstruction are related, but they are not the same
   mathematical object. Separating them is essential for any later gauge or
   fermionic extension.

## Knowledge-advancing milestones

The following milestones would make the project more meaningful even to experts
skeptical of "formalized QFT" as a slogan.

- Prove `MeasureModel -> TensorSchwingerModel -> DistributionalSchwingerModel`
  for the current scalar theories, rather than leaving these identifications
  informal.
- Isolate the exact reconstruction input used in each route (torus, cylinder,
  plane), especially where analyticity or linear-growth bounds enter.
- Document explicitly which physically interesting settings fail at the
  `MeasureModel` layer but may still fit the later layers.
- Use a non-measure-first benchmark after `P(Φ)₂`, rather than jumping directly
  to Yang-Mills rhetoric. Good candidates include free fermionic or
  gauge-invariant observable interfaces, and eventually the `O(3)` sigma model
  as a formulation stress test.
- Keep a separate research branch for enlarged test-function frameworks
  (hyperfunctions or related variants) if they clarify reconstruction, but do
  not make them part of the core until the comparison maps are understood.

## What this changes in practice

This roadmap does not repudiate the current scalar construction. It changes the
question the repository is answering.

Old question:
"How much of a constructive scalar measure-based QFT can be formalized?"

Better question:
"What is the minimal formal interface that can host multiple Euclidean and
Minkowski formulations, together with explicit comparison theorems between
them?"

Answering the second question would make the current work legible not only as a
completed constructive theorem, but as the first well-understood instance of a
broader foundations program.
