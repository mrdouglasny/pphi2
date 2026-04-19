# pphi2

Formal construction of the P(Φ)₂ Euclidean quantum field theory in Lean 4,
following the Glimm-Jaffe/Nelson lattice approach.

## What this project proves

**Main theorem** (`Pphi2/Main.lean`): For any even polynomial P of degree ≥ 4
bounded below and any mass m > 0, there exists a probability measure μ on the
space of tempered distributions S'(ℝ²) satisfying all five Osterwalder-Schrader
axioms:

- **OS0 (Analyticity):** The generating functional Z[Σ zᵢJᵢ] is entire analytic
  in z ∈ ℂⁿ.
- **OS1 (Regularity):** ‖Z[f]‖ ≤ exp(c(‖f‖₁ + ‖f‖ₚᵖ)) for some 1 ≤ p ≤ 2.
- **OS2 (Euclidean Invariance):** Z[g·f] = Z[f] for all g ∈ E(2) = ℝ² ⋊ O(2).
- **OS3 (Reflection Positivity):** The RP matrix Σᵢⱼ cᵢcⱼ Re(Z[fᵢ − Θfⱼ]) ≥ 0.
- **OS4 (Clustering):** Z[f + Tₐg] → Z[f]·Z[g] as ‖a‖ → ∞.

By the Osterwalder-Schrader reconstruction theorem, this yields a relativistic
Wightman QFT in 1+1 Minkowski spacetime with a positive mass gap.

This is the theorem originally proved by Glimm-Jaffe (1968–1973), Nelson (1973),
and Simon, with contributions from Guerra-Rosen-Simon and others.

## Scope and foundations direction

This repository currently formalizes one specific Euclidean-QFT formulation:
the Glimm-Jaffe/Nelson construction of a positive probability measure on
`S'(ℝ²)` for bosonic scalar `P(Φ)₂`. It does not yet formalizes gauge fields,
fermions, chemical potential, or topological terms.

A framework for defining QFTs on general spacetimes
(compact manifolds, lattices, manifolds with boundary) with separated spacetime
geometry and field content is a WIP. An exploratory organizational proposal is in
[`docs/foundational-roadmap.md`](docs/foundational-roadmap.md), with a
technical reference for the current formulation-layer code in
[`docs/formulation-layer.md`](docs/formulation-layer.md) and open design
questions (general manifolds, multiple fields, fermions, signed/complex
measures) in
[`docs/formulation-layer-questions.md`](docs/formulation-layer-questions.md).

## Proof approach

The construction proceeds in six phases:

1. **Lattice measure** — Define the Wick-ordered interaction
   V_a(φ) = a² Σ_x :P(φ(x)):_a on the finite lattice (ℤ/Nℤ)² and construct
   the interacting measure μ_a = (1/Z_a) exp(−V_a) dμ_{GFF,a}.

2. **Transfer matrix** — Decompose the lattice action into time slices. The
   transfer matrix T is a positive trace-class operator. This gives reflection
   positivity (OS3).

3. **Spectral gap** — Show T has a spectral gap (λ₀ > λ₁) by Perron-Frobenius.
   This gives the mass gap and exponential clustering (OS4).

4. **Continuum limit** — Embed lattice measures into S'(ℝ²), prove tightness
   (Mitoma + Nelson's hypercontractive estimate), extract a convergent
   subsequence by Prokhorov. OS0, OS1, OS3, OS4 transfer to the limit.
   The free (Gaussian) case is handled separately in `GaussianContinuumLimit/`:
   the lattice GFF measures are tight (Mitoma criterion with uniform m⁻²
   second-moment bound from the spectral gap of −Δ_a + m²), their weak
   limits are Gaussian (Bochner-Minlos), and the covariance converges to
   the continuum Green's function G(f,g) = ∫ f̂(k)ĝ(k)/(|k|²+m²) dk/(2π)².

5. **Euclidean invariance** — Restore full E(2) symmetry via a Ward identity
   argument. The rotation-breaking operator has scaling dimension 4 > d = 2,
   so the anomaly is RG-irrelevant and vanishes as O(a²) in the continuum limit.
   Super-renormalizability ensures no logarithmic corrections.

6. **Assembly** — Combine all axioms into the main theorem.

## Four routes (spacetimes)

The construction is carried out on four spacetimes, each targeting different
OS axioms. See [ROUTES.md](ROUTES.md) for the detailed comparison.

### Route A: ℝ² (Euclidean plane) — OS0–OS4
The full construction targets S'(ℝ²) and proves all five OS axioms.
The continuum limit involves both UV (a → 0) and IR (volume → ∞) limits.
**22 axioms, 0 sorries** (pphi2) + **3 axioms** (gaussian-field) = **25 combined**.

### Route B: T²_L (symmetric torus) — OS0–OS2
Finite-volume warm-up isolating the UV limit. Lattice (ℤ/Nℤ)² with
spacing a = L/N → 0. The interacting continuum limit `torusInteractingLimit_exists`
is proved via Mitoma-Chebyshev tightness + Nelson's exponential estimate
(proved: physical volume a²N²=L² is constant). OS3 dropped (→ Routes B', C).

**`TorusInteractingOS.lean`: 0 local axioms, 0 sorry.**
All OS0–OS2 proofs are complete within this file. Upstream dependencies
are now largely resolved (see `docs/torus-route-gap-audit.md`):
- ~~OS0 uses `osgood_separately_analytic` (axiom)~~ **PROVED** — Osgood's lemma fully verified (1965 lines, 0 axioms)
- ~~Gaussian OS0 uses `torusGeneratingFunctionalℂ_analyticOnNhd` (axiom)~~ **PROVED** — Gaussian integrability via AM-GM induction
- ~~OS2 time reflection uses `evalTorusAtSite_timeReflection` (sorry)~~ **PROVED** in gaussian-field
- ~~OS2 lattice translation uses `evalTorusAtSite_latticeTranslation` (sorry)~~ **PROVED** in gaussian-field
- Limit existence uses `configuration_tight_of_uniform_second_moments` (theorem in gaussian-field)

See `docs/torus-interacting-os-proof.md` for the proof overview.

### Route B': T_{Lt,Ls} → S¹_{Ls} × ℝ (asymmetric torus → cylinder) — OS0–OS3
Extends Route B to the cylinder by taking the time direction to infinity.
The construction proceeds in two limits:

1. **UV limit (DONE):** On the asymmetric torus T_{Lt,Ls} = (ℝ/Lt ℤ) × (ℝ/Ls ℤ)
   with lattice (ℤ/Nℤ)² and geometric-mean spacing √(Lt·Ls)/N, take N → ∞.
   Route B's OS0–OS2 proofs are fully adapted to the asymmetric case.
   `AsymTorusOS.lean`: **0 axioms, 0 sorry.**

2. **IR limit (in progress):** Take Lt → ∞ with Ls fixed. The torus measures
   μ_{P,Lt,Ls} on T_{Lt,Ls} converge weakly to a measure μ_{P,Ls} on the
   cylinder S¹_{Ls} × ℝ. Tightness follows from uniform-in-Lt moment bounds
   via the **method of images** (gaussian-field `Cylinder/MethodOfImages.lean`).
   The IR limit files are in `IRLimit/` with 4 axioms and 0 sorries.
   `limit_exponential_moment` (MCT + truncation) is now fully proved.
   OS2 (time reflection) of the limit measure is **proved** via characteristic
   functional convergence.

The cylinder S¹_{Ls} × ℝ has a natural time axis ℝ, enabling:
- **OS3 (Reflection positivity):** Time reflection Θ: t ↦ -t is a clean
  involution on S¹_{Ls} × ℝ. The RP matrix for positive-time test functions
  is positive semidefinite, proved from the lattice RP (transfer matrix
  positivity) + weak limit transfer.
- **Transfer matrix:** The cylinder admits a Hilbert space decomposition
  L²(S¹_{Ls}) via spatial slicing at fixed time. The transfer operator
  T = exp(-H) where H is the P(φ)₂ Hamiltonian. Spectral gap of T
  gives the mass gap and clustering.

**Advantages over Route C:** Reuses all Route B infrastructure (0 axioms for
OS0–OS2). Only needs new work for OS3 (RP) and the Lt → ∞ limit.
**Status:** UV limit (Step 1) complete — `AsymTorusOS.lean` has **0 axioms,
0 sorry** for OS0–OS2. Cylinder IR limit (Step 2) in progress — `IRLimit/` has
**4 axioms, 0 sorries**. `limit_exponential_moment` (MCT + truncation + BC convergence)
is now fully proved. OS2 time reflection is proved via characteristic-functional
convergence, and compact-support, finite-rank, and general cylinder covariance
convergence are proved against a global physically normalized cylinder form
obtained from `cylinderGreen` by explicit temporal `2π` rescaling, with uniform
bilinear seminorm control of the embedded torus covariance family. Spatial
translation is exact at each finite `Lt`; what remains axiomatized in the IR
lane is the uniform second-moment bound, uniform exponential moment, and OS0/OS3.

### Route C: S¹_L × ℝ (cylinder, direct) — OS0–OS3
Direct Nelson/Simon construction with natural time axis ℝ for OS reconstruction.
The field is a distribution (not a function), requiring isonormal Gaussian extension.
OS3 uses Laplace factorization of the cylinder Green's function.
**21 axioms + 0 sorries** (preserved in `future/`, not in active build).

### Which OS axiom comes from which route?
| OS axiom | Best route | Why |
|----------|-----------|-----|
| OS0 (Analyticity) | B, B' | Exponential moment bounds (proved) |
| OS1 (Regularity) | B, B' | Clean moment bounds (proved) |
| OS2 (Symmetry) | B' or A | B' for cylinder symmetries, A for full E(2) |
| OS3 (RP) | B' or C | Natural time half-space on cylinder |
| OS4 (Clustering) | B' or A | Transfer matrix spectral gap |

## Construction parameters and renormalization

The construction takes two inputs:

- **P** (`InteractionPolynomial`) — an even polynomial of degree ≥ 4, bounded below.
  Examples: P(τ) = λτ⁴, P(τ) = λτ⁴ + μτ², P(τ) = (τ²−a²)⁴.
  P may have a nonzero quadratic coefficient; the physical mass receives
  contributions from both the Gaussian mass and the quadratic term in P.

- **mass** (`mass : ℝ`, `0 < mass`) — the mass parameter in the Gaussian
  reference measure, whose covariance is (−Δ_a + mass²)⁻¹. This must be
  strictly positive so the lattice operator is invertible (the zero mode
  has eigenvalue mass²). This is a technical requirement for the Gaussian
  reference measure, not a physical restriction on the theory.

The expansion is always around φ = 0, but this does not force the theory
into the symmetric phase. An even polynomial can have its global minima at
±a ≠ 0 (e.g. P(τ) = (τ²−a²)⁴); the functional integral determines which
phase the theory is in.

**Renormalization:** P(Φ)₂ is super-renormalizable in d = 2. The only UV
counterterm is the Wick ordering constant c_a = G_a(0,0) ~ (1/2π)log(1/a),
which is the lattice propagator at coinciding points. The Wick-ordered
interaction :P(φ(x)):_a subtracts the divergent self-contractions at each
lattice spacing. No mass, coupling constant, or wave function
renormalization is needed beyond Wick ordering.

## Consistency checks

Beyond the OS axioms themselves, the construction should satisfy additional
consistency checks:

- **Mass reparametrization invariance.** The physical measure depends on the
  total action, not on how it is split between the Gaussian reference measure
  and the interaction. Shifting the bare mass m → m' while compensating
  P → P + m²/2 − (m')²/2 leaves the total quadratic term (−Δ + m²) + P
  unchanged, so the resulting continuum measure must be identical.

- **Wick ordering scheme independence.** The Wick ordering constant
  c_a = G_a(0,0) depends on the bare mass m through the propagator. A mass
  shift changes c_a, but the compensating shift in P absorbs this, so the
  Wick-ordered interaction :P(φ):_a is scheme-independent up to the total
  action.

- **Torus–infinite volume consistency.** For test functions supported well
  inside T²_L (away from the boundary identification), the torus and
  infinite-volume Schwinger functions should agree in the L → ∞ limit.

## Current status

All six phases are structurally complete and the full project builds
(`lake build`).

- **pphi2:** 22 axioms, 0 sorries in the active build; `continuumMeasures_tight` (Route A tightness on S'(ℝ^d)) ported from the torus pipeline (Mitoma-Chebyshev + `interacting_moment_bound` + `gaussian_second_moment_uniform`); `cylinderIR_os0` (OS0 analyticity) proved via `analyticOnNhd_integral` + exponential moment transfer; Route C's 21 axioms remain preserved in `future/`
- **Route B (torus):** 0 axioms, 0 sorries — the most developed route
- **Route B' IR limit:** 3 axioms, 5 sorries — OS0 analyticity proved from uniform exponential moments + BC weak convergence; what remains is the uniform second-moment bound, uniform exponential moment, and OS3
- **Shared foundations layer:** `Common/QFT/Euclidean/Formulations.lean` and
  `Common/QFT/Euclidean/ReconstructionInterfaces.lean` separate concrete
  measure models, tensor-moment Schwinger data, distributional Schwinger data,
  explicit reconstruction hypotheses, and backend-independent reconstruction rules

The torus continuum limit (`TorusContinuumLimit/`) provides a cleaner alternative
to the S'(ℝ^d) approach: by fixing the physical volume L and taking only N→∞,
the UV limit is isolated from IR issues. Prokhorov extraction on the Polish
torus configuration space is **proved** (not axiomatized). The same pipeline
handles both Gaussian and interacting (P(φ)₂) measures via Cauchy-Schwarz
density transfer. The torus Gaussian continuum limit satisfies OS axioms
OS0–OS3 (`TorusOSAxioms.lean`), with OS0 (analyticity), OS1 (regularity),
OS2 (translation + D4 invariance), and OS3 (reflection positivity) **proved**.
OS0 uses `exp ∘ (quadratic polynomial)` analyticity via Mathlib. OS3 uses the
matrix/generating-functional form matching `OSAxioms.lean`, with
positive-time test function support; the proof transfers lattice RP through
weak limits via `torusMatrixRP_of_weakLimit`.

See [status.md](status.md) for a complete inventory of all axioms and sorries,
organized by difficulty and priority.

For [Convergence.lean](Pphi2/ContinuumLimit/Convergence.lean),
`prokhorov_configuration_sequential` is now a **proved theorem** using
gaussian-field's `prokhorov_configuration` (which embeds Configuration into
ℕ → ℝ via the DM basis, avoiding Polish/Borel). The old axiomatized
Polish/Borel instances were removed as inconsistent. See
[SobolevProkhorovPlan.lean](Pphi2/ContinuumLimit/SobolevProkhorovPlan.lean).

## Nontrivial infrastructure notes

- **Configuration-space Prokhorov bridge**:
  [SobolevProkhorovPlan.lean](Pphi2/ContinuumLimit/SobolevProkhorovPlan.lean)
  records the staged theorem API to replace
  `prokhorov_configuration_sequential`.
- **Transfer-matrix spectral infrastructure (Jentzsch)**:
  [Jentzsch.lean](Pphi2/TransferMatrix/Jentzsch.lean) contains the
  positivity-improving/Perron-Frobenius spectral input used for mass-gap-level
  statements.
- **Convolution operator infrastructure**:
  [L2Convolution.lean](Pphi2/TransferMatrix/L2Convolution.lean) centralizes
  Young-type analytic dependencies for `L²` convolution operators.
- **Global inventory and difficulty tracking**:
  [status.md](status.md) and [docs/axiom_proof_plans.md](docs/axiom_proof_plans.md).

## File structure

```
Pphi2/
  Polynomial.lean                    -- Interaction polynomial P(τ)
  WickOrdering/                      -- Phase 1: Wick monomials and counterterms
  InteractingMeasure/                -- Phase 1: Lattice action and measure
  TransferMatrix/                    -- Phase 2-3: Transfer matrix, positivity, spectral gap
    L2Multiplication.lean            -- Multiplication operator M_w on L²
    L2Convolution.lean               -- Convolution operator Conv_G on L² (Young's inequality)
    L2Operator.lean                  -- Transfer operator T = M_w ∘ Conv_G ∘ M_w
    Jentzsch.lean                    -- Jentzsch's theorem, Perron-Frobenius spectral properties
  OSProofs/
    OS3_RP_Lattice.lean              -- Phase 2: Reflection positivity on the lattice
    OS3_RP_Inheritance.lean          -- Phase 2: RP closed under weak limits
    OS4_MassGap.lean                 -- Phase 3: Clustering from spectral gap
    OS4_Ergodicity.lean              -- Phase 3: Ergodicity from mass gap
    OS2_WardIdentity.lean            -- Phase 5: Ward identity for rotation invariance
  OSforGFF/                          -- Matrix positivity library (from OSforGFF)
    PositiveDefinite.lean            -- Positive definite functions
    FrobeniusPositivity.lean         -- Frobenius inner product positivity
    SchurProduct.lean                -- Schur (Hadamard) product theorem
    HadamardExp.lean                 -- Entrywise exponential preserves PSD/PD
    TimeTranslation.lean             -- Schwartz space time translation continuity
  ContinuumLimit/                    -- Phase 4: Embedding, tightness, convergence
    Hypercontractivity.lean          -- Nelson's estimate (Option A: Cauchy-Schwarz density transfer)
  GaussianContinuumLimit/            -- Phase 4G: Free GFF continuum limit (reusable infrastructure)
    EmbeddedCovariance.lean          -- gaussianContinuumMeasure, embeddedTwoPoint, continuumGreenBilinear
    PropagatorConvergence.lean       -- Lattice propagator → continuum Green's function; uniform bound
    GaussianTightness.lean           -- Tightness of {ν_{GFF,a}} via Mitoma criterion
    GaussianLimit.lean               -- Existence + Gaussianity of the limit; IsGaussianContinuumLimit
  TorusContinuumLimit/               -- Phase 4T: Torus continuum limit (UV only, L fixed)
    TorusEmbedding.lean              -- torusEmbedLift, torusContinuumMeasure, Green's function
    TorusPropagatorConvergence.lean  -- Lattice → continuum eigenvalues, uniform bound, positivity
    TorusTightness.lean              -- Tightness via Mitoma on torus (finite volume)
    TorusConvergence.lean            -- Prokhorov extraction (PROVED, not axiomatized)
    TorusGaussianLimit.lean          -- Gaussian identification, IsTorusGaussianContinuumLimit
    TorusInteractingLimit.lean       -- P(φ)₂ tightness + existence (Cauchy-Schwarz transfer)
  GeneralResults/
    FunctionalAnalysis.lean          -- Pure Mathlib results: Cesàro, Schwartz Lp, trig identity
  OSAxioms.lean                      -- Phase 6: OS axiom definitions (matching OSforGFF)
  FormulationAdapter.lean            -- Exports `Pphi2` to the shared formulation interfaces
  Main.lean                          -- Phase 6: Main theorem assembly
  Bridge.lean                        -- Bridge between pphi2 and Phi4 approaches
Common/
  QFT/Euclidean/Formulations.lean    -- Shared formulation layers: measure / Schwinger / reconstruction input
  QFT/Euclidean/ReconstructionInterfaces.lean -- Backend-independent linear-growth / reconstruction interfaces
```

## Dependencies

- [gaussian-field](https://github.com/mrdouglasny/gaussian-field) — Gaussian
  free field on nuclear spaces, lattice field theory, FKG inequality
- [Mathlib](https://github.com/leanprover-community/mathlib4) — Lean 4
  mathematics library

## Building

Requires Lean 4. gaussian-field is a git dependency (fetched automatically).

```bash
git clone https://github.com/mrdouglasny/pphi2.git
cd pphi2
lake build
```

### Continuous integration

Pull requests and pushes to `main` run [GitHub Actions](.github/workflows/ci.yml)
using [leanprover/lean-action](https://github.com/leanprover/lean-action): install
the toolchain from `lean-toolchain`, optionally `lake exe cache get` for Mathlib,
then `lake build`. Workflow YAML is checked with [actionlint](.github/workflows/actionlint.yml).
[Dependabot](.github/dependabot.yml) proposes weekly updates for action versions.

## Documentation

### Expository
- [docs/construction-overview.md](docs/construction-overview.md) —
  End-to-end overview of the six-phase construction, from lattice to QFT
- [docs/wick-ordering.md](docs/wick-ordering.md) — Wick ordering,
  renormalization, and why only one counterterm is needed
- [docs/nuclear-spaces-and-measures.md](docs/nuclear-spaces-and-measures.md) —
  Nuclear spaces, the Gel'fand triple, and Gaussian measure construction
- [docs/transfer-matrix-and-mass-gap.md](docs/transfer-matrix-and-mass-gap.md) —
  Transfer matrix, Jentzsch's theorem, and the mass gap
- [docs/reflection-positivity.md](docs/reflection-positivity.md) —
  Reflection positivity (OS3), the perfect square argument, and OS
  reconstruction
- [docs/hypercontractivity.md](docs/hypercontractivity.md) — Why
  hypercontractivity is needed and how it transfers Gaussian estimates to
  the interacting measure
- [docs/tightness-and-weak-convergence.md](docs/tightness-and-weak-convergence.md) —
  Tightness, weak convergence, Prokhorov's theorem, and uniqueness of
  the limit

### Technical
- [status.md](status.md) — Complete axiom/sorry inventory with difficulty
  ratings and priority ordering
- [docs/plan.md](docs/plan.md) — Development roadmap and construction outline
- [docs/foundational-roadmap.md](docs/foundational-roadmap.md) — Why the repo
  is being refactored around formulation layers (measure / Schwinger /
  reconstruction)
- [docs/axiom_audit.md](docs/axiom_audit.md) — Self-audit of all axioms
  (pphi2 + gaussian-field) with correctness ratings
- [docs/mathlib_candidates.md](docs/mathlib_candidates.md) — Standard results
  suitable for Mathlib contribution (~50 across pphi2 + gaussian-field)
- [docs/gemini_review.md](docs/gemini_review.md) — External review of axioms
  with references and proof strategies
- [docs/torus_continuum_limit_plan.md](docs/torus_continuum_limit_plan.md) —
  Plan for torus OS axioms (Gaussian + interacting P(φ)₂)
- [docs/os_axioms_lattice_plan.md](docs/os_axioms_lattice_plan.md) — Design
  notes for OS axiom formulations

## References

- J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point of View*,
  Springer (1987)
- B. Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Princeton (1974)
- E. Nelson, "Construction of quantum fields from Markoff fields," *J. Funct. Anal.* (1973)
- K. Osterwalder and R. Schrader, "Axioms for Euclidean Green's functions I, II,"
  *Comm. Math. Phys.* 31 (1973), 42 (1975)

## Imported material

The files under `Pphi2/OSforGFF/` (PositiveDefinite, FrobeniusPositivity, SchurProduct,
HadamardExp) are imported from the
[OSforGFF](https://github.com/mrdouglasny/OSforGFF) project, authored by
Michael R. Douglas, Sarah Hoback, Anna Mei, and
Ron Nissim. These provide the Schur product theorem and entrywise exponential
positivity results used in the OS3 reflection positivity proof.

## Related work

- Xi Yin, [Phi4](https://github.com/xiyin137/Phi4) — Formalization of φ⁴ quantum
  field theory in Lean 4

## Future projects

- **Unified OS axiom framework.** Currently the infinite-volume OS axioms
  (`OSAxioms.lean`) and torus OS axioms (`TorusOSAxioms.lean`) are defined
  separately. These should be unified into a single parametric `SatisfiesOS`
  structure taking a `SpaceTime` parameter that encodes the geometry:
  whether space is compact (torus vs ℝ², controlling ergodicity/clustering),
  whether a distinguished time direction exists (enabling reflection positivity),
  the symmetry group (E(2) vs translations × D4), and so on. The OS axioms
  and other consistency tests (e.g. moment bounds, support properties) would
  then be stated once and instantiated for each spacetime. Both the Gaussian
  and interacting measures would be verified against the same axiom bundle.

## Author

Michael R. Douglas and collaborators

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
