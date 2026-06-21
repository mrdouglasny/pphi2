# pphi2

Formal construction of the P(Φ)₂ Euclidean quantum field theory in Lean 4,
following the Glimm-Jaffe/Nelson lattice approach.

> **📍 The master status of the remaining-axiom discharge is
> [`planning/INDEX.md`](planning/INDEX.md)** (current). The earlier T²_L OS0–OS2 endpoint campaign
> and its five-workstream roadmap are recorded in
> [`docs/T2-master-plan.md`](docs/T2-master-plan.md) (historical).

> **🛠 Active workstream — the cylinder `S¹(L_s) × ℝ` φ⁴₂ construction** on an isotropic
> `Z_{N_t} × Z_{N_s}` lattice (single spacing `a`, `L_s = N_s·a` fixed, `N_t → ∞`): leaving the
> compact torus behind to gain **reflection positivity (OS3)** and the **mass gap / clustering
> (OS4)**, on the path to **OS reconstruction → a Wightman QFT in 1+1d**.
> `cylinderIso_OS_of_RP_OS2` (`AsymTorus/AsymContinuumLimit.lean`) assembles the cylinder
> **OS0–OS3** modulo the remaining project axioms. Build green, **0 sorries**; the debt is the
> project axioms.
>
> **📋 Master status of the remaining axioms → [`planning/INDEX.md`](planning/INDEX.md)** — a
> plan-loop status machine over all 17 axioms, grouped by OS-program cluster, with the dependency
> DAG, difficulty ratings, and a discharge plan for each. The four genuine hard cores: the
> `Lt`-uniform exponential-moment chain (Layer A + Layer B2, the latter mostly proved this cycle),
> the uniform spectral gap, non-Gaussianity (`u₄≠0`), and rotation restoration.
>
> **⚠ Read [`planning/coherence-analysis.md`](planning/coherence-analysis.md) first.** The axioms
> are individually sound but **do not yet compose into "an *interacting* φ⁴₂ QFT exists"**:
> `SatisfiesFullOS` is satisfied by the free field too, and non-triviality / non-Gaussianity are
> *separate* existence statements never conjoined with the OS measure. The keystone — **weak-coupling
> uniqueness** ([`planning/weak-coupling-uniqueness.md`](planning/weak-coupling-uniqueness.md)) —
> glues them into one measure, propagates the (necessary) weak-coupling regime, and upgrades the
> Prokhorov subsequence to a genuine limit. The honest headline is the *conjoined* theorem
> `∃ μ, SatisfiesFullOS μ ∧ (∀ f≠0, S₂>0) ∧ u₄≠0`.
>
> **Layer B1** of the remaining-axiom discharge architecture (cylinder
> transfer matrix → variance bound) is **complete** 2026-05-31:
> `AsymL2Operator.lean` (TM compactness + self-adjointness),
> `AsymJentzsch.lean` (positivity-improving + ground simple),
> `AsymPositivity.lean` (energy levels + mass gap pos),
> `AsymVarianceBound.lean` (Layer B1 variance bound).
>
> **Remaining workstreams** for the last axiom:
> - **Layer A** (Newman MGF via Lee-Yang): new `lee-yang` repo
>   scaffolded at `~/Documents/GitHub/lee-yang/`, Phase 1 not yet
>   implemented. See `lee-yang/PLAN.md`.
> - **Layer B2** (`asymInteractingVariance_le_freeVariance_Lt_uniform`,
>   Lt-uniformity): now pursued via the **transfer-matrix Feynman–Kac
>   route** (not chessboard). Much of it is **done & axiom-clean**
>   (2026-06-04): the abstract trace dictionary (merged), the φ⁴₂
>   `TransferSystem` instance (merged PR #36), the vetted energy
>   factorization, the GaussianField asym density bridge (merged
>   gaussian-field PR #3), the **measure factorization**
>   `μ_int.map sliceEquiv = pathMeasure`, the abstract **B4
>   susceptibility engine** (merged reflection-positivity PR #3), and
>   the operator↔kernel link (`asymTransferKernel_kPow_apply`). Remaining
>   tail: the **Hilbert–Schmidt trace-bridge layer** + single-slice
>   stability. See [`docs/B4B5-design.md`](docs/B4B5-design.md) and
>   [`docs/transfer-instantiation-plan.md`](docs/transfer-instantiation-plan.md).
> - **Layer C** (assembly): ~50 lines, blocked on A + B2.
>
> Roadmap docs:
> - [`docs/cylinder-master-plan.md`](docs/cylinder-master-plan.md) — campaign master plan
> - [`docs/cylinder-isotropic-lattice-redesign.md`](docs/cylinder-isotropic-lattice-redesign.md) — *why* the isotropic redesign (the metric-correctness diagnosis)
> - [`docs/cylinder-isotropic-lattice-implementation.md`](docs/cylinder-isotropic-lattice-implementation.md) — phase-by-phase build plan (Phases 1a / 1b / 2 / 3)
> - [`docs/asym-fielddecomposition-redesign.md`](docs/asym-fielddecomposition-redesign.md) — the §2 polynomial-chaos `FieldDecomposition` port with the unit-by-unit status table
> - [`docs/asym-cross-term-l2-discharge-plan.md`](docs/asym-cross-term-l2-discharge-plan.md) — the cross-term L² Wick identity discharge plan (status: ✅ DONE 2026-05-29)
> - [`docs/asym-chaos-cutoff-decomposition-discharge-plan.md`](docs/asym-chaos-cutoff-decomposition-discharge-plan.md) — UNIT 6 + UNIT 7 plan: promote `asymChaosCutoffDecomposition` axiom → theorem (~290–500 lines)
> - [`docs/cylinder-conditional-inputs-provability.md`](docs/cylinder-conditional-inputs-provability.md) — provability vetting of every conditional input the cylinder OS theorem rests on
> - [`docs/cylinder-os3-discharge-plan.md`](docs/cylinder-os3-discharge-plan.md) — the OS3 `hRP` hypothesis discharge plan

The lattice-action normalisation diagnosed in early May 2026 (a missing
`a^d` Riemann-sum prefactor on the kinetic term, identified by a
Gemini-vetted scaling analysis) was resolved and merged into `main`;
the historical fix branch is preserved as the
[`archive/fix/lattice-action-normalization`](https://github.com/mrdouglasny/pphi2/releases/tag/archive%2Ffix%2Flattice-action-normalization)
tag for reference. The Glimm–Jaffe-aligned action `S = (a^d/2) ⟨φ, M_a φ⟩`
is now the project default, with `latticeCovarianceGJ` and the matching
`gaussianDensity = exp(-(a^d/2)⟨φ, Qφ⟩)`. The OS0–OS4 chain in
`Pphi2/Main.lean` proves theorems about the textbook GJ-aligned measure.
The Stage 1 / Cluster A / Cluster B axiom inventory introduced for
the genuine uniform bounds has since been substantially discharged via
Workstream A (Phase B Glimm–Jaffe Fourier estimates, complete 2026-05-16;
both `smoothWickConstant_le_log_uniform_in_aN` and
`canonicalRoughCovariance_pow_sum_le_uniform_in_aN` are now theorems)
and Workstream C (gaussian-hilbert OU/Mehler discharge, complete
2026-05-15). The single remaining non-Mathlib axiom on the T²_L OS0–OS2
critical path is `polynomial_chaos_exp_moment_bridge` (Workstream B,
in flight; the last math blocker `wickPolynomial_lower_bound_general`
resolved 2026-05-17). For per-axiom status, plans, and the full
multi-repo roadmap, see [`docs/T2-master-plan.md`](docs/T2-master-plan.md);
for the original lattice-action diagnosis see
[`docs/lattice-action-normalization-fix.md`](docs/lattice-action-normalization-fix.md).

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

By the Osterwalder-Schrader reconstruction theorem, the corresponding
mathematical theorem in the literature yields a relativistic Wightman QFT in
1+1 Minkowski spacetime with a positive mass gap. This repository currently
formalizes the Euclidean OS side, not the reconstruction step itself.

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
   This is the lattice mass gap; OS4 on the periodic torus is phrased with **cyclic**
   Euclidean-time separation (`latticeEuclideanTimeSeparation` in `OS4_MassGap.lean`),
   and the textbook continuum clustering picture is recovered after IR/continuum limits.

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
   so the anomaly is RG-irrelevant and vanishes in the continuum limit; in the
   super-renormalizable `P(Φ)₂` setting one allows at most polynomial
   `|log a|` corrections, still multiplied by the vanishing `a²` factor.

6. **Assembly** — Combine all axioms into the main theorem.

## Four routes (spacetimes)

The construction is carried out on four spacetimes, each targeting different
OS axioms. See [ROUTES.md](ROUTES.md) for the detailed comparison.

### Route A: ℝ² (Euclidean plane) — OS0–OS4
The full construction targets S'(ℝ²) and proves all five OS axioms.
The continuum limit involves both UV (a → 0) and IR (volume → ∞) limits.
**pphi2 main: 20 real / 23 raw axioms, 0 sorries** (rechecked 2026-06-21; raw → real
reconciliation is 3 docstring matches of the word "axiom"). The `cylinder-isotropic-lattice`
branch has been merged into `main`, so the cylinder `Z_Nt × Z_Ns` construction —
including the deep-think-vetted `asymInteracting_expMoment_volume_uniform` (Layer C
assembly point) — is part of the main count. `wickConstantAsym_eq_variance` and
`asymChaosCutoffDecomposition` are now theorems; `MeasureHasGreenMomentBound` is a
theorem; `cylinderIso_OS_of_RP_OS2` gives cylinder OS0/OS1/OS2/OS3 modulo the separate
reflection-positivity and OS2-symmetry inputs (see
[`docs/cylinder-conditional-inputs-provability.md`](docs/cylinder-conditional-inputs-provability.md)
for the input-by-input provability map). Per-axiom status lives in
[`planning/INDEX.md`](planning/INDEX.md) (the master status machine); per-dependency
upstream counts (gaussian-field **3 axioms / 0 sorries**, gibbs-variational **0 axioms /
1 off-critical-path sorry**, markov-semigroups + gaussian-hilbert tracking `main`) live
in each repo's own `AXIOM_AUDIT.md` and are pinned in
[`AXIOM_AUDIT.md`](AXIOM_AUDIT.md). The Phase B Glimm-Jaffe Fourier estimates are
theorems, and `#print axioms Pphi2.rough_error_variance` shows only
`[propext, Classical.choice, Quot.sound]`.
Stage 1 lattice-action fix raised the count from 22 to 35; Phase 2
partial discharge plus PR #14 (Route B′ IR-limit refactor +
`fourierTransform_lp_eq_fourierIntegral` proof) brought it back to 24.
Cluster B is now complete: the symmetric-torus uniform-bound pair
(`torusEmbeddedTwoPoint_uniform_bound` / `torusEmbeddedTwoPoint_le_seminorm`)
and the asymmetric pair (`asymGaussian_second_moment_uniform_bound` /
`asymGf_sub_norm_le_seminorm`) are all proved, the latter via a new
GJ-aligned asym embedding `evalAsymAtFinSiteGJ := a_geom • evalAsymAtFinSite`
mirroring the symmetric `evalTorusAtSiteGJ`. Other Phase 2 discharges:
`roughCovariance_sq_summable`, `smoothVariance_le_log` (trivial-`C` form),
the gaussian-field density bridge
`normalizedGaussianDensityMeasure_eq_normalizedQuadraticGaussianMeasure`,
the GJ-aligned Gaussian Fourier identity
`normalizedGaussianDensityMeasure_linearFourier`, and
`torus_propagator_convergence_GJ`. Three additional pphi2 axioms cleared
by PR #14: `fourierTransform_lp_eq_fourierIntegral` (private),
`cylinderIR_uniform_exponential_moment`, and `cylinderIR_os3` (refactored
to consume explicit Green-moment / RP inputs).
Remaining 4 Stage 1 axioms are all in **Cluster A** (Nelson dynamical-cutoff,
Glimm–Jaffe Ch. 8) — multi-week deliverable.
All four remaining Stage 1 axioms (Cluster A) reduce to the same
Glimm–Jaffe Ch. 8 dynamical-cutoff Nelson estimate (~6-8 wk per the
Gemini estimate in `docs/lattice-action-normalization-fix.md`). The
embedding-normalisation audit on `circleRestriction` is complete
(2026-05-08).

### Route B: T²_L (symmetric torus) — OS0–OS2
Finite-volume warm-up isolating the UV limit. Lattice (ℤ/Nℤ)² with
spacing a = L/N → 0. The interacting continuum limit `torusInteractingLimit_exists`
is proved via Mitoma-Chebyshev tightness + Nelson's exponential estimate
(proved: physical volume a²N²=L² is constant). OS3 dropped (→ Routes B', C).

**`TorusInteractingOS.lean`: 0 local axioms, 0 sorries.**
(`torusEmbeddedTwoPoint_le_seminorm` was discharged 2026-05-08 via the
`(a^d)⁻¹·(L/N)² = 1` cancellation between `evalTorusAtSiteGJ` and
`latticeCovarianceGJ`.)
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
   `AsymTorusOS.lean`: **1 axiom, 0 sorries** (`asymTorusInteracting_exponentialMomentBound`,
   Cluster A; `asymGf_sub_norm_le_seminorm` was discharged 2026-05-08 via
   the new `evalAsymAtFinSiteGJ` GJ asym embedding). The remaining input
   in `AsymTorusInteractingLimit.lean` is `asymNelson_exponential_estimate`
   (also Cluster A); `asymGaussian_second_moment_uniform_bound` was
   discharged the same day via the same cancellation pattern.

2. **IR limit (in progress):** Take Lt → ∞ with Ls fixed. The torus measures
   μ_{P,Lt,Ls} on T_{Lt,Ls} converge weakly to a measure μ_{P,Ls} on the
   cylinder S¹_{Ls} × ℝ. Tightness follows from uniform-in-Lt moment bounds
   via the **method of images** (gaussian-field `Cylinder/MethodOfImages.lean`).
   The IR limit files are in `IRLimit/` with 0 local axioms and 0 sorries,
   plus explicit nonlocal inputs for eventual Green moments and eventual
   pullback reflection positivity.
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
**0 local axioms, 0 sorries**. `limit_exponential_moment` (MCT + truncation + BC convergence)
is now fully proved, and the uniform cylinder exponential moment is derived
from the explicit eventual Green-controlled torus moment hypothesis
`AsymTorusSequenceHasUniformGreenMomentBound`; stronger pointwise or `Lt ≥ 1`
tail estimates are converted to this input by proved bridge theorems. OS2 time reflection is proved via characteristic-functional
convergence, and compact-support, finite-rank, and general cylinder covariance
convergence are proved against a global physically normalized cylinder form
obtained from `cylinderGreen` by explicit temporal `2π` rescaling, with uniform
bilinear seminorm control of the embedded torus covariance family. Spatial
translation is exact at each finite `Lt`; OS3 is now transferred from the
explicit eventual pullback RP hypothesis
`CylinderMeasureSequenceEventuallyReflectionPositive`, with proved bridge
theorems from full-RP statements to the exact matrixwise eventual input.

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

> **Navigating in-flight work:** [`BRANCHES.md`](BRANCHES.md) maps the live git branches to the
> axioms they discharge (and flags superseded/dormant ones); [`planning/INDEX.md`](planning/INDEX.md)
> is the per-axiom master status machine.

All six phases are structurally complete and the full project builds
(`lake build`).

- **pphi2:** **20 real axioms, 0 sorries** in the active build (rechecked 2026-06-21;
  `count_axioms.sh` reports 23 because 3 lines are docstring matches of the word "axiom" at
  `Pphi2/NelsonEstimate/LatticeBridge.lean:21`, `Pphi2/NelsonEstimate/LayerCake.lean:85`,
  `Pphi2/AsymTorus/AsymExpMomentDischarge.lean:244`). The 20 real axioms break down as:
  - **17 architectural** — enumerated and clustered by OS-program target in
    [`planning/INDEX.md`](planning/INDEX.md), the master status machine. Highlights:
    the **CYL-1a chain** (items 1, 2, 3, 12) gates OS0/OS1, with item 3 (Layer-B2 variance bound)
    machinery built and sorry-free on `main` (remaining gap is wiring B3→B4→B5 per
    [`docs/B4B5-design.md`](docs/B4B5-design.md)); the **CYL-2a chain** (items 16, 17, 14, 15)
    gates OS4 mass-gap clustering, regime-restricted to weak coupling; **non-Gaussianity**
    (item 9, `u₄≠0`) is **DONE on T² and AXIOM-FREE** as of 2026-06-07 via Route A
    (`torus_pphi2_isInteractingStrict_weakCoupling`, PR #48 — clears one ★★★ mountain on the
    T² front).
  - **2 private scaffolding** — `asymTorusInteracting_exponentialMomentBound`
    (`AsymTorus/AsymTorusOS.lean`), `gaussian_rp_cov_perfect_square` (`OSProofs/OS3_RP_Lattice.lean`).
  - **1 superseded-chain axiom** — `torus_weakCoupling_lattice_connectedFourPoint_strictNeg`
    (`TorusContinuumLimit/TorusInteractingResult.lean`, added 2026-06-05): consumed only by
    `torus_pphi2_isInteracting_weakCoupling` (same file), which is itself **superseded by
    Route A's** `torus_pphi2_isInteractingStrict_weakCoupling` (2026-06-07, PR #48). Axiom +
    dead theorem should be removed together in the next cleanup pass.
  - Per the cross-cutting **coherence analysis**
    ([`planning/coherence-analysis.md`](planning/coherence-analysis.md)), the 17 axioms do not
    yet assemble into "an *interacting* φ⁴₂ QFT exists" — the missing keystone is **18.
    weak-coupling uniqueness** (cluster expansion); a new target carried alongside the 17.

  Recent earlier discharges that the README used to detail individually (cluster B / Phase B
  Glimm-Jaffe Fourier; `measure_determined_by_schwinger`; `rough_error_variance`;
  `continuumMeasures_tight`; the `cylinderIR_os0` / `os0_for_continuum_limit` /
  `os1_for_continuum_limit` / `os4_for_continuum_limit` wrappers; the inheritance-layer split;
  `wickConstantAsym_eq_variance` and `asymChaosCutoffDecomposition`; cylinder TM + Layer-B1
  variance bound) are recorded chronologically in [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md). Route C's
  21 axioms remain preserved in `future/`
- **Route B (torus):** 0 axioms, 0 sorries — the most developed route
- **Route B' IR limit:** 0 local axioms, 0 sorries — OS0 analyticity is proved from uniform exponential moments plus bounded-continuous weak convergence; OS2 uses the narrowed `AsymTorusSequenceHasCylinderOS2Symmetry` input, with a proved bridge from `AsymSatisfiesTorusOS`; OS3 is transferred from `CylinderMeasureSequenceEventuallyReflectionPositive`; the remaining nonlocal inputs are the eventual Green-moment bound `AsymTorusSequenceHasUniformGreenMomentBound` and eventual pullback RP for the concrete asymmetric-torus family
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
    FunctionalAnalysis.lean          -- Pure Mathlib results: Cesàro, Schwartz Lp, trig identities, log-decay, CF defect control
  ContinuumLimit/
    CharacteristicFunctional.lean    -- Continuum CF analyticity/invariance/reality/ergodicity support
    TimeReflection.lean              -- Continuum time reflection on Schwartz space and distributions
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
- [AXIOM_AUDIT.md](AXIOM_AUDIT.md) — Self-audit of all axioms
  (pphi2 + gaussian-field + markov-semigroups + gaussian-hilbert) with
  correctness ratings; format per `~/.claude/AXIOM_AUDIT_FORMAT.md`.
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
