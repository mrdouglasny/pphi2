# P(φ)₂ Interacting Measure — Construction Routes

Three live routes + one preserved route. All share the interacting-measure
framework `dμ_V = (1/Z) exp(-V) dμ_free` (`InteractingMeasure/General.lean`).

**Current state** (`scripts/count_axioms.sh`, 2026-05-08, on
`fix/lattice-action-normalization`):
**pphi2 total: 19 axioms, 0 sorries. pinned Lake GaussianField: 5 axioms, 1 sorry.**

The 4-axiom delta over `main` (which is at 15) is the surviving
Stage 1 GJ-aligned cohort introduced when the lattice action was renormalised
to the Glimm–Jaffe convention `S = (a^d/2)⟨φ, M_a φ⟩`. 9 of the original
11 Stage 1 axioms have been discharged in Phase 2 (**Cluster B complete**:
both symmetric and asymmetric uniform-bound pairs proved via the
`(a^d)⁻¹ · a_geom² = 1` cancellation; the asym side now has its own
GJ-aligned embedding `evalAsymAtFinSiteGJ` mirroring `evalTorusAtSiteGJ`).
Remaining 4 are all in **Cluster A** (Nelson dynamical-cutoff family).

Recent reductions (this branch):

* 2026-05-08 (PR #14, merged main): `fourierTransform_lp_eq_fourierIntegral`
  discharged as theorem in `Pphi2/TransferMatrix/GaussianFourier.lean` via
  Mathlib's tempered-distribution Fourier compatibility, the classical
  Fourier Fubini identity, and equality of locally integrable functions
  from compactly supported smooth tests. The convolution quadratic-form
  identity `fourier_representation_convolution` is therefore axiom-free
  inside `GaussianFourier.lean`. PR #14 also refactored
  `cylinderIR_uniform_exponential_moment` and `cylinderIR_os3` to consume
  explicit Green-moment / RP inputs (axioms → theorems).
* 2026-05-08 (this branch, Phase 2 partial):
  `normalizedGaussianDensityMeasure_linearFourier` discharged in
  gaussian-field via the GJ-adapted `integral_massEigenbasis_cexp_GJ`
  helper; `torus_propagator_convergence_GJ` discharged in pphi2 via the
  `(a^d)⁻¹ · (L/N)² = 1` cancellation between `evalTorusAtSiteGJ` and
  `latticeCovarianceGJ`. `roughCovariance_sq_summable` and
  `smoothVariance_le_log` (trivial-`C` form) discharged in
  `NelsonEstimate/CovarianceSplit.lean`.
* 2026-04-29: `integral_operator_l2_kernel_compact` — Hilbert-Schmidt
  compactness in convolution-kernel form — converted from axiom to
  theorem in `Pphi2/GeneralResults/HilbertSchmidt.lean`.
* 2026-04-30 (PR #11, merged main): `cylinderIR_uniform_second_moment`
  converted from axiom to theorem.

Net of Stage 1 + Phase 2 + PR #14: Stage 1 raised pphi2 22 → 29 axioms
(plus 2 in gaussian-field); Phase 2 partial discharge + PR #14 brought
the combined count from 35 to 28 (5 Stage 1 GJ axioms + 3 main-track
axioms discharged).

---

## Route A: Lattice → S'(ℝ²)

**Purpose:** Main theorem — P(φ)₂ QFT on the Euclidean plane satisfying OS0–OS4.

**Spacetime:** ℝ² (2D Euclidean plane).

**Main theorem:** `pphi2_exists_os_and_massParameter_positive` (`Main.lean`) —
structurally assembled, conditional on the remaining axioms.

### Files and axiom count

| Cluster | Files | Axioms |
|--------|-------|--------|
| Transfer matrix + spectrum | `TransferMatrix/L2Operator`, `GaussianFourier`, `SpectralGap` | 3 |
| Lattice RP | `OSProofs/OS3_RP_Lattice` | 1 |
| Lattice clustering / OS4 | `OSProofs/OS4_MassGap` | 2 |
| Ward identity / continuum OS2 | `OSProofs/OS2_WardIdentity` | 1 |
| Propagator convergence | `GaussianContinuumLimit/PropagatorConvergence` | 1 |
| Continuum limit / non-Gaussianity | `ContinuumLimit/Convergence` | 1 |
| Continuum inheritance | `ContinuumLimit/AxiomInheritance` | 3 |
| Main assembly | `Main.lean` | 1 |
| **Route A total** | | **13** |

### OS axiom strategy

| OS axiom | Status | Method |
|----------|--------|--------|
| OS0 analyticity | axiom chain | Vitali on analytic functions under weak limits (`analyticOn_generatingFunctionalC`) |
| OS1 regularity | proved conditional on Ward-chain | exponential-moment Schwartz bound |
| OS2 translation | proved conditional | lattice translation invariance + CF continuity |
| OS2 rotation | axiom | Ward identity + `anomaly_bound_from_superrenormalizability` |
| OS3 reflection positivity | proved conditional on `gaussian_rp_cov_perfect_square` | transfer matrix + lattice-to-continuum RP inheritance |
| OS4 clustering + ergodicity | proved conditional | uniform mass gap (`spectral_gap_uniform`) + exp clustering |

### Remaining axiom categories

- **Deep mathematical content (multi-week work each)**:
  `spectral_gap_uniform`, `spectral_gap_lower_bound`, `continuumLimit_nonGaussian`,
  `pphi2_nontriviality`, `anomaly_bound_from_superrenormalizability`,
  `rotation_invariance_continuum`, `continuum_exponential_clustering`.
- **Mathlib-upstream**: `fourier_representation_convolution` (L² convolution
  theorem, not yet in Mathlib). (`integral_operator_l2_kernel_compact` —
  the Reed-Simon HS theorem — was an axiom; **proved 2026-04-29** in
  `Pphi2/GeneralResults/HilbertSchmidt.lean`. Belongs in Mathlib or
  SpectralThm long-term.)
- **Self-contained classical** (textbook but long): `gaussian_rp_cov_perfect_square`,
  `latticeGreenBilinear_basis_tendsto_continuum`.

### Tightness and convergence infrastructure
- `continuumMeasures_tight` — **PROVED** (ported from torus pipeline, 2026-04-19)
- `gaussianContinuumMeasures_tight` — **PROVED** for `d > 0`
- `prokhorov_configuration_sequential` — **PROVED** via gaussian-field
- `continuumLimit` (subsequential Prokhorov extraction) — **PROVED**
- `pphi2_limit_exists` — proved, currently using a trivial δ₀ witness

---

## Route B: Lattice → T²_L (UV warm-up)  ✅ DONE

**Purpose:** UV-limit warm-up isolating the `a → 0` step from IR issues.

**Spacetime:** T²_L = (ℝ/Lℤ)² (2D torus, fixed side L).

**Main theorem:** `torusInteractingLimit_exists` (`TorusContinuumLimit/TorusInteractingLimit.lean`)
— **fully proved**, not conditional on any Route-B-local axioms.

### Files and axiom count

| Files | Axioms | Sorries |
|-------|--------|---------|
| `TorusContinuumLimit/*.lean` | 0 | 0 |
| `NelsonEstimate/*.lean` | 0 | 0 |
| **Route B total** | **0** | **0** |

### OS axioms proved

| OS axiom | Status | Theorem |
|----------|--------|---------|
| OS0 analyticity | **proved** | `torusGaussianLimit_os0`, `torusInteractingLimit_os0` |
| OS1 regularity | **proved** | `torusInteractingLimit_os1` |
| OS2 translation invariance | **proved** | baked into lattice measure, transferred through UV |
| OS3 | **intentionally out of scope** | No natural time-reflection on T²; deferred to Route B′ |
| OS4 | **intentionally out of scope** | No thermodynamic limit at finite L; deferred to Route A |

Route B is structurally the simplest and the first to be closed. It served as
the template for porting tightness to Route A (`continuumMeasures_tight`).

---

## Route B′: Asymmetric Torus UV → Cylinder IR limit

**Purpose:** Recover OS3 using cylinder geometry where time-reflection is natural.

**Spacetime:** S¹_Ls × ℝ (spatial circle × Euclidean time line).

**Main theorem (target):** `routeBPrime_cylinder_OS` (`IRLimit/CylinderOS.lean`) —
structurally assembled with 0 local IR-limit axioms, conditional on explicit
family-level inputs: the eventual Green-moment bound
`AsymTorusSequenceHasUniformGreenMomentBound` and eventual pullback RP
`CylinderMeasureSequenceEventuallyReflectionPositive`.

### Pipeline

1. **UV (`AsymTorus/`)**: Lattice → asymmetric torus T_{Lt,Ls} with differently-sized
   time (Lt) and space (Ls) circles. UV limit `a → 0` at fixed (Lt, Ls). OS0, OS1, OS2
   proved via method-of-images propagator on the asymmetric torus. **0 axioms, 0 sorries.**
2. **IR (`IRLimit/`)**: Cylinder pullback at finite Lt, then IR limit Lt → ∞ to obtain
   a measure on S'(S¹_Ls × ℝ). OS0, OS2-translation and OS2-time-reflection are proved
   at each finite Lt (periodization intertwines shifts). Prokhorov extraction through
   the IR limit is proved in `IRLimit/IRTightness.lean`. OS3 via density on
   compactly-supported positive-time test functions.

### Files and axiom count

| Files | Axioms | Sorries |
|-------|--------|---------|
| `AsymTorus/*.lean` (UV) | 0 | 0 |
| `IRLimit/Periodization.lean` | 0 | 0 |
| `IRLimit/CylinderEmbedding.lean` | 0 | 0 |
| `IRLimit/CovarianceConvergence*.lean` | 0 | 0 |
| `IRLimit/IRTightness.lean` | 0 | 0 |
| `IRLimit/GreenFunctionComparison.lean` | 0 | 0 |
| `IRLimit/UniformExponentialMoment.lean` | **0** (`cylinderIR_uniform_exponential_moment` derived from uniform Green-moment input; `cylinderIR_uniform_second_moment` derived as theorem 2026-04-25) | 0 |
| `IRLimit/CylinderOS.lean` | **0** (OS3 transfer from `CylinderMeasureSequenceEventuallyReflectionPositive`) | 0 |
| **Route B′ total** | **0** | **0** |

### OS axioms

| OS axiom | Status | Method |
|----------|--------|--------|
| OS0 analyticity | **proved** | uniform exp moment + BC weak convergence + `analyticOnNhd_integral` |
| OS2 time translation | **proved** | periodization intertwines shifts exactly |
| OS2 time reflection | **proved** | periodization + torus time-reflection invariance |
| OS2 spatial translation | **proved** | inherited from torus spatial invariance |
| OS3 reflection positivity | **proved conditional** | eventual pullback RP + characteristic-functional convergence |

### Remaining external inputs — proof routes

- ~~**`cylinderIR_uniform_second_moment`**~~ — **converted to theorem 2026-04-25**
  in `UniformExponentialMoment.lean`, deriving from
  `cylinderIR_uniform_exponential_moment` via the elementary inequality
  `x² ≤ 2 e^|x|` and a scaling optimization. Statement now in additive form
  `C₁ q(f)² + C₂` (the form actually consumed by IR-tightness).
- ~~**`cylinderIR_uniform_exponential_moment`**~~ — **converted to theorem 2026-05-04**
  in `UniformExponentialMoment.lean`, conditional on
  `MeasureHasGreenMomentBound` for each measure. At sequence level this is
  tracked by `AsymTorusSequenceHasUniformGreenMomentBound`, an eventual
  `atTop` condition. Consumers combine it with `Lt → ∞` to get the
  `Lt ≥ 1` tail needed by the method-of-images theorem. The proof composes
  `cylinderPullback_expMoment_uniform_bound` with the method-of-images Green
  estimate, keeping the remaining volume-uniform analytic input explicit.
- ~~**`cylinderIR_os3`**~~ — **removed 2026-05-07**. `CylinderOS.lean`
  now defines `CylinderMeasureSequenceEventuallyReflectionPositive` and proves
  the IR-limit OS3 matrix inequality from that eventual pullback RP input plus
  characteristic-functional convergence. Full-RP statements imply this exact
  input via `CylinderMeasureSequenceEventuallyReflectionPositive.of_forall` or
  `CylinderMeasureSequenceEventuallyReflectionPositive.of_eventually_full`.
  Remaining proof strategy for that input:
  1. At finite Lt and for `f ∈ C_c^∞((0, Lt/2) × S¹_Ls)`, `embed f` has no wrap-around;
     the torus measure satisfies RP across t = 0 (proved via the asymmetric-torus OS3
     construction, if/when that's completed for AsymTorus — see note below).
  2. Under the cylinder pullback `cylinderPullbackMeasure`, RP transfers exactly at
     each finite Lt (no loss).
  3. Density of `C_c^∞((0, Lt/2) × S¹_Ls)` in `cylinderPositiveTimeSubmodule` in
     the relevant Schwartz topology extends RP to all positive-time Schwartz test
     functions.
  - The weak-limit transfer step is now formalized in `routeBPrime_cylinder_OS`.
  - Difficulty: requires establishing RP on AsymTorus/pullbacks first.

### Note: AsymTorus OS3 status
`AsymSatisfiesTorusOS` currently bundles OS0, OS1, OS2-translation,
OS2-time-reflection — but **not** OS3. To discharge
`CylinderMeasureSequenceEventuallyReflectionPositive` for the concrete family,
one still needs either a compactly-supported asymmetric-torus OS3 theorem with
no wrap-around plus density, or a direct eventual theorem for the cylinder
pullback sequence.

---

## Route C: Direct cylinder construction (inactive, preserved)

**Purpose:** Alternative direct Nelson/Simon-style cylinder construction with two
cutoffs (UV Λ and IR T). Preserved in `future/CylinderContinuumLimit/` but not
in the active build.

**Files:** `future/CylinderContinuumLimit/*.lean` (6 files, **21 axioms**).

**Status:** **Superseded by Route B′**. Route B′ reuses all of Route B's UV infrastructure
and avoids the isonormal-extension sorry that blocked Route C's `cylinderOUProcessEval`.

---

## Cross-route and upstream

### Bridge (`Bridge.lean`, 3 axioms)
Connects Pphi2 and Phi4 constructions. Separate workstream from Route A's main theorem.
- `measure_determined_by_schwinger` (moment determinacy, Dimock-Glimm / Gel'fand-Vilenkin)
- `schwinger_agreement` (weak-coupling cluster expansion, Guerra-Rosen-Simon)
- `os2_from_phi4`

### Upstream gaussian-field
Not counted in this checkout: the local counter reports that it cannot see a
sibling `../gaussian-field` tree. Cylinder Green-function, method-of-images,
and Schwartz-nuclear-extension infrastructure remain upstream concerns.

---

## Grand total

| Route | Axioms | Sorries |
|-------|--------|---------|
| Route A (main line, ex-Bridge) | 13 | 0 |
| Route B (torus UV) | 0 | 0 |
| Route B′ (cylinder IR limit) | 0 | 0 |
| Bridge (cross-formulation) | 3 | 0 |
| **pphi2 total** | **16** | **0** |
| pinned Lake `GaussianField` dependency | 4 | 0 |

Route B is the "done" route. Route B′ now has no local IR-limit axioms, but
remains conditional on explicit family-level Green-moment and eventual RP
inputs. Route A's transfer-matrix cluster lost `integral_operator_l2_kernel_compact`
and the Fourier/convolution footprint in `GaussianFourier.lean`; the
`L¹∩L²` Plancherel representative bridge is now proved from pinned Mathlib's
tempered-distribution Fourier API.
