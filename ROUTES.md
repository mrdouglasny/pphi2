# P(φ)₂ Interacting Measure — Construction Routes

Three live routes + one preserved route. All share the interacting-measure
framework `dμ_V = (1/Z) exp(-V) dμ_free` (`InteractingMeasure/General.lean`).

**Current state** (`scripts/count_axioms.sh`, 2026-04-19):
**pphi2 total: 22 axioms, 0 sorries. gaussian-field: 2 axioms, 1 sorry.**

---

## Route A: Lattice → S'(ℝ²)

**Purpose:** Main theorem — P(φ)₂ QFT on the Euclidean plane satisfying OS0–OS4.

**Spacetime:** ℝ² (2D Euclidean plane).

**Main theorem:** `pphi2_exists_os_and_massParameter_positive` (`Main.lean`) —
structurally assembled, conditional on the remaining axioms.

### Files and axiom count

| Cluster | Files | Axioms |
|--------|-------|--------|
| Transfer matrix + spectrum | `TransferMatrix/L2Operator`, `GaussianFourier`, `SpectralGap` | 4 |
| Lattice RP | `OSProofs/OS3_RP_Lattice` | 1 |
| Lattice clustering / OS4 | `OSProofs/OS4_MassGap` | 2 |
| Ward identity / continuum OS2 | `OSProofs/OS2_WardIdentity` | 6 |
| Propagator convergence | `GaussianContinuumLimit/PropagatorConvergence` | 1 |
| Continuum limit / non-Gaussianity | `ContinuumLimit/Convergence` | 1 |
| Main assembly | `Main.lean` | 1 |
| **Route A total** | | **16** |

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
- **Mathlib-upstream**: `integral_operator_l2_kernel_compact` (HS theorem, Reed-Simon),
  `fourier_representation_convolution` (L² convolution theorem, not yet in Mathlib).
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
structurally assembled, conditional on 3 IR-limit axioms.

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
| `IRLimit/GreenFunctionComparison.lean` | **1** (`cylinderIR_uniform_second_moment`) | 0 |
| `IRLimit/UniformExponentialMoment.lean` | **1** (`cylinderIR_uniform_exponential_moment`) | 0 |
| `IRLimit/CylinderOS.lean` | **1** (`cylinderIR_os3`) | 0 |
| **Route B′ total** | **3** | **0** |

### OS axioms

| OS axiom | Status | Method |
|----------|--------|--------|
| OS0 analyticity | **proved** | uniform exp moment + BC weak convergence + `analyticOnNhd_integral` |
| OS2 time translation | **proved** | periodization intertwines shifts exactly |
| OS2 time reflection | **proved** | periodization + torus time-reflection invariance |
| OS2 spatial translation | **proved** | inherited from torus spatial invariance |
| OS3 reflection positivity | **1 axiom** (`cylinderIR_os3`) | compactly-supported positive-time test functions + torus RP at finite Lt + density |

### Remaining axioms — proof routes

- **`cylinderIR_uniform_second_moment`** (`GreenFunctionComparison.lean:102`):
  `E_{ν_Lt}[(ω f)²] ≤ C·q(f)²` uniformly in Lt ≥ 1. Needed for IR tightness.
  Proof chain already staged:
  - `cylinderPullback_second_moment_eq` (proved): pullback identity.
  - `cylinderPullback_second_moment_density_transfer_cutoff` (proved): finite-cutoff
    density transfer via Cauchy-Schwarz on the interacting Boltzmann weight.
  - Remaining: package the torus UV limit + uniform-in-Lt method-of-images bound
    `torusGreen_uniform_bound` (proved in gaussian-field) into a single statement.
  - Difficulty: mostly plumbing, no new mathematical content.
- **`cylinderIR_uniform_exponential_moment`** (`UniformExponentialMoment.lean:53`):
  `∫ exp(|ωf|) dν_Lt ≤ K·exp(C·q(f)²)` uniformly in Lt ≥ 1. Needed for OS0 and OS1.
  Proof chain:
  - `AsymSatisfiesTorusOS.os1` provides the torus exponential-moment bound.
  - Method-of-images bound `‖embed f‖ ≤ C·q(f)` uniformly in Lt.
  - Compose: pullback + density transfer + method-of-images.
  - Difficulty: parallel to the second-moment case.
- **`cylinderIR_os3`** (`CylinderOS.lean:294`):
  RP of the IR-limit cylinder measure. Proof strategy (see docstring):
  1. At finite Lt and for `f ∈ C_c^∞((0, Lt/2) × S¹_Ls)`, `embed f` has no wrap-around;
     the torus measure satisfies RP across t = 0 (proved via the asymmetric-torus OS3
     construction, if/when that's completed for AsymTorus — see note below).
  2. Under the cylinder pullback `cylinderPullbackMeasure`, RP transfers exactly at
     each finite Lt (no loss).
  3. RP is closed under weak limits (standard: matrix entries are bounded continuous
     in ω, so RP passes through Prokhorov extraction).
  4. Density of `C_c^∞((0, Lt/2) × S¹_Ls)` in `cylinderPositiveTimeSubmodule` in
     the relevant Schwartz topology extends RP to all positive-time Schwartz test
     functions.
  - Difficulty: largest of the three; requires establishing RP on AsymTorus first.

### Note: AsymTorus OS3 status
`AsymSatisfiesTorusOS` currently bundles OS0, OS1, OS2-translation,
OS2-time-reflection — but **not** OS3. To prove `cylinderIR_os3`, step 1 of the
proof route above requires extending `AsymSatisfiesTorusOS` with a compactly-supported
OS3 clause (or a separate theorem on compactly-supported test functions with no
wrap-around). This extension is a prerequisite for Route B′ completion.

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
**2 axioms, 3 sorries.** Cylinder Green-function, method-of-images, and
Schwartz-nuclear-extension infrastructure. See `../gaussian-field/status.md`.

---

## Grand total

| Route | Axioms | Sorries |
|-------|--------|---------|
| Route A (main line, ex-Bridge) | 16 | 0 |
| Route B (torus UV) | 0 | 0 |
| Route B′ (cylinder IR limit) | 3 | 0 |
| Bridge (cross-formulation) | 3 | 0 |
| **pphi2 total** | **22** | **0** |
| gaussian-field (upstream) | 2 | 3 |

Route B is the "done" route. Route B′ is the next candidate for a focused completion
effort — its 3 axioms are structurally clear with documented proof routes, and no
Route-B′-internal axiom is blocked by external work (unlike Route A's
`fourier_representation_convolution`, which waits on Mathlib's L² convolution theorem).
