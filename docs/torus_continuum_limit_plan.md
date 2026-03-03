# Torus Continuum Limit Completion Plan

## Overview

The torus continuum limit isolates the UV limit (a = L/N → 0) from IR issues
by fixing the physical volume L. The pipeline handles both Gaussian and
interacting (P(φ)₂) measures.

**Current state (2026-03-03):** 7 files in `TorusContinuumLimit/`, 15 torus
axioms, 2 sorries (both in TorusOSAxioms). OS0–OS3 defined for the torus
Gaussian continuum limit; OS2 + OS3 proved, OS0 + OS1 sorry'd.

## Architecture

```
gaussian-field (upstream)                    pphi2 (downstream)
─────────────────────────                    ──────────────────
NuclearTensorProduct.evalCLM ──────────────→ TorusEmbedding.lean
HeatKernel/Bilinear.lean    ──────────────→   torusContinuumGreen = greenFunctionBilinear
  HasLaplacianEigenvalues                      torusContinuumMeasure
  heatKernelBilinear                           torusEmbeddedTwoPoint
  greenFunctionBilinear
Torus/Symmetry.lean         ──────────────→ TorusOSAxioms.lean
  torusTranslation                             torusGeneratingFunctional
  torusSwap                                    TorusOS0 (sorry)
  torusTimeReflection                          TorusOS1 (sorry)
  torusConfigReflection                        TorusOS2_Translation (PROVED)
                                               TorusOS2_D4 (PROVED)
                                             TorusPropagatorConvergence.lean
                                               torus_propagator_convergence (axiom)
                                               torusEmbeddedTwoPoint_uniform_bound (axiom)
                                               torusContinuumGreen_pos (PROVED)

                                             TorusTightness.lean
                                               torusContinuumMeasures_tight (axiom)

                                             TorusConvergence.lean
                                               torusGaussianLimit_exists (PROVED)

                                             TorusGaussianLimit.lean
                                               torusGaussianLimit_isGaussian (axiom)
                                               torusGaussianMeasure_isGaussian (axiom)
                                               torusLimit_covariance_eq (axiom)
                                               gaussian_measure_unique_of_covariance (axiom)
                                               torusGaussianMeasure_z2_symmetric (axiom)
                                               z2_symmetric_of_weakLimit (axiom)
                                               torusGaussianLimit_fullConvergence (axiom)
                                               torusGaussianLimit_converges (PROVED)
                                               torusGaussianLimit_nontrivial (PROVED)

                                             TorusOSAxioms.lean
                                               torusGaussianLimit_characteristic_functional (axiom)
                                               torusContinuumGreen_translation_invariant (axiom)
                                               torusContinuumGreen_pointGroup_invariant (axiom)
                                               torusLattice_rp (axiom)
                                               torusGaussianLimit_os0 (sorry)
                                               torusGaussianLimit_os1 (sorry)
                                               torusGaussianLimit_os2_translation (PROVED)
                                               torusGaussianLimit_os2_D4 (PROVED)
                                               torusGaussianLimit_os3 (PROVED)
                                               torusGaussianLimit_satisfies_OS (PROVED)

                                             TorusInteractingLimit.lean
                                               torus_interacting_tightness (axiom)
                                               torusInteractingLimit_exists (PROVED)
```

## Current Status by File

| File | Axioms | Sorries | Proved |
|------|--------|---------|--------|
| TorusEmbedding | 0 | 0 | `torusEmbedLift_measurable`, `torusContinuumMeasure_isProbability` |
| TorusPropagatorConvergence | 2 | 0 | `torusContinuumGreen_pos` |
| TorusTightness | 1 | 0 | `torus_second_moment_uniform` |
| TorusConvergence | 0 | 0 | `torusGaussianLimit_exists` |
| TorusGaussianLimit | 7 | 0 | `torusGaussianLimit_converges`, `torusGaussianLimit_nontrivial` |
| TorusOSAxioms | 4 | 2 | `os2_translation`, `os2_D4`, `os3`, `satisfies_OS` |
| TorusInteractingLimit | 1 | 0 | `torusInteractingLimit_exists` |
| **Total** | **15** | **2** | |

## Next Steps: Fill the 2 Sorries

### `torusGaussianLimit_os1` (OS1, easy)

**Statement:** `‖torusGeneratingFunctional L μ f‖ ≤ 1`

**Proof:** `|E[e^{iωf}]| ≤ E[|e^{iωf}|] = E[1] = 1` by norm_integral_le_integral_norm
+ `‖exp(ix)‖ = 1` + probability measure has total mass 1.

This is the same argument as the proved `norm_generatingFunctional_le_one` in
OS2_WardIdentity.lean — just for torus test functions instead of Schwartz.

**Blocked by:** Nothing.

### `torusGaussianLimit_os0` (OS0, straightforward)

**Statement:** `Re(Z[Σ zᵢJᵢ])` is real-analytic on ℝⁿ.

**Proof:** By `torusGaussianLimit_characteristic_functional`, Z[f] = exp(-½G(f,f)).
So Z[Σ zᵢJᵢ] = exp(-½ Σᵢⱼ zᵢzⱼ G(Jᵢ,Jⱼ)), a composition of a polynomial (the
bilinear form) with exp, which is entire. Take Re to get a real-analytic function.

**Blocked by:** `torusGaussianLimit_characteristic_functional` axiom (needed in proof).

## Axiom Inventory (15 axioms)

### Tier A: Convergence Infrastructure (7 axioms in TorusGaussianLimit)

| Axiom | Difficulty | Description |
|-------|-----------|-------------|
| `torusGaussianLimit_isGaussian` | Medium | Weak limits of Gaussians are Gaussian (Bochner-Minlos) |
| `torusGaussianMeasure_isGaussian` | Easy | Lattice GFF pushforward is Gaussian (linear pushforward of Gaussian) |
| `torusLimit_covariance_eq` | Easy-Med | Weak convergence transfers second moments (uniform integrability) |
| `gaussian_measure_unique_of_covariance` | Easy | Gaussian determined by covariance (Bochner-Minlos uniqueness) |
| `torusGaussianMeasure_z2_symmetric` | Easy | Centered Gaussian is Z₂-symmetric |
| `z2_symmetric_of_weakLimit` | Easy | Z₂ symmetry preserved under weak limits (homeomorphism) |
| `torusGaussianLimit_fullConvergence` | Medium | Full sequence convergence from uniqueness |

### Tier B: UV Convergence (3 axioms)

| Axiom | Difficulty | Description |
|-------|-----------|-------------|
| `torus_propagator_convergence` | Medium | Lattice eigenvalues → continuum eigenvalues |
| `torusEmbeddedTwoPoint_uniform_bound` | Easy | E[Φ_N(f)²] ≤ C uniformly (λ ≥ m²) |
| `torusContinuumMeasures_tight` | Medium | Tightness via Mitoma criterion |

### Tier C: OS Axiom Support (4 axioms in TorusOSAxioms)

| Axiom | Difficulty | Description |
|-------|-----------|-------------|
| `torusGaussianLimit_characteristic_functional` | Easy-Med | Z[f] = exp(-½G(f,f)) from MGF → CF analytic continuation |
| `torusContinuumGreen_translation_invariant` | Easy | G_L(Tf,Tg) = G_L(f,g) — phase cancellation in Fourier |
| `torusContinuumGreen_pointGroup_invariant` | Easy | G_L is D4-invariant — eigenvalue symmetry |
| `torusLattice_rp` | Medium | Lattice GFF is RP (transfer matrix H ≥ 0) |

### Tier D: Interacting Extension (1 axiom)

| Axiom | Difficulty | Description |
|-------|-----------|-------------|
| `torus_interacting_tightness` | Hard | Cauchy-Schwarz density transfer + Nelson |

## Priority for Axiom Reduction

1. **`torusGaussianMeasure_z2_symmetric`** (Easy) — centered Gaussian is even
2. **`z2_symmetric_of_weakLimit`** (Easy) — negation is a homeomorphism
3. **`torusGaussianMeasure_isGaussian`** (Easy) — linear pushforward of Gaussian
4. **`torusContinuumGreen_translation_invariant`** (Easy) — spectral argument
5. **`torusContinuumGreen_pointGroup_invariant`** (Easy) — eigenvalue symmetry
6. **`torusEmbeddedTwoPoint_uniform_bound`** (Easy) — λ ≥ m² + Parseval
7. **`gaussian_measure_unique_of_covariance`** (Easy) — Fourier transform injectivity
8. **`torusLimit_covariance_eq`** (Easy-Med) — uniform integrability
9. **`torusGaussianLimit_characteristic_functional`** (Easy-Med) — Wick rotation
10. **`torusGaussianLimit_isGaussian`** (Medium) — Bochner-Minlos
11. **`torus_propagator_convergence`** (Medium) — dominated convergence
12. **`torusContinuumMeasures_tight`** (Medium) — Mitoma criterion
13. **`torusGaussianLimit_fullConvergence`** (Medium) — subsequential uniqueness
14. **`torusLattice_rp`** (Medium) — transfer matrix argument
15. **`torus_interacting_tightness`** (Hard) — Nelson + hypercontractivity

## Success Criteria

- 2 sorries filled (OS0 + OS1)
- `torusGaussianLimit_satisfies_OS` compiles with no sorry
- `lake build` passes with no regressions
- Axiom count ideally decreases (easy axioms proved)
