# P(Φ)₂ Project Status

## Overview

The project formalizes the construction of P(Φ)₂ Euclidean quantum field theory
in Lean 4 via the Glimm-Jaffe/Nelson lattice approach. All six phases are
structurally complete and the full project builds successfully (`lake build`).

The proof architecture is: axiomatize key analytic/probabilistic results with
detailed proof sketches, prove the logical structure connecting them, and
progressively fill in the axioms with full proofs.

A shared `Common/QFT` layer now separates concrete measure models, tensor
moments, distributional Schwinger-function data, explicit reconstruction input,
and backend-independent reconstruction rules. This keeps the current scalar
positive-measure construction explicit while opening a path to broader
Euclidean/Minkowski interfaces.

**Current counter (`./scripts/count_axioms.sh`, 2026-05-03): 19 axioms, 0 sorries.**

Recent reduction (2026-04-30, this PR): `cylinderIR_uniform_second_moment`
in `IRLimit/UniformExponentialMoment.lean` converted from axiom to theorem,
derived from `cylinderIR_uniform_exponential_moment` via the elementary
inequality `x² ≤ 2·exp(|x|)` plus a scaling optimisation. The new
theorem packages `Integrable (fun ω => (ω f)²) ν` alongside the
additive bound `∫(ωf)² ≤ C₁·q(f)² + C₂`, derived from the same
exp-moment input (no circularity).

Recent reductions (2026-04-19):
- `continuumMeasures_tight` (Tightness.lean) — **PROVED** (axiom → theorem). Port of the
  torus tightness pipeline to ℝ^d: `continuum_second_moment_uniform` derived from
  `interacting_moment_bound` (at `n=1, p=2`) + `gaussian_second_moment_uniform` gives the
  uniform second moment; tightness then follows from
  `configuration_tight_of_uniform_second_moments` (Mitoma-Chebyshev on the nuclear dual).
  Requires `[Fact (0 < d)]` for the `DyninMityaginSpace (ContinuumTestFunction d)` instance.

Recent corrections (2026-04-03):
- `general_clustering_from_spectral_gap` — **statement corrected**: `G` is evaluated on
  `latticeConfigEuclideanTimeShift N R ω` (the integrand now contains the actual translated
  observable), and the decay exponent is measured against the **cyclic torus time separation**
  `latticeEuclideanTimeSeparation N R` rather than an inconsistent unbounded `R`. Added
  `latticeEuclideanTimeShift`, `latticeConfigEuclideanTimeShift`, and
  `latticeEuclideanTimeSeparation`.
- `general_clustering_lattice` — removed unused phantom parameter `Nt` (theorem uses section `Ns` only).
- `Main.lean` — **honest naming**: `massParameter_positive`, `pphi2_exists_os_and_massParameter_positive`;
  `os_reconstruction` and `pphi2_wightman` kept as `@[deprecated]` aliases.

Recent reductions (2026-04-02):
- `limit_exponential_moment` sorry — **ELIMINATED**: truncation + MCT proof via
  `lintegral_iSup` (monotone convergence) + `Integrable.of_bound` + `ofReal_integral_eq_lintegral_ofReal`.
  Key insight: use `Measurable.aestronglyMeasurable` (not `Continuous.aestronglyMeasurable`
  which needs `OpensMeasurableSpace` on domain) to get AEStronglyMeasurability.
- `cylinderIR_os0` — **PROVED** (axiom → theorem): OS0 analyticity for the IR limit
  derived from `cylinderIR_uniform_exponential_moment` + BC weak convergence +
  `analyticOnNhd_integral`.
- `gaussianLimit_isGaussian` — **PROVED** by reducing continuum Gaussianity to
  1D evaluation marginals and a generic weak-limit theorem for centered real
  Gaussians
- `configuration_continuum_polishSpace` — **REMOVED** (inconsistent: weak-* dual is not Polish)
- `configuration_continuum_borelSpace` — **REMOVED** (inconsistent: same reason)
  Replaced by `prokhorov_configuration` from gaussian-field (proved, avoids Polish/Borel)
- `os3_inheritance` — **REMOVED** (incorrectly stated for ALL bounded continuous F)
- `os3_for_continuum_limit` — **PROVED** by strengthening `IsPphi2Limit` with
  inline reflection positivity of the approximating continuum measures and
  passing the RP matrix entries to the limit via characteristic-functional
  convergence
- `continuum_embedded_measure_rp` — **REMOVED** (dead code after OS3 restructuring)
- `gaussianContinuumMeasures_tight` sorry — **ELIMINATED by proving the theorem for `d > 0`** via `configuration_tight_of_uniform_second_moments`; the excluded `d = 0` case is a separate Dynin-Mityagin / Schwartz-space infrastructure issue
- `signedVal` + `signedVal_neg` — **PROVED** (centered coordinates for lattice embedding)
- `latticeEmbedLift_intertwines_reflection` — **PROVED** (embedding commutes with time reflection)
- `distribTimeReflection_continuous` — **PROVED** (WeakDual.continuous_of_continuous_eval)
- `physicalPosition` — switched to centered coordinates (`signedVal` replaces `ZMod.val`)

Upstream gaussian-field reductions (2026-03-27):
- `schwartzLaplaceEvalCLM` — **PROVED** (new SchwartzFourier/LaplaceCLM.lean, 0 axioms)
- `schwartzLaplaceEvalCLM_apply` — **PROVED** (definitional rfl)
- `schwartzLaplace_uniformBound` — **PROVED** (via toLpCLM + Seminorm.bound_of_continuous)
- gaussian-field axiom count: **7 → 3**

Earlier reductions (PR#1 from Matteo Cipollina):
- `gaussian_hermite_zero_mean` — **PROVED** (Hermite orthonormality from Mathlib)
- `wickConstant_eq_variance` — **PROVED** (product DFT Parseval + translation invariance)
- `periodicResolvent_convergence_rate` — **PROVED** (hyperbolic identity manipulation)

**Route B (torus): `TorusInteractingOS.lean` has 0 local axioms, 0 sorries.**
All OS0–OS2 proofs complete within this file. Transitive dependencies are
now largely resolved — see `docs/torus-route-gap-audit.md` for details.
Recently closed:
- `osgood_separately_analytic` — **PROVED** (Osgood/OsgoodN.lean, 1965 lines)
- `torusGeneratingFunctionalℂ_analyticOnNhd` — **PROVED** (Gaussian integrability via AM-GM)
- `evalTorusAtSite` sorries — **PROVED** in gaussian-field
Remaining: `configuration_tight_of_uniform_second_moments` (theorem in gaussian-field).

**Route B' (asymmetric torus): `AsymTorusOS.lean` has 0 axioms, 0 sorry.**
OS0 (analyticity), OS1 (regularity), OS2 (time reflection + translation) all proved.
Four infrastructure lemmas (lattice translation invariance, GF Lipschitz bound,
translation continuity, lattice approximation error vanishing) were formerly
axiomatized and are now fully proved theorems (2026-03-18).
Extends Route B to T_{Lt,Ls} with different circle sizes per direction.

**Other routes: ~50 axioms** (Routes A, C — not yet updated).

Note: Two axioms are `private`: `fourier_representation_convolution` (GaussianFourier)
and `gaussian_rp_cov_perfect_square` (OS3_RP_Lattice).
`schwartz_riemann_sum_bound` (PropagatorConvergence) was proved via Schwartz decay +
telescoping sum bound. The remaining Gaussian propagator debt is now isolated in the
spectral axiom `latticeGreenBilinear_basis_tendsto_continuum`; `propagator_convergence`
itself is a theorem via `embeddedTwoPoint_eq_latticeGreenBilinear`.

`schwinger2_convergence` was proved from
`schwinger_n_convergence`, and `pphi2_nonGaussianity` from `continuumLimit_nonGaussian`.

## File inventory

### Active files (lattice approach)

| Phase | File | Status |
|-------|------|--------|
| Core | `Polynomial.lean` | 0 axioms |
| 1 | `WickOrdering/WickPolynomial.lean` | 0 axioms |
| 1 | `WickOrdering/Counterterm.lean` | 0 axioms |
| 1 | `InteractingMeasure/LatticeAction.lean` | 0 axioms |
| 1 | `InteractingMeasure/LatticeMeasure.lean` | 0 axioms, 0 sorries |
| 1 | `InteractingMeasure/Normalization.lean` | 0 axioms, 0 sorries |
| 2 | `TransferMatrix/TransferMatrix.lean` | 0 axioms |
| 2 | `TransferMatrix/L2Multiplication.lean` | 0 axioms (multiplication operator M_w) |
| 2 | `TransferMatrix/L2Convolution.lean` | 0 axioms (Fubini identity proved) |
| 2 | `TransferMatrix/L2Operator.lean` | 1 axiom (`integral_operator_l2_kernel_compact`); `hilbert_schmidt_isCompact` + `transferOperator_isCompact` proved |
| 2 | `TransferMatrix/GaussianFourier.lean` | 1 private axiom (`fourier_representation_convolution`); `inner_convCLM_pos_of_fourier_pos` proved from axiom; `fourier_gaussian_pos` proved |
| 2 | `TransferMatrix/Jentzsch.lean` | 0 axioms; Jentzsch + nontriviality + positivity-improving + strict PD all proved |
| 2 | `TransferMatrix/Positivity.lean` | 0 axioms (energy levels, mass gap) |
| 2 | `OSProofs/OS3_RP_Lattice.lean` | 1 axiom (`gaussian_rp_cov_perfect_square`), 0 sorries |
| 2 | `OSProofs/OS3_RP_Inheritance.lean` | 0 axioms, 0 sorries |
| 3 | `TransferMatrix/SpectralGap.lean` | 2 axioms |
| 3 | `OSProofs/OS4_MassGap.lean` | 2 axioms, 0 sorries |
| 3 | `OSProofs/OS4_Ergodicity.lean` | 0 axioms, 0 sorries |
| 4 | `ContinuumLimit/Embedding.lean` | 0 axioms (`IsPphi2Limit` is a def) |
| 4 | `ContinuumLimit/Hypercontractivity.lean` | 0 axioms, 0 sorries (`wickConstant_eq_variance` now proved generically; `wickConstant_eq_variance_two_dim` remains as a 2D corollary) |
| 4 | `ContinuumLimit/Tightness.lean` | **0 axioms, 0 sorries** (`continuumMeasures_tight` proved from Mitoma-Chebyshev + `interacting_moment_bound`) |
| 4 | `ContinuumLimit/Convergence.lean` | 1 axiom, 0 sorries (`continuumLimit` and `pphi2_limit_exists` proved) |
| 4 | `ContinuumLimit/AxiomInheritance.lean` | **3 axioms, 0 sorries** (`continuum_exponential_moment_bound`, `canonical_continuumMeasure_cf_tendsto`, `continuum_exponential_clustering`; derived OS0/OS1/OS4 inheritance wrappers live here) |
| 4 | `ContinuumLimit/CharacteristicFunctional.lean` | 0 axioms, 0 sorries (complex analyticity, complex-from-real invariance, Z₂/reality, translation continuity, ergodicity support) |
| 4 | `ContinuumLimit/TimeReflection.lean` | 0 axioms, 0 sorries (continuum time reflection on Schwartz space and distributions) |
| 4 | `ContinuumLimit/RPTransfer.lean` | 0 axioms, 0 sorries (intertwining proved, signedVal) |
| 4G | `GaussianContinuumLimit/EmbeddedCovariance.lean` | 0 axioms, 0 sorries |
| 4G | `GaussianContinuumLimit/PropagatorConvergence.lean` | 1 axiom, 0 sorries (`propagator_convergence` now theorem; remaining axiom is `latticeGreenBilinear_basis_tendsto_continuum`) |
| 4G | `GaussianContinuumLimit/GaussianTightness.lean` | 0 axioms, 0 sorries |
| 4G | `GaussianContinuumLimit/GaussianLimit.lean` | 0 axioms, 0 sorries |
| 5 | `OSProofs/OS2_WardIdentity.lean` | 1 axiom |
| — | `GeneralResults/ComplexAnalysis.lean` | **0 axioms** (`osgood_separately_analytic` proved via Osgood/) |
| — | `GeneralResults/Osgood/Multilinear.lean` | 0 axioms (multilinear map infrastructure, from Irving) |
| — | `GeneralResults/Osgood/Osgood2.lean` | 0 axioms (2-variable Osgood, adapted from Irving) |
| — | `GeneralResults/Osgood/OsgoodN.lean` | **0 axioms, 0 sorries** (n-variable Osgood by induction) |
| — | `GeneralResults/FunctionalAnalysis.lean` | 0 axioms (pure Mathlib results: Cesàro, Schwartz `L^p`, trig identities, logarithmic decay near `0`, generic characteristic-functional defect control) |
| — | `GeneralResults/ResolventFourierAnalysis.lean` | 0 axioms (Fourier/resolvent kernel identities) |
| — | `GeneralResults/SchwartzCutoff.lean` | 0 axioms (smooth cutoff operators on Schwartz space) |
| — | `Common/QFT/Euclidean/Formulations.lean` | 0 axioms (shared measure / Schwinger / reconstruction-input interfaces) |
| — | `Common/QFT/Euclidean/ReconstructionInterfaces.lean` | 0 axioms (backend-independent linear-growth / reconstruction rule interfaces) |
| — | `GeneralResults/LatticeFourierIndexing.lean` | 0 axioms (Fourier mode reindexing and 2D lattice-eigenvalue sum theorem) |
| — | `GeneralResults/LatticeProductDFT.lean` | 0 axioms (generic product DFT Parseval theorem and abstract-vs-explicit spectral covariance identity) |
| — | `OSforGFF/TimeTranslation.lean` | 0 axioms, 0 sorries (Schwartz translation continuity) |
| 6 | `OSAxioms.lean` | 0 axioms, 0 sorries |
| 6 | `FormulationAdapter.lean` | 0 axioms, 0 sorries (exports `Pphi2` into the shared formulation layer) |
| 6 | `Main.lean` | 1 axiom, 0 sorries |
| 4T | `TorusContinuumLimit/TorusEmbedding.lean` | 0 axioms, 0 sorries (`torusContinuumGreen` now `greenFunctionBilinear`) |
| 4T | `TorusContinuumLimit/TorusPropagatorConvergence.lean` | 0 axioms, 0 sorries (`torus_propagator_convergence` proved via gaussian-field `lattice_green_tendsto_continuum` axiom) |
| 4T | `TorusContinuumLimit/TorusTightness.lean` | 0 axioms, 0 sorries |
| 4T | `TorusContinuumLimit/TorusConvergence.lean` | 0 axioms, 0 sorries (Prokhorov proved!) |
| 4T | `TorusContinuumLimit/TorusGaussianLimit.lean` | 0 axioms, 0 sorries |
| 4T | `TorusContinuumLimit/TorusInteractingLimit.lean` | 0 axioms, 0 sorries |
| 4T | `TorusContinuumLimit/TorusOSAxioms.lean` | 0 axioms, 0 sorries |
| 4T | `TorusContinuumLimit/TorusInteractingOS.lean` | 0 axioms, 0 sorries |
| 4T | `TorusContinuumLimit/MeasureUniqueness.lean` | 0 axioms, 0 sorries |
| 4T | `TorusContinuumLimit/TorusNuclearBridge.lean` | 0 axioms, 0 sorries |
| 4T | `NelsonEstimate/*.lean` | 0 axioms, 0 sorries |
| B' | `AsymTorus/AsymTorusEmbedding.lean` | 0 axioms, 0 sorries |
| B' | `AsymTorus/AsymTorusInteractingLimit.lean` | 0 axioms, 0 sorries |
| B' | `AsymTorus/AsymTorusOS.lean` | **0 axioms, 0 sorries** (OS0–OS2 fully proved) |
| 6 | `Bridge.lean` | 3 axioms, 0 sorries |
| B'IR | `IRLimit/Periodization.lean` | 0 axioms, 0 sorries (re-exports from gaussian-field) |
| B'IR | `IRLimit/CylinderEmbedding.lean` | **0 axioms, 0 sorries** (intertwining proved via NTP pure tensor density) |
| B'IR | `IRLimit/CovarianceConvergence.lean` | 0 axioms, 0 sorries (spectral decompositions, pullback measures, basis machinery) |
| B'IR | `IRLimit/CovarianceConvergenceProof.lean` | 0 axioms, 0 sorries (exponential convergence rates, `asymTorusGreen_tendsto_physicalCylinderGreen`, `cylinderIRLimit_covariance_eq`) |
| B'IR | `IRLimit/GreenFunctionComparison.lean` | 1 axiom, 0 sorries (uniform 2nd moment) |
| B'IR | `IRLimit/UniformExponentialMoment.lean` | 1 axiom, 0 sorries (uniform exp moment) |
| B'IR | `IRLimit/IRTightness.lean` | 0 axioms, 0 sorries (Prokhorov extraction proved) |
| B'IR | `IRLimit/CylinderOS.lean` | 1 axiom, 0 sorries (OS3 axiomatized; OS0+OS2 proved) |

### Inactive files (old DDJ/stochastic quantization approach)

These files are from the earlier DDJ-based approach and live in `ddj/`.
They are not imported by the build but may be useful as reference.

- `ddj/Basic.lean` — cylinder test function spaces (44 sorries in instances)
- `ddj/FunctionSpaces/WeightedLp.lean`, `ddj/FunctionSpaces/Embedding.lean`
- `ddj/GaussianCylinder/Covariance.lean`
- `ddj/MeasureCylinder/Regularized.lean`, `ddj/MeasureCylinder/UVLimit.lean`
- `ddj/StochasticQuant/DaPratoDebussche.lean`
- `ddj/StochasticEst/InfiniteVolumeBound.lean`
- `ddj/Energy/EnergyEstimate.lean`
- `ddj/InfiniteVolume/Tightness.lean`
- `ddj/Integrability/Regularity.lean`
- `ddj/ReflectionPositivity/RPPlane.lean`
- `ddj/EuclideanInvariance/Invariance.lean`

---

## OS axiom formulations (OSAxioms.lean)

The OS axioms are stated for a probability measure μ on S'(ℝ²) =
`Configuration (ContinuumTestFunction 2)`, matching the formulations in
`OSforGFF/OS_Axioms.lean` (adapted from d=4 to d=2).

### Infrastructure definitions

| Definition | Type | Description |
|-----------|------|-------------|
| `SpaceTime2` | `Type` | `EuclideanSpace ℝ (Fin 2)` — Euclidean ℝ² |
| `TestFunction2` | `Type` | `ContinuumTestFunction 2` = `SchwartzMap (EuclideanSpace ℝ (Fin 2)) ℝ` |
| `TestFunction2ℂ` | `Type` | `SchwartzMap SpaceTime2 ℂ` — complex test functions |
| `FieldConfig2` | `Type` | `Configuration (ContinuumTestFunction 2)` = `WeakDual ℝ S(ℝ²)` |
| `E2` | `structure` | Euclidean motion: `R : O2`, `t : SpaceTime2` |
| `O2` | `Type` | `LinearIsometry (RingHom.id ℝ) SpaceTime2 SpaceTime2` |
| `generatingFunctional μ f` | `ℂ` | `Z[f] = ∫ exp(i⟨ω, f⟩) dμ(ω)` for real f |
| `generatingFunctionalℂ μ J` | `ℂ` | Complex extension of Z |
| `timeReflection2 p` | `SpaceTime2` | `(t, x) ↦ (-t, x)` |
| `hasPositiveTime2 p` | `Prop` | First coordinate > 0 |
| `positiveTimeSubmodule2` | `Submodule ℝ TestFunction2` | Test functions with `tsupport ⊆ {t > 0}` |
| `PositiveTimeTestFunction2` | `Type` | Elements of `positiveTimeSubmodule2` |

### Operations on Schwartz space (all proved, 0 axioms in OSAxioms.lean)

| Definition | Signature | Construction |
|------------|-----------|-------------|
| `euclideanAction2 g` | `TestFunction2 →L[ℝ] TestFunction2` | `compCLMOfAntilipschitz` with inverse Euclidean action |
| `euclideanAction2ℂ g` | `TestFunction2ℂ →L[ℝ] TestFunction2ℂ` | Same for complex test functions |
| `compTimeReflection2` | `TestFunction2 →L[ℝ] TestFunction2` | `compCLMOfContinuousLinearEquiv` with time reflection CLE |
| `SchwartzMap.translate a` | `TestFunction2 →L[ℝ] TestFunction2` | `compCLMOfAntilipschitz` with translation |

### OS axiom definitions

**OS0 (Analyticity)** — `OS0_Analyticity μ`

```
∀ (n : ℕ) (J : Fin n → TestFunction2ℂ),
  AnalyticOn ℂ (fun z : Fin n → ℂ =>
    generatingFunctionalℂ μ (∑ i, z i • J i)) Set.univ
```

Z[Σ zᵢJᵢ] is entire analytic in z ∈ ℂⁿ for any complex test functions Jᵢ.

**OS1 (Regularity)** — `OS1_Regularity μ`

```
∃ (p : ℝ) (c : ℝ), 1 ≤ p ∧ p ≤ 2 ∧ c > 0 ∧
  ∀ (f : TestFunction2ℂ),
    ‖generatingFunctionalℂ μ f‖ ≤
      Real.exp (c * (∫ x, ‖f x‖ ∂volume + ∫ x, ‖f x‖ ^ p ∂volume))
```

Exponential bound on Z[f] controlled by L¹ and Lᵖ norms of the test function.
For P(Φ)₂, the relevant bound is `‖Z[f]‖ ≤ exp(c · ‖f‖²_{H^{-1}})` from
Nelson's hypercontractive estimate.

**OS2 (Euclidean Invariance)** — `OS2_EuclideanInvariance μ`

```
∀ (g : E2) (f : TestFunction2ℂ),
  generatingFunctionalℂ μ f =
  generatingFunctionalℂ μ (euclideanAction2ℂ g f)
```

Z[g·f] = Z[f] for all g ∈ E(2) = ℝ² ⋊ O(2).

**OS3 (Reflection Positivity)** — `OS3_ReflectionPositivity μ`

```
∀ (n : ℕ) (f : Fin n → PositiveTimeTestFunction2) (c : Fin n → ℝ),
  0 ≤ ∑ i, ∑ j, c i * c j *
    (generatingFunctional μ
      ((f i).val - compTimeReflection2 ((f j).val))).re
```

The RP matrix `Mᵢⱼ = Re(Z[fᵢ - Θfⱼ])` is positive semidefinite for
positive-time test functions fᵢ and real coefficients cᵢ.

**OS4 (Clustering)** — `OS4_Clustering μ`

```
∀ (f g : TestFunction2) (ε : ℝ), ε > 0 →
  ∃ (R : ℝ), R > 0 ∧ ∀ (a : SpaceTime2), ‖a‖ > R →
  ‖generatingFunctional μ (f + SchwartzMap.translate a g)
   - generatingFunctional μ f * generatingFunctional μ g‖ < ε
```

Correlations factor at large separations: Z[f + T_a g] → Z[f]·Z[g] as ‖a‖ → ∞.

**OS4 (Ergodicity)** — `OS4_Ergodicity μ`

Time-averaged generating functional converges to the product:
`(1/T) ∫₀ᵀ Re(Z[f + τ_{(t,0)} g]) dt → Re(Z[f]) · Re(Z[g])` as T → ∞.

### Full axiom bundle

`SatisfiesFullOS μ` is a structure with fields:
- `os0 : OS0_Analyticity μ`
- `os1 : OS1_Regularity μ`
- `os2 : OS2_EuclideanInvariance μ`
- `os3 : OS3_ReflectionPositivity μ`
- `os4_clustering : OS4_Clustering μ`
- `os4_ergodicity : OS4_Ergodicity μ`

### Sorries in OSAxioms.lean

None — all sorries have been resolved.

### Proved theorems in OSAxioms.lean

| Theorem | Description |
|---------|-------------|
| `timeReflection2_involution` | `Θ(Θp) = p` — time reflection is an involution |
| `positiveTimeSubmodule2` | Submodule proof: zero_mem, add_mem, smul_mem |

---

## Axiom inventory (all active files)

### Difficulty rating

- **Easy**: Straightforward from Mathlib or simple calculation
- **Medium**: Requires nontrivial but standard arguments
- **Hard**: Deep analytic result, significant proof effort
- **Infrastructure**: Needs Mathlib API that may not exist yet

### Phase 1: Wick ordering and lattice measure

All Phase 1 axioms have been proved or removed. `wickConstant_log_divergence`
(a pure computation, unused by the proof chain) was moved to `Unused/WickAsymptotics.lean`.

### Phase 2: Transfer matrix and reflection positivity

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| ~~`transferOperatorCLM`~~ | L2Operator | ✅ **Defined** | Transfer matrix as `M_w ∘L Conv_G ∘L M_w` via kernel factorization. Uses `mulCLM` (L2Multiplication) and `convCLM` (L2Convolution). |
| ~~`young_convolution_memLp`~~ | L2Convolution | ✅ **Proved** | Via Cauchy-Schwarz + Tonelli + translation invariance of Haar measure. |
| ~~`young_convolution_bound`~~ | L2Convolution | ✅ **Proved** | Young's inequality norm bound via `young_eLpNorm_bound`. |
| ~~`young_convolution_ae_add`~~ | L2Convolution | ✅ **Proved** | Via Fubini on `‖g‖` × `fᵢ²` (both L¹), bound `ab ≤ a + ab²`, `ConvolutionExistsAt.distrib_add`. |
| ~~`convCLM_isSelfAdjoint_of_even`~~ | L2Convolution | ✅ **Proved** | Self-adjointness of convolution by even kernel. Proved via `integral_mul_conv_eq` Fubini identity. |
| ~~`integral_mul_conv_eq`~~ | L2Convolution | ✅ **Proved** | Fubini identity: `∫ h·(g⋆f) = ∫ (g⋆h)·f` for even g. Proved via product integrability (AM-GM + Tonelli + translation invariance), `integral_integral_swap`, `convolution_eq_swap`. |
| ~~`transferOperator_isSelfAdjoint`~~ | L2Operator | ✅ **Proved** | Self-adjointness of `A ∘ B ∘ A` from `mulCLM_isSelfAdjoint` and `convCLM_isSelfAdjoint_of_even` for the Gaussian kernel. |
| ~~`transferOperator_isCompact`~~ | L2Operator | ✅ **Proved** | Compactness from `hilbert_schmidt_isCompact` (proved) + `transferWeight_memLp_two` (w ∈ L²) + `transferGaussian_norm_le_one` (‖G‖ ≤ 1). |
| `integral_operator_l2_kernel_compact` | L2Operator | Medium | Convolution-form integral operators with L² kernels are compact (Hilbert-Schmidt theorem). Reed-Simon I, Thm VI.23. |
| ~~`hilbert_schmidt_isCompact`~~ | L2Operator | ✅ **Proved** | Proved from `integral_operator_l2_kernel_compact` via `tensor_kernel_memLp` (Tonelli + ‖g‖²≤‖g‖ bound) + `mul_conv_integral_rep` (integral representation). |
| `transferOperator_spectral` | L2Operator | **Proved** | Spectral decomposition from `compact_selfAdjoint_spectral` (gaussian-field). |
| ~~`jentzsch_theorem`~~ | Jentzsch | ✅ **Proved** | Jentzsch's theorem for compact self-adjoint positivity-improving operators: ground eigenvalue simple with strict spectral gap. Reed-Simon IV, XIII.43–44. Full proof in `JentzschProof.lean`, bridge via `IsPositivityImproving.toPI'`. |
| ~~`transferOperator_positivityImproving`~~ | Jentzsch | ✅ **Proved** | Transfer kernel K(ψ,ψ') = w(ψ)G(ψ-ψ')w(ψ') > 0 everywhere, so T maps nonneg nonzero f to a.e. strictly positive Tf. Proved via T = M_w ∘ Conv_G ∘ M_w factorization, Cauchy-Schwarz for L² integrability, measure-preserving translation, and `integral_pos_iff_support_of_nonneg_ae`. |
| ~~`transferOperator_strictly_positive_definite`~~ | Jentzsch | ✅ **Proved** | ⟨f, Tf⟩ > 0 for f ≠ 0. Proved via self-adjointness of M_w (⟨f, M_w(Conv_G(M_w f))⟩ = ⟨M_w f, Conv_G(M_w f)⟩), injectivity of M_w (w > 0), and Gaussian convolution strict PD axiom. |
| ~~`inner_convCLM_pos_of_fourier_pos`~~ | GaussianFourier | ✅ **Proved** | Convolution with Gaussian exp(-½‖·‖²) is strictly PD on L²: ⟨f, Conv_G f⟩ = ∫ |f̂(k)|² Ĝ(k) dk > 0. Proved via Fourier representation axiom + `fourier_gaussian_pos` + Plancherel injectivity. |
| `fourier_representation_convolution` | GaussianFourier | Medium | L² Fourier representation: ⟨f, g⋆f⟩ = ∫ Re(ĝ)·‖f̂‖². Proof via Schwartz density (`DenseRange.equalizer`): both sides continuous, agree on Schwartz by `Real.fourier_smul_convolution_eq` + Parseval. Blocked by L² convolution theorem not yet in Mathlib. |
| ~~`l2SpatialField_hilbertBasis_nontrivial`~~ | Jentzsch | ✅ **Proved** | Any Hilbert basis of L²(ℝ^Ns) has ≥ 2 elements. Proved via indicator functions on disjoint balls + orthogonality. |
| ~~`transferOperator_inner_nonneg`~~ | Jentzsch | ✅ **Proved** | ⟨f, Tf⟩ ≥ 0. Derived from strict PD (> 0 for f ≠ 0, = 0 for f = 0). |
| ~~`transferOperator_eigenvalues_pos`~~ | Jentzsch | ✅ **Proved** | λᵢ > 0. From ⟨bᵢ, Tbᵢ⟩ = λᵢ‖bᵢ‖² > 0 by strict PD. |
| ~~`transferOperator_ground_simple`~~ | Jentzsch | ✅ **Proved** | Ground-state simplicity. Derived from Jentzsch + eigenvalue positivity + nontriviality. |
| ~~`action_decomposition`~~ | OS3_RP_Lattice | ✅ **Proved** | S_plus = V/2, using sum-reindexing by site-reflection bijection (timeReflection2D is involution). |
| ~~`lattice_rp`~~ | OS3_RP_Lattice | ✅ **Proved** | RP inequality for `interactingLatticeMeasure`. Proved from `gaussian_rp_with_boundary_weight` via time-slice decomposition V=V₊+V₀+V₋, reflection symmetry V₋(φ)=V₊(Θφ), and integrand factorization. |
| ~~`gaussian_rp_with_boundary_weight`~~ | OS3_RP_Lattice | ✅ **Proved** | Derived from `gaussian_density_rp` via `evalMapMeasurableEquiv` density bridge: `∫ F(evalMap ω) dμ = (∫ F·ρ) / (∫ ρ)`, ratio ≥ 0. |
| ~~`gaussian_density_rp`~~ | OS3_RP_Lattice | ✅ **Proved** | Core Gaussian RP at density level: ∫ G(φ)·G(Θφ)·w(φ)·ρ(φ) dφ ≥ 0. Non-integrable case proved; integrable case: density factorization ρ = exp(-½A)·exp(-½C) proved (linearity + self-adjointness + block-zero), A-independence of v₋ proved. Final step via `gaussian_rp_perfect_square` theorem (factors G out) + `gaussian_rp_cov_perfect_square` axiom (COV + perfect square). |
| ~~`lattice_rp_matrix`~~ | OS3_RP_Lattice | ✅ **Proved** | Matrix form of RP via cos(u-v) expansion + `lattice_rp`. |
| ~~`rp_from_transfer_positivity`~~ | OS3_RP_Lattice | ✅ **Proved** | ⟨f, T^n f⟩ ≥ 0 via `transferOperatorCLM`. |
| `gaussian_rp_cov_perfect_square` | OS3_RP_Lattice | Medium | Second Fubini + COV + perfect square for Gaussian RP. Decomposes into: (1) second Fubini splitting v=(v₋,v₀), (2) factoring out boundary terms, (3) COV identity (the hard part: time-reflection on S₋ using `massOperatorMatrix_timeNeg_invariant`), (4) Fubini swap u↔v₀, (5) perfect square `∫ w·exp·[∫ G·exp]² ≥ 0`. Private axiom. |

### Phase 3: Spectral gap and clustering

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| `spectral_gap_uniform` | SpectralGap | Hard | Mass gap bounded below uniformly in a. Key input: the interaction is a bounded perturbation of the free field in the sense of Kato-Rellich, and the free mass gap is m > 0. Needs careful control of the perturbation as a→0. |
| `spectral_gap_lower_bound` | SpectralGap | Hard | m_phys ≥ c·m_bare. Quantitative bound on the physical mass. |
| ~~`connectedTwoPoint_nonneg_delta`~~ | OS4_MassGap | ✅ **Proved** | Variance nonnegativity: direct proof via ∫(X-E[X])² ≥ 0. |
| ~~`two_point_clustering_lattice`~~ | OS4_MassGap | ✅ **Proved** | Exponential decay bound using `finLatticeDelta`, `massGap`, and the cyclic torus time separation. |
| ~~`general_clustering_lattice`~~ | OS4_MassGap | ✅ **Proved** | Bounded `F`, `G` with `G` on time-shifted config `latticeConfigEuclideanTimeShift N R ω`, decaying in `latticeEuclideanTimeSeparation N R`. |
| ~~`clustering_implies_ergodicity`~~ | OS4_Ergodicity | ✅ **Proved** | Exponential clustering → ergodicity of time translations. |
| ~~`unique_vacuum`~~ | OS4_Ergodicity | ✅ **Proved** | From `transferOperator_ground_simple_spectral`. |
| ~~`exponential_mixing`~~ | OS4_Ergodicity | ✅ **Proved** | Exponential mixing from mass gap. |
| ~~`os4_lattice`~~ | OS4_Ergodicity | ✅ **Proved** | Lattice satisfies OS4 (assembles the above). |

Note: `partitionFunction_eq_trace`, `hamiltonian_selfadjoint`, `hamiltonian_compact_resolvent`,
`ground_state_simple`, `ground_state_positive`, `ground_state_smooth` were removed in earlier
refactoring (functionality consolidated into L2Operator axioms).

### Phase 4: Continuum limit

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| ~~`latticeEmbed`~~ | Embedding | ✅ Proved | Constructed via `SchwartzMap.mkCLMtoNormedSpace`. Bound: `|ι_a(φ)(f)| ≤ (a^d·Σ|φ(x)|)·seminorm(0,0)(f)`. |
| ~~`latticeEmbed_eval`~~ | Embedding | ✅ Proved | `rfl` from construction. |
| ~~`latticeEmbed_measurable`~~ | Embedding | ✅ Proved | `configuration_measurable_of_eval_measurable` + continuity of finite sum. |
| ~~`latticeEmbedLift`~~ | Embedding | ✅ Proved | Constructed as `latticeEmbed d N a ha (fun x => ω (Pi.single x 1))`. |
| ~~`latticeEmbedLift_measurable`~~ | Embedding | ✅ Proved | `configuration_measurable_of_eval_measurable` + `configuration_eval_measurable`. |
| `second_moment_uniform` | Tightness | Hard | ∫|Φ_a(f)|² dν_a ≤ C(f) uniformly in a. Key input: Nelson's hypercontractive estimate + convergence of lattice propagator. |
| `moment_equicontinuity` | Tightness | Hard | Equicontinuity of moments in f. Needs Schwartz seminorm control. |
| ~~`continuumMeasures_tight`~~ | Tightness | **PROVED** | Mitoma-Chebyshev + uniform second moments. `continuum_second_moment_uniform` derives the uniform bound from `interacting_moment_bound` (at `n=1, p=2`) + `gaussian_second_moment_uniform`. |
| ~~`gaussian_hypercontractivity_continuum`~~ | Hypercontractivity | **Proved** | Gaussian hypercontractivity in continuum-embedded form. Proved from `gaussian_hypercontractive` (gaussian-field) via pushforward + `latticeEmbedLift_eval_eq`. |
| ~~`wickMonomial_latticeGaussian`~~ | Hypercontractivity | **Theorem** | Proved from `wickConstant_eq_variance` + marginal Gaussian + `gaussian_hermite_zero_mean`. |
| ~~`wickConstant_eq_variance`~~ | Hypercontractivity | **Theorem** | Proved generically from `GeneralResults/LatticeProductDFT.lean`: product-DFT Parseval plus the abstract spectral covariance formula identify the site variance with the Wick constant in arbitrary dimension. |
| ~~`gaussian_hermite_zero_mean`~~ | Hypercontractivity | **Proved** | 1D: ∫ He_n dN(0,σ²) = 0 for n ≥ 1; polynomial integrability under `gaussianReal`. |
| ~~`wickPolynomial_uniform_bounded_below`~~ | WickPolynomial | **Proved** | Wick polynomial P(c,x) ≥ -A uniformly for c ∈ [0,C]. Coefficient continuity + compactness + leading term dominance. |
| ~~`exponential_moment_bound`~~ | Hypercontractivity | **Proved** | ∫ exp(-2V_a) dμ_{GFF} ≤ K. Proved from `wickPolynomial_uniform_bounded_below` + pointwise exp bound + probability measure. |
| ~~`interacting_moment_bound`~~ | Hypercontractivity | **Proved** | Bounds interacting L^{pn} moments in terms of FREE Gaussian L^{2n} moments via Cauchy-Schwarz density transfer. Proved from `exponential_moment_bound`, `partitionFunction_ge_one`, `pairing_memLp`, and Hölder/Cauchy-Schwarz. |
| ~~`partitionFunction_ge_one`~~ | Hypercontractivity | **Proved** | Z_a ≥ 1 by Jensen's inequality (`ConvexOn.map_integral_le`) + `interactionFunctional_mean_nonpos`. |
| ~~`interactionFunctional_mean_nonpos`~~ | Hypercontractivity | **Proved** | ∫ V dμ_GFF ≤ 0. Proved from `wickMonomial_latticeGaussian` (Hermite orthogonality) + linearity + `P.coeff_zero_nonpos`. |
| `prokhorov_configuration_sequential` | Convergence | Infrastructure | Sequential extraction axiom directly on `Configuration (ContinuumTestFunction d)`; avoids global Polish/Borel assumptions on full weak-* dual. |
| ~~`prokhorov_sequential`~~ | Convergence | ~~Infrastructure~~ | **Proved** — generic Polish-space sequential Prokhorov theorem (kept as theorem, not used by `continuumLimit`). |
| ~~`schwinger2_convergence`~~ | Convergence | **PROVED** | 2-point Schwinger functions converge. Proved from `schwinger_n_convergence`. |
| `schwinger_n_convergence` | Convergence | Hard | n-point Schwinger functions converge along subsequence. Diagonal subsequence extraction. |
| `continuumLimit_nontrivial` | Convergence | Hard | ∫ (ω f)² dμ > 0 for some f. Free field two-point function gives lower bound. |
| `continuumLimit_nonGaussian` | Convergence | Hard | Connected 4-point function ≠ 0. Perturbation theory gives O(λ) contribution. |
| `continuum_exponential_moment_bound` | AxiomInheritance | Hard | Mixed `L¹`/Green exponential-moment input `∫ exp(|ω f|) ≤ exp(c₁∫|f| + c₂ G(f,f))` used to derive the OS0/OS1 wrappers. |
| ~~`os3_for_continuum_limit`~~ | OS2_WardIdentity | ✅ **Proved** | Standard OS3 from inline approximant RP in `IsPphi2Limit` + entrywise characteristic-functional convergence. |
| `continuum_exponential_clustering` | AxiomInheritance | Hard | Continuum characteristic-functional clustering input from the spectral-gap package. |
| ~~`os0_for_continuum_limit / os1_for_continuum_limit / os4_for_continuum_limit`~~ | AxiomInheritance | **Theorem** | Derived wrappers packaging the analytic and clustering inputs into the generic OS bundle. |

### Phase 4G: Gaussian continuum limit

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| `latticeGreenBilinear_basis_tendsto_continuum` | PropagatorConvergence | Medium | Spectral lattice Green bilinear on Dynin-Mityagin basis pairs → continuum Fourier Green bilinear. `latticeGreenBilinear_tendsto_continuum` and `propagator_convergence` are now derived theorems. |
| ~~`gaussianContinuumMeasures_tight`~~ | GaussianTightness | **PROVED for `d > 0`** | Tightness via `configuration_tight_of_uniform_second_moments` + integrability through lattice embedding. The excluded `d = 0` case is a separate Dynin-Mityagin / Schwartz-space infrastructure issue. |
| ~~`gaussianLimit_isGaussian`~~ | GaussianLimit | **PROVED** | Weak limits of Gaussian measures are Gaussian. Proved via 1D evaluation marginals and `weakLimit_centered_gaussianReal`. |

**Proved theorems (GaussianContinuumLimit/):**
- `gaussianContinuumMeasure_isProbability`: Pushforward of probability measure is probability.
- `embeddedTwoPoint_eq_covariance`: Change-of-variables reducing pushforward integral to lattice GFF.
- `embeddedTwoPoint_eq_latticeGreenBilinear`: Canonical reduction of the embedded two-point function to the lattice spectral Green bilinear form.
- `embeddedTwoPoint_eq_spectral_sum`: Explicit spectral-sum form of the same reduction.
- `propagator_convergence`: Now a theorem, deduced from `embeddedTwoPoint_eq_latticeGreenBilinear` and the deeper spectral convergence axiom.
- `gaussian_second_moment_uniform`: Uniform second moment bound from `embeddedTwoPoint_uniform_bound`.
- `gaussianContinuumLimit_exists`: Subsequential weak limit via Prokhorov extraction.
- `gaussianContinuumLimit_nontrivial`: `∫ (ω f)² dμ > 0` from `continuumGreenBilinear_pos`.
- `gaussian_feeds_interacting_tightness`: Bridge — Gaussian bound feeds Cauchy-Schwarz density transfer.
- `gaussianContinuumMeasures_tight`: Tightness of embedded GFF measures via `configuration_tight_of_uniform_second_moments`, now proved for `d > 0`.
- `gaussianLimit_isGaussian`: Weak limits of the embedded Gaussian measures are Gaussian.
- `gaussianContinuumMeasure_sq_integrable`: Integrability of `(ω f)²` through lattice embedding via `pairing_product_integrable`.

**Open work in this slice:**
- `latticeGreenBilinear_basis_tendsto_continuum`: remaining analytic convergence core for the Gaussian continuum route.
- Optional full generality for `gaussianContinuumMeasures_tight` (`d = 0` case): add a dedicated `DyninMityaginSpace (ContinuumTestFunction 0)` instance, then audit `GaussianLimit.lean` and `ContinuumLimit/Convergence.lean` for other `d > 0` dependencies.

Note: `os1_inheritance` is a theorem (not axiom) — OS1 transfers trivially since |cos(·)| ≤ 1.

### Phase 4T: Torus continuum limit (UV only, L fixed)

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| ~~`torus_propagator_convergence`~~ | TorusPropagatorConvergence | **PROVED** | Proved via gaussian-field `lattice_green_tendsto_continuum` axiom. Chain: `torusEmbeddedTwoPoint` → `lattice_cross_moment` → `covariance` → axiom. |
| ~~`torusEmbeddedTwoPoint_uniform_bound`~~ | TorusPropagatorConvergence | **PROVED** | `E[Φ_N(f)²] ≤ C` uniformly in N. Eigenvalue lower bound `λ_k ≥ m²` + Parseval + Riemann sum bound on compact torus. |
| ~~`torusContinuumMeasures_tight`~~ | TorusTightness | **PROVED** | Proved from `configuration_tight_of_uniform_second_moments` (Mitoma-Chebyshev axiom) + `torus_second_moment_uniform`. |
| `configuration_tight_of_uniform_second_moments` | TorusTightness | Medium | ✅ Verified (DT 2026-03-11). Mitoma-Chebyshev: on nuclear dual (`DyninMityaginSpace`), uniform 2nd moments ⟹ tightness. Mitoma (1983), Simon §V.1. Nuclearity essential (ℓ² counterexample). |
| ~~`torusGaussianMeasure_isGaussian`~~ | TorusGaussianLimit | **PROVED** | Lattice GFF pushforward is Gaussian. MGF: `E[e^{ω(f)}] = exp(½ E[ω(f)²])`. |
| ~~`torusGaussianLimit_isGaussian`~~ | TorusGaussianLimit | **PROVED** | Weak limits of Gaussians on torus are Gaussian. Proved via `pushforward_eval_gaussianReal` (MGF matching → complexMGF extension → measure equality) + `weakLimit_centered_gaussianReal`. |
| ~~`weakLimit_centered_gaussianReal`~~ | TorusGaussianLimit | **PROVED** | Weak limits of centered Gaussians on ℝ are centered Gaussian. Proved via charFun decomposition into cos/sin integrals, variance extraction from log limit, and `Measure.ext_of_charFun`. |
| `torusLimit_covariance_eq` | TorusGaussianLimit | Medium | Weak convergence transfers second moments. Uniform integrability from `torusEmbeddedTwoPoint_uniform_bound`. |
| `gaussian_measure_unique_of_covariance` | TorusGaussianLimit | Medium | Gaussian on nuclear space determined by covariance. Bochner-Minlos uniqueness. |
| `torusGaussianMeasure_z2_symmetric` | TorusGaussianLimit | **PROVED** | Lattice GFF pushforward is Z₂-symmetric: both `neg_* ν` and `ν` are Gaussian with same covariance, hence equal by `gaussian_measure_unique_of_covariance`. |
| `z2_symmetric_of_weakLimit` | TorusGaussianLimit | **PROVED** | Z₂ symmetry transfers through weak limits. Proved via configBasisEval pushforward to ℝ^ℕ (Polish) + Portmanteau. |
| ~~`torusGaussianLimit_fullConvergence`~~ | TorusGaussianLimit | **PROVED** | Full sequence convergence via `Filter.tendsto_of_subseq_tendsto` + Prokhorov + Gaussian uniqueness. |
| `torus_interacting_tightness` | TorusInteractingLimit | Medium | Cauchy-Schwarz density transfer from Gaussian tightness. Nelson's estimate + hypercontractivity. |

| ~~`torusGaussianLimit_characteristic_functional`~~ | TorusOSAxioms | **PROVED** | CF `E[e^{iωf}] = exp(-½G(f,f))` from MGF via `complexMGF` analytic continuation + `charFun_gaussianReal`. |
| `torusPositiveTimeSubmodule` | TorusOSAxioms | Infrastructure | Submodule of torus test functions with time support in (0, L/2). Nuclear tensor product lacks pointwise evaluation, so submodule axiomatized. |
| ~~`torusGaussianLimit_complex_cf_quadratic`~~ | TorusOSAxioms | **PROVED** | Complex CF of Gaussian = exp(-½ ∑ᵢⱼ zᵢzⱼ G(Jᵢ,Jⱼ)). Proved via `torusGeneratingFunctionalℂ_analyticOnNhd` + `analyticOnNhd_eq_of_eqOn_reals`. |
| ~~`torusGeneratingFunctionalℂ_analyticOnNhd`~~ | TorusOSAxioms | **PROVED** | Analyticity of complex generating functional on ℂⁿ. Proved via `analyticOnNhd_integral` + `gaussian_exp_sum_abs_integrable` (AM-GM induction). |
| `torusLattice_rp` | TorusOSAxioms | Medium | Matrix-form reflection positivity for lattice GFF on torus. For positive-time test functions, Σᵢⱼ cᵢcⱼ Re(Z[fᵢ - Θfⱼ]) ≥ 0. Fubini + perfect-square argument. |
| ~~`torusGaussianLimit_complex_cf_norm`~~ | TorusOSAxioms | **ELIMINATED** | Axiom eliminated: OS1 proved directly via triangle inequality `‖Z_ℂ‖ ≤ ∫ exp(-ω(f_im)) dμ = exp(½G₂₂)` without needing exact norm. |
| ~~`torusContinuumGreen_continuous_diag`~~ | TorusOSAxioms | **PROVED** | Proved via `greenFunctionBilinear_continuous_diag` in gaussian-field. Locally uniform convergence of partial sums (Weierstrass M-test + coeff_decay). |

**Proved theorems (TorusContinuumLimit/):**
- `torusEmbedLift_measurable`: Measurability of torus embedding lift.
- `torusContinuumMeasure_isProbability`: Pushforward of probability measure is probability.
- `torus_second_moment_uniform`: Uniform second moment bound from `torusEmbeddedTwoPoint_uniform_bound`.
- `torusGaussianLimit_exists`: **PROVED** — Prokhorov extraction on Polish torus (no `prokhorov_configuration_sequential` axiom needed).
- `torusGaussianLimit_converges`: **PROVED** — Full sequence convergence (not just subsequential). From Gaussianity + covariance uniqueness.
- `torusGaussianLimit_nontrivial`: `∫ (ω f)² dμ > 0` from `torusContinuumGreen_pos`.
- `torusInteractingMeasure_isProbability`: Interacting pushforward is probability.
- `torusInteractingLimit_exists`: **PROVED** — Prokhorov extraction for interacting measures.
- `torusContinuumGreen_nonneg`: `G_L(f,f) ≥ 0` from `greenFunctionBilinear_nonneg` (proved in gaussian-field).
- `torusContinuumGreen_continuous_diag`: **PROVED** — f ↦ G_L(f,f) continuous. Via `greenFunctionBilinear_continuous_diag` in gaussian-field (Weierstrass M-test + coeff_decay + locally uniform convergence).
- `torusGaussianLimit_characteristic_functional`: **PROVED** — CF formula `E[e^{iωf}] = exp(-½G(f,f))`. From MGF agreement → `eqOn_complexMGF_of_mgf` → `charFun_gaussianReal` (Mathlib Gaussian CF).
- `torusGaussianLimit_os0`: **PROVED** -- OS0 analyticity. Rewrites complex CF as exp(-½ ∑ zᵢzⱼ Gᵢⱼ) via `torusGaussianLimit_complex_cf_quadratic`, then exp-of-polynomial is analytic via `AnalyticAt.cexp'` + `Finset.analyticAt_fun_sum` + `ContinuousLinearMap.proj.analyticAt`.
- `torusGaussianLimit_os1`: **PROVED** — OS1 regularity with q(f)=G_L(f,f), c=½. Triangle inequality: `‖Z_ℂ‖ ≤ ∫ exp(-ω(f_im)) dμ = exp(½G₂₂) ≤ exp(½(G₁₁+G₂₂))` via `norm_integral_le`, `Complex.norm_exp`, Gaussian MGF, and `torusContinuumGreen_nonneg`.
- `torusMatrixRP_of_weakLimit`: **PROVED** — Matrix RP transfers through weak limits via Re(Z[g]) = ∫ cos(ω(g)) dμ (bounded continuous) + `tendsto_finset_sum` + `ge_of_tendsto'`.
- `torusGaussianLimit_os3`: **PROVED** — OS3 reflection positivity from `torusMatrixRP_of_weakLimit` + `torusLattice_rp` + `torusGaussianLimit_fullConvergence`.

**Sorries (provable):**
- ~~`torusEmbeddedTwoPoint_uniform_bound`~~: **PROVED.** `latticeTestFn_norm_sq_bounded` filled via DM expansion + Fourier basis C^0 bounds.

**Former sorries (now resolved):**
- ~~`torusContinuumGreen`~~: Now defined as `greenFunctionBilinear` from gaussian-field `HeatKernel/Bilinear.lean`.
- ~~`torusContinuumGreen_pos`~~: Now proved from `greenFunctionBilinear_pos`.
- ~~Z₂ symmetry~~: Now axiomatized as `torusGaussianMeasure_z2_symmetric` + `z2_symmetric_of_weakLimit`.
- ~~Full sequence convergence~~: Now axiomatized as `torusGaussianLimit_fullConvergence`.

### Phase 5: Euclidean invariance (OS2) and OS proof chains

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| ~~`latticeAction_translation_invariant`~~ | OS2_WardIdentity | ~~Easy~~ | **Proved** — relabeling via `Equiv.subRight`. |
| ~~`cesaro_set_integral_tendsto`~~ | GeneralResults/FunctionalAnalysis | ~~Medium~~ | **Proved** — moved to GeneralResults as pure Mathlib result. |
| ~~`tendsto_zero_pow_mul_one_add_abs_log_pow`~~ | GeneralResults/FunctionalAnalysis | ~~Medium~~ | **Proved** — generalized positive-power log-decay lemma: `a_n^m (1 + |log a_n|)^p → 0` for every natural `m ≥ 1`, with the former square case now a corollary used by OS2. |
| ~~`norm_configuration_expIntegral_sub_le_integral_cexp_eval_dist`~~ | GeneralResults/FunctionalAnalysis | ~~Medium~~ | **Proved** — generic characteristic-functional defect estimate `‖∫e^{i⟨ω,g⟩} - ∫e^{i⟨ω,f⟩}‖ ≤ ∫‖e^{i⟨ω,g⟩} - e^{i⟨ω,f⟩}‖`, now specialized by OS2. |
| ~~`pphi2_generating_functional_real`~~ | CharacteristicFunctional | ~~Medium~~ | **Proved** — from `pphi2_measure_neg_invariant` via conj(Z[f])=Z[f]. |
| ~~`pphi2_measure_neg_invariant`~~ | CharacteristicFunctional | ~~Medium~~ | **Proved** — Z₂ symmetry baked into `IsPphi2Limit` definition. |
| ~~`generatingFunctional_translate_continuous`~~ | CharacteristicFunctional | ~~Easy~~ | **Proved** — via DCT (bound 1) + `continuous_timeTranslationSchwartz` from TimeTranslation.lean. |
| ~~`norm_generatingFunctional_le_one`~~ | CharacteristicFunctional | ✅ **Proved** | ‖Z[f]‖ ≤ 1 from norm_integral ≤ ∫ norm + ‖exp(ix)‖=1. |
| ~~`os4_clustering_implies_ergodicity`~~ | CharacteristicFunctional | ✅ **Proved** | OS4_Clustering → OS4_Ergodicity via reality of Z + Cesàro convergence. |
| ~~`latticeMeasure_translation_invariant`~~ | OS2_WardIdentity | ~~Medium~~ | **Proved** — density bridge + change of variables. BW and ρ invariant under translation, Lebesgue measure preserved by `piCongrLeft`. |
| ~~`translation_invariance_continuum`~~ | OS2_WardIdentity | ~~Medium~~ | **Proved** — strengthened `IsPphi2Limit` with `cf_tendsto` + `lattice_inv` fields; continuum invariance via `tendsto_nhds_unique_of_eventuallyEq`. |
| `rotation_cf_defect_polylog_bound` | OS2_WardIdentity | Hard | Remaining OS2 axiom: one-point super-renormalizable bound on the canonical characteristic-functional defect `rotationCFDefect`, uniform in the lattice size `N` and scaling like `C·a²·(1+|log a|)^p`. |
| `canonical_continuumMeasure_cf_tendsto` | AxiomInheritance | Hard | Coupled UV/IR bridge: canonical `continuumMeasure 2 (N n) P (a n) mass` approximants converge in characteristic functionals to `μ` along `a_n → 0`, `N_n → ∞`, and physical volume `(N_n : ℝ) * a_n → ∞`. |
| `continuum_exponential_moment_bound` | AxiomInheritance | Hard | Project-level continuum exponential-moment bridge `∫ exp(|ω f|) dμ ≤ exp(c₁∫|f| + c₂ G(f,f))`. Single remaining OS0/OS1 analytic input. |
| ~~`analyticOn_generatingFunctionalC`~~ | CharacteristicFunctional | ~~Medium~~ | **Proved** — via `analyticOnNhd_integral`, the finite-source pairing rewrite, and compact domination from exponential moments of `schwartzRe`/`schwartzIm`. |
| ~~`continuum_exponential_moments`~~ | AxiomInheritance | ~~Hard~~ | **Proved** — derived by scaling from `continuum_exponential_moment_bound`. Feeds OS0 + OS1. |
| ~~`exponential_moment_schwartz_bound`~~ | AxiomInheritance | ~~Medium~~ | **Proved** — combines `continuum_exponential_moment_bound` with `continuumGreenBilinear_le_mass_inv_sq`. |
| ~~`rotation_invariance_continuum`~~ | OS2_WardIdentity | Hard | **Proved** — canonical CF convergence for `continuumMeasure` + `anomaly_vanishes` + Mathlib logarithmic asymptotics yield `Z[R·f] = Z[f]`. Feeds OS2. |
| `continuum_exponential_clustering` | AxiomInheritance | Hard | `‖Z[f+τ_a g] - Z[f]Z[g]‖ ≤ C·exp(-m₀·‖a‖)`. Spectral gap → exp clustering. Feeds OS4. |

**Proof chain theorems** (all fully proved, no sorries):
- `ward_identity_lattice`: Ward identity bound (**proved**)
- `anomaly_scaling_dimension`: lattice dispersion Taylor error bound (**proved**, cos_bound + crude bound)
- `configuration_cexp_eval_sub_integrand` / `configuration_cexp_eval_dist`: generic characteristic-functional defect observables (**proved** definitions, in `FunctionalAnalysis`)
- `norm_configuration_expIntegral_sub_le_integral_cexp_eval_dist`: generic CF defect control theorem (**proved**, in `FunctionalAnalysis`)
- `rotationCFPointwiseDefectIntegrand` / `rotationCFPointwiseDefect`: OS2 specialization of the generic CF defect API (**proved** abbreviations)
- `rotationCFDefect`: concrete one-point canonical CF rotation defect (**proved** definition)
- `rotation_cf_defect_polylog_bound`: uniform defect-level Ward bound (**axiom**)
- `anomaly_bound_from_superrenormalizability`: one-point CF anomaly bound (**proved**, derived from `rotation_cf_defect_polylog_bound`)
- `anomaly_vanishes`: one-point anomaly satisfies `‖Z_a[R·f] - Z_a[f]‖ ≤ C·a²·(1 + |log a|)^p` and hence vanishes (**proved**, from `anomaly_bound_from_superrenormalizability` + logarithmic asymptotics)
- `complex_gf_invariant_of_real_gf_invariant`: complex Euclidean invariance from real invariance + analyticity (**proved**, now in `CharacteristicFunctional`)
- `os0_for_continuum_limit`: exponential moments → OS0_Analyticity (**proved**, now in `AxiomInheritance`)
- `os1_for_continuum_limit`: exponential moments → OS1_Regularity (**proved**, now in `AxiomInheritance`)
- `os2_for_continuum_limit`: translation + rotation → OS2_EuclideanInvariance (**proved**)
- `os4_for_continuum_limit`: exponential clustering → OS4_Clustering (**proved**, now in `AxiomInheritance`; ε-δ from exp decay)
- `os4_clustering_implies_ergodicity`: OS4_Clustering → OS4_Ergodicity (**proved**, now in `CharacteristicFunctional`; via reality of Z + Cesàro convergence)
- `norm_generatingFunctional_le_one`: ‖Z[f]‖ ≤ 1 (**proved**, now in `CharacteristicFunctional`; norm_integral_le + ‖exp(ix)‖ = 1)

### Phase 6: OS axioms and assembly

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| ~~`euclideanAction2`~~ | OSAxioms | ✅ Proved | Constructed via `SchwartzMap.compCLMOfAntilipschitz` with inverse Euclidean action (antilipschitz + temperate growth). |
| ~~`euclideanAction2ℂ`~~ | OSAxioms | ✅ Proved | Same construction for complex Schwartz functions. |
| ~~`compTimeReflection2`~~ | OSAxioms | ✅ Proved | Constructed via `SchwartzMap.compCLMOfContinuousLinearEquiv` with time reflection as CLE. |
| ~~`compTimeReflection2_apply`~~ | OSAxioms | ✅ Proved | Follows by `rfl` from the construction. |
| ~~`SchwartzMap.translate`~~ | OSAxioms | ✅ Proved | Constructed via `SchwartzMap.compCLMOfAntilipschitz` with translation (antilipschitz + temperate growth). |
| ~~`massParameter_positive`~~ | Main | **Proved** | ∃ m₀ > 0 witnessed by hypothesis `0 < mass` (not OS reconstruction / not Wightman). |
| ~~`pphi2_exists_os_and_massParameter_positive`~~ | Main | **Proved** | `pphi2_exists` + `massParameter_positive`. |
| ~~`os_reconstruction`~~ | Main | **Deprecated alias** | Use `massParameter_positive` (since 2026-04-03). |
| ~~`pphi2_wightman`~~ | Main | **Deprecated alias** | Use `pphi2_exists_os_and_massParameter_positive` (since 2026-04-03). |
| ~~`pphi2_nontrivial`~~ | Main | **Proved** | Uses `pphi2_nontriviality` axiom. |
| ~~`pphi2_nonGaussian`~~ | Main | **Proved** | Uses `pphi2_nonGaussianity` axiom. |
| `pphi2_nontriviality` | Main | Hard | ∫ (ω f)² dμ > 0 for all f ≠ 0. Correlation inequalities (Griffiths, FKG). |
| ~~`pphi2_nonGaussianity`~~ | Main | **PROVED** | Proved from `continuumLimit_nonGaussian` by providing a fixed sequence `aₙ = 1/(n+1)`. |
| `measure_determined_by_schwinger` | Bridge | Medium | Moment determinacy on S'(ℝ²) with exponential (Fernique-type) moment bound. |
| ~~`wick_constant_comparison`~~ | ~~Bridge~~ | — | **Removed** — duplicate of `wickConstant_log_divergence`, moved to Unused/. |
| `same_continuum_measure` | Bridge | Medium | pphi2 and Phi4 constructions agree at weak coupling. Requires `IsPphi2ContinuumLimit`, `IsPhi4ContinuumLimit`, `IsWeakCoupling`. |
| `os2_from_phi4` | Bridge | Medium | OS2 for Phi4 continuum limit. Requires `IsPhi4ContinuumLimit` hypothesis. |
| ~~`os3_from_pphi2`~~ | Bridge | ✅ **Proved** | From `os3_for_continuum_limit` + `IsPphi2ContinuumLimit.toIsPphi2Limit`. |
| `schwinger_agreement` | Bridge | Very Hard | Schwinger function agreement at weak coupling. Cluster expansion (Guerra-Rosen-Simon). |

---

## Sorry inventory (all active files)

### Provable with current Lean/Mathlib

| Sorry | File | Notes |
|-------|------|-------|
| ~~`polynomial_lower_bound`~~ | Polynomial | **Promoted to axiom** — even degree + positive leading coeff → bounded below. |
| ~~`transferKernel_symmetric`~~ | TransferMatrix | **Proved** — `(a-b)² = (b-a)²` + `ring`. |
| ~~`timeCoupling_eq_zero_iff`~~ | TransferMatrix | **Proved** — sum of nonneg squares = 0 iff each is 0. |
| ~~`latticeInteraction_continuous`~~ | LatticeAction | **Proved** — via `wickMonomial_continuous` + finite sums. |
| ~~`continuumMeasure_isProbability`~~ | Embedding | **Proved** — pushforward of probability measure is probability measure. |
| ~~`connectedTwoPoint_symm`~~ | OS4_MassGap | **Proved** — symmetry of the connected 2-point function. |

### Require nontrivial proofs

| Sorry | File | Notes |
|-------|------|-------|
| ~~`generatingFunctionalℂ` body~~ | OSAxioms | **Proved** — complex generating functional defined. |
| ~~`interactionFunctional_measurable`~~ | LatticeMeasure | **Proved** — measurability of V_a. |
| ~~`boltzmannWeight_integrable`~~ | LatticeMeasure | **Proved** — exp(-V_a) integrable w.r.t. Gaussian. |
| ~~`partitionFunction_pos`~~ | LatticeMeasure | **Proved** — Z_a > 0. |
| ~~`interactingLatticeMeasure_isProbability`~~ | LatticeMeasure | **Proved** — μ_a is a probability measure. |
| ~~`boundedFunctions_integrable`~~ | Normalization | **Proved** — bounded functions integrable w.r.t. probability measure. |
| ~~`field_second_moment_finite`~~ | Normalization | **Proved** — ∫|ω(δ_x)|² dμ_a < ∞. Boltzmann weight bounded above + Gaussian L². |
| ~~`fkg_interacting`~~ | Normalization | **Proved** — FKG for interacting measure. From `fkg_perturbed` + single-site + algebra. |
| ~~`generating_functional_bounded`~~ | Normalization | **Proved** — \|Z[f]\| ≤ 1 for real f. From \|exp(it)\| = 1. |
| ~~`wickConstant_le_inv_mass_sq`~~ | Counterterm | **Proved** (in gaussian-field) — c_a ≤ 1/m². |
| ~~`wickConstant_antitone_mass`~~ | Counterterm | **Proved** (in gaussian-field) — c_a decreasing in mass. |
| ~~`energyLevel_gap`~~ | Positivity | **Proved** — E₁ > E₀ from transfer eigenvalue gap. |
| ~~`rp_closed_under_weak_limit`~~ | OS3_RP_Inheritance | **Proved** — RP closed under weak limits. |
| ~~`reflection_positivity_lattice`~~ | OS3_RP_Lattice | **Converted** to `lattice_rp` axiom. |
| ~~`continuumLimit`~~ | Convergence | **Proved** — Apply configuration-space sequential Prokhorov axiom to the tight family (`prokhorov_configuration_sequential` + `continuumMeasures_tight`). |
| ~~`continuumTimeReflection`~~ | TimeReflection | **Proved** — defined via `compCLMOfContinuousLinearEquiv`. |
| ~~`so2Generator`~~ | OS2_WardIdentity | **Proved** — SO(2) generator J f = x₁·∂f/∂x₂ - x₂·∂f/∂x₁ via `smulLeftCLM` + `lineDerivOpCLM`. |
| ~~`pphi2_exists`~~ | OS2_WardIdentity | **Proved** — Main existence theorem. Uses `continuumLimit_satisfies_fullOS`. |

---

## Priority ordering for filling axioms

### Tier 1: Infrastructure (unlocks further work)

1. ~~**`prokhorov_sequential`**~~ — **Proved.** Now a theorem with complete proof.
2. **`transferEigenvalue` + spectral axioms** — L2Operator.lean created with L² type, operator axioms, and proved spectral decomposition. Eigenvalue axioms remain (sorting + Perron-Frobenius).
3. ~~**`latticeEmbed` / `latticeEmbedLift`**~~ — ✅ All proved. `latticeEmbed` via `mkCLMtoNormedSpace`, `latticeEmbedLift` via composition with `Pi.single`.
4. ~~**`euclideanAction2` / `compTimeReflection2` / `SchwartzMap.translate`**~~ — ✅ All proved using `SchwartzMap.compCLMOfContinuousLinearEquiv` and `SchwartzMap.compCLMOfAntilipschitz`.

### Tier 2: Core analytic results (the hard axioms)

5. **Hypercontractivity** — `wickMonomial_latticeGaussian`, `wickConstant_eq_variance`, and `gaussian_hermite_zero_mean` are now **theorems**. The remaining work in this area is downstream analytic strengthening, not the Wick/GFF variance bridge. `wickConstant_eq_variance` is now proved generically via `GeneralResults/LatticeProductDFT.lean`. `wickPolynomial_uniform_bounded_below` proved. `exponential_moment_bound` proved from bounded-below + probability measure. `interactionFunctional_mean_nonpos` proved from `wickMonomial_latticeGaussian` + linearity + `P.coeff_zero_nonpos`. `partitionFunction_ge_one` / `interacting_moment_bound` as before.
6. **`second_moment_uniform` + `continuumMeasures_tight`** — Tightness argument. Depends on Nelson.
7. **`spectral_gap_uniform`** — Uniform mass gap. Kato-Rellich perturbation theory.
8. **`ward_identity_lattice` + `anomaly_vanishes`** — Ward identity + power counting for rotation invariance.

### Tier 3: Medium-difficulty proofs

9. ~~Transfer matrix properties (self-adjoint, positive definite, Hilbert-Schmidt, trace class)~~ — Replaced by L2Operator axioms (CLM, self-adjoint, compact)
10. Reflection positivity on the lattice (action decomposition → perfect square)
11. Clustering from spectral gap (standard spectral decomposition)
12. OS axiom inheritance (mostly soft analysis: limits preserve bounds)
13. ~~Bridge from `SatisfiesAllOS` to `SatisfiesFullOS`~~ — **Eliminated.** `SatisfiesAllOS` removed; `continuumLimit_satisfies_fullOS` returns `SatisfiesFullOS` directly. Sorries now in inheritance layer.

### Tier 4: Easy / straightforward

14. `os1_inheritance` — |cos| ≤ 1
15. Remaining measurability and integrability lemmas

---

## Proved theorems (non-trivial)

The following theorems have complete proofs (no sorry):

| Theorem | File | Description |
|---------|------|-------------|
| `latticeInteraction_bounded_below` | LatticeAction | V_a ≥ -B from Wick polynomial bounds |
| `latticeEmbedEval_linear_phi` | Embedding | Bilinearity in φ |
| `latticeEmbedEval_linear_f` | Embedding | Bilinearity in f |
| `timeCoupling_nonneg` | TransferMatrix | Time coupling ≥ 0 |
| `transferKernel_pos` | TransferMatrix | Transfer kernel > 0 (from exp_pos) |
| `massGap_pos` | Positivity | Mass gap > 0 (from eigenvalue gap) |
| `spectral_gap_pos` | SpectralGap | Spectral gap > 0 (from mass gap) |
| `clustering_uniform` | OS4_MassGap | Uniform clustering (from uniform spectral gap) |
| `os4_lattice_from_gap` | OS4_Ergodicity | OS4 from mass gap (assembly) |
| `timeReflection2D_involution` | OS3_RP_Lattice | Time reflection is an involution |
| `timeReflection2_involution` | OSAxioms | Θ² = id for continuum time reflection |
| `positiveTimeSubmodule2` | OSAxioms | Submodule proof for positive-time test functions |
| `wickMonomial_continuous` | LatticeAction | Wick monomials are continuous in their argument |
| `latticeInteraction_continuous` | LatticeAction | Lattice interaction is continuous (finite sums of continuous functions) |
| `transferKernel_symmetric` | TransferMatrix | T(ψ,ψ') = T(ψ',ψ) by (a-b)² = (b-a)² |
| `timeCoupling_eq_zero_iff` | TransferMatrix | K(ψ,ψ') = 0 ↔ ψ = ψ' (sum of squares) |
| `latticeAction_translation_invariant` | OS2_WardIdentity | V_a[T_v φ] = V_a[φ] via Equiv.subRight |
| `os2_inheritance` | OS2_WardIdentity | E(2) invariance (from translation + rotation) |
| `continuumLimit_satisfies_fullOS` | OS2_WardIdentity | All OS axioms (assembly into SatisfiesFullOS) |
| `interactionFunctional_measurable` | LatticeMeasure | Measurability of V_a as function on Configuration space |
| `boltzmannWeight_integrable` | LatticeMeasure | exp(-V_a) is integrable w.r.t. Gaussian measure |
| `partitionFunction_pos` | LatticeMeasure | Z_a > 0 from exp(-V_a) > 0 and Gaussian full support |
| `interactingLatticeMeasure_isProbability` | LatticeMeasure | μ_a is a probability measure |
| `latticeInteraction_single_site` | LatticeAction | V_a decomposes as sum of single-site functions (replaced false convexity axiom) |
| `bounded_integrable_interacting` | Normalization | Bounded functions integrable w.r.t. interacting measure |
| `generating_functional_bounded` | Normalization | \|Z[f]\| ≤ 1 for real f |
| `rp_closed_under_weak_limit` | OS3_RP_Inheritance | RP closed under weak limits |
| `continuumMeasure_isProbability` | Embedding | Pushforward of probability measure is probability measure |
| `connectedTwoPoint_symm` | OS4_MassGap | Symmetry of connected 2-point function |
| `energyLevel_gap` | Positivity | E₁ > E₀ from spectral-data ground/excited separation |
| `prokhorov_configuration_sequential` | Convergence | Sequential extraction on configuration space (axiom) |
| `prokhorov_sequential` | Convergence | Generic Polish-space sequential Prokhorov theorem (proved) |
| `wickPolynomial_bounded_below` | WickPolynomial | Wick polynomial bounded below — from leading term domination via `poly_even_degree_bounded_below` |
| `poly_even_degree_bounded_below` | WickPolynomial | Even-degree polynomial with positive leading coeff is bounded below — `eval_eq_sum_range` + coefficient bound + `Continuous.exists_forall_le` |
| `pphi2_generating_functional_real` | CharacteristicFunctional | Im(Z[f])=0 via conj(Z[f])=Z[f] from Z₂ symmetry |
| `generatingFunctional_translate_continuous` | CharacteristicFunctional | t ↦ Z[f + τ_{(t,0)} g] continuous via DCT + `continuous_timeTranslationSchwartz` |
| `InteractionPolynomial.eval_neg` | Polynomial | P(-τ) = P(τ) from even polynomial symmetry |
| `field_second_moment_finite` | Normalization | ∫\|ω(δ_x)\|² dμ_a < ∞ — `integrable_withDensity_iff` + `pairing_product_integrable` + domination by exp(B)·f² |
| `field_all_moments_finite` | Normalization | ∫\|ω(δ_x)\|^p dμ_a < ∞ for all p — `pairing_is_gaussian` + `integrable_pow_of_mem_interior_integrableExpSet` |
| `euclideanAction2` | OSAxioms | E(2) pullback on Schwartz functions — `compCLMOfAntilipschitz` with inverse Euclidean action |
| `euclideanAction2ℂ` | OSAxioms | Same for complex Schwartz functions |
| `compTimeReflection2` | OSAxioms | Time reflection on Schwartz space — `compCLMOfContinuousLinearEquiv` with time reflection CLE |
| `SchwartzMap.translate` | OSAxioms | Translation on Schwartz space — `compCLMOfAntilipschitz` with translation |
| `so2Generator` | OS2_WardIdentity | SO(2) generator J f = x₁·∂f/∂x₂ - x₂·∂f/∂x₁ — `smulLeftCLM` + `lineDerivOpCLM` |
| `continuumLimit` | Convergence | Continuum limit via configuration extraction axiom — `prokhorov_configuration_sequential` + `continuumMeasures_tight` |
| `latticeEmbed` | Embedding | Lattice→S'(ℝ^d) embedding — `SchwartzMap.mkCLMtoNormedSpace` with `|ι(φ)(f)| ≤ (a^d·Σ|φ(x)|)·seminorm(0,0)(f)` |
| `latticeEmbed_eval` | Embedding | Evaluation formula — `rfl` from construction |
| `transferOperator_spectral` | L2Operator | Spectral decomposition — `compact_selfAdjoint_spectral` from gaussian-field |
| `latticeEmbed_measurable` | Embedding | `configuration_measurable_of_eval_measurable` + `continuous_apply` for each coordinate |
| `norm_generatingFunctional_le_one` | CharacteristicFunctional | ‖Z[f]‖ ≤ 1 via norm_integral + ‖exp(ix)‖ = 1 + measure_univ = 1 |
| `os4_clustering_implies_ergodicity` | CharacteristicFunctional | Clustering → Ergodicity via reality of Z[f], Cesàro convergence, and characteristic function bound |
| `transferWeight_measurable` | L2Operator | Transfer weight w(ψ) = exp(-(a/2)·h(ψ)) is measurable — continuity chain via `wickMonomial_continuous` |
| `transferWeight_bound` | L2Operator | Transfer weight is essentially bounded — from `wickPolynomial_bounded_below` + exponentiation |
| `transferGaussian_memLp` | L2Operator | Gaussian kernel ∈ L¹ — product factorization + `integrable_exp_neg_mul_sq` |
| `transferGaussian_norm_le_one` | L2Operator | ‖G(ψ)‖ ≤ 1 — `exp_le_one_iff` + `timeCoupling_nonneg` |
| `transferWeight_memLp_two` | L2Operator | Transfer weight ∈ L² — Gaussian decay bound + product factorization |
| ~~`transferOperator_isCompact`~~ | L2Operator | **PROVED** — from `hilbert_schmidt_isCompact` (proved) + w ∈ L² + ‖G‖ ≤ 1 |
| `mulCLM` | L2Multiplication | Multiplication by bounded function as CLM on L² — Hölder (∞,2,2) |
| `convCLM` | L2Convolution | Convolution with L¹ function as CLM on L² — Young's inequality |

---

## Provability assessment (ranked by difficulty)

Axioms ranked by feasibility of proving them with current Lean/Mathlib
infrastructure. Assessment date: 2026-03-04.

### Tier 1: Recently proved

| Axiom | File | Status |
|-------|------|--------|
| ~~`torusContinuumGreen_continuous_diag`~~ | TorusOSAxioms | **PROVED.** Via `greenFunctionBilinear_continuous_diag` in gaussian-field. |
| ~~`torusEmbeddedTwoPoint_uniform_bound`~~ | TorusPropagatorConvergence | **PROVED.** DM expansion + Fourier basis bounds. |
| ~~`torusGaussianMeasure_z2_symmetric`~~ | TorusGaussianLimit | **PROVED.** Gaussian uniqueness via same covariance. |
| ~~`z2_symmetric_of_weakLimit`~~ | TorusGaussianLimit | **PROVED.** `ext_of_forall_integral_eq_of_IsFiniteMeasure` + uniqueness of limits. |
| ~~`torusGaussianMeasure_isGaussian`~~ | TorusGaussianLimit | **PROVED.** Lattice GFF pushforward is Gaussian via `pairing_is_gaussian`. |
| ~~`torusGaussianLimit_isGaussian`~~ | TorusGaussianLimit | **PROVED.** MGF matching → complexMGF extension → measure equality + `weakLimit_centered_gaussianReal`. |
| ~~`torusGaussianLimit_complex_cf_quadratic`~~ | TorusOSAxioms | **PROVED.** Via `torusGeneratingFunctionalℂ_analyticOnNhd` + identity theorem. |
| ~~`torusContinuumGreen_translation_invariant`~~ | TorusOSAxioms | **PROVED.** Via `greenFunctionBilinear_translation_invariant` in gaussian-field. |
| ~~`torusContinuumGreen_pointGroup_invariant`~~ | TorusOSAxioms | **PROVED.** Via `greenFunctionBilinear_swap_invariant` + `_timeReflection_invariant`. |
| ~~`schwinger2_convergence`~~ | Convergence | **PROVED.** From `schwinger_n_convergence`. |
| ~~`pphi2_nonGaussianity`~~ | Main | **PROVED.** From `continuumLimit_nonGaussian` with `aₙ = 1/(n+1)`. |

### Tier 2: Easy (provable now)

| Axiom | File | Strategy |
|-------|------|----------|
| ~~`weakLimit_centered_gaussianReal`~~ | TorusGaussianLimit | **PROVED.** CharFun decomposition into cos/sin integrals + variance extraction via log + `Measure.ext_of_charFun`. |
| ~~`torus_propagator_convergence`~~ | TorusPropagatorConvergence | **PROVED.** Via gaussian-field `lattice_green_tendsto_continuum` axiom. |
| ~~`latticeMeasure_translation_invariant`~~ | OS2_WardIdentity | **Proved** — density bridge + change of variables. |

### Tier 3: Moderate (nontrivial but standard)

| Axiom | File | Strategy |
|-------|------|----------|
| `torusLimit_covariance_eq` | TorusGaussianLimit | Weak convergence transfers second moments. Uniform integrability from `torusEmbeddedTwoPoint_uniform_bound` + Vitali convergence. |
| `gaussian_measure_unique_of_covariance` | TorusGaussianLimit | Gaussian on nuclear space determined by covariance. Bochner-Minlos uniqueness. |
| ~~`torusContinuumMeasures_tight`~~ | TorusTightness | **PROVED** from `configuration_tight_of_uniform_second_moments` + `torus_second_moment_uniform`. |
| `configuration_tight_of_uniform_second_moments` | TorusTightness | ✅ Verified (DT 2026-03-11). Mitoma-Chebyshev for nuclear duals. Mitoma (1983) + Chebyshev. Nuclearity essential. |
| `torusPositiveTimeSubmodule` | TorusOSAxioms | Submodule of positive-time test functions. Infrastructure axiom. |
| ~~`torusGeneratingFunctionalℂ_analyticOnNhd`~~ | TorusOSAxioms | **PROVED.** Analyticity of complex generating functional. Via `analyticOnNhd_integral` + AM-GM Gaussian integrability. |
| `torusLattice_rp` | TorusOSAxioms | Matrix-form RP for lattice GFF on torus. Fubini + perfect-square argument. |
| `gaussian_rp_with_boundary_weight` | OS3_RP_Lattice | Core Gaussian RP: ∫ G·G∘Θ·w dμ_GFF ≥ 0. Gaussian Markov property. Glimm-Jaffe Ch. 6.1. |
| ~~`transferOperator_isCompact`~~ | L2Operator | **PROVED** from `hilbert_schmidt_isCompact` (proved) + `transferWeight_memLp_two` + `transferGaussian_norm_le_one`. |
| ~~`hilbert_schmidt_isCompact`~~ | L2Operator | **PROVED** from `integral_operator_l2_kernel_compact` + `tensor_kernel_memLp` + `mul_conv_integral_rep`. |
| `integral_operator_l2_kernel_compact` | L2Operator | General HS theorem: convolution-form L² kernel integral operators are compact. Reed-Simon I, Thm VI.23. |
| ~~`translation_invariance_continuum`~~ | OS2_WardIdentity | **Proved** — `tendsto_nhds_unique_of_eventuallyEq` from `cf_tendsto` + `lattice_inv`. |
| `analyticOn_generatingFunctionalC` | CharacteristicFunctional | Analyticity of complex generating functional from exponential moments via Morera. |
| `continuum_exponential_moment_bound` | AxiomInheritance | Mixed `L¹`/Green exponential-moment input `∫ exp(|ω f|) ≤ exp(c₁∫|f| + c₂ G(f,f))` for OS0 + OS1. |
| `os3_inheritance` | AxiomInheritance | RP transfers through weak limits. From `lattice_rp_matrix` + `rp_closed_under_weak_limit` (proved). |
| `os0_inheritance` | AxiomInheritance | Uniform moment bounds + pointwise convergence → limit has all moments finite. |
| `torus_interacting_tightness` | TorusInteractingLimit | Cauchy-Schwarz density transfer from Gaussian tightness. |

### Tier 4: Hard (deep analytic results)

| Axiom | File | Strategy |
|-------|------|----------|
| ~~`inner_convCLM_pos_of_fourier_pos`~~ | GaussianFourier | ✅ **Proved** from `fourier_representation_convolution` axiom. |
| `fourier_representation_convolution` | GaussianFourier | L² Fourier representation identity. Schwartz density + L² convolution theorem (not yet in Mathlib). |
| `latticeGreenBilinear_basis_tendsto_continuum` | PropagatorConvergence | Spectral lattice Green bilinear on Dynin-Mityagin basis pairs → continuum Fourier Green bilinear on ℝ^d. Extend to all test functions by bilinear continuity. |
| `os4_inheritance` | AxiomInheritance | Exponential clustering survives weak limits. Uniform spectral gap + weak convergence. |
| `rotation_cf_defect_polylog_bound` | OS2_WardIdentity | Minimal remaining OS2 axiom: polynomial-log `a²` bound for the canonical CF defect `rotationCFDefect`, uniform in the lattice size `N`. |
| `continuum_exponential_moment_bound` | AxiomInheritance | Project-level continuum exponential-moment bridge `∫ exp(|ω f|) ≤ exp(c₁∫|f| + c₂ G(f,f))`; source for derived OS0/OS1 estimates. |
| ~~`wickMonomial_latticeGaussian`~~ | Hypercontractivity | **Theorem** (see `Hypercontractivity.lean`). |
| ~~`wickConstant_eq_variance`~~ | Hypercontractivity | **Theorem** (generic proof via `GeneralResults/LatticeProductDFT.lean`; 2D corollary retained in `Hypercontractivity.lean`). |
| ~~`gaussian_hermite_zero_mean`~~ | Hypercontractivity | **Theorem** (see `GaussianHermiteMean.lean`). |
| ~~`wickPolynomial_uniform_bounded_below`~~ | WickPolynomial | ✅ **Proved** via coefficient continuity + compactness + leading term dominance. |
| `canonical_continuumMeasure_cf_tendsto` | AxiomInheritance | Coupled canonical `continuumMeasure` approximants converge CF-wise to `μ`; bridge needed to apply the Ward anomaly bound to an abstract `IsPphi2Limit`. |
| `continuum_exponential_clustering` | AxiomInheritance | Spectral gap → exponential clustering in continuum. |

### Tier 5: Very hard / infrastructure gaps

| Axiom | File | Strategy |
|-------|------|----------|
| `spectral_gap_uniform` | SpectralGap | Uniform mass gap. Central result of Glimm-Jaffe. |
| `spectral_gap_lower_bound` | SpectralGap | Quantitative mass gap bound. |
| `prokhorov_configuration_sequential` | Convergence | Sequential extraction on S'(ℝ²). Blocked by Mathlib nuclear space gap. (Not needed for torus path.) |
| `continuumLimit_nonGaussian` | Convergence | Nonzero 4th cumulant via perturbation theory. |
| `continuumLimit_nontrivial` | Convergence | Two-point function > 0. Correlation inequalities (Griffiths, FKG). |
| `schwinger_n_convergence` | Convergence | n-point Schwinger functions converge. Diagonal subsequence extraction. |
| `pphi2_nontriviality` | Main | ∫ (ω f)² dμ > 0 for all f ≠ 0. Correlation inequalities. |
| `schwinger_agreement` | Bridge | Cluster expansion uniqueness (Guerra-Rosen-Simon). |
| `same_continuum_measure` | Bridge | pphi2 and Phi4 agree at weak coupling. |
| `os2_from_phi4` | Bridge | OS2 for Phi4 continuum limit. |
| `measure_determined_by_schwinger` | Bridge | Moment determinacy on S'(ℝ²). |
| `two_point_clustering_from_spectral_gap` | OS4_MassGap | 2-point clustering from mass gap with cyclic torus time separation. |
| `general_clustering_from_spectral_gap` | OS4_MassGap | Bounded observables; `G` on `latticeConfigEuclideanTimeShift`, decay measured in `latticeEuclideanTimeSeparation`. |
| `second_moment_uniform` | Tightness | Uniform second moments for interacting measure. |
| `moment_equicontinuity` | Tightness | Equicontinuity of moments in f. |
| ~~`continuumMeasures_tight`~~ | Tightness | **PROVED** via `configuration_tight_of_uniform_second_moments` + `continuum_second_moment_uniform` (ported from torus tightness pipeline). |
| ~~`gaussianContinuumMeasures_tight`~~ | GaussianTightness | **PROVED for `d > 0`** — Tightness via `configuration_tight_of_uniform_second_moments`; the remaining `d = 0` case is a separate Dynin-Mityagin / Schwartz-space infrastructure issue. |
| `gaussianLimit_isGaussian` | GaussianLimit | Weak limits of Gaussians are Gaussian (S'(ℝ²) version). |

### Recommended attack order

1. **Easy wins**: `weakLimit_centered_gaussianReal`, `torus_propagator_convergence`, `latticeMeasure_translation_invariant`
2. **Torus infrastructure**: `torusLimit_covariance_eq`, `gaussian_measure_unique_of_covariance`, `torusContinuumMeasures_tight`, `torusLattice_rp`
3. **Transfer matrix**: `integral_operator_l2_kernel_compact` — general HS theorem (Reed-Simon I, Thm VI.23); `hilbert_schmidt_isCompact` **proved** from it
4. **OS inheritance**: `gaussian_rp_with_boundary_weight`, `os3_inheritance`, `os0_inheritance` — fills the RP chain
5. **Hard analysis**: spectral gap, clustering, exponential moments — the deep results

---

## Upstream: gaussian-field

The gaussian-field library (dependency) has **14 axioms, 0 sorries**.
- `GaussianField/Properties.lean`: 1 axiom (`measure_unique_of_charFun`)
- `GaussianField/Support.lean`: 2 axioms (`not_supported_of_not_hilbertSchmidt`, `supportHilbertSpace_exists`)
- `HeatKernel/PositionKernel.lean`: 1 axiom (`mehlerKernel_eq_series`)
- `HeatKernel/GreenInvariance.lean`: 0 axioms (all 3 proved via pure tensor extension)
- `Torus/Restriction.lean`: 0 axioms (PolishSpace axioms removed as incorrect)
- `SmoothCircle/FourierTranslation.lean`: 0 axioms (all 6 proved)
- `Nuclear/TensorProductFunctorAxioms.lean`: 6 axioms (tensor product functor)
- `Lattice/Convergence.lean`: 2 axioms (`lattice_covariance_pure_eq_2d_spectral`, `lattice_green_tendsto_continuum`)
- `Lattice/HeatKernelConvergence1d.lean`: 0 axioms (spectral expansion proved via matrix exponential)
See [gaussian-field status](../gaussian-field/status.md) for the full inventory.
