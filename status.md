# P(Φ)₂ Project Status

## Overview

The project formalizes the construction of P(Φ)₂ Euclidean quantum field theory
in Lean 4 via the Glimm-Jaffe/Nelson lattice approach. All six phases are
structurally complete and the full project builds successfully (`lake build`,
3530 jobs).

The proof architecture is: axiomatize key analytic/probabilistic results with
detailed proof sketches, prove the logical structure connecting them, and
progressively fill in the axioms with full proofs.

**pphi2: 59 axioms, 2 sorries** (plus 1 private axiom `schwartz_riemann_sum_bound` in GaussianContinuumLimit; plus 1 unused computation and 1 unused Option B file in `Unused/`) | **gaussian-field (upstream): 10 axioms, 1 sorry**

`Pphi2/Unused/HypercontractivityOptionB.lean` preserves an optional
Gross-Rothaus-Simon OU semigroup route as inactive reference material.
It is not imported and not counted in the active axiom inventory.
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
| 2 | `TransferMatrix/L2Operator.lean` | 1 axiom (compactness) |
| 2 | `TransferMatrix/GaussianFourier.lean` | 1 axiom (Gaussian convolution strict PD); `fourier_gaussian_pos` proved |
| 2 | `TransferMatrix/Jentzsch.lean` | 0 axioms; Jentzsch + nontriviality + positivity-improving + strict PD all proved |
| 2 | `TransferMatrix/Positivity.lean` | 0 axioms (energy levels, mass gap) |
| 2 | `OSProofs/OS3_RP_Lattice.lean` | 1 axiom, 0 sorries |
| 2 | `OSProofs/OS3_RP_Inheritance.lean` | 0 axioms, 0 sorries |
| 3 | `TransferMatrix/SpectralGap.lean` | 2 axioms |
| 3 | `OSProofs/OS4_MassGap.lean` | 2 axioms, 0 sorries |
| 3 | `OSProofs/OS4_Ergodicity.lean` | 0 axioms, 0 sorries |
| 4 | `ContinuumLimit/Embedding.lean` | 0 axioms (`IsPphi2Limit` is a def) |
| 4 | `ContinuumLimit/Hypercontractivity.lean` | 2 axioms |
| 4 | `ContinuumLimit/Tightness.lean` | 3 axioms |
| 4 | `ContinuumLimit/Convergence.lean` | 4 axioms, 2 proved theorems |
| 4 | `ContinuumLimit/AxiomInheritance.lean` | 3 axioms, 0 sorries |
| 4G | `GaussianContinuumLimit/EmbeddedCovariance.lean` | 0 axioms, 0 sorries |
| 4G | `GaussianContinuumLimit/PropagatorConvergence.lean` | 1 axiom + 1 private axiom (`schwartz_riemann_sum_bound`), 0 sorries |
| 4G | `GaussianContinuumLimit/GaussianTightness.lean` | 1 axiom, 0 sorries |
| 4G | `GaussianContinuumLimit/GaussianLimit.lean` | 1 axiom, 0 sorries |
| 5 | `OSProofs/OS2_WardIdentity.lean` | 8 axioms |
| — | `GeneralResults/FunctionalAnalysis.lean` | 0 axioms (pure Mathlib results) |
| — | `OSforGFF/TimeTranslation.lean` | 0 axioms, 0 sorries (Schwartz translation continuity) |
| 6 | `OSAxioms.lean` | 0 axioms, 0 sorries |
| 6 | `Main.lean` | 1 axiom, 1 sorry |
| 4T | `TorusContinuumLimit/TorusEmbedding.lean` | 0 axioms, 0 sorries (`torusContinuumGreen` now `greenFunctionBilinear`) |
| 4T | `TorusContinuumLimit/TorusPropagatorConvergence.lean` | 2 axioms, 0 sorries |
| 4T | `TorusContinuumLimit/TorusTightness.lean` | 1 axiom, 0 sorries |
| 4T | `TorusContinuumLimit/TorusConvergence.lean` | 0 axioms, 0 sorries (Prokhorov proved!) |
| 4T | `TorusContinuumLimit/TorusGaussianLimit.lean` | 7 axioms, 0 sorries |
| 4T | `TorusContinuumLimit/TorusInteractingLimit.lean` | 1 axiom, 0 sorries |
| 4T | `TorusContinuumLimit/TorusOSAxioms.lean` | 7 axioms, 1 sorry (OS0–OS3; OS1+OS2+OS3 proved) |
| 6 | `Bridge.lean` | 4 axioms, 0 sorries |

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
| `transferOperator_isCompact` | L2Operator | Medium | Compactness from Hilbert-Schmidt strategy using Gaussian decay of the weight (not the divergent translation-invariant bound). |
| `transferOperator_spectral` | L2Operator | **Proved** | Spectral decomposition from `compact_selfAdjoint_spectral` (gaussian-field). |
| ~~`jentzsch_theorem`~~ | Jentzsch | ✅ **Proved** | Jentzsch's theorem for compact self-adjoint positivity-improving operators: ground eigenvalue simple with strict spectral gap. Reed-Simon IV, XIII.43–44. Full proof in `JentzschProof.lean`, bridge via `IsPositivityImproving.toPI'`. |
| ~~`transferOperator_positivityImproving`~~ | Jentzsch | ✅ **Proved** | Transfer kernel K(ψ,ψ') = w(ψ)G(ψ-ψ')w(ψ') > 0 everywhere, so T maps nonneg nonzero f to a.e. strictly positive Tf. Proved via T = M_w ∘ Conv_G ∘ M_w factorization, Cauchy-Schwarz for L² integrability, measure-preserving translation, and `integral_pos_iff_support_of_nonneg_ae`. |
| ~~`transferOperator_strictly_positive_definite`~~ | Jentzsch | ✅ **Proved** | ⟨f, Tf⟩ > 0 for f ≠ 0. Proved via self-adjointness of M_w (⟨f, M_w(Conv_G(M_w f))⟩ = ⟨M_w f, Conv_G(M_w f)⟩), injectivity of M_w (w > 0), and Gaussian convolution strict PD axiom. |
| `convolution_gaussian_strictly_positive_definite` | Jentzsch | Medium | Bridge axiom from bochner project. Convolution with Gaussian exp(-½‖·‖²) is strictly PD on L²: ⟨f, Conv_G f⟩ = ∫ |f̂(k)|² Ĝ(k) dk > 0. Bochner's theorem + Plancherel. |
| ~~`l2SpatialField_hilbertBasis_nontrivial`~~ | Jentzsch | ✅ **Proved** | Any Hilbert basis of L²(ℝ^Ns) has ≥ 2 elements. Proved via indicator functions on disjoint balls + orthogonality. |
| ~~`transferOperator_inner_nonneg`~~ | Jentzsch | ✅ **Proved** | ⟨f, Tf⟩ ≥ 0. Derived from strict PD (> 0 for f ≠ 0, = 0 for f = 0). |
| ~~`transferOperator_eigenvalues_pos`~~ | Jentzsch | ✅ **Proved** | λᵢ > 0. From ⟨bᵢ, Tbᵢ⟩ = λᵢ‖bᵢ‖² > 0 by strict PD. |
| ~~`transferOperator_ground_simple`~~ | Jentzsch | ✅ **Proved** | Ground-state simplicity. Derived from Jentzsch + eigenvalue positivity + nontriviality. |
| ~~`action_decomposition`~~ | OS3_RP_Lattice | ✅ **Proved** | S_plus = V/2, using sum-reindexing by site-reflection bijection (timeReflection2D is involution). |
| `lattice_rp` | OS3_RP_Lattice | Medium | RP inequality for `interactingLatticeMeasure`. Fubini + perfect-square from action decomposition. |
| ~~`lattice_rp_matrix`~~ | OS3_RP_Lattice | ✅ **Proved** | Matrix form of RP via cos(u-v) expansion + `lattice_rp`. |
| ~~`rp_from_transfer_positivity`~~ | OS3_RP_Lattice | ✅ **Proved** | ⟨f, T^n f⟩ ≥ 0 via `transferOperatorCLM`. |

### Phase 3: Spectral gap and clustering

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| `spectral_gap_uniform` | SpectralGap | Hard | Mass gap bounded below uniformly in a. Key input: the interaction is a bounded perturbation of the free field in the sense of Kato-Rellich, and the free mass gap is m > 0. Needs careful control of the perturbation as a→0. |
| `spectral_gap_lower_bound` | SpectralGap | Hard | m_phys ≥ c·m_bare. Quantitative bound on the physical mass. |
| ~~`connectedTwoPoint_nonneg_delta`~~ | OS4_MassGap | ✅ **Proved** | Variance nonnegativity: direct proof via ∫(X-E[X])² ≥ 0. |
| ~~`two_point_clustering_lattice`~~ | OS4_MassGap | ✅ **Proved** | Exponential decay bound using `finLatticeDelta` and `massGap`. |
| ~~`general_clustering_lattice`~~ | OS4_MassGap | ✅ **Proved** | Quantified clustering over bounded observables. |
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
| `continuumMeasures_tight` | Tightness | Hard | Tightness via Mitoma criterion + Chebyshev + uniform second moments. Combines second_moment_uniform with Mitoma's theorem. |
| ~~`gaussian_hypercontractivity_continuum`~~ | Hypercontractivity | **Proved** | Gaussian hypercontractivity in continuum-embedded form. Proved from `gaussian_hypercontractive` (gaussian-field) via pushforward + `latticeEmbedLift_eval_eq`. |
| `exponential_moment_bound` | Hypercontractivity | Hard | ∫ exp(-2V_a) dμ_{GFF} ≤ K uniformly in a. Deep stability estimate (cluster expansions, Glimm-Jaffe Thm 8.6.1). |
| `interacting_moment_bound` | Hypercontractivity | Medium | Bounds interacting L^{pn} moments in terms of FREE Gaussian L^{2n} moments via Cauchy-Schwarz density transfer. RHS uses μ_{GFF}, not μ_a (converting back requires e^{+V_a} which diverges). |
| `prokhorov_configuration_sequential` | Convergence | Infrastructure | Sequential extraction axiom directly on `Configuration (ContinuumTestFunction d)`; avoids global Polish/Borel assumptions on full weak-* dual. |
| ~~`prokhorov_sequential`~~ | Convergence | ~~Infrastructure~~ | **Proved** — generic Polish-space sequential Prokhorov theorem (kept as theorem, not used by `continuumLimit`). |
| `schwinger2_convergence` | Convergence | Med/Hard | 2-point Schwinger functions converge along subsequence. Prokhorov + uniform L² integrability. |
| `schwinger_n_convergence` | Convergence | Hard | n-point Schwinger functions converge along subsequence. Diagonal subsequence extraction. |
| `continuumLimit_nontrivial` | Convergence | Hard | ∫ (ω f)² dμ > 0 for some f. Free field two-point function gives lower bound. |
| `continuumLimit_nonGaussian` | Convergence | Hard | Connected 4-point function ≠ 0. Perturbation theory gives O(λ) contribution. |
| `os0_inheritance` | AxiomInheritance | Medium | OS0 transfers: uniform moment bounds + pointwise convergence → limit has all moments finite. |
| `os3_inheritance` | AxiomInheritance | Medium | Abstract RP: ∫ F(ω)·F(Θ*ω) dμ ≥ 0 for bounded continuous F. Follows from lattice_rp_matrix + rp_closed_under_weak_limit (proved). |
| `os4_inheritance` | AxiomInheritance | Med/Hard | Exponential clustering survives weak limits. Uniform spectral gap + weak convergence. |
| ~~`continuumLimit_satisfies_os0134`~~ | AxiomInheritance | **Theorem** | Assembly of os0/os1/os3/os4 inheritance results. |

### Phase 4G: Gaussian continuum limit

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| `propagator_convergence` | PropagatorConvergence | Medium | Lattice Riemann sum of Green's function → continuum Fourier integral. Dominated convergence + Schwartz decay. |
| `gaussianContinuumMeasures_tight` | GaussianTightness | Medium | Tightness of embedded GFF measures via Mitoma criterion + Chebyshev from uniform second moments. |
| `gaussianLimit_isGaussian` | GaussianLimit | Medium | Weak limits of Gaussian measures are Gaussian. Bochner-Minlos + pointwise convergence of characteristic functionals. |

**Proved theorems (GaussianContinuumLimit/):**
- `gaussianContinuumMeasure_isProbability`: Pushforward of probability measure is probability.
- `embeddedTwoPoint_eq_covariance`: Change-of-variables reducing pushforward integral to lattice GFF.
- `gaussian_second_moment_uniform`: Uniform second moment bound from `embeddedTwoPoint_uniform_bound`.
- `gaussianContinuumLimit_exists`: Subsequential weak limit via Prokhorov extraction.
- `gaussianContinuumLimit_nontrivial`: `∫ (ω f)² dμ > 0` from `continuumGreenBilinear_pos`.
- `gaussian_feeds_interacting_tightness`: Bridge — Gaussian bound feeds Cauchy-Schwarz density transfer.

**Sorries (provable):**
- `embeddedTwoPoint_eq_latticeSum`: Pushforward integral → lattice double sum (Fubini + Gaussian integration).
- `embeddedTwoPoint_uniform_bound`: `E[Φ_a(f)²] ≤ C` from eigenvalue bound + Riemann sum.
- `continuumGreenBilinear_pos`: `G(f,f) > 0` from Fourier injectivity on Schwartz space.

Note: `os1_inheritance` is a theorem (not axiom) — OS1 transfers trivially since |cos(·)| ≤ 1.

### Phase 4T: Torus continuum limit (UV only, L fixed)

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| `torus_propagator_convergence` | TorusPropagatorConvergence | Medium | Lattice eigenvalues `(4N²/L²)sin²(πn/N) + m²` → continuum `(2πn/L)² + m²`. Pure UV limit, dominated convergence with rapid Fourier decay. |
| `torusEmbeddedTwoPoint_uniform_bound` | TorusPropagatorConvergence | Easy | `E[Φ_N(f)²] ≤ C` uniformly in N. Eigenvalue lower bound `λ_k ≥ m²` + Parseval + Riemann sum bound on compact torus. |
| `torusContinuumMeasures_tight` | TorusTightness | Medium | Tightness via Mitoma criterion on torus. Finite volume makes this cleaner than S'(ℝ^d). |
| `torusGaussianMeasure_isGaussian` | TorusGaussianLimit | Easy | Lattice GFF pushforward is Gaussian. MGF: `E[e^{ω(f)}] = exp(½ E[ω(f)²])`. |
| `torusGaussianLimit_isGaussian` | TorusGaussianLimit | Medium | Weak limits of Gaussians on torus are Gaussian. Bochner-Minlos + characteristic functionals. |
| `torusLimit_covariance_eq` | TorusGaussianLimit | Medium | Weak convergence transfers second moments. Uniform integrability from `torusEmbeddedTwoPoint_uniform_bound`. |
| `gaussian_measure_unique_of_covariance` | TorusGaussianLimit | Medium | Gaussian on nuclear space determined by covariance. Bochner-Minlos uniqueness. |
| `torusGaussianMeasure_z2_symmetric` | TorusGaussianLimit | Easy | Lattice GFF pushforward is Z₂-symmetric: `μ_N` is invariant under φ ↦ -φ. |
| `z2_symmetric_of_weakLimit` | TorusGaussianLimit | Medium | Z₂ symmetry transfers through weak limits. |
| `torusGaussianLimit_fullConvergence` | TorusGaussianLimit | Medium | Full sequence convergence (not just subsequential) from Gaussianity + covariance uniqueness + Z₂ symmetry. |
| `torus_interacting_tightness` | TorusInteractingLimit | Medium | Cauchy-Schwarz density transfer from Gaussian tightness. Nelson's estimate + hypercontractivity. |

| `torusPositiveTimeSubmodule` | TorusOSAxioms | Infrastructure | Submodule of torus test functions with time support in (0, L/2). Nuclear tensor product lacks pointwise evaluation, so submodule axiomatized. |
| `torusGaussianLimit_complex_cf_norm` | TorusOSAxioms | Easy | ✅ Verified (Gemini). ‖Z_ℂ[f_re,f_im]‖ = exp(½(G(f_im,f_im)-G(f_re,f_re))). Gaussian MGF with complex coefficients (t₁=i, t₂=-1). Fernique §III.4. |
| `torusContinuumGreen_continuous_diag` | TorusOSAxioms | Easy | ✅ Verified (Gemini). f ↦ G_L(f,f) continuous. G_L is a continuous bilinear form on nuclear Fréchet space; diagonal restriction is continuous. Trèves Ch. 50. |

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
- `torusGaussianLimit_os1`: **PROVED** — OS1 regularity with q(f)=G_L(f,f), c=½. From `torusGaussianLimit_complex_cf_norm` + `torusContinuumGreen_nonneg`.
- `torusMatrixRP_of_weakLimit`: **PROVED** — Matrix RP transfers through weak limits via Re(Z[g]) = ∫ cos(ω(g)) dμ (bounded continuous) + `tendsto_finset_sum` + `ge_of_tendsto'`.
- `torusGaussianLimit_os3`: **PROVED** — OS3 reflection positivity from `torusMatrixRP_of_weakLimit` + `torusLattice_rp` + `torusGaussianLimit_fullConvergence`.

**Sorries (provable):**
- `torusEmbeddedTwoPoint_uniform_bound`: `E[Φ_N(f)²] ≤ C` from eigenvalue bound λ ≥ m².

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
| ~~`pphi2_generating_functional_real`~~ | OS2_WardIdentity | ~~Medium~~ | **Proved** — from `pphi2_measure_neg_invariant` via conj(Z[f])=Z[f]. |
| ~~`pphi2_measure_neg_invariant`~~ | OS2_WardIdentity | ~~Medium~~ | **Proved** — Z₂ symmetry baked into `IsPphi2Limit` definition. |
| ~~`generatingFunctional_translate_continuous`~~ | OS2_WardIdentity | ~~Easy~~ | **Proved** — via DCT (bound 1) + `continuous_timeTranslationSchwartz` from TimeTranslation.lean. |
| ~~`norm_generatingFunctional_le_one`~~ | OS2_WardIdentity | ✅ **Proved** | ‖Z[f]‖ ≤ 1 from norm_integral ≤ ∫ norm + ‖exp(ix)‖=1. |
| ~~`os4_clustering_implies_ergodicity`~~ | OS2_WardIdentity | ✅ **Proved** | OS4_Clustering → OS4_Ergodicity via reality of Z + Cesàro convergence. |
| `continuum_exponential_moments` | OS2_WardIdentity | Hard | `∀ c > 0, Integrable (exp(c·\|ω f\|)) μ`. Fernique + Nelson, transferred to limit. Feeds OS0 + OS1. |
| `rotation_invariance_continuum` | OS2_WardIdentity | Hard | `Z[R·f] = Z[f]` for R ∈ O(2). Ward identity + anomaly irrelevance. Feeds OS2. |
| `continuum_exponential_clustering` | OS2_WardIdentity | Hard | `‖Z[f+τ_a g] - Z[f]Z[g]‖ ≤ C·exp(-m₀·‖a‖)`. Spectral gap → exp clustering. Feeds OS4. |

**Proof chain theorems** (all fully proved, no sorries):
- `ward_identity_lattice`: Ward identity bound (**proved**)
- `anomaly_scaling_dimension`: lattice dispersion Taylor error bound (**proved**, cos_bound + crude bound)
- `anomaly_vanishes`: ‖Z[R·f] - Z[f]‖ ≤ C·a² (**proved**, from anomaly_bound_from_superrenormalizability)
- `os0_for_continuum_limit`: exponential moments → OS0_Analyticity (**proved**)
- `os1_for_continuum_limit`: exponential moments → OS1_Regularity (**proved**)
- `os2_for_continuum_limit`: translation + rotation → OS2_EuclideanInvariance (**proved**)
- `os4_for_continuum_limit`: exponential clustering → OS4_Clustering (**proved**, ε-δ from exp decay)
- `os4_clustering_implies_ergodicity`: OS4_Clustering → OS4_Ergodicity (**proved**, via reality of Z + Cesàro convergence)
- `norm_generatingFunctional_le_one`: ‖Z[f]‖ ≤ 1 (**proved**, norm_integral_le + ‖exp(ix)‖ = 1)

### Phase 6: OS axioms and assembly

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| ~~`euclideanAction2`~~ | OSAxioms | ✅ Proved | Constructed via `SchwartzMap.compCLMOfAntilipschitz` with inverse Euclidean action (antilipschitz + temperate growth). |
| ~~`euclideanAction2ℂ`~~ | OSAxioms | ✅ Proved | Same construction for complex Schwartz functions. |
| ~~`compTimeReflection2`~~ | OSAxioms | ✅ Proved | Constructed via `SchwartzMap.compCLMOfContinuousLinearEquiv` with time reflection as CLE. |
| ~~`compTimeReflection2_apply`~~ | OSAxioms | ✅ Proved | Follows by `rfl` from the construction. |
| ~~`SchwartzMap.translate`~~ | OSAxioms | ✅ Proved | Constructed via `SchwartzMap.compCLMOfAntilipschitz` with translation (antilipschitz + temperate growth). |
| ~~`os_reconstruction`~~ | Main | **Proved** | ∃ m₀ > 0 from ⟨mass, hmass⟩. Full Wightman formalism not formalized. |
| ~~`pphi2_wightman`~~ | Main | **Proved** | Full OS bundle + mass gap existence, from `pphi2_exists` + `os_reconstruction`. |
| ~~`pphi2_nontrivial`~~ | Main | **Proved** | Uses `pphi2_nontriviality` axiom. |
| ~~`pphi2_nonGaussian`~~ | Main | **Proved** | Uses `pphi2_nonGaussianity` axiom. |
| `pphi2_nontriviality` | Main | Hard | ∫ (ω f)² dμ > 0 for all f ≠ 0. Correlation inequalities (Griffiths, FKG). |
| `pphi2_nonGaussianity` | Main | Hard | ∫ (ω f)⁴ dμ − 3(∫ (ω f)² dμ)² ≠ 0. Perturbation theory, O(λ) at weak coupling. |
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
| ~~`continuumTimeReflection`~~ | AxiomInheritance | **Proved** — defined via `compCLMOfContinuousLinearEquiv`. |
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

5. **Hypercontractivity axioms** (`exponential_moment_bound`, `interacting_moment_bound`) — Cauchy-Schwarz density transfer approach. `gaussian_hypercontractivity_continuum` proved from gaussian-field.
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
| `pphi2_generating_functional_real` | OS2_WardIdentity | Im(Z[f])=0 via conj(Z[f])=Z[f] from Z₂ symmetry |
| `generatingFunctional_translate_continuous` | OS2_WardIdentity | t ↦ Z[f + τ_{(t,0)} g] continuous via DCT + `continuous_timeTranslationSchwartz` |
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
| `norm_generatingFunctional_le_one` | OS2_WardIdentity | ‖Z[f]‖ ≤ 1 via norm_integral + ‖exp(ix)‖ = 1 + measure_univ = 1 |
| `os4_clustering_implies_ergodicity` | OS2_WardIdentity | Clustering → Ergodicity via reality of Z[f], Cesàro convergence, and characteristic function bound |
| `transferWeight_measurable` | L2Operator | Transfer weight w(ψ) = exp(-(a/2)·h(ψ)) is measurable — continuity chain via `wickMonomial_continuous` |
| `transferWeight_bound` | L2Operator | Transfer weight is essentially bounded — from `wickPolynomial_bounded_below` + exponentiation |
| `transferGaussian_memLp` | L2Operator | Gaussian kernel ∈ L¹ — product factorization + `integrable_exp_neg_mul_sq` |
| `mulCLM` | L2Multiplication | Multiplication by bounded function as CLM on L² — Hölder (∞,2,2) |
| `convCLM` | L2Convolution | Convolution with L¹ function as CLM on L² — Young's inequality |

---

## Upstream: gaussian-field

The gaussian-field library (dependency) has **10 axioms and 1 sorry**.
- `GaussianField/Support.lean`: 2 axioms
- `HeatKernel/PositionKernel.lean`: 1 axiom (`circleHeatKernel_pos`)
- `HeatKernel/Bilinear.lean`: 0 axioms, 1 sorry (Green's function infrastructure; `greenFunctionBilinear_nonneg` proved)
- `Torus/Restriction.lean`: 2 axioms
- `SmoothCircle/Basic.lean`: 1 axiom
- `Nuclear/TensorProductFunctorAxioms.lean`: 4 axioms
See [gaussian-field status](../gaussian-field/status.md) for the full inventory.
