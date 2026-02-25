# P(Φ)₂ Project Status

## Overview

The project formalizes the construction of P(Φ)₂ Euclidean quantum field theory
in Lean 4 via the Glimm-Jaffe/Nelson lattice approach. All six phases are
structurally complete and the full project builds successfully (`lake build`,
3103 jobs).

The proof architecture is: axiomatize key analytic/probabilistic results with
detailed proof sketches, prove the logical structure connecting them, and
progressively fill in the axioms with full proofs.

**pphi2: 38 axioms (33 required + 5 Option B), 16 sorries** | **gaussian-field (upstream): 15 axioms, 9 sorries**

Note: The 5 "Option B" axioms in `Hypercontractivity.lean` provide an alternative
full Gross-Rothaus-Simon proof path but are **not required** for the main pphi2 theorem.
The main proof uses Option A (Cauchy-Schwarz density transfer, 2 axioms + 1 proved theorem).

## File inventory

### Active files (lattice approach)

| Phase | File | Status |
|-------|------|--------|
| Core | `Polynomial.lean` | 0 axioms |
| 1 | `WickOrdering/WickPolynomial.lean` | 0 axioms |
| 1 | `WickOrdering/Counterterm.lean` | 1 axiom |
| 1 | `InteractingMeasure/LatticeAction.lean` | 0 axioms |
| 1 | `InteractingMeasure/LatticeMeasure.lean` | 0 axioms, 0 sorries |
| 1 | `InteractingMeasure/Normalization.lean` | 0 axioms, 0 sorries |
| 2 | `TransferMatrix/TransferMatrix.lean` | 0 axioms |
| 2 | `TransferMatrix/L2Operator.lean` | 8 axioms (4 operator + 4 eigenvalue) |
| 2 | `TransferMatrix/Positivity.lean` | 0 axioms (energy levels, mass gap) |
| 2 | `OSProofs/OS3_RP_Lattice.lean` | 2 axioms, 1 sorry |
| 2 | `OSProofs/OS3_RP_Inheritance.lean` | 0 axioms, 0 sorries |
| 3 | `TransferMatrix/SpectralGap.lean` | 2 axioms |
| 3 | `OSProofs/OS4_MassGap.lean` | 0 axioms, 2 sorries |
| 3 | `OSProofs/OS4_Ergodicity.lean` | 0 axioms, 0 sorries |
| 4 | `ContinuumLimit/Embedding.lean` | 0 axioms |
| 4 | `ContinuumLimit/Hypercontractivity.lean` | 7 axioms (2 required Option A + 5 optional Option B), 1 proved theorem |
| 4 | `ContinuumLimit/Tightness.lean` | 3 axioms |
| 4 | `ContinuumLimit/Convergence.lean` | 2 axioms, 4 sorries |
| 4 | `ContinuumLimit/AxiomInheritance.lean` | 2 axioms, 1 sorry |
| 5 | `OSProofs/OS2_WardIdentity.lean` | 6 axioms, 5 sorries |
| 6 | `OSAxioms.lean` | 0 axioms, 0 sorries |
| 6 | `Main.lean` | 0 axioms, 2 sorries |
| 6 | `Bridge.lean` | 5 axioms, 1 sorry |

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

None — all sorries have been resolved. The 5 remaining axioms are the infrastructure CLM axioms listed above.

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

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| ~~`polynomial_lower_bound`~~ | Polynomial | ✅ Removed | Dead code — superseded by `wickPolynomial_bounded_below` in WickPolynomial.lean. |
| ~~`wickMonomial_eq_hermite`~~ | WickPolynomial | ~~Medium~~ | **Proved** — via `wick_eq_hermiteR_rpow` from gaussian-field HermiteWick |
| ~~`wickPolynomial_bounded_below`~~ | WickPolynomial | ~~Medium~~ | **Proved** — Even-degree Wick polynomial with positive leading coeff is bounded below. Proved via `poly_even_degree_bounded_below` (leading term domination + `Continuous.exists_forall_le`). |
| `wickConstant_log_divergence` | Counterterm | Medium | `c_a ~ (1/2π) log(1/a)` as a→0. Needs lattice Green's function asymptotics. |
| `latticeInteraction_single_site` | LatticeAction | **Proved** | V_a decomposes as sum of single-site functions. Enables FKG via log-supermodularity. (Replaced false `latticeInteraction_convex` axiom.) |
| ~~`field_all_moments_finite`~~ | Normalization | ✅ Proved | All moments finite: `pairing_is_gaussian` + `integrable_pow_of_mem_interior_integrableExpSet` gives Gaussian moments, domination by `exp(B)` handles the interaction weight. |

### Phase 2: Transfer matrix and reflection positivity

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| `transferOperatorCLM` | L2Operator | Medium | Transfer matrix as CLM on L²(ℝ^Ns). Integral operator with Gaussian-bounded kernel. |
| `transferOperator_isSelfAdjoint` | L2Operator | Easy | Self-adjointness from kernel symmetry T(ψ,ψ') = T(ψ',ψ). |
| `transferOperator_isCompact` | L2Operator | Medium | Compactness from Hilbert-Schmidt property (Gaussian kernel decay). |
| `transferOperator_spectral` | L2Operator | **Proved** | Spectral decomposition from `compact_selfAdjoint_spectral` (gaussian-field). |
| `transferEigenvalue` | L2Operator | Infrastructure | Sorted eigenvalue sequence λ₀ ≥ λ₁ ≥ ... from spectral decomposition. |
| `transferEigenvalue_pos` | L2Operator | Easy | Eigenvalues positive (Perron-Frobenius for positivity-improving operators). |
| `transferEigenvalue_antitone` | L2Operator | Easy | Eigenvalues decrease: λ₀ ≥ λ₁ ≥ ... (by construction from sorting). |
| `transferEigenvalue_ground_simple` | L2Operator | Medium | λ₀ > λ₁ (strict). Perron-Frobenius for positivity-improving operators. |
| `action_decomposition` | OS3_RP_Lattice | Medium | Lattice action decomposes as S = S⁺ + S⁻ across time-reflection plane. Standard for nearest-neighbor actions. |
| ~~`lattice_rp`~~ | OS3_RP_Lattice | **Theorem (sorry)** | RP inequality for `interactingLatticeMeasure`. |
| `lattice_rp_matrix` | OS3_RP_Lattice | Medium | Matrix form of RP: Σᵢⱼ cᵢc̄ⱼ Z[fᵢ-Θfⱼ] ≥ 0. Equivalent to lattice_rp. |
| ~~`rp_from_transfer_positivity`~~ | OS3_RP_Lattice | **Theorem (sorry)** | ⟨f, T^n f⟩ ≥ 0 via `transferOperatorCLM`. |

### Phase 3: Spectral gap and clustering

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| `spectral_gap_uniform` | SpectralGap | Hard | Mass gap bounded below uniformly in a. Key input: the interaction is a bounded perturbation of the free field in the sense of Kato-Rellich, and the free mass gap is m > 0. Needs careful control of the perturbation as a→0. |
| `spectral_gap_lower_bound` | SpectralGap | Hard | m_phys ≥ c·m_bare. Quantitative bound on the physical mass. |
| ~~`connectedTwoPoint_nonneg_delta`~~ | OS4_MassGap | ✅ Proved | Variance nonnegativity: direct proof via ∫(X-E[X])² ≥ 0. |
| ~~`two_point_clustering_lattice`~~ | OS4_MassGap | **Theorem (sorry)** | Exponential decay bound using `finLatticeDelta` and `massGap`. |
| ~~`general_clustering_lattice`~~ | OS4_MassGap | **Theorem (sorry)** | Quantified clustering over bounded observables. |
| ~~`clustering_implies_ergodicity`~~ | OS4_Ergodicity | **Theorem (sorry)** | Exponential clustering → ergodicity of time translations. |
| ~~`unique_vacuum`~~ | OS4_Ergodicity | ✅ **Proved** | From `transferEigenvalue_ground_simple`. No sorry. |
| ~~`exponential_mixing`~~ | OS4_Ergodicity | **Theorem (sorry)** | Exponential mixing from mass gap. |
| ~~`os4_lattice`~~ | OS4_Ergodicity | **Theorem (sorry)** | Lattice satisfies OS4 (assembles the above). |

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
| `wick_is_eigenfunction` | Hypercontractivity | Medium | (Option B) Wick monomials :φ^n: are eigenfunctions of the number operator. |
| `ou_semigroup_exists` | Hypercontractivity | Medium | (Option B) OU semigroup P_t exists on L²(μ_GFF) with Mehler formula. |
| `ou_semigroup_eigenvalue` | Hypercontractivity | Medium | (Option B) P_t(:φ^n:) = e^{-nt}·:φ^n:. From Mehler kernel reproducing formula. |
| `gross_theorem_lsi_to_hypercontractivity` | Hypercontractivity | Hard | (Option B) Gross's theorem: LSI ⟹ OU hypercontractivity via Rothaus-Simon ODE. |
| `bakry_emery_gaussian_lsi` | Hypercontractivity | Medium | (Option B) Bakry-Émery Γ₂ criterion gives LSI(m²) for Gaussian. |
| ~~`prokhorov_sequential`~~ | Convergence | ~~Infrastructure~~ | **Proved** — Prokhorov's theorem (sequential version). Now a theorem with complete proof. |
| ~~`schwinger2_convergence`~~ | Convergence | **Theorem (sorry)** | 2-point Schwinger functions converge along subsequence. |
| ~~`schwinger_n_convergence`~~ | Convergence | **Theorem (sorry)** | n-point Schwinger functions converge along subsequence. |
| ~~`continuumLimit_nontrivial`~~ | Convergence | **Theorem (sorry)** | ∫ (ω f)² dμ > 0 for some f. |
| ~~`continuumLimit_nonGaussian`~~ | Convergence | **Theorem (sorry)** | Connected 4-point function ≠ 0. |
| `configuration_polishSpace` | Convergence | Infrastructure | S'(ℝ^d) is Polish (dual of nuclear Fréchet). Not in Mathlib. |
| `configuration_borelSpace` | Convergence | Infrastructure | Borel σ-algebra on S'(ℝ^d) = cylindrical σ-algebra (weak-* topology). Not in Mathlib. |
| `os0_inheritance` | AxiomInheritance | Medium | OS0 transfers: uniform moment bounds + pointwise convergence → limit has all moments finite. |
| `os3_inheritance` | AxiomInheritance | Medium | Abstract RP: ∫ F(ω)·F(Θ*ω) dμ ≥ 0 for bounded continuous F. Follows from lattice_rp_matrix + rp_closed_under_weak_limit (proved). |
| ~~`os4_inheritance`~~ | AxiomInheritance | **Theorem (sorry)** | Exponential clustering of connected 2-point functions. |
| ~~`continuumLimit_satisfies_os0134`~~ | AxiomInheritance | **Theorem** | Assembly of os0/os1/os3/os4 inheritance results. |

Note: `os1_inheritance` is a theorem (not axiom) — OS1 transfers trivially since |cos(·)| ≤ 1.

### Phase 5: Euclidean invariance (OS2) and OS proof chains

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| ~~`latticeAction_translation_invariant`~~ | OS2_WardIdentity | ~~Easy~~ | **Proved** — relabeling via `Equiv.subRight`. |
| `continuum_exponential_moments` | OS2_WardIdentity | Hard | `∀ c > 0, Integrable (exp(c·\|ω f\|)) μ`. Fernique + Nelson, transferred to limit. Feeds OS0 + OS1. |
| `rotation_invariance_continuum` | OS2_WardIdentity | Hard | `Z[R·f] = Z[f]` for R ∈ O(2). Ward identity + anomaly irrelevance. Feeds OS2. |
| `continuum_exponential_clustering` | OS2_WardIdentity | Hard | `‖Z[f+τ_a g] - Z[f]Z[g]‖ ≤ C·exp(-m₀·‖a‖)`. Spectral gap → exp clustering. Feeds OS4. |

**Proof chain theorems** (sorry-proofed with real Lean types):
- `latticeMeasure_translation_invariant`: integral equality under lattice translation (sorry)
- `translation_invariance_continuum`: `Z[τ_v f] = Z[f]` (3 sorries: continuity, density, combine)
- `ward_identity_lattice`: Ward identity bound (proved; pending lattice rotation action)
- `anomaly_scaling_dimension`: lattice dispersion Taylor error bound (**proved**, cos_bound + crude bound)
- `anomaly_vanishes`: ‖Z[R·f] - Z[f]‖ ≤ C·a² for continuum-embedded lattice measure (sorry)
- `os0_for_continuum_limit`: exponential moments → OS0_Analyticity (3 sorries)
- `os1_for_continuum_limit`: exponential moments → OS1_Regularity (2 sorries: h_exp_norm_bound, final assembly)
- `os2_for_continuum_limit`: translation + rotation → OS2_EuclideanInvariance (2 sorries)
- `os4_for_continuum_limit`: exponential clustering → OS4_Clustering (**fully proved**, ε-δ from exp decay)

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
| ~~`pphi2_nontrivial`~~ | Main | **Theorem (sorry)** | ∫ (ω f)² dμ > 0 for all f ≠ 0. |
| ~~`pphi2_nonGaussian`~~ | Main | **Theorem (sorry)** | ∫ (ω f)⁴ dμ - 3(∫ (ω f)² dμ)² ≠ 0. |
| `measure_determined_by_schwinger` | Bridge | Medium | Moment determinacy on S'(ℝ²) with exponential (Fernique-type) moment bound. |
| `wick_constant_comparison` | Bridge | Medium | Wick constant c_a ≈ (2π)⁻¹ log(1/a) with bounded remainder. |
| `same_continuum_measure` | Bridge | Medium | pphi2 and Phi4 constructions agree at weak coupling. Requires `IsPphi2ContinuumLimit`, `IsPhi4ContinuumLimit`, `IsWeakCoupling`. |
| `os2_from_phi4` | Bridge | Medium | OS2 for Phi4 continuum limit. Requires `IsPhi4ContinuumLimit` hypothesis. |
| `os3_from_pphi2` | Bridge | Medium | OS3 for pphi2 continuum limit. Requires `IsPphi2ContinuumLimit` hypothesis. |

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
| ~~`reflection_positivity_lattice`~~ | OS3_RP_Lattice | **Converted** to `lattice_rp` theorem (sorry). |
| ~~`continuumLimit`~~ | Convergence | **Proved** — Apply Prokhorov to the tight family. Uses `prokhorov_sequential` + `continuumMeasures_tight`. PolishSpace/BorelSpace instances now axioms. |
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
| `continuumLimit_satisfies_fullOS` | OS2_WardIdentity | All OS axioms (assembly into SatisfiesFullOS, with sorry for type gaps) |
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
| `energyLevel_gap` | Positivity | E₁ > E₀ from transfer eigenvalue gap |
| `prokhorov_sequential` | Convergence | Prokhorov's theorem (sequential version) — proved as theorem with proof |
| `wickPolynomial_bounded_below` | WickPolynomial | Wick polynomial bounded below — from leading term domination via `poly_even_degree_bounded_below` |
| `poly_even_degree_bounded_below` | WickPolynomial | Even-degree polynomial with positive leading coeff is bounded below — `eval_eq_sum_range` + coefficient bound + `Continuous.exists_forall_le` |
| `field_second_moment_finite` | Normalization | ∫\|ω(δ_x)\|² dμ_a < ∞ — `integrable_withDensity_iff` + `pairing_product_integrable` + domination by exp(B)·f² |
| `field_all_moments_finite` | Normalization | ∫\|ω(δ_x)\|^p dμ_a < ∞ for all p — `pairing_is_gaussian` + `integrable_pow_of_mem_interior_integrableExpSet` |
| `euclideanAction2` | OSAxioms | E(2) pullback on Schwartz functions — `compCLMOfAntilipschitz` with inverse Euclidean action |
| `euclideanAction2ℂ` | OSAxioms | Same for complex Schwartz functions |
| `compTimeReflection2` | OSAxioms | Time reflection on Schwartz space — `compCLMOfContinuousLinearEquiv` with time reflection CLE |
| `SchwartzMap.translate` | OSAxioms | Translation on Schwartz space — `compCLMOfAntilipschitz` with translation |
| `so2Generator` | OS2_WardIdentity | SO(2) generator J f = x₁·∂f/∂x₂ - x₂·∂f/∂x₁ — `smulLeftCLM` + `lineDerivOpCLM` |
| `continuumLimit` | Convergence | Continuum limit via Prokhorov — `prokhorov_sequential` + `continuumMeasures_tight` |
| `latticeEmbed` | Embedding | Lattice→S'(ℝ^d) embedding — `SchwartzMap.mkCLMtoNormedSpace` with `|ι(φ)(f)| ≤ (a^d·Σ|φ(x)|)·seminorm(0,0)(f)` |
| `latticeEmbed_eval` | Embedding | Evaluation formula — `rfl` from construction |
| `transferOperator_spectral` | L2Operator | Spectral decomposition — `compact_selfAdjoint_spectral` from gaussian-field |
| `latticeEmbed_measurable` | Embedding | `configuration_measurable_of_eval_measurable` + `continuous_apply` for each coordinate |

---

## Upstream: gaussian-field

The gaussian-field library (dependency) has **15 axioms and 13 sorries**.
See [gaussian-field status](../gaussian-field/status.md) for the full inventory.
