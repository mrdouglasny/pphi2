# P(Φ)₂ Project Status

## Overview

The project formalizes the construction of P(Φ)₂ Euclidean quantum field theory
in Lean 4 via the Glimm-Jaffe/Nelson lattice approach. All six phases are
structurally complete and the full project builds successfully (`lake build`,
3081 jobs).

The proof architecture is: axiomatize key analytic/probabilistic results with
detailed proof sketches, prove the logical structure connecting them, and
progressively fill in the axioms with full proofs.

**pphi2: 27 axioms, 13 sorries** | **gaussian-field (upstream): 21 axioms, 6 sorries**

## File inventory

### Active files (lattice approach)

| Phase | File | Status |
|-------|------|--------|
| Core | `Polynomial.lean` | 0 axioms |
| 1 | `WickOrdering/WickPolynomial.lean` | 1 axiom (wickMonomial_eq_hermite) |
| 1 | `WickOrdering/Counterterm.lean` | 1 axiom |
| 1 | `InteractingMeasure/LatticeAction.lean` | 0 axioms |
| 1 | `InteractingMeasure/LatticeMeasure.lean` | 0 axioms, 0 sorries |
| 1 | `InteractingMeasure/Normalization.lean` | 0 axioms, 0 sorries |
| 2 | `TransferMatrix/TransferMatrix.lean` | 0 axioms |
| 2 | `TransferMatrix/Positivity.lean` | 4 axioms |
| 2 | `OSProofs/OS3_RP_Lattice.lean` | 2 axioms, 2 sorries |
| 2 | `OSProofs/OS3_RP_Inheritance.lean` | 0 axioms, 0 sorries |
| 3 | `TransferMatrix/SpectralGap.lean` | 2 axioms |
| 3 | `OSProofs/OS4_MassGap.lean` | 0 axioms |
| 3 | `OSProofs/OS4_Ergodicity.lean` | 0 axioms |
| 4 | `ContinuumLimit/Embedding.lean` | 5 axioms |
| 4 | `ContinuumLimit/Tightness.lean` | 3 axioms |
| 4 | `ContinuumLimit/Convergence.lean` | 2 axioms, 0 sorries |
| 4 | `ContinuumLimit/AxiomInheritance.lean` | 1 axiom |
| 5 | `OSProofs/OS2_WardIdentity.lean` | 1 axiom, 0 sorries |
| 6 | `OSAxioms.lean` | 0 axioms, 0 sorries |
| 6 | `Main.lean` | 0 axioms, 5 sorries |
| 6 | `Bridge.lean` | 5 axioms, 6 sorries |

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

```
True  -- Placeholder; full formulation needs time translation on
      -- Configuration space and L²(μ) convergence
```

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
| `wickMonomial_eq_hermite` | WickPolynomial | Medium | Wick monomials equal probabilist Hermite polynomials |
| ~~`wickPolynomial_bounded_below`~~ | WickPolynomial | ~~Medium~~ | **Proved** — Even-degree Wick polynomial with positive leading coeff is bounded below. Proved via `poly_even_degree_bounded_below` (leading term domination + `Continuous.exists_forall_le`). |
| `wickConstant_log_divergence` | Counterterm | Medium | `c_a ~ (1/2π) log(1/a)` as a→0. Needs lattice Green's function asymptotics. |
| `latticeInteraction_single_site` | LatticeAction | **Proved** | V_a decomposes as sum of single-site functions. Enables FKG via log-supermodularity. (Replaced false `latticeInteraction_convex` axiom.) |
| ~~`field_all_moments_finite`~~ | Normalization | ✅ Proved | All moments finite: `pairing_is_gaussian` + `integrable_pow_of_mem_interior_integrableExpSet` gives Gaussian moments, domination by `exp(B)` handles the interaction weight. |

### Phase 2: Transfer matrix and reflection positivity

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| `transferOperator_selfAdjoint` | Positivity | Easy | T(ψ,ψ') = T(ψ',ψ) by construction (symmetric split of potential). |
| `transferOperator_positiveDefinite` | Positivity | Medium | `⟨f, Tf⟩ > 0` for f ≠ 0. From Gaussian kernel positivity + exp(-V) > 0. |
| `transferOperator_hilbertSchmidt` | Positivity | Medium | T is Hilbert-Schmidt. Kernel is L² because Gaussian factor gives exponential decay. |
| `transferOperator_traceClass` | Positivity | Medium | Follows from Hilbert-Schmidt (HS ∘ HS = trace class, and T = T^{1/2} · T^{1/2}). |
| `transferEigenvalue` | Positivity | Infrastructure | Existence of eigenvalue sequence. Spectral theorem for compact self-adjoint operators. |
| `transferEigenvalue_pos` | Positivity | Easy | Eigenvalues positive (from positive definiteness). |
| `transferEigenvalue_antitone` | Positivity | Easy | Eigenvalues decrease: λ₀ ≥ λ₁ ≥ ... (standard spectral ordering). |
| `transferEigenvalue_ground_simple` | Positivity | Medium | λ₀ > λ₁ (strict). Perron-Frobenius for positivity-preserving operators. |
| `action_decomposition` | OS3_RP_Lattice | Medium | Lattice action decomposes as S = S⁺ + S⁻ across time-reflection plane. Standard for nearest-neighbor actions. |
| `lattice_rp` | OS3_RP_Lattice | Medium | Lattice measure satisfies RP. From action decomposition + exp(-S) = exp(-S⁺)·exp(-S⁻) perfect square argument. |
| `lattice_rp_matrix` | OS3_RP_Lattice | Medium | Matrix form of RP: Σᵢⱼ cᵢc̄ⱼ Z[fᵢ-Θfⱼ] ≥ 0. Equivalent to lattice_rp. |
| `rp_from_transfer_positivity` | OS3_RP_Lattice | Medium | RP from transfer matrix positivity. Alternative proof route. |
| `partitionFunction_eq_trace` | TransferMatrix | Medium | Z = Tr(T^{Nt}). Standard transfer matrix identity. |

### Phase 3: Spectral gap and clustering

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| `hamiltonian_selfadjoint` | SpectralGap | Easy | H = -(1/a)log(T) is self-adjoint (from T self-adjoint, positive). |
| `hamiltonian_compact_resolvent` | SpectralGap | Medium | Follows from T being trace class. |
| `ground_state_simple` | SpectralGap | Medium | Non-degenerate ground state. From Perron-Frobenius (positivity-preserving). |
| `spectral_gap_uniform` | SpectralGap | Hard | Mass gap bounded below uniformly in a. Key input: the interaction is a bounded perturbation of the free field in the sense of Kato-Rellich, and the free mass gap is m > 0. Needs careful control of the perturbation as a→0. |
| `spectral_gap_lower_bound` | SpectralGap | Hard | m_phys ≥ c·m_bare. Quantitative bound on the physical mass. |
| `ground_state_positive` | SpectralGap | Medium | Ground state wavefunction is strictly positive. From Perron-Frobenius. |
| `ground_state_smooth` | SpectralGap | Medium | Ground state is smooth. From elliptic regularity of H. |
| `two_point_clustering_lattice` | OS4_MassGap | Medium | Two-point function decays exponentially with rate = mass gap. Standard spectral decomposition argument. |
| `general_clustering_lattice` | OS4_MassGap | Medium | General n-point clustering from spectral gap. |
| ~~`connectedTwoPoint_nonneg_delta`~~ | OS4_MassGap | ✅ Proved | Variance nonnegativity: direct proof via ∫(X-E[X])² ≥ 0. |
| `clustering_implies_ergodicity` | OS4_Ergodicity | Medium | Exponential clustering → ergodicity of time translations. Standard. |
| `unique_vacuum` | OS4_Ergodicity | Medium | Unique vacuum from ergodicity. Via GNS/OS reconstruction. |
| `exponential_mixing` | OS4_Ergodicity | Medium | Exponential mixing from mass gap. |
| `os4_lattice` | OS4_Ergodicity | Easy | Lattice satisfies OS4 (assembles the above). |

### Phase 4: Continuum limit

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| `latticeEmbed` | Embedding | Easy | The embedding ι_a : FinLatticeField → S'(ℝ^d). Constructible (should be `def`). |
| `latticeEmbed_eval` | Embedding | Easy | Embedding agrees with the explicit formula. Would be `rfl` if embed were a `def`. |
| `latticeEmbed_measurable` | Embedding | Easy | Map is continuous (stronger). Provable from finite-dimensional linearity. |
| `latticeEmbedLift` | Embedding | Medium | Lift of embedding to Configuration space. Domain matches `interactingLatticeMeasure`. |
| `latticeEmbedLift_measurable` | Embedding | Easy | Lifted embedding measurable. Continuous → measurable. |
| `second_moment_uniform` | Tightness | Hard | ∫|Φ_a(f)|² dν_a ≤ C(f) uniformly in a. Key input: Nelson's hypercontractive estimate + convergence of lattice propagator. |
| `moment_equicontinuity` | Tightness | Hard | Equicontinuity of moments in f. Needs Schwartz seminorm control. |
| `continuumMeasures_tight` | Tightness | Hard | Tightness via Mitoma criterion + Chebyshev + uniform second moments. Combines second_moment_uniform with Mitoma's theorem. |
| `nelson_hypercontractive` | Tightness | Hard | Nelson's hypercontractive estimate. Deep result (via Gross log-Sobolev inequality). |
| ~~`prokhorov_sequential`~~ | Convergence | ~~Infrastructure~~ | **Proved** — Prokhorov's theorem (sequential version). Now a theorem with complete proof. |
| `schwinger2_convergence` | Convergence | Medium | 2-point Schwinger functions converge. From weak convergence + uniform integrability. |
| `schwinger_n_convergence` | Convergence | Medium | n-point Schwinger functions converge. |
| `continuumLimit_nontrivial` | Convergence | Medium | Limit is not δ₀. From positive 2-point function. |
| `continuumLimit_nonGaussian` | Convergence | Medium | Limit is not Gaussian. From nonzero 4th cumulant. |
| `configuration_polishSpace` | Convergence | Infrastructure | S'(ℝ^d) is Polish (dual of nuclear Fréchet). Not in Mathlib. |
| `configuration_borelSpace` | Convergence | Infrastructure | Borel σ-algebra on S'(ℝ^d) = cylindrical σ-algebra (weak-* topology). Not in Mathlib. |
| `os0_inheritance` | AxiomInheritance | Medium | OS0 transfers: uniform moment bounds + pointwise convergence → limit has all moments finite. |
| `os1_inheritance` | AxiomInheritance | Easy | OS1 transfers: |cos(·)| ≤ 1 trivially. |
| `os3_inheritance` | AxiomInheritance | Medium | OS3 transfers: RP is a nonnegativity condition, closed under pointwise limits. Uses rp_closed_under_weak_limit from Phase 2. |
| `os4_inheritance` | AxiomInheritance | Medium | OS4 transfers: uniform mass gap + weak convergence → exponential clustering preserved. |
| `continuumLimit_satisfies_os0134` | AxiomInheritance | Easy | Assembly of the above four. |

### Phase 5: Euclidean invariance (OS2)

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| ~~`latticeAction_translation_invariant`~~ | OS2_WardIdentity | ~~Easy~~ | **Proved** — relabeling via `Equiv.subRight`. |
| `latticeMeasure_translation_invariant` | OS2_WardIdentity | Easy | Lattice measure is translation-invariant (from Gaussian + interaction). |
| `translation_invariance_continuum` | OS2_WardIdentity | Medium | Continuum limit is translation-invariant. Lattice translations approximate all translations as a→0; density argument. |
| `rotationBreakingOperator` | OS2_WardIdentity | Medium | The rotation anomaly operator O_break. Explicit construction from lattice Laplacian correction terms. |
| `ward_identity_lattice` | OS2_WardIdentity | Hard | Ward identity: ⟨δ_J F⟩_a = ⟨F · O_break⟩_a. Integration by parts in the path integral. |
| `anomaly_scaling_dimension` | OS2_WardIdentity | Medium | dim(O_break) = 4. From Fourier analysis: Δ_lattice - Δ_continuum = O(a²k⁴). |
| `anomaly_vanishes` | OS2_WardIdentity | Hard | Anomaly coefficient is O(a²). Needs power counting + super-renormalizability (no log corrections in d=2). |
| `rotation_invariance_continuum` | OS2_WardIdentity | Hard | SO(2) invariance in the limit. Combines Ward identity + anomaly vanishing + Schwinger functions determine the measure. |

### Phase 6: OS axioms and assembly

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| ~~`euclideanAction2`~~ | OSAxioms | ✅ Proved | Constructed via `SchwartzMap.compCLMOfAntilipschitz` with inverse Euclidean action (antilipschitz + temperate growth). |
| ~~`euclideanAction2ℂ`~~ | OSAxioms | ✅ Proved | Same construction for complex Schwartz functions. |
| ~~`compTimeReflection2`~~ | OSAxioms | ✅ Proved | Constructed via `SchwartzMap.compCLMOfContinuousLinearEquiv` with time reflection as CLE. |
| ~~`compTimeReflection2_apply`~~ | OSAxioms | ✅ Proved | Follows by `rfl` from the construction. |
| ~~`SchwartzMap.translate`~~ | OSAxioms | ✅ Proved | Constructed via `SchwartzMap.compCLMOfAntilipschitz` with translation (antilipschitz + temperate growth). |
| `os_reconstruction` | Main | Infrastructure | OS reconstruction theorem (Osterwalder-Schrader 1973, 1975). Would require formalizing Minkowski QFT. |
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
| `reflection_positivity_lattice` | OS3_RP_Lattice | Lattice RP from action decomposition. |
| ~~`continuumLimit`~~ | Convergence | **Proved** — Apply Prokhorov to the tight family. Uses `prokhorov_sequential` + `continuumMeasures_tight`. PolishSpace/BorelSpace instances now axioms. |
| ~~`continuumTimeReflection`~~ | AxiomInheritance | **Proved** — defined via `compCLMOfContinuousLinearEquiv`. |
| ~~`so2Generator`~~ | OS2_WardIdentity | **Proved** — SO(2) generator J f = x₁·∂f/∂x₂ - x₂·∂f/∂x₁ via `smulLeftCLM` + `lineDerivOpCLM`. |
| `pphi2_exists` | OS2_WardIdentity | Main existence theorem. Needs continuumLimit + continuumLimit_satisfies_allOS. |

---

## Priority ordering for filling axioms

### Tier 1: Infrastructure (unlocks further work)

1. ~~**`prokhorov_sequential`**~~ — **Proved.** Now a theorem with complete proof.
2. **`transferEigenvalue` + spectral axioms** — Need compact self-adjoint operator spectral theory in Mathlib.
3. **`latticeEmbed` / `latticeEmbedLift`** — Construction of the embedding as a CLM on Schwartz space.
4. ~~**`euclideanAction2` / `compTimeReflection2` / `SchwartzMap.translate`**~~ — ✅ All proved using `SchwartzMap.compCLMOfContinuousLinearEquiv` and `SchwartzMap.compCLMOfAntilipschitz`.

### Tier 2: Core analytic results (the hard axioms)

5. **`nelson_hypercontractive`** — Deep (Gross log-Sobolev). Key engine for all moment bounds.
6. **`second_moment_uniform` + `continuumMeasures_tight`** — Tightness argument. Depends on Nelson.
7. **`spectral_gap_uniform`** — Uniform mass gap. Kato-Rellich perturbation theory.
8. **`ward_identity_lattice` + `anomaly_vanishes`** — Ward identity + power counting for rotation invariance.

### Tier 3: Medium-difficulty proofs

9. Transfer matrix properties (self-adjoint, positive definite, Hilbert-Schmidt, trace class)
10. Reflection positivity on the lattice (action decomposition → perfect square)
11. Clustering from spectral gap (standard spectral decomposition)
12. OS axiom inheritance (mostly soft analysis: limits preserve bounds)
13. Bridge from `SatisfiesAllOS` to `SatisfiesFullOS` (connecting placeholder and real formulations)

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
| `continuumLimit_satisfies_allOS` | OS2_WardIdentity | All OS axioms (assembly from phases) |
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

---

## Upstream: gaussian-field axioms and sorries

The gaussian-field library (dependency) has **18 axioms and 4 sorries**.
These are organized by priority for pphi2.

*Updated 2026-02-24. See also `docs/gemini_review.md` for external review.*

### Used by pphi2 Normalization (FKG)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `fkg_from_lattice_condition` | Lattice/FKG | axiom | Hard | Core FKG: lattice condition ⟹ correlation inequality (Holley 1974). |
| `gaussian_fkg_lattice_condition` | Lattice/FKG | axiom | Hard | Gaussian density satisfies FKG lattice condition (non-positive off-diagonal precision). |
| `fkg_perturbed` | Lattice/FKG | axiom | Medium | FKG for single-site perturbed measure. Takes `hV_single_site`. |

Proved supporting results in FKG.lean:
- `chebyshev_integral_inequality` — 1D FKG for any probability measure (full proof via Fubini)
- `fkg_lattice_condition_mul` — product of FKG-lattice densities is FKG-lattice
- `fkg_lattice_condition_single_site` — exp(-V) trivially FKG for single-site V
- `fkg_lattice_gaussian` — **now a theorem** (derived from `gaussian_fkg_lattice_condition`)

### Lattice Laplacian properties — ALL PROVED

| Item | File | Type | Description |
|------|------|------|-------------|
| `finiteLaplacian_selfAdjoint` | Lattice/Laplacian | **theorem** | Proved via `Equiv.addRight (Pi.single i 1)` reindexing. |
| `finiteLaplacian_neg_semidefinite` | Lattice/Laplacian | **theorem** | Proved via summation by parts. |
| `massOperator_pos_def` | Lattice/Laplacian | **theorem** | Proved from neg-semidefinite + m²‖f‖² > 0. |

Note: `infiniteLaplacian` and `infiniteLaplacian_apply` remain axioms (infinite lattice, not needed by pphi2).

### Infinite lattice (not needed by pphi2)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `latticeEnum` | Lattice/RapidDecayLattice | axiom | Hard | ℤ^d ≃ ℕ shell enumeration. |
| `latticeEnum_norm_bound` | Lattice/RapidDecayLattice | axiom | Hard | ‖enum⁻¹(m)‖ ≤ C·m^{1/d}. |
| `latticeEnum_index_bound` | Lattice/RapidDecayLattice | axiom | Hard | enum(x) ≤ C·(1+‖x‖)^d. |
| `latticeRapidDecayEquiv` | Lattice/RapidDecayLattice | axiom | Hard | CLE to RapidDecaySeq. |

### Heat kernel (cylinder QFT, not used by lattice approach)

PositionKernel.lean has **7 remaining axioms**. Proved axioms (now theorems):
- `mehlerKernel_pos` — positivity from closed form (rpow_pos + sinh_pos + exp_pos)
- `circleHeatKernel_symmetric` — tsum_congr + ring
- `circleHeatKernel_periodic₁/₂` — fourierBasisFun_periodic
- `circleHeatKernel_summable` — geometric series comparison
- `mehlerKernel_summable` — Hermite sup bound + polynomial × geometric series

Remaining axioms:
| Item | Difficulty | Description |
|------|-----------|-------------|
| `mehlerKernel_eq_series` | Hard | Mehler's formula (PDE uniqueness or generating function). |
| `mehlerKernel_reproduces_hermite` | Medium | Series expansion + orthonormality. |
| `mehlerKernel_semigroup` | Medium | Series expansion + Fubini + orthonormality. |
| `circleHeatKernel_pos` | Hard | Requires Poisson summation (periodized Gaussian). |
| `circleHeatKernel_reproduces_fourier` | Medium | Fourier orthonormality. |
| `circleHeatKernel_semigroup` | Medium | Fourier + Fubini + orthonormality. |
| `cylinderHeatKernel_eq_series` | Medium | Product of two series → single series via Nat.pair. |
| `cylinderEval_summable` | Medium | Convergence of eigenfunction expansion. |
| `cylinderHeatKernel_reproduces` | Hard | Bridge theorem. |

### Sorries

| Sorry | File | Difficulty | Description |
|-------|------|-----------|-------------|
| `schwartzPointwiseProduct_apply` | SchwartzNuclear/SchwartzTensorProduct | Medium | Hermite-Fubini factorization. |
| `hermiteTensorProduct_*` (2) | SchwartzNuclear/HermiteTensorProduct | Medium | Hermite tensor product sorries. |
| `schwartzSlicing_*` (1) | SchwartzNuclear/SchwartzSlicing | Medium | Schwartz slicing sorry. |

### Summary

| Category | Axioms | Sorries |
|----------|--------|---------|
| PositionKernel (heat kernel / cylinder) | 9 | 0 |
| RapidDecayLattice (infinite lattice) | 4 | 0 |
| Laplacian (infinite only) | 2 | 0 |
| FKG (used by pphi2 Normalization) | 3 | 0 |
| SchwartzNuclear | 0 | 4 |
| **Total** | **21** | **6** |
