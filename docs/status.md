# P(Φ)₂ Project Status

## Overview

The project formalizes the construction of P(Φ)₂ Euclidean quantum field theory
in Lean 4 via the Glimm-Jaffe/Nelson lattice approach. All six phases are
structurally complete and the full project builds successfully (`lake build`,
3067 jobs).

The proof architecture is: axiomatize key analytic/probabilistic results with
detailed proof sketches, prove the logical structure connecting them, and
progressively fill in the axioms with full proofs.

## File inventory

### Active files (lattice approach)

| Phase | File | Status |
|-------|------|--------|
| Core | `Polynomial.lean` | 1 sorry (polynomial_lower_bound) |
| 1 | `WickOrdering/WickPolynomial.lean` | 3 axioms |
| 1 | `WickOrdering/Counterterm.lean` | 1 axiom, 2 sorries |
| 1 | `InteractingMeasure/LatticeAction.lean` | 1 axiom, 1 sorry |
| 1 | `InteractingMeasure/LatticeMeasure.lean` | 4 sorries |
| 1 | `InteractingMeasure/Normalization.lean` | 1 axiom, 4 sorries |
| 2 | `TransferMatrix/TransferMatrix.lean` | 1 axiom, 2 sorries |
| 2 | `TransferMatrix/Positivity.lean` | 8 axioms, 1 sorry |
| 2 | `OSProofs/OS3_RP_Lattice.lean` | 4 axioms, 2 sorries |
| 2 | `OSProofs/OS3_RP_Inheritance.lean` | 0 axioms, 1 sorry |
| 3 | `TransferMatrix/SpectralGap.lean` | 7 axioms |
| 3 | `OSProofs/OS4_MassGap.lean` | 3 axioms, 1 sorry |
| 3 | `OSProofs/OS4_Ergodicity.lean` | 4 axioms |
| 4 | `ContinuumLimit/Embedding.lean` | 5 axioms, 1 sorry |
| 4 | `ContinuumLimit/Tightness.lean` | 4 axioms |
| 4 | `ContinuumLimit/Convergence.lean` | 5 axioms, 1 sorry |
| 4 | `ContinuumLimit/AxiomInheritance.lean` | 5 axioms, 1 sorry |
| 5 | `OSProofs/OS2_WardIdentity.lean` | 8 axioms, 2 sorries |
| 6 | `OSAxioms.lean` | 0 axioms, 0 sorries |
| 6 | `Main.lean` | 1 axiom, 1 sorry |

**Active file totals: 61 axioms, 25 sorries**

### Inactive files (old DDJ/stochastic quantization approach)

These files are from the earlier DDJ-based approach and are not imported by the
build. They may be useful as reference but are not part of the current
development path.

- `Basic.lean` — cylinder test function spaces (44 sorries in instances)
- `FunctionSpaces/WeightedLp.lean`, `FunctionSpaces/Embedding.lean`
- `GaussianCylinder/Covariance.lean`
- `MeasureCylinder/Regularized.lean`, `MeasureCylinder/UVLimit.lean`
- `StochasticQuant/DaPratoDebussche.lean`
- `StochasticEst/InfiniteVolumeBound.lean`
- `Energy/EnergyEstimate.lean`
- `InfiniteVolume/Tightness.lean`
- `Integrability/Regularity.lean`
- `ReflectionPositivity/RPPlane.lean`
- `EuclideanInvariance/Invariance.lean`

---

## Axiom inventory (active files only)

### Difficulty rating

- **Easy**: Straightforward from Mathlib or simple calculation
- **Medium**: Requires nontrivial but standard arguments
- **Hard**: Deep analytic result, significant proof effort
- **Infrastructure**: Needs Mathlib API that may not exist yet

### Phase 1: Wick ordering and lattice measure

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| `wickMonomial_eq_hermite` | WickPolynomial | Medium | Wick monomials equal probabilist Hermite polynomials |
| `wickPolynomial_bounded_below` | WickPolynomial | Medium | Even-degree Wick polynomial with positive leading coeff is bounded below. Provable from leading term domination. |
| `wickConstant_log_divergence` | Counterterm | Medium | `c_a ~ (1/2π) log(1/a)` as a→0. Needs lattice Green's function asymptotics. |
| `latticeInteraction_convex` | LatticeAction | Medium | V_a is convex when P is convex. Needed for FKG. Sum of convex functions argument. |
| `field_all_moments_finite` | Normalization | Medium | All moments of field evaluations are finite under the interacting measure. From Nelson's estimate. |

### Phase 2: Transfer matrix and reflection positivity

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| `transferOperator_selfAdjoint` | Positivity | Easy | T(ψ,ψ') = T(ψ',ψ) by construction (symmetric split of potential). |
| `transferOperator_positiveDefinite` | Positivity | Medium | `⟨f, Tf⟩ > 0` for f ≠ 0. From Gaussian kernel positivity + exp(-V) > 0. |
| `transferOperator_hilbertSchmidt` | Positivity | Medium | T is Hilbert-Schmidt. Kernel is L² because Gaussian factor gives exponential decay. |
| `transferOperator_traceClass` | Positivity | Medium | Follows from Hilbert-Schmidt (HS ∘ HS = trace class, and T = T^{1/2} · T^{1/2}). |
| `transferEigenvalue` | Positivity | Infrastructure | Existence of eigenvalue sequence. Needs spectral theorem for compact self-adjoint operators in Mathlib. |
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
| `connectedTwoPoint_nonneg_delta` | OS4_MassGap | Medium | Connected 2-point function ≥ 0 for delta functions (positivity). |
| `clustering_implies_ergodicity` | OS4_Ergodicity | Medium | Exponential clustering → ergodicity of time translations. Standard. |
| `unique_vacuum` | OS4_Ergodicity | Medium | Unique vacuum from ergodicity. Via GNS/OS reconstruction. |
| `exponential_mixing` | OS4_Ergodicity | Medium | Exponential mixing from mass gap. |
| `os4_lattice` | OS4_Ergodicity | Easy | Lattice satisfies OS4 (assembles the above). |

### Phase 4: Continuum limit

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| `latticeEmbed` | Embedding | Medium | The embedding ι_a : FinLatticeField → Configuration(S(ℝ^d)). Needs to show that f ↦ a^d Σ_x φ(x)f(ax) is continuous on Schwartz space. Finite sum of point evaluations — straightforward. |
| `latticeEmbed_eval` | Embedding | Easy | Embedding agrees with the explicit formula. By construction. |
| `latticeEmbed_measurable` | Embedding | Medium | Measurability of the embedding. Needs measurable structure on S'(ℝ^d). |
| `latticeEmbedLift` | Embedding | Medium | Lift of embedding to Configuration space. |
| `latticeEmbedLift_measurable` | Embedding | Medium | Measurability of the lifted embedding. |
| `second_moment_uniform` | Tightness | Hard | ∫|Φ_a(f)|² dν_a ≤ C(f) uniformly in a. Key input: Nelson's hypercontractive estimate + convergence of lattice propagator. |
| `moment_equicontinuity` | Tightness | Hard | Equicontinuity of moments in f. Needs Schwartz seminorm control. |
| `continuumMeasures_tight` | Tightness | Hard | Tightness via Mitoma criterion + Chebyshev + uniform second moments. Combines second_moment_uniform with Mitoma's theorem. |
| `nelson_hypercontractive` | Tightness | Hard | Nelson's hypercontractive estimate. Deep result (via Gross log-Sobolev inequality). |
| `prokhorov_sequential` | Convergence | Infrastructure | Prokhorov's theorem (sequential version). Partially in Mathlib (`tight_iff_isRelativelyCompact`). |
| `schwinger2_convergence` | Convergence | Medium | 2-point Schwinger functions converge. From weak convergence + uniform integrability. |
| `schwinger_n_convergence` | Convergence | Medium | n-point Schwinger functions converge. |
| `continuumLimit_nontrivial` | Convergence | Medium | Limit is not δ₀. From positive 2-point function. |
| `continuumLimit_nonGaussian` | Convergence | Medium | Limit is not Gaussian. From nonzero 4th cumulant. |
| `os0_inheritance` | AxiomInheritance | Medium | OS0 transfers: uniform moment bounds + pointwise convergence → limit has all moments finite. |
| `os1_inheritance` | AxiomInheritance | Easy | OS1 transfers: |cos(·)| ≤ 1 trivially. |
| `os3_inheritance` | AxiomInheritance | Medium | OS3 transfers: RP is a nonnegativity condition, closed under pointwise limits. Uses rp_closed_under_weak_limit from Phase 2. |
| `os4_inheritance` | AxiomInheritance | Medium | OS4 transfers: uniform mass gap + weak convergence → exponential clustering preserved. |
| `continuumLimit_satisfies_os0134` | AxiomInheritance | Easy | Assembly of the above four. |

### Phase 5: Euclidean invariance (OS2)

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| `latticeAction_translation_invariant` | OS2_WardIdentity | Easy | Lattice action is translation-invariant (relabeling sum indices). |
| `latticeMeasure_translation_invariant` | OS2_WardIdentity | Easy | Lattice measure is translation-invariant (from Gaussian + interaction). |
| `translation_invariance_continuum` | OS2_WardIdentity | Medium | Continuum limit is translation-invariant. Lattice translations approximate all translations as a→0; density argument. |
| `rotationBreakingOperator` | OS2_WardIdentity | Medium | The rotation anomaly operator O_break. Explicit construction from lattice Laplacian correction terms. |
| `ward_identity_lattice` | OS2_WardIdentity | Hard | Ward identity: ⟨δ_J F⟩_a = ⟨F · O_break⟩_a. Integration by parts in the path integral. |
| `anomaly_scaling_dimension` | OS2_WardIdentity | Medium | dim(O_break) = 4. From Fourier analysis: Δ_lattice - Δ_continuum = O(a²k⁴). |
| `anomaly_vanishes` | OS2_WardIdentity | Hard | Anomaly coefficient is O(a²). Needs power counting + super-renormalizability (no log corrections in d=2). |
| `rotation_invariance_continuum` | OS2_WardIdentity | Hard | SO(2) invariance in the limit. Combines Ward identity + anomaly vanishing + Schwinger functions determine the measure. |

### Phase 6: Assembly

| Axiom | File | Difficulty | Description |
|-------|------|-----------|-------------|
| `os_reconstruction` | Main | Infrastructure | OS reconstruction theorem (Osterwalder-Schrader 1973, 1975). Converts Euclidean QFT to Wightman QFT. Would require formalizing Minkowski QFT. |

---

## Sorry inventory (active files only)

These are theorems/definitions with `sorry` that need proofs filled in.

### Provable with current Lean/Mathlib

| Sorry | File | Notes |
|-------|------|-------|
| `polynomial_lower_bound` | Polynomial | Even degree + positive leading coeff → bounded below. Needs Polynomial API. |
| `transferKernel_symmetric` | TransferMatrix | Algebra: the symmetric split K(ψ,ψ') + ½h(ψ) + ½h(ψ') is symmetric. Should close with `ring` after proper unfolding. |
| `timeCoupling_eq_zero_iff` | TransferMatrix | When is the time coupling zero? Needs analysis of the sum. |
| `latticeInteraction_continuous` | LatticeAction | Continuous function on finite-dimensional space. Composition of continuous operations. |
| `continuumMeasure_isProbability` | Embedding | Pushforward of probability measure is probability measure. Standard measure theory. |
| `connectedTwoPoint_symm` | OS4_MassGap | Symmetry of the connected 2-point function. Integral equality. |

### Require nontrivial proofs

| Sorry | File | Notes |
|-------|------|-------|
| `interactionFunctional_measurable` | LatticeMeasure | Measurability of V_a as function on Configuration space. |
| `boltzmannWeight_integrable` | LatticeMeasure | exp(-V_a) is integrable w.r.t. Gaussian measure. Uses V_a bounded below. |
| `partitionFunction_pos` | LatticeMeasure | Z_a > 0. From exp(-V_a) > 0 and Gaussian measure has full support. |
| `interactingLatticeMeasure_isProbability` | LatticeMeasure | μ_a is a probability measure. From Z_a > 0 + normalization. |
| `boundedFunctions_integrable` | Normalization | Bounded functions are integrable w.r.t. probability measure. |
| `field_second_moment_finite` | Normalization | Second moment finite. From Nelson's estimate. |
| `fkg_interacting` | Normalization | FKG for the interacting measure. From lattice FKG + convex perturbation. |
| `generating_functional_bounded` | Normalization | |Z[f]| ≤ 1 for real f. From |exp(it)| = 1. |
| `wickConstant_le_inv_mass_sq` | Counterterm | c_a ≤ 1/m². Upper bound on Wick constant. |
| `wickConstant_antitone_mass` | Counterterm | c_a decreasing in mass. Monotonicity of Green's function. |
| `energyLevel_gap` | Positivity | E₁ > E₀. From transfer eigenvalue gap. |
| `rp_closed_under_weak_limit` | OS3_RP_Inheritance | RP closed under weak limits. General topological fact: nonnegativity conditions are closed. |
| `reflection_positivity_lattice` | OS3_RP_Lattice | Lattice RP from action decomposition. |
| `continuumLimit` (as `continuumLimit_weak_convergence`) | Convergence | Apply Prokhorov to the tight family. Needs prokhorov_sequential + continuumMeasures_tight. |
| `continuumTimeReflection` | AxiomInheritance | Define Θf where (Θf)(t,x) = f(-t,x) as SchwartzMap. Needs Schwartz space API. |
| `so2Generator` | OS2_WardIdentity | SO(2) generator J on Schwartz space. Needs SchwartzMap API for differential operators. |
| `pphi2_exists` | OS2_WardIdentity | Main existence theorem. Needs continuumLimit + continuumLimit_satisfies_allOS. |
| `pphi2_existence` | Main | Same as above, with SatisfiesFullOS instead of SatisfiesAllOS. |

---

## Priority ordering for filling axioms

### Tier 1: Infrastructure (unlocks further work)

1. **`prokhorov_sequential`** — May become available in Mathlib. Otherwise, axiomatize with a full proof sketch referencing Billingsley.
2. **`transferEigenvalue` + spectral axioms** — Need compact self-adjoint operator spectral theory in Mathlib.
3. **`latticeEmbed` / `latticeEmbedLift`** — Construction of the embedding as a CLM on Schwartz space.

### Tier 2: Core analytic results (the hard axioms)

4. **`nelson_hypercontractive`** — Deep (Gross log-Sobolev). Key engine for all moment bounds.
5. **`second_moment_uniform` + `continuumMeasures_tight`** — Tightness argument. Depends on Nelson.
6. **`spectral_gap_uniform`** — Uniform mass gap. Kato-Rellich perturbation theory.
7. **`ward_identity_lattice` + `anomaly_vanishes`** — Ward identity + power counting for rotation invariance.

### Tier 3: Medium-difficulty proofs

8. Transfer matrix properties (self-adjoint, positive definite, Hilbert-Schmidt, trace class)
9. Reflection positivity on the lattice (action decomposition → perfect square)
10. Clustering from spectral gap (standard spectral decomposition)
11. OS axiom inheritance (mostly soft analysis: limits preserve bounds)

### Tier 4: Easy / straightforward

12. `latticeAction_translation_invariant` — relabeling sums
13. `os1_inheritance` — |cos| ≤ 1
14. `transferKernel_symmetric` — algebra
15. Various measurability and integrability lemmas

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
| `os2_inheritance` | OS2_WardIdentity | E(2) invariance (from translation + rotation) |
| `continuumLimit_satisfies_allOS` | OS2_WardIdentity | All OS axioms (assembly from phases) |
| `pphi2_main` | Main | Main theorem: SatisfiesFullOS (assembly) |

---

## Upstream: gaussian-field axioms and sorries

The gaussian-field library (dependency) has 29 axioms and 14 sorries that
pphi2 relies on. These are organized by priority for pphi2.

### Critical for pphi2 (blocks lattice Gaussian measure)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `spectralCLM` | HeatKernel/Axioms | axiom | Hard | Core: E →L[ℝ] ell2' from singular values. Everything flows through this. |
| `spectralCLM_coord` | HeatKernel/Axioms | axiom | Easy | Coordinate formula. By construction. |
| `spectralCLM_zero` | HeatKernel/Axioms | axiom | Easy | Zero singular values → zero map. |
| `spectralCLM_smul` | HeatKernel/Axioms | axiom | Easy | Scalar compatibility. |
| `finLatticeField_dyninMityaginSpace` | Lattice/FiniteField | 8 sorries | Medium | DyninMityaginSpace instance for finite lattice. Trivial in finite dim but needs careful ℕ-indexed framework handling. |
| `lattice_singular_values_bounded` | Lattice/Covariance | sorry | Easy | σ_m ≤ 1/mass. From eigenvalue lower bound mass² > 0. |
| `finiteLaplacian` linearity | Lattice/Laplacian | 3 sorries | Easy | map_add', map_smul', cont. Finite sums are linear, finite-dim is continuous. |

### Used by pphi2 Normalization (FKG)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `fkg_lattice_gaussian` | Lattice/FKG | axiom | Hard | FKG inequality for Gaussian measure. Harris-Kleitman generalization to continuous spins + log-concave density. |
| `fkg_perturbed` | Lattice/FKG | axiom | Medium | FKG for convexly-perturbed measure. From fkg_lattice_gaussian + Holley criterion. |

### Lattice Laplacian properties

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `finiteLaplacian_selfAdjoint` | Lattice/Laplacian | axiom | Easy | Symmetry: reindex summation. |
| `finiteLaplacian_neg_semidefinite` | Lattice/Laplacian | axiom | Medium | ⟨f, Δf⟩ ≤ 0. Summation by parts. |
| `massOperator_pos_def` | Lattice/Laplacian | axiom | Medium | -Δ + m² > 0. From neg-semidef + m² > 0. |
| `infiniteLaplacian` | Lattice/Laplacian | axiom | Medium | CLM on RapidDecayLattice. Continuity proof needed. |
| `infiniteLaplacian_apply` | Lattice/Laplacian | axiom | Easy | Application formula. By construction. |

### Infinite lattice (not immediately needed by pphi2)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `latticeEnum` | Lattice/RapidDecayLattice | axiom | Hard | ℤ^d ≃ ℕ with polynomial norm growth. Shell enumeration. |
| `latticeEnum_norm_bound` | Lattice/RapidDecayLattice | axiom | Hard | ‖enum⁻¹(m)‖ ≤ C·m^{1/d}. |
| `latticeEnum_index_bound` | Lattice/RapidDecayLattice | axiom | Hard | enum(x) ≤ C·(1+‖x‖)^d. |
| `latticeRapidDecayEquiv` | Lattice/RapidDecayLattice | axiom | Hard | CLE to RapidDecaySeq. Requires enumeration + norm bounds. |
| `latticeCoeffCLM` cont | Lattice/RapidDecayLattice | sorry | Medium | Continuity of evaluation CLM. |

### Heat kernel (cylinder QFT, not used by lattice approach)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `mehlerKernel_eq_series` | HeatKernel/PositionKernel | axiom | Hard | Mehler kernel = Hermite series. |
| `mehlerKernel_summable` | HeatKernel/PositionKernel | axiom | Medium | Summability. |
| `mehlerKernel_pos` | HeatKernel/PositionKernel | axiom | Hard | Strict positivity. |
| `mehlerKernel_reproduces_hermite` | HeatKernel/PositionKernel | axiom | Medium | Reproducing property. |
| `mehlerKernel_semigroup` | HeatKernel/PositionKernel | axiom | Medium | Chapman-Kolmogorov. |
| `circleHeatKernel_*` (7 axioms) | HeatKernel/PositionKernel | axiom | Easy–Medium | Circle heat kernel properties. |
| `cylinderHeatKernel_*` (3 axioms) | HeatKernel/PositionKernel | axiom | Medium | Cylinder = product kernel. |
| `qft_singular_values_bounded` | HeatKernel/Axioms | axiom | Medium | QFT singular values bounded. |
| `heat_singular_values_bounded'` | HeatKernel/Axioms | axiom | Medium | Heat singular values bounded. |

### Other

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `schwartzComplexificationEquiv` | Nuclear/Complexification | sorry | Hard | CLE for complexified Schwartz space. |
| `schwartzPointwiseProduct_apply` | SchwartzNuclear/SchwartzTensorProduct | sorry | Medium | Hermite-Fubini factorization. |

### Summary

| Category | Axioms | Sorries |
|----------|--------|---------|
| Critical for pphi2 lattice measure | 4 | 12 |
| FKG (used by pphi2 Normalization) | 2 | 0 |
| Lattice Laplacian | 5 | 0 |
| Infinite lattice (future) | 4 | 1 |
| Heat kernel / cylinder (not used) | 16 | 0 |
| Other | 0 | 2 |
| **Total** | **29** | **14** (unique sorry sites) |
