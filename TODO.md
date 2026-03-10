# pphi2 TODO

## Infrastructure to eliminate axioms

### 1. Lattice reflection positivity (eliminates 2 axioms)

Target axioms:
- `gaussian_density_rp` (OSProofs/OS3_RP_Lattice) — Medium
- `torusLattice_rp` (TorusContinuumLimit/TorusOSAxioms) — Medium

`lattice_rp` is now **proved** from `gaussian_rp_with_boundary_weight`,
which itself is **proved** from `gaussian_density_rp` via the
`evalMapMeasurableEquiv` density bridge (no measurability on integrands).
The remaining axiom is the density-level RP:
∫ G(φ)·G(Θφ)·w(φ)·ρ(φ) dφ ≥ 0, which follows from the Gaussian Markov
property (conditional independence of positive/negative time fields given
boundary) directly on Lebesgue integrals.

### 2. ~~Transfer operator compactness~~ (DONE — proved `transferOperator_isCompact`)

`transferOperator_isCompact` is now a **theorem** proved from:
- `hilbert_schmidt_isCompact` (new axiom): general HS → compact for M_w ∘ Conv_g ∘ M_w
- `transferWeight_memLp_two` (proved): w ∈ L² from Gaussian decay
- `transferGaussian_norm_le_one` (proved): ‖G‖ ≤ 1

Remaining: prove `hilbert_schmidt_isCompact` (Reed-Simon I, Thm VI.23).
Strategy: expand L² kernel in ONB, finite-rank approximation, use
`isCompactOperator_of_tendsto` from Mathlib.

### 3. Tightness via Mitoma criterion (eliminates ~3 axioms)

Target axioms:
- `continuumMeasures_tight` (ContinuumLimit/Tightness) — Hard
- `gaussianContinuumMeasures_tight` (GaussianContinuumLimit/GaussianTightness) — Medium
- `torusContinuumMeasures_tight` (TorusContinuumLimit/TorusTightness) — Medium

Mitoma's theorem: tightness of measures on E' (nuclear Frechet dual)
reduces to tightness of 1D projections omega |-> omega(f) for each f in E.
Combined with Chebyshev + uniform second moments (proved for Gaussian case).

What to build:
- Mitoma's theorem (not in Mathlib)
- Or: direct Prokhorov on Polish torus (already done for torus case)

### 4. Gaussian convolution strict positive definiteness (eliminates 1 axiom)

Target axiom:
- `inner_convCLM_pos_of_fourier_pos` (TransferMatrix/GaussianFourier) — Medium

<f, Conv_G f>_{L^2} = integral |f_hat(k)|^2 G_hat(k) dk > 0 for f != 0.
Bochner's theorem + Plancherel. G_hat(k) = exp(-||k||^2/2) > 0.

What to build:
- Plancherel theorem connection: <f, g*f> = integral |f_hat|^2 g_hat
- Or: use Mathlib's Fourier analysis on L^2(R^n)

### 5. Exponential moment / stability bounds (eliminates ~3 hard axioms)

Target axioms:
- `exponential_moment_bound` (ContinuumLimit/Hypercontractivity) — Hard
- `continuum_exponential_moments` (OSProofs/OS2_WardIdentity) — Hard
- `continuum_exponential_clustering` (OSProofs/OS2_WardIdentity) — Hard

These are the deep analytic core of the construction:
- Stability of exp(-V) under the Gaussian measure (cluster expansions,
  Glimm-Jaffe Thm 8.6.1)
- Fernique + Nelson estimates transferred to the continuum limit
- Spectral gap -> exponential clustering in the continuum

### 6. Spectral gap uniform in lattice spacing (eliminates 2 hard axioms)

Target axioms:
- `spectral_gap_uniform` (TransferMatrix/SpectralGap) — Hard
- `spectral_gap_lower_bound` (TransferMatrix/SpectralGap) — Hard

The physical mass gap m_phys >= c * m_bare, bounded below uniformly in the
lattice spacing a. Key input: the interaction is a bounded perturbation of
the free field (Kato-Rellich), and the free mass gap is m > 0.

### 7. OS axiom inheritance (eliminates ~3 axioms)

Target axioms:
- `os0_inheritance` (ContinuumLimit/AxiomInheritance) — Medium
- `os3_inheritance` (ContinuumLimit/AxiomInheritance) — Medium
- `os4_inheritance` (ContinuumLimit/AxiomInheritance) — Med/Hard

These transfer OS axioms from lattice to continuum limit:
- OS0: uniform moment bounds + pointwise convergence -> all moments finite
- OS3: lattice RP + weak limit closure (rp_closed_under_weak_limit proved)
- OS4: uniform spectral gap + weak convergence -> clustering

### 8. Ward identity and rotation invariance (eliminates ~3 axioms)

Target axioms:
- `latticeMeasure_translation_invariant` (OSProofs/OS2_WardIdentity) — Medium
- `anomaly_bound_from_superrenormalizability` (OSProofs/OS2_WardIdentity) — Hard
- `rotation_invariance_continuum` (OSProofs/OS2_WardIdentity) — Hard

Translation invariance: relabeling argument on the lattice.
Rotation: Ward identity + super-renormalizability (scaling dimension 4 > d=2)
gives anomaly = O(a^2) -> 0 in continuum limit.

### 9. Gaussian continuum limit sorries (provable, not axioms)

Target sorries in GaussianContinuumLimit/:
- `embeddedTwoPoint_eq_latticeSum` — Fubini + Gaussian integration
- `embeddedTwoPoint_uniform_bound` — eigenvalue bound + Riemann sum
- `continuumGreenBilinear_pos` — Fourier injectivity on Schwartz space
- `propagator_convergence` — dominated convergence + Schwartz decay

These are Medium difficulty and don't need new infrastructure.
