# pphi2 Axiom Proof Plans

**Updated**: 2026-04-03
**Status note**: exact axiom counts move quickly; see `status.md` for the current inventory.

See [axiom_audit.md](axiom_audit.md) for correctness ratings and verification
status. See [mathlib_candidates.md](mathlib_candidates.md) for results
suitable for Mathlib contribution.

---

## Recommended Attack Order

1. `transferOperator_isCompact` — Hilbert-Schmidt, unlocks spectral theory
2. `gaussian_density_rp` — Gaussian Markov property, fills RP chain
3. Torus tier: `torusContinuumMeasures_tight`, `torusLimit_covariance_eq`,
   `gaussian_measure_unique_of_covariance`, `torusLattice_rp`
4. OS inheritance: `os3_inheritance`, `os0_inheritance`
5. Hard analysis: `exponential_moment_bound` → `interacting_moment_bound` →
   `second_moment_uniform` → `continuumMeasures_tight`
6. Spectral gap: `spectral_gap_uniform` → clustering chain
7. Ward identity: `anomaly_bound` → `rotation_invariance_continuum`
8. Bridge: last priority, requires both approaches complete

## Dependency Graph (Critical Paths)

```
exponential_moment_bound ──→ interacting_moment_bound ──→ second_moment_uniform
                                                      ──→ continuum_exponential_moments
                                                      ──→ torus_interacting_tightness

spectral_gap_uniform ──→ spectral_gap_lower_bound
                     ──→ two_point_clustering ──→ general_clustering
                     ──→ continuum_exponential_clustering ──→ os4_inheritance

transferOperator_isCompact ──→ (unlocks spectral theory for spectral_gap proofs)

gaussian_density_rp ──→ os3_inheritance (via lattice_rp chain)

anomaly_bound ──→ rotation_invariance_continuum ──→ os2

fourierTransform_lp_eq_fourierIntegral ──→ fourier_representation_convolution
                                     ──→ (proved; Fourier chain axiom-free)
```

---

## Tier 1: Moderate — Provable Now

### 1. `transferOperator_isCompact` (L2Operator.lean)

**Difficulty**: Medium
**Statement**: Transfer operator T is compact on L^2.
**Plan**: Hilbert-Schmidt strategy. Kernel K(ψ,ψ') = w(ψ)G(ψ-ψ')w(ψ')
where w = exp(-½aV) ∈ L^2 (InteractionPolynomial enforces this) and
G = exp(-½‖·‖²) is Gaussian. Show ∫∫ K² < ∞ via product factorization.
**Prereqs**: `transferWeight_bound` (proved), `transferGaussian_memLp` (proved),
`HilbertSchmidt.isCompact` (Mathlib).
**Blocker**: Need to verify `IsHilbertSchmidt` API in Mathlib is sufficient.

---

### 2. Fourier representation bridge (GaussianFourier.lean) — proved

**Difficulty**: Medium
**Former axiom**: `fourierTransform_lp_eq_fourierIntegral`, the textbook
bridge identifying the Lp Fourier-transform representative with the Fourier
integral for functions in `L¹ ∩ L²`.
**Downstream theorem**: `fourier_representation_convolution`,
`⟨f, g⋆f⟩ = ∫ Re(ĝ)·|f̂|²`, is now a private theorem built from that bridge
plus the Schwartz/density infrastructure.
**Proof**: The bridge is proved via `Lp.fourier_toTemperedDistribution_eq`,
`Lp.toTemperedDistribution_apply`,
`VectorFourier.integral_bilin_fourierIntegral_eq_flip`, real inner-product
symmetry for the flipped kernel, and `ae_eq_of_integral_contDiff_smul_eq`.
**Status**: Closed in `Pphi2/TransferMatrix/GaussianFourier.lean`.

---

### 3. `gaussian_density_rp` (OS3_RP_Lattice.lean)

**Difficulty**: Medium
**Statement**: ∫ G(φ)·G(Θφ)·w(φ)·ρ(φ) dφ ≥ 0 (core Gaussian RP at density level).
**Plan**: Gaussian Markov property — conditional on boundary, upper and lower
half-planes independent. Factorize G(φ)·G(Θφ) = |G₊(φ)|² where G₊ uses only
positive-time data. Then ∫ |G₊|²·w·ρ ≥ 0.
**Prereqs**: Gaussian conditional independence (needs formalization).
**Reference**: Glimm-Jaffe Ch. 6.1.

---

### 4. `torusContinuumMeasures_tight` (TorusTightness.lean)

**Difficulty**: Medium
**Statement**: {ν_N} tight on torus configuration space.
**Plan**: Mitoma criterion — tight iff ∀ test f, {μ_N ∘ ev_f⁻¹} tight on ℝ.
Use Chebyshev from `torus_second_moment_uniform` (proved): P(|X|>R) ≤ C/R².
**Prereqs**: `torus_second_moment_uniform` (proved), Mitoma criterion.

---

### 5. `torusLimit_covariance_eq` (TorusGaussianLimit.lean)

**Difficulty**: Medium
**Statement**: Weak convergence transfers second moments.
**Plan**: Vitali convergence theorem. Uniform integrability from
`torusEmbeddedTwoPoint_uniform_bound` (proved).
**Prereqs**: `torusEmbeddedTwoPoint_uniform_bound` (proved),
`MeasureTheory.UnifIntegrable` (Mathlib).

---

### 6. `gaussian_measure_unique_of_covariance` (TorusGaussianLimit.lean)

**Difficulty**: Medium
**Statement**: Gaussian on nuclear space determined by covariance.
**Plan**: Bochner-Minlos: CF = exp(-½Q(f)) determines μ, and Q determined by
covariance. Two Gaussians with same covariance → same CF → same measure.
**Prereqs**: `Measure.ext_of_charFun` (Mathlib), Gaussian CF formula.

---

### 7. `torusGeneratingFunctionalℂ_analyticOnNhd` (TorusOSAxioms.lean)

**Difficulty**: Medium
**Statement**: z ↦ ∫ exp(i⟨ω, Σ zⱼJⱼ⟩) dμ is analytic on ℂⁿ.
**Plan**: Gaussian → all moments finite. Dominated convergence differentiating
under integral sign. Or: Morera's theorem.
**Prereqs**: Gaussian exponential moments, Morera's theorem (Mathlib).

---

### 8. `torusLattice_rp` (TorusOSAxioms.lean)

**Difficulty**: Medium
**Statement**: Σᵢⱼ cᵢcⱼ Re(Z_N[fᵢ-Θfⱼ]) ≥ 0 for positive-time test functions.
**Plan**: Expand cos(⟨φ,fᵢ-Θfⱼ⟩) using cos(A-B). Apply `rp_matrix_trig_identity`
(proved in FunctionalAnalysis.lean) to decompose as sum of squares. Each square
nonneg under Gaussian RP.
**Prereqs**: `rp_matrix_trig_identity` (proved), Gaussian RP on torus.

---

### 9. `analyticOn_generatingFunctionalC` (OS2_WardIdentity.lean)

**Difficulty**: Medium
**Statement**: Complex generating functional is jointly analytic on ℂⁿ.
**Plan**: Same pattern as `torusGeneratingFunctionalℂ_analyticOnNhd`.
Exponential moments → dominated convergence → power series → analytic.
**Prereqs**: `continuum_exponential_moments` (axiom, Tier 2).

---

### 10. `exponential_moment_schwartz_bound` (OS2_WardIdentity.lean)

**Difficulty**: Medium
**Statement**: ∫ exp(c|ω(f)|) dμ ≤ exp(C·p(f)^q).
**Plan**: Gaussian domination. Gaussian ω(f) ~ N(0,σ²) where σ² = ⟨f,Cf⟩
= ‖f‖²_{H⁻¹}. Sobolev: ‖f‖_{H⁻¹} bounded by Schwartz seminorms.
**Prereqs**: `continuum_exponential_moments` (axiom), Schwartz-Sobolev comparison.

---

### 11. `os0_inheritance` (AxiomInheritance.lean)

**Difficulty**: Medium
**Statement**: OS0 (analyticity/moment bounds) transfers to limit.
**Plan**: Uniform moment bounds + truncation + weak convergence + Fatou.
**Prereqs**: Uniform exponential moments, weak convergence.
**Note**: Circular import issue — can't use `continuum_exponential_moments`
directly. May need restructuring.

---

### 12. `os3_inheritance` (AxiomInheritance.lean)

**Difficulty**: Medium
**Statement**: RP transfers through weak limits.
**Plan**: `lattice_rp_matrix` gives RP for each lattice measure.
`rp_closed_under_weak_limit` (proved) shows RP persists under weak limits.
Connect via `IsPphi2Limit`.
**Prereqs**: `lattice_rp_matrix` (proved modulo `gaussian_density_rp`),
`rp_closed_under_weak_limit` (proved).

---

### 13. `torus_interacting_tightness` (TorusInteractingLimit.lean)

**Difficulty**: Medium
**Statement**: Interacting measures tight on torus (Cauchy-Schwarz transfer).
**Plan**: ∫ |Φ(f)|² dν ≤ √(∫ e^{-2V} dμ_GFF) · √(∫ |Φ(f)|⁴ dμ_GFF).
RHS: Nelson hypercontractivity for Gaussian.
**Prereqs**: `torusContinuumMeasures_tight` (axiom #4), hypercontractivity.

---

## Tier 2: Hard — Deep Analytic Results

### 14. `latticeGreenBilinear_basis_tendsto_continuum` (PropagatorConvergence.lean)

**Difficulty**: Hard
**Statement**: Spectral lattice Green bilinear on Dynin-Mityagin basis pairs
converges to `continuumGreenBilinear` on ℝ^d.
**Plan**: Dominated convergence + Schwartz decay on the basis, then extend to all
test functions by bilinear continuity. `propagator_convergence` is now a theorem
from `embeddedTwoPoint_eq_latticeGreenBilinear`, so the remaining debt is
exactly this basis-level spectral convergence statement. Model:
`riemann_sum_periodic_tendsto` (proved in gf).
**Prereqs**: Schwartz decay, lattice eigenvalue convergence (proved in gf).
**Detailed discharge plan**: [`plans/lattice-green-flat-Rd-discharge-plan.md`](../plans/lattice-green-flat-Rd-discharge-plan.md) — Strategy A (factor through torus + IR limit, ~3 weeks). **Caveat**: NOT on the T² continuum-limit critical path; only needed if the project pushes to flat-ℝ² S'(ℝ²) Wightman directly.

---

### 15. ~~`gaussianContinuumMeasures_tight`~~ (GaussianTightness.lean)

**Status**: **PROVED for `d > 0`**
**Plan used**: `configuration_tight_of_uniform_second_moments` +
`gaussian_second_moment_uniform`.
**Residual note**: The excluded `d = 0` case is a separate nuclear-space instance gap.

---

### 16. ~~`gaussianLimit_isGaussian`~~ (GaussianLimit.lean)

**Status**: **PROVED**
**Plan used**: Reduction to 1D evaluation marginals and
`weakLimit_centered_gaussianReal`, then reconstruction of the characteristic
functional.

---

### 17. `exponential_moment_bound` (Hypercontractivity.lean)

**Difficulty**: Hard
**Statement**: ∫ exp(-2V_a) dμ_GFF ≤ K uniformly in a.
**Plan**: Deep stability estimate. Cluster expansion (Glimm-Jaffe Thm 8.6.1)
or Nelson's chessboard estimate via Wick ordering cancellations.
**Prereqs**: Wick ordering (proved), Gaussian hypercontractivity (proved).
**Note**: Key "hard analysis" axiom — makes everything downstream work.

---

### 18. `interacting_moment_bound` (Hypercontractivity.lean)

**Difficulty**: Medium (conditional on #17)
**Statement**: Interacting L^{pn} moments bounded by Gaussian L^{2n} moments.
**Plan**: Cauchy-Schwarz density transfer.
**Prereqs**: `exponential_moment_bound` (#17).

---

### 19. `second_moment_uniform` (Tightness.lean)

**Difficulty**: Hard
**Statement**: ∫ Φ_a(f)² dν_a ≤ C(f) uniformly in a.
**Plan**: Nelson/Froehlich Gaussian domination. Chain from #17 → #18 → here.
**Prereqs**: `interacting_moment_bound` (#18).

---

### 20. `moment_equicontinuity` (Tightness.lean)

**Difficulty**: Hard
**Statement**: Equicontinuity of moments in f (Schwartz seminorm control).
**Plan**: E[|Φ_a(f-g)|²] ≤ ⟨f-g, C_{0,a}(f-g)⟩. Sobolev regularity of
C_{0,a} = (-Δ_a + m²)⁻¹ gives Schwartz seminorm bound.
**Prereqs**: Sobolev spaces, lattice covariance operator.

---

### 21. `continuumMeasures_tight` (Tightness.lean)

**Difficulty**: Hard
**Statement**: Tightness via Mitoma for interacting measures on S'(ℝ²).
**Plan**: Combines `second_moment_uniform` + `moment_equicontinuity` +
Mitoma criterion.
**Prereqs**: #19, #20.

---

### 22. `spectral_gap_uniform` (SpectralGap.lean)

**Difficulty**: Very Hard
**Statement**: ∃ m₀ > 0, gap(a) ≥ m₀ ∀ a ≤ a₀.
**Plan**: Central result of Glimm-Jaffe-Spencer. Interaction is bounded
Kato-Rellich perturbation of free field with gap m > 0. In d=2 with m > 0,
no phase transition.
**Prereqs**: `transferOperator_isCompact` (#1), Kato-Rellich perturbation theory.
**Note**: Deepest result in the construction.

---

### 23. `spectral_gap_lower_bound` (SpectralGap.lean)

**Difficulty**: Very Hard
**Statement**: gap ≥ c · m_bare.
**Plan**: Quantitative refinement of #22. Same proof.
**Prereqs**: `spectral_gap_uniform` (#22).

---

### 24. `two_point_clustering_from_spectral_gap` (OS4_MassGap.lean)

**Difficulty**: Hard
**Statement**: Connected 2-point function decays exponentially in the **cyclic torus
time separation**.
**Plan**: Spectral decomposition: ⟨f, T^n g⟩ = λ₀ⁿ⟨f,e₀⟩⟨e₀,g⟩ + O(λ₁ⁿ).
On a periodic time circle, combine the forward and backward winding contributions
into a bound in `min(n, N-n)`. Since λ₁/λ₀ = exp(-gap), get exponential decay
in the cyclic distance.
**Prereqs**: `spectral_gap_uniform` (#22), spectral decomposition (proved).

---

### 25. `general_clustering_from_spectral_gap` (OS4_MassGap.lean)

**Difficulty**: Hard
**Statement**: Bounded-observable clustering from spectral gap, with decay measured
in the cyclic torus time separation.
**Plan**: Schwarz inequality / transfer-matrix extension of #24, preserving the
cyclic-distance geometry of the periodic time direction.
**Prereqs**: `two_point_clustering_from_spectral_gap` (#24).

---

### 26. `anomaly_bound_from_superrenormalizability` (OS2_WardIdentity.lean)

**Difficulty**: Hard
**Statement**: ‖Z_a[R·f] - Z_a[f]‖ ≤ C·a²·(1+|log a|)^p.
**Plan**: Super-renormalizability: scaling dimension 4 > d=2 gives a²
suppression. `anomaly_scaling_dimension` (proved) provides local bound.
No log corrections in d=2.
**Prereqs**: `anomaly_scaling_dimension` (proved), Fourier analysis.

---

### 27. `rotation_invariance_continuum` (OS2_WardIdentity.lean)

**Difficulty**: Hard
**Statement**: Z[R·f] = Z[f] for R ∈ O(2).
**Plan**: From #26: ‖Z_a[R·f] - Z_a[f]‖ → 0 as a→0. Plus weak convergence.
**Prereqs**: `anomaly_bound_from_superrenormalizability` (#26).

---

## Tier 3: Hard — Infrastructure Gaps / Deep Results (10 axioms)

### 28. `continuum_exponential_moments` (OS2_WardIdentity.lean)

**Difficulty**: Hard
**Statement**: ∀ c > 0, Integrable (exp(c·|ω f|)) μ.
**Plan**: Nelson hypercontractive estimate → uniform integrability → Vitali.
**Prereqs**: `interacting_moment_bound` (#18).

---

### 29. `continuum_exponential_clustering` (OS2_WardIdentity.lean)

**Difficulty**: Hard
**Statement**: ‖Z[f+τ_a g] - Z[f]Z[g]‖ ≤ C·exp(-m₀·‖a‖).
**Plan**: From `spectral_gap_uniform` via transfer matrix spectral decomposition.
**Prereqs**: `spectral_gap_uniform` (#22), `two_point_clustering` (#24).

---

### 30. `os4_inheritance` (AxiomInheritance.lean)

**Difficulty**: Med/Hard
**Statement**: Exponential clustering survives weak limits.
**Plan**: Uniform bound C·exp(-m₀R) passes through weak convergence.
**Prereqs**: `continuum_exponential_clustering` (#29).

---

### 31. `pphi2_measure_neg_invariant` (OS2_WardIdentity.lean)

**Difficulty**: Medium
**Statement**: Z₂ symmetry: map Neg.neg μ = μ.
**Plan**: Even P + GFF symmetry + weak limit closure.
**Prereqs**: Even polynomial (proved), Gaussian Z₂ symmetry.

---

### 32. `prokhorov_configuration_sequential` (Convergence.lean)

**Difficulty**: Infrastructure
**Statement**: Sequential Prokhorov on S'(ℝ²).
**Plan**: S'(ℝ²) is Polish (Gelfand-Vilenkin).
**Blocker**: Mathlib lacks nuclear space API.
**Alternative**: Bypass via torus path (already done for Gaussian).

---

### 33. `schwinger_n_convergence` (Convergence.lean)

**Difficulty**: Hard
**Statement**: n-point Schwinger functions converge along subsequence.
**Plan**: Diagonal subsequence extraction from tightness.
**Prereqs**: `continuumMeasures_tight` (#21).

---

### 34. `continuumLimit_nontrivial` (Convergence.lean)

**Difficulty**: Hard
**Statement**: ∫(ωf)² > 0 from free field lower bound.
**Plan**: Griffiths/FKG correlation inequalities.
**Prereqs**: FKG inequality (proved in gf).

---

### 35. `continuumLimit_nonGaussian` (Convergence.lean)

**Difficulty**: Hard
**Statement**: Connected 4-point function ≠ 0.
**Plan**: Perturbation theory O(λ) contribution.
**Prereqs**: Cluster expansion.

---

### 36. `pphi2_nontriviality` (Main.lean)

**Difficulty**: Hard
**Statement**: ∫ (ω f)² dμ > 0 for all f ≠ 0.
**Plan**: Same as #34.

---

### 37. `pphi2_limit_exists` (Convergence.lean)

**Difficulty**: Medium (meta-theorem)
**Statement**: ∃ μ, IsPphi2Limit μ P mass.
**Plan**: Prokhorov + tightness + diagonal argument.
**Prereqs**: `continuumMeasures_tight` (#21), inheritance axioms.

---

## Tier 4: Very Hard / Bridge (8 axioms)

### 38. `torusPositiveTimeSubmodule` (TorusOSAxioms.lean)

**Difficulty**: Infrastructure
**Statement**: Submodule of torus test functions with time support in (0,L/2).
**Plan**: Nuclear tensor product lacks pointwise evaluation, so axiomatized.
Should be converted to def once nuclear space API improves.

---

### 39. `lattice_rp_matrix` (OS3_RP_Lattice.lean)

**Difficulty**: Medium (partially done)
**Statement**: RP in matrix form on lattice.
**Current state**: `lattice_rp_matrix_reduction` proved; remaining gap is
`h_expand` (trig expansion identity).
**Prereqs**: `gaussian_density_rp` (#3).

---

### 40. `schwinger_agreement` (Bridge.lean)

**Difficulty**: Very Hard
**Statement**: Schwinger function agreement at weak coupling.
**Plan**: Cluster expansion (Guerra-Rosen-Simon 1975).
**Note**: Research-level formalization.

---

### 41. `same_continuum_measure` (Bridge.lean)

**Difficulty**: Very Hard (conditional on #40)
**Statement**: pphi2 and Phi4 constructions agree at weak coupling.
**Plan**: `schwinger_agreement` + `measure_determined_by_schwinger`.
**Prereqs**: #40, `measure_determined_by_schwinger`.

---

### 42. `os2_from_phi4` (Bridge.lean)

**Difficulty**: Medium (given Phi4)
**Statement**: OS2 for Phi4 continuum limit.
**Plan**: GFF is E(2)-invariant; regularization preserves invariance.
**Prereqs**: `IsPhi4ContinuumLimit` hypothesis.

---

### 43. `measure_determined_by_schwinger` (Bridge.lean)

**Difficulty**: Medium
**Statement**: Moment determinacy on S'(ℝ²) with exponential moments.
**Plan**: Characteristic function analytic in strip → determined by moments →
Lévy inversion → unique measure. Carleman's condition.
**Prereqs**: Exponential moments, Carleman's condition (Mathlib gap).

---

### 44. `wickConstant_log_divergence` (Counterterm.lean)

**Difficulty**: Medium
**Statement**: |c_a - (2π)⁻¹ log(1/a)| ≤ C.
**Plan**: Momentum-space computation. Euler-Maclaurin or direct Riemann sum.
c_a = G_a(0,0) = (1/|Λ*|) Σ_k (4sin²(ak/2)/a² + m²)⁻¹.
**Prereqs**: Euler-Maclaurin formula.

---

### 45. `schwartz_riemann_sum_bound` (PropagatorConvergence.lean) — private

**Difficulty**: Medium
**Statement**: Schwartz-space Riemann sum error bound.
**Plan**: Standard Schwartz decay + lattice spacing error.
**Prereqs**: Schwartz seminorm estimates.

---

## Summary Table

| Tier | Count | Key Axioms |
|------|-------|-----------|
| 1: Moderate | 13 | `transferOperator_isCompact`, `fourierTransform_lp_eq_fourierIntegral`, `gaussian_density_rp`, torus infrastructure, OS inheritance |
| 2: Hard | 14 | `spectral_gap_uniform`, `exponential_moment_bound`, Ward identity, tightness chain |
| 3: Infra/Deep | 10 | `prokhorov_configuration_sequential`, nontriviality, clustering |
| 4: Very Hard | 8 | Bridge axioms, `schwinger_agreement`, infrastructure |
| **Total** | **41** (+ 4 private/removed) | |

## Proved Axioms (Historical)

See [axiom_audit.md](axiom_audit.md) §Proved Axioms for the complete list of
axioms converted to theorems, with dates and methods.
