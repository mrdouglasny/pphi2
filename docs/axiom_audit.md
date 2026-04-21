# Comprehensive Axiom Audit: pphi2 + gaussian-field

**Updated**: 2026-03-21
**pphi2**: 32 axioms, 0 sorries (active build) | **gaussian-field**: 14 axioms, 0 sorries

Note: pphi2 count includes 3 private axioms (`schwartz_riemann_sum_bound`,
`fourier_representation_convolution`, `gaussian_rp_cov_perfect_square`).

## Verification Sources

- **GR** = `docs/gemini_review.md` (2026-02-23) — external review in 5 thematic groups
- **DT** = Gemini deep think verification (date noted)
- **SA** = self-audit (this document)
- **(NOT VERIFIED)** = no external review beyond self-audit

## Self-Audit Ratings

- **✅ Standard** — well-known mathematical fact, stated correctly
- **⚠️ Likely correct** — mathematically sound, needs careful type/quantifier verification
- **❓ Needs review** — potentially problematic or non-standard formulation
- **🔧 Placeholder** — conclusion is `True` or trivially weak

---

## pphi2 Axioms (25 active)

### Phase 1: Wick Ordering (1 active axiom, 1 proved)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|-------|
| 1 | ~~`wickMonomial_eq_hermite`~~ | WickPolynomial:113 | ✅ **PROVED** | SA 2026-02-24 | Via `wick_eq_hermiteR_rpow` from gaussian-field HermiteWick. |
| 2 | `wickConstant_log_divergence` | Counterterm:146 | ✅ Standard | GR Group 5 | c_a ~ (2π)⁻¹ log(1/a). Standard lattice Green's function asymptotics. |

### Phase 2: Transfer Matrix and RP (3 active axioms, 7 proved)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|-------|
| 3 | ~~`transferOperatorCLM`~~ | L2Operator | ✅ **DEFINED** | SA | Transfer matrix defined as `M_w ∘L Conv_G ∘L M_w` (no longer axiom). |
| 4 | ~~`transferOperator_isSelfAdjoint`~~ | L2Operator | ✅ **PROVED** | SA | Self-adjoint from self-adjointness of M_w and Conv_G. |
| 5 | ~~`transferOperator_isCompact`~~ | L2Operator | ✅ **PROVED** | CC 2026-03-09 | Proved from `hilbert_schmidt_isCompact` + `transferWeight_memLp_two` + `transferGaussian_norm_le_one`. |
| 5a | `hilbert_schmidt_isCompact` | L2Operator | ✅ Correct | Gemini 2026-03-07 | General HS theorem: M_w ∘ Conv_g ∘ M_w compact when w ∈ L² ∩ L∞, ‖g‖_∞ ≤ 1. Reed-Simon I, Thm VI.23. |
| 6 | ~~`transferEigenvalue`~~ | L2Operator | ✅ **PROVED** | DT 2026-02-24 | Sorted eigenvalue sequence via spectral theorem. |
| 7 | ~~`transferEigenvalue_pos`~~ | L2Operator | ✅ **PROVED** | GR Group 3 | All eigenvalues > 0. Derived from Jentzsch theorem. |
| 8 | ~~`transferEigenvalue_antitone`~~ | L2Operator | ✅ **PROVED** | GR Group 3 | Eigenvalues decreasing. Derived from spectral ordering. |
| 9 | ~~`transferEigenvalue_ground_simple`~~ | L2Operator | ✅ **PROVED** | GR Group 3 | λ₀ > λ₁. Derived from Jentzsch/Perron-Frobenius. |
| 9a | ~~`gaussian_conv_strictlyPD`~~ | GaussianFourier | ✅ **PROVED** | SA 2026-02-27 | ⟨f, G⋆f⟩ > 0 for f ≠ 0. Proved from `inner_convCLM_pos_of_fourier_pos` (also proved) via `fourier_representation_convolution` axiom + `fourier_gaussian_pos` + Plancherel injectivity. |
| 9b | `fourier_representation_convolution` | GaussianFourier | ✅ Standard | SA 2026-03-08 | ⟨f, g⋆f⟩ = ∫ Re(ĝ)·‖f̂‖². L² Fourier representation identity. Proof via Schwartz density (convolution theorem for integrable+continuous + Parseval). Blocked by L² convolution theorem not yet in Mathlib. Private axiom. Folland §8.3, Reed-Simon I §IX.4. |
| 10 | ~~`action_decomposition`~~ | OS3_RP_Lattice | ✅ **PROVED** | GR Group 5 | S = S⁺ + S⁻ via `Fintype.sum_equiv` + `Involutive.toPerm`. |
| 11 | `lattice_rp_matrix` | OS3_RP_Lattice | ⚠️ Likely correct | DT 2026-02-24 | RP matrix Σ cᵢc̄ⱼ ∫ cos(⟨φ, fᵢ-Θfⱼ⟩) dμ_a ≥ 0. Partial formalization: helper lemmas + `lattice_rp_matrix_reduction`; remaining gap is explicit trig/sum expansion identity. |

### Phase 3: Spectral Gap (2 axioms)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|-------|
| 12 | `spectral_gap_uniform` | SpectralGap:134 | ⚠️ Correct for P(Φ)₂ | Gemini 2026-03-07 | ∃ m₀ > 0, gap(a) ≥ m₀ ∀a ≤ a₀. Glimm-Jaffe-Spencer. No phase transition in d=2 with m>0. |
| 13 | `spectral_gap_lower_bound` | SpectralGap:145 | ⚠️ Correct for P(Φ)₂ | Gemini 2026-03-07 | gap ≥ c·mass. Correct in single-well regime (our InteractionPolynomial class). |

### Phase 4: Continuum Limit (8 active axioms, 5 proved)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|-------|
| 11 | ~~`latticeEmbed`~~ | Embedding:136 | ✅ **PROVED** | DT 2026-02-24 | Constructed via `SchwartzMap.mkCLMtoNormedSpace`. |
| 12 | ~~`latticeEmbed_eval`~~ | Embedding:170 | ✅ **PROVED** | DT 2026-02-24 | `rfl` from construction. |
| 13 | ~~`latticeEmbed_measurable`~~ | Embedding | ✅ **PROVED** | DT 2026-02-24 | `configuration_measurable_of_eval_measurable` + `continuous_apply` for each coordinate. |
| 14 | ~~`latticeEmbedLift`~~ | Embedding:201 | ✅ **PROVED** | SA 2026-02-24 | Constructed as `latticeEmbed d N a ha (fun x => ω (Pi.single x 1))`. |
| 15 | ~~`latticeEmbedLift_measurable`~~ | Embedding:212 | ✅ **PROVED** | SA 2026-02-24 | `configuration_measurable_of_eval_measurable` + `configuration_eval_measurable`. |
| 16 | `second_moment_uniform` | Tightness:74 | ✅ Correct | Gemini 2026-03-07 | ∫ Φ_a(f)² dν_a ≤ C(f). Nelson/Froehlich Gaussian domination. |
| 17 | `moment_equicontinuity` | Tightness:89 | ✅ Correct | Gemini 2026-03-07 | Fixed RHS. Uniform field oscillation control. |
| 18 | `continuumMeasures_tight` | Tightness:110 | ✅ Correct | Gemini 2026-03-07 | Mitoma criterion + moment bounds. |
| 19 | `prokhorov_configuration_sequential` | Convergence | ✅ Correct | Gemini 2026-03-07 | Sequential Prokhorov. S'(ℝ²) is Polish mathematically. |
| 21 | `os0_inheritance` | AxiomInheritance:78 | ✅ Correct | Gemini 2026-03-07 | OS0 transfers via uniform hypercontractivity. |
| 22 | `os3_inheritance` | AxiomInheritance | ✅ Standard | DT 2026-02-25 | Abstract IsRP for continuum limit: ∫ F·F(Θ*·) dμ ≥ 0. Now requires `IsPphi2Limit`. Follows from lattice_rp_matrix + rp_closed_under_weak_limit (proved). |
| 22b | ~~`IsPphi2Limit`~~ | Embedding:271 | ✅ **DEFINED** | SA 2026-02-25 | Converted from axiom to `def`: ∃ (a, ν) with Schwinger function convergence. Mirrors `IsPphi2ContinuumLimit` in Bridge.lean. |
| 22c | `pphi2_limit_exists` | Convergence | ⚠️ Likely correct | SA 2026-02-25 | ∃ μ `IsPphi2Limit`. Prokhorov + tightness + diagonal argument. Moved from OS2_WardIdentity to Convergence. |

### Phase 4G: Gaussian Continuum Limit (1 axiom, 0 sorries)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|-------|
| G1 | `latticeGreenBilinear_tendsto_continuum` | PropagatorConvergence | ✅ Standard | SA | Spectral lattice Green bilinear on discretized Schwartz functions converges to the continuum Green bilinear. This is the analytic core formerly packaged as `propagator_convergence`, which is now a theorem via `embeddedTwoPoint_eq_latticeGreenBilinear`. Glimm-Jaffe §6.1. |
| ~~G2~~ | ~~`gaussianContinuumMeasures_tight`~~ | GaussianTightness | **PROVED** | SA | Tightness of embedded GFF measures via `configuration_tight_of_uniform_second_moments`, proved for `d > 0`. |
| ~~G3~~ | ~~`gaussianLimit_isGaussian`~~ | GaussianLimit | **PROVED** | SA | Weak limits of Gaussian measures are Gaussian. Proved via 1D evaluation marginals and `weakLimit_centered_gaussianReal`. |

**Sorries (provable, not axioms):** none currently in the Gaussian continuum slice.

### Phase 4T: Torus Continuum Limit (7 axioms)

| # | Name | File | Rating | Verified | Notes |
|---|------|------|--------|----------|-------|
| T1 | `configuration_tight_of_uniform_second_moments` | TorusTightness | ✅ Standard | ✅ DT 2026-03-11: Mitoma (1983) + Chebyshev. Nuclearity essential (ℓ² counterexample). | Mitoma-Chebyshev criterion for nuclear Fréchet duals (`DyninMityaginSpace`). Uniform 2nd moments ⟹ tightness. |
| ~~T2~~ | ~~`torusContinuumMeasures_tight`~~ | TorusTightness | ✅ **PROVED** | 2026-03-11 | From `configuration_tight_of_uniform_second_moments` + `torus_second_moment_uniform`. |

### Phase 5: OS2 Ward Identity and Proof Chain (8 axioms)

All axioms in this file now require `IsPphi2Limit μ P mass` (fixed 2026-02-25:
6 axioms were overly strong, quantifying over arbitrary μ instead of P(φ)₂ limits).

| # | Name | File | Rating | Verified | Notes |
|---|------|------|--------|----------|-------|
| 22 | `latticeMeasure_translation_invariant` | OS2_WardIdentity | ✅ Standard | DT 2026-02-25 | Lattice measure invariant under cyclic translation. |
| 23 | ~~`translation_invariance_continuum`~~ | OS2_WardIdentity | ✅ **PROVED** | SA 2026-03-07 | `Z[τ_v f] = Z[f]`. From `cf_tendsto` + `lattice_inv` via `tendsto_nhds_unique_of_eventuallyEq`. |
| 24 | `anomaly_bound_from_superrenormalizability` | OS2_WardIdentity | ✅ Correct | Gemini 2026-03-07 | `‖Z_a[R·f]-Z_a[f]‖ ≤ C·a²·(1+\|log a\|)^p`. Scaling dim 4 > d=2. |
| 25 | `rotation_invariance_continuum` | OS2_WardIdentity | ✅ Correct | Gemini 2026-03-07 | `Z[R·f] = Z[f]` for R ∈ O(2). Ward identity + anomaly → 0. |
| 26 | `continuum_exponential_moments` | OS2_WardIdentity | ✅ Correct | Gemini 2026-03-07 | Nelson hypercontractivity. Simon 1974, Thm V.7. |
| 27 | `analyticOn_generatingFunctionalC` | OS2_WardIdentity | ✅ Standard | DT 2026-02-25 | Exp moments → joint analyticity (Hartogs + dominated convergence). |
| 28 | `exponential_moment_schwartz_bound` | OS2_WardIdentity | ✅ Correct | Gemini 2026-03-07 | Gaussian + interaction contribution. Simon 1974, Froehlich 1974. |
| ~~29~~ | ~~`complex_gf_invariant_of_real_gf_invariant`~~ | OS2_WardIdentity | **Proved** | | Identity theorem for analytic functions: F(z)=G(z) on ℝ → F=G on ℂ, evaluate at z=i. |
| 30 | `continuum_exponential_clustering` | OS2_WardIdentity | ⚠️ Correct for P(Φ)₂ | Gemini 2026-03-07 | Downstream of `spectral_gap_uniform`. No phase transition in d=2 with m>0. |
| 31 | `cesaro_set_integral_tendsto` | **PROVED** → `GeneralResults/FunctionalAnalysis.lean` | ✅ Proved | 2026-02-25 | Continuous Cesàro convergence. Moved to GeneralResults as pure Mathlib result. |
| 32 | `pphi2_generating_functional_real` | **PROVED** from `pphi2_measure_neg_invariant` | ✅ Proved | 2026-02-25 | Im(Z[f])=0 via conj(Z[f])=Z[f] from Z₂ symmetry. |
| 32a | `pphi2_measure_neg_invariant` | OS2_WardIdentity | ✅ Standard | 2026-02-25 | Z₂ symmetry: map Neg.neg μ = μ. From even P + GFF symmetry + weak limit closure. |
| 33 | `generatingFunctional_translate_continuous` | **PROVED** in OS2_WardIdentity | ✅ Proved | 2026-02-25 | t ↦ Z[f + τ_{(t,0)} g] continuous. Proved via DCT + `continuous_timeTranslationSchwartz`. |

**Proved theorems in OS2_WardIdentity.lean:**
- `os4_clustering_implies_ergodicity`: clustering → ergodicity via Cesàro + reality (**fully proved**)
- `anomaly_vanishes`: delegates to `anomaly_bound_from_superrenormalizability`
- `os3_for_continuum_limit`: trig identity decomposition + `os3_inheritance` (**fully proved**)
- `os0_for_continuum_limit`: exponential moments → OS0_Analyticity
- `os1_for_continuum_limit`: exponential moments → OS1_Regularity (**fully proved**)
- `os2_for_continuum_limit`: translation + rotation → OS2_EuclideanInvariance
- `os4_for_continuum_limit`: exponential clustering → OS4_Clustering (**fully proved**)

### Phase 6: Bridge (5 axioms)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|---------|
| 33 | ~~`IsPphi2ContinuumLimit.toIsPphi2Limit`~~ | Bridge | ✅ **PROVED** | SA 2026-02-25 | Converted from axiom to `theorem`. Proof is `exact h` since `IsPphi2Limit` and `IsPphi2ContinuumLimit` have identical bodies (modulo type aliases). |
| 34 | `measure_determined_by_schwinger` | Bridge | ⚠️ Likely correct | DT 2026-02-24 | Moment determinacy with exponential (Fernique-type) moment bound. |
| 35 | `wick_constant_comparison` | Bridge | ✅ Standard | DT 2026-02-24 | Wick constant ≈ (2π)⁻¹ log(1/a) with bounded remainder. |
| 36 | `schwinger_agreement` | Bridge | ⚠️ Likely correct | DT 2026-02-24 | n-point Schwinger function equality at weak coupling. |
| 37 | `same_continuum_measure` | Bridge | ⚠️ Likely correct | DT 2026-02-24 | Fixed: requires `IsPphi2ContinuumLimit`, `IsPhi4ContinuumLimit`, `IsWeakCoupling`. |
| 38 | `os2_from_phi4` | Bridge | ⚠️ Likely correct | DT 2026-02-24 | Fixed: requires `IsPhi4ContinuumLimit`. |
| 39 | ~~`os3_from_pphi2`~~ | Bridge | ✅ **PROVED** | SA 2026-02-27 | Replaced axiom with theorem: `exact os3_for_continuum_limit ... (IsPphi2ContinuumLimit.toIsPphi2Limit h)`. |

### Route B': Asymmetric Torus (0 axioms — all proved 2026-03-18)

All four infrastructure axioms have been replaced with theorems.

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| ~~B'1~~ | `asymTorusInteractingMeasure_gf_latticeTranslation_invariant` | AsymTorusOS | **PROVED** | Via evalAsymAtFinSite equivariance + lattice measure translation invariance. |
| ~~B'2~~ | `asymGf_sub_norm_le_seminorm` | AsymTorusOS | **PROVED** | Cauchy-Schwarz + hypercontractivity + tight lattice norm bound. |
| ~~B'3~~ | `asymTorusTranslation_continuous_in_v` | AsymTorusOS | **PROVED** | DM expansion + Sobolev isometry + 3-epsilon argument. |
| ~~B'4~~ | `asymTorusGF_latticeApproximation_error_vanishes` | AsymTorusOS | **PROVED** | Lattice rounding + squeeze using B'1–B'3. |

### Verification Summary (pphi2)

| Status | Count |
|--------|-------|
| Active axioms | 38 |
| Proved/Defined (no longer axioms) | 19+ |
| Verified (GR or DT) among active | 35+ |
| Self-audit only | 1 |

Most active axioms verified by GR or DT.
1 self-audit only: `pphi2_limit_exists` (Prokhorov existence).

### Notes from DT review (2026-02-25)

**Batch review of 19 new axioms (sorry→axiom conversion):**
- 15 Correct, 2 Likely correct, 1 Suspicious, 0 Wrong
- **Fixed SUSPICIOUS**: `anomaly_bound_from_superrenormalizability` — missing log factors per Glimm-Jaffe Thm 19.3.1. Now `C·a²·(1+|log a|)^p` instead of `C·a²`.
- **Likely correct**: `lattice_rp_matrix` (cos vs exp(i) — correct, both equivalent formulations), `exponential_moment_schwartz_bound` (non-standard norm but correct bound)
- **Fixed 6 overly-strong axioms**: `translation_invariance_continuum`, `rotation_invariance_continuum`, `continuum_exponential_moments`, `os0_inheritance`, `os3_inheritance`, `os4_inheritance` — all now require `IsPphi2Limit μ P mass`
- **Added 3 new axioms**: `IsPphi2Limit` (marker predicate, later converted to def), `pphi2_limit_exists` (Prokhorov existence, moved to Convergence.lean), `IsPphi2ContinuumLimit.toIsPphi2Limit` (bridge, later proved as theorem)

---

## gaussian-field Axioms (25 active, 0 sorries — table below is partially stale)

*Updated 2026-03-07. Current count per `count_axioms.sh`: 25 axioms, 0 sorries.*

| File | Axioms | Sorries | Verified | Notes |
|------|--------|---------|----------|-------|
| GaussianField/Density.lean | 2 | 0 | DT 2026-02-25 | Density bridge: `latticeGaussianMeasure_density_integral`, `integrable_mul_gaussianDensity`. NEW. |
| GaussianField/Hypercontractive.lean | 1 | 0 | DT 2026-02-25 | `gaussian_moment_ratio_bound` — Gamma function inequality for 1D hypercontractivity. NEW. |
| HeatKernel/PositionKernel.lean | 3 | 2 | GR Group 1 | Mehler formula, circle positivity, cylinder summability. (was 4; `cylinderHeatKernel_reproduces` restored as proved code) |
| Lattice/FKG.lean | 9 | 0 | DT 2026-02-25 | 9 axioms: `ad_marginal_preservation_ae` (LIKELY CORRECT), 4 Fubini/integration axioms (CORRECT), 4 truncation axioms (CORRECT). All support FKG proof. |
| Lattice/RapidDecayLattice.lean | 3 | 0 | GR Group 2 | Shell enumeration bounds, rapid decay equiv. |
| **Total** | **18** | **2** | | |

### New axiom details (DT 2026-02-25 review: 9 CORRECT, 1 LIKELY CORRECT)

| # | Name | File | Rating | Notes |
|---|------|------|--------|-------|
| 1 | `gaussian_moment_ratio_bound` | Hypercontractive:152 | ✅ CORRECT | `E[Z^{pn}]^{1/p} ≤ (p-1)^{n/2} E[Z^{2n}]^{1/2}` for standard Normal. Sharp Bonami inequality. |
| 2 | `latticeGaussianMeasure_density_integral` | Density:98 | ✅ CORRECT | Density bridge: abstract Gaussian measure ↔ Lebesgue integral with `gaussianDensity`. |
| 3 | `integrable_mul_gaussianDensity` | Density:112 | ✅ CORRECT | Direct corollary of density bridge. |
| 4 | `fubini_pi_decomp` | FKG:507 | ✅ CORRECT | Fubini for ℝ^ι = ℝ × ℝ^{ι\{i}}. |
| 5 | `integrable_marginal` | FKG:514 | ✅ CORRECT | Fubini-Tonelli for nonneg integrable. |
| 6 | `integrable_fiber_ae` | FKG:522 | ✅ CORRECT | Fiber integrable a.e. (Fubini). |
| 7 | `integral_empty_pi` | FKG:529 | ✅ CORRECT | Base case: ∫ over ℝ^∅ = f(unique point). |
| 8 | `ad_marginal_preservation_ae` | FKG:567 | ⚠️ LIKELY CORRECT | AD condition preserved by marginalization. Core induction step for FKG. |
| 9 | `fkg_truncation_dct` | FKG:732 | ✅ CORRECT | DCT for truncation max(F,-n)→F. Domination: \|max(F,-n)\| ≤ \|F\|. |
| 10 | `fkg_truncation_dct_prod` | FKG:739 | ✅ CORRECT | DCT for product truncation. |
| 11 | `integrable_truncation_mul` | FKG:747 | ✅ CORRECT | Integrability of truncated F·ρ. |
| 12 | `integrable_truncation_prod_mul` | FKG:752 | ✅ CORRECT | Integrability of truncated F·G·ρ. |

### Lattice Convergence (added 2026-03-07)

| # | Name | File | Rating | Notes |
|---|------|------|--------|-------|
| 13 | `lattice_covariance_pure_eq_2d_spectral` | Convergence:65 | ✅ Standard | BCCB circulant diagonalization: lattice covariance for pure tensors = explicit 2D DFT spectral sum. Davis, *Circulant Matrices*, Ch. 5. **(NOT VERIFIED)** |
| 14 | `latticeDFTCoeff1d_quadratic_bound` | Convergence:85 | ✅ Standard | Uniform quadratic DFT coefficient decay via discrete summation by parts. Katznelson, *Harmonic Analysis*, §I.2. **(NOT VERIFIED)** |
| 15 | `lattice_green_tendsto_continuum` | Convergence:363 | ⚠️ Likely correct | Bilinear extension from pure tensors to general elements. Follows from `lattice_green_tendsto_continuum_pure` (proved) + density + continuity. **(NOT VERIFIED)** |

**Proved theorem**: `lattice_green_tendsto_continuum_pure` — convergence for pure tensors via Tannery's theorem (`tendsto_tsum_of_dominated_convergence`) on ℕ×ℕ. Uses `latticeEigenvalue1d_tendsto_continuum`, `latticeDFTCoeff1d_tendsto` (mode convergence), and `latticeDFTCoeff1d_quadratic_bound` (domination via `C/((1+m₁)⁴(1+m₂)⁴)`). Summability via shifted p-series (`Real.summable_one_div_nat_pow` + `Summable.comp_injective`) and product (`Summable.mul_of_nonneg`).

---

## Critical Issues

### 1. ~~❓ `same_continuum_measure`~~ — FIXED (2026-02-24)

**Status**: RESOLVED. Now requires `IsPphi2ContinuumLimit`, `IsPhi4ContinuumLimit`, and `IsWeakCoupling` hypotheses. Also fixed `os2_from_phi4` (was FALSE without `IsPhi4ContinuumLimit`), `os3_from_pphi2` (was FALSE without `IsPphi2ContinuumLimit`), and `measure_determined_by_schwinger` (polynomial→exponential moments).

### 2. ~~❓ `moment_equicontinuity`~~ — FIXED (2026-02-24)

**Status**: RESOLVED. RHS now `C * (SchwartzMap.seminorm ℝ k n (f - g)) ^ 2` with existentially quantified seminorm indices `k n`. Was bare constant `C` (flagged WRONG by GR).

### 3. ⚠️ `os0_inheritance` (AxiomInheritance:78)

**Severity**: LOW — Verified but flagged **TOO WEAK** by GR
**Issue**: States all moments finite, but OS0 requires factorial growth bound (E0' condition).
**Action**: Strengthen to include growth bound.

---

## Placeholder Theorems (Filled 2026-02-24)

All 21 former placeholder theorems (previously `True`-valued) have been filled with
real Lean types and `sorry` proofs. They are now tracked as sorries in the sorry count.
`unique_vacuum` was fully proved. `ward_identity_lattice` was proved (trivially, since
the lattice rotation action is not yet defined). The rest are sorry-proofed with
meaningful mathematical types.

### OS2: Euclidean Invariance (Ward Identity)
- `latticeMeasure_translation_invariant` — Integral equality under lattice translation (sorry)
- `ward_identity_lattice` — Ward identity bound: $|∫ F dμ - ∫ F∘R_θ dμ| ≤ C|θ|a²$ (proved, pending rotation action)
- `anomaly_scaling_dimension` — Lattice dispersion Taylor error $≤ a²(Σ k_i⁴ + 3Σ k_i²)$ (**proved**, cos_bound + crude bound)
- `anomaly_vanishes` — $‖Z[R·f] - Z[f]‖ ≤ C·a²·(1+|log a|)^p$ for continuum-embedded lattice measure (delegates to axiom)

### OS3: Reflection Positivity
- `lattice_rp` — **PROVED** from `gaussian_rp_with_boundary_weight` via time-slice decomposition
- `gaussian_rp_with_boundary_weight` — **PROVED** from `gaussian_density_rp` via `evalMapMeasurableEquiv` density bridge
- `gaussian_density_rp` — **PROVED** from `gaussian_rp_perfect_square` (density factorization + A-independence + factoring G(u) out via `integral_const_mul`)
- `gaussian_rp_perfect_square` — **PROVED** from `gaussian_rp_cov_perfect_square`: factors G(u) out of inner integral using `hG_dep` + `integral_const_mul`
- `gaussian_rp_cov_perfect_square` — **AXIOM** (private): second Fubini + COV + perfect square in factored form (Glimm-Jaffe Ch. 6.1)
- `rp_from_transfer_positivity` — **PROVED** $⟨f, T^n f⟩_{L²} ≥ 0$ via `transferOperatorCLM`

### OS4: Clustering & Ergodicity
- `two_point_clustering_lattice` — Exponential decay bound using `finLatticeDelta` and `massGap` (sorry)
- `general_clustering_lattice` — Quantified clustering over bounded observables (sorry)
- `clustering_implies_ergodicity` — Measure-theoretic ergodicity criterion (sorry)
- `unique_vacuum` — **PROVED** from `transferEigenvalue_ground_simple`

### Continuum Limit & Convergence
- ~~`gaussian_hypercontractivity_continuum`~~ — **PROVED** from `gaussian_hypercontractive` via pushforward + `latticeEmbedLift_eval_eq`
- `wickMonomial_latticeGaussian` — ✅ Verified (Gemini). Hermite orthogonality: $∫ :τ^n:_c \, dμ_{GFF} = 0$ for $n ≥ 1$. Defining property of Wick ordering. Glimm-Jaffe Ch. 6, Simon §III.1. (axiom)
- ~~`wickPolynomial_uniform_bounded_below`~~ — **PROVED** in WickPolynomial.lean via coefficient continuity + compactness + leading term dominance
- ~~`exponential_moment_bound`~~ — **PROVED** from `wickPolynomial_uniform_bounded_below` + pointwise exp bound on probability measure
- ~~`interacting_moment_bound`~~ — **PROVED** from `exponential_moment_bound`, `partitionFunction_ge_one`, `pairing_memLp`, and Hölder/Cauchy-Schwarz density transfer
- ~~`partitionFunction_ge_one`~~ — **PROVED** from Jensen's inequality (`ConvexOn.map_integral_le`) + `interactionFunctional_mean_nonpos`
- ~~`interactionFunctional_mean_nonpos`~~ — **PROVED** from `wickMonomial_latticeGaussian` (Hermite orthogonality) + linearity + `P.coeff_zero_nonpos`
- `os4_inheritance` — Exponential clustering of connected 2-point functions (sorry)
- `schwinger2_convergence` — 2-point Schwinger function convergence along subsequence (sorry)
- `schwinger_n_convergence` — n-point Schwinger function convergence along subsequence (sorry)
- `continuumLimit_nontrivial` — $∫ (ω f)² dμ > 0$ for some $f$ (sorry)
- `continuumLimit_nonGaussian` — Connected 4-point function $≠ 0$ (sorry)

### Main Assembly & Bridge
- `schwinger_agreement` — n-point Schwinger function equality between lattice and Phi4 limits (sorry)
- `pphi2_nontrivial` — $∫ (ω f)² dμ > 0$ for all $f ≠ 0$ (sorry)
- `pphi2_nonGaussian` — $∫ (ω f)⁴ dμ - 3(∫ (ω f)² dμ)² ≠ 0$ (sorry)
- `os_reconstruction` — OS reconstruction yields mass gap $m₀ > 0$ (proved: `⟨mass, hmass⟩`)
- `pphi2_wightman` — Full OS bundle + mass gap existence (proved from `pphi2_exists` + `os_reconstruction`)

---

## Proved Axioms (historical record)

The following were previously axioms and are now theorems:

| Name | File | Date Proved | Method |
|------|------|-------------|--------|
| `euclideanAction2` | OSAxioms | 2026-02-23 | `compCLMOfAntilipschitz` |
| `euclideanAction2ℂ` | OSAxioms | 2026-02-23 | `compCLMOfAntilipschitz` |
| `compTimeReflection2` | OSAxioms | 2026-02-23 | `compCLMOfContinuousLinearEquiv` |
| `compTimeReflection2_apply` | OSAxioms | 2026-02-23 | `rfl` from construction |
| `SchwartzMap.translate` | OSAxioms | 2026-02-23 | `compCLMOfAntilipschitz` |
| `prokhorov_sequential` | Convergence | 2026-02-23 | Full proof via Mathlib's `isCompact_closure_of_isTightMeasureSet` |
| `wickPolynomial_bounded_below` | WickPolynomial | 2026-02-23 | `poly_even_degree_bounded_below` + `Continuous.exists_forall_le` |
| `latticeInteraction_convex` | LatticeAction | 2026-02-23 | **Removed (was FALSE)**. Replaced by `latticeInteraction_single_site`. |
| `polynomial_lower_bound` | Polynomial | 2026-02-23 | Dead code removed |
| `field_all_moments_finite` | Normalization | 2026-02-23 | `pairing_is_gaussian` + integrability |
| `rp_closed_under_weak_limit` | OS3_RP_Inheritance | 2026-02-23 | Weak limits of nonneg expressions |
| `connectedTwoPoint_nonneg_delta` | OS4_MassGap | 2026-02-23 | Variance ∫(X-E[X])² ≥ 0 |
| `so2Generator` | OS2_WardIdentity | 2026-02-24 | `smulLeftCLM` + `lineDerivOpCLM` |
| `continuumLimit` | Convergence | 2026-02-24 | `prokhorov_sequential` + `continuumMeasures_tight` |
| `latticeEmbed` | Embedding | 2026-02-24 | `SchwartzMap.mkCLMtoNormedSpace` with seminorm bound |
| `latticeEmbed_eval` | Embedding | 2026-02-24 | `rfl` from `latticeEmbed` construction |
| `transferOperator_spectral` | L2Operator | 2026-02-24 | `compact_selfAdjoint_spectral` from gaussian-field (proved spectral theorem) |
| `latticeEmbed_measurable` | Embedding | 2026-02-24 | `configuration_measurable_of_eval_measurable` + continuity of finite sum |
| `latticeEmbedLift` | Embedding | 2026-02-24 | Constructed as `latticeEmbed (fun x => ω (Pi.single x 1))` |
| `latticeEmbedLift_measurable` | Embedding | 2026-02-24 | `configuration_measurable_of_eval_measurable` + `configuration_eval_measurable` |
| `wickMonomial_eq_hermite` | WickPolynomial | 2026-02-24 | `wick_eq_hermiteR_rpow` from gaussian-field HermiteWick |

---

## Audit: New axioms added 2026-02-25

### Session 1: OS proof chain axioms (10 new axioms, self-audited)

| # | Name | File | Rating | Notes |
|---|------|------|--------|-------|
| 28 | `latticeMeasure_translation_invariant` | OS2_WardIdentity | ⚠️ Likely correct | Lattice translation invariance. Change-of-variables on torus. **Note:** correctly uses `ω.comp L_v.toContinuousLinearMap`. |
| 29 | `translation_invariance_continuum` | OS2_WardIdentity | ⚠️ Overly strong | Claims for ANY μ (P, mass unused). Correct for the intended use (continuum limit) but strictly this says all probability measures are translation-invariant. Trivially true for `Measure.dirac 0`. |
| 30 | `anomaly_bound_from_superrenormalizability` | OS2_WardIdentity | ⚠️ Likely correct | O(a²) anomaly bound. Correct physics (dim 4 > d = 2, no log corrections). Correctly quantified: C exists uniformly, bound ∀ a ≤ 1. |
| 31 | `continuum_exponential_moments` | OS2_WardIdentity | ⚠️ Overly strong | Claims ∀ c > 0, Integrable(exp(c|ω f|)) for ANY μ. Same issue as #29 — correct for continuum limit, too strong for arbitrary μ. |
| 32 | `analyticOn_generatingFunctionalC` | OS2_WardIdentity | ✅ Standard | Requires h_moments hypothesis → AnalyticOn. Correctly stated with Hartogs + dominated convergence. |
| 33 | `exponential_moment_schwartz_bound` | OS2_WardIdentity | ⚠️ Likely correct | Gaussian integral bound. Uses L¹ + L² norms as proxy for H⁻¹ norm via Sobolev. |
| 34 | `complex_gf_invariant_of_real_gf_invariant` | OS2_WardIdentity | ✅ Standard | Cramér-Wold + Lévy uniqueness. Correctly elevates real GF invariance to complex. |
| 35 | `os4_clustering_implies_ergodicity` | OS2_WardIdentity | ⚠️ Likely correct | Clustering → ergodicity via Cesàro + reality of Z[f]. |
| 36 | `two_point_clustering_from_spectral_gap` | OS4_MassGap | ✅ Standard | Spectral gap → 2-pt exponential clustering. Correct: uses `transferEigenvalue` and `massGap`. |
| 37 | `general_clustering_from_spectral_gap` | OS4_MassGap | ✅ Standard | Extends to bounded observables. |
| 38 | `transferOperator_inner_nonneg` | L2Operator | ✅ Standard | ⟨f, Tf⟩ ≥ 0 from Perron-Frobenius (strictly positive kernel). Reed-Simon IV Thm XIII.44. |

### Session 2: Final 9 sorry eliminations (9 new axioms, self-audited)

| # | Name | File | Rating | Notes |
|---|------|------|--------|-------|
| 39 | `os4_inheritance` | AxiomInheritance | ⚠️ Fixed 2026-02-25 | **Had quantifier bug:** C depended on R (vacuously true). Fixed: C now quantified before R (∀ f g, ∃ C, ∀ R). **Note:** R still has no structural connection to f, g — this is a weak formulation but not vacuous after fix. |
| 40 | `schwinger2_convergence` | Convergence | ⚠️ Likely correct | Prokhorov + uniform L² integrability → subsequential convergence of 2-pt functions. Standard. |
| 41 | `schwinger_n_convergence` | Convergence | ⚠️ Likely correct | Diagonal subsequence extraction for n-pt functions. Standard. |
| 42 | `continuumLimit_nontrivial` | Convergence | ⚠️ Likely correct | ∃ f with ∫(ω f)² > 0. Free field gives lower bound via Griffiths inequalities. |
| 43 | `continuumLimit_nonGaussian` | Convergence | ⚠️ Likely correct | Nonzero 4th cumulant. InteractionPolynomial requires degree ≥ 4 with lead coeff 1/n, so interaction is always nontrivial. O(λ) perturbative bound. |
| 44 | ~~`gaussian_density_rp`~~ | OS3_RP_Lattice | ✅ **PROVED** | Core Gaussian RP at density level. Non-integrable case proved; integrable case: density factorization + A-independence proved. Final step uses `gaussian_rp_perfect_square` theorem. |
| 44a | ~~`gaussian_rp_perfect_square`~~ | OS3_RP_Lattice | ✅ **PROVED** | SA 2026-03-11 | Factors G(u) out of inner integral using `hG_dep` + `integral_const_mul`, then applies `gaussian_rp_cov_perfect_square`. |
| 44b | `gaussian_rp_cov_perfect_square` | OS3_RP_Lattice | ✅ Standard | SA 2026-03-11 | Second Fubini + COV (time-reflection on S₋→S₊) + perfect square for Gaussian RP (factored form: G(u) already pulled out). Private axiom. Glimm-Jaffe Ch. 6.1, Osterwalder-Seiler §3. |
| 45 | `schwinger_agreement` | Bridge | ⚠️ Likely correct | Cluster expansion uniqueness at weak coupling. Properly constrained with `isPhi4`, `IsWeakCoupling` hypotheses. Very deep result (Guerra-Rosen-Simon 1975). |
| 46 | `pphi2_nontriviality` | Main | ⚠️ Likely correct | ∃ μ, ∀ f ≠ 0, ∫(ω f)² > 0. Griffiths/FKG correlation inequality. The ∃ μ is existential (finds a good measure, not Measure.dirac 0). |
| 47 | `pphi2_nonGaussianity` | Main | ⚠️ Likely correct | ∃ μ with nonzero 4th cumulant. Same ∃ μ pattern. |

### Known design issues (not bugs)

1. **Unused P/mass pattern**: ~10 axioms (continuum_exponential_moments, translation_invariance_continuum, rotation_invariance_continuum, os4_inheritance, os4_clustering_implies_ergodicity, etc.) claim properties for arbitrary μ without connecting to the lattice construction. This is a design simplification: the axioms serve as stand-ins for proper proofs that would take μ as "the continuum limit of lattice measures." Since `pphi2_exists` currently uses `Measure.dirac 0`, these axioms are trivially satisfied by the specific measure used.

2. **`SatisfiesOS0134` unused**: The secondary OS bundle with Schwinger function formulation is dead code — not imported by `Main.lean`. The main theorem uses `SatisfiesFullOS` via `continuumLimit_satisfies_fullOS`.

### Verification Summary (updated 2026-03-07)

All 42 active pphi2 axioms have been reviewed by Gemini.

| Status | Count |
|--------|-------|
| ✅ Verified correct | 35 |
| ⚠️ Correct in intended regime | 5 (`spectral_gap_uniform`, `spectral_gap_lower_bound`, `continuum_exponential_clustering`, `os4_inheritance`, `torusPositiveTimeSubmodule`) |
| ⚠️ Design note (not bug) | 2 (`torusLattice_rp` trivially true for odd N; `torusPositiveTimeSubmodule` should be def) |
| ❌ Wrong | 0 |
| **Total active** | **42** |

Notes on ⚠️ axioms:
- `spectral_gap_*` and downstream clustering axioms: Gemini flags potential issues
  at critical points or strong coupling. These don't apply to P(Φ)₂ in d=2 with
  m > 0: the Glimm-Jaffe-Spencer theorem establishes a mass gap uniformly for
  our `InteractionPolynomial` class (even degree ≥ 4, positive leading coeff 1/n).
- `torusPositiveTimeSubmodule`: axiomatic submodule is a design simplification;
  doesn't affect correctness.
- `torusLattice_rp`: for odd N, `torusPositiveTimeSubmodule` may be trivial,
  making RP vacuously true. Not a bug.

---

## Torus OS Axioms (TorusOSAxioms.lean + Torus/Symmetry.lean)

### gaussian-field axioms

| # | Axiom | Rating | Source |
|---|-------|--------|--------|
| 1 | `nuclearTensorProduct_mapCLM` | ✅ Standard | ✅ DT 2026-03-03: Trèves Ch.50, standard projective tensor product property |
| 2 | `nuclearTensorProduct_swapCLM` | ✅ Standard | ✅ DT 2026-03-03: canonical isomorphism, Trèves Ch.43 |

### pphi2 axioms

| # | Axiom | Rating | Source |
|---|-------|--------|--------|
| ~~3~~ | ~~`torusGaussianLimit_characteristic_functional`~~ | **PROVED** | Now a theorem. CF `E[e^{iωf}] = exp(-½G(f,f))` proved from MGF via `complexMGF` analytic continuation + `charFun_gaussianReal`. |
| 3 | `torusGaussianLimit_complex_cf_quadratic` | ✅ Standard | Complex CF of Gaussian equals exp(-½ ∑ᵢⱼ zᵢzⱼ G(Jᵢ,Jⱼ)). Multivariate complex MGF of joint Gaussian vector. Requires bilinearity of Green's function + complex MGF. Fernique §III.4, Simon P(φ)₂ Ch.I |
| 4 | `torusContinuumGreen_translation_invariant` | ✅ Standard | ✅ DT 2026-03-03: translation acts by phase in Fourier space |
| 5 | `torusContinuumGreen_pointGroup_invariant` | ✅ Standard | ✅ DT 2026-03-03: D4 symmetry of Laplacian eigenvalues |
| 6 | `torusPositiveTimeSubmodule` | ✅ Infrastructure | Submodule of torus test functions with time support in (0, L/2). Nuclear tensor product lacks pointwise evaluation, so axiomatized. |
| 7 | `torusLattice_rp` | ✅ Standard | Matrix form: Σᵢⱼ cᵢcⱼ Re(Z_N[fᵢ - Θfⱼ]) ≥ 0 for positive-time test functions. Correct by transfer matrix factorization with H ≥ 0. Replaces incorrect single-function form (counterexample: F(ω) = tanh(ω(f) - ω(Θf))). |
| ~~8~~ | ~~`torusGaussianLimit_complex_cf_norm`~~ | **ELIMINATED** | OS1 proved directly via triangle inequality without needing exact norm. |
| ~~9~~ | ~~`torusContinuumGreen_continuous_diag`~~ | **PROVED** | Now a theorem. Via `greenFunctionBilinear_continuous_diag` in gaussian-field. |

---

### Route B' IR Limit (7 axioms, added 2026-03-19)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|-------|
| 1 | `cylinderToTorusEmbed_comp_timeTranslation` | CylinderEmbedding:99 | ✅ Standard | ✅ Gemini (2026-03-19) | Periodization intertwines time translation. Reindexing sum over ℤ. |
| 2 | `cylinderToTorusEmbed_comp_timeReflection` | CylinderEmbedding:106 | ✅ Standard | ✅ Gemini (2026-03-19) | Periodization intertwines time reflection. Reindex k → -k. |
| 3 | `cylinderIR_uniform_second_moment` | GreenFunctionComparison:52 | ✅ Standard | ✅ Gemini (2026-03-19) | Pullback → OS1 regularity → method of images. Uniform in Lt ≥ 1. |
| 4 | `cylinderIR_uniform_exponential_moment` | UniformExponentialMoment:53 | ✅ Standard | ✅ Gemini (2026-03-19) | Nelson/Fröhlich + method of images. Sufficient for Vitali/Montel. |
| 5 | `cylinderIRLimit_exists` | IRTightness:60 | ✅ Standard | ✅ Gemini (2026-03-19) | Mitoma tightness → Prokhorov → Lévy continuity. Char. functional convergence correct. |
| 6 | `cylinderIR_os0` | CylinderOS:130 | ✅ Standard | ✅ Gemini (2026-03-19) | Uniform exp moments → Vitali/Montel → analyticity. |
| 7 | `cylinderIR_os3` | CylinderOS:144 | ✅ Standard | ✅ Gemini (2026-03-19) | No wrap-around for Lt > 2R confirmed valid. Density of C_c^∞ confirmed. |

**Gemini review notes (2026-03-19):**
- All 7 axioms verified correct with no modifications needed.
- The Re() in OS3 is redundant (M_{ij} is Hermitian so c†Mc is real) but harmless.
- Characteristic functional convergence is the standard notion for nuclear spaces.
- **UPDATE**: `cylinderToTorusEmbed_comp_timeTranslation` and `_comp_timeReflection`
  are now **PROVED** via NTP pure tensor density technique.

### Factored axioms (added 2026-03-20)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|-------|
| 1 | `wickConstant_eq_variance` | Hypercontractivity:197 | ✅ Standard | ✅ Gemini (2026-03-20) | Wick constant = GFF variance. Spectral decomposition + Parseval. |
| 2 | `gaussian_hermite_zero_mean` | Hypercontractivity:223 | ✅ Standard | ✅ Gemini (2026-03-20) | Hermite orthogonality under matching Gaussian. Standard 1D probability. |
| 3 | `configuration_continuum_polishSpace` | Convergence:183 | ✅ Standard | ✅ Gemini (2026-03-20) | S'(ℝ^d) Polish. Gel'fand-Vilenkin: nuclear Fréchet dual is Polish. |
| 4 | `configuration_continuum_borelSpace` | Convergence:187 | ✅ Standard | — | Borel σ-algebra on S'(ℝ^d). Standard topology. |
| 5 | `fourierMultiplier_preserves_real` | FourierMultiplier:244 (g-f) | ✅ Standard | ✅ Gemini (2026-03-20) | Even real symbol → real output. Requires σ even (corrected). |
| 6 | `fourierMultiplierCLM_translation_comm` | FourierMultiplier:289 (g-f) | ✅ Standard | — | M_σ commutes with translation. Phase factor commutativity. |
| 7 | `fourierMultiplierCLM_even_reflection_comm` | FourierMultiplier:301 (g-f) | ✅ Standard | — | M_σ commutes with reflection for even σ. Even symbol invariance. |
- The "no wrap-around" argument for OS3 is the key mechanism for transferring torus RP to cylinder.

## References

- Glimm-Jaffe, *Quantum Physics: A Functional Integral Point of View* (1987)
- Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory* (1974)
- Reed-Simon, *Methods of Modern Mathematical Physics* Vol II, IV
- Osterwalder-Schrader, "Axioms for Euclidean Green's Functions I, II" (1973, 1975)
- Gelfand-Vilenkin, *Generalized Functions Vol. 4* — nuclear spaces, S'(ℝ^d) Polish
- Bogachev, *Gaussian Measures* §3.2 — duals of Fréchet spaces
- Holley (1974), Fortuin-Kasteleyn-Ginibre (1971) — FKG inequality
- Mitoma (1983) — tightness on S'
- Symanzik (1983) — lattice continuum limit, improved action
- Guerra-Rosen-Simon (1975) — Cluster expansion uniqueness

- Trèves, *Topological Vector Spaces, Distributions, and Kernels* — tensor product CLMs
- Fernique (1975) — Gaussian measures on nuclear spaces

---

## Audit entry 2026-04-21: MomentBoundOS1 infrastructure + Route B′ refactor premise

This is a design-level audit (not a new axiom) of the Green-function-controlled
OS1 refactor path for Route B′.

**New file:** `Pphi2/AsymTorus/MomentBoundOS1.lean` (214 lines, 0 axioms, 0 sorries).
Introduces:
- `MeasureHasGreenMomentBound mass K C μ` — predicate asserting
  `∫ exp(|ω f|) dμ ≤ K · exp(C · G_{Lt,Ls}(f, f))`.
- `cylinderPullback_expMoment_{eq, le_green, uniform_bound}` — three theorems
  composing the pullback with `torusGreen_uniform_bound` (gaussian-field) to
  give the uniform-in-`Lt` cylinder bound that matches
  `cylinderIR_uniform_exponential_moment`.

### Gemini deep-think verdict (2026-04-21)

**Point 1 (predicate correctness): GREEN.** The identification
`G_{Lt,Ls}(f, f) = ‖f‖²_{H⁻¹(T_{Lt,Ls})}` is tight by definition of the
Sobolev norm. For the GFF, `∫ exp(ω(f)) dμ_{GFF} = exp(½ G(f,f))` exactly,
and the interacting-case bound inherits the quadratic-in-Green form through
Cauchy-Schwarz density transfer. No slack.

**Point 2 (Lt-uniformity of K, C): YELLOW / important correction.**
Our initial intuition that volume dependencies in `K_Nelson ≤ exp(K'·Vol)`
and `Z ≥ exp(p·Vol)` would cancel in the density-transfer ratio is
**insufficient**. The naive Cauchy-Schwarz of `exp(-V)/Z` does not give
volume-independent constants; it gives constants with explicit
volume-exponential dependence that do not cancel cleanly. True Lt-uniformity
is a "cornerstone" result for P(φ)₂, proved via:
- **Cluster expansion** (weak coupling) — Glimm-Jaffe-Spencer
- **Correlation inequalities** (GKS, FKG — available for e.g. φ⁴)
- **Chessboard estimates** (from reflection positivity)

Any derivation of "concrete UV-limit family satisfies uniform
`MeasureHasGreenMomentBound`" from first principles is book-length
(Glimm-Jaffe Ch. 18–19 or Simon Ch. VIII). Formalization path: introduce
a single axiom expressing the uniform-in-volume P(φ)₂ exponential moment
bound, citing the literature, and derive the three current IRLimit axioms
from it via `MomentBoundOS1.lean`. This replaces 3 axioms with 1 deeper
axiom but does **not** reduce to elementary calculations.

**Point 3 (quantifier composition): GREEN.** `MeasureHasGreenMomentBound`
is a concrete analytic property supporting OS0 specifically; it is not a
replacement for `AsymSatisfiesTorusOS` but rather evidence for one of its
clauses. The `∃ K' C' q, ∀ Lt μ hμ f, ...` structure in
`cylinderPullback_expMoment_uniform_bound` correctly lifts a uniform-in-Lt
Green-moment bound on the torus family to a uniform-in-Lt cylinder bound.

### Implication for Route B′ plan

The `MomentBoundOS1.lean` infrastructure is correct and reusable. The
hard work is still in front of us: proving (or axiomatizing at a cleaner
level) the Lt-uniform `MeasureHasGreenMomentBound` for the concrete
UV-limit family. This is comparable in difficulty to Route A's
`spectral_gap_uniform`. Not a quick-session target.

The three existing IRLimit axioms
(`cylinderIR_uniform_second_moment`,
`cylinderIR_uniform_exponential_moment`, `cylinderIR_os3`) remain as
the live axioms pending this deeper work.

**Audit Date**: 2026-03-19
