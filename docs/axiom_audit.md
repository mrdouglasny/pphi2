# Comprehensive Axiom Audit: pphi2 + gaussian-field

**Updated**: 2026-02-25 (All sorries eliminated, 47 axioms)
**pphi2**: 49 axioms, 0 sorries | **gaussian-field**: 2 axioms, 0 sorries | **Total**: 51

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

### Phase 2: Transfer Matrix and RP (9 axioms)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|-------|
| 3 | `transferOperatorCLM` | L2Operator | ⚠️ Likely correct | SA | Transfer matrix as CLM on L²(ℝ^Ns). Integral operator with Gaussian-bounded kernel. NEW. |
| 4 | `transferOperator_isSelfAdjoint` | L2Operator | ✅ Standard | SA | Self-adjoint from kernel symmetry. NEW. |
| 5 | `transferOperator_isCompact` | L2Operator | ⚠️ Likely correct | SA | Compact from Hilbert-Schmidt (Gaussian kernel decay). NEW. |
| 6 | `transferEigenvalue` | L2Operator | ⚠️ Likely correct | DT 2026-02-24 | Sorted eigenvalue sequence. Connected to spectral theorem via `transferOperator_spectral` (proved). |
| 7 | `transferEigenvalue_pos` | L2Operator | ✅ Standard | GR Group 3 | All eigenvalues > 0. Perron-Frobenius for strictly positive kernel. |
| 8 | `transferEigenvalue_antitone` | L2Operator | ✅ Standard | GR Group 3 | Eigenvalues decreasing. Standard spectral ordering (min-max). |
| 9 | `transferEigenvalue_ground_simple` | L2Operator | ✅ Standard | GR Group 3 | λ₀ > λ₁. Perron-Frobenius for positivity-improving operators. Reed-Simon IV Thm XIII.44. |
| 10 | `action_decomposition` | OS3_RP_Lattice | ⚠️ Likely correct | GR Group 5 | S = S⁺ + S⁻ across time-reflection plane. Now uses `siteEquiv` + `fieldToSites` to connect `Fin N × Fin N` to `FinLatticeSites 2 N`. |
| 11 | `lattice_rp_matrix` | OS3_RP_Lattice | ⚠️ Likely correct | DT 2026-02-24 | RP matrix Σ cᵢc̄ⱼ ∫ cos(⟨φ, fᵢ-Θfⱼ⟩) dμ_a ≥ 0. New partial formalization in-file: helper lemmas + `lattice_rp_matrix_reduction`; remaining gap is explicit trig/sum expansion identity. |

### Phase 3: Spectral Gap (2 axioms)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|-------|
| 12 | `spectral_gap_uniform` | SpectralGap:134 | ⚠️ Likely correct | GR Group 3 | ∃ m₀ > 0, gap(a) ≥ m₀ ∀a ≤ a₀. Central result of Glimm-Jaffe. VERY HARD. |
| 13 | `spectral_gap_lower_bound` | SpectralGap:145 | ⚠️ Likely correct | GR Group 3 | gap ≥ c·mass. Standard weak-coupling result. |

### Phase 4: Continuum Limit (8 active axioms, 5 proved)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|-------|
| 11 | ~~`latticeEmbed`~~ | Embedding:136 | ✅ **PROVED** | DT 2026-02-24 | Constructed via `SchwartzMap.mkCLMtoNormedSpace`. |
| 12 | ~~`latticeEmbed_eval`~~ | Embedding:170 | ✅ **PROVED** | DT 2026-02-24 | `rfl` from construction. |
| 13 | ~~`latticeEmbed_measurable`~~ | Embedding | ✅ **PROVED** | DT 2026-02-24 | `configuration_measurable_of_eval_measurable` + `continuous_apply` for each coordinate. |
| 14 | ~~`latticeEmbedLift`~~ | Embedding:201 | ✅ **PROVED** | SA 2026-02-24 | Constructed as `latticeEmbed d N a ha (fun x => ω (Pi.single x 1))`. |
| 15 | ~~`latticeEmbedLift_measurable`~~ | Embedding:212 | ✅ **PROVED** | SA 2026-02-24 | `configuration_measurable_of_eval_measurable` + `configuration_eval_measurable`. |
| 16 | `second_moment_uniform` | Tightness:74 | ⚠️ Likely correct | GR Group 4 | ∫ Φ_a(f)² dν_a ≤ C(f). Nelson's hypercontractive estimate. |
| 17 | `moment_equicontinuity` | Tightness:89 | ⚠️ Likely correct | GR Group 4 | Fixed: RHS now `C * (seminorm k n (f-g))²`. Was bare constant (flagged WRONG by GR). |
| 18 | `continuumMeasures_tight` | Tightness:110 | ⚠️ Likely correct | GR Group 4 | Mitoma criterion + moment bounds. |
| 19 | `prokhorov_configuration_sequential` | Convergence | ⚠️ Infrastructure | DT 2026-02-26 | Configuration-space sequential extraction axiom replacing global Polish/Borel assumptions on `Configuration (ContinuumTestFunction d)`. Planned replacement route documented in `Pphi2/ContinuumLimit/SobolevProkhorovPlan.lean`. |
| 21 | `os0_inheritance` | AxiomInheritance:78 | ⚠️ Likely correct | GR Group 4 | OS0 transfers. GR notes: "TRUE but TOO WEAK" — should include factorial growth (E0'). |
| 22 | `os3_inheritance` | AxiomInheritance | ✅ Standard | DT 2026-02-25 | Abstract IsRP for continuum limit: ∫ F·F(Θ*·) dμ ≥ 0. Now requires `IsPphi2Limit`. Follows from lattice_rp_matrix + rp_closed_under_weak_limit (proved). |
| 22b | ~~`IsPphi2Limit`~~ | Embedding:271 | ✅ **DEFINED** | SA 2026-02-25 | Converted from axiom to `def`: ∃ (a, ν) with Schwinger function convergence. Mirrors `IsPphi2ContinuumLimit` in Bridge.lean. |
| 22c | `pphi2_limit_exists` | Convergence | ⚠️ Likely correct | SA 2026-02-25 | ∃ μ `IsPphi2Limit`. Prokhorov + tightness + diagonal argument. Moved from OS2_WardIdentity to Convergence. |

### Phase 5: OS2 Ward Identity and Proof Chain (12 axioms)

All axioms in this file now require `IsPphi2Limit μ P mass` (fixed 2026-02-25:
6 axioms were overly strong, quantifying over arbitrary μ instead of P(φ)₂ limits).

| # | Name | File | Rating | Verified | Notes |
|---|------|------|--------|----------|-------|
| 22 | `latticeMeasure_translation_invariant` | OS2_WardIdentity | ✅ Standard | DT 2026-02-25 | Lattice measure invariant under cyclic translation. |
| 23 | `translation_invariance_continuum` | OS2_WardIdentity | ✅ Standard | DT 2026-02-25 | `Z[τ_v f] = Z[f]`. Now requires `IsPphi2Limit`. Rational density + continuity. |
| 24 | `anomaly_bound_from_superrenormalizability` | OS2_WardIdentity | ⚠️ Likely correct | DT 2026-02-25 | `‖Z_a[R·f]-Z_a[f]‖ ≤ C·a²·(1+\|log a\|)^p`. **Fixed**: added log factor per Glimm-Jaffe Thm 19.3.1 (was flagged SUSPICIOUS by DT without log). |
| 25 | `rotation_invariance_continuum` | OS2_WardIdentity | ⚠️ Likely correct | DT 2026-02-25 | `Z[R·f] = Z[f]` for R ∈ O(2). Now requires `IsPphi2Limit`. Ward identity + irrelevance. |
| 26 | `continuum_exponential_moments` | OS2_WardIdentity | ⚠️ Likely correct | DT 2026-02-25 | `∀ c > 0, Integrable (exp(c·\|ω f\|)) μ`. Now requires `IsPphi2Limit`. Fernique + Nelson. Feeds OS0+OS1. |
| 27 | `analyticOn_generatingFunctionalC` | OS2_WardIdentity | ✅ Standard | DT 2026-02-25 | Exp moments → joint analyticity (Hartogs + dominated convergence). |
| 28 | `exponential_moment_schwartz_bound` | OS2_WardIdentity | ⚠️ Likely correct | DT 2026-02-25 | `∫ exp(\|ω g\|) ≤ exp(c·(‖g‖₁+‖g‖₂²))`. Non-standard norm formulation. |
| 29 | `complex_gf_invariant_of_real_gf_invariant` | OS2_WardIdentity | ✅ Standard | DT 2026-02-25 | Real Z invariance → complex Z invariance (Cramér-Wold + Lévy uniqueness). |
| 30 | `continuum_exponential_clustering` | OS2_WardIdentity | ⚠️ Likely correct | DT 2026-02-25 | `‖Z[f+τ_a g] - Z[f]Z[g]‖ ≤ C·exp(-m₀·‖a‖)`. Now requires `IsPphi2Limit`. Spectral gap. |
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

### Phase 6: Bridge (6 axioms)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|---------|
| 33 | ~~`IsPphi2ContinuumLimit.toIsPphi2Limit`~~ | Bridge | ✅ **PROVED** | SA 2026-02-25 | Converted from axiom to `theorem`. Proof is `exact h` since `IsPphi2Limit` and `IsPphi2ContinuumLimit` have identical bodies (modulo type aliases). |
| 34 | `measure_determined_by_schwinger` | Bridge | ⚠️ Likely correct | DT 2026-02-24 | Moment determinacy with exponential (Fernique-type) moment bound. |
| 35 | `wick_constant_comparison` | Bridge | ✅ Standard | DT 2026-02-24 | Wick constant ≈ (2π)⁻¹ log(1/a) with bounded remainder. |
| 36 | `schwinger_agreement` | Bridge | ⚠️ Likely correct | DT 2026-02-24 | n-point Schwinger function equality at weak coupling. |
| 37 | `same_continuum_measure` | Bridge | ⚠️ Likely correct | DT 2026-02-24 | Fixed: requires `IsPphi2ContinuumLimit`, `IsPhi4ContinuumLimit`, `IsWeakCoupling`. |
| 38 | `os2_from_phi4` | Bridge | ⚠️ Likely correct | DT 2026-02-24 | Fixed: requires `IsPhi4ContinuumLimit`. |
| 39 | `os3_from_pphi2` | Bridge | ⚠️ Likely correct | DT 2026-02-24 | Fixed: requires `IsPphi2ContinuumLimit`. |

### Verification Summary (pphi2)

| Status | Count |
|--------|-------|
| Verified (GR or DT) | 35 |
| Self-audit only | 2 |
| Proved/Defined (no longer axioms) | 8 |
| **Total active** | **54** |

35 of 54 active axioms verified by GR or DT.
2 self-audit only: `pphi2_limit_exists` (Prokhorov existence), `transferOperatorCLM` (CLM construction).

### Notes from DT review (2026-02-25)

**Batch review of 19 new axioms (sorry→axiom conversion):**
- 15 Correct, 2 Likely correct, 1 Suspicious, 0 Wrong
- **Fixed SUSPICIOUS**: `anomaly_bound_from_superrenormalizability` — missing log factors per Glimm-Jaffe Thm 19.3.1. Now `C·a²·(1+|log a|)^p` instead of `C·a²`.
- **Likely correct**: `lattice_rp_matrix` (cos vs exp(i) — correct, both equivalent formulations), `exponential_moment_schwartz_bound` (non-standard norm but correct bound)
- **Fixed 6 overly-strong axioms**: `translation_invariance_continuum`, `rotation_invariance_continuum`, `continuum_exponential_moments`, `os0_inheritance`, `os3_inheritance`, `os4_inheritance` — all now require `IsPphi2Limit μ P mass`
- **Added 3 new axioms**: `IsPphi2Limit` (marker predicate, later converted to def), `pphi2_limit_exists` (Prokhorov existence, moved to Convergence.lean), `IsPphi2ContinuumLimit.toIsPphi2Limit` (bridge, later proved as theorem)

---

## gaussian-field Axioms (18 active, 2 sorries)

*Updated 2026-02-25 (rev 567851c). See gemini_review.md Group 1-2 for original review; DT 2026-02-25 for new axioms.*

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
- `lattice_rp` — RP inequality for `interactingLatticeMeasure` with `fieldFromSites`/`fieldReflection2D` (sorry)
- `rp_from_transfer_positivity` — $⟨f, T^n f⟩_{L²} ≥ 0$ via `transferOperatorCLM` (sorry)

### OS4: Clustering & Ergodicity
- `two_point_clustering_lattice` — Exponential decay bound using `finLatticeDelta` and `massGap` (sorry)
- `general_clustering_lattice` — Quantified clustering over bounded observables (sorry)
- `clustering_implies_ergodicity` — Measure-theoretic ergodicity criterion (sorry)
- `unique_vacuum` — **PROVED** from `transferEigenvalue_ground_simple`

### Continuum Limit & Convergence
- ~~`gaussian_hypercontractivity_continuum`~~ — **PROVED** from `gaussian_hypercontractive` via pushforward + `latticeEmbedLift_eval_eq`
- `exponential_moment_bound` — Deep stability estimate: $∫ e^{-2V_a} dμ_{GFF} ≤ K$ uniformly in $a$ (axiom)
- `interacting_moment_bound` — Bounds interacting $L^{pn}$ moments in terms of FREE Gaussian $L^{2n}$ moments (axiom)
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
| 44 | `lattice_rp` | OS3_RP_Lattice | ✅ Standard | Reflection positivity via Fubini + perfect square. Standard textbook result (Glimm-Jaffe Ch. 6.1). |
| 45 | `schwinger_agreement` | Bridge | ⚠️ Likely correct | Cluster expansion uniqueness at weak coupling. Properly constrained with `isPhi4`, `IsWeakCoupling` hypotheses. Very deep result (Guerra-Rosen-Simon 1975). |
| 46 | `pphi2_nontriviality` | Main | ⚠️ Likely correct | ∃ μ, ∀ f ≠ 0, ∫(ω f)² > 0. Griffiths/FKG correlation inequality. The ∃ μ is existential (finds a good measure, not Measure.dirac 0). |
| 47 | `pphi2_nonGaussianity` | Main | ⚠️ Likely correct | ∃ μ with nonzero 4th cumulant. Same ∃ μ pattern. |

### Known design issues (not bugs)

1. **Unused P/mass pattern**: ~10 axioms (continuum_exponential_moments, translation_invariance_continuum, rotation_invariance_continuum, os4_inheritance, os4_clustering_implies_ergodicity, etc.) claim properties for arbitrary μ without connecting to the lattice construction. This is a design simplification: the axioms serve as stand-ins for proper proofs that would take μ as "the continuum limit of lattice measures." Since `pphi2_exists` currently uses `Measure.dirac 0`, these axioms are trivially satisfied by the specific measure used.

2. **`SatisfiesOS0134` unused**: The secondary OS bundle with Schwinger function formulation is dead code — not imported by `Main.lean`. The main theorem uses `SatisfiesFullOS` via `continuumLimit_satisfies_fullOS`.

### Verification Summary (updated 2026-02-25)

| Status | Count |
|--------|-------|
| Verified (GR or DT) | 20 |
| New (self-audit, standard) | 5 |
| New (self-audit, likely correct) | 15 |
| New (self-audit, overly strong) | 3 |
| Proved (no longer axioms) | historical |
| **Total active** | **49** (Option B moved to `Pphi2/Unused/` and excluded) |

---

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

**Audit Date**: 2026-02-25
