# Comprehensive Axiom Audit: pphi2 + gaussian-field

**Updated**: 2026-02-24 (L2Operator.lean + spectral theorem, Bridge axioms fixed)
**pphi2**: 27 axioms | **gaussian-field**: 13 axioms | **Total**: 40

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

## pphi2 Axioms (27 active)

### Phase 1: Wick Ordering (2 axioms)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|-------|
| 1 | `wickMonomial_eq_hermite` | WickPolynomial:113 | ⚠️ Likely correct | GR Group 5 | :x^n:_c = c^{n/2} He_n(x/√c). Standard; check normalization convention. |
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
| 10 | `action_decomposition` | OS3_RP_Lattice:114 | ⚠️ Likely correct | GR Group 5 | S = S⁺ + S⁻ across time-reflection plane. Standard for nearest-neighbor actions. |
| 11 | `lattice_rp_matrix` | OS3_RP_Lattice:155 | ⚠️ Likely correct | DT 2026-02-24 | RP matrix Σ cᵢc̄ⱼ Z[fᵢ-Θfⱼ] ≥ 0. Support condition correct for periodic lattice. |

### Phase 3: Spectral Gap (2 axioms)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|-------|
| 12 | `spectral_gap_uniform` | SpectralGap:134 | ⚠️ Likely correct | GR Group 3 | ∃ m₀ > 0, gap(a) ≥ m₀ ∀a ≤ a₀. Central result of Glimm-Jaffe. VERY HARD. |
| 13 | `spectral_gap_lower_bound` | SpectralGap:145 | ⚠️ Likely correct | GR Group 3 | gap ≥ c·mass. Standard weak-coupling result. |

### Phase 4: Continuum Limit (11 axioms)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|-------|
| 11 | ~~`latticeEmbed`~~ | Embedding:136 | ✅ **PROVED** | DT 2026-02-24 | Constructed via `SchwartzMap.mkCLMtoNormedSpace`. |
| 12 | ~~`latticeEmbed_eval`~~ | Embedding:170 | ✅ **PROVED** | DT 2026-02-24 | `rfl` from construction. |
| 13 | ~~`latticeEmbed_measurable`~~ | Embedding | ✅ **PROVED** | DT 2026-02-24 | `configuration_measurable_of_eval_measurable` + `continuous_apply` for each coordinate. |
| 14 | `latticeEmbedLift` | Embedding:151 | ⚠️ Likely correct | DT 2026-02-24 | Lifted embedding on Configuration space. Domain matches `interactingLatticeMeasure`. |
| 15 | `latticeEmbedLift_measurable` | Embedding:156 | ✅ Standard | DT 2026-02-24 | Lifted embedding measurable. Continuous → measurable. |
| 16 | `second_moment_uniform` | Tightness:74 | ⚠️ Likely correct | GR Group 4 | ∫ Φ_a(f)² dν_a ≤ C(f). Nelson's hypercontractive estimate. |
| 17 | `moment_equicontinuity` | Tightness:89 | ❓ Needs review | GR Group 4 | **⚠️ WRONG AS STATED** per gemini review. RHS must depend on ‖f-g‖_s, not bare constant. |
| 18 | `continuumMeasures_tight` | Tightness:110 | ⚠️ Likely correct | GR Group 4 | Mitoma criterion + moment bounds. |
| 19 | `configuration_polishSpace` | Convergence:173 | ✅ Standard | DT 2026-02-24 | S'(ℝ^d) Polish. Gelfand-Vilenkin Vol. 4, Bogachev §3.2. |
| 20 | `configuration_borelSpace` | Convergence:180 | ✅ Standard | DT 2026-02-24 | Borel = cylindrical σ-algebra. Bochner-Minlos framework. |
| 21 | `os0_inheritance` | AxiomInheritance:78 | ⚠️ Likely correct | GR Group 4 | OS0 transfers. GR notes: "TRUE but TOO WEAK" — should include factorial growth (E0'). |

### Phase 5: Euclidean Invariance (1 axiom)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|-------|
| 22 | `rotationBreakingOperator` | OS2_WardIdentity:177 | ⚠️ Likely correct | GR Group 5 | O_break with dim=4. Symanzik improvement: anomaly RG-irrelevant in d=2. |

### Phase 6: Bridge (5 axioms)

| # | Name | File:Line | Rating | Verified | Notes |
|---|------|----------|--------|----------|-------|
| 23 | `measure_determined_by_schwinger` | Bridge:152 | ⚠️ Likely correct | DT 2026-02-24 | Moment determinacy with exponential (Fernique-type) moment bound. Fixed from polynomial→exponential per DT review. |
| 24 | `wick_constant_comparison` | Bridge:180 | ✅ Standard | DT 2026-02-24 | Wick constant ≈ (2π)⁻¹ log(1/a) with bounded remainder. Standard asymptotics. |
| 25 | `same_continuum_measure` | Bridge:222 | ⚠️ Likely correct | DT 2026-02-24 | Fixed: now requires `IsPphi2ContinuumLimit`, `IsPhi4ContinuumLimit`, `IsWeakCoupling` hypotheses. Was ❓ (vacuous), now properly constrained. |
| 26 | `os2_from_phi4` | Bridge:255 | ⚠️ Likely correct | DT 2026-02-24 | Fixed: now requires `IsPhi4ContinuumLimit` hypothesis (was FALSE without it). |
| 27 | `os3_from_pphi2` | Bridge:300 | ⚠️ Likely correct | DT 2026-02-24 | Fixed: now requires `IsPphi2ContinuumLimit` hypothesis (was FALSE without it). |

### Verification Summary (pphi2)

| Status | Count |
|--------|-------|
| Verified (GR or DT) | 24 |
| New (L2Operator, self-audit only) | 3 |
| Proved (no longer axioms) | 3 |
| **Total active** | **27** |

25 of 28 axioms verified by GR or DT. 3 new L2Operator axioms (CLM, self-adjoint, compact) are standard and self-audited.

### Notes from DT review (2026-02-24)

- `latticeEmbed`, `latticeEmbed_eval`, `latticeEmbed_measurable` are constructible — should be converted from axioms to defs/theorems
- `latticeEmbedLift` domain is `Configuration (FinLatticeField d N)` which matches `interactingLatticeMeasure` type (the gaussian-field library wraps all field spaces in `Configuration E = WeakDual ℝ E`)

---

## gaussian-field Axioms (21 active)

*Counts from `count_axioms.sh` 2026-02-24. See gemini_review.md Group 1-2 for detailed review of heat kernel and FKG axioms.*

| File | Count | Verified | Notes |
|------|-------|----------|-------|
| HeatKernel/PositionKernel.lean | 9 | GR Group 1 | All standard heat kernel facts. |
| Lattice/FKG.lean | 6 | GR Group 2 | FKG lattice condition, Gaussian FKG, perturbed FKG. |
| Lattice/Laplacian.lean | 2 | GR Group 2 | Infinite lattice Laplacian (not used by pphi2). |
| Lattice/RapidDecayLattice.lean | 4 | GR Group 2 | Shell enumeration, rapid decay equiv. |
| **Total** | **21** | | |

---

## Critical Issues

### 1. ~~❓ `same_continuum_measure`~~ — FIXED (2026-02-24)

**Status**: RESOLVED. Now requires `IsPphi2ContinuumLimit`, `IsPhi4ContinuumLimit`, and `IsWeakCoupling` hypotheses. Also fixed `os2_from_phi4` (was FALSE without `IsPhi4ContinuumLimit`), `os3_from_pphi2` (was FALSE without `IsPphi2ContinuumLimit`), and `measure_determined_by_schwinger` (polynomial→exponential moments).

### 2. ❓ `moment_equicontinuity` (Tightness:89)

**Severity**: MEDIUM — Verified but flagged **WRONG** by GR
**Issue**: RHS is bare constant C, should be C·‖f-g‖_s in Schwartz/Sobolev norm.
**Action**: Correct the bound to depend on ‖f-g‖_s.

### 3. ⚠️ `os0_inheritance` (AxiomInheritance:78)

**Severity**: LOW — Verified but flagged **TOO WEAK** by GR
**Issue**: States all moments finite, but OS0 requires factorial growth bound (E0' condition).
**Action**: Strengthen to include growth bound.

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

**Audit Date**: 2026-02-24
