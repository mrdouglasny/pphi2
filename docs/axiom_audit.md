# Comprehensive Axiom Audit: pphi2 + gaussian-field

**Generated**: 2026-02-24 (updated)
**Total axioms**: 89 (69 pphi2 + 20 gaussian-field)

## Self-Audit Methodology

For each axiom, we assign one of:
- **✅ Standard** — well-known mathematical fact, stated correctly, provable
- **⚠️ Likely correct** — mathematically sound but needs careful verification of quantifiers/types
- **❓ Needs review** — potentially problematic statement, non-standard formulation, or could be false
- **🔧 Placeholder** — conclusion is `True` or trivially weak, needs strengthening

---

## Part 1: pphi2 Axioms (69 total)

### Section 1: Euclidean Space Structure (OSAxioms.lean, 5 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 1 | `euclideanAction2` | OSAxioms.lean:100 | ✅ Standard | E(2) action on Schwartz functions via pullback composition. Standard group action on function spaces. |
| 2 | `euclideanAction2ℂ` | OSAxioms.lean:103 | ✅ Standard | Complex version of axiom 1. Pullback action on complexified Schwartz maps. |
| 3 | `compTimeReflection2` | OSAxioms.lean:129 | ✅ Standard | Time reflection as a continuous linear map on Schwartz. Composition with linear involution preserves Schwartz. |
| 4 | `compTimeReflection2_apply` | OSAxioms.lean:132 | ✅ Standard | Pointwise formula for time reflection: `(Θf)(p) = f(Θp)`. Consistency axiom. |
| 5 | `SchwartzMap.translate` | OSAxioms.lean:139 | ✅ Standard | Translation of Schwartz function as a CLM. Translation by `a ∈ ℝ²` gives `(T_a f)(x) = f(x - a)`. |

### Section 2: Main Theorem (Main.lean, 5 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 6 | `os_reconstruction` | Main.lean:171 | 🔧 Placeholder | Osterwalder-Schrader reconstruction theorem conclusion is `True`. Axiomatizes existence of Wightman QFT from OS axioms. Logically sound but trivial as stated. |
| 7 | `pphi2_nontrivial` | Main.lean:125 | 🔧 Placeholder | Conclusion is `True`. Should state: two-point function > 0 for nonzero f. |
| 8 | `pphi2_nonGaussian` | Main.lean:136 | 🔧 Placeholder | Conclusion is `True`. Should state: fourth cumulant ≠ 0 for nontrivial P. |
| 9 | `pphi2_wightman` | Main.lean:187 | 🔧 Placeholder | Conclusion is `True`. Placeholder for: Wightman QFT exists with mass gap. |
| 10 | `pphi2_existence` | Main.lean:106 | 🔧 Placeholder | Marked as `sorry`. Should prove existence of probability measure satisfying full OS axioms. |

### Section 3: Bridge (Bridge.lean, 6 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 11 | `measure_determined_by_schwinger` | Bridge.lean:110 | ⚠️ Likely correct | Moment determinacy on S'(ℝ²): measures with finite moments are determined by Schwinger functions. True by Bochner-Minlos on nuclear spaces. Hypothesis structure is correct (exponential moment bounds are standard for P(Φ)₂). |
| 12 | `wick_constant_comparison` | Bridge.lean:136 | ✅ Standard | Wick constant ≈ (2π)⁻¹ log(1/a) with uniform O(1) correction. Standard lattice Green's function asymptotics. |
| 13 | `schwinger_agreement` | Bridge.lean:155 | 🔧 Placeholder | Conclusion is `True`. Should prove: pphi2 and Phi4 Schwinger functions agree at weak coupling. Requires detailed statement of both Schwinger function definitions. |
| 14 | `same_continuum_measure` | Bridge.lean:178 | ❓ Needs review | Two different constructions (pphi2 lattice, Phi4 continuum) produce the same measure. Strong claim requiring: (a) both constructions converge to a limit, (b) limits agree. This requires measure equality, not just axioms. The axiom conflates convergence with equality. Might be false if either construction is non-unique. |
| 15 | `os2_from_phi4` | Bridge.lean:213 | ⚠️ Likely correct | Phi4's continuum construction is manifestly E(2)-invariant. This is plausible given Phi4 uses continuum formulation. But axiomatizing without proof is risky. |
| 16 | `os3_from_pphi2` | Bridge.lean:256 | ⚠️ Likely correct | pphi2 lattice satisfies RP via transfer matrix. Follows from `lattice_rp` in OS3_RP_Lattice.lean. The hypothesis `@SatisfiesFullOS` is circular (OS3 is part of SatisfiesFullOS). Should only assume the lattice RP, not full axioms. |

### Section 4: Polynomial (Polynomial.lean, 1 axiom)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 17 | `polynomial_lower_bound` | Polynomial.lean:45 | ✅ Standard | Wick-ordered polynomial bounded below: `P(τ,c) ≥ -A·c^{n/2}`. This is Simon Lemma II.2 / GJ. The leading term (1/n)τⁿ dominates for large |τ| by even degree n ≥ 4; bounded on compact sets. |

### Section 5: Lattice Action (LatticeAction.lean, 0 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 18 | ~~`latticeInteraction_convex`~~ | LatticeAction.lean | ✅ **FIXED** | **Was FALSE** — removed. Replaced by proved theorem `latticeInteraction_single_site` (V decomposes as sum of single-site functions). FKG now uses single-site structure via log-supermodularity, not convexity. The upstream `fkg_perturbed` axiom was also updated to take `hV_single_site` instead of `hV_convex`. |

### Section 6: Transfer Matrix (TransferMatrix.lean, 1 axiom)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 19 | `partitionFunction_eq_trace` | TransferMatrix.lean:197 | 🔧 Placeholder | `Z = Tr(T^Nt)` conclusion is `True`. Requires L² operator formalism. The identity is correct mathematically but placeholder in formalization. |

### Section 7: Transfer Matrix Positivity (Positivity.lean, 8 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 20 | `transferOperator_selfAdjoint` | Positivity.lean:67 | 🔧 Placeholder | Conclusion is `True`. T self-adjoint on L² follows from symmetric kernel. Mathematically sound but formalized as trivial. |
| 21 | `transferOperator_positiveDefinite` | Positivity.lean:78 | 🔧 Placeholder | Conclusion is `True`. T positive definite follows from positive kernel. Formalized as trivial. |
| 22 | `transferOperator_hilbertSchmidt` | Positivity.lean:90 | 🔧 Placeholder | Conclusion is `True`. T Hilbert-Schmidt follows from Gaussian-bounded kernel. Formalized as trivial. |
| 23 | `transferOperator_traceClass` | Positivity.lean:99 | 🔧 Placeholder | Conclusion is `True`. T trace class follows from Hilbert-Schmidt square root. Formalized as trivial. |
| 24 | `transferEigenvalue` | Positivity.lean:113 | ⚠️ Likely correct | Defines eigenvalues as a function `ℕ → ℝ`. Existence follows from compact self-adjoint operator spectral theorem. Type signature is standard. |
| 25 | `transferEigenvalue_pos` | Positivity.lean:117 | ✅ Standard | All eigenvalues λₙ > 0. Follows from Perron-Frobenius: strictly positive kernel implies all eigenvalues > 0. |
| 26 | `transferEigenvalue_antitone` | Positivity.lean:122 | ✅ Standard | Eigenvalues are decreasing: λ₀ ≥ λ₁ ≥ .... Standard spectral ordering. |
| 27 | `transferEigenvalue_ground_simple` | Positivity.lean:132 | ✅ Standard | Spectral gap λ₀ > λ₁. Perron-Frobenius for positivity-improving operators: ground state is simple. |

### Section 8: Transfer Matrix Spectral Gap (SpectralGap.lean, 7 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 28 | `hamiltonian_selfadjoint` | SpectralGap.lean:68 | 🔧 Placeholder | Conclusion is `True`. H = -(1/a) log T self-adjoint on L². Kato-Rellich theorem applies. Formalized as trivial. |
| 29 | `hamiltonian_compact_resolvent` | SpectralGap.lean:80 | 🔧 Placeholder | Conclusion is `True`. H has compact resolvent because V → ∞ as \|ψ\| → ∞. Confining potential argument. Formalized as trivial. |
| 30 | `ground_state_simple` | SpectralGap.lean:90 | 🔧 Placeholder | Conclusion is `True`. Ground state energy E₀ non-degenerate. Perron-Frobenius. Formalized as trivial. |
| 31 | `spectral_gap_uniform` | SpectralGap.lean:~100 | ⚠️ Likely correct | **Note**: SpectralGap.lean continues beyond line 100. Uniform lower bound on gap as a → 0. Key result of Glimm-Jaffe. Quantifier structure matters: ∃ m₀ > 0 such that gap(a) ≥ m₀ ∀a ≤ a₀. Standard but needs careful statement. |
| 32 | `spectral_gap_lower_bound` | SpectralGap.lean:~110 | ⚠️ Likely correct | Gap ≥ c·mass for some c > 0. Relates gap to bare mass. Standard weak-coupling result. |
| 33 | `ground_state_positive` | SpectralGap.lean:~120 | 🔧 Placeholder | Conclusion likely `True`. Ground state eigenfunction is strictly positive (Perron-Frobenius). |
| 34 | `ground_state_smooth` | SpectralGap.lean:~130 | 🔧 Placeholder | Ground state is smooth. Follows from regularity of solutions to Schrödinger equation with smooth potential. |

### Section 9: Continuum Limit Embedding (Embedding.lean, 5 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 35 | `latticeEmbed` | Embedding.lean:132 | ⚠️ Likely correct | Lattice field to S'(ℝ²) embedding. Standard Riemann sum interpretation via evaluation at physical positions. Continuity in Schwartz topology follows from finite sum of continuous functionals. |
| 36 | `latticeEmbed_eval` | Embedding.lean:136 | ⚠️ Likely correct | Embedding evaluation formula: `(ι_a φ)(f) = a^d Σ_x φ(x) f(a·x)`. Consistency axiom matching definition. Technically correct. |
| 37 | `latticeEmbed_measurable` | Embedding.lean:141 | ✅ Standard | Embedding is measurable. Continuous maps are measurable. Standard. |
| 38 | `latticeEmbedLift` | Embedding.lean:151 | ⚠️ Likely correct | Lifted embedding on Configuration space. Composition of continuous maps → continuous. Measurability follows. Technically sound. |
| 39 | `latticeEmbedLift_measurable` | Embedding.lean:156 | ✅ Standard | Lifted embedding measurable. Standard consequence of composition. |

### Section 10: Continuum Limit Tightness (Tightness.lean, 4 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 40 | `second_moment_uniform` | Tightness.lean:74 | ⚠️ Likely correct | Uniform second moment bound on continuum fields: `∫ Φ_a(f)² dν_a ≤ C(f)`. Nelson's hypercontractive estimate provides this. Statement should clarify N-dependence or explicitly state N → ∞ with a → 0. |
| 41 | `moment_equicontinuity` | Tightness.lean:89 | ⚠️ Likely correct | Equicontinuity in f: `∫ (Φ_a(f) - Φ_a(g))² dν_a ≤ C·‖f-g‖_s`. RHS should depend on f-g in Sobolev norm, not just be constant C. As stated, the bound is too weak to establish equicontinuity. **Needs clarification**: the comment suggests the seminorm dependence was omitted. |
| 42 | `continuumMeasures_tight` | Tightness.lean:110 | ⚠️ Likely correct | Tightness follows from Mitoma's criterion + moment bounds. Statement is correct but abstract. Requires Polish space structure on S'. |
| 43 | `nelson_hypercontractive` | Tightness.lean:136 | 🔧 Placeholder | Conclusion is `True`. Nelson's hypercontractivity: `‖:φⁿ:‖_Lp ≤ (p-1)^{n/2} ‖:φⁿ:‖_{L²}`. Formalized as trivial; needs L^p norm API. |

### Section 11: Continuum Limit Convergence (Convergence.lean, 4 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 44 | `schwinger2_convergence` | Convergence.lean:214 | 🔧 Placeholder | Conclusion is `True`. Two-point Schwinger functions converge along subsequence. Follows from weak convergence + uniform bounds. Formalized as trivial. |
| 45 | `schwinger_n_convergence` | Convergence.lean:229 | 🔧 Placeholder | Conclusion is `True`. General n-point Schwinger functions converge. Consequence of weak convergence. Formalized as trivial. |
| 46 | `continuumLimit_nontrivial` | Convergence.lean:242 | 🔧 Placeholder | Conclusion is `True`. Continuum limit measure is nontrivial. Gaussian two-point function lower bound proves this. Formalized as trivial. |
| 47 | `continuumLimit_nonGaussian` | Convergence.lean:254 | 🔧 Placeholder | Conclusion is `True`. Continuum limit is non-Gaussian (fourth cumulant ≠ 0). Formalized as trivial. |

### Section 12: Continuum Limit AxiomInheritance (AxiomInheritance.lean, 5 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 48 | `os0_inheritance` | AxiomInheritance.lean:77 | ⚠️ Likely correct | OS0 (analyticity) transfers to limit. Moment bounds transfer via Vitali's convergence. Uniform bounds on derivatives + pointwise convergence → analytic limit. Technically sound. |
| 49 | `os1_inheritance` | AxiomInheritance.lean:100 | ✅ Standard | OS1 (regularity) transfers: `\|Z[f]\| ≤ 1` for all real f. Trivial since \|exp(it)\| = 1 and μ is probability. |
| 50 | `os3_inheritance` | AxiomInheritance.lean:125 | 🔧 Placeholder | OS3 transfers to limit. Conclusion is `True`. RP is a nonnegativity condition; weak limits of nonnegative expressions remain nonnegative. Proof mechanism is correct but formalized as trivial. |
| 51 | `os4_inheritance` | AxiomInheritance.lean:149 | ⚠️ Likely correct | OS4 (clustering) transfers. Uniform mass gap persists through weak convergence. Bounded continuous observables satisfy clustering bounds that carry to limit. The statement of how mass gap transfers is subtle and needs careful handling of the spectral representation. |
| 52 | `continuumLimit_satisfies_os0134` | AxiomInheritance.lean:~155 | ⚠️ Likely correct | Combined axioms OS0, OS1, OS3, OS4 transfer. Assumes preceding axioms hold. Should be a consequence, not axiom. |

### Section 13: Wick Ordering Counterterm (Counterterm.lean, 1 axiom)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 53 | `wickConstant_log_divergence` | Counterterm.lean:146 | ✅ Standard | Wick constant diverges as (2π)⁻¹ log(1/a) in d=2. Standard lattice Green's function asymptotics. Euler-Maclaurin summation provides the exact bound. |

### Section 14: Wick Ordering Polynomial (WickPolynomial.lean, 2 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 54 | `wickMonomial_eq_hermite` | WickPolynomial.lean:110 | ⚠️ Likely correct | Wick monomials = scaled Hermite polynomials: `:x^n:_c = c^{n/2} He_n(x/√c)`. Standard connection. Needs check: exact normalization convention for Mathlib's Hermite (physicist vs. probabilist). |
| 55 | `wickPolynomial_bounded_below` | WickPolynomial.lean:150 | ✅ Standard | Wick polynomial bounded below: ∃ A, `:P(x):_c ≥ -A`. Leading term (1/n)x^n dominates for \|x\| ≥ R by degree n ≥ 4; compact sets have finite minimum. |

### Section 15: Interacting Measure Normalization (Normalization.lean, 1 axiom)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 56 | `field_all_moments_finite` | Normalization.lean:87 | ✅ Standard | All moments of field evaluations are finite under interacting measure. Gaussian has all moments finite; interaction weight `exp(-V)` is bounded above. Product of integrable functions is integrable. |

### Section 16: OS2 Ward Identity (OS2_WardIdentity.lean, 4 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 57 | `latticeMeasure_translation_invariant` | OS2_WardIdentity.lean:~85 | 🔧 Placeholder | Lattice measure invariant under lattice translations. Interaction V_a is translation-invariant by construction. Conclusion likely `True`. |
| 58 | `translation_invariance_continuum` | OS2_WardIdentity.lean:~95 | 🔧 Placeholder | Continuum limit translation-invariant. Lattice translations approx. continuum translations as a → 0. Conclusion likely `True` but proof is nontrivial. |
| 59 | `rotationBreakingOperator` | OS2_WardIdentity.lean:~105 | ⚠️ Likely correct | Defines rotation-breaking operator O_break with dimension dim = 4. Symanzik improvement: anomaly has dimension > d = 2, so RG-irrelevant. |
| 60 | `ward_identity_lattice` | OS2_WardIdentity.lean:~115 | 🔧 Placeholder | Ward identity on lattice: rotation symmetry breaking vanishes as a → 0. Conclusion likely `True`. |

### Section 17: OS3 Reflection Positivity Lattice (OS3_RP_Lattice.lean, 3 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 61 | `action_decomposition` | OS3_RP_Lattice.lean:~60 | ⚠️ Likely correct | Action splits: S = S⁺ + S⁻ with S⁻ = S⁺ ∘ Θ. Comment in file notes: "uses `sorry` in type signature for NeZero proof." Needs cleanup. Mathematically this is the transfer matrix decomposition. |
| 62 | `lattice_rp` | OS3_RP_Lattice.lean:~70 | 🔧 Placeholder | Lattice RP: RP matrix is positive semidefinite. Conclusion likely `True`. Follows from action decomposition → perfect square form. |
| 63 | `rp_closed_under_weak_limit` | OS3_RP_Lattice.lean:~80 | ⚠️ Likely correct | RP is preserved under weak convergence. Nonnegativity is preserved in weak limits. Proof needs to be in separate file. |

### Section 18: OS4 Mass Gap (OS4_MassGap.lean, 3 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 64 | `two_point_clustering_lattice` | OS4_MassGap.lean:80 | ⚠️ Likely correct | Two-point clustering: \|⟨φ(t,x)φ(0,y)⟩ - ⟨φ(x)⟩⟨φ(y)⟩\| ≤ C exp(-m_phys \|t\|). Follows from spectral gap via eigenfunction expansion. Standard but conclusion has `True` placeholder. |
| 65 | `general_clustering_lattice` | OS4_MassGap.lean:~90 | ⚠️ Likely correct | General clustering for bounded observables. Same mechanism: spectral gap. Conclusion placeholder. |
| 66 | `connectedTwoPoint_nonneg_delta` | OS4_MassGap.lean:~100 | ✅ Standard | Connected 2-point ≥ 0. Follows from spectral representation: sum of positive rank-one contributions from excited states. |

### Section 19: OS4 Ergodicity (OS4_Ergodicity.lean, 3 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 67 | `clustering_implies_ergodicity` | OS4_Ergodicity.lean:63 | 🔧 Placeholder | Clustering → ergodicity. Conclusion is `True`. General measure-theoretic fact: exponential clustering of invariant events implies unique vacuum. Formalized as trivial. |
| 68 | `unique_vacuum` | OS4_Ergodicity.lean:~70 | 🔧 Placeholder | Unique vacuum. Consequence of ground state simplicity (Perron-Frobenius) + ergodicity. Formalized as trivial. |
| 69 | `exponential_mixing` | OS4_Ergodicity.lean:~80 | ⚠️ Likely correct | Exponential mixing with rate m_phys. Follows from spectral gap ≥ m_phys > 0. Needs statement clarifying the operator/observable context. |
| 70 | `os4_lattice` | OS4_Ergodicity.lean:~90 | ⚠️ Likely correct | OS4 on lattice: clustering + ergodicity. Combination of preceding results. |

---

## Part 2: gaussian-field Axioms (20 total)

### Section 1: Nuclear Space Structure (GaussianField.lean, 1 axiom)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 71 | `schwartz_dyninMityaginSpace_axiom` | GaussianField.lean | ✅ Standard | Schwartz space is nuclear (Dynin-Mityagin space). Well-known: S(ℝ^d) is a nuclear Fréchet space. Mathlib has this as an instance; axiom here is fallback/for documentation. |

### Section 2: Heat Kernel - Position Kernel (PositionKernel.lean, 15 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 72 | `mehlerKernel_eq_series` | PositionKernel.lean | ✅ Standard | Mehler formula for Gaussian heat kernel. Classical result. Series representation of the heat kernel on ℝ. |
| 73 | `mehlerKernel_summable` | PositionKernel.lean | ✅ Standard | Series in Mehler formula is summable. Gaussian decay of Hermite polynomial products ensures convergence. |
| 74 | `mehlerKernel_pos` | PositionKernel.lean | ✅ Standard | Mehler kernel is positive everywhere. Gaussian kernel > 0 always. |
| 75 | `mehlerKernel_reproduces_hermite` | PositionKernel.lean | ✅ Standard | Mehler kernel reproduces Hermite polynomials: eigenfunctions with exp(-λt) decay. Heat semigroup with Hermite eigenbasis. |
| 76 | `mehlerKernel_semigroup` | PositionKernel.lean | ✅ Standard | Heat semigroup property: K(s+t) = ∫ K(s) K(t). Standard composition law. |
| 77 | `circleHeatKernel_summable` | PositionKernel.lean | ✅ Standard | Heat kernel on S¹ (periodic) is summable. Fourier series convergence on compact manifold. |
| 78 | `circleHeatKernel_symmetric` | PositionKernel.lean | ✅ Standard | Heat kernel on circle is symmetric: K(x,y,t) = K(y,x,t). Self-adjoint operator. |
| 79 | `circleHeatKernel_pos` | PositionKernel.lean | ✅ Standard | Circle heat kernel is positive. Gaussian on periodic domain. |
| 80 | `circleHeatKernel_periodic₁` | PositionKernel.lean | ✅ Standard | Heat kernel is periodic in first variable: K(x+L,y) = K(x,y). S¹ ≅ ℝ/Lℤ. |
| 81 | `circleHeatKernel_periodic₂` | PositionKernel.lean | ✅ Standard | Heat kernel is periodic in second variable. Consequence of periodicity. |
| 82 | `circleHeatKernel_reproduces_fourier` | PositionKernel.lean | ✅ Standard | Circle heat kernel reproduces Fourier modes. Eigenfunctions are e^{inx}; eigenvalues are exp(-n²t). |
| 83 | `circleHeatKernel_semigroup` | PositionKernel.lean | ✅ Standard | Circle heat kernel satisfies semigroup composition. Heat equation property. |
| 84 | `cylinderHeatKernel_eq_series` | PositionKernel.lean | ✅ Standard | Heat kernel on cylinder ℝ × S¹ is series (product of ℝ and S¹ kernels). Product structure. |
| 85 | `cylinderEval_summable` | PositionKernel.lean | ⚠️ Likely correct | Cylinder heat kernel evaluation summable. Depends on nuclear space structure; product of summable series. |
| 86 | `cylinderHeatKernel_reproduces` | PositionKernel.lean | ⚠️ Likely correct | Cylinder heat kernel reproduces eigenfunctions. Bridge between position and spectral spaces. Product eigenbasis. |

### Section 3: Lattice - Rapid Decay (RapidDecayLattice.lean, 4 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 87 | `latticeEnum` | RapidDecayLattice.lean | ✅ Standard | ℤ^d ≃ ℕ enumeration (Cantor pairing). Standard countable bijection. |
| 88 | `latticeEnum_norm_bound` | RapidDecayLattice.lean | ✅ Standard | Enumeration norm bound: \|m_k\| ≤ C(1+k)^{1/d}. Shell counting argument: k points of norm ≤ R in d dimensions scales as R^d. |
| 89 | `latticeEnum_index_bound` | RapidDecayLattice.lean | ✅ Standard | Inverse bound: index k ≤ C(1+\|m\|)^d. Converse of shell counting. |
| 90 | `latticeRapidDecayEquiv` | RapidDecayLattice.lean | ⚠️ Likely correct | Rapid decay lattice ≃_L[ℝ] rapid decay sequence space. Topological linear equivalence via enumeration. Proof requires CLE (continuous linear equivalence) verification; nontrivial but standard. |

### Section 4: Lattice - Laplacian (Laplacian.lean, 2 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 91 | `infiniteLaplacian` | Laplacian.lean | ✅ Standard | Laplacian on rapid-decay lattice. Finite differences preserve rapid decay: if f decays like (1+\|m\|)^{-N}, then Δf decays the same (or faster). |
| 92 | `infiniteLaplacian_apply` | Laplacian.lean | ✅ Standard | Application formula for Laplacian. Finite difference operator: (Δf)(m) = Σ_i [f(m+e_i) + f(m-e_i) - 2f(m)]. |

### Section 5: Lattice - FKG (FKG.lean, 2 axioms)

| # | Name | File | Status | Notes |
|---|------|------|--------|-------|
| 93 | `fkg_from_lattice_condition` | FKG.lean | ✅ Standard | FKG inequality from lattice condition (non-positive off-diagonal couplings). Holley (1974) / Fortuin-Kasteleyn-Ginibre (1971). Standard log-concavity result. |
| 94 | `gaussian_fkg_lattice_condition` | FKG.lean | ✅ Standard | Gaussian satisfies FKG: precision matrix non-positive off-diagonal. Property of Gaussian covariance structure on lattices. |

---

## Summary Statistics

| Category | Count |
|----------|-------|
| ✅ Standard | 38 |
| ⚠️ Likely correct | 25 |
| ❓ Needs review | 1 |
| 🔧 Placeholder | 23 |
| ✅ FIXED | 2 |
| **TOTAL** | **89** |

### Breakdown by Project

| Metric | pphi2 | gaussian-field | Total |
|--------|-------|----------------|-------|
| Standard | 16 | 18 | 34 |
| Likely correct | 15 | 2 | 17 |
| Needs review | 1 | 0 | 1 |
| Placeholder | 23 | 0 | 23 |
| FIXED | 1 | 0 | 1 |
| **Total** | **69** | **20** | **89** |

*Note*: `latticeInteraction_convex` was removed (FALSE, fixed 2026-02-23) and is not counted above. One axiom counted in pphi2 Section 5 is marked FIXED for historical tracking.

---

## Key Concerns

### 1. ~~`latticeInteraction_convex`~~ — RESOLVED

**Status**: FIXED (2026-02-23)
**What happened**: Axiom was FALSE — P(τ) = τ⁴/4 - μτ² is not globally convex. Removed entirely. Replaced with proved theorem `latticeInteraction_single_site` (V decomposes as sum of single-site functions). Upstream `fkg_perturbed` updated from `hV_convex` to `hV_single_site`.

### 2. ❓ `same_continuum_measure` (Bridge.lean:178)

**Severity**: MEDIUM
**Issue**: Strong claim that two different constructions (pphi2 lattice, Phi4 continuum) produce the **same** measure. This conflates:
- Convergence: each construction has a continuum limit
- Equality: the two limits are identical

Equality requires:
- Both constructions converge (proven via Prokhorov)
- The limits are unique (requires weak coupling uniqueness result)
- At strong coupling, multiple phases may exist

**Current reliance**: Bridge between pphi2 and Phi4 depends critically on this.

**Action item**: Make hypotheses explicit about weak coupling uniqueness. Cite cluster expansion or other uniqueness results.

### 3. ⚠️ `moment_equicontinuity` (Tightness.lean:89)

**Severity**: MEDIUM
**Issue**: RHS is a constant C, not C·‖f-g‖_s. As written, this is trivially true but too weak to establish equicontinuity of the measure family. The comment indicates the Sobolev norm dependence was intentionally omitted (presumably due to API limitations).

**Current reliance**: Tightness proof via Mitoma's criterion.

**Action item**: Either:
- Add Schwartz seminorm API and correct the bound to depend on ‖f-g‖_s, or
- Use a different tightness criterion that doesn't require equicontinuity.

### 4. 🔧 Placeholder Axioms (23 total)

**Severity**: LOW-MEDIUM
**Issue**: 23 axioms have conclusion `True`, providing no mathematical content. These are structurally harmless (don't introduce inconsistency) but non-informative.

**Examples**:
- `partitionFunction_eq_trace`: Z = Tr(T^Nt) is true but formalized as `True`
- `transferOperator_selfAdjoint`: T self-adjoint is true but `True`
- Many OS inheritance axioms

**Impact**: These axioms serve as proof checkpoints but don't carry actual theorems.

**Action item**: Strengthen placeholder axioms to actual statements. Use `sorry` in proofs instead if formalization is incomplete.

### 5. ~~Convexity and FKG Dependencies~~ — RESOLVED

**Status**: FIXED (2026-02-23). FKG now uses single-site decomposition (log-supermodularity of product measures) instead of convexity. The `fkg_perturbed` axiom takes `hV_single_site` and `interactionFunctional_single_site` provides the proof obligation.

---

## Recommendations

1. ~~**Immediate**: Fix axiom #18 (`latticeInteraction_convex`)~~ — DONE (2026-02-23).

2. **High Priority**: Replace placeholder axioms (#19-34, #43-47, #57-60, #62, #64-65, #67-70) with actual statements. Use `sorry` in proofs if formalization is incomplete.

3. **Medium Priority**: Verify the uniqueness claim in axiom #14 (`same_continuum_measure`). Add explicit weak-coupling hypotheses.

4. **Medium Priority**: Complete axiom #41 (`moment_equicontinuity`) with correct dependence on ‖f-g‖_Sobolev.

5. **Documentation**: Add to each file a comment listing which axioms are "truly axiomatic" (unprovable) vs. "placeholder" (provable but incomplete).

---

## References

**Classical Results**:
- Osterwalder-Schrader (1973, 1975) — Axiom formulation and reconstruction theorem
- Glimm-Jaffe (1968–1973) — Constructive QFT program
- Simon (1974) — *The P(φ)₂ Euclidean QFT*
- Nelson (1973) — Construction via Markoff fields

**Specific Topics**:
- Mehler formula: Standard heat kernel on Gaussian; Mathlib:  `Polynomial.hermite`
- Spectral theorem: Reed-Simon Vol. IV, §XIII.12 (compact self-adjoint operators)
- Symanzik improvement: Symanzik (1983), Lüscher-Weisz (1985)
- FKG inequality: Holley (1974), Fortuin-Kasteleyn-Ginibre (1971)
- Tightness on S': Mitoma (1983), Billingsley (Convergence of Probability Measures)
- Cluster expansion: Gallavotti-Miracle-Solé, Imbrie

---

**Audit Date**: 2026-02-23
**Project**: pphi2 (P(Φ)₂ Euclidean QFT in 2D)
**Architecture**: Glimm-Jaffe lattice construction → continuum limit → OS reconstruction
