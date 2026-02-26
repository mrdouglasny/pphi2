# pphi2 Axiom Proof Plans

**Generated**: 2026-02-25 via Gemini deep think review
**Total**: 46 axioms, 0 sorries (plus 5 Option B)

> Update (2026-02-26): `transferOperator_isSelfAdjoint` is now proved in
> `TransferMatrix/L2Operator.lean`. The remaining analytic gap is tracked as
> `convCLM_isSelfAdjoint_of_even` in `TransferMatrix/L2Convolution.lean`.

## Priority Order

### Tier 1: EASY (standard arguments, conditional on infrastructure)

#### 1. ~~`transferOperator_isSelfAdjoint`~~ (L2Operator.lean)

**Status**: **PROVED**.

Theorem now follows by operator algebra from
`mulCLM_isSelfAdjoint` and the convolution self-adjointness bridge axiom.

**Follow-up target**: prove `convCLM_isSelfAdjoint_of_even` directly (Fubini
with product-integrand integrability).

---

#### 2. `transferOperator_isCompact` (L2Operator.lean:135)

**Statement**: The transfer operator T is compact on L^2 spatial field space.

**Plan**:
1. In the construction of T (transferOperatorCLM), T is shown to be Hilbert-Schmidt
2. Mathlib has: every Hilbert-Schmidt operator is compact
3. Apply `HilbertSchmidt.toCompactOperator`

**Key Mathlib**: `HilbertSchmidt.toCompactOperator`
**Depends on**: `transferOperatorCLM`
**Difficulty**: EASY (conditional on transfer operator construction)

---

#### 3. `transferEigenvalue_antitone` (L2Operator.lean:209)

**Statement**: Eigenvalues are decreasing: lambda_0 >= lambda_1 >= lambda_2 >= ...

**Plan**:
1. The eigenvalue sequence from the spectral theorem (#5) is constructed sorted in descending order of absolute value
2. From `transferEigenvalue_pos`, all eigenvalues are positive
3. Therefore sorting by decreasing absolute value = sorting by decreasing value
4. Antitonicity follows directly from the definition

**Key Mathlib**: Sorting lemmas for real sequences
**Depends on**: `transferEigenvalue`, `transferEigenvalue_pos`
**Difficulty**: EASY

---

#### 4. `os3_inheritance` (AxiomInheritance.lean:169)

**Statement**: OS3 (reflection positivity) transfers to continuum limit. For bounded continuous F: integral F(omega) * F(Theta omega) d mu >= 0.

**Plan**:
1. Let F be bounded, continuous on S'(R^d)
2. Define g(omega) := F(omega) * F(Theta omega). Since F and Theta are continuous and F is bounded, g is bounded and continuous
3. Lattice measures satisfy integral g d mu_a >= 0 for all a
4. By weak convergence: lim_{a->0} integral g d mu_a = integral g d mu
5. Limit of nonneg sequence is nonneg, so integral g d mu >= 0

**Key Mathlib**: `MeasureTheory.Measure.WeaklyConvergesTo.tendsto_integral`, `ge_of_tendsto`
**Blocker**: Need Theta continuous on S'(R^d)
**Difficulty**: EASY

---

#### 5. `lattice_rp_matrix` (OS3_RP_Lattice.lean:199)

**Statement**: RP in matrix form: sum c_i c_j integral cos(phi . (f_i - Theta f_j)) d mu >= 0.

**Plan**:
1. Assume `lattice_rp`
2. Choose F(phi) = sum_i c_i cos(<phi, f_i>) with f_i supported in positive time
3. Substitute into lattice_rp: integral F(phi) * F(Theta phi) d mu >= 0
4. Expand using `Finset.sum_mul_sum` and linearity of integral
5. Use trig identities to get the cos(A-B) form

**Key Mathlib**: `Finset.sum_mul_sum`, `MeasureTheory.integral_finset_sum`
**Depends on**: `lattice_rp`
**Difficulty**: EASY (conditional on lattice_rp)

---

#### 6. `interacting_moment_bound` (Hypercontractivity.lean:243)

**Statement**: Interacting moment bound via Cauchy-Schwarz/Holder density transfer.

**Plan**:
1. Write interacting expectation: E_{nu_a}[|Phi(f)|^{pn}] = (1/Z_a) integral |Phi(f)|^{pn} exp(-V_a) d mu_0
2. Apply Holder's inequality with exponents (2, 2):
   integral |Phi(f)|^{pn} exp(-V_a) d mu_0 <= (integral |Phi(f)|^{2pn} d mu_0)^{1/2} * (integral exp(-2V_a) d mu_0)^{1/2}
3. First factor: Gaussian moment, computable via Wick's theorem
4. Second factor: bounded by `exponential_moment_bound`
5. Partition function Z_a bounded below (standard from cluster expansion)

**Key Mathlib**: `MeasureTheory.lintegral_mul_le_Lp_mul_Lq` (Holder)
**Depends on**: `exponential_moment_bound`
**Difficulty**: EASY (conditional on exponential_moment_bound)

---

#### 7. `same_continuum_measure` (Bridge.lean:280)

**Statement**: The pphi2 lattice and Phi4 continuum constructions produce the same measure.

**Plan**:
1. From `schwinger_agreement`: both constructions have identical Schwinger functions
2. From exponential moment bounds: both measures satisfy moment determinacy conditions
3. From `measure_determined_by_schwinger`: measures with same Schwinger functions and exponential moments are equal
4. Direct logical combination

**Key Mathlib**: Basic logic
**Depends on**: `schwinger_agreement`, `measure_determined_by_schwinger`
**Difficulty**: EASY (conditional on prerequisites)

---

#### 8. `pphi2_limit_exists` (Convergence.lean:365)

**Statement**: Existence of P(Phi)_2 continuum limit measure satisfying IsPphi2Limit.

**Plan**:
1. Start with family of continuum-embedded lattice measures (mu_a)
2. From `continuumMeasures_tight`: family is tight
3. By Prokhorov's theorem: extract weakly convergent subsequence mu -> mu
4. Verify limit mu satisfies IsPphi2Limit properties using inheritance axioms
5. Combine all ingredients

**Key Mathlib**: Prokhorov's theorem
**Depends on**: `continuumMeasures_tight`, inheritance axioms
**Difficulty**: EASY (meta-theorem combining other results)

---

### Tier 2: MEDIUM (clear path, moderate formalization effort)

#### 9. `transferEigenvalue` (L2Operator.lean:188)

**Statement**: Eigenvalues of T, sorted in decreasing order.

**Plan**:
1. T is compact (from #4) and self-adjoint (from #2) on a Hilbert space
2. Apply Spectral Theorem for Compact Self-Adjoint Operators
3. Extract sequence of real eigenvalues converging to 0 with orthonormal eigenvectors
4. Sort in descending order of absolute value to get canonical sequence

**Key Mathlib**: `IsCompactOperator.spectral_theorem_of_isSelfAdjoint` (in `Analysis.Complex.Operator.Compact`)
**Blocker**: API for spectral theorem may need wrappers for convenient extraction
**Difficulty**: MEDIUM

---

#### 10. `transferEigenvalue_pos` (L2Operator.lean:201)

**Statement**: All eigenvalues lambda_n are strictly positive.

**Plan**:
1. **Nonneg**: Let v be eigenvector with eigenvalue lambda. Then <v, Tv> = lambda * ||v||^2. Since T is positive (#3), <v,Tv> >= 0, so lambda >= 0
2. **Nonzero**: Show T is injective (trivial kernel)
   - Let Tf = 0, meaning integral Kernel(psi, psi') f(psi') d mu = 0 for a.e. psi
   - Kernel is strictly positive (exp(-S) > 0)
   - Integral of strictly positive kernel times f can only be 0 if f = 0 a.e.
3. Since T is injective and spectrum = eigenvalues union {0}, 0 is not an eigenvalue

**Key Mathlib**: `MeasureTheory.integral_pos_iff`, `LinearMap.ker_eq_bot_iff_injective`
**Blocker**: Proving strictly positive kernel implies injectivity for L^2 integral operators
**Difficulty**: MEDIUM

---

#### 11. `os0_inheritance` (AxiomInheritance.lean:78)

**Statement**: OS0 (moment integrability) transfers to continuum limit.

**Plan**:
1. Uniform moment bound hypothesis: for all n, exists C_n, for all a, integral |omega f|^n d mu_a <= C_n
2. Want: integral |omega f|^n d mu <= C_n
3. Truncation: define g_M(x) := min(x, M). Then g_M(|omega f|^n) is bounded and continuous
4. By weak convergence: lim integral g_M(...) d mu_a = integral g_M(...) d mu
5. Fatou's lemma: integral |omega f|^n d mu <= liminf_M integral g_M(...) d mu
6. Since g_M(x) <= x: integral g_M(...) d mu_a <= C_n
7. Conclude integral |omega f|^n d mu <= C_n

**Key Mathlib**: `MeasureTheory.lintegral_le_liminf_lintegral` (Fatou), `tendsto_le_of_eventually_le`
**Blocker**: Need evaluation map omega -> omega(f) continuous on S'(R^d)
**Difficulty**: MEDIUM

---

#### 12. `latticeMeasure_translation_invariant` (OS2_WardIdentity.lean:133)

**Statement**: Interacting lattice measure is translation-invariant.

**Plan**:
1. The measure is d mu(phi) = (1/Z) exp(-S(phi)) d lambda(phi), where d lambda is the GFF measure
2. Define lattice translation tau_v for v in Lambda
3. **Action invariance**: S(tau_v phi) = S(phi) by change of summation variable in the bond sum (permutation of finite set)
4. **GFF invariance**: GFF covariance (-Delta)^{-1} commutes with translations on periodic lattice
5. Change variables phi' = tau_v phi: Jacobian is 1, integral is preserved

**Key Mathlib**: `Equiv.sum_comp` (change of variables in finite sum), `MeasureTheory.Measure.map_apply`
**Blocker**: Formal theory of Gaussian measures on R^n with specified covariance matrix
**Difficulty**: MEDIUM

---

#### 13. `translation_invariance_continuum` (OS2_WardIdentity.lean:165)

**Statement**: Translation invariance of continuum limit: Z[tau_v f] = Z[f] for all v in R^2.

**Plan**:
1. Know Z_a[tau_u f] = Z_a[f] for lattice translations u in aZ^2
2. For arbitrary v in R^2, approximate by lattice vectors u_n in a_n Z^2 with u_n -> v
3. Triangle inequality: |Z[tau_v f] - Z[f]| <= |Z[tau_v f] - Z_a[tau_v f]| + |Z_a[tau_v f] - Z_a[tau_{u_a} f]| + |Z_a[tau_{u_a} f] - Z[f]|
4. First and third terms -> 0 by continuum limit convergence
5. Middle term: continuity of v -> Z_a[tau_v f] via dominated convergence
6. Since Z_a[tau_{u_a} f] = Z_a[f], third term = |Z_a[f] - Z[f]| -> 0

**Key Mathlib**: `Topology.Dense`, `dist_triangle`, `MeasureTheory.tendsto_integral_of_dominated_convergence`
**Difficulty**: MEDIUM

---

#### 14. `rotation_invariance_continuum` (OS2_WardIdentity.lean:389)

**Statement**: Rotation invariance of continuum limit: Z[R*f] = Z[f] for all R in O(2).

**Plan**:
1. Assume lattice Ward identity: Z_a[R*f] - Z_a[f] = <A_a(R)>
2. Assume anomaly bound: |<A_a(R)>| <= C * a^2 * |log a|^p
3. Take limit a -> 0:
   - lim Z_a[R*f] = Z[R*f] (continuum limit)
   - lim Z_a[f] = Z[f] (continuum limit)
   - lim C * a^2 * |log a|^p = 0
4. By squeeze theorem: |Z[R*f] - Z[f]| <= 0, hence Z[R*f] = Z[f]

**Key Mathlib**: `Filter.Tendsto`, `tendsto_of_tendsto_of_tendsto_of_le_of_le` (squeeze), `tendsto_mul`, `tendsto_pow`
**Depends on**: `anomaly_bound_from_superrenormalizability`
**Difficulty**: MEDIUM (conditional on anomaly bound)

---

#### 15. `analyticOn_generatingFunctionalC` (OS2_WardIdentity.lean:666)

**Statement**: Complex generating functional z -> Z_C[sum z_i J_i] is jointly analytic in C^n.

**Plan**:
1. Define Z_C[J] = integral exp(<omega, J>) d mu for complex test functions J
2. Expand exponential as power series: Z_C[sum z_i J_i] = integral sum_{k=0}^infty (1/k!) (sum z_i <omega, J_i>)^k d mu
3. Swap integral and sum via dominated convergence — justified by exponential moment bounds (axiom 8)
4. Result is a convergent power series in z_i
5. Function given by convergent power series is analytic

**Key Mathlib**: `Analysis.AnalyticOn`, `HasFPowerSeriesOnBall`, `MeasureTheory.integral_tsum`, `ContinuousMultilinearMap`
**Depends on**: `continuum_exponential_moments`
**Difficulty**: MEDIUM

---

#### 16. `complex_gf_invariant_of_real_gf_invariant` (OS2_WardIdentity.lean:806)

**Statement**: If real generating functional is g-invariant, then complex generating functional is too.

**Plan**:
1. Consider h(z) := Z[exp(zA) * f] where A generates a one-parameter subgroup of the symmetry group
2. From `analyticOn_generatingFunctionalC`: h(z) is analytic in z
3. Real invariance: h(t) = Z[f] for all real t
4. Identity theorem for analytic functions: if two analytic functions agree on a set with accumulation point (the real axis), they agree everywhere
5. Therefore h(z) = Z[f] for all z in C

**Key Mathlib**: `AnalyticOn.eq_on_of_preconnected_of_eventually_eq` (identity theorem)
**Depends on**: `analyticOn_generatingFunctionalC`
**Difficulty**: MEDIUM

---

#### 17. ~~`os4_clustering_implies_ergodicity`~~ (OS2_WardIdentity.lean:1031) — **PROVED**

Now a theorem, proved from `cesaro_set_integral_tendsto` + `pphi2_generating_functional_real` +
`generatingFunctional_translate_continuous` + exponential clustering.

---

#### 17a. `cesaro_set_integral_tendsto` — **PROVED**

Proved and moved to `GeneralResults/FunctionalAnalysis.lean`. Pure Mathlib result (no project types).
**Difficulty**: EASY

---

#### 17b. `pphi2_generating_functional_real` — **PROVED**

Proved from new axiom `pphi2_measure_neg_invariant` (Z₂ symmetry: `Measure.map Neg.neg μ = μ`).
Proof: `conj(Z[f]) = Z[f]` via `integral_conj` + change of variables ω → -ω + Z₂ symmetry.
Then `Complex.conj_eq_iff_im` gives `Im(Z[f]) = 0`.

---

#### 17c. ~~`generatingFunctional_translate_continuous`~~ — **PROVED**

Proved via `MeasureTheory.continuous_of_dominated` with bound 1 (‖exp(ix)‖=1) and
`continuous_timeTranslationSchwartz` from `OSforGFF/TimeTranslation.lean` for the
Schwartz-topology continuity of `t ↦ translate(t,0) g`.

---

#### 18. `configuration_borelSpace` (moved upstream)

Now provided by `gaussian-field` as
`GaussianField.configuration_borelSpace` in
`GaussianField/ConfigurationTopology.lean`.

---

#### 19. `schwinger_n_convergence` (Convergence.lean:239)

**Statement**: n-point Schwinger functions converge along a subsequence.

**Plan**:
1. Family (mu_a) is tight (from `continuumMeasures_tight`)
2. By Prokhorov's theorem: extract weakly convergent subsequence mu_{a_{k_j}} -> mu
3. Schwinger functions: S_a(f_1,...,f_n) = integral omega(f_1)...omega(f_n) d mu_a
4. g(omega) = prod omega(f_i) is continuous but unbounded
5. Use uniform integrability from moment bounds + Vitali convergence theorem to pass the limit

**Key Mathlib**: `MeasureTheory.isTight`, Prokhorov's theorem
**Depends on**: `continuumMeasures_tight`, moment bounds
**Difficulty**: MEDIUM

---

#### 20. `second_moment_uniform` (Tightness.lean:74)

**Statement**: Uniform bound on second moment integral (omega f)^2 d nu_a <= C.

**Plan**:
1. Second moment = <f, C_a f> where C_a is covariance of interacting measure
2. Use correlation inequality (GHS/Lebowitz) to bound: 0 <= <f, C_a f>_{interacting} <= <f, C_a f>_{free}
3. Free covariance = (-Delta_a + m^2)^{-1}
4. In momentum space: <f, C_0 f> = integral |f_hat(k)|^2 / (k^2 + m^2) dk
5. This is the H^{-1} norm of f, bounded uniformly in a by properties of f in Schwartz space

**Key Mathlib**: `InnerProductSpace`
**Blocker**: Lattice Laplacian, Green's function, correlation inequalities
**Difficulty**: MEDIUM

---

#### 21. `moment_equicontinuity` (Tightness.lean:89)

**Statement**: Equicontinuity of moments in test function.

**Plan**:
1. E[|Phi_a(f) - Phi_a(g)|^2] = E[|Phi_a(f-g)|^2] by linearity
2. This is the second moment with test function h = f-g
3. Bound by free covariance: E[|Phi_a(h)|^2] <= <h, C_{0,a} h>
4. The operator C_{0,a} = (-Delta_a + m^2)^{-1} gains Sobolev regularity
5. <h, C_{0,a} h> is bounded by a Schwartz seminorm of h

**Key Mathlib**: Sobolev space theory
**Blocker**: Sobolev spaces on R^d, lattice covariance operator
**Difficulty**: MEDIUM

---

#### 22. `wickConstant_log_divergence` (Counterterm.lean:146)

**Statement**: |c_a - (1/(2pi)) log(1/a)| <= C.

**Plan**:
1. Wick constant = G_a(0,0) = diagonal of lattice Green's function
2. In momentum space: G_a(0,0) = (1/|Lambda*|) sum_k (sum_i (4/a^2) sin^2(ak_i/2) + m^2)^{-1}
3. For small a, sin^2(ak/2) ~ (ak/2)^2, so denominator ~ k^2 + m^2
4. Sum approximated by integral: integral_{|k|<pi/a} d^2k / (k^2 + m^2)
5. In polar coordinates: integral (2pi r dr) / (r^2 + m^2) = pi log(R^2/m^2 + 1) ~ (1/2pi) log(1/a) + const
6. Euler-Maclaurin formula bounds the error between sum and integral

**Key Mathlib**: None directly applicable
**Blocker**: Euler-Maclaurin formula, lattice Fourier transform
**Difficulty**: MEDIUM

---

#### 23. `wick_constant_comparison` (Bridge.lean:228)

**Statement**: |c_a - (2pi)^{-1} log(a^{-1})| <= C.

**Plan**: Identical to `wickConstant_log_divergence` with slightly different normalization convention. Same proof.

**Difficulty**: MEDIUM (same as #22)

---

#### 24. `measure_determined_by_schwinger` (Bridge.lean:200)

**Statement**: Probability measures with finite exponential moments are determined by their moments.

**Plan**:
1. Exponential moments imply the characteristic function chi(f) = E[exp(i omega(f))] is analytic in a strip around the real axis
2. Derivatives of chi at f=0 are determined by moments (Schwinger functions)
3. Analytic function uniquely determined by derivatives at a point
4. By Levy inversion theorem: characteristic function uniquely determines the measure

**Key Mathlib**: `ProbabilityTheory.charact_func`, `ProbabilityTheory.measure_eq_of_charact_func_eq`
**Blocker**: Carleman's condition connecting moment bounds to analyticity
**Difficulty**: MEDIUM

---

#### 25. `os2_from_phi4` (Bridge.lean:313)

**Statement**: OS2 (Euclidean invariance) for Phi4's continuum construction.

**Plan**:
1. Define E(2) action on S(R^d) and S'(R^d)
2. Show GFF measure mu_0 is E(2)-invariant (covariance (-Delta+m^2)^{-1} commutes with E(2))
3. Interaction integral :phi^4:(x) d^2x is E(2)-invariant
4. Show regularization/renormalization procedure preserves invariance
5. Schwinger functions of regularized theory converge to E(2)-invariant limits

**Key Mathlib**: `MulAction`
**Blocker**: Formalizing E(2) action on function/distribution spaces
**Difficulty**: MEDIUM

---

#### 26. `os3_from_pphi2` (Bridge.lean:358)

**Statement**: OS3 for pphi2's lattice continuum limit.

**Plan**:
1. Define Hilbert space H of functions on single time-slice
2. Construct transfer matrix T acting on H
3. Show T is positive self-adjoint operator
4. Express RP integral as <v_F, T^N v_F> where v_F encodes the test function F
5. Since T is positive, T^N is positive, so inner product >= 0
6. This gives lattice RP, then use `os3_inheritance` for continuum limit

**Key Mathlib**: `IsSelfAdjoint`, `ContinuousLinearMap.IsPositive`
**Depends on**: Transfer matrix construction, `os3_inheritance`
**Difficulty**: MEDIUM

---

### Tier 3: HARD (major formalization effort or missing infrastructure)

#### 27. `transferOperatorCLM` (L2Operator.lean:90)

**Statement**: Constructs the transfer operator on L^2 spatial field as a continuous linear map.

**Plan**:
1. Define spatial field space F_space (functions on 1D lattice Z/NZ)
2. Define L^2(F_space, d mu_C) where d mu_C is GFF measure on F_space
3. Define kernel: Kernel(psi, psi') = integral exp(-S(psi, phi, psi')) d mu_0(phi)
4. Prove Hilbert-Schmidt: integral integral |Kernel(psi,psi')|^2 d mu_C(psi) d mu_C(psi') < infinity
   - Bound using Gaussian decay of the free theory
   - Interaction exp(-V) is bounded
5. Construct CLM from Hilbert-Schmidt norm bound

**Key Mathlib**: `MeasureTheory.Lp`, `Analysis.InnerProductSpace.HilbertSchmidt`, `MeasureTheory.integral_integral_swap`
**Blocker**: Gaussian (Free Field) measures on function spaces — single biggest blocker
**Difficulty**: HARD

---

#### 28. `transferOperator_inner_nonneg` (L2Operator.lean:119)

**Statement**: T is positive: <f, Tf> >= 0 for all f.

**Plan**:
1. Express <f, T f> as a reflection-positive expectation value on the full lattice
2. Define time-reflection operator Theta
3. Prove reflection positivity: <(Theta F) F> >= 0 for positive-time-supported F
4. Show <f, T^n f> can be expressed as such an RP expectation (for n=1 gives result)

**Key Mathlib**: `ContinuousLinearMap.isPositive`
**Blocker**: Reflection positivity formalism for lattice functional integrals
**Difficulty**: HARD

---

#### 29. `transferEigenvalue_ground_simple` (L2Operator.lean:222)

**Statement**: Ground state eigenvalue lambda_0 is simple: lambda_0 > lambda_1.

**Plan**:
1. Formalize "positivity-improving" operator: for nonzero f >= 0, Tf > 0 a.e.
2. Prove T is positivity-improving (kernel is strictly positive everywhere)
3. Apply Perron-Frobenius theorem for compact, self-adjoint, positivity-improving operators on L^2
4. Theorem states: spectral radius is simple eigenvalue with strictly positive eigenvector
5. Spectral radius = lambda_0, so lambda_0 is simple, hence lambda_0 > lambda_1

**Key Mathlib**: None (Perron-Frobenius for L^2 integral operators missing)
**Blocker**: Perron-Frobenius / Krein-Rutman theorem for integral operators on L^2
**Difficulty**: HARD

---

#### 30. `action_decomposition` (OS3_RP_Lattice.lean:146)

**Statement**: Lattice action decomposes as S_plus(phi) + S_plus(Theta phi).

**Plan**:
1. Define lattice Lambda = Fin N x Fin N with nearest-neighbor bonds B
2. Define time-reversal Theta(t,x) = (-t, x) with Fin N arithmetic
3. Define upper half-plane Lambda_+ = {p : p.1 > 0}
4. Partition bond set B into B_+, B_-, B_0 (boundary)
5. Use `Finset.sum_union_disjoint` to decompose the action sum
6. Show sum over B_- = sum over B_+ evaluated at Theta phi, via change of summation variable

**Key Mathlib**: `Finset.sum`, `Finset.filter`, `Finset.sum_union_disjoint`, `Equiv.sum_comp`
**Blocker**: Careful finite-set combinatorics with periodic boundary conditions. Not conceptually hard but definitionally involved
**Difficulty**: MEDIUM-HARD

---

#### 31. `lattice_rp` (OS3_RP_Lattice.lean:175)

**Statement**: Reflection positivity on the lattice.

**Plan**:
1. Factorize the integral over time slices using the transfer matrix
2. Define Hilbert space H = L^2(R^{Fin N}, d nu) for single time-slice
3. Define transfer matrix T acting on H
4. Express RP integral as inner product <Psi_F, T^k Psi_F>
5. Show T is positive self-adjoint
6. <v, T^k v> >= 0 for positive operators

**Key Mathlib**: `MeasureTheory.integral`, `InnerProductSpace`
**Blocker**: Transfer matrix formalism — defining integral operators on L^2 field spaces
**Difficulty**: HARD

---

#### 32. `spectral_gap_uniform` (SpectralGap.lean:87)

**Statement**: Mass gap bounded below uniformly in lattice spacing.

**Plan**:
1. This is a deep non-perturbative result requiring cluster expansion
2. Formalize polymers, activities, and polymer models
3. Prove fundamental convergence theorem for cluster expansions
4. Apply to P(Phi)_2: show polymer activities are small for small a / weak coupling
5. Extract spectral information from cluster expansion
6. Show mass gap expression is bounded below by constant independent of a

**Key Mathlib**: `Filter.Tendsto`, `Real.log`, `Real.exp` (basics only)
**Blocker**: Cluster/polymer expansion (massive formalization), renormalization
**Difficulty**: HARD (research-level)

---

#### 33. `spectral_gap_lower_bound` (SpectralGap.lean:98)

**Statement**: m_phys >= c * m_bare for some c depending on P.

**Plan**:
1. Via correlation inequalities (GHS, FKG):
   - Relate two-point function decay rate (m_phys) to bare mass parameter
   - Compare interacting theory to free theory
2. Alternatively via cluster expansion (same as #32)

**Key Mathlib**: None for core techniques
**Blocker**: Correlation inequalities or cluster expansion
**Difficulty**: HARD

---

#### 34. `two_point_clustering_from_spectral_gap` (OS4_MassGap.lean:82)

**Statement**: Connected two-point function decays exponentially with rate = mass gap.

**Plan**:
1. Write time-evolved correlation as <psi_0, phi T^n phi psi_0> in transfer matrix picture
2. Insert spectral decomposition: T^n = sum_k lambda_k^n |psi_k><psi_k|
3. Two-point function = sum_k lambda_k^n |<psi_0, phi psi_k>|^2
4. Connected part: subtract k=0 term (proportional to <phi>^2)
5. Leading term: (lambda_1/lambda_0)^n = exp(-n*a*m)
6. Bound remainder of series

**Key Mathlib**: Spectral theorem from #9, properties of exp/log
**Blocker**: Unbounded operators (field phi as multiplication operator), full transfer matrix machinery
**Difficulty**: HARD

---

#### 35. `general_clustering_from_spectral_gap` (OS4_MassGap.lean:97)

**Statement**: Connected correlators of bounded observables decay exponentially.

**Plan**: Same as #34 but simpler since A, B are bounded operators.

**Depends on**: `two_point_clustering_from_spectral_gap` infrastructure
**Difficulty**: MEDIUM-HARD

---

#### 36. `anomaly_bound_from_superrenormalizability` (OS2_WardIdentity.lean:331)

**Statement**: Rotation anomaly is O(a^2 |log a|^p).

**Plan**:
1. Define the anomaly A(R) = R(S_a) - S_a from broken O(2) symmetry of lattice Laplacian
2. Power counting: anomaly involves fourth-order differences, scaling dimension 4
3. In d=2, dimension 4 > d=2, so anomaly is O(a^{4-2}) = O(a^2)
4. Logarithmic corrections from loop calculations in perturbation theory
5. Super-renormalizability limits logs to polynomial powers: O(a^2 |log a|^p)

**Key Mathlib**: None for renormalization theory
**Blocker**: Scaling dimension, renormalization, power counting, Feynman diagrams
**Difficulty**: HARD (research-level)

---

#### 37. `continuum_exponential_moments` (OS2_WardIdentity.lean:642)

**Statement**: Exponential moments of continuum limit are finite.

**Plan**:
1. For GFF: omega(f) is Gaussian, so Fernique's theorem gives finite exponential moments
2. For interacting theory: Nelson's hypercontractivity estimates provide uniform L^p bounds
3. L^p bounds give E[|omega(f)|^n] growing slower than n!, ensuring convergence of exp series
4. Uniform in lattice spacing -> passes to continuum limit

**Key Mathlib**: `ProbabilityTheory.gaussian` (1D only), `ENNReal.tsum_coe_eq_top_iff`
**Blocker**: Fernique's theorem (Gaussian measures on Banach spaces), Nelson's hypercontractivity
**Difficulty**: HARD

---

#### 38. `exponential_moment_schwartz_bound` (OS2_WardIdentity.lean:700)

**Statement**: Exponential moment bounded by Schwartz norms.

**Plan**:
1. For Gaussian field: omega(f) has variance sigma^2 = <f, C f> where C = (-Delta+m^2)^{-1}
2. In momentum space: <f, C f> = integral |f_hat(k)|^2 / (k^2+m^2) dk = ||f||_{H^{-1}}^2
3. Sobolev embedding: ||f||_{H^{-1}} bounded by Schwartz seminorms
4. All Gaussian moments E[|omega(f)|^{2n}] = (2n-1)!! sigma^{2n}
5. Exponential moment follows from moment bounds

**Key Mathlib**: `Analysis.Fourier.fourierIntegral`, Sobolev spaces
**Blocker**: Sobolev spaces, GFF covariance as H^{-1} operator
**Difficulty**: MEDIUM-HARD

---

#### 39. `continuum_exponential_clustering` (OS2_WardIdentity.lean:880)

**Statement**: Exponential clustering from spectral gap.

**Plan**:
1. Express generating functional in transfer matrix picture with Hamiltonian H
2. Use ground state Omega with mass gap m_0
3. Correlation = sum_{n!=0} <Omega, O_1|n> exp(-E_n * t) <n|O_2 Omega>
4. Since E_n >= m_0: bound by exp(-m_0 * t)
5. Time separation t corresponds to ||a||

**Key Mathlib**: Spectral theory for operators
**Blocker**: Transfer matrix + spectral gap formalism (same as #32, #34)
**Difficulty**: HARD

---

#### 40. `os4_inheritance` (AxiomInheritance.lean:199)

**Statement**: OS4 (exponential clustering) transfers to continuum limit.

**Plan**:
1. spectral_gap_uniform provides uniform decay bound m > 0 for lattice Schwinger functions
2. Lattice Schwinger functions converge to limit (from schwinger_n_convergence)
3. Uniform exponential decay |S_a(f, g_t) - S_a(f)S_a(g_t)| <= C exp(-mt) passes to limit
4. Therefore |S(f, g_t) - S(f)S(g_t)| <= C exp(-mt)

**Key Mathlib**: Limit inequalities
**Blocker**: Requires spectral_gap_uniform + schwinger_n_convergence
**Difficulty**: MEDIUM-HARD

---

#### 41. `configuration_polishSpace` (moved upstream)

Now provided by `gaussian-field` as
`GaussianField.configuration_polishSpace` in
`GaussianField/ConfigurationTopology.lean`.

---

#### 42. `continuumLimit_nontrivial` (Convergence.lean:309)

**Statement**: Continuum limit is nontrivial (two-point function positive).

**Plan**:
1. Use Griffiths/FKG correlation inequality on lattice: <phi_x phi_y> >= 0
2. Stronger: for ferromagnetic models, get lower bound S_a(f,f) >= c > 0 (uniform in a)
3. Lower bound passes to weak limit: S(f,f) >= c > 0

**Key Mathlib**: None for correlation inequalities
**Blocker**: FKG/Griffiths correlation inequalities for lattice models
**Difficulty**: HARD

---

#### 43. `continuumLimit_nonGaussian` (Convergence.lean:333)

**Statement**: Connected 4-point function is nonzero.

**Plan**:
1. Calculate lattice u_4 via cluster expansion in coupling constant lambda
2. Show u_4_a = -lambda * (positive term) + O(lambda^2)
3. For small lambda, u_4_a != 0
4. Result uniform enough in a to survive continuum limit

**Key Mathlib**: N/A
**Blocker**: Cluster expansion machinery
**Difficulty**: HARD

---

#### 44. `continuumMeasures_tight` (Tightness.lean:110)

**Statement**: Tightness of continuum-embedded measures on S'(R^d).

**Plan**:
1. State a tightness criterion (Mitoma's theorem or Sobolev-norm criterion)
2. Mitoma: tightness iff pushforward measures on R via ev_f are tight + equicontinuity
3. Or: sup_a E[||Phi_a||_{H^{-s}}^p] < infinity for some s > d/2, p > 1
4. Verify criterion using `second_moment_uniform` and `moment_equicontinuity`

**Key Mathlib**: `MeasureTheory.isTight`
**Blocker**: Mitoma's theorem (probability on infinite-dimensional spaces)
**Difficulty**: HARD

---

#### 45. `exponential_moment_bound` (Hypercontractivity.lean:203)

**Statement**: exp(-V_a) has uniformly bounded L^2 norm w.r.t. Gaussian.

**Plan**:
1. Need to bound integral exp(-2V_a) d mu_0
2. **Cluster expansion**: write log integral as convergent series in coupling lambda
3. Or **chessboard estimates** (Nelson): divide lattice into checkerboard, bound cross-terms
4. Either approach gives uniform bound for sufficiently small coupling

**Key Mathlib**: N/A
**Blocker**: Cluster expansion or chessboard estimates
**Difficulty**: HARD

---

#### 46. `pphi2_nontriviality` (Main.lean:113)

**Statement**: For all nonzero f, integral (omega f)^2 d mu > 0.

**Plan**: Same as `continuumLimit_nontrivial` (#42). Uses Griffiths/FKG correlation inequalities.

**Difficulty**: HARD

---

#### 47. `schwinger_agreement` (Bridge.lean:253)

**Statement**: At weak coupling, pphi2 lattice and Phi4 continuum constructions have same Schwinger functions.

**Plan**:
1. Perform cluster expansion for P(Phi)_2 on lattice
2. Perform renormalized perturbation expansion for Phi4 continuum theory
3. Show that after a->0 limit, lattice diagram sums converge to renormalized continuum diagrams
4. Wick constant difference (axiom 18) absorbed into renormalization
5. Order-by-order agreement

**Key Mathlib**: N/A
**Blocker**: Full cluster expansion for both lattice and continuum, BPHZ renormalization
**Difficulty**: HARD (research-level)

---

## Summary Table

| # | Axiom | File | Difficulty | Key Blocker |
|---|-------|------|-----------|-------------|
| 1 | ~~`transferOperator_isSelfAdjoint`~~ | L2Operator | **PROVED** | — |
| 2 | `transferOperator_isCompact` | L2Operator | EASY | Needs transferOperatorCLM |
| 3 | `transferEigenvalue_antitone` | L2Operator | EASY | Needs eigenvalue construction |
| 4 | `os3_inheritance` | AxiomInheritance | EASY | Theta continuity on S' |
| 5 | `lattice_rp_matrix` | OS3_RP_Lattice | EASY | Needs lattice_rp |
| 6 | `interacting_moment_bound` | Hypercontractivity | EASY | Needs exponential_moment_bound |
| 7 | `same_continuum_measure` | Bridge | EASY | Needs schwinger_agreement + moment_det |
| 8 | `pphi2_limit_exists` | Convergence | EASY | Meta-theorem, needs all prerequisites |
| 9 | `transferEigenvalue` | L2Operator | MEDIUM | Spectral theorem API |
| 10 | `transferEigenvalue_pos` | L2Operator | MEDIUM | Positive kernel injectivity |
| 11 | `os0_inheritance` | AxiomInheritance | MEDIUM | Evaluation map continuity |
| 12 | `latticeMeasure_translation_invariant` | OS2_Ward | MEDIUM | Gaussian measures on R^n |
| 13 | `translation_invariance_continuum` | OS2_Ward | MEDIUM | Continuum limit convergence |
| 14 | `rotation_invariance_continuum` | OS2_Ward | MEDIUM | Needs anomaly bound |
| 15 | `analyticOn_generatingFunctionalC` | OS2_Ward | MEDIUM | Needs exponential moments |
| 16 | `complex_gf_invariant_of_real_gf_invariant` | OS2_Ward | MEDIUM | Needs analyticity |
| 17 | ~~`os4_clustering_implies_ergodicity`~~ | OS2_Ward | **PROVED** | — |
| 17a | `cesaro_set_integral_tendsto` | **PROVED** | — | Moved to GeneralResults/FunctionalAnalysis.lean |
| 17b | `pphi2_generating_functional_real` | **PROVED** | — | From pphi2_measure_neg_invariant |
| 17c | `generatingFunctional_translate_continuous` | **PROVED** | — | DCT + continuous_timeTranslationSchwartz |
| 18 | `configuration_borelSpace` | **MOVED UPSTREAM** | — | Provided by `gaussian-field` (`ConfigurationTopology.lean`) |
| 19 | `schwinger_n_convergence` | Convergence | MEDIUM | Needs tightness |
| 20 | `second_moment_uniform` | Tightness | MEDIUM | Lattice Green's function |
| 21 | `moment_equicontinuity` | Tightness | MEDIUM | Sobolev spaces |
| 22 | `wickConstant_log_divergence` | Counterterm | MEDIUM | Euler-Maclaurin formula |
| 23 | `wick_constant_comparison` | Bridge | MEDIUM | Same as #22 |
| 24 | `measure_determined_by_schwinger` | Bridge | MEDIUM | Carleman's condition |
| 25 | `os2_from_phi4` | Bridge | MEDIUM | E(2) action on S' |
| 26 | `os3_from_pphi2` | Bridge | MEDIUM | Transfer matrix |
| 27 | `transferOperatorCLM` | L2Operator | HARD | Gaussian measures on function spaces |
| 28 | `transferOperator_inner_nonneg` | L2Operator | HARD | Reflection positivity formalism |
| 29 | `transferEigenvalue_ground_simple` | L2Operator | HARD | Perron-Frobenius for L^2 operators |
| 30 | `action_decomposition` | OS3_RP_Lattice | MEDIUM-HARD | Finite-set combinatorics |
| 31 | `lattice_rp` | OS3_RP_Lattice | HARD | Transfer matrix formalism |
| 32 | `spectral_gap_uniform` | SpectralGap | HARD | Cluster expansion (research-level) |
| 33 | `spectral_gap_lower_bound` | SpectralGap | HARD | Correlation inequalities / cluster exp |
| 34 | `two_point_clustering_from_spectral_gap` | OS4_MassGap | HARD | Unbounded operators, transfer matrix |
| 35 | `general_clustering_from_spectral_gap` | OS4_MassGap | MEDIUM-HARD | Same infrastructure as #34 |
| 36 | `anomaly_bound_from_superrenormalizability` | OS2_Ward | HARD | Renormalization theory (research-level) |
| 37 | `continuum_exponential_moments` | OS2_Ward | HARD | Fernique + hypercontractivity |
| 38 | `exponential_moment_schwartz_bound` | OS2_Ward | MEDIUM-HARD | Sobolev, GFF covariance |
| 39 | `continuum_exponential_clustering` | OS2_Ward | HARD | Transfer matrix + spectral gap |
| 40 | `os4_inheritance` | AxiomInheritance | MEDIUM-HARD | Needs spectral_gap_uniform |
| 41 | `configuration_polishSpace` | **MOVED UPSTREAM** | — | Provided by `gaussian-field` (`ConfigurationTopology.lean`) |
| 42 | `continuumLimit_nontrivial` | Convergence | HARD | Correlation inequalities |
| 43 | `continuumLimit_nonGaussian` | Convergence | HARD | Cluster expansion |
| 44 | `continuumMeasures_tight` | Tightness | HARD | Mitoma's theorem |
| 45 | `exponential_moment_bound` | Hypercontractivity | HARD | Cluster exp / chessboard estimates |
| 46 | `pphi2_nontriviality` | Main | HARD | Same as #42 |
| 47 | `schwinger_agreement` | Bridge | HARD | Full cluster expansion + renormalization |
