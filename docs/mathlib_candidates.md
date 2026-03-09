# Mathlib Candidate Results

Standard mathematical results from pphi2 and gaussian-field that don't depend
on project-specific definitions. Candidates for eventual Mathlib PRs.

**Updated**: 2026-03-09

## Priority 1: High Impact

### Young's Inequality L^1 x L^2 -> L^2

**File**: `Pphi2/TransferMatrix/L2Convolution.lean:117`
**Name**: `young_eLpNorm_bound`
**Statement**: `eLpNorm (g ⋆ f) 2 μ ≤ eLpNorm g 1 μ * eLpNorm f 2 μ`
**Notes**: **Explicitly listed as TODO** in Mathlib's `Analysis/Convolution.lean`.
Proof (~90 lines) via triangle inequality + Cauchy-Schwarz + Tonelli + translation
invariance. References: Reed-Simon II §IX.4, Stein-Weiss Thm 1.2.

Also extract:
- `lintegral_mul_sq_le` (line 65) — weighted Cauchy-Schwarz for lintegral
- `convCLM` + `convCLM_spec` — convolution with L^1 kernel as CLM on L^2

### Ahlswede-Daykin Inequality

**File**: `gaussian-field: Lattice/FKG.lean`
**Names**: `chebyshev_integral_inequality` (line 111),
`ahlswede_daykin_one_dim` (line 399), `ahlswede_daykin_ennreal` (line 851),
`ahlswede_daykin` (line 1531)
**Statement**: Classical n-dimensional Ahlswede-Daykin four-functions inequality,
proved by Fubini induction from the 1D base case. Also includes the Chebyshev
integral inequality for monotone functions (∫fg dμ ≥ (∫f)(∫g)).
**Notes**: Foundational for FKG inequality and lattice correlation inequalities.
Classical results (Holley 1974, FKG 1971). Full proofs with no axioms.

### Hermite Function Theory

**File**: `gaussian-field: SchwartzNuclear/HermiteFunctions.lean`
**Names**:
- `hermiteFunction_orthonormal` (line 536) — ∫ ψ_n ψ_m = δ_{nm}
- `hermiteFunction_complete` (line 1826) — complete ONB for L^2(ℝ)
- `hermiteFunction_schwartz` (line 630) — Hermite functions are Schwartz
- `hermiteFunction_sup_bound` (line 1052) — |ψ_n(x)| ≤ C(1+n)^s
- `hermite_derivative` (line 254) — (hermite (n+1))' = (n+1) · hermite n

**Notes**: Fills major gap in Mathlib's harmonic analysis coverage. Complete
proofs with extensive supporting infrastructure (ladder operators, Sobolev
bounds, seminorm estimates).

### Prokhorov's Theorem (Sequential)

**File**: `Pphi2/ContinuumLimit/Convergence.lean:84`
**Name**: `prokhorov_sequential`
**Statement**: On a Polish space, tight sequence of probability measures has
a weakly convergent subsequence.
**Notes**: Full proof via Mathlib's `isCompact_closure_of_isTightMeasureSet` +
`ProbabilityMeasure` metrization. Important probability result.

### Cesaro Integral Convergence

**File**: `Pphi2/GeneralResults/FunctionalAnalysis.lean:37`
**Name**: `cesaro_set_integral_tendsto`
**Statement**: If h : ℝ → ℝ is measurable, bounded, and h(t) → L as t → +∞,
then (1/T)∫₀ᵀ h(t) dt → L as T → +∞.
**Notes**: Continuous analogue of `Filter.Tendsto.cesaro`. Substantial proof
(~130 lines) with careful integral bounds. Missing from Mathlib.

## Priority 2: Operator Theory

### Multiplication Operator on L^2

**File**: `Pphi2/TransferMatrix/L2Multiplication.lean`
**Names**:
- `mul_L2_bound` (line 46) — ‖w·f‖₂ ≤ C·‖f‖₂ when ‖w‖∞ ≤ C
- `mulCLM` (line 69) — bounded multiplication operator as CLM
- `mulCLM_spec` (line 115) — (M_w f)(x) = w(x)·f(x) a.e.
- `mulCLM_isSelfAdjoint` (line 146) — self-adjoint for real-valued w

**Notes**: Standard functional analysis. Clean API with norm bound + spec +
self-adjointness. Uses `LinearMap.mkContinuous` + Hölder (L^∞ × L^2 → L^2).

### Positivity-Improving Operators (Jentzsch)

**File**: `Pphi2/TransferMatrix/JentzschProof.lean`
**Names**:
- `IsPositivityPreserving` (line 39) — T maps f ≥ 0 to Tf ≥ 0
- `IsPositivityImproving` (line 47) — T maps f ≥ 0, f ≠ 0 to Tf > 0 a.e.
- `abs_apply_le_apply_abs` (line 105) — |Tf| ≤ T|f| for PP operators
- `abs_inner_le_inner_abs` (line 179) — |⟨f,Tf⟩| ≤ ⟨|f|,T|f|⟩
- `abs_eigenvector_of_top_eigenvector` (line 211) — |f| eigenvector for λ₀

**Notes**: Novel approach to Jentzsch/Perron-Frobenius avoiding Krein-Rutman.
Uses Lp lattice structure. Three-phase proof: absolute value inequality →
inner product inequality → variational argument.

### Fourier L^2 Results

**File**: `Pphi2/TransferMatrix/GaussianFourier.lean`
**Names**:
- `fourier_ae_nonzero_of_nonzero` (line 47) — nonzero f ∈ L^2 ⟹ f̂ not a.e. zero
- `fourier_gaussian_pos` (line 130) — F.T. of exp(-b‖x‖²) is strictly positive

**Notes**: `fourier_ae_nonzero_of_nonzero` uses Plancherel injectivity
(`Lp.fourierTransformₗᵢ`). `fourier_gaussian_pos` is a one-liner from
`fourier_gaussian_innerProductSpace`.

## Priority 3: DFT / Fourier on ZMod

### DFT Orthogonality

**File**: `gaussian-field: Lattice/CirculantDFT.lean`
**Names**:
- `sum_cos_zmod_eq_zero` (line 634) — Σ_{z:ZMod N} cos(2πkz/N) = 0 when N∤k
- `sum_sin_zmod_eq_zero` (line 686) — same for sin
- `sum_cos_zmod_eq_N` (line 734) — Σ cos = N when N∣k
- `latticeFourierBasisFun_orthogonal` (line 1079) — DFT basis orthogonality

**Notes**: Fundamental DFT identities. Uses ZMod arithmetic.

### Discrete Laplacian Eigenvalues

**File**: `gaussian-field: Lattice/CirculantDFT.lean`
**Names**:
- `negLaplacian1d_cos_eigenvector` (line 128) — cos is eigenvector of -Δ₁
- `negLaplacian1d_sin_eigenvector` (line 146) — sin is eigenvector of -Δ₁
- `eigenvalue_formula` (line 136) — λ_k = (4/a²)sin²(πk/N)

**Notes**: Standard discrete Fourier analysis.

## Priority 4: Heat Kernel / Mehler Kernel

### Mehler Kernel Properties

**File**: `gaussian-field: HeatKernel/PositionKernel.lean`
**Names**:
- `mehlerKernel_symmetric` (line 148) — K(t,x₁,x₂) = K(t,x₂,x₁)
- `mehlerKernel_pos` (line 153) — K(t,x₁,x₂) > 0 for t > 0
- `mehlerKernel_reproduces_hermite` (line 164) — eigenfunction reproduction
- `mehlerKernel_semigroup` (line 326) — ∫ K(s,x,z)K(t,z,y) = K(s+t,x,y)

**Notes**: Classical heat kernel semigroup properties. Uses Hermite function
spectral expansion.

## Priority 5: Circle / Periodic Function Theory

### Fourier Coefficients Under Symmetries

**File**: `gaussian-field: SmoothCircle/FourierTranslation.lean`
**Names**:
- `fourierCoeffReal_circleTranslation_{zero,cos,sin}` (lines 152-229)
- `fourierCoeffReal_circleReflection_{zero,cos,sin}` (lines 285-343)

**Notes**: All 6 proved. Fourier coefficient transformation rules for
translation and reflection on the circle.

### Periodic Function Analysis

**File**: `gaussian-field: SmoothCircle/Basic.lean`
**Names**:
- `periodic_iteratedDeriv` (line 147) — periodicity preserved under derivatives
- `fourierCoeffReal_bound` (line 407) — Fourier coefficient bounds
- `sobolevSeminorm_fourierBasis_le` (line 776) — Sobolev seminorm via Fourier

### Riemann Sum Convergence

**File**: `gaussian-field: Lattice/HeatKernelConvergence1d.lean:496`
**Name**: `riemann_sum_periodic_tendsto`
**Statement**: Riemann sums converge for continuous periodic functions.
**Notes**: Proved via uniform continuity (Heine-Cantor) + integral splitting.

## Priority 6: Miscellaneous

### Trig Identity for Reflection Positivity

**File**: `Pphi2/GeneralResults/FunctionalAnalysis.lean:199`
**Name**: `rp_matrix_trig_identity`
**Statement**: Σᵢⱼ cᵢcⱼ cos(aᵢ-bⱼ) = (Σ cᵢcos aᵢ)(Σ cⱼcos bⱼ) + (Σ cᵢsin aᵢ)(Σ cⱼsin bⱼ)
**Notes**: Finite proof using cos(A-B) expansion + bilinearity.

### Schwartz Integrability

**File**: `Pphi2/GeneralResults/FunctionalAnalysis.lean:173`
**Name**: `schwartz_integrable_norm_rpow`
**Statement**: Schwartz functions have integrable ‖f x‖^p for any p > 0.

### Parametric Schwartz Integration

**File**: `gaussian-field: SchwartzNuclear/ParametricCalculus.lean:105`
**Name**: `contDiff_schwartz_parametric_integral`
**Statement**: Schwartz space closed under parametric integration.

### Fourier Coefficient Decay

**File**: `gaussian-field: Lattice/Convergence.lean:86`
**Name**: `latticeDFTCoeff1d_quadratic_bound`
**Statement**: DFT coefficient decay |c_m(f)| ≤ C/(1+m)² for smooth functions.

## Extraction Plan

To prepare for Mathlib PRs, extract results into standalone `GeneralResults/` files:

| Target File | Source | Contents |
|------------|--------|----------|
| `GeneralResults/YoungConvolution.lean` | L2Convolution | Young L^1×L^2→L^2, convCLM |
| `GeneralResults/MultiplicationOperator.lean` | L2Multiplication | mulCLM + API |
| `GeneralResults/PositivityImproving.lean` | JentzschProof | PP/PI defs + Jentzsch phases |
| `GeneralResults/FourierL2.lean` | GaussianFourier | Plancherel injectivity, Gaussian FT |
| `GeneralResults/ProkhorovSequential.lean` | Convergence | Sequential Prokhorov |
| `GeneralResults/FunctionalAnalysis.lean` | (already exists) | Cesaro, Schwartz Lp, trig identity |

For gaussian-field results, extraction would happen in that repository's own
`GeneralResults/` directory.
