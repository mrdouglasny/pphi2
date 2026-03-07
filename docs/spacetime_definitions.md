# Spacetime Definitions and Infrastructure

Reference for all spacetime types, test function spaces, symmetry operations,
spectral data, heat kernels, Green's functions, embeddings, tensor products,
and measure constructions across the pphi2 and gaussian-field repositories.

## 1. Spaces

### 1.1 Circle: `SmoothMap_Circle L R`

**File:** `gaussian-field/SmoothCircle/Basic.lean`

The space of L-periodic smooth functions `R -> R`, representing C^inf(S^1_L).

```
structure SmoothMap_Circle (L : R) (F : Type*) [Fact (0 < L)] where
  toFun : R -> R
  periodic' : Function.Periodic toFun L
  smooth'   : ContDiff R top toFun
```

**Topology:** Nuclear Frechet, defined by the family of Sobolev sup-seminorms
`p_k(f) = sup_{x in [0,L]} |f^(k)(x)|` via `smoothCircle_withSeminorms`.

**Instances:** `IsTopologicalAddGroup`, `ContinuousSMul R`, `DyninMityaginSpace`
(from `SmoothCircle/Nuclear.lean`).

### 1.2 Torus: `TorusTestFunction L`

**File:** `gaussian-field/Torus/Restriction.lean`

The 2D torus test function space C^inf(T^2_L) = C^inf(S^1_L) ot C^inf(S^1_L).

```
abbrev TorusTestFunction L := NuclearTensorProduct (SmoothMap_Circle L R) (SmoothMap_Circle L R)
```

Inherits `DyninMityaginSpace` from `NuclearTensorProduct`.

### 1.3 Finite lattice sites: `FinLatticeSites d N`

**File:** `gaussian-field/Lattice/Sites.lean`

Sites of the discrete torus (Z/NZ)^d with periodic boundary conditions.

```
abbrev FinLatticeSites (d : N) (N : N) := Fin d -> ZMod N
```

Also defines `InfLatticeSites d := Fin d -> Z` (infinite lattice) and
`latticeNorm` (l^1 norm on Z^d).

### 1.4 Finite lattice field: `FinLatticeField d N`

**File:** `gaussian-field/Lattice/FiniteField.lean`

Real-valued field configurations on the finite lattice.

```
abbrev FinLatticeField (d : N) (N : N) := FinLatticeSites d N -> R
```

Has `DyninMityaginSpace` instance (finite-dimensional, delta-function basis),
`HasPointEval` instance. Basis: `finLatticeBasisVec m` (delta function at
m-th site). Coefficients: `finLatticeCoeffCLM m` (evaluation at m-th site).

### 1.5 Configuration space: `Configuration E`

**File:** `gaussian-field/GaussianField/Construction.lean`

The weak dual of a test function space -- where field configurations live.

```
abbrev Configuration E := WeakDual R E
```

Equipped with `instMeasurableSpaceConfiguration` (cylindrical sigma-algebra,
comap of evaluation maps). For torus: `Configuration (TorusTestFunction L)`
is Polish (`configuration_torus_polish`, axiom) and Borel
(`configuration_torus_borelSpace`, axiom).

### 1.6 Rapidly decreasing sequences: `RapidDecaySeq`

**File:** `gaussian-field/Nuclear/NuclearTensorProduct.lean`

The Kothe sequence space s(N) of rapidly decreasing real sequences.

```
structure RapidDecaySeq where
  val : N -> R
  rapid_decay : forall k, Summable (fun m => |val m| * (1 + m)^k)
```

Seminorms: `rapidDecaySeminorm k (a) = sum_m |a_m| * (1+m)^k`.
Has `DyninMityaginSpace` instance (identity basis).

## 2. Abstract framework

### 2.1 Dynin-Mityagin spaces: `DyninMityaginSpace E`

**File:** `gaussian-field/Nuclear/DyninMityagin.lean`

Typeclass for nuclear Frechet spaces with a Schauder basis, implementing
the Dynin-Mityagin representation theorem.

```
class DyninMityaginSpace (E : Type*) ... extends T1Space E where
  iota : Type                        -- seminorm index type
  p : iota -> Seminorm R E           -- seminorm family
  h_with : WithSeminorms p           -- topology = seminorm topology
  basis : N -> E                     -- Schauder basis
  coeff : N -> (E ->L[R] R)          -- coefficient functionals
  expansion : ...                    -- f = sum_m coeff_m(f) * basis_m
  basis_growth : ...                 -- p_i(basis_m) <= C * (1+m)^s
  coeff_decay : ...                  -- |coeff_m(f)| * (1+m)^k <= C * p_s(f)
```

All Gaussian measure and heat kernel constructions are parametric in `E`
through this typeclass.

### 2.2 Laplacian eigenvalues: `HasLaplacianEigenvalues E`

**File:** `gaussian-field/HeatKernel/Bilinear.lean`

Typeclass equipping a DyninMityaginSpace with eigenvalues of -Delta.

```
class HasLaplacianEigenvalues (E : Type*) ... where
  eigenvalue : N -> R
  eigenvalue_nonneg : forall m, 0 <= eigenvalue m
```

**Design:** eigenvalues are of -Delta alone (nonneg, zero mode allowed).
Mass enters only through the Green's function. This ensures tensor product
correctness: mu_{E1 ot E2} = mu_{E1} + mu_{E2}.

### 2.3 Nuclear tensor product: `NuclearTensorProduct E1 E2`

**File:** `gaussian-field/Nuclear/NuclearTensorProduct.lean`

Completed projective tensor product of nuclear Frechet spaces, realized
as `RapidDecaySeq` via Cantor pairing s(N) ot s(N) = s(N^2) = s(N).

Has `DyninMityaginSpace` instance. Pure tensors: `NuclearTensorProduct.pure`.
Coefficient factorization: `pure_val` relates tensor product coefficients
to products of factor coefficients.

## 3. Fourier basis and spectral data

### 3.1 Fourier basis: `fourierBasisFun`

**File:** `gaussian-field/SmoothCircle/Basic.lean`

Real Fourier basis functions on S^1_L, indexed by N:

| Index n | Function | Type |
|---------|----------|------|
| 0 | 1/sqrt(L) | constant |
| 2k-1 (k >= 1) | sqrt(2/L) * cos(2*pi*k*x/L) | cosine |
| 2k (k >= 1) | sqrt(2/L) * sin(2*pi*k*x/L) | sine |

Key definitions:
- `fourierBasisFun n : R -> R` -- bare function
- `fourierBasis n : SmoothMap_Circle L R` -- lifted to circle space
- `fourierFreq n : N` -- frequency: 0 for n=0, n/2+1 for n >= 1
- `fourierCoeffReal n f : R` -- L^2 inner product integral_0^L f(x) * psi_n(x) dx
- `fourierCoeffCLM n : SmoothMap_Circle L R ->L[R] R` -- as CLM

### 3.2 Circle eigenvalues

**File:** `gaussian-field/SmoothCircle/Nuclear.lean`

```
circleHasLaplacianEigenvalues : HasLaplacianEigenvalues (SmoothMap_Circle L R)
```

Eigenvalues of -Delta on S^1_L: `mu_n = (2*pi*fourierFreq(n)/L)^2`.
Cosine/sine pairs (2k-1, 2k) share the same eigenvalue (degeneracy).

### 3.3 Lattice eigenvalues

**File:** `gaussian-field/Lattice/Laplacian.lean`

Eigenvalues of the discrete Laplacian -Delta_a on (Z/NZ)^d with spacing a:
```
latticeLaplacianEigenvalue d N a m = (4/a^2) * sum_i sin^2(pi * k_i / N)
```

Mass operator eigenvalues: `latticeEigenvalue d N a mass m = latticeLaplacianEigenvalue + mass^2`.

### 3.4 Lattice DFT coefficients

**File:** `gaussian-field/Lattice/HeatKernelConvergence1d.lean`

```
latticeDFTCoeff1d L N m f = sqrt(L/N) * sum_{j=0}^{N-1} f(j*L/N) * psi_m(j*L/N)
```

These are Riemann-sum approximations to continuum Fourier coefficients.
Convergence proved: `latticeDFTCoeff1d_tendsto`.

### 3.5 Lattice Fourier basis

**File:** `gaussian-field/SmoothCircle/Restriction.lean`

```
latticeFourierBasisFun L N m j = fourierBasisFun m (j * L / N)
```

Sampling of continuum Fourier basis at lattice points. Normalization factor
`sqrt(L/N)` ensures `circleRestriction` maps between spaces correctly.

## 4. Symmetry operations

### 4.1 Circle-level

**File:** `gaussian-field/Torus/Symmetry.lean`

| Operation | Definition | Action |
|-----------|-----------|--------|
| `circleReflection L` | `f |-> f(-.)` | time reflection Theta |
| `circleTranslation L v` | `f |-> f(. - v)` | translation by v |

Both are CLMs (`SmoothMap_Circle L R ->L[R] SmoothMap_Circle L R`).
Continuity proved via Sobolev seminorm bounds.

**Algebra:**
- `circleReflection_involution`: Theta^2 = id
- `circleTranslation_zero`: T_0 = id
- `circleTranslation_add`: T_v . T_u = T_{u+v}

### 4.2 Torus-level (via tensor product lifting)

**File:** `gaussian-field/Torus/Symmetry.lean`

| Operation | Definition | Action |
|-----------|-----------|--------|
| `torusTimeReflection L` | `mapCLM(Theta, id)` | (t,x) |-> (-t,x) |
| `torusTranslation L v` | `mapCLM(T_{v1}, T_{v2})` | (t,x) |-> (t-v1, x-v2) |
| `torusSwap L` | `swapCLM` | (t,x) |-> (x,t) |

These use the tensor product functor axioms
(`nuclearTensorProduct_mapCLM`, `nuclearTensorProduct_swapCLM`).

**Algebra:**
- `torusTimeReflection_involution`: Theta^2 = id (from `mapCLM_comp` + circle involution)

**Symmetry group:** Translations (R/LZ)^2 + D4 point group (generated by
swap + reflections). For OS axioms, the key operation is time reflection
Theta ot id.

### 4.3 Configuration-level (dual actions)

**File:** `gaussian-field/Torus/Symmetry.lean`

Symmetry actions on test functions induce dual actions on configurations
by precomposition: `(T_* omega)(f) = omega(T f)`.

| Operation | Definition |
|-----------|-----------|
| `torusConfigReflection L` | `omega |-> omega . Theta` |
| `torusConfigTranslation L v` | `omega |-> omega . T_v` |

Both are continuous (`torusConfigReflection_continuous`,
`torusConfigTranslation_continuous`).

`torusConfigReflection_involution`: Theta_*^2 = id.

### 4.4 Fourier coefficient transformation

**File:** `gaussian-field/SmoothCircle/FourierTranslation.lean`

How Fourier coefficients transform under symmetries (all proved):

**Reflection** (`f |-> f(-.)`):**
- `fourierCoeffReal_circleReflection_zero`: c_0(Theta f) = c_0(f)
- `fourierCoeffReal_circleReflection_cos`: c_{2k-1}(Theta f) = c_{2k-1}(f) (cosine even)
- `fourierCoeffReal_circleReflection_sin`: c_{2k}(Theta f) = -c_{2k}(f) (sine odd)

**Translation** (`f |-> f(. - v)`):
- `fourierCoeffReal_circleTranslation_zero`: c_0(T_v f) = c_0(f)
- `fourierCoeffReal_circleTranslation_cos`: c_{2k-1}(T_v f) = cos(...) c_{2k-1}(f) - sin(...) c_{2k}(f)
- `fourierCoeffReal_circleTranslation_sin`: c_{2k}(T_v f) = sin(...) c_{2k-1}(f) + cos(...) c_{2k}(f)

**Paired product invariance:**
- `paired_coeff_product_circleTranslation`: c_{2k-1}(Tf) c_{2k-1}(Tg) + c_{2k}(Tf) c_{2k}(Tg) = c_{2k-1}(f) c_{2k-1}(g) + c_{2k}(f) c_{2k}(g)
- `paired_coeff_product_circleReflection`: same for reflection

## 5. Heat kernel and Green's function

### 5.1 Heat kernel: `heatKernelBilinear`

**File:** `gaussian-field/HeatKernel/Bilinear.lean`

Spectral heat kernel on any DyninMityaginSpace with Laplacian eigenvalues:

```
K_t(f, g) = sum_m exp(-t * mu_m) * coeff_m(f) * coeff_m(g)
```

Key properties (all proved):
- `heatKernelBilinear_summable` -- absolute convergence for t > 0
- `heatKernelBilinear_nonneg` -- K_t(f,f) >= 0
- `heatKernelBilinear_le_l2` -- K_t(f,f) <= <f,f>_{L^2}
- `heatKernelBilinear_tendsto_l2` -- K_t -> L^2 inner product as t -> 0+
- `heatKernelBilinear_tensorProduct` -- K_t factors under tensor product

### 5.2 Green's function: `greenFunctionBilinear`

**File:** `gaussian-field/HeatKernel/Bilinear.lean`

Spectral representation of (-Delta + mass^2)^{-1}:

```
G_mass(f, g) = sum_m coeff_m(f) * coeff_m(g) / (mu_m + mass^2)
```

Key properties (all proved):
- `greenFunctionBilinear_summable` -- absolute convergence
- `greenFunctionBilinear_nonneg` -- G(f,f) >= 0
- `greenFunctionBilinear_pos` -- G(f,f) > 0 for f != 0
- `greenFunctionBilinear_le` -- G(f,f) <= (1/mass^2) <f,f>_{L^2}

### 5.3 Green's function invariance

**File:** `gaussian-field/HeatKernel/GreenInvariance.lean`

Invariance under torus symmetries on pure tensors (axioms):
- `greenFunctionBilinear_reflection_pure` -- G(Theta f, Theta g) = G(f,g)
- `greenFunctionBilinear_translation_pure` -- G(T_v f, T_v g) = G(f,g)
- `greenFunctionBilinear_invariant_of_pure` -- extension from pure tensors

Full invariance (proved from axioms):
- `greenFunctionBilinear_timeReflection_invariant`
- `greenFunctionBilinear_swap_invariant`
- `greenFunctionBilinear_translation_invariant`

### 5.4 L^2 inner product: `l2InnerProduct`

**File:** `gaussian-field/HeatKernel/Bilinear.lean`

```
<f, g>_{L^2} = sum_m coeff_m(f) * coeff_m(g)
```

The Parseval identity for the orthonormal Schauder basis. Summable
(`l2InnerProduct_summable`).

### 5.5 Position-space kernels

**File:** `gaussian-field/HeatKernel/PositionKernel.lean`

**Circle heat kernel:** `circleHeatKernel t theta1 theta2` --
periodized Gaussian / Jacobi theta function on S^1_L. Proved positive
(`circleHeatKernel_pos` via Hurwitz zeta / Poisson summation).

**Mehler kernel:** `mehlerKernel t x1 x2` -- harmonic oscillator heat kernel
(closed form). Connection to Hermite eigenfunction expansion is axiomatized
(`mehlerKernel_eq_series`).

### 5.6 Spectral multiplier CLM: `spectralCLM`

**File:** `gaussian-field/HeatKernel/Axioms.lean`

Given a bounded multiplier sequence sigma : N -> R, constructs a CLM
`E ->L[R] ell2` acting as `f |-> (sigma_m * coeff_m(f))_m`. Used to
build the covariance CLM for Gaussian measures.

## 6. Lattice operators and measures

### 6.1 Discrete Laplacian: `finiteLaplacian`

**File:** `gaussian-field/Lattice/Laplacian.lean`

```
(Delta_a f)(x) = (1/a^2) * sum_i [f(x + e_i) + f(x - e_i) - 2*f(x)]
```

Self-adjoint (`finiteLaplacian_selfAdjoint`, proved).

### 6.2 Lattice covariance: `latticeCovariance`

**File:** `gaussian-field/Lattice/Covariance.lean`

CLM `T = Q^{-1/2} : FinLatticeField d N ->L[R] ell2` where Q = -Delta_a + m^2.
Singular values: `latticeSingularValue d N a mass m = lambda_m^{-1/2}`.
Bounded sequence (`lattice_singular_values_bounded`).

### 6.3 Lattice Gaussian measure: `latticeGaussianMeasure`

**File:** `gaussian-field/Lattice/Covariance.lean`

Centered Gaussian measure on `Configuration (FinLatticeField d N)` with
covariance `C(f,g) = <Tf, Tg>_{ell2}` where T is the lattice covariance CLM.
Constructed via `GaussianField.measure`.

### 6.4 Gaussian measure construction: `GaussianField.measure`

**File:** `gaussian-field/GaussianField/Construction.lean`

Given a CLM `T : E ->L[R] H` from a nuclear Frechet space to a separable
Hilbert space, constructs a centered Gaussian probability measure mu on
`Configuration E` with covariance `C(f,g) = <T(f), T(g)>_H`.

Construction: nuclear SVD factorization -> noise measure (product of N(0,1))
-> series limit map `omega(f) = sum_n xi_n <e_n, T(f)>` -> pushforward.

Characteristic functional: `charFun` gives `E[exp(i*omega(f))] = exp(-||Tf||^2/2)`.

## 7. Embeddings

### 7.1 Circle restriction: `circleRestriction`

**File:** `gaussian-field/SmoothCircle/Restriction.lean`

Sampling of smooth periodic functions at lattice points:
```
circleRestriction L N : SmoothMap_Circle L R ->L[R] FinLatticeField 1 N
```

Maps `f |-> (f(j*L/N))_{j in Z/NZ}`. Normalization involves `sqrt(L/N)`.

### 7.2 Torus embedding CLM: `torusEmbedCLM`

**File:** `gaussian-field/Torus/Evaluation.lean`

Embedding of lattice fields into torus Configuration space:
```
torusEmbedCLM L N : FinLatticeField 2 N ->L[R] R
```

Lifts lattice field configurations into the dual of `TorusTestFunction L`
via evaluation at lattice sites.

### 7.3 Lattice embedding: `latticeEmbed`

**File:** `pphi2/Pphi2/ContinuumLimit/Embedding.lean`

Embedding of lattice configurations into S'(R^2) for the infinite-volume
continuum limit.

### 7.4 Torus embedding lift: `torusEmbedLift`

**File:** `pphi2/Pphi2/TorusContinuumLimit/TorusEmbedding.lean`

Maps lattice configurations to torus `Configuration` space:
```
torusEmbedLift L N : FinLatticeField 2 N -> Configuration (TorusTestFunction L)
```

Pushforward of lattice Gaussian measure defines `torusContinuumMeasure`.

## 8. Continuum limit measures

### 8.1 Gaussian continuum measure (S'(R^2))

**File:** `pphi2/Pphi2/GaussianContinuumLimit/EmbeddedCovariance.lean`

```
gaussianContinuumMeasure mass : Measure (Configuration ContinuumTestFunction)
```

Limit of embedded lattice Gaussian measures as a -> 0.
Proved Gaussian (`gaussianContinuumMeasure_isGaussian`) with covariance
converging to the continuum Green's function.

### 8.2 Torus continuum measure

**File:** `pphi2/Pphi2/TorusContinuumLimit/TorusConvergence.lean`

```
torusContinuumMeasure L mass : Measure (Configuration (TorusTestFunction L))
```

Weak limit of `torusEmbedLift_*(latticeGaussianMeasure)` as N -> inf.
Extraction via Prokhorov's theorem on the Polish torus configuration space
(proved, not axiomatized).

### 8.3 Interacting lattice measure

**File:** `pphi2/Pphi2/InteractingMeasure/Action.lean`

```
interactingLatticeMeasure d N a mass P : Measure (Configuration (FinLatticeField d N))
```

Wick-ordered P(phi)_2 measure: `(1/Z) * exp(-V_a(phi)) * d(mu_GFF)` where
`V_a = a^2 * sum_x :P(phi(x)):_a`.

## 9. Convergence results

### 9.1 Eigenvalue convergence

- `latticeEigenvalue1d_tendsto`: lattice eigenvalue -> continuum eigenvalue
  as N -> inf (via sinc factorization)
- `latticeEigenvalue1d_ge_8m`: eigenvalue lower bound via Jordan's inequality

### 9.2 DFT coefficient convergence

- `latticeDFTCoeff1d_tendsto`: lattice DFT coefficients -> continuum Fourier
  coefficients via Riemann sum convergence (proved)
- `latticeDFTCoeff1d_flat_bound`: uniform bound |c_m| <= sqrt(2L) * ||f||_C0

### 9.3 Heat kernel convergence (1D)

**File:** `gaussian-field/Lattice/HeatKernelConvergence1d.lean`

- `lattice_heatKernel_tendsto_continuum_1d`: full 1D heat kernel bilinear
  form convergence (proved via Tannery's theorem / dominated convergence)

### 9.4 Green's function convergence (2D)

**File:** `gaussian-field/Lattice/Convergence.lean`

- `lattice_green_tendsto_continuum_pure`: convergence for pure tensors
  via Tannery's theorem on N x N (proved)
- `lattice_green_tendsto_continuum`: bilinear extension to general elements
  (axiom)

### 9.5 Propagator convergence

**Files:** `pphi2/Pphi2/GaussianContinuumLimit/PropagatorConvergence.lean`,
`pphi2/Pphi2/TorusContinuumLimit/TorusPropagatorConvergence.lean`

Lattice propagator -> continuum Green's function, with uniform bounds.

## 10. Interaction polynomial

**File:** `pphi2/Pphi2/Polynomial.lean`

```
structure InteractionPolynomial where
  P : Polynomial R
  even : P.mirror = P
  deg_ge : 4 <= P.natDegree
  bounded_below : exists c, forall x, c <= P.eval x
```

An even polynomial of degree >= 4, bounded below. Examples: lambda*tau^4,
lambda*tau^4 + mu*tau^2, (tau^2 - a^2)^4.

## 11. Relationship diagram

```
SmoothMap_Circle L R                     FinLatticeField d N
     |                                         |
     | (tensor product)                        | (lattice covariance CLM)
     v                                         v
TorusTestFunction L                    Configuration(FinLatticeField)
     |                                         |
     | (weak dual)                             | (torusEmbedLift / latticeEmbed)
     v                                         v
Configuration(Torus)  <--- Prokhorov ---  Embedded measures
     |
     | (weak limit N -> inf)
     v
torusContinuumMeasure / gaussianContinuumMeasure
```

Key bridges:
- `circleRestriction`: SmoothMap_Circle -> FinLatticeField (sampling)
- `torusEmbedLift`: FinLatticeField -> Configuration(Torus) (embedding)
- `GaussianField.measure`: nuclear SVD -> Gaussian probability measure
- Fourier coefficient CLMs: test function space -> R (both lattice and continuum)

## 12. Axiom summary (spacetime-related)

| Axiom | File | Purpose |
|-------|------|---------|
| `nuclearTensorProduct_mapCLM` | Nuclear/TensorProductFunctorAxioms | Tensor product of CLMs |
| `nuclearTensorProduct_swapCLM` | Nuclear/TensorProductFunctorAxioms | Swap factors |
| `nuclearTensorProduct_mapCLM_comp` | Nuclear/TensorProductFunctorAxioms | Functoriality |
| `nuclearTensorProduct_mapCLM_id` | Nuclear/TensorProductFunctorAxioms | Identity |
| `nuclearTensorProduct_mapCLM_pure` | Nuclear/TensorProductFunctorAxioms | Action on pure tensors |
| `nuclearTensorProduct_swapCLM_pure` | Nuclear/TensorProductFunctorAxioms | Swap on pure tensors |
| `configuration_torus_polish` | Torus/Restriction | Polish space for Configuration(Torus) |
| `configuration_torus_borelSpace` | Torus/Restriction | Cylindrical = Borel sigma-algebra |
| `greenFunctionBilinear_reflection_pure` | HeatKernel/GreenInvariance | Green fn reflection invariance |
| `greenFunctionBilinear_translation_pure` | HeatKernel/GreenInvariance | Green fn translation invariance |
| `greenFunctionBilinear_invariant_of_pure` | HeatKernel/GreenInvariance | Extension from pure tensors |
| `mehlerKernel_eq_series` | HeatKernel/PositionKernel | Mehler formula = Hermite expansion |

## References

- Dynin, Mityagin, "Criterion for nuclearity in terms of approximative dimension"
- Gel'fand-Vilenkin, *Generalized Functions* Vol. 4
- Treves, *Topological Vector Spaces, Distributions, and Kernels*, Ch. 43, 50
- Glimm-Jaffe, *Quantum Physics: A Functional Integral Point of View*
- Simon, *The P(phi)_2 Euclidean (Quantum) Field Theory*
