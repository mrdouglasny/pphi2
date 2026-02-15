# Plan: Formal Construction of P(Phi)_2 in Lean 4

## Goal

Formalize the construction of the P(Phi)_2 Euclidean quantum field theory
on the plane and verify the Osterwalder-Schrader axioms, following
Duch-Dybalski-Jahandideh (arXiv:2311.04137).

The main theorem to be proved:

> The sequence of measures (j_R^* # mu_R)_{R in N_+} on S'(R^2) has a weakly
> convergent subsequence. Every accumulation point mu is invariant under the
> Euclidean symmetries of the plane and reflection positive. Moreover, there
> exists a ball B in S(R^2) such that for all f in B,
> integral exp(phi(f)^n) d mu(phi) <= 2.

This establishes OS axioms E1 (Euclidean invariance), E2 (reflection
positivity), and E5 (regularity) for the interacting theory. Clustering (E4)
is not proved in DDJ and is known only for small coupling.

---

## Primary Reference

**Duch, Dybalski, Jahandideh** (2311.04137):
*Stochastic quantization of two-dimensional P(Phi) Quantum Field Theory*

Located at: `refs/duch-dybalski-jahandideh-2311.04137/sphere.tex`

### Supplementary References

- Barashkov-Gubinelli (1805.10814): Variational method for Phi^4_3
- Gubinelli-Hofmanova (1810.01700): PDE construction of Phi^4_3
- Barashkov-Gubinelli (2112.05562): Infinite volume phi^4_2 tightness
- Gubinelli (2025): GSSI lecture notes on fractional Phi^4_3

---

## Proof Architecture (DDJ)

### Section 2: UV Limit (sphere.tex lines 166-298)

**Input:** Polynomial P(tau) of degree n >= 4 (n even), coupling lambda > 0.

**Definitions:**
- S_R: round 2-sphere of radius R
- G_R = (1 - Delta_R)^{-1}: free covariance on S_R
- K_{R,N} = (1 - Delta_R/N^2)^{-1}: UV regularization operator
- G_{R,N} = K_{R,N} G_R K_{R,N}: regularized covariance
- nu_{R,N}: Gaussian measure on D'(S_R) with covariance G_{R,N}
- c_{R,N} = Tr(G_{R,N}) / (4 pi R^2): counterterm (Wick ordering constant)
- P(tau, c): Wick-ordered polynomial (Hermite polynomial form)
- mu_{R,N}: regularized P(Phi)_2 measure = (1/Z) exp(-int P(phi, c_{R,N})) d nu_{R,N}
- mu_{R,N}^g: auxiliary measure with extra exp(phi(g)^n/n) factor

**Key results:**
- **Lemma 2.1** (mu_measure_well_defined): mu_{R,N}^g is well-defined, measures
  concentrate on L^1_2(S_R)
- **Lemma 2.3** (polynomial_bound): P(tau, c) >= tau^n/(2n) - A c^{n/2}
- **Proposition 2.4** (uv_limit): UV limit N -> infinity exists by Vitali's theorem.
  Uses Nelson hypercontractivity (Lemma C.4) for uniform integrability.

**Proof technique:** Vitali's convergence theorem. Need convergence in probability
(from stochastic estimates in Appendix C) and uniform integrability (from Nelson
hypercontractivity + polynomial lower bound).

### Section 3: Stochastic Quantization (lines 300-438)

**Key idea:** The P(Phi)_2 measure is the stationary distribution of a stochastic
PDE (Parisi-Wu). Use the Da Prato-Debussche trick to decompose the solution.

**Definitions:**
- W_R(t): cylindrical Wiener process on L_2(S_R)
- Q_{R,N} = (1 - Delta_R)(1 - Delta_R/N^2)^2: drift operator
- Z_{R,N}(t): OU process (free field dynamics), stationary dist = nu_{R,N}
- Phi_{R,N}^g(t): interacting dynamics, stationary dist = mu_{R,N}^g
- Psi_{R,N}^g := Phi_{R,N}^g - Z_{R,N}: Da Prato-Debussche remainder

**Key results:**
- **Lemma 3.3** (Law_Z_phi): Law(Z_{R,N}(t)) = nu_{R,N} and
  Law(Phi_{R,N}^g(t)) = mu_{R,N}^g for all t (stationarity)
- **Eq. (3.13)** (varPsi_pde): PDE for Psi (non-singular in N -> infinity limit):
  d_t Psi = -Q Psi - P'(Psi + Z, c) + ((Psi+Z)(g))^{n-1} g
- **Eq. (3.17)** (varPsi_pde2): Expanded form separating Psi^{n-1} from
  stochastic forcing terms involving Z^{:m-l:} Psi^l

### Section 4: Stereographic Projection (lines 442-482)

**Definitions:**
- j_R : R^2 -> S_R \ {north pole}: stereographic parametrization
- w_R(x) = 16R^4 / (4R^2 + |x|^2)^2: conformal weight
- j_R^* : D'(S_R) -> S'(R^2): pullback of distributions

**Key identities:**
- Volume form: rho_R(dx) = w_R(x) dx in stereographic coordinates
- Laplacian: j_R^* Delta_R = w_R^{-1} Delta j_R^*
- Distribution pullback: <j_R^* phi, f> = <phi, (w_R^{-1} f) o j_R^{-1}>

### Section 5: A Priori Bound / Energy Estimate (lines 488-570)

**This is the core technical section.** The energy method provides bounds
uniform in both R (infrared) and N (ultraviolet).

**Definitions:**
- v_L = (1/(4 pi L^2)) w_L^8: polynomial weight on R^2

**Key results:**
- **Proposition 5.1** (energy_method): For R >= L, N >= 1, g sufficiently small:

      8 d_t ||j_R^* Psi||^2_{L_2(v_L^{1/2})}
        + ||j_R^* Psi||^n_{L_n(v_L^{1/n})}
        <= C sum_{k=0}^{n-1} ||j_R^* Z^{:k:}||^p_{L_p^{-kappa}(v_L^{1/p})}

  This bounds the Psi norm growth by free-field stochastic terms.

- **Lemma 5.2** (weights_derivatives): Integration by parts estimates (A), (B), (C)
  for weighted Laplacian powers. Requires L sufficiently large.
- **Remark 5.3** (L_two_interms_of_L_n): L_2 weighted norm controlled by L_n.

**Proof technique:** Multiply Psi PDE by v_L * Psi, integrate over R^2.
The nonlinear term gives coercive ||Psi||^n_{L_n}. Cross terms
Z^{:m:} Psi^l bounded by Lemma A.5 (Young + Sobolev interpolation).
The g-dependent term bounded by choosing ball B small enough.

### Section 6: Tightness (lines 645-711)

**Key results:**
- **Proposition 6.1** (tightness): Uniform moment bound:
  integral ||j_R^* phi||^n_{L_n^{-kappa}(v_L^{1/n})} d mu^g_{R,N} <= C

- **Remark 6.2**: By compact embedding L_n^{-kappa}(v_L^{1/n}) -> L_n^{-2kappa}(v_L^{2/n})
  and tightness criterion (Lemma B.5), the sequence (j_R^* # mu_R) is tight.
  Prokhorov's theorem gives a weakly convergent subsequence.

**Proof technique:** Use stationarity (Lemma 3.3) to convert spatial moment
to time-averaged moment. Apply energy estimate (Prop 5.1) to bound time
average. Use free-field moment bounds (Lemma C.6) for the RHS.

### Section 7: Integrability / OS Regularity (lines 715-767)

**Key results:**
- **Proposition 7.1** (integrability): There exists ball B in S(R^2) such that
  for all f in B: integral exp(phi(f)^n) d mu(phi) <= 2.

**Proof technique:** Hairer-Steele argument. Use the auxiliary measure mu^g
and the variational bound (Lemma 7.2, from Barashkov):
  integral exp(F) d mu <= exp(integral F d mu^F).
Combine with tightness bound (Prop 6.1) and Holder's inequality.

### Section 8: Reflection Positivity (lines 770-909)

**Key idea:** Finite-volume measure mu_R on S_R is reflection positive.
This transfers to the infinite-volume limit.

**Important subtlety:** The spectral UV cutoff K_{R,N} breaks reflection
positivity. DDJ introduce a *local* UV cutoff hat{K}_{R,N} with kernel
hat{K}_{R,N}(x,y) = N^2 h(N d_R(x,y)) that preserves RP.

**Definitions:**
- Theta_R: reflection x_1 -> -x_1 on S_R (and Theta on R^2)
- S_{R,N}^+, S_{R,N}^-: half-spheres with 1/N gap
- F_R^+, F_{R,N}^+: cylindrical functionals supported on half-spheres
- hat{K}_{R,N}: local UV regularization operator (Def 8.3)
- hat{X}_{R,N}, tilde{Y}_{R,N}: free field and action with local cutoff

**Key results:**
- **Lemma 8.5** (reflection_positivity): Four-step proof:
  (A) Free field X_R on S_R is RP (cite Dimock 2004)
  (B) hat{X}_{R,N} = hat{K}_{R,N} X_R is RP (support property of local kernel)
  (C) exp(-tilde{Y}_{R,N}) preserves RP (half-space factorization Y = Y^+ + Y^-)
  (D) mu_R is RP (UV limit: hat cutoff -> no cutoff via Lemma 8.4)

- **Proposition 8.1** (reflection_positivity for mu): Passes RP from mu_R to
  limit mu by weak convergence.

### Section 9: Euclidean Invariance (lines 912-1070)

**Key insight:** dim SO(3) = dim E(2) = 3.

**Rotational invariance:** Rotations R_{R,alpha} around x_3 axis of S_R correspond
exactly to rotations R_alpha of R^2 under stereographic projection. Since mu_R
is SO(3)-invariant, j_R^* # mu_R is rotationally invariant, and so is the limit.

**Translational invariance:** More subtle. Rotations T_{R,alpha} around x_2 axis
map under stereographic projection to transformations S_{R,alpha} of R^2 that
are NOT translations. But S_{R,alpha} -> T_alpha as R -> infinity.

**Key results:**
- **Remark 9.3** (translation): |partial^a S_{R,alpha}(x) - partial^a T_alpha(x)| <= C/R
- **Proposition 9.1** (euclidean_inv_plane): mu is both rotationally and
  translationally invariant.

### Appendix A: Function Spaces (lines 1077-1228)

Weighted Bessel potential spaces L^alpha_p(R^d, w), Sobolev embeddings,
multiplication theorem, interpolation theorem, and the key estimate
Lemma A.5 (Z_Psi_n) bounding cross-terms.

### Appendix B: Mathematical Preliminaries (lines 1239-1293)

Prokhorov's theorem, tightness criterion via compact embeddings,
trace estimates for spectral sums on spheres.

### Appendix C: Stochastic Estimates (lines 1295-1623)

Wiener chaos, Hermite polynomials, Nelson hypercontractivity,
moment bounds for free fields uniform in R and N. The key result
is Lemma C.6 (stochastic_bound_infinite_volume): free field moments
in weighted Bessel spaces are bounded uniformly in R, N.

---

## Dependency Diagram

```
                    Appendix A              Appendix B           Appendix C
                  (Function Spaces)      (Prokhorov etc.)    (Stochastic Est.)
                   /     |     \               |                /    |    \
                  /      |      \              |               /     |     \
    Sec 4        /  Sec 5: Energy \        Sec 6: Tight.  Sec 2: UV Limit
  (Stereo.) ---/   Estimate (core) \-------->  |  <------      |
       \       /         |          \          |           Sec 3: Stoch. Quant.
        \     /          |           \         |              /
         \   /           v            v        v             /
          \ /     Sec 7: Integrability   Sec 8: RP         /
           \             |                  |              /
            \            v                  v             /
             -----> Sec 9: Euclidean Invariance <--------
                            |
                            v
                      MAIN THEOREM
```

---

## What Transfers from OSforGFF

The OSforGFF project (47 files, ~31,600 lines, 0 sorries) provides:

### Directly reusable:
1. **OS axiom definitions** (`OS_Axioms.lean`): OS0-OS4 formalized for
   measures on S'(R^4). Need to adapt to d=2 (change SpaceTime from R^4 to R^2).
2. **Positive definiteness** (`PositiveDefinite.lean`, `SchurProduct.lean`,
   `HadamardExp.lean`): General theory of PD functions/kernels.
3. **Nuclear space framework** (`NuclearSpace.lean`): Definition + schwartz_nuclear axiom.
4. **Minlos theorem** (`Minlos.lean`): Measure existence on nuclear spaces.
   (Though DDJ doesn't use Minlos directly -- measures are constructed via limits.)
5. **Schwartz function infrastructure** (`FunctionalAnalysis.lean`,
   `ComplexTestFunction.lean`): Embeddings, integrability, decay.
6. **Distribution pairing** (`Basic.lean`): WeakDual-based FieldConfiguration.

### Partially reusable (needs adaptation):
7. **Euclidean group action** (`Euclidean.lean`): Need E(2) instead of E(4).
8. **Reflection and time translation** (`DiscreteSymmetry.lean`,
   `TimeTranslation.lean`): Structure transfers but details differ in d=2.
9. **Generating functionals** (`Basic.lean`): General framework applicable.
10. **Covariance theory** (`Covariance.lean`, `CovarianceR.lean`): Free field
    covariance. OSforGFF works in d=4 with mass; here we need d=2 on spheres.

### Not reusable (must build new):
- Everything related to spheres S_R, stereographic projection
- Stochastic quantization / SPDE theory
- Wick ordering on spheres
- Weighted Bessel potential spaces with polynomial weights
- Energy estimates
- Nelson hypercontractivity for Wiener chaos on spheres
- Tightness and Prokhorov machinery
- Local UV cutoff and its RP properties

---

## What Needs Mathlib (and likely exists)

1. **Spherical harmonics and Laplace-Beltrami** -- Partial: Mathlib has some
   manifold theory but likely not spectral theory on S^2 specifically.
2. **Prokhorov's theorem** -- Mathlib has `MeasureTheory.Measure.tightness`
   infrastructure but may not have the full theorem.
3. **Sobolev embedding theorems** -- Likely not in Mathlib for weighted spaces.
4. **Cylindrical Wiener process** -- Not in Mathlib.
5. **Hermite polynomials** -- Mathlib has `Polynomial.hermite`.
6. **Semigroup theory (e^{-tA})** -- Partial in Mathlib.
7. **Weak convergence of measures** -- Mathlib has portmanteau etc.
8. **Compact embeddings** -- Need Rellich-Kondrachov type results.

---

## Proposed Lean File Structure

```
Pphi2/
  -- Core setup
  Basic.lean              -- R^2 as SpaceTime, S_R definition, basic notation
  Polynomial.lean         -- P(tau) polynomial, degree n >= 4, P bounded below
  WickOrdering.lean       -- Wick-ordered polynomial P(tau, c), Hermite expansion

  -- Function spaces (Appendix A)
  FunctionSpaces/
    WeightedLp.lean       -- L_p(R^d, w) weighted spaces
    BesselPotential.lean  -- L^alpha_p(R^d, w) weighted Bessel potential spaces
    SobolevSphere.lean    -- L^alpha_p(S_R) Bessel potential spaces on sphere
    Embedding.lean        -- Sobolev embeddings (Thm A.5), compact embeddings (Thm A.5(C))
    Multiplication.lean   -- Sobolev multiplication (Thm A.6)
    Interpolation.lean    -- Sobolev interpolation (Thm A.7)
    ZPsiEstimate.lean     -- Cross-term estimate Lemma A.5 (Z_Psi_n)

  -- Sphere geometry
  Sphere/
    Basic.lean            -- S_R in R^3, geodesic distance, Riemannian measure
    LaplaceBeltrami.lean  -- Delta_R, spectral decomposition, eigenvalues l(l+1)/R^2
    SphericalHarmonics.lean  -- Eigenspaces, Legendre polynomials
    StereographicProj.lean   -- j_R, w_R, pullback j_R^*, Laplacian identity

  -- Gaussian measure on sphere (Section 2)
  GaussianSphere/
    Covariance.lean       -- G_R = (1-Delta_R)^{-1}, regularized G_{R,N}
    Counterterm.lean      -- c_{R,N} = Tr(G_{R,N})/(4pi R^2), bound |c - log N/2pi| <= C
    GaussianMeasure.lean  -- nu_{R,N} on D'(S_R), concentration on L^1_2(S_R)
    WickFields.lean       -- X_{R,N}, X^{:m:}_{R,N}, Y_{R,N}, Y^g_{R,N}

  -- P(Phi)_2 measure on sphere (Section 2)
  MeasureSphere/
    Regularized.lean      -- mu_{R,N} and mu_{R,N}^g, well-definedness (Lem 2.1)
    PolynomialBound.lean  -- P(tau,c) >= tau^n/(2n) - A c^{n/2} (Lem 2.3)
    UVLimit.lean          -- UV limit mu_R = lim mu_{R,N} via Vitali (Prop 2.4)

  -- Stochastic quantization (Section 3)
  StochasticQuant/
    WienerProcess.lean    -- Cylindrical Wiener process W_R(t)
    OUProcess.lean        -- Z_{R,N}(t) OU process, mild solution
    InteractingSPDE.lean  -- Phi_{R,N}^g(t) interacting dynamics, mild solution
    DapratoDebussche.lean -- Psi = Phi - Z, PDE for Psi (non-singular)
    Stationarity.lean     -- Law(Z(t)) = nu, Law(Phi(t)) = mu (Lem 3.3)

  -- Stochastic estimates (Appendix C)
  StochasticEst/
    WienerChaos.lean      -- Wiener chaos, Hermite structure
    NelsonHypercontractivity.lean  -- Nelson estimate (Lem C.4)
    MomentBounds.lean     -- Lem C.1 (non-uniform), Lem C.2 (uniform in R,N)
    YConvergence.lean     -- Y_{R,N} convergence (Lem C.3)
    InfiniteVolumeBound.lean  -- ||j_R^* X^{:m:}||_{L^{-kappa}_p} <= C (Lem C.6)

  -- Energy estimate (Section 5)
  Energy/
    Weight.lean           -- v_L = w_L^8 / (4 pi L^2)
    WeightEstimates.lean  -- Integration by parts (Lem 5.2 A,B,C)
    EnergyEstimate.lean   -- Main a priori bound (Prop 5.1)

  -- Infinite volume limit (Section 6)
  InfiniteVolume/
    Tightness.lean        -- Uniform moment bound (Prop 6.1)
    Prokhorov.lean        -- Prokhorov's theorem, weak convergence
    Limit.lean            -- Existence of accumulation point mu

  -- Integrability (Section 7)
  Integrability/
    VariationalBound.lean -- Lemma 7.2 (Barashkov's variational inequality)
    Regularity.lean       -- OS regularity: int exp(phi(f)^n) d mu <= 2 (Prop 7.1)

  -- Reflection positivity (Section 8)
  ReflectionPositivity/
    Reflection.lean       -- Theta_R on S_R, Theta on R^2, half-spheres
    CylindricalFunctionals.lean  -- F_R, F_R^+, F_{R,N}^+
    LocalUVCutoff.lean    -- hat{K}_{R,N} with local kernel (Def 8.3)
    LocalFields.lean      -- hat{X}_{R,N}, tilde{Y}_{R,N} (Def 8.5)
    UVConvergence.lean    -- Local cutoff -> no cutoff (Lem 8.4)
    RPSphere.lean         -- RP for mu_R (Lem 8.5 A-D)
    RPPlane.lean          -- RP for mu (Prop 8.1)

  -- Euclidean invariance (Section 9)
  EuclideanInvariance/
    RotationSphere.lean   -- R_{R,alpha}: rotation of S_R around x_3
    TranslationSphere.lean -- T_{R,alpha}: rotation around x_2
    SRalpha.lean          -- S_{R,alpha} = j_R^{-1} o T_{R,alpha} o j_R on R^2
    Convergence.lean      -- S_{R,alpha} -> T_alpha as R -> infty (Rem 9.3)
    Invariance.lean       -- mu is E(2)-invariant (Prop 9.1)

  -- Main theorem
  Main.lean               -- Assembly of all OS axioms for P(Phi)_2
```

---

## Formalization Strategy

### Phase 1: Foundation (Parallel tracks)

**Track A: Function spaces** (can start immediately)
- Weighted L_p spaces, Bessel potential spaces
- Sobolev embeddings on R^2 and S_R
- These are general and don't depend on the specific QFT problem

**Track B: Sphere infrastructure** (can start immediately)
- S_R as a Riemannian manifold in Lean/Mathlib
- Spectral theory of Laplace-Beltrami (eigenvalues l(l+1)/R^2)
- Stereographic projection and its properties

**Track C: Port OS axiom definitions** (quick, from OSforGFF)
- Adapt OS axiom definitions from d=4 to d=2
- Set up FieldConfiguration = WeakDual R (SchwartzMap R^2 R)

### Phase 2: Gaussian Theory on Spheres

- Free covariance G_R, regularized G_{R,N}
- Counterterm bounds (Lemma B.1)
- Gaussian measure nu_{R,N} on D'(S_R)
- Wick ordering, Hermite polynomials
- Nelson hypercontractivity

### Phase 3: Stochastic Quantization

- Cylindrical Wiener process (may need significant new Mathlib work)
- OU process Z_{R,N}
- Interacting process Phi_{R,N}^g
- Da Prato-Debussche decomposition
- Stationarity of measures

### Phase 4: Core Estimates

- Energy estimate (Prop 5.1) -- the hardest analytical part
- Stochastic moment bounds uniform in R, N (Appendix C)
- Cross-term estimates (Lemma A.5)

### Phase 5: Limit and Axioms

- Tightness (Prop 6.1) via energy estimate
- Prokhorov -> weak convergence
- Integrability / OS regularity (Prop 7.1)
- Reflection positivity (Sec 8) -- needs local cutoff
- Euclidean invariance (Sec 9) -- the payoff of the sphere approach

### Phase 6: Assembly

- Main theorem combining all axioms

---

## Key Difficulties and Gaps

### Hard parts:
1. **Cylindrical Wiener process in Lean**: No existing formalization.
   This is a major infrastructure piece. May need to axiomatize initially.
2. **Spectral theory on S_R**: Eigenvalue decomposition of Laplace-Beltrami.
   Mathlib has some manifold theory but not this specifically.
3. **Energy estimate (Prop 5.1)**: Technically involved, requires careful
   integration by parts with weights. Many intermediate bounds.
4. **Sobolev embedding/interpolation with weights**: Not in Mathlib.
   Could axiomatize or build from scratch.

### Likely axioms needed:
- Spectral decomposition of Laplace-Beltrami on S_R
- Cylindrical Wiener process existence and properties
- Sobolev embedding theorems for weighted spaces
- Nelson hypercontractivity (or Gross's log-Sobolev inequality)
- Prokhorov's theorem (if not yet in Mathlib)
- Possibly: semigroup theory for e^{-tQ}

### Estimated effort:
- **Phase 1**: 2-4 months (function spaces + sphere infrastructure)
- **Phase 2**: 1-2 months (Gaussian theory, leveraging OSforGFF patterns)
- **Phase 3**: 2-3 months (stochastic quantization -- most novel)
- **Phase 4**: 3-4 months (core estimates -- most technically demanding)
- **Phase 5**: 2-3 months (limits and axiom verification)
- **Phase 6**: 1 month (assembly and polish)

---

## Immediate Next Steps

1. Set up the directory structure in Pphi2/
2. Define R^2 as SpaceTime, S_R, basic notation
3. Start function space definitions (weighted Bessel potential spaces)
4. Port OS axiom definitions from OSforGFF (adapt d=4 -> d=2)
5. Define stereographic projection j_R and prove basic identities
6. Begin Gaussian measure on sphere (covariance G_R)
