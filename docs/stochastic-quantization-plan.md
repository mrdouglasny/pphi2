# Stochastic Quantization Plan for P(Phi)_2

## Goal

Add a stochastic quantization module to pphi2 that constructs the
P(Phi)_2 measure on the 2D torus T^2_L as the invariant measure of the
stochastic PDE (Langevin equation):

$$\partial_\tau \phi = \Delta\phi - m^2\phi - P'(\phi) + \sqrt{2}\,\eta$$

where $\eta$ is space-time white noise. This provides a second
nonperturbative construction of the same measure, independent of the
lattice/Prokhorov approach (Route B). The identification of the two
constructions is a nontrivial consistency check and enables new proof
strategies for remaining axioms (notably `spectral_gap_uniform` via
log-Sobolev/Bakry-Emery).

## Mathematical Approach: Da Prato-Debussche (2003)

We follow the Da Prato-Debussche approach, which is the simplest
rigorous SPDE construction for Phi^4_2. The key idea: decompose the
solution as $\phi = Z + v$ where:

- $Z$ is the **stationary Ornstein-Uhlenbeck process** — the solution of
  the linearized equation $\partial_\tau Z = (\Delta - m^2) Z + \sqrt{2}\,\eta$.
  This is an explicit Gaussian process constructed via stochastic
  convolution.
- $v = \phi - Z$ solves a **remainder PDE** with better regularity:
  $\partial_\tau v = (\Delta - m^2) v - P'(Z + v)$.
  The nonlinearity $P'(Z + v)$ involves products of distributions,
  which require Wick renormalization. For $P(\tau) = \lambda \tau^4$,
  $P'(\tau) = 4\lambda \tau^3$, and $Z^3$ requires subtracting $3 c_\infty Z$
  where $c_\infty = E[Z(t,x)^2]$ is the Wick constant. This is exactly
  the same Wick ordering as in the lattice construction.

The critical regularity fact: on T^2, $Z \in C^{-\varepsilon}$ a.s.
(negative Holder regularity, i.e., a distribution just barely worse
than a function). After Wick renormalization, $:Z^3:$ makes sense as a
distribution, and $v$ has strictly better regularity than $Z$, so $v$
can be found by a fixed-point argument in an appropriate function space.

**Reference:** Da Prato and Debussche, "Strong solutions to the
stochastic quantization equations," *Ann. Probab.* **31** (2003),
1900-1916.

## Existing Infrastructure

### In this project (pphi2)
- Wick ordering (`WickOrdering/`) — Wick monomials, counterterms, uniform lower bounds
- Torus P(Phi)_2 measure (`TorusContinuumLimit/`) — 0 axioms, 0 sorries
- Torus embedding and Green's function (`TorusEmbedding.lean`)
- Fourier eigenvalues on T^2 (`TorusPropagatorConvergence.lean`)

### hille-yosida (../hille-yosida)
- C_0-semigroups (`StronglyContinuousSemigroup.lean`) — 0 axioms
- Infinitesimal generators, domains, growth bounds
- Resolvent operators, Hille-Yosida bound ||R(lambda)|| <= 1/lambda
- ~8,500 lines, fully proved

### brownian-motion (../brownian-motion)
- Brownian motion construction via Kolmogorov extension — complete, published
- Kolmogorov-Chentsov theorem (path regularity) — complete
- Holder continuity infrastructure — complete
- Stochastic integral infrastructure (in progress, 46 sorries)
- ~14,300 lines

### stochasticpde-itocalculus (../stochasticpde-itocalculus)
- Ito integral (1D, L^2 construction) — 0 sorries
- Ito isometry — 0 sorries
- Ito formula — 0 sorries
- Quadratic variation — 0 sorries
- Kolmogorov-Chentsov (independent implementation) — 0 sorries
- ~24,400 lines, fully proved

### Mathlib
- Holder spaces (HolderWith, HolderNorm, MemHolder)
- Tempered distributions (complete, including Fourier transform)
- Schwartz space, Fourier analysis
- L^p spaces (comprehensive)
- Gaussian distributions, Fernique's theorem
- NO: Besov spaces, heat semigroup, stochastic convolution, cylindrical Wiener process

## Module Plan

### Phase 0: Dependencies and Lakefile (1 week)

Add hille-yosida as a Lake dependency. Verify that pphi2, hille-yosida,
brownian-motion, and stochasticpde-itocalculus can coexist (they all
depend on Mathlib; version pinning may be needed).

**Decision:** Whether to depend on brownian-motion and
stochasticpde-itocalculus directly, or to extract the needed components.
The brownian-motion repo depends on kolmogorov_extension4 which adds
another transitive dependency. The stochasticpde-itocalculus repo is
self-contained with only a Mathlib dependency.

**Output:** `lakefile.toml` updated, `lake build` succeeds.

### Phase 1: Heat Semigroup on T^2 (2-3 weeks)

Instantiate the C_0-semigroup framework from hille-yosida for the
Laplacian on the torus.

```
Pphi2/StochasticQuantization/
  HeatSemigroup.lean
```

**Key definitions:**
- `torusLaplacian : L^2(T^2) -> L^2(T^2)` — the Laplacian on the torus,
  defined via Fourier eigenvalues $\lambda_k = -4\pi^2|k|^2/L^2$
- `heatSemigroup : R_+ -> L^2(T^2) ->L[R] L^2(T^2)` — $e^{t\Delta}$,
  defined via Fourier multiplier $e^{-4\pi^2|k|^2 t/L^2}$
- Instance: `StronglyContinuousSemigroup heatSemigroup`

**Key theorems:**
- `heatSemigroup_contraction` — $\|e^{t\Delta}\|_{L^2 \to L^2} \leq 1$
- `heatSemigroup_generator` — generator of the semigroup is $\Delta$
- `heatSemigroup_smoothing` — $e^{t\Delta} : H^s \to H^{s+r}$ for $t > 0$
  (regularization, key for the fixed-point argument)

**Existing infrastructure used:** The torus Fourier eigenvalues and
eigenfunctions are already defined in `TorusPropagatorConvergence.lean`.
The hille-yosida semigroup framework provides the abstract theory.

### Phase 2: Cylindrical Wiener Process (2-3 weeks)

Construct the cylindrical Wiener process on $L^2(T^2)$, which is the
rigorous version of space-time white noise.

```
Pphi2/StochasticQuantization/
  CylindricalWiener.lean
```

**Key definitions:**
- `cylindricalWiener : R_+ -> L^2(T^2) -> Omega -> R` — the cylindrical
  Wiener process: for each $f \in L^2(T^2)$, $t \mapsto W_t(f)$ is a
  real-valued Brownian motion with $E[W_t(f) W_s(g)] = \min(t,s) \langle f, g \rangle$
- Alternatively: $W_t = \sum_k \beta_k(t) e_k$ where $\beta_k$ are iid
  standard Brownian motions and $e_k$ are Fourier modes on T^2

**Approach:** The Fourier mode decomposition reduces the cylindrical
Wiener process to a countable family of independent 1D Brownian motions.
Each $\beta_k$ is a standard Brownian motion from the brownian-motion
library. The sum does not converge in $L^2(T^2)$ (cylindrical processes
are not genuine random variables in a Hilbert space), but the stochastic
convolution with the heat semigroup does converge (see Phase 3).

**Key theorems:**
- `cylindricalWiener_isometry` — $E[W_t(f) W_s(g)] = \min(t,s) \langle f, g \rangle$
- `cylindricalWiener_independent_increments` — $W_t - W_s$ independent of $\mathcal{F}_s$

### Phase 3: Stochastic Convolution and the OU Process (3-4 weeks)

Construct the stationary Ornstein-Uhlenbeck process on T^2:

$$Z_t = \int_{-\infty}^t e^{(t-s)(\\Delta - m^2)}\, dW_s$$

```
Pphi2/StochasticQuantization/
  StochasticConvolution.lean
  OrnsteinUhlenbeck.lean
```

**Key definitions:**
- `stochasticConvolution S W t` — $\int_0^t S(t-s)\, dW_s$ for a
  C_0-semigroup $S$ and cylindrical Wiener process $W$
- `ornsteinUhlenbeck mass` — the stationary OU process on T^2 with
  drift $\Delta - m^2$

**Key theorems:**
- `stochasticConvolution_convergence` — the integral converges in
  $L^2(\Omega; H^{-\varepsilon})$ for any $\varepsilon > 0$. This is
  where nuclearity enters: $\sum_k \|e^{t\Delta} e_k\|^2 < \infty$ for
  $t > 0$ because the heat semigroup maps into smoother spaces.
- `ornsteinUhlenbeck_stationary` — $Z_t$ is a stationary Gaussian process
- `ornsteinUhlenbeck_covariance` — $E[Z_t(f) Z_t(g)] = \langle f, (-\Delta + m^2)^{-1} g \rangle / 2$ —
  this is half the Green's function, matching the GFF covariance
- `ornsteinUhlenbeck_regularity` — $Z_t \in C^{-\varepsilon}(T^2)$ a.s.
  for any $\varepsilon > 0$ (via Kolmogorov-Chentsov on the Fourier
  coefficients)

**Main difficulty:** The stochastic integral is in infinite dimensions
(Hilbert-space-valued). The Fourier decomposition reduces it to a
countable sum of 1D stochastic integrals (each handled by
stochasticpde-itocalculus), but the convergence of the sum needs the
trace-class condition $\mathrm{Tr}(e^{2t(\Delta - m^2)}) < \infty$,
which holds on T^2 because the eigenvalues grow as $|k|^2$.

### Phase 4: Wick Renormalization of the Nonlinearity (2 weeks)

Define the Wick-ordered powers $:Z^n:$ and the renormalized
nonlinearity $:P'(Z + v):$.

```
Pphi2/StochasticQuantization/
  WickRenormalization.lean
```

**Key definitions:**
- `wickPower n Z` — $:Z^n:_{c_\infty}$ where
  $c_\infty = E[Z_t(x)^2] = (1/2)\mathrm{Tr}(-\Delta + m^2)^{-1}$
  is the continuum Wick constant
- `renormalizedNonlinearity P Z v` — $:P'(Z + v):$ with all necessary
  Wick subtractions

**Key theorems:**
- `wickConstant_continuum_eq` — $c_\infty$ equals the continuum limit
  of the lattice Wick constants $c_a$
- `wickPower_regularity` — $:Z^n: \in C^{-n\varepsilon}(T^2)$ a.s.
  (products of distributions lose regularity)
- `renormalizedNonlinearity_welldefined` — the renormalized nonlinearity
  makes sense as a distribution for the relevant values of $n$

**Existing infrastructure:** The Wick ordering machinery in
`WickOrdering/WickPolynomial.lean` defines Wick monomials via the same
Hermite polynomial recursion. The key connection: the stochastic
quantization Wick constant $c_\infty$ is the $a \to 0$ limit of the
lattice Wick constant $c_a$.

### Phase 5: Fixed-Point for the Remainder (3-4 weeks)

Solve the remainder equation for $v = \phi - Z$:

$$\partial_\tau v = (\Delta - m^2) v - :P'(Z + v):$$

by a fixed-point argument in an appropriate function space.

```
Pphi2/StochasticQuantization/
  RemainderPDE.lean
  MildSolution.lean
```

**Key definitions:**
- `mildSolution Z v` — $v$ satisfies the Duhamel/mild formulation:
  $v(t) = e^{t(\Delta - m^2)} v_0 - \int_0^t e^{(t-s)(\Delta - m^2)} :P'(Z_s + v_s): ds$
- `solutionMap Z` — the contraction map whose fixed point gives $v$

**Key theorems:**
- `solutionMap_contraction` — the map is a contraction in
  $C([0,T]; C^{2-n\varepsilon})$ for $T$ small enough. The gain comes
  from the smoothing of the heat semigroup ($e^{t\Delta}$ gains regularity)
  compensating the loss from the nonlinearity.
- `mildSolution_exists` — existence and uniqueness of $v$ on $[0,T]$
- `mildSolution_global` — global existence (extend to all $T$) using
  a priori estimates from the energy bound

**Main difficulty:** The Schauder-type estimates for the heat semigroup
on Besov/Holder spaces. This requires:
$\|e^{t\Delta} f\|_{C^\alpha} \lesssim t^{-(\alpha - \beta)/2} \|f\|_{C^\beta}$
for $\alpha > \beta$. This is where Besov space infrastructure is needed.

**Simplification for T^2:** On the torus, the Fourier eigenfunction
expansion makes the Schauder estimates more explicit: each Fourier mode
$\hat{f}_k$ is damped by $e^{-4\pi^2|k|^2 t/L^2}$, so the smoothing
is directly visible in the decay of high-frequency modes.

### Phase 6: Invariant Measure Identification (2-3 weeks)

Show that the stationary measure of the SPDE equals the P(Phi)_2
measure constructed in Route B.

```
Pphi2/StochasticQuantization/
  InvariantMeasure.lean
  MeasureIdentification.lean
```

**Key theorems:**
- `spde_invariant_measure_exists` — the dynamics has a unique invariant
  measure $\mu_{\mathrm{SPDE}}$ on $C^{-\varepsilon}(T^2)$
- `invariant_measure_charFun` — the characteristic functional of
  $\mu_{\mathrm{SPDE}}$ satisfies
  $\int e^{i\Phi(f)} d\mu_{\mathrm{SPDE}} = \exp(-\frac{1}{2}\langle f, (-\Delta + m^2)^{-1} f \rangle + \text{interaction terms})$
- `invariant_measure_eq_pphi2` — **Main identification:**
  $\mu_{\mathrm{SPDE}} = \mu_{\mathrm{P(\Phi)_2}}$
  (the torus interacting measure from Route B)

**Proof strategy:** Both measures are characterized by the same DLR
(Dobrushin-Lanford-Ruelle) equations, or equivalently, both satisfy the
same integration-by-parts formula (the SPDE generator equation in weak
form). Uniqueness of the solution to the DLR equations (in the massive
regime $m > 0$) gives equality.

**Alternative strategy:** Compare characteristic functionals directly.
The SPDE invariant measure has characteristic functional determined by
the stationary covariance of the OU process plus interaction
corrections. The lattice measure's characteristic functional is known
from the torus construction. Show they agree.

### Phase 7: Applications (ongoing)

Once the SPDE construction is in place, several applications become
available:

- **Log-Sobolev inequality for P(Phi)_2:** The SPDE generator satisfies
  a log-Sobolev inequality (Bakry-Emery criterion), which gives
  exponential convergence to equilibrium. The rate of convergence is
  related to the spectral gap — providing an alternative approach to
  `spectral_gap_uniform`.

- **Ergodicity:** The SPDE dynamics is ergodic (unique invariant
  measure), giving OS4 (clustering) via time-averaging along the
  stochastic flow.

- **Stochastic integrability:** Moment bounds for the SPDE solution
  give alternative proofs of the hypercontractive estimates.

## Dependency Graph

```
Mathlib
  |
  +-- hille-yosida (C_0-semigroups)
  |     |
  +-- brownian-motion (BM construction, K-C theorem)
  |     |
  +-- stochasticpde-itocalculus (Ito integral, Ito formula)
  |
  +-- gaussian-field (GFF, tightness, Prokhorov)
  |     |
  +-----+-- pphi2
              |
              +-- Phase 1: HeatSemigroup.lean (uses hille-yosida)
              +-- Phase 2: CylindricalWiener.lean (uses brownian-motion)
              +-- Phase 3: StochasticConvolution.lean, OrnsteinUhlenbeck.lean
              +-- Phase 4: WickRenormalization.lean (uses WickOrdering/)
              +-- Phase 5: RemainderPDE.lean, MildSolution.lean
              +-- Phase 6: InvariantMeasure.lean, MeasureIdentification.lean
```

## Estimated Effort

| Phase | Weeks | New lines (est.) | Dependencies |
|-------|-------|-----------------|--------------|
| 0: Lakefile setup | 1 | 50 | All repos |
| 1: Heat semigroup | 2-3 | 500-800 | hille-yosida |
| 2: Cylindrical Wiener | 2-3 | 400-600 | brownian-motion |
| 3: Stochastic convolution + OU | 3-4 | 800-1200 | Phases 1-2 |
| 4: Wick renormalization | 2 | 300-500 | WickOrdering/ |
| 5: Fixed-point for remainder | 3-4 | 800-1200 | Phase 3-4, Besov |
| 6: Invariant measure identification | 2-3 | 400-700 | Phase 5, Route B |
| **Total** | **15-20** | **3300-5000** | |

## Risk Assessment

**Low risk:**
- Phase 1 (heat semigroup): straightforward instantiation of hille-yosida
- Phase 4 (Wick renormalization): reuses existing WickOrdering infrastructure

**Medium risk:**
- Phase 2 (cylindrical Wiener): conceptually clear but infinite-dimensional
  construction requires care with convergence
- Phase 3 (stochastic convolution): the trace-class condition is
  straightforward on T^2 but needs Fourier analysis infrastructure
- Phase 6 (identification): multiple proof strategies available

**High risk:**
- Phase 5 (fixed-point): needs Besov/Holder regularity estimates that
  don't exist in Mathlib. The Schauder estimates for the heat semigroup
  on the torus may need to be developed from scratch. This is the
  bottleneck of the entire plan.
- Phase 0 (dependency management): four repos plus Mathlib at compatible
  versions could be painful

## Alternative: Axiomatize and Connect

If Phase 5 proves too difficult, an intermediate approach:

1. Complete Phases 1-4 (heat semigroup through Wick renormalization).
2. Axiomatize Phase 5: state `mildSolution_exists` as an axiom.
3. Complete Phase 6 using the axiom.

This gives the full SPDE-to-measure identification with a single
axiom encoding the PDE fixed-point argument. The axiom is mathematically
standard (Da Prato-Debussche 2003) and could be eliminated later as
Besov infrastructure matures in Mathlib.

## References

- Da Prato and Debussche, "Strong solutions to the stochastic
  quantization equations," *Ann. Probab.* **31** (2003), 1900-1916.
- Da Prato and Debussche, "Ergodicity for the 3D stochastic
  Navier-Stokes equations," *J. Math. Pures Appl.* **82** (2003), 877-947.
- Hairer, "A theory of regularity structures," *Invent. Math.* **198**
  (2014), 269-504.
- Mourrat and Weber, "The dynamic Phi^4_3 model comes down from
  infinity," *Comm. Math. Phys.* **356** (2017), 673-753.
- Gubinelli, Imkeller, and Perkowski, "Paracontrolled distributions and
  singular PDEs," *Forum Math. Pi* **3** (2015), e6.
- Nelson, "The free Markoff field," *J. Funct. Anal.* **12** (1973), 211-227.
