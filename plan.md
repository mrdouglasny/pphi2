# Plan: P(Φ)₂ via Lattice Construction

## Goal

Construct the interacting P(Φ)₂ Euclidean quantum field theory in Lean 4
and prove all five Osterwalder-Schrader axioms (OS0–OS4), using a lattice
regularization and continuum limit.

The main theorem:

> For P(τ) an even polynomial of degree ≥ 4 bounded below, there exists a
> probability measure μ on S'(ℝ²) such that:
> - (OS0) The generating functional Z[f] is entire analytic
> - (OS1) |Z[f]| ≤ exp(c(‖f‖₁ + ‖f‖_p^p)) (regularity)
> - (OS2) Z[g·f] = Z[f] for all g ∈ E(2) (Euclidean invariance)
> - (OS3) Reflection positivity
> - (OS4) Exponential clustering (mass gap)

## Approach: Lattice → Continuum

We replace the DDJ stochastic quantization approach (previous plan) with the
classical Glimm-Jaffe/Nelson lattice construction. This gives all 5 OS axioms
including clustering, and tests the modular architecture needed for O(3) NLSM.

**Construction outline:**

1. Define the lattice P(Φ)₂ measure:
   `dμ_a = (1/Z_a) exp(-V_a(φ)) dμ_{GFF,a}(φ)`
   where `μ_{GFF,a}` is the lattice Gaussian from gaussian-field and
   `V_a(φ) = a² Σ_x :P(φ(x)):_a` is the Wick-ordered interaction.

2. Prove OS axioms on the lattice (finite-dimensional, all proofs are clean).

3. Embed lattice fields into S'(ℝ²), show tightness, extract continuum limit.

4. Show OS axioms transfer to the limit.

**Key advantage:** Super-renormalizability means only one counterterm (mass).
No coupling constant or wave function renormalization.

---

## Dependencies

- **gaussian-field** (`Lattice/` module): `latticeGaussianMeasure`,
  `latticeCovariance`, `latticeEigenvalue`, `fkg_perturbed`, `FinLatticeField`,
  `FinLatticeSites`, `finiteLaplacian`, `massOperator`
- **gaussian-field** (core): `GaussianField.measure`, `spectralCLM`,
  `cross_moment_eq_covariance`, `wick_recursive`, `Configuration`
- **OSforGFF**: `QFTFramework`, `OS_Axioms_Generic` (OS0–OS4 definitions)
- **Mathlib**: measure theory, Schwartz space, spectral theory, weak convergence

---

## File Structure

### Keep from current pphi2

| File | Role | Changes |
|------|------|---------|
| `Basic.lean` | SpaceTimeCyl, TestFunctionCyl, QFTFramework instance | Minimal — keep as the continuum target space |
| `Polynomial.lean` | InteractionPolynomial structure | Add Wick ordering interface |
| `OSAxioms.lean` | OS axiom bundle | Extend to all 5 axioms |
| `Main.lean` | Main theorem | Rewrite for lattice route |
| `FunctionSpaces/` | Weighted Lp, Sobolev embeddings | Keep for continuum limit |

### Remove (DDJ stochastic quantization path)

These are replaced by the lattice construction:
- `StochasticQuant/DaPratoDebussche.lean`
- `StochasticEst/InfiniteVolumeBound.lean`
- `Energy/EnergyEstimate.lean`
- `MeasureCylinder/Regularized.lean`, `UVLimit.lean`
- `GaussianCylinder/Covariance.lean`

### New files

```
Pphi2/
  Basic.lean                          -- KEEP: continuum types
  Polynomial.lean                     -- KEEP+EXTEND: add Wick ordering
  OSAxioms.lean                       -- EXTEND: OS0–OS4 bundle
  Main.lean                           -- REWRITE: lattice route

  WickOrdering/
    WickPolynomial.lean               -- :P(φ):_a definition via Hermite polynomials
    Counterterm.lean                  -- c_a = G_a(0,0), asymptotics c_a ~ (1/2π) log(1/a)

  InteractingMeasure/
    LatticeAction.lean                -- V_a(φ) = a² Σ_x :P(φ(x)):_a
    LatticeMeasure.lean               -- dμ_a = (1/Z_a) exp(-V_a) dμ_{GFF,a}
    Normalization.lean                -- Z_a > 0, integrability of exp(-V_a)

  TransferMatrix/
    TransferMatrix.lean               -- T_a = e^{-aH} integral kernel
    Positivity.lean                   -- T_a self-adjoint and positive
    SpectralGap.lean                  -- H has compact resolvent, gap > 0

  OSProofs/
    OS0_Analyticity.lean              -- Z_a[J] entire, uniform bounds
    OS1_Regularity.lean               -- |Z[f]| ≤ exp(c‖f‖²), uniform in a
    OS2_WardIdentity.lean             -- Ward identity + irrelevance O(a²)
    OS3_RP_Lattice.lean               -- RP via transfer matrix decomposition
    OS3_RP_Inheritance.lean           -- RP closed under weak limits
    OS4_MassGap.lean                  -- Spectral gap → exponential clustering
    OS4_Ergodicity.lean               -- Clustering → ergodicity

  ContinuumLimit/
    Embedding.lean                    -- ι_a : lattice fields → S'(ℝ²)
    Tightness.lean                    -- Uniform bounds → tightness
    Convergence.lean                  -- μ_a ⇀ μ weakly (Prokhorov)
    AxiomInheritance.lean             -- OS axioms pass to the limit

  FunctionSpaces/                     -- KEEP
    WeightedLp.lean
    Embedding.lean

  ReflectionPositivity/               -- KEEP (may merge into OSProofs/)
    RPPlane.lean

  EuclideanInvariance/                -- KEEP (may merge into OSProofs/)
    Invariance.lean

  InfiniteVolume/                     -- KEEP (adapt for lattice tightness)
    Tightness.lean

  Integrability/                      -- KEEP
    Regularity.lean
```

---

## Detailed File Contents

### WickOrdering/WickPolynomial.lean

Wick ordering `:P(φ):_a` with respect to the lattice Gaussian measure.

Definitions:
- `wickConstant d N a mass : ℝ` — the self-contraction `c_a = G_a(0,0)`,
  computed as `(1/N^d) Σ_k 1/λ_k` where `λ_k = latticeEigenvalue d N a mass k`.
  This equals the diagonal of the lattice Green's function.
- `wickMonomial (n : ℕ) (c : ℝ) (x : ℝ) : ℝ` — the Wick-ordered monomial
  `:x^n:_c`, defined via Hermite polynomials: `:x^n:_c = c^{n/2} He_n(x/√c)`.
- `wickPolynomial (P : InteractionPolynomial) (c : ℝ) (x : ℝ) : ℝ` — apply Wick
  ordering to each monomial of P.

Key properties:
- `wickMonomial_expectation_zero`: `E_μ[:φ^n:] = 0` for n ≥ 1 (the point of Wick ordering)
- `wickMonomial_recursion`: `:x^{n+1}: = x · :x^n: - n·c · :x^{n-1}:`

### WickOrdering/Counterterm.lean

Asymptotics of the Wick ordering constant.

Definitions:
- `wickConstant_formula`: express `c_a` in terms of `latticeEigenvalue`

Key results:
- `wickConstant_pos`: `c_a > 0`
- `wickConstant_bound`: `c_a ≤ C · |log a| + C'` for uniform constants C, C'
  (the logarithmic divergence — this is the ONLY UV divergence in P(Φ)₂)
- `wickConstant_asymptotics`: `c_a ~ (1/2π) log(1/a) + O(1)` as `a → 0`
  (axiomatize the asymptotic; the upper bound may be provable)

### InteractingMeasure/LatticeAction.lean

The lattice interaction.

Definitions:
- `latticeInteraction (P : InteractionPolynomial) (d N : ℕ) (a mass : ℝ) :
    FinLatticeField d N → ℝ`
  defined as `V_a(φ) = a^d · Σ_{x : FinLatticeSites d N} wickPolynomial P c_a (φ x)`

Key properties:
- `latticeInteraction_bounded_below`: `V_a(φ) ≥ -C · |Λ_a|` because P has
  even degree ≥ 4 with positive leading coefficient
- `latticeInteraction_convex`: `V_a` is convex on `FinLatticeField d N`
  when P is convex (enables `fkg_perturbed` from gaussian-field)
- `latticeInteraction_continuous`: continuous (finite-dimensional, automatic)

### InteractingMeasure/LatticeMeasure.lean

The interacting lattice measure.

Definitions:
- `interactingLatticeMeasure (P : InteractionPolynomial) (d N : ℕ) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    Measure (Configuration (FinLatticeField d N))`
  defined as `(1/Z_a) · (fun φ => exp(-V_a(φ))) • latticeGaussianMeasure d N a mass ha hmass`
  i.e., the Gaussian measure reweighted by `exp(-V_a)/Z_a`.
- `partitionFunction`: `Z_a = ∫ exp(-V_a(φ)) dμ_{GFF,a}(φ)`

### InteractingMeasure/Normalization.lean

Well-definedness of the interacting measure.

Key results:
- `expNegV_integrable`: `exp(-V_a) ∈ L¹(μ_{GFF,a})` — follows from
  `latticeInteraction_bounded_below` (exp(-V) ≤ exp(C·|Λ|))
- `partitionFunction_pos`: `Z_a > 0` — since `exp(-V) > 0` a.e.
- `interactingLatticeMeasure_isProbability`: μ_a is a probability measure

### TransferMatrix/TransferMatrix.lean

Transfer matrix for the lattice theory.

The key idea: decompose the lattice action across time slices. On a lattice
`{0,...,N_t-1} × {0,...,N_s-1}^{d-1}`, the action splits as:

```
S_a[φ] = Σ_{t=0}^{N_t-1} [ ½a^{d-2} Σ_x |φ(t+1,x) - φ(t,x)|²
                            + a^{d-1} · h_a(φ(t,·)) ]
```

where `h_a(ψ) = ½ Σ_{<xy>} a^{d-2}|ψ(x)-ψ(y)|² + a^{d-1} Σ_x (m²|ψ(x)|² + :P(ψ(x)):)`
is the spatial action for a single time-slice field `ψ : {0,...,N_s-1}^{d-1} → ℝ`.

Definitions:
- `spatialField d N := FinLatticeSites (d-1) N → ℝ` — field on one time slice
- `transferMatrix (d N : ℕ) (a mass : ℝ) (P : InteractionPolynomial) :
    spatialField d N → spatialField d N → ℝ`
  the integral kernel `T(ψ, ψ') = exp(-½a^{d-2} Σ_x |ψ(x)-ψ'(x)|² - a·h_a(ψ))`
  (for d=2: `T(ψ,ψ') = exp(-½ Σ_x (ψ_x - ψ'_x)² - a·h_a(ψ))`)

### TransferMatrix/Positivity.lean

Self-adjointness and positivity of the transfer matrix.

Key results:
- `transferMatrix_symmetric`: `T(ψ, ψ') = T(ψ', ψ)` (the kernel is symmetric
  after absorbing half of h_a into each side)
- `transferMatrix_positive`: `T(ψ, ψ') > 0` for all ψ, ψ' (the kernel is
  strictly positive because it's a Gaussian times exp(-V) > 0)
- As an operator on L²(ℝ^{N_s^{d-1}}): T is self-adjoint, positive, trace class

### TransferMatrix/SpectralGap.lean

Spectral gap of the transfer matrix Hamiltonian.

The transfer matrix is `T = e^{-aH}` where the Hamiltonian is:
```
H = -½ Σ_x ∂²/∂ψ(x)² + spatial kinetic + Σ_x (½m²ψ(x)² + :P(ψ(x)):)
```

For d=2, spatial dimension = 1, so H acts on L²(ℝ^{N_s}).

Key results (axiomatize):
- `hamiltonian_selfadjoint`: H is self-adjoint on L²
- `hamiltonian_compact_resolvent`: (H + λ)⁻¹ is compact for λ large
  (because V(ψ) → ∞ as |ψ| → ∞, so the potential is confining)
- `hamiltonian_discrete_spectrum`: H has discrete spectrum E₀ < E₁ ≤ E₂ ≤ ...
- `spectral_gap_pos`: `E₁ - E₀ > 0` (strict gap)
  Proof: The ground state of a confining 1D Schrödinger operator is
  non-degenerate (Perron-Frobenius for the heat semigroup).
- `spectral_gap_lower_bound (m₀ λ : ℝ) : E₁ - E₀ ≥ f(m₀, λ)`
  (explicit lower bound; stretch goal)

### OSProofs/OS3_RP_Lattice.lean

Reflection positivity on the lattice — the cleanest OS proof.

**Proof sketch** (one page):
1. Split the lattice at the time-reflection hyperplane t = 0.
2. Fields decompose: φ = (φ⁺, φ⁰, φ⁻) where φ⁺ is at t > 0, φ⁰ at t = 0, φ⁻ at t < 0.
3. The action decomposes: S[φ] = S⁺[φ⁺, φ⁰] + S⁻[φ⁻, φ⁰] where S⁻[φ⁻, φ⁰] = S⁺[Θφ⁻, φ⁰].
4. For F supported at positive time:
   `∫ F(φ) · F(Θφ) dμ_a = (1/Z) ∫∫∫ F(φ⁺) · F(Θφ⁻) · e^{-S⁺-S⁻} dφ⁺ dφ⁰ dφ⁻`
   `= (1/Z) ∫ dφ⁰ [∫ F(φ⁺) e^{-S⁺[φ⁺,φ⁰]} dφ⁺]² ≥ 0`
5. The square appears because Θ maps φ⁻ to the same integral as φ⁺.

Definitions:
- `positiveTimeField`, `negativeTimeField`, `boundaryField`: projections
- `actionDecomposition`: `S[φ] = S⁺[φ⁺, φ⁰] + S⁻[φ⁻, φ⁰]`
- `actionReflectionSymmetry`: `S⁻[φ⁻, φ⁰] = S⁺[Θφ⁻, φ⁰]`

Main result:
- `lattice_rp`: For test functions f₁,...,fₙ supported at t > 0 and
  coefficients c₁,...,cₙ: `Σᵢⱼ cᵢcⱼ ∫ exp(i⟨φ, fᵢ - Θfⱼ⟩) dμ_a ≥ 0`

### OSProofs/OS3_RP_Inheritance.lean

RP transfers to the continuum limit.

**Proof:** RP is a condition of the form `Σᵢⱼ cᵢcⱼ F(fᵢ, fⱼ) ≥ 0` where
`F(f,g) = ∫ exp(i⟨φ, f-Θg⟩) dμ`. Since `φ ↦ exp(i⟨φ,f⟩)` is bounded and
continuous on S', and `μ_a ⇀ μ` weakly, each `F_a(f,g) → F(f,g)`.
A nonneg sum of convergent terms stays nonneg.

Main result:
- `rp_closed_under_weak_limit`: If `{μ_n}` are RP measures converging weakly
  to μ, then μ is RP. (This should be provable, not just axiomatized.)

### OSProofs/OS4_MassGap.lean

Exponential clustering from spectral gap.

**Proof (on lattice):**
The two-point function satisfies:
```
⟨φ(t,x) φ(0,y)⟩ - ⟨φ⟩² = Σ_{n≥1} |⟨Ω, φ(x) ψ_n⟩|² · e^{-(E_n - E₀)|t|}
                            ≤ C · e^{-(E₁ - E₀)|t|}
```
where Ω is the ground state and ψ_n are eigenstates of H.
The exponential decay rate is the spectral gap `m_phys = E₁ - E₀ > 0`.

For general n-point functions, the same argument gives:
```
|⟨F(φ)·G(T_R φ)⟩ - ⟨F⟩⟨G⟩| ≤ C(F,G) · exp(-m_phys · R)
```

Key results:
- `exponential_clustering_lattice`: exponential decay on the lattice
- `mass_gap_uniform`: the spectral gap is bounded below uniformly in a
  (because the potential grows as φ^{2p}, confining regardless of a)

### OSProofs/OS0_Analyticity.lean

The generating functional Z_a[J] = ∫ exp(i⟨φ,J⟩) dμ_a is entire.

**Proof (on lattice):** The integrand exp(i Σ J_x φ_x) is entire in J for
each φ. Differentiation under the integral is justified by dominated
convergence: |∂^α exp(i⟨φ,J⟩)| ≤ |φ|^|α| · exp(|Im J| · |φ|), and the
Gaussian tail of μ_a (plus boundedness below of V_a) gives integrability
of |φ|^k · exp(ε|φ|) for all k and small ε.

### OSProofs/OS1_Regularity.lean

Regularity bound: |Z[f]| ≤ exp(c · ‖f‖²).

**Proof (on lattice):** `|Z_a[f]| ≤ ∫ |exp(i⟨φ,f⟩)| dμ_a = 1` trivially
for real f. The nontrivial bound is on derivatives / moments:
`∫ |⟨φ,f⟩|^{2n} dμ_a ≤ (2n)! · C^n · ‖f‖²ⁿ_{H^{-1}}`
with C uniform in a. This follows from Wick's theorem for the Gaussian part
plus the interaction only improving decay.

### OSProofs/OS2_WardIdentity.lean

Euclidean invariance restoration — the hardest axiom.

The lattice breaks E(2) to discrete symmetries. Full invariance is restored
in the continuum limit by a Ward identity argument.

**Strategy:**
1. Lattice translations by a are exact symmetries → translation invariance
   in the limit (translations by multiples of a approximate all translations).
2. Rotation invariance via Ward identity:
   - Define the SO(2) generator J on lattice observables.
   - The Ward identity on the lattice has an anomaly term O_break from the
     nearest-neighbor action breaking rotation symmetry.
   - O_break has scaling dimension 4.
   - Since dim(O_break) = 4 > d = 2, it is RG-irrelevant.
   - Its coefficient vanishes as O(a²) in the continuum limit.
   - **Key simplification vs O(3):** P(Φ)₂ is super-renormalizable, so there
     are NO logarithmic corrections competing with the a² decay. The irrelevance
     argument is purely polynomial.

Key results (axiomatize with detailed proof sketches):
- `translation_invariance`: lattice translations → continuum translations
- `ward_identity_lattice`: Ward identity with anomaly term
- `anomaly_dimension`: dim(O_break) = 4
- `anomaly_vanishes`: coefficient of O_break is O(a²)
- `rotation_invariance_continuum`: full SO(2) invariance in the limit

### ContinuumLimit/Embedding.lean

Embedding lattice fields into the continuum distribution space.

Definitions:
- `latticeEmbed (d N : ℕ) (a : ℝ) (ha : 0 < a) :
    FinLatticeField d N → Configuration (TestFunction d)`
  defined by `(ι_a φ)(f) = a^d · Σ_{x : FinLatticeSites d N} φ(x) · f(a · x)`
  where `f(a·x)` evaluates the Schwartz function f at the physical position of
  lattice site x. This is a continuous linear functional on S(ℝ^d), hence an
  element of S'(ℝ^d) = Configuration(TestFunction d).

- `continuumMeasure_a`: pushforward `(ι_a)_* μ_a` on Configuration(TestFunction d)

Properties:
- `latticeEmbed_continuous`: ι_a is continuous (finite sum)
- `latticeEmbed_linear`: ι_a is linear
- `continuumMeasure_isProbability`: pushforward of probability is probability

### ContinuumLimit/Tightness.lean

Tightness of the family `{(ι_a)_* μ_a}_{a>0}` in S'(ℝ²).

**Tightness criterion** (Mitoma): A family of measures on S'(ℝ^d) is tight iff
for each f ∈ S(ℝ^d), the family of pushforward measures under `φ ↦ φ(f)` is
tight on ℝ.

Key results:
- `second_moment_uniform`: `∫ |Φ_a(f)|² dμ_a ≤ C(f)` uniformly in a
  (from lattice covariance convergence: `⟨f, G_a f⟩ → ⟨f, G f⟩`)
- `moment_equicontinuity`: `∫ |Φ_a(f) - Φ_a(g)|² dμ_a ≤ C · ‖f-g‖²_s`
  (from Sobolev regularity of the propagator)
- `continuumMeasures_tight`: the family is tight in S'(ℝ²)

### ContinuumLimit/Convergence.lean

Existence of the continuum limit.

Key results:
- `prokhorov`: Tightness in S'(ℝ²) (Polish space) implies every sequence
  has a weakly convergent subsequence. (Axiomatize; Prokhorov's theorem is
  partially in Mathlib.)
- `continuumLimit`: `∃ μ : ProbabilityMeasure (Configuration (TestFunction 2)),`
  subsequence `μ_{a_k} ⇀ μ` weakly
- `schwinger_convergence`: n-point Schwinger functions converge:
  `S_a^{(n)}(f₁,...,fₙ) → S^{(n)}(f₁,...,fₙ)` for all test functions

### ContinuumLimit/AxiomInheritance.lean

OS axioms pass from lattice to continuum.

Key results:
- `os0_inheritance`: Analyticity from uniform exponential bounds
- `os1_inheritance`: Regularity from uniform ‖f‖² bounds
- `os3_inheritance`: RP from weak closure of RP cone (provable)
- `os4_inheritance`: Clustering from uniform mass gap lower bound
- `os2_inheritance`: Euclidean invariance from Ward identity (the hard one)

### OSAxioms.lean (extended)

```lean
/-- Full OS axiom bundle for P(Φ)₂. -/
structure SatisfiesFullOS (F : QFTFramework)
    (dμ : ProbabilityMeasure F.FieldConfig) : Prop where
  os0 : OS0_Analyticity_generic F dμ
  os1 : OS1_Regularity_generic F dμ
  os2 : OS2_Invariance_generic F dμ
  os3 : OS3_ReflectionPositivity_generic F dμ
  os4 : OS4_Clustering_generic F dμ
```

### Main.lean (rewritten)

```lean
/-- **Main Theorem**: The P(Φ)₂ measure exists and satisfies all OS axioms.
    Constructed as the continuum limit of lattice measures. -/
theorem pphi2_full_OS (P : InteractionPolynomial) :
    ∃ (F : QFTFramework) (dμ : ProbabilityMeasure F.FieldConfig),
      SatisfiesFullOS F dμ
```

---

## What to Axiomatize vs Prove

### Prove (feasible in Lean now)

| Result | Why provable |
|--------|-------------|
| `wickConstant_pos` | Finite sum of positive terms |
| `latticeInteraction_bounded_below` | Polynomial with positive leading coeff |
| `expNegV_integrable` | Bounded below → exp is bounded above |
| `partitionFunction_pos` | exp > 0 a.e. |
| `interactingLatticeMeasure_isProbability` | Normalization |
| `lattice_rp` (OS3 on lattice) | Transfer matrix decomposition (finite-dim linear algebra) |
| `rp_closed_under_weak_limit` | Bounded continuous functions + weak convergence |
| `latticeEmbed_continuous` | Finite sum |
| `wickMonomial_recursion` | Hermite polynomial identity |

### Axiomatize (with proof outlines, prove later)

| Result | Difficulty | Proof strategy |
|--------|-----------|----------------|
| `wickConstant_asymptotics` | Medium | Euler-Maclaurin summation |
| `transferMatrix_positive` | Medium | Gaussian kernel positivity |
| `hamiltonian_compact_resolvent` | Medium | Confining potential → compact embedding |
| `spectral_gap_pos` | Medium | Perron-Frobenius / non-degeneracy of ground state |
| `mass_gap_uniform` | Hard | Uniform lower bound on confining potential |
| `second_moment_uniform` | Hard | Nelson's estimate (hypercontractivity) |
| `continuumMeasures_tight` | Hard | Uses Nelson's estimate + Mitoma criterion |
| `prokhorov` | Medium | Standard but not fully in Mathlib |
| `schwinger_convergence` | Hard | Lattice propagator → continuum propagator |
| `translation_invariance` | Medium | Lattice translations approximate continuum |
| `ward_identity_lattice` | Hard | Lattice Ward identity computation |
| `anomaly_vanishes` | Hard | Power counting / RG irrelevance |
| `os4_inheritance` | Medium | Uniform spectral gap → exponential decay in limit |

### Nelson's estimate (the key hard axiom)

Nelson's hypercontractive estimate is the engine behind tightness and uniform
bounds. It says that for the Gaussian measure:

```
‖:φ^n:‖_{L^p(μ_GFF)} ≤ (p-1)^{n/2} · ‖:φ^n:‖_{L^2(μ_GFF)}
```

The proof goes through the Gross log-Sobolev inequality. This is deep and would
be a significant formalization project in its own right. We axiomatize it as:

```lean
axiom nelson_hypercontractive (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (n : ℕ) (p : ℝ) (hp : 2 ≤ p) :
    ∫ |wickMonomial n c_a (φ x)|^p dμ_{GFF,a} ≤
    (p - 1)^(n*p/2) * (∫ |wickMonomial n c_a (φ x)|^2 dμ_{GFF,a})^(p/2)
```

Breaking this into sub-axioms: log-Sobolev → hypercontractivity → moment bounds
→ tightness gives a clear path for incremental proof.

---

## Development Phases

### Phase 1: Wick Ordering + Interacting Measure (2 weeks)

Build the lattice interacting measure on top of gaussian-field.

1. `WickOrdering/WickPolynomial.lean` — Hermite-based Wick ordering
2. `WickOrdering/Counterterm.lean` — `c_a = G_a(0,0)` from `latticeEigenvalue`
3. `InteractingMeasure/LatticeAction.lean` — `V_a(φ)`
4. `InteractingMeasure/LatticeMeasure.lean` — `dμ_a`
5. `InteractingMeasure/Normalization.lean` — `Z_a > 0`

**Verification:** `lake build` succeeds; `interactingLatticeMeasure` has the right type.

### Phase 2: Transfer Matrix + OS3 (2–3 weeks)

The cleanest OS proof — test the pipeline.

1. `TransferMatrix/TransferMatrix.lean` — define T
2. `TransferMatrix/Positivity.lean` — T symmetric and positive
3. `OSProofs/OS3_RP_Lattice.lean` — RP via action decomposition
4. `OSProofs/OS3_RP_Inheritance.lean` — RP closed under weak limits

**Verification:** `lattice_rp` and `rp_closed_under_weak_limit` compile.

### Phase 3: Spectral Gap + OS4 (2–3 weeks)

1. `TransferMatrix/SpectralGap.lean` — axiomatize spectral gap
2. `OSProofs/OS4_MassGap.lean` — exponential clustering
3. `OSProofs/OS4_Ergodicity.lean` — ergodicity from clustering

**Verification:** `exponential_clustering_lattice` compiles with correct type.

### Phase 4: Continuum Limit (3–4 weeks)

The main technical phase.

1. `ContinuumLimit/Embedding.lean` — ι_a : lattice → S'
2. `ContinuumLimit/Tightness.lean` — uniform bounds (axiomatize Nelson)
3. `ContinuumLimit/Convergence.lean` — Prokhorov, weak limit
4. `ContinuumLimit/AxiomInheritance.lean` — OS0, OS1, OS3, OS4 transfer

**Verification:** `continuumLimit` and `os3_inheritance` compile.

### Phase 5: Euclidean Invariance (3–4 weeks)

The hardest axiom.

1. `OSProofs/OS2_WardIdentity.lean` — Ward identity + irrelevance
2. Translation invariance (easier half)
3. Rotation invariance (Ward identity argument)

**Verification:** `os2_inheritance` compiles.

### Phase 6: Assembly (1 week)

1. Extend `OSAxioms.lean` to `SatisfiesFullOS`
2. Rewrite `Main.lean` to assemble all 5 axioms
3. Full `lake build` succeeds

---

## Import Dependencies

```
gaussian-field/Lattice ←── WickOrdering (uses latticeEigenvalue, latticeGaussianMeasure)
WickOrdering ←── InteractingMeasure (uses wickPolynomial, wickConstant)
InteractingMeasure ←── TransferMatrix (uses latticeInteraction)
InteractingMeasure ←── OSProofs/OS3_RP_Lattice (uses interactingLatticeMeasure)
TransferMatrix ←── OSProofs/OS4_MassGap (uses spectral_gap_pos)
InteractingMeasure ←── ContinuumLimit/Embedding (uses interactingLatticeMeasure)
ContinuumLimit ←── ContinuumLimit/AxiomInheritance
OSProofs/* + ContinuumLimit/AxiomInheritance ←── Main.lean
```

---

## References

### P(Φ)₂ Construction
- **Glimm-Jaffe** (1973): Original construction
- **Simon** (1974): *The P(φ)₂ Euclidean (Quantum) Field Theory* (Princeton)
- **Guerra-Rosen-Simon** (1975): Correlation inequalities, Nelson's symmetry
- **Nelson** (1973): *The free Markoff field*, hypercontractivity

### OS Axioms
- **Osterwalder-Schrader** (1973, 1975): Axiom formulation and reconstruction
- **Osterwalder-Seiler** (1978): Lattice reflection positivity
- **Glimm-Jaffe** (1987): *Quantum Physics*, Ch. 6, 19

### Cluster Expansion / Mass Gap
- **Glimm-Jaffe-Spencer** (1975): Cluster expansion for P(φ)₂
- **Simon-Hoegh-Krohn** (1972): Spectral gap → exponential clustering

### Euclidean Invariance Restoration
- **Symanzik** (1983): Continuum limit of lattice field theories
- **Luscher-Weisz** (1985): Symanzik improvement program
