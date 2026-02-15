# Plan: Full OS Axioms for P(Φ)₂ on the Lattice

**Goal:** Prove all five Osterwalder-Schrader axioms (OS0-OS4) for the P(Φ)₂ Euclidean QFT
in Lean 4, starting from a lattice formulation and taking the continuum limit.
This serves as a **proof of principle** for the modular architecture before
tackling the harder O(3) NLSM.

**Key advantage of P(Φ)₂:** Super-renormalizable (only mass renormalization needed),
scalar target space ℝ, complete rigorous constructions exist in the literature
(Glimm-Jaffe, Simon, Nelson, Guerra-Rosen-Simon, Duch-Dybalski-Jahandideh).

---

## 1. Strategy: Two-Layer Construction

### Layer 1: Free Field (GFF at d=2)

Generalize the existing OSforGFF proofs from d=4 to d=2.
The OS axiom **definitions** in `OSforGFF/OS_Axioms.lean` are already parametric in `d`.
The **proofs** (OS0_GFF.lean through OS4_Ergodicity.lean) are currently d=4 only
and need d=2 versions.

The d=2 GFF is simpler than d=4:
- Covariance kernel: C(x) ~ -1/(2π) log|x| + ... (logarithmic, not power-law)
- Momentum propagator: 1/(k₀² + k₁² + m²) (2 components, not 4)
- Spatial dimension = 1 (circle S¹_L or line ℝ)
- Bessel function: K₀(m|x|) instead of |x|^{-1} K₁(m|x|)
- Heat kernel: (4πt)^{-1} exp(-|x|²/4t) instead of (4πt)^{-2}

### Layer 2: Interacting Theory (P(Φ)₂)

Build the interacting measure as a perturbation of the GFF:
- dμ_{P(Φ)₂} = (1/Z) exp(-∫ :P(φ(x)): dx) dμ_GFF
- P(τ) = λτ^{2p} + lower order (even degree ≥ 4, bounded below)
- :P: denotes Wick ordering (subtracts mass counterterm)

Prove that the perturbation preserves/modifies OS axioms appropriately.

---

## 2. What Transfers from OSforGFF

### Directly Reusable (Already Parametric in d)

| Module | Content | Status |
|--------|---------|--------|
| `Basic.lean` | `SpaceTime d`, `TestFunction d`, `FieldConfiguration d`, generating functionals | ✓ Works for d=2 |
| `OS_Axioms.lean` | All axiom definitions (OS0-OS4) | ✓ Parametric |
| `Euclidean.lean` | E(d) group actions, measure preservation | ✓ Parametric |
| `TimeTranslation.lean` | Time shift on Schwartz space and distributions | ✓ Parametric |
| `DiscreteSymmetry.lean` | Time reflection, parity | ✓ Parametric |
| `FunctionalAnalysis.lean` | Mollifiers, convolution, distribution theory | ✓ Mostly parametric |
| `ComplexTestFunction.lean` | Complex Schwartz operations | ✓ Parametric |

### Needs d=2 Adaptation

| Module | What Changes | Difficulty |
|--------|-------------|-----------|
| `Covariance*.lean` | Propagator form changes (K₀ Bessel, log singularity) | Medium |
| `BesselFunction.lean` | Need K₀(z) instead of K₁(z)/z | Medium |
| `LaplaceIntegral.lean` | Heat kernel normalization: (4πt)^{-1} not (4πt)^{-2} | Easy |
| `SpacetimeDecomp.lean` | ℝ² = ℝ × ℝ instead of ℝ⁴ = ℝ × ℝ³ | Easy |
| `OS3_MixedRep*.lean` | Momentum integrals in 2D, simpler spatial Fourier | Medium |
| `Parseval.lean` | Plancherel in d=2 (simpler) | Easy |

### New for P(Φ)₂ (Not in OSforGFF)

| Component | Description | Difficulty |
|-----------|-------------|-----------|
| Wick ordering | Hermite polynomial renormalization | Medium |
| Lattice measure | Finite-dimensional lattice path integral | Easy |
| Lattice RP | Transfer matrix positivity on lattice | Easy |
| Cluster expansion | Polymer expansion for small coupling | Hard |
| Continuum limit | Lattice → continuum convergence | Hard |
| Mass gap proof | Exponential decay of correlations | Medium |

---

## 3. Lattice P(Φ)₂ Theory

### 3.1 Lattice Definitions

**Lattice spacetime:** Λ_a = aℤ² ∩ [-L,L]² with spacing a > 0.

**Lattice fields:** φ : Λ_a → ℝ (one real scalar per site).

**Lattice action:**
```
S_a[φ] = a² Σ_{<xy>} (1/a²)(φ_x - φ_y)² + a² Σ_x [m₀² φ_x² + λ P(φ_x)]
       = Σ_{<xy>} (φ_x - φ_y)² + a² Σ_x [m₀² φ_x² + λ :P(φ_x):]
```
where `<xy>` are nearest-neighbor pairs and `:P:` is Wick-ordered.

**Lattice measure:**
```
dμ_a[φ] = (1/Z_a) exp(-S_a[φ]) Π_x dφ_x
```
This is a well-defined finite-dimensional integral (Lebesgue measure on ℝ^|Λ_a|)
because P is bounded below and even degree ≥ 4.

**Mass counterterm:** The Wick ordering constant is:
```
c_a = (1/|Λ_a|) Σ_x G_a(x,x) ~ (1/2π) log(1/a) + O(1)
```
where G_a is the lattice Green's function. This is the ONLY renormalization needed
(super-renormalizability).

### 3.2 Why the Lattice Approach

For a proof-of-principle of the O(3) pipeline, we want to test:
1. Lattice RP proof → continuum inheritance (Module A pattern)
2. Mass gap via spectral analysis (Module B/C pattern)
3. Euclidean invariance via symmetry restoration (Module D/E pattern)
4. Full OS axiom assembly

P(Φ)₂ is ideal because:
- **Super-renormalizable:** Only one counterterm (mass), no coupling constant renormalization
- **No curved target:** ℝ instead of S², eliminates geometric complications
- **Explicit transfer matrix:** T = e^{-aH} with H = -Δ + V(φ), positive by construction
- **Well-understood:** Every step has rigorous precedent in the literature

---

## 4. OS Axioms: Proof Strategy

### OS0 (Analyticity)

**Statement:** The generating functional Z[J] = ∫ exp(i⟨φ,J⟩) dμ(φ) is entire analytic
in the test function J.

**Lattice proof:** On the lattice, Z_a[J] = ∫_{ℝ^n} exp(i Σ J_x φ_x) dμ_a is
analytic because the integrand is entire and the measure has Gaussian tail bounds
(from the quartic term in the action). Differentiation under the integral sign is
justified by dominated convergence.

**Continuum:** Analyticity is preserved under weak limits of measures with
uniform exponential bounds.

**Reuse from OSforGFF:** The proof strategy in `OS0_GFF.lean` (holomorphic integral
theorem) generalizes directly. The axiom `differentiable_analyticAt_finDim` applies.

**Difficulty:** Easy.

---

### OS1 (Regularity)

**Statement:** ∃ p ∈ [1,2], c > 0 such that
|Z[f]| ≤ exp(c(‖f‖_{L¹} + ‖f‖_{Lp}^p)) for all test functions f.

**Lattice proof:** On the lattice, the generating functional satisfies
|Z_a[f]| ≤ exp(c ‖f‖²_{L²}) because the GFF covariance provides L² bounds,
and the interaction P(φ) only improves decay. Use p = 2.

**Continuum:** The bound transfers to the continuum limit because the constants
are uniform in a.

**Reuse from OSforGFF:** The proof in `OS1_GFF.lean` uses Fourier/momentum methods
with p = 2. Adapting to d=2 requires the d=2 propagator bound:
∫ |Ĉ(k)|² dk < ∞ (which holds because 1/(k² + m²) ∈ L²(ℝ²) for m > 0).

**Difficulty:** Easy-Medium.

---

### OS2 (Euclidean Invariance)

**Statement:** Z[f] = Z[g·f] for all g ∈ E(2) (Euclidean group of ℝ²).

**The challenge:** The lattice breaks continuous E(2) down to the discrete
symmetry group of ℤ² (translations by a, 90° rotations, reflections).

**Strategy (Two-Path / Ward Identity approach from Deep Think Q5):**

**Option A (Direct, for translations):**
- Lattice translations by multiples of a are exact symmetries
- In the continuum limit a → 0, these approximate all translations
- Translation invariance is inherited

**Option B (Ward identities, for rotations):**
1. Define the rotation generator J_{SO(2)} on lattice observables
2. Compute the Ward identity with lattice anomaly:
   δ_{SO(2)} ⟨φ(x₁)···φ(xₙ)⟩_a = ⟨φ(x₁)···φ(xₙ) · O_break⟩_a
3. The rotation-breaking operator O_break has dimension 4 in 2D
4. Since dim(O_break) = 4 > d = 2, it is RG-irrelevant
5. Its coefficient vanishes as O(a²) in the continuum limit
6. Therefore: full E(2) invariance is restored

**Option C (DDJ sphere approach, already in pphi2):**
- The existing plan uses S_R spheres where SO(3) ≅ E(2) is manifest
- Stereographic projection transfers invariance to the plane
- This is an alternative to the lattice Ward identity approach

**For proof of principle:** Use **Option B** (Ward identities) to test the
same pipeline as O(3). The power-counting argument is simpler because
P(Φ)₂ is super-renormalizable (no log corrections fighting the a² decay).

**Reuse from OSforGFF:** `OS2_GFF.lean` proves Euclidean invariance for the
free field via covariance invariance. For P(Φ)₂ on the lattice, we need the
Ward identity machinery (new).

**Difficulty:** Medium-Hard (the Ward identity / irrelevance proof is the main
technical challenge, but simpler than O(3) because super-renormalizable).

---

### OS3 (Reflection Positivity)

**Statement:** For test functions f₁,...,fₙ supported at positive time and
real coefficients c₁,...,cₙ:
Σᵢⱼ cᵢcⱼ Z[fᵢ - Θfⱼ] ≥ 0
where Θ is time reflection.

**Lattice proof (direct):**
1. The lattice action decomposes across the t = 0 hyperplane:
   S_a[φ] = S⁺[φ⁺] + S⁻[φ⁻] + Σ_{x: t=0} φ_x(φ_{x+ê₀} + φ_{x-ê₀})
2. The coupling term is reflection-symmetric
3. The transfer matrix T = exp(-aH) is self-adjoint and positive
4. Therefore: ⟨F⁺, T F⁻⟩ = ⟨F⁺, T ΘF⁺⟩ ≥ 0

This is the standard lattice RP proof (Osterwalder-Seiler 1978).

**Continuum:** RP measures form a closed cone under weak convergence.
Therefore RP is automatically inherited in the continuum limit.
(This is the "Module A" insight from Deep Think Q4.)

**Reuse from OSforGFF:** `OS3_GFF.lean` proves RP for the Gaussian via
Hadamard exponential preservation of positive semi-definiteness. For P(Φ)₂
on the lattice, we need the transfer matrix argument (new, but standard).

**Difficulty:** Easy (lattice RP is a one-page proof; inheritance is standard).

---

### OS4 (Clustering / Mass Gap)

**Statement:** For test functions f, g with g translated by distance R:
|⟨Z[f + T_R g]⟩ - ⟨Z[f]⟩⟨Z[g]⟩| → 0 as R → ∞

Stronger form (exponential clustering / mass gap):
|⟨φ(x)φ(0)⟩ - ⟨φ⟩²| ≤ C exp(-m|x|) with m > 0

**Lattice proof strategy:**

*For small coupling λ:* Cluster expansion (Glimm-Jaffe-Spencer).
- Write the partition function as a polymer expansion
- Each polymer is a connected cluster of lattice sites
- The expansion converges for |λ| small enough (or m₀ large enough)
- Exponential clustering follows from the cluster expansion convergence
- This gives an explicit mass gap m ≥ m₀ - O(λ)

*For general coupling:* Use the transfer matrix spectral gap.
- T = exp(-aH) with H = -Δ + m₀² + λP'(φ) on L²(ℝ)
- For P bounded below and even degree ≥ 4: H has compact resolvent
- Therefore H has discrete spectrum with lowest eigenvalue E₀
- Mass gap = E₁ - E₀ > 0 (strict because P is confining)
- Simon-Hoegh-Krohn (1972): spectral gap implies exponential clustering

**Continuum:** Mass gap is inherited if TRG/cluster expansion error bounds
are controlled (the "Module C" strategy from Deep Think Q4).

**Reuse from OSforGFF:** `OS4_Clustering.lean` proves clustering for GFF via
Gaussian factorization. For P(Φ)₂, the Gaussian argument doesn't apply
directly; we need the cluster expansion or spectral gap argument (new).

**Difficulty:** Medium. The cluster expansion is technically involved but
well-established. The spectral gap argument is cleaner for Lean.

---

### OS4-alt (Ergodicity)

**Statement:** Time averages converge to ensemble averages in L²(μ):
(1/T) ∫₀ᵀ A(T_s φ) ds → 𝔼[A] as T → ∞

**Proof:** Follows automatically from OS4 (clustering) via a standard
argument: polynomial clustering with rate α > 1 implies ergodicity.

**Reuse from OSforGFF:** `OS4_Ergodicity.lean` proves this implication
generically. It should work at d=2 with minimal changes.

**Difficulty:** Easy (given OS4 clustering).

---

## 5. Lean Module Architecture

### Existing Modules (Reuse / Adapt)

```
OSforGFF/                          -- imported as dependency
├── Basic.lean                     -- SpaceTime 2, TestFunction 2, etc. ✓
├── OS_Axioms.lean                 -- All axiom definitions ✓
├── Euclidean.lean                 -- E(2) actions ✓
├── TimeTranslation.lean           -- Time shifts ✓
├── DiscreteSymmetry.lean          -- Θ reflection ✓
└── FunctionalAnalysis.lean        -- Distribution theory ✓
```

### New / Adapted Modules in pphi2

```
Pphi2/
├── Basic.lean                     -- (exists) d=2 setup, cylinder
├── Polynomial.lean                -- (exists) Interaction polynomial, Wick ordering
├── OSAxioms.lean                  -- (exists) Axiom bundle → EXTEND to all 5
│
├── Lattice/                       -- NEW: Lattice infrastructure
│   ├── LatticeSpace.lean          -- Λ_a = aℤ² ∩ [-L,L]², lattice fields
│   ├── LatticeAction.lean         -- S_a[φ], nearest-neighbor action
│   ├── LatticeMeasure.lean        -- dμ_a, well-definedness, normalization
│   ├── LatticeGreenFunction.lean  -- G_a(x,y), Wick ordering counterterm c_a
│   └── TransferMatrix.lean        -- T = e^{-aH}, self-adjoint, positive
│
├── FreeField/                     -- NEW: GFF at d=2
│   ├── Covariance2D.lean          -- C(x) = K₀(m|x|)/(2π), log singularity
│   ├── HeatKernel2D.lean          -- (4πt)^{-1} exp(-|x|²/4t)
│   └── GFF2D.lean                 -- d=2 Gaussian measure, Minlos construction
│
├── OSProofs/                      -- NEW: OS axiom proofs
│   ├── OS0_Analyticity.lean       -- Analytic generating functional
│   ├── OS1_Regularity.lean        -- Exponential bounds with p=2
│   ├── OS2_Invariance.lean        -- Ward identity + irrelevance proof
│   ├── OS3_RP_Lattice.lean        -- Transfer matrix RP on lattice
│   ├── OS3_RP_Continuum.lean      -- RP inheritance via weak convergence
│   ├── OS4_ClusterExpansion.lean  -- Polymer expansion, convergence
│   ├── OS4_MassGap.lean           -- Spectral gap of transfer matrix
│   └── OS4_Ergodicity.lean        -- Ergodicity from clustering
│
├── ContinuumLimit/                -- NEW: a → 0 limit
│   ├── WickCounterterm.lean       -- c_a ~ (1/2π) log(1/a), uniformity
│   ├── CorrelationConvergence.lean -- Schwinger functions converge
│   └── MeasureConvergence.lean    -- Weak convergence of μ_a → μ
│
├── WardIdentity/                  -- NEW: Euclidean invariance restoration
│   ├── RotationGenerator.lean     -- SO(2) generator on lattice
│   ├── LatticeWardIdentity.lean   -- Ward identity with anomaly
│   ├── IrrelevanceProof.lean      -- dim(O_break) = 4 > 2, coefficient → 0
│   └── SymmetryRestoration.lean   -- Full E(2) invariance in continuum
│
├── Main.lean                      -- (exists) Main theorem → EXTEND
│
├── MeasureCylinder/               -- (exists) UV limit construction
├── ReflectionPositivity/          -- (exists) DDJ-style RP
├── EuclideanInvariance/           -- (exists) DDJ-style invariance
├── Integrability/                 -- (exists) OS regularity
├── InfiniteVolume/                -- (exists) Tightness/Prokhorov
├── StochasticQuant/               -- (exists) Da Prato-Debussche
├── StochasticEst/                 -- (exists) Free field bounds
├── Energy/                        -- (exists) A priori estimates
├── FunctionSpaces/                -- (exists) Weighted Lp, Sobolev
└── GaussianCylinder/              -- (exists) Gaussian on cylinder
```

### Main Theorem (Extended)

```lean
/-- Full OS axioms for P(Φ)₂ via lattice construction. -/
theorem pphi2_full_OS (P : InteractionPolynomial) :
    ∃ (dμ : ProbabilityMeasure (FieldConfiguration 2)),
      OS0_Analyticity dμ ∧
      OS1_Regularity dμ ∧
      OS2_EuclideanInvariance dμ ∧
      OS3_ReflectionPositivity dμ ∧
      OS4_Clustering dμ ∧
      OS4_Ergodicity dμ
```

This is stronger than the current `pphi2_main` which only bundles 3 axioms
on the cylinder (no OS0, OS4) and uses `sorry` for all three.

---

## 6. Implementation Phases

### Phase 1: GFF at d=2 (Generalize OSforGFF)

**Goal:** Prove all OS axioms for the free scalar field at d=2.

**Tasks:**
1. Create `FreeField/Covariance2D.lean` — d=2 propagator C(k) = 1/(k² + m²)
2. Create `FreeField/HeatKernel2D.lean` — (4πt)^{-1} heat kernel
3. Adapt momentum-space proofs from OSforGFF `CovarianceMomentum.lean` to d=2
4. Prove OS0-OS4 for GFF at d=2 (adapt existing OSforGFF proofs)
   - Most proofs simplify because d=2 integrals are lower-dimensional
   - `OS3_MixedRep` calculations become 1D spatial Fourier transforms

**Estimated effort:** 2-3 weeks. The OSforGFF proofs are the template;
d=2 calculations are uniformly simpler.

### Phase 2: Lattice Infrastructure

**Goal:** Define lattice scalar field theory in Lean.

**Tasks:**
1. `Lattice/LatticeSpace.lean` — Finite lattice Λ_a as `Finset (Fin N × Fin N)`
2. `Lattice/LatticeAction.lean` — S_a[φ] as sum over edges and vertices
3. `Lattice/LatticeMeasure.lean` — Product Lebesgue measure × exp(-S_a)
4. `Lattice/LatticeGreenFunction.lean` — Discrete Laplacian, Green's function
5. `Lattice/TransferMatrix.lean` — T as integral kernel, self-adjointness

**Estimated effort:** 2-3 weeks. All definitions are finite-dimensional
linear algebra, well within Lean/Mathlib capabilities.

### Phase 3: Lattice OS Proofs

**Goal:** Prove OS axioms directly on the lattice.

**Tasks:**
1. `OSProofs/OS3_RP_Lattice.lean` — RP via transfer matrix positivity
   - Key: S_a decomposes across t = 0 plane
   - Transfer matrix T is symmetric and positive
   - This is a **one-page proof** on the lattice

2. `OSProofs/OS4_MassGap.lean` — Spectral gap of H
   - H = -d²/dφ² + V(φ) on L²(ℝ) (1D quantum mechanics!)
   - V(φ) = m₀²φ² + λP(φ) is confining (grows as φ^{2p})
   - Compact resolvent → discrete spectrum → gap > 0
   - Mathlib has spectral theory for compact operators

3. `OSProofs/OS4_ClusterExpansion.lean` — Polymer expansion (optional)
   - Alternative proof of mass gap via combinatorial expansion
   - More technical but gives explicit bounds on correlation length

**Estimated effort:** 3-4 weeks.

### Phase 4: Continuum Limit

**Goal:** Take a → 0 and prove convergence.

**Tasks:**
1. `ContinuumLimit/WickCounterterm.lean` — c_a = (1/2π)log(1/a) + O(1)
   - Only counterterm needed (super-renormalizability)
   - Uniform bounds in a

2. `ContinuumLimit/CorrelationConvergence.lean`
   - Schwinger functions converge: |S_a^(n) - S^(n)| → 0
   - Use lattice Green's function convergence to continuum propagator

3. `ContinuumLimit/MeasureConvergence.lean`
   - Weak convergence of measures μ_a → μ
   - Use tightness (from uniform moment bounds) + Prokhorov's theorem

**Estimated effort:** 3-4 weeks.

### Phase 5: OS Axiom Inheritance + Euclidean Invariance

**Goal:** Prove all OS axioms hold in the continuum limit.

**Tasks:**
1. `OSProofs/OS3_RP_Continuum.lean` — RP closed cone argument
   - RP measures form closed set under weak convergence
   - Lattice RP + weak convergence → continuum RP

2. `OSProofs/OS0_Analyticity.lean` — Analyticity from uniform bounds
3. `OSProofs/OS1_Regularity.lean` — Regularity from uniform bounds

4. `WardIdentity/` — Euclidean invariance restoration (the hardest part)
   - Define SO(2) generator on lattice
   - Compute Ward identity anomaly
   - Prove anomaly = O(a²) via power counting
   - **Key simplification vs O(3):** P(Φ)₂ is super-renormalizable,
     so there are NO logarithmic corrections fighting the a² decay.
     The irrelevance proof is purely polynomial, no multi-scale expansion needed.

5. `OSProofs/OS4_Ergodicity.lean` — From clustering (generic argument)

**Estimated effort:** 4-5 weeks.

### Phase 6: Assembly and Main Theorem

**Goal:** Wire everything together.

**Tasks:**
1. Extend `OSAxioms.lean` to bundle all 5 axioms
2. Update `Main.lean` with the full theorem
3. Verify the entire proof compiles

**Estimated effort:** 1 week.

---

## 7. Relationship to Existing pphi2 Code

The current pphi2 codebase follows the DDJ stochastic quantization approach
(sphere S_R → stereographic projection → plane ℝ²). This is a **different
construction** of the same P(Φ)₂ theory.

**Strategy:** Keep both constructions:
- **DDJ path** (existing code): Stochastic quantization on S_R
  - Proves OS1 (regularity), OS2 (invariance), OS3 (RP) for cylinder
  - Does NOT prove OS4 (clustering/mass gap)
  - Euclidean invariance is manifest (via sphere symmetry)

- **Lattice path** (new code): Lattice → continuum limit
  - Proves ALL OS axioms including OS4
  - RP is manifest on lattice
  - Euclidean invariance via Ward identity restoration
  - Tests the modular architecture for O(3)

Eventually, one could prove these two constructions yield the **same** continuum
theory (a universality theorem), but this is not required for the proof of principle.

---

## 8. Comparison: P(Φ)₂ vs O(3) NLSM

| Feature | P(Φ)₂ | O(3) NLSM |
|---------|--------|-----------|
| Target space | ℝ (flat) | S² (curved) |
| Renormalizability | Super-renormalizable | Renormalizable (marginal) |
| Counterterms | Mass only: c_a ~ log(1/a) | Running coupling β(a) |
| Mass gap mechanism | Confining potential | Asymptotic freedom |
| RP on lattice | Easy (scalar transfer matrix) | Medium (need S² geometry) |
| Euclidean invariance | Easy (no log corrections) | Hard (logs fight a² decay) |
| Cluster expansion | Standard (Glimm-Jaffe-Spencer) | Advanced (Bałaban-style) |
| TRG needed? | Optional (spectral gap suffices) | Essential (for mass gap bounds) |
| Literature | Complete (1970s) | Partial (active research) |

**Key simplifications for P(Φ)₂:**
1. No curved target space geometry (no harmonic maps, CG coefficients)
2. No running coupling (only mass renormalization)
3. Ward identity irrelevance: O(a²) with NO competing log terms
4. Transfer matrix spectral gap: 1D quantum mechanics with confining potential
5. Cluster expansion: standard, not multi-scale

---

## 9. Key References

### P(Φ)₂ Construction
- **Glimm-Jaffe** (1973): Original construction, *Positivity of the φ⁴₃ Hamiltonian*
- **Simon** (1974): *The P(φ)₂ Euclidean (Quantum) Field Theory* (Princeton)
- **Guerra-Rosen-Simon** (1975): Nelson's symmetry, correlation inequalities
- **Duch-Dybalski-Jahandideh** (2311.04137): Modern stochastic quantization approach

### OS Axioms
- **Osterwalder-Schrader** (1973, 1975): Original axiom formulation
- **Glimm-Jaffe** (1987): *Quantum Physics* textbook, Chapter 6
- **Osterwalder-Seiler** (1978): Lattice reflection positivity

### Cluster Expansion
- **Glimm-Jaffe-Spencer** (1975): Cluster expansion for P(φ)₂
- **Brydges** (1986): Lectures on cluster expansions
- **Rivasseau** (1991): *From Perturbative to Constructive Renormalization*

### Euclidean Invariance Restoration
- **Symanzik** (1983): Continuum limit of lattice field theories
- **Luscher-Weisz** (1985): Symanzik improvement program
- **Duch** (2024): Ward identities for lattice → continuum (O(N) models)

---

## 10. Success Criteria

The proof of principle is successful if we can:

1. ✅ State all 5 OS axioms for P(Φ)₂ in Lean with d=2
2. ✅ Prove RP on the lattice (transfer matrix argument)
3. ✅ Prove mass gap (spectral gap of 1D Schrödinger operator)
4. ✅ Prove continuum limit exists (tightness + Prokhorov)
5. ✅ Prove RP inheritance (closed cone)
6. ✅ Prove Euclidean invariance restoration (Ward identity + irrelevance)
7. ✅ Assemble all axioms into the full theorem `pphi2_full_OS`

**Stretch goal:** Explicit numerical bounds on mass gap as function of (m₀, λ).

**Timeline estimate:** 15-20 weeks total across all phases.
